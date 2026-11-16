module
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSectionsRingSpec
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective

/-!
# Restricting a divisorial valuation along a quasi-finite dominant morphism

Let `q : Y_e ⟶ Y₀` be a dominant, locally quasi-finite morphism of varieties over a field `k`
(for instance a dominant étale morphism of normal complex varieties). Then `k(Y_e)` is a finite
extension of `k(Y₀)`, and the restriction to `k(Y₀)` of a normalized divisorial valuation `w`
of `k(Y_e)` is a positive integer multiple `e · v` of a normalized divisorial valuation `v` of
`k(Y₀)`; the integer `e` is the ramification index of `w` over `v`.

## Main results

* `MMP.Fourfold.exists_isNormalizedDivisorialValuation_comap_eq_pow`: for `w` normalized
  divisorial on `k(Y_e)` there are a normalized divisorial `v` on `k(Y₀)` and `0 < e` with
  `w (q^* g) = v g ^ e` for all `g ∈ k(Y₀)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.6.2)

## Implementation notes

* Valuations are multiplicative, with values in `ℤᵐ⁰`, so the additive `w|_{k(Y₀)} = e · v`
  reads `w (q^* g) = v g ^ e`.
* The variety structure of `Y_e` is `q ≫ s₀`, so `q` is a morphism of `k`-varieties.
* The source takes `k = ℂ`, `q` étale and both varieties normal. The statement is made over any
  field, for `q` dominant and locally quasi-finite (an étale morphism is locally quasi-finite);
  normality is not used. A finite surjective morphism of normal varieties is a special case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

section Helpers

open WithZero

/-- The value group of a rank-one discrete `ℤᵐ⁰`-valued valuation of a field is `e ℤ`, `e > 0`:
every nonzero value has logarithm divisible by `e`, and `-e` is a logarithm of a value. -/
private theorem exists_log_dvd_of_isRankOneDiscrete {K : Type*} [Field K] (r : Valuation K ℤᵐ⁰)
    [r.IsRankOneDiscrete] :
    ∃ e : ℕ, 0 < e ∧ (∀ x, r x ≠ 0 → (e : ℤ) ∣ (r x).log) ∧
      ∃ x, r x ≠ 0 ∧ (r x).log = -e := by
  obtain ⟨γ, hγ, hγ1⟩ := Valuation.IsRankOneDiscrete.exists_generator_lt_one r
  have hγ0 : (γ : ℤᵐ⁰) ≠ 0 := γ.ne_zero
  have hlog : (γ : ℤᵐ⁰).log < 0 := by
    have : (γ : ℤᵐ⁰) < 1 := by exact_mod_cast hγ1
    rwa [← exp_log hγ0, ← exp_zero, exp_lt_exp] at this
  refine ⟨(-(γ : ℤᵐ⁰).log).toNat, by omega, fun x hx => ?_, ?_⟩
  · have hm : Units.mk0 (r x) hx ∈ Subgroup.zpowers γ := by
      rw [hγ]
      exact MonoidWithZeroHom.mem_valueGroup _ ⟨x, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at hm
    obtain ⟨n, hn⟩ := hm
    have : r x = (γ : ℤᵐ⁰) ^ n := by
      have := congrArg Units.val hn; simpa using this.symm
    rw [this, log_zpow]
    refine ⟨-n, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; simp; ring
  · obtain ⟨⟨x, hx⟩, -⟩ := (MonoidWithZeroHom.valueGroup_eq_range
      (f := MonoidWithZeroHom.ofClass r)).subset ⟨γ, hγ ▸ Subgroup.mem_zpowers γ, rfl⟩
    replace hx : r x = γ := hx
    refine ⟨x, hx ▸ hγ0, ?_⟩
    rw [hx, Int.toNat_of_nonneg (by omega)]; ring

/-- A rank-one discrete `ℤᵐ⁰`-valued valuation `r` of a field is `v ^ e` for some `e > 0` and a
valuation `v` taking the value `exp (-1)` (a normalized discrete valuation). -/
private theorem exists_pow_eq_of_isRankOneDiscrete {K : Type*} [Field K] (r : Valuation K ℤᵐ⁰)
    [r.IsRankOneDiscrete] :
    ∃ v : Valuation K ℤᵐ⁰, ∃ e : ℕ, 0 < e ∧ (∀ x, r x = v x ^ e) ∧ ∃ x, v x = exp (-1) := by
  obtain ⟨e, he, hdvd, x₀, hx₀, hlog₀⟩ := exists_log_dvd_of_isRankOneDiscrete r
  let f : ℤᵐ⁰ → ℤᵐ⁰ := fun a => if a = 0 then 0 else exp (a.log / e)
  have hmono : ∀ x y, r x ≤ r y → f (r x) ≤ f (r y) := by
    intro x y hxy
    by_cases hx : r x = 0
    · simp [f, hx]
    have hy : r y ≠ 0 := fun h => hx (le_antisymm (h ▸ hxy) zero_le')
    simp only [f, hx, hy, if_false, exp_le_exp]
    exact Int.ediv_le_ediv (by omega) ((log_le_log hx hy).mpr hxy)
  let v : Valuation K ℤᵐ⁰ :=
    { toFun := fun x => f (r x)
      map_zero' := by simp [f]
      map_one' := by simp [f]
      map_mul' := by
        intro x y
        by_cases hx : r x = 0
        · simp [f, hx]
        by_cases hy : r y = 0
        · simp [f, hy]
        have hxy : r (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
        simp only [f, if_neg hxy, if_neg hx, if_neg hy]
        rw [map_mul, log_mul hx hy, Int.add_ediv_of_dvd_left (hdvd x hx), exp_add]
      map_add_le_max' := by
        intro x y
        rcases le_max_iff.mp (r.map_add x y) with h | h
        · exact (hmono _ _ h).trans (le_max_left _ _)
        · exact (hmono _ _ h).trans (le_max_right _ _) }
  refine ⟨v, e, he, fun x => ?_, x₀, ?_⟩
  · change r x = f (r x) ^ e
    by_cases hx : r x = 0
    · simp [f, hx, he.ne']
    simp only [f, hx, if_false, ← exp_nsmul]
    rw [nsmul_eq_mul, Int.mul_ediv_cancel' (hdvd x hx), exp_log hx]
  · change f (r x₀) = _
    simp only [f, hx₀, if_false, hlog₀]
    rw [Int.neg_ediv_self _ (by omega)]

/-- A dominant, locally quasi-finite morphism of integral schemes locally of finite type over a
field has a finite extension of function fields: the generic point of the source is the only
point over the generic point of the target. -/
private theorem finite_functionField_of_locallyQuasiFinite {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀]
    [IsIntegral Yₑ] (q : Yₑ ⟶ Y₀) [IsDominant q] [LocallyQuasiFinite q]
    [LocallyOfFiniteType q] :
    letI := (functionFieldMap q).toAlgebra
    Module.Finite Y₀.functionField Yₑ.functionField := by
  have hgen : ∀ x : Yₑ, q x = genericPoint Y₀ → x = genericPoint Yₑ := fun x hx => by
    have hsp := genericPoint_specializes x
    have h₀ : q (genericPoint Yₑ) = genericPoint Y₀ :=
      ((hx ▸ hsp.map q.continuous).antisymm (genericPoint_specializes _)).eq
    exact (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite q hsp (h₀.trans hx.symm)).symm
  have h := (trdeg_functionField_eq_zero_iff_finite q).mp
    (trdeg_functionField_eq_zero_of_eq_genericPoint q hgen)
  convert h using 3
  exact (MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap q).symm

/-- A `ℤᵐ⁰`-valued valuation of a field taking the value `exp (-1)` is rank-one discrete. -/
private theorem isRankOneDiscrete_of_exists_eq_exp_neg_one {K : Type*} [Field K]
    (v : Valuation K ℤᵐ⁰) (hv : ∃ g, v g = exp (-1)) : v.IsRankOneDiscrete := by
  obtain ⟨g, hval⟩ := hv
  refine ⟨⟨Units.mk0 (exp (-1)) exp_ne_zero, le_antisymm ?_ ?_, ?_⟩⟩
  · rw [Subgroup.zpowers_le]
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨g, by simpa using hval⟩
  · intro γ _
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-(γ : ℤᵐ⁰).log, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← exp_zsmul, smul_neg, smul_eq_mul, mul_one,
      neg_neg, exp_log γ.ne_zero]
  · change exp (-1 : ℤ) < 1
    rw [← exp_zero, exp_lt_exp]
    omega

/-- The valuation `ord_E` of a divisor `(W, f, E)` over an integral scheme, regarded as a
valuation of `k(X)`, is a rank-one discrete valuation. -/
private theorem isRankOneDiscrete_divisorOver_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (D : MMP.Mori.DivisorOver k sX) :
    D.valuation.IsRankOneDiscrete := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D.E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
  obtain ⟨g, hg⟩ := (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
    D.isBirationalMorphism).2 (algebraMap D.E.localRing D.Y.functionField ϖ)
  refine isRankOneDiscrete_of_exists_eq_exp_neg_one _ ⟨g, ?_⟩
  change D.E.divisorialValuation (functionFieldMap D.f g) = _
  rw [hg]
  exact D.E.divisorialValuation_algebraMap_of_irreducible hϖ

/-- The centre of `w = ord_E` on `Y_e` maps to a centre on `Y₀` of every `v` with
`v ^ e = w|_{k(Y₀)}`: the local ring `𝒪_{Y₀, q(f(η_E))}` is dominated by the valuation ring
of `v`. -/
private theorem exists_dominates_of_pow_eq {k : Type u} [Field k] {Y₀ Yₑ : Scheme.{u}}
    [IsIntegral Y₀] [IsIntegral Yₑ] (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) [IsDominant q]
    (D : MMP.Mori.DivisorOver k (q ≫ s₀)) (v : Valuation Y₀.functionField ℤᵐ⁰) (e : ℕ)
    (he : 0 < e) (hv : ∀ g, D.valuation (functionFieldMap q g) = v g ^ e) :
    ∃ x : Y₀, (∀ a : Y₀.presheaf.stalk x, v (algebraMap _ Y₀.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y₀.presheaf.stalk x),
        v (algebraMap _ Y₀.functionField a) < 1 := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hval : ∀ a : Y₀.presheaf.stalk ((D.f ≫ q) D.E.genericPoint),
      v (algebraMap _ Y₀.functionField a) ^ e = D.E.divisorialValuation
        (algebraMap D.E.localRing D.Y.functionField (((D.f ≫ q).stalkMap _).hom a)) := by
    intro a
    rw [← hv]
    change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap q _)) = _
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
  refine ⟨(D.f ≫ q) D.E.genericPoint, fun a => ?_, fun a ha => ?_⟩
  · refine le_of_not_gt fun h₁ => (one_lt_pow' h₁ he.ne').not_ge ?_
    rw [hval]
    exact (D.E.divisorialValuation_le_one_iff _).mpr ⟨_, rfl⟩
  · refine lt_of_pow_lt_pow_left' e ?_
    rw [hval, one_pow, D.E.divisorialValuation_algebraMap_lt_one_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit _ _ hu)

/-- The `k`-algebra structure on the residue field of the valuation ring of `v`, through
`k → 𝒪_{X,x} → 𝒪_v`, for `v` nonnegative on the local ring `𝒪_{X,x}`. -/
private noncomputable abbrev residueAlgebra {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) (v : Valuation X.functionField ℤᵐ⁰) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1) :
    Algebra k (IsLocalRing.ResidueField v.valuationSubring) :=
  ((IsLocalRing.residue v.valuationSubring).comp
    (((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict v.valuationSubring
      fun a => (v.mem_valuationSubring_iff _).mpr (hle a)).comp
      ((X.presheaf.germ ⊤ x trivial).hom.comp
        ((sX.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra

section Realization

open MMP.Mori MMP.Flips

universe w

/-- A local ring of an integral scheme `Y` birational to `X` which, inside the function field, is
the valuation ring of a valuation of `k(X)` is a valuation ring. -/
private theorem valuationRing_stalk_of_forall_le_one_iff {X Y : Scheme.{w}}
    [IsIntegral X] [IsIntegral Y] (β : Y ⟶ X) (hβ : IsBirationalMorphism β)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation X.functionField Γ) (q : Y)
    (hq : haveI : IsDominant β := hβ.isDominant
      ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = functionFieldMap β g) :
    ValuationRing (Y.presheaf.stalk q) := by
  haveI : IsDominant β := hβ.isDominant
  let φ := RingEquiv.ofBijective (functionFieldMap β) hβ.functionFieldMap_bijective
  let w : Valuation Y.functionField Γ := v.comap φ.symm.toRingHom
  have hw : ∀ r, w r ≤ 1 ↔ ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = r := by
    intro r
    have := hq (φ.symm r)
    rwa [show functionFieldMap β (φ.symm r) = φ (φ.symm r) from rfl,
      RingEquiv.apply_symm_apply] at this
  exact ValuationRing.of_integers w
    ⟨IsFractionRing.injective _ _, fun a => (hw _).2 ⟨a, rfl⟩, fun r hr => (hw r).1 hr⟩

/-- A dominant morphism of integral schemes inducing a surjection of function fields is an
isomorphism on the local ring at every point whose image has a valuation ring as local ring. -/
private theorem isIso_stalkMap_of_valuationRing {Y Z : Scheme.{w}} [IsIntegral Y] [IsIntegral Z]
    (ν : Z ⟶ Y) [IsDominant ν] (hν : Function.Surjective (functionFieldMap ν)) (z : Z)
    [ValuationRing (Y.presheaf.stalk (ν z))] : IsIso (ν.stalkMap z) := by
  set φ := (ν.stalkMap z).hom
  have hsq : ∀ a, algebraMap _ Z.functionField (φ a) =
      functionFieldMap ν (algebraMap _ Y.functionField a) := fun a =>
    (MMP.Mori.functionFieldMap_algebraMap_stalk ν z a).symm
  have hinj : Function.Injective φ := by
    intro a b hab
    apply IsFractionRing.injective (Y.presheaf.stalk (ν z)) Y.functionField
    apply (functionFieldMap ν).injective
    rw [← hsq, ← hsq, hab]
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨r, hr⟩ := hν (algebraMap _ Z.functionField b)
    by_cases hr0 : r = 0
    · refine ⟨0, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
      rw [map_zero, map_zero, ← hr, hr0, map_zero]
    rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk (ν z)) r with ⟨a, ha⟩ | ⟨c, hc⟩
    · refine ⟨a, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
      rw [hsq, ha, hr]
    · have h1 : φ c * b = 1 := by
        apply IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField
        rw [map_mul, hsq, hc, ← hr, ← map_mul, inv_mul_cancel₀ hr0, map_one, map_one]
      have hcu : IsUnit c := (isUnit_map_iff φ c).mp (IsUnit.of_mul_eq_one _ h1)
      obtain ⟨d, hd⟩ := hcu.exists_left_inv
      refine ⟨d, ?_⟩
      calc φ d = φ d * (φ c * b) := by rw [h1, mul_one]
        _ = b := by rw [← mul_assoc, ← map_mul, hd, map_one, one_mul]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{w}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- An ideal of the sections over an affine open extends to an ideal sheaf: the kernel of the
closed subscheme `Spec (Γ(X, U) ⧸ J) ⟶ X`, i.e. the ideal sheaf of its scheme-theoretic closure. -/
private theorem exists_idealSheafData_ideal_eq {X : Scheme.{w}} [QuasiSeparatedSpace X]
    (U : X.affineOpens) (J : Ideal Γ(X, U)) : ∃ ℐ : X.IdealSheafData, ℐ.ideal U = J := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let π : Spec (.of (Γ(X, U) ⧸ J)) ⟶ X := Spec.map φ ≫ hU.fromSpec
  refine ⟨π.ker, ?_⟩
  rw [Scheme.Hom.ker_apply]
  ext a
  rw [RingHom.mem_ker]
  have hle : (⊤ : (Spec (.of (Γ(X, U) ⧸ J))).Opens) ≤ π ⁻¹ᵁ U := by
    intro y _
    change hU.fromSpec ((Spec.map φ) y) ∈ (U : X.Opens)
    exact hU.range_fromSpec.subset ⟨_, rfl⟩
  have hres : (π.app U).hom a = 0 ↔ (π.appLE U ⊤ hle).hom a = 0 := by
    have heq : (homOfLE hle) = eqToHom (top_le_iff.mp hle).symm := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, heq, CommRingCat.comp_apply]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((Spec (.of (Γ(X, U) ⧸ J))).presheaf.map (eqToHom (top_le_iff.mp hle).symm).op)).1).symm
  have hcomp : π.appLE U ⊤ hle = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    congr 1
  rw [hres, hcomp, CommRingCat.comp_apply]
  have hnat := congrArg (fun g => g.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hnat
  rw [← map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).hom).1]
  erw [hnat]
  rw [CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  exact Ideal.Quotient.eq_zero_iff_mem (I := J)

/-- Let `φ : S → L` land in the valuation ring of `w`, with `S` essentially of finite type over
`R`. If a subring `C` contains the images of `R` and of the generators of `S`, every `φ s` is a
fraction `c / t` with `c, t ∈ C` and `w t = 1`. -/
private theorem exists_mul_eq_of_essFiniteType {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (φ : S →+* L)
    (hφ : ∀ s, w (φ s) ≤ 1) (C : Subring L) (hR : ∀ r, φ (algebraMap R S r) ∈ C)
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, φ s ∈ C) (s : S) :
    ∃ c ∈ C, ∃ t ∈ C, w t = 1 ∧ φ s * t = c := by
  have hcond := (Algebra.essFiniteType_cond_iff R S (Algebra.EssFiniteType.finset R S)).mp
    (Algebra.EssFiniteType.isLocalization R S)
  have hadj : ∀ y ∈ Algebra.adjoin R (Algebra.EssFiniteType.finset R S : Set S), φ y ∈ C := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hσ x hx
    | algebraMap r => exact hR r
    | add x y _ _ hx hy => rw [map_add]; exact C.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact C.mul_mem hx hy
  obtain ⟨t, ht, htu, hst⟩ := hcond s
  exact ⟨φ (s * t), hadj _ hst, φ t, hadj _ ht,
    (letI := φ.toAlgebra; Valuation.Integers.one_of_isUnit' (v := w) htu hφ),
    (map_mul φ s t).symm⟩

/-- If every element of `J` has value at most that of `h`, every element of `Jⁿ` has value at
most that of `hⁿ`. -/
private theorem valuation_le_pow_of_mem_pow {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ι : A →+* L)
    (hA : ∀ a, w (ι a) ≤ 1) (J : Ideal A) (h : A) (hJ : ∀ y ∈ J, w (ι y) ≤ w (ι h)) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, w (ι y) ≤ w (ι h) ^ n := by
  intro n
  induction n with
  | zero => intro y _; rw [pow_zero]; exact hA y
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, map_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hJ b hb)
    · rw [map_add]
      exact (w.map_add _ _).trans (max_le ha hb)

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type w} [Field k] {Y : Scheme.{w}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  letI := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- Sections pulled back along a dominant morphism of integral schemes map to the function field
through `functionFieldMap`. -/
private theorem germToFunctionField_appLE {X Y : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (V : Y.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    Y.germToFunctionField V (f.appLE U V h s) = functionFieldMap f (X.germToFunctionField U s) := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty V›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (h hy),
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  congr 1
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- The constants `k ⊆ k(X)` are sections over every nonempty open. -/
private theorem exists_germToFunctionField_eq_algebraMap {k : Type w} [Field k] {X : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] (U : X.Opens) [Nonempty U] (c : k) :
    letI := functionFieldAlgebra sX
    ∃ a : Γ(X, U), X.germToFunctionField U a = algebraMap k X.functionField c := by
  letI := functionFieldAlgebra sX
  refine ⟨X.presheaf.map (homOfLE le_top).op (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv c)), ?_⟩
  change X.presheaf.germ U _ _ _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) (by simp)) c
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- The prime of the point of an affine open given by a prime `P` of its sections is `P`. -/
private theorem primeIdealOf_fromSpec {X : Scheme.{w}} {W : X.Opens} (hW : IsAffineOpen W)
    (P : PrimeSpectrum Γ(X, W)) (hP : hW.fromSpec P ∈ W) :
    hW.primeIdealOf ⟨hW.fromSpec P, hP⟩ = P := by
  have : (⟨hW.fromSpec P, hP⟩ : W) = hW.isoSpec.inv P := rfl
  rw [this]
  have h := Scheme.Hom.comp_apply hW.isoSpec.inv hW.isoSpec.hom (show Spec Γ(X, W) from P)
  rw [Iso.inv_hom_id] at h
  exact h.symm

/-- If `v ≤ 1` on `A` and every generator of `(h, T)` other than `h` has value at most `v h`, then
every element of the ideal `(h, T)` has value at most `v h`. -/
private theorem valuation_le_of_mem_span_insert {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ι : A →+* L)
    (hA : ∀ a, w (ι a) ≤ 1) (h : A) (T : Set A) (hT : ∀ t ∈ T, w (ι t) ≤ w (ι h)) :
    ∀ y ∈ Ideal.span (insert h T), w (ι y) ≤ w (ι h) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact le_rfl
    · exact hT z hz
  | zero =>
    rw [map_zero, map_zero]
    exact zero_le
  | add y z _ _ hy hz =>
    rw [map_add]
    exact (w.map_add _ _).trans (max_le hy hz)
  | smul c y _ hy =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (hA c)).trans hy

/-- For `ψ : A →+* L` landing in the valuation ring of `w`, the elements of value `< 1` form a
prime ideal of `A`. -/
private theorem exists_isPrime_forall_mem_iff {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ψ : A →+* L)
    (hψ : ∀ t, w (ψ t) ≤ 1) : ∃ P : Ideal A, P.IsPrime ∧ ∀ t, t ∈ P ↔ w (ψ t) < 1 := by
  let P : Ideal A :=
    { carrier := {t | w (ψ t) < 1}
      add_mem' := fun {y z} hy hz => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact (w.map_add _ _).trans_lt (max_lt hy hz)
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact (mul_le_of_le_one_left' (hψ c)).trans_lt hy }
  have hP : ∀ t, t ∈ P ↔ w (ψ t) < 1 := fun _ => Iff.rfl
  refine ⟨P, ⟨?_, fun {y z} h => ?_⟩, hP⟩
  · rw [Ideal.ne_top_iff_one, hP, map_one, map_one]
    exact lt_irrefl _
  · rw [hP, map_mul, map_mul] at h
    rw [hP, hP]
    by_contra hc
    push Not at hc
    rw [le_antisymm (hψ y) hc.1, le_antisymm (hψ z) hc.2, one_mul] at h
    exact lt_irrefl _ h

/-- In the localization `O = A_P` at `P = {t | w (ψ t) < 1}`, a fraction `c / t` with
`w (ψ t) = 1` is the image of an element of `O`. -/
private theorem exists_eq_of_mul_eq_of_isLocalization {A O L : Type*} [CommRing A] [CommRing O]
    [Field L] [Algebra A O] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    (P : Ideal A) [P.IsPrime] [IsLocalization P.primeCompl O] (ψ : A →+* L) (μ : O →+* L)
    (hμ : ∀ t, μ (algebraMap A O t) = ψ t) (hP : ∀ t, t ∈ P ↔ w (ψ t) < 1) {z : L} {c t : A}
    (ht : w (ψ t) = 1) (hct : z * ψ t = ψ c) : ∃ y, μ y = z := by
  have htP : t ∈ P.primeCompl := fun h => ((hP t).1 h).ne ht
  have hψt : ψ t ≠ 0 := fun h => by
    rw [h, map_zero] at ht
    exact zero_ne_one ht
  refine ⟨IsLocalization.mk' O c (⟨t, htP⟩ : P.primeCompl), mul_right_cancel₀ hψt ?_⟩
  rw [hct, ← hμ, ← hμ, ← map_mul, IsLocalization.mk'_spec]

/-- In the localization `O = A_P` at `P = {t | w (ψ t) < 1}`, where `w ∘ ψ ≤ 1`, every element of
`O` has value at most `1`. -/
private theorem valuation_le_one_of_isLocalization {A O L : Type*} [CommRing A] [CommRing O]
    [Field L] [Algebra A O] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    (P : Ideal A) [P.IsPrime] [IsLocalization P.primeCompl O] (ψ : A →+* L) (μ : O →+* L)
    (hμ : ∀ t, μ (algebraMap A O t) = ψ t) (hA : ∀ t, w (ψ t) ≤ 1)
    (hP : ∀ t, t ∈ P ↔ w (ψ t) < 1) (y : O) : w (μ y) ≤ 1 := by
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  have ht : w (ψ t) = 1 := le_antisymm (hA t) (not_lt.mp fun h => t.2 ((hP t).2 h))
  calc w (μ (IsLocalization.mk' O c t)) = w (μ (IsLocalization.mk' O c t) * ψ t) := by
        rw [map_mul, ht, mul_one]
    _ = w (ψ c) := by rw [← hμ, ← hμ, ← map_mul, IsLocalization.mk'_spec]
    _ ≤ 1 := hA c

/-- A morphism `f` maps the point of an affine open `W ≤ f⁻¹ U` cut out by a prime `P` of
`Γ(Y, W)` to `x ∈ U` as soon as `P` pulls back to the prime of `x`. -/
private theorem hom_fromSpec_eq_of_forall_mem_iff {X Y : Scheme.{w}} (f : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {W : Y.Opens} (hW : IsAffineOpen W) (hWle : W ≤ f ⁻¹ᵁ U)
    (P : PrimeSpectrum Γ(Y, W)) {x : X} (hxU : x ∈ U)
    (h : ∀ s, (f.appLE U W hWle).hom s ∈ P.asIdeal ↔ s ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    f (hW.fromSpec P) = x := by
  have hqW : hW.fromSpec P ∈ W := hW.range_fromSpec.subset ⟨P, rfl⟩
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU W hW hWle hqW
  have h2 : hU.primeIdealOf ⟨f (hW.fromSpec P), hWle hqW⟩ = hU.primeIdealOf ⟨x, hxU⟩ := by
    rw [← h1, primeIdealOf_fromSpec hW P hqW]
    apply PrimeSpectrum.ext
    ext s
    exact h s
  have := congrArg hU.fromSpec h2
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this

/-- On the chart `Spec Γ(X, U)[J/a]` of the blow-up of `ℐ`, `J = ℐ(U)`, every section has value
at most `1` for the valuation `w` induced by `v`, if `v ≤ 1` on `Γ(X, U)` and `v ≤ v a` on `J`. -/
private theorem valuation_germToFunctionField_blowUpChart_le_one {X : Scheme.{w}} [IsIntegral X]
    (ℐ : X.IdealSheafData) [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0)
    [Nonempty (blowUpChartOpen ℐ U a).1] {v : Valuation X.functionField ℤᵐ⁰}
    {w : Valuation (blowUp ℐ).functionField ℤᵐ⁰}
    (hw : ∀ g, w (functionFieldMap (blowUpToBase ℐ) g) = v g)
    (hle : ∀ s, v ((X.germToFunctionField U).hom s) ≤ 1)
    (hJ : ∀ y ∈ ℐ.ideal U,
      v ((X.germToFunctionField U).hom y) ≤ v ((X.germToFunctionField U).hom a))
    (t : Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1)) :
    w (((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom t) ≤ 1 := by
  let ι := (X.germToFunctionField U).hom
  let χ := (blowUpChartMap ℐ U a).hom
  let ψ := ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U _ (blowUpChartOpen_le ℐ U a) s
  obtain ⟨n, y, hy, hty⟩ := exists_mem_pow_mul_eq_blowUpChartMap ℐ U a t
  have hty' : t * χ a ^ n = χ y := hty
  have h1 : ψ t * fβ (ι a) ^ n = fβ (ι y) := by
    have := congrArg ψ hty'
    rwa [map_mul, map_pow, hψχ, hψχ] at this
  have h2 : w (ψ t) * v (ι a) ^ n = v (ι y) := by
    rw [← hw, ← hw, ← map_pow, ← map_mul, h1]
  have h3 := valuation_le_pow_of_mem_pow v ι hle _ _ hJ n y hy
  have hpos : 0 < v (ι a) ^ n := by
    apply pow_pos
    rw [zero_lt_iff, ne_eq, Valuation.zero_iff, ← map_zero ι]
    exact fun h => ha (X.germToFunctionField_injective U h)
  rw [← h2] at h3
  exact (mul_le_iff_le_one_left hpos).mp h3

/-- The chart `Spec Γ(X, U)[ℐ(U)/a]` of the blow-up of `ℐ` at a nonzero `a` is nonempty. -/
private theorem nonempty_blowUpChartOpen {X : Scheme.{w}} [IsIntegral X] (ℐ : X.IdealSheafData)
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0) :
    Nonempty (blowUpChartOpen ℐ U a).1 := by
  have hW : IsAffineOpen (blowUpChartOpen ℐ U a).1 := (blowUpChartOpen ℐ U a).2
  haveI : Nontrivial Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1) := by
    haveI : Nontrivial (Localization.Away (a : Γ(X, U))) := by
      have hinj := IsLocalization.injective (Localization.Away (a : Γ(X, U)))
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
      exact ⟨⟨_, _, hinj.ne zero_ne_one⟩⟩
    exact (blowUpChartRingIso ℐ U a).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_maximal Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1)
  exact ⟨⟨hW.fromSpec (show Spec _ from ⟨p₀, hp₀.isPrime⟩), hW.range_fromSpec.subset ⟨_, rfl⟩⟩⟩

/-- On the chart `Spec Γ(X, U)[ℐ(U)/a]` of the blow-up of `ℐ`, a function `z` with `a z ∈ ℐ(U)`
is a section. -/
private theorem mem_range_germToFunctionField_blowUpChart {X : Scheme.{w}} [IsIntegral X]
    (ℐ : X.IdealSheafData) [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (U : X.affineOpens) [Nonempty (U : X.Opens)] (a : ℐ.ideal U) (ha : (a : Γ(X, U)) ≠ 0)
    [Nonempty (blowUpChartOpen ℐ U a).1] {y : Γ(X, U)} (hy : y ∈ ℐ.ideal U) {z : X.functionField}
    (hz : (X.germToFunctionField U).hom y = (X.germToFunctionField U).hom a * z) :
    functionFieldMap (blowUpToBase ℐ) z ∈
      ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom.range := by
  let ι := (X.germToFunctionField U).hom
  let χ := (blowUpChartMap ℐ U a).hom
  let ψ := ((blowUp ℐ).germToFunctionField (blowUpChartOpen ℐ U a).1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U _ (blowUpChartOpen_le ℐ U a) s
  have hfa : fβ (ι a) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero ι]
    exact fun h => ha (X.germToFunctionField_injective U h)
  obtain ⟨t, ht⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow ℐ U a (n := 1) (x := y)
    (by rwa [pow_one])
  have ht' : χ y = χ a ^ 1 * t := ht
  have := congrArg ψ ht'
  rw [pow_one, map_mul, hψχ, hψχ, hz, map_mul] at this
  exact ⟨t, (mul_left_cancel₀ hfa this).symm⟩

/-- **The chart of the blow-up, at a given ideal sheaf.** Let `ℐ(U)` contain `h₀ ≠ 0`, have
values at most `v h₀`, and contain `h₀ φ(s)` for the generators `s` of `S`, whose image `φ(S)` is
the valuation ring of `v`. Then the valuation ring of `v` is the local ring of a point of the
chart `Spec Γ(X, U)[ℐ(U)/h₀]` of the blow-up lying over `x`. -/
private theorem exists_blowUp_stalk_eq_integer_of_mem_ideal {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] {X : Scheme.{w}} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} (φ : S →+* X.functionField)
    (hφ : ∀ g, v g ≤ 1 ↔ ∃ s, φ s = g) (U : X.affineOpens) [Nonempty (U : X.Opens)] {x : X}
    (hxU : x ∈ (U : X.Opens)) (hle : ∀ a, v ((X.germToFunctionField U).hom a) ≤ 1)
    (hlt : ∀ a : Γ(X, U),
      a ∈ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal ↔ v ((X.germToFunctionField U).hom a) < 1)
    (ℐ : X.IdealSheafData) {h₀ : Γ(X, U)} (hh₀ : h₀ ∈ ℐ.ideal U) (hh₀0 : h₀ ≠ 0)
    (hJ : ∀ y ∈ ℐ.ideal U,
      v ((X.germToFunctionField U).hom y) ≤ v ((X.germToFunctionField U).hom h₀))
    (hR : ∀ r, ∃ c, (X.germToFunctionField U).hom c = φ (algebraMap R S r))
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, ∃ y ∈ ℐ.ideal U,
      (X.germToFunctionField U).hom y = (X.germToFunctionField U).hom h₀ * φ s)
    [IsIntegral (blowUp ℐ)] [IsDominant (blowUpToBase ℐ)]
    (hsurj : Function.Surjective (functionFieldMap (blowUpToBase ℐ))) :
    ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
      ∀ g : X.functionField, v g ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
        algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g := by
  let ι := (X.germToFunctionField U).hom
  let a : ℐ.ideal U := ⟨h₀, hh₀⟩
  let W := blowUpChartOpen ℐ U a
  have hW : IsAffineOpen W.1 := W.2
  have hWle : W.1 ≤ blowUpToBase ℐ ⁻¹ᵁ U := blowUpChartOpen_le ℐ U a
  let χ : Γ(X, U) →+* Γ(blowUp ℐ, W.1) := (blowUpChartMap ℐ U a).hom
  haveI : Nonempty W.1 := nonempty_blowUpChartOpen ℐ U a hh₀0
  let ψ : Γ(blowUp ℐ, W.1) →+* (blowUp ℐ).functionField :=
    ((blowUp ℐ).germToFunctionField W.1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U W.1 hWle s
  let e := RingEquiv.ofBijective fβ ⟨fβ.injective, hsurj⟩
  let w : Valuation (blowUp ℐ).functionField ℤᵐ⁰ := v.comap e.symm.toRingHom
  have hw : ∀ g, w (fβ g) = v g := fun g => by
    simp only [w, Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact congrArg v (e.symm_apply_apply g)
  have hTle : ∀ t, w (ψ t) ≤ 1 :=
    valuation_germToFunctionField_blowUpChart_le_one ℐ U a hh₀0 hw hle hJ
  have hR' : ∀ r, (fβ.comp φ) (algebraMap R S r) ∈ ψ.range := fun r =>
    (hR r).elim fun c hc => ⟨χ c, by rw [hψχ, hc, RingHom.comp_apply]⟩
  have hσ' : ∀ s ∈ Algebra.EssFiniteType.finset R S, (fβ.comp φ) s ∈ ψ.range := fun s hs =>
    (hσ s hs).elim fun _ ⟨hy, hys⟩ => mem_range_germToFunctionField_blowUpChart ℐ U a hh₀0 hy hys
  obtain ⟨𝔮, h𝔮p, h𝔮⟩ := exists_isPrime_forall_mem_iff w ψ hTle
  let P : PrimeSpectrum Γ(blowUp ℐ, W.1) := ⟨𝔮, h𝔮p⟩
  have hqW : hW.fromSpec P ∈ W.1 := hW.range_fromSpec.subset ⟨P, rfl⟩
  refine ⟨hW.fromSpec P, hom_fromSpec_eq_of_forall_mem_iff _ U.2 hW hWle P hxU fun s => ?_,
    fun g' => ?_⟩
  · change χ s ∈ 𝔮 ↔ _
    rw [h𝔮, hψχ, hw, hlt]
  letI : Algebra Γ(blowUp ℐ, W.1) ((blowUp ℐ).presheaf.stalk (hW.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨_, hqW⟩
  haveI : IsLocalization P.asIdeal.primeCompl ((blowUp ℐ).presheaf.stalk (hW.fromSpec P)) :=
    hW.isLocalization_stalk' P hqW
  haveI := functionField_isScalarTower (blowUp ℐ) W.1 ⟨_, hqW⟩
  have hμ : ∀ t, algebraMap _ (blowUp ℐ).functionField (algebraMap Γ(blowUp ℐ, W.1)
      ((blowUp ℐ).presheaf.stalk (hW.fromSpec P)) t) = ψ t := fun t => by
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  refine ⟨fun hg => ?_, fun ⟨y, hy⟩ => ?_⟩
  · obtain ⟨s, rfl⟩ := (hφ g').1 hg
    obtain ⟨_, ⟨c, rfl⟩, _, ⟨t, rfl⟩, ht, hct⟩ :=
      exists_mul_eq_of_essFiniteType w (fβ.comp φ)
        (fun s => by
          rw [RingHom.comp_apply, hw]
          exact (hφ _).2 ⟨s, rfl⟩) ψ.range hR' hσ' s
    exact exists_eq_of_mul_eq_of_isLocalization w P.asIdeal ψ _ hμ h𝔮 ht hct
  · rw [← hw, ← hy]
    exact valuation_le_one_of_isLocalization w P.asIdeal ψ _ hμ hTle h𝔮 y

/-- **The chart of the blow-up.** There are an affine open `U ∋ x` and a nonzero ideal
`J = (h₀, g₁, …, gₖ)` of `Γ(X, U)` such that, on the blow-up of any ideal sheaf restricting to `J`
on `U`, the point of the chart `Spec Γ(X, U)[J/h₀]` cut out by `𝔪_v` lies over `x` and has the
valuation ring of `v` as local ring. -/
private theorem exists_affineOpen_ideal_blowUp_stalk_eq_integer {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰}
    (hv : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ (U : X.affineOpens) (J : Ideal Γ(X, U)), x ∈ (U : X.Opens) ∧ J ≠ ⊥ ∧
      ∀ (ℐ : X.IdealSheafData), ℐ.ideal U = J → ∀ [IsIntegral (blowUp ℐ)]
        [IsDominant (blowUpToBase ℐ)], Function.Surjective (functionFieldMap (blowUpToBase ℐ)) →
        ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
          ∀ g : X.functionField, v g ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
            algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g := by
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  letI := functionFieldAlgebra sX
  obtain ⟨S, _, _, _, φ, hφ⟩ := hv
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  let ι : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  have hι : ∀ a, algebraMap Γ(X, U) X.functionField a = ι a := fun _ => rfl
  have hιle : ∀ a, v (ι a) ≤ 1 := fun a => by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]
    exact hle _
  have hιlt : ∀ a, a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ↔ v (ι a) < 1 := by
    intro a
    rw [hU.primeIdealOf_eq_map_closedPoint]
    change X.presheaf.germ U x hxU a ∈ IsLocalRing.maximalIdeal _ ↔ _
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]
    refine ⟨hlt _, fun h => ?_⟩
    by_contra hm
    exact h.ne (Valuation.Integers.one_of_isUnit' (of_not_not hm) hle)
  classical
  set σ := Algebra.EssFiniteType.finset k S
  obtain ⟨⟨h₀, hh₀⟩, hden⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors Γ(X, U)) (σ.image φ)
  have hden' : ∀ s ∈ σ, ∃ r : Γ(X, U), ι r = ι h₀ * φ s := fun s hs => by
    obtain ⟨r, hr⟩ := hden (φ s) (Finset.mem_image_of_mem _ hs)
    exact ⟨r, by rw [← hι, hr, Algebra.smul_def, hι]⟩
  choose! g hg using hden'
  have hh₀0 : h₀ ≠ 0 := nonZeroDivisors.ne_zero hh₀
  let J : Ideal Γ(X, U) := Ideal.span (insert h₀ (g '' σ))
  have hJ : ∀ y ∈ J, v (ι y) ≤ v (ι h₀) :=
    valuation_le_of_mem_span_insert v ι hιle h₀ _ (by
      rintro _ ⟨s, hs, rfl⟩
      rw [hg s hs, map_mul]
      exact mul_le_of_le_one_right' ((hφ _).2 ⟨s, rfl⟩))
  refine ⟨⟨U, hU⟩, J, hxU, ?_, fun ℐ hℐ _ _ hsurj => ?_⟩
  · rw [ne_eq, Ideal.span_eq_bot]
    push Not
    exact ⟨h₀, Set.mem_insert _ _, hh₀0⟩
  have hmemJ : ∀ y ∈ J, y ∈ ℐ.ideal ⟨U, hU⟩ := fun y hy => hℐ ▸ hy
  exact exists_blowUp_stalk_eq_integer_of_mem_ideal φ.toRingHom
    (fun g => (hφ g).trans (AlgHom.mem_range φ)) ⟨U, hU⟩ hxU hιle hιlt ℐ
    (hmemJ _ (Ideal.subset_span (Set.mem_insert _ _))) hh₀0 (fun y hy => hJ y (hℐ ▸ hy))
    (fun r => by
      obtain ⟨c, hc⟩ := exists_germToFunctionField_eq_algebraMap sX U r
      exact ⟨c, hc.trans (φ.commutes r).symm⟩)
    (fun s hs => ⟨g s, hmemJ _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩)),
      hg s hs⟩) hsurj

/-- **The blow-up step.** There is a projective birational `β : X₂ ⟶ X` from a variety and a
point `q ↦ x` of `X₂` whose local ring, inside `k(X)`, is the valuation ring of `v`. -/
private theorem exists_blowUp_stalk_eq_integer {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰}
    (hv : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ (X₂ : Scheme.{w}) (β : X₂ ⟶ X) (_ : AlgebraicGeometry.IsVariety k (β ≫ sX))
      (hβ : IsBirationalMorphism β),
      IsProjective β ∧ ∃ q : X₂, β q = x ∧
        haveI : IsDominant β := hβ.isDominant
        ∀ g : X.functionField, v g ≤ 1 ↔
          ∃ a : X₂.presheaf.stalk q, algebraMap _ X₂.functionField a = functionFieldMap β g := by
  obtain ⟨U, J, -, hJ, hchart⟩ := exists_affineOpen_ideal_blowUp_stalk_eq_integer sX hv x hle hlt
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  obtain ⟨ℐ, hℐ⟩ := exists_idealSheafData_ideal_eq U J
  have hℐ0 : ℐ ≠ ⊥ := by
    rintro rfl
    exact hJ (hℐ.symm.trans rfl)
  obtain ⟨hvar, hproj, hbir⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX ℐ hℐ0
  haveI : IsIntegral (blowUp ℐ) := hvar.toIsIntegral
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  haveI : IsProper (blowUpToBase ℐ) := hproj.isProper
  have hβ := isBirationalMorphism_of_isBirational (blowUpToBase ℐ) hbir
  haveI : IsDominant (blowUpToBase ℐ) := hβ.isDominant
  obtain ⟨q, hq, hstalk⟩ := hchart ℐ hℐ hβ.functionFieldMap_bijective.2
  exact ⟨blowUp ℐ, blowUpToBase ℐ, hvar, hβ, hproj, q, hq, hstalk⟩

/-- **The normalization step.** The normalization of a variety is a finite, hence projective,
birational morphism from a normal variety, and it is an isomorphism on local rings over a point
whose local ring is a valuation ring. -/
private theorem exists_normalization_isIso_stalkMap {k : Type w} [Field k] {Y : Scheme.{w}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] (q : Y)
    [ValuationRing (Y.presheaf.stalk q)] :
    ∃ (Z : Scheme.{w}) (ν : Z ⟶ Y), IsNormalVariety k (ν ≫ sY) ∧ IsProjective ν ∧
      IsBirationalMorphism ν ∧ ∃ z : Z, ν z = q ∧ IsIso (ν.stalkMap z) := by
  let ν := normalizationOverField k sY
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k sY
  have hbir : IsBirational ν := Scheme.isBirational_normalization Y hX
  haveI : IsFinite ν := isFinite_normalizationOverField k sY
  haveI hvar : AlgebraicGeometry.IsVariety k (ν ≫ sY) := isVariety_normalizationOverField k sY
  haveI : IsIntegral (normalizationSchemeOverField k sY) := hvar.toIsIntegral
  have hνb : IsBirationalMorphism ν := isBirationalMorphism_of_isBirational ν hbir
  haveI : IsDominant ν := hνb.isDominant
  obtain ⟨z, hz⟩ := (Scheme.surjective_normalization Y hX).surj q
  refine ⟨_, ν, ⟨hvar, Scheme.isNormal_normalizationScheme Y hX⟩,
    Stacks.FiniteMorphismProjective.isProjective_of_isFinite ν, hνb, z, hz, ?_⟩
  subst hz
  exact isIso_stalkMap_of_valuationRing ν hνb.functionFieldMap_bijective.2 z

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{w}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{w}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{w}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

/-- Transport of "the local ring at `ν z` is a given subset of `k(X)`" along a morphism `ν`
which is an isomorphism on local rings at `z`. -/
private theorem forall_iff_exists_stalk_comp {X Y Z : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (ν : Z ⟶ Y) (β : Y ⟶ X) [IsDominant ν] [IsDominant β] [IsDominant (ν ≫ β)]
    (z : Z) [IsIso (ν.stalkMap z)] (S : Set X.functionField)
    (hq : ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Y.presheaf.stalk (ν z), algebraMap _ Y.functionField a = functionFieldMap β g) :
    ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap (ν ≫ β) g := by
  intro g
  rw [hq g]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(ν.stalkMap z).hom a, ?_⟩
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, ha,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · rintro ⟨b, hb⟩
    refine ⟨(inv (ν.stalkMap z)).hom b, (functionFieldMap ν).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ← hb]
    congr 1
    exact congrArg (fun φ => φ.hom b) (IsIso.inv_hom_id (ν.stalkMap z))

/-- Two equivalent `ℤᵐ⁰`-valued valuations of a field which both take the value `exp (-1)` are
equal. -/
private theorem eq_of_isEquiv_of_exp_neg_one {K : Type*} [Field K] {w₁ w₂ : Valuation K ℤᵐ⁰}
    (h : w₁.IsEquiv w₂) (h₁ : ∃ a, w₁ a = WithZero.exp (-1))
    (h₂ : ∃ a, w₂ a = WithZero.exp (-1)) : w₁ = w₂ := by
  obtain ⟨ϖ, hϖ⟩ := h₁
  obtain ⟨ϖ', hϖ'⟩ := h₂
  have hpow : ∀ (w : Valuation K ℤᵐ⁰) (c : ℤ), w ϖ = WithZero.exp c → ∀ n : ℤ,
      w (ϖ ^ n) = WithZero.exp (c * n) := by
    intro w c hc n
    rw [map_zpow₀, hc, ← WithZero.exp_zsmul, smul_eq_mul, mul_comm]
  have hw₂ϖ : w₂ ϖ ≠ 0 := by
    rw [ne_eq, ← h.eq_zero, hϖ]; exact WithZero.exp_ne_zero
  set a := WithZero.log (w₂ ϖ)
  have ha : w₂ ϖ = WithZero.exp a := (WithZero.exp_log hw₂ϖ).symm
  have hw₁ϖ' : w₁ ϖ' ≠ 0 := by
    rw [ne_eq, h.eq_zero, hϖ']; exact WithZero.exp_ne_zero
  set b := WithZero.log (w₁ ϖ')
  have hb : w₁ ϖ' = WithZero.exp b := (WithZero.exp_log hw₁ϖ').symm
  have hab : w₂ ϖ' = WithZero.exp (a * -b) := by
    rw [← hpow w₂ a ha]
    exact (h.eq_iff).mp (by rw [hb, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [hϖ', WithZero.exp_inj] at hab
  have ha0 : a < 0 := by
    have : w₂ ϖ < 1 := (Valuation.isEquiv_iff_val_lt_one.mp h).mp
      (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    rwa [ha, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have ha1 : a = -1 := by
    have : a * b = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h <;> omega
  ext g
  by_cases hg : g = 0
  · simp [hg]
  have hg1 : w₁ g ≠ 0 := by simp [hg]
  set m := WithZero.log (w₁ g)
  have hm : w₁ g = WithZero.exp m := (WithZero.exp_log hg1).symm
  have : w₂ g = w₂ (ϖ ^ (-m)) :=
    (h.eq_iff).mp (by rw [hm, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [this, hpow w₂ a ha, hm, ha1]; congr 1; ring

/-- If the local ring of `Z` at `z` is, inside `k(X)`, the valuation ring of a valuation taking
the value `exp (-1)`, it is not a field. -/
private theorem not_isField_stalk_of_forall_le_one_iff {X Z : Scheme.{w}} [IsIntegral X]
    [IsIntegral Z] (h : Z ⟶ X) [IsDominant h] (v : Valuation X.functionField ℤᵐ⁰) (z : Z)
    (hz : ∀ g : X.functionField, v g ≤ 1 ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g)
    {g₀ : X.functionField} (hg₀ : v g₀ = WithZero.exp (-1)) :
    ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  obtain ⟨a, ha⟩ := (hz g₀).1 (by rw [hg₀, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero, ← v.zero_iff, hg₀] at ha
    exact WithZero.exp_ne_zero ha
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
  have hb' : v g₀⁻¹ ≤ 1 := (hz _).2 ⟨b, by
    rw [map_inv₀, ← ha]
    exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, hb, map_one])⟩
  rw [map_inv₀, hg₀, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb'
  omega

/-- **The assembly step.** On a normal locally noetherian integral scheme `Z` dominating `X`, a
point `z` whose local ring is, inside `k(X)`, the valuation ring of a divisor `v` of `k(X)`, is
the generic point of a prime divisor `F` with `ord_F = v`. -/
private theorem exists_primeDivisor_valuationOver_eq {k : Type w} [Field k] {X : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] {v : Valuation X.functionField ℤᵐ⁰}
    (hv₁ : ∃ g, v g = WithZero.exp (-1)) {Z : Scheme.{w}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (h : Z ⟶ X) (hh : IsBirationalMorphism h) (z : Z)
    (hz : haveI : IsDominant h := hh.isDominant
      ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g) :
    ∃ F : MMP.Mori.PrimeDivisor Z, F.genericPoint = z ∧
      haveI : IsDominant h := hh.isDominant
      F.valuationOver h = v := by
  haveI : IsDominant h := hh.isDominant
  haveI := valuationRing_stalk_of_forall_le_one_iff h hh v z hz
  obtain ⟨g₀, hg₀⟩ := hv₁
  have hnf := not_isField_stalk_of_forall_le_one_iff h v z hz hg₀
  haveI : IsDiscreteValuationRing (Z.presheaf.stalk z) :=
    ((IsDiscreteValuationRing.TFAE (Z.presheaf.stalk z) hnf).out 1 2).mpr ‹_›
  have hcoh : Order.coheight z = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh, ?_⟩
  set F : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh
  have hF : F.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh
  have hrange : ∀ r : Z.functionField,
      r ∈ (algebraMap F.localRing Z.functionField).range ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = r := by
    intro r
    change (∃ a : Z.presheaf.stalk F.genericPoint, _) ↔ _
    clear_value F
    subst hF
    rfl
  apply eq_of_isEquiv_of_exp_neg_one
  · refine Valuation.isEquiv_iff_val_le_one.mpr fun {g} => ?_
    rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.divisorialValuation_le_one_iff, hrange,
      hz g]
  · haveI := F.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
    obtain ⟨g, hg⟩ := hh.functionFieldMap_bijective.2 (algebraMap F.localRing Z.functionField ϖ)
    refine ⟨g, ?_⟩
    rw [PrimeDivisor.valuationOver_apply, hg]
    exact F.divisorialValuation_algebraMap_of_irreducible hϖ
  · exact ⟨g₀, hg₀⟩

/-- A normalized discrete valuation `v` of `k(X)` whose valuation ring is essentially of finite
type over `k` and dominates `𝒪_{X,x}` is `ord_F` for a divisor `(Z, h, F)` over `X`, `h`
projective with `h(η_F) = x`. -/
private theorem exists_properDivisorOver_of_essFiniteType {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰}
    (hv : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range)
    (hv₁ : ∃ g, v g = WithZero.exp (-1)) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ D : ProperDivisorOver k sX, IsProjective D.f ∧ D.valuation = v ∧
      D.f D.E.genericPoint = x := by
  obtain ⟨X₂, β, hvar₂, hβ, hprojβ, q, hqx, hq⟩ :=
    exists_blowUp_stalk_eq_integer sX hv x hle hlt
  haveI : IsIntegral X₂ := hvar₂.toIsIntegral
  haveI : IsDominant β := hβ.isDominant
  obtain ⟨Z, ν, hZ, hprojν, hν, z, hzq, hiso⟩ :=
    haveI := valuationRing_stalk_of_forall_le_one_iff β hβ v q hq
    exists_normalization_isIso_stalkMap (β ≫ sX) q
  subst hzq
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hh : IsBirationalMorphism (ν ≫ β) := isBirationalMorphism_comp hν hβ
  have hZ' : IsNormalVariety k ((ν ≫ β) ≫ sX) := by rwa [Category.assoc]
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI : LocallyOfFiniteType ((ν ≫ β) ≫ sX) := hZ'.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((ν ≫ β) ≫ sX)
  haveI : IsDominant ν := hν.isDominant
  haveI : IsDominant (ν ≫ β) := hh.isDominant
  have hz := forall_iff_exists_stalk_comp ν β z {g | v g ≤ 1} hq
  obtain ⟨F, hFz, hFv⟩ := exists_primeDivisor_valuationOver_eq sX hv₁ (ν ≫ β) hh z hz
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  have hproj : IsProjective (ν ≫ β) :=
    IsProjective.comp hprojν hprojβ
  refine ⟨⟨⟨Z, ν ≫ β, hZ', hh, F⟩, hproj.isProper⟩, hproj, hFv, ?_⟩
  change (ν ≫ β) F.genericPoint = x
  rw [hFz, Scheme.Hom.comp_apply, hqx]

end Realization

/-- The morphisms `Xᵢ ⟶ X` of a Zariski sequence. -/
private noncomputable def toBase {B : Type u} [CommRing B] [IsLocalRing B] {X : Scheme.{u}}
    {f : Spec (.of B) ⟶ X} (S : MMP.Mori.ZariskiSequence X f) : ∀ i, S.obj i ⟶ X
  | 0 => eqToHom S.obj_zero
  | i + 1 => S.β i ≫ toBase S i

private theorem mor_comp_toBase {B : Type u} [CommRing B] [IsLocalRing B] {X : Scheme.{u}}
    {f : Spec (.of B) ⟶ X} (S : MMP.Mori.ZariskiSequence X f) :
    ∀ i, S.mor i ≫ toBase S i = f
  | 0 => S.mor_zero
  | i + 1 => by rw [toBase, ← Category.assoc, S.mor_succ_comp_β, mor_comp_toBase S i]

private theorem locallyOfFiniteType_toBase_comp {B : Type u} [CommRing B] [IsLocalRing B]
    {k : Type u} [Field k] {X : Scheme.{u}} {f : Spec (.of B) ⟶ X}
    (S : MMP.Mori.ZariskiSequence X f) (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    ∀ i, LocallyOfFiniteType (toBase S i ≫ sX)
  | 0 => by rw [toBase]; infer_instance
  | i + 1 => by
    have := locallyOfFiniteType_toBase_comp S sX i
    have : IsLocallyNoetherian (S.obj i) :=
      LocallyOfFiniteType.isLocallyNoetherian (toBase S i ≫ sX)
    have : LocallyOfFiniteType (S.β i) := by rw [S.β_eq]; infer_instance
    rw [toBase, Category.assoc]; infer_instance

/-- The global sections of a morphism from the spectrum of a local ring, read through the
stalk at the image of the closed point. -/
private theorem germ_top_stalkClosedPointTo {B : Type u} [CommRing B] [IsLocalRing B]
    {Y : Scheme.{u}} (g : Spec (.of B) ⟶ Y) :
    Y.presheaf.germ ⊤ (g (IsLocalRing.closedPoint B)) trivial ≫ Scheme.stalkClosedPointTo g =
      g.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom := by
  rw [Scheme.germ_stalkClosedPointTo g ⊤ trivial]
  simp only [Scheme.Hom.appTop]
  congr 1

/-- If `v ≤ 1` on a local ring `A → K` and `v < 1` on its maximal ideal, then `A` maps to the
valuation ring of `v` by a local homomorphism. -/
private theorem isLocalHom_codRestrict_valuationSubring {A K : Type*} [CommRing A]
    [IsLocalRing A] [Field K] [Algebra A K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (hA : ∀ a : A, algebraMap A K a ∈ v.valuationSubring.toSubring)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal A, v (algebraMap A K a) < 1) :
    IsLocalHom ((algebraMap A K).codRestrict v.valuationSubring.toSubring hA) := by
  let R := v.valuationSubring.toSubring
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 := hlt a ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  obtain ⟨u, hu⟩ := ha
  have hb : v ((u⁻¹ : Rˣ) : K) ≤ 1 := (v.mem_valuationSubring_iff _).mp (u⁻¹ : Rˣ).1.2
  have h2 : algebraMap A K a * ((u⁻¹ : Rˣ) : K) = 1 := by
    have := congrArg Subtype.val (u.mul_inv)
    rw [hu] at this
    exact this
  have h3 := congrArg v h2
  rw [map_mul, map_one] at h3
  exact lt_irrefl (1 : Γ) (h3.symm.trans_le (mul_le_of_le_one_right' hb) |>.trans_lt h1)

/-- **Zariski's characterization of divisorial valuations** (Kollár–Mori, Lemma 2.45). On a
variety `X` over `k`, the valuation ring of a normalized discrete valuation `v` of `k(X)` which
dominates a local ring `𝒪_{X,x}` and whose residue field has transcendence degree `dim X - 1`
over `k` is essentially of finite type over `k`: it is the local ring of a point of a variety
obtained from `X` by a Zariski sequence of blow-ups. -/
private theorem exists_essFiniteType_of_trdeg_residueField (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX)
    (v : Valuation X.functionField ℤᵐ⁰) (hv₁ : ∃ g, v g = exp (-1)) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1)
    (htrdeg : letI := residueAlgebra sX v x hle
      (((Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring)).toENat + 1 : ℕ∞) :
        WithBot ℕ∞) = topologicalKrullDim X) :
    letI := MMP.Mori.functionFieldAlgebra sX
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
      (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  haveI : IsSeparated (X ↘ Spec (.of k)) := hX.toIsSeparated
  haveI : QuasiCompact (X ↘ Spec (.of k)) := hX.toQuasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := isRankOneDiscrete_of_exists_eq_exp_neg_one v hv₁
  let R : Subring X.functionField := v.valuationSubring.toSubring
  haveI : IsDiscreteValuationRing R := inferInstanceAs (IsDiscreteValuationRing v.valuationSubring)
  have hR : ∀ s : X.presheaf.stalk x, algebraMap _ X.functionField s ∈ R :=
    fun s => (v.mem_valuationSubring_iff _).mpr (hle s)
  have hdom := isLocalHom_codRestrict_valuationSubring v hR hlt
  set f := MMP.Mori.fromSpecOfStalkLE x R hR
  obtain ⟨⟨Z⟩, hSE⟩ := MMP.Mori.ZariskiSequence.nonempty_and_forall_isIntegral x R
    (IsDiscreteValuationRing.not_isField R) hR hdom
  obtain ⟨n, hn⟩ := MMP.Mori.ZariskiSequence.exists_isIso_stalkClosedPointTo x R hR hdom htrdeg Z
  haveI : IsIntegral (Z.obj n) := (hSE Z n).1
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo (Z.mor n))
  haveI : LocallyOfFiniteType (toBase Z n ≫ sX) := locallyOfFiniteType_toBase_comp Z sX n
  let cR := (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict R hR
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.stalkAlgebra (toBase Z n ≫ sX) (Z.mor n (IsLocalRing.closedPoint R))
  haveI := essFiniteType_stalkAlgebra (toBase Z n ≫ sX) (Z.mor n (IsLocalRing.closedPoint R))
  have h3 : X.presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo f =
      X.presheaf.germ ⊤ x trivial ≫ CommRingCat.ofHom cR :=
    Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ ⊤ trivial
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (toBase Z n ≫ sX).appTop ≫
      (Z.obj n).presheaf.germ ⊤ (Z.mor n (IsLocalRing.closedPoint R)) trivial ≫
      Scheme.stalkClosedPointTo (Z.mor n) = (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ CommRingCat.ofHom cR := by
    rw [germ_top_stalkClosedPointTo, ← Scheme.Hom.comp_appTop_assoc,
      show Z.mor n ≫ toBase Z n ≫ sX = f ≫ sX by rw [← Category.assoc, mor_comp_toBase],
      Scheme.Hom.comp_appTop_assoc, ← germ_top_stalkClosedPointTo f, h3]
  have hcomm : ∀ c : k, (((Scheme.stalkClosedPointTo (Z.mor n)).hom (algebraMap k _ c) : R) :
      X.functionField) = algebraMap k X.functionField c := by
    intro c
    exact (congrArg (fun φ => ((φ.hom c : R) : X.functionField)) key).trans
      (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := ⊤) (x := x)
        (TopologicalSpace.Opens.mem_top x) _)
  let φ : (Z.obj n).presheaf.stalk (Z.mor n (IsLocalRing.closedPoint R)) →ₐ[k] X.functionField :=
    { toRingHom := R.subtype.comp (Scheme.stalkClosedPointTo (Z.mor n)).hom
      commutes' := hcomm }
  refine ⟨_, inferInstance, inferInstance, inferInstance, φ, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := hbij.2 ⟨g, (v.mem_valuationSubring_iff g).mpr hg⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact (v.mem_valuationSubring_iff _).mp ((Scheme.stalkClosedPointTo (Z.mor n)).hom c).2

/-- A dominant, locally quasi-finite morphism of varieties preserves dimension: the function
fields have the same transcendence degree, the extension being finite. -/
private theorem topologicalKrullDim_eq_of_locallyQuasiFinite (k : Type u) [Field k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ] (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀)
    [LocallyOfFiniteType s₀] [LocallyOfFiniteType (q ≫ s₀)] [IsDominant q]
    [LocallyQuasiFinite q] : topologicalKrullDim Yₑ = topologicalKrullDim Y₀ := by
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
  letI := MMP.Mori.functionFieldAlgebra s₀
  letI := MMP.Mori.functionFieldAlgebra (q ≫ s₀)
  letI := MMP.Mori.functionFieldMapAlgebra q
  haveI := MMP.Mori.isScalarTower_functionFieldMap s₀ q
  haveI : Module.Finite Y₀.functionField Yₑ.functionField :=
    finite_functionField_of_locallyQuasiFinite q
  rw [← MMP.Mori.toENat_trdeg_functionField (sX := q ≫ s₀),
    ← MMP.Mori.toENat_trdeg_functionField (sX := s₀), ← trdeg_add_eq k Y₀.functionField,
    trdeg_eq_zero (R := Y₀.functionField) (A := Yₑ.functionField), add_zero]

/-- An algebraic extension `L / K` has the same transcendence degree over `k` as `K`. -/
private theorem trdeg_eq_of_isAlgebraic (k : Type*) {K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] [Algebra.IsAlgebraic K L] :
    Algebra.trdeg k L = Algebra.trdeg k K := by
  haveI : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).mpr (algebraMap K L).injective
  rw [← trdeg_add_eq k K (A := L), trdeg_eq_zero (R := K) (A := L), add_zero]

/-- A ring homomorphism into `L` landing in the image of an injective `algebraMap O L` factors
through `O`. -/
private theorem exists_ringHom_algebraMap_eq {A O L : Type*} [CommRing A] [CommRing O]
    [CommRing L] [Algebra O L] (hinj : Function.Injective (algebraMap O L)) (f : A →+* L)
    (hf : ∀ a, f a ∈ (algebraMap O L).range) :
    ∃ β : A →+* O, ∀ a, algebraMap O L (β a) = f a := by
  let ι : O ≃+* (algebraMap O L).range := RingEquiv.ofBijective (algebraMap O L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  exact ⟨ι.symm.toRingHom.comp (f.codRestrict _ hf), fun a =>
    congrArg Subtype.val (ι.apply_symm_apply ⟨_, hf a⟩)⟩

/-- A ring homomorphism from the valuation ring of `w` to a local ring `O`, sending the elements
of value `< 1` into the maximal ideal, is local. -/
private theorem isLocalHom_of_lt_one {K O : Type*} [Field K] [CommRing O] [IsLocalRing O]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (β : w.valuationSubring →+* O)
    (hβ : ∀ a : w.valuationSubring, w (a : K) < 1 → β a ∈ IsLocalRing.maximalIdeal O) :
    IsLocalHom β := by
  refine ⟨fun a ha => ?_⟩
  have h1 : w a = 1 := le_antisymm ((w.mem_valuationSubring_iff _).mp a.2)
    (not_lt.mp fun hlt => (IsLocalRing.mem_maximalIdeal _).mp (hβ a hlt) ha)
  have ha0 : (a : K) ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  exact IsUnit.of_mul_eq_one (a := a) ⟨(a : K)⁻¹,
    (w.mem_valuationSubring_iff _).mpr (by rw [map_inv₀, h1, inv_one])⟩
    (Subtype.ext (mul_inv_cancel₀ ha0))

/-- The valuation ring of `v(E, Y)` maps to the local ring of `Y` at the generic point of `E`,
compatibly with `k(X) → k(Y)`, by a local homomorphism inducing a surjection of residue fields. -/
private theorem exists_isLocalHom_surjective_residueField_map {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} (D : MMP.Mori.DivisorOver k sX) :
    haveI := D.isIntegral
    haveI := D.isDominant
    ∃ β : D.valuation.valuationSubring →+* D.Y.presheaf.stalk D.E.genericPoint,
      ∃ _ : IsLocalHom β, (∀ a, algebraMap _ D.Y.functionField (β a) = functionFieldMap D.f a) ∧
        Function.Surjective (IsLocalRing.ResidueField.map β) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  set O := D.Y.presheaf.stalk D.E.genericPoint
  have hinj := IsFractionRing.injective O D.Y.functionField
  obtain ⟨β, hβ⟩ := exists_ringHom_algebraMap_eq hinj
    ((functionFieldMap D.f).comp D.valuation.valuationSubring.subtype) fun a =>
      (D.E.divisorialValuation_le_one_iff _).mp ((D.valuation.mem_valuationSubring_iff _).mp a.2)
  haveI : IsLocalHom β := isLocalHom_of_lt_one D.valuation β fun a hlt => by
    have : D.E.divisorialValuation (algebraMap O D.Y.functionField (β a)) < 1 := by
      rw [hβ]
      exact hlt
    exact (D.E.divisorialValuation_algebraMap_lt_one_iff _).mp this
  refine ⟨β, inferInstance, hβ, fun z => ?_⟩
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨g, hg⟩ := (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
    D.isBirationalMorphism).2 (algebraMap O _ s)
  have hg1 : D.valuation g ≤ 1 := by
    change D.E.divisorialValuation (functionFieldMap D.f g) ≤ 1
    rw [hg]
    exact (D.E.divisorialValuation_le_one_iff _).mpr ⟨s, rfl⟩
  refine ⟨IsLocalRing.residue _ ⟨g, (D.valuation.mem_valuationSubring_iff _).mpr hg1⟩, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  congr 1
  exact hinj ((hβ _).trans hg)

/-- The constants `k` of `k(X)`, read on the local ring of `x` and pulled back along dominant
morphisms `Z ⟶ Y ⟶ X`, are the constants of `k(Z)`, read on the local ring of `z`. -/
private theorem functionFieldMap_comp_algebraMap_germ_appTop {k : Type u} [Field k]
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (s : X ⟶ Spec (.of k))
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f] [IsDominant g] (x : X) (z : Z) (c : k) :
    functionFieldMap g (functionFieldMap f (algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))))) =
      algebraMap (Z.presheaf.stalk z) Z.functionField ((Z.presheaf.germ ⊤ z trivial).hom
        ((g ≫ f ≫ s).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) := by
  letI := MMP.Mori.functionFieldAlgebra s
  letI := MMP.Mori.functionFieldAlgebra (f ≫ s)
  letI := MMP.Mori.functionFieldAlgebra (g ≫ f ≫ s)
  have t1 := MMP.Mori.isScalarTower_functionFieldMap s f
  have t2 := MMP.Mori.isScalarTower_functionFieldMap (f ≫ s) g
  have e1 : functionFieldMap f (algebraMap k X.functionField c) =
      algebraMap k Y.functionField c :=
    (@IsScalarTower.algebraMap_apply _ _ _ _ _ _ _ (MMP.Mori.functionFieldMapAlgebra f)
      _ t1 c).symm
  have e2 : functionFieldMap g (algebraMap k Y.functionField c) =
      algebraMap k Z.functionField c :=
    (@IsScalarTower.algebraMap_apply _ _ _ _ _ _ _ (MMP.Mori.functionFieldMapAlgebra g)
      _ t2 c).symm
  have s1 := MMP.Mori.isScalarTower_stalk_functionField s x
  have s2 := MMP.Mori.isScalarTower_stalk_functionField (g ≫ f ≫ s) z
  have f1 : algebraMap (X.presheaf.stalk x) X.functionField
      ((X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
      algebraMap k X.functionField c :=
    (@IsScalarTower.algebraMap_apply _ _ _ _ _ _ (MMP.Mori.stalkAlgebra s x) _ _ s1 c).symm
  have f2 : algebraMap (Z.presheaf.stalk z) Z.functionField ((Z.presheaf.germ ⊤ z trivial).hom
      ((g ≫ f ≫ s).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) =
      algebraMap k Z.functionField c :=
    (@IsScalarTower.algebraMap_apply _ _ _ _ _ _
      (MMP.Mori.stalkAlgebra (g ≫ f ≫ s) z) _ _ s2 c).symm
  rw [f1, e1, e2, f2]

/-- The residue field of `v`, where `v ^ e` is the restriction of `w = ord_E`, and the residue
field `k(E)` of `E` have the same transcendence degree over `k`: through the finite extension
`k(Y_e) / k(Y₀)`, `k(E)` is a finite extension of the residue field of `v`. -/
private theorem trdeg_residueField_eq_trdeg_residueField_genericPoint (k : Type u) [Field k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ] (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀)
    (hₑ : IsVariety k (q ≫ s₀)) [IsDominant q] [LocallyQuasiFinite q]
    (D : MMP.Mori.DivisorOver k (q ≫ s₀))
    (v : Valuation Y₀.functionField ℤᵐ⁰) (e : ℕ) (he : 0 < e)
    (hv : ∀ g, D.valuation (functionFieldMap q g) = v g ^ e) (x : Y₀)
    (hle : ∀ a : Y₀.presheaf.stalk x, v (algebraMap _ Y₀.functionField a) ≤ 1) :
    letI := residueAlgebra s₀ v x hle
    letI : Algebra k (D.Y.residueField D.E.genericPoint) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.f ≫ q ≫ s₀).appTop ≫
        D.Y.Γevaluation D.E.genericPoint).hom.toAlgebra
    Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring) =
      Algebra.trdeg k (D.Y.residueField D.E.genericPoint) := by
  letI := residueAlgebra s₀ v x hle
  letI : Algebra k (D.Y.residueField D.E.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.f ≫ q ≫ s₀).appTop ≫
      D.Y.Γevaluation D.E.genericPoint).hom.toAlgebra
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (q ≫ s₀) := hₑ.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q s₀
  letI := (functionFieldMap q).toAlgebra
  haveI : FiniteDimensional Y₀.functionField Yₑ.functionField :=
    finite_functionField_of_locallyQuasiFinite q
  haveI := isRankOneDiscrete_divisorOver_valuation D
  haveI : v.HasExtension D.valuation := ⟨fun a b => by
    change _ ↔ D.valuation (functionFieldMap q a) ≤ D.valuation (functionFieldMap q b)
    rw [hv, hv, pow_le_pow_iff_left₀ zero_le' zero_le' he.ne']⟩
  set κv := IsLocalRing.ResidueField v.valuationSubring
  set κw := IsLocalRing.ResidueField D.valuation.valuationSubring
  letI : Algebra k κw := ((algebraMap κv κw).comp (algebraMap k κv)).toAlgebra
  haveI : IsScalarTower k κv κw := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite κv κw :=
    (MMP.Valuation.isRankOneDiscrete_and_relIndex_ne_zero_and_finite_residueField_of_hasExtension
      v D.valuation).2.2
  haveI : Algebra.IsAlgebraic κv κw := Algebra.IsAlgebraic.of_finite κv κw
  rw [← trdeg_eq_of_isAlgebraic k (K := κv) (L := κw)]
  set O := D.Y.presheaf.stalk D.E.genericPoint
  have hinj := IsFractionRing.injective O D.Y.functionField
  obtain ⟨β, _, hβ, hsurj⟩ := exists_isLocalHom_surjective_residueField_map D
  let B₀ : κw →+* D.Y.residueField D.E.genericPoint := IsLocalRing.ResidueField.map β
  have hcomm : ∀ c : k, B₀ (algebraMap k κw c) =
      algebraMap k (D.Y.residueField D.E.genericPoint) c := by
    intro c
    change IsLocalRing.ResidueField.map β
        (IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ _)) =
      (D.Y.presheaf.germ ⊤ D.E.genericPoint trivial ≫ D.Y.residue _).hom _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue O _ = IsLocalRing.residue O _
    congr 1
    apply hinj
    rw [hβ]
    exact functionFieldMap_comp_algebraMap_germ_appTop s₀ q D.f x D.E.genericPoint c
  exact (AlgEquiv.ofBijective { B₀ with commutes' := hcomm } ⟨B₀.injective, hsurj⟩).trdeg_eq

/-- The residue field of `v`, where `v ^ e` is the restriction of `w = ord_E` along the finite
extension `k(Y_e) / k(Y₀)`, has transcendence degree `dim Y₀ - 1` over `k`: the residue field of
`w` is `k(E)`, of transcendence degree `dim Y_e - 1 = dim Y₀ - 1`, and it is a finite extension
of the residue field of `v` (the valuation rings of `v` and `v ^ e` agree). -/
private theorem trdeg_residueField_of_pow_eq (k : Type u) [Field k] {Y₀ Yₑ : Scheme.{u}}
    [IsIntegral Y₀] [IsIntegral Yₑ] (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀)
    (h₀ : IsVariety k s₀) (hₑ : IsVariety k (q ≫ s₀)) [IsDominant q] [LocallyQuasiFinite q]
    (D : MMP.Mori.DivisorOver k (q ≫ s₀))
    (v : Valuation Y₀.functionField ℤᵐ⁰) (e : ℕ) (he : 0 < e)
    (hv : ∀ g, D.valuation (functionFieldMap q g) = v g ^ e) (x : Y₀)
    (hle : ∀ a : Y₀.presheaf.stalk x, v (algebraMap _ Y₀.functionField a) ≤ 1) :
    letI := residueAlgebra s₀ v x hle
    (((Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring)).toENat + 1 : ℕ∞) :
      WithBot ℕ∞) = topologicalKrullDim Y₀ := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := D.E.isDiscreteValuationRing_localRing
  haveI : LocallyOfFiniteType s₀ := h₀.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ s₀) := hₑ.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (D.f ≫ q ≫ s₀) := D.isNormalVariety.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety k (q ≫ s₀) := hₑ
  haveI : MMP.Mori.IsVariety k (D.f ≫ q ≫ s₀) := D.isNormalVariety.1
  rw [trdeg_residueField_eq_trdeg_residueField_genericPoint k s₀ q hₑ D v e he hv x hle,
    ← topologicalKrullDim_eq_of_locallyQuasiFinite k s₀ q,
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (q ≫ s₀) (D.f ≫ q ≫ s₀)
      D.isBirationalMorphism,
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k D.Y (D.f ≫ q ≫ s₀)
      D.E.genericPoint,
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k D.Y (D.f ≫ q ≫ s₀) D.E.genericPoint]
  haveI : IsDiscreteValuationRing (D.Y.presheaf.stalk D.E.genericPoint) :=
    D.E.isDiscreteValuationRing_localRing
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
  rfl

end Helpers

/-- The restriction of a normalized divisorial valuation `w` of `k(Y_e)` along a dominant,
locally quasi-finite morphism of `k`-varieties `q : Y_e ⟶ Y₀` is a positive power (an
integer multiple, additively) of a normalized divisorial valuation `v` of `k(Y₀)`. This covers
a finite surjective morphism of normal varieties, which is dominant and locally quasi-finite. -/
@[mmp "lem_oai4_c2_restriction_divisorial", mmp "lem_mmp_finite_divisorial_valuation_restriction"]
public theorem exists_isNormalizedDivisorialValuation_comap_eq_pow
    (k : Type u) [Field k] {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsIntegral Yₑ]
    (s₀ : Y₀ ⟶ Spec (.of k)) (q : Yₑ ⟶ Y₀) (h₀ : IsVariety k s₀) (hₑ : IsVariety k (q ≫ s₀))
    [IsDominant q] [LocallyQuasiFinite q]
    (w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ)))
    (hw : MMP.Intersection.IsNormalizedDivisorialValuation k (q ≫ s₀) w) :
    ∃ v : Valuation Y₀.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsNormalizedDivisorialValuation k s₀ v ∧
      ∃ e : ℕ, 0 < e ∧ ∀ g : Y₀.functionField, w (functionFieldMap q g) = v g ^ e := by
  obtain ⟨D, hD, rfl⟩ := hw
  haveI : LocallyOfFiniteType q :=
    haveI := hₑ.toLocallyOfFiniteType
    locallyOfFiniteType_of_comp q s₀
  letI := (functionFieldMap q).toAlgebra
  haveI : FiniteDimensional Y₀.functionField Yₑ.functionField :=
    finite_functionField_of_locallyQuasiFinite q
  haveI := isRankOneDiscrete_divisorOver_valuation D
  let r := D.valuation.comap (algebraMap Y₀.functionField Yₑ.functionField)
  haveI : r.HasExtension D.valuation := ⟨fun _ _ => Iff.rfl⟩
  haveI : r.IsRankOneDiscrete :=
    (MMP.Valuation.isRankOneDiscrete_and_relIndex_ne_zero_and_finite_residueField_of_hasExtension
      r D.valuation).1
  obtain ⟨v, e, he, hrv, hv₁⟩ := exists_pow_eq_of_isRankOneDiscrete r
  have hv : ∀ g, D.valuation (functionFieldMap q g) = v g ^ e := hrv
  haveI : IsVariety k s₀ := h₀
  obtain ⟨x, hle, hlt⟩ := exists_dominates_of_pow_eq s₀ q D v e he hv
  obtain ⟨F, -, hFv, -⟩ := exists_properDivisorOver_of_essFiniteType s₀
    (exists_essFiniteType_of_trdeg_residueField k s₀ h₀ v hv₁ x hle hlt
      (trdeg_residueField_of_pow_eq k s₀ q h₀ hₑ D v e he hv x hle)) hv₁ x hle hlt
  exact ⟨v, ⟨F.toDivisorOver, F.isProper, hFv.symm⟩, e, he, hv⟩

end MMP.Fourfold
