module
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart

/-!
# The Jacobian divisor of a proper birational morphism is effective and exceptional

Let `g : S ⟶ X` be a proper birational morphism from a normal variety `S` to a smooth variety `X`
of dimension `n` over a field `k`, such that every prime divisor of `S` meets the smooth locus
`S_sm`, and let `ω` be a nonzero rational `n`-form on `X`. Then
`div_S(g^*ω) - g^* div_X(ω)` is an effective `g`-exceptional divisor: at the generic point of a
prime divisor `P` its coefficient is the order of the Jacobian of `g` in local coordinates, which
is a unit when `P` is not contracted.

## Main results

* `MMP.Resolution.isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback`
* `MMP.Resolution.exists_coeff_sub_eq_ord`: the coefficient of `P` in `div_S(g^*ω) - g^*div_X(ω)`
  is the order of the Jacobian, built from
  `MMP.Resolution.algebraMap_ne_zero_of_topFormsMap_eq_smul` and
  `MMP.Resolution.coeff_eq_ord_formCoeff_of_isPullback`.

## Implementation notes

The variety structure of `S` is `g ≫ s_X`, so that `g` is a morphism over `k`; the pull-back
`g^*ω` is `MMP.Mori.pullbackRationalPluriForms`, `div_S` is
`MMP.Resolution.divisorOfFormOnSmoothLocus` and `div_X(ω)` is `MMP.Mori.divisorOfForm`, all of
whose prime divisors meet the smooth locus `X = X_sm`. The pull-back `g^* div_X(ω)` of the
(Cartier) divisor `div_X(ω)` is characterised by `MMP.Mori.Divisor.IsPullback`; the statement holds
for every divisor satisfying it, which on the smooth `X` exists and is unique.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Theorem 2.13]
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace MMP.Resolution

section

variable {k : Type u} [Field k] {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : S ⟶ X)

/-- At the generic point of a prime divisor in the smooth locus of a variety of dimension `n`,
the top forms `Ω^n_{𝒪_{S,P}/k}` have a generator with nonzero image in `Ω^n_{k(S)/k}`. -/
public theorem exists_topForms_generator_of_mem_smoothLocus {sS : S ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sS] [IsLocallyNoetherian S] [IsIntegral S] [IsNormal S]
    {n : ℕ} (hn : topologicalKrullDim S = n) (P : MMP.Mori.PrimeDivisor S)
    (hP : P.genericPoint ∈ smoothLocus sS) :
    letI := stalkAlgebra sS P.genericPoint
    letI := functionFieldAlgebra sS
    haveI := isScalarTower_stalk_functionField sS P.genericPoint
    ∃ σ : ⋀[P.localRing]^n Ω[P.localRing⁄k], Submodule.span P.localRing {σ} = ⊤ ∧
      topFormsMap k P.localRing S.functionField n σ ≠ 0 := by
  let := stalkAlgebra sS P.genericPoint
  let := functionFieldAlgebra sS
  have := isScalarTower_stalk_functionField sS P.genericPoint
  have : LocallyOfFiniteType sS := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : Algebra.FormallySmooth k P.localRing :=
    (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff P).mp hP
  have : Algebra.EssFiniteType k P.localRing := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P.genericPoint) isOpen_univ
    have hU' : IsAffineOpen U := hU
    let x : U := ⟨P.genericPoint, hxU⟩
    let := sectionAlgebra sS U
    have := finiteType_sectionAlgebra sS hU'
    let : Algebra Γ(S, U) P.localRing := TopCat.Presheaf.algebra_section_stalk S.presheaf x
    have := isScalarTower_section_stalk sS U x
    have := hU'.isLocalization_stalk x
    have : Algebra.EssFiniteType Γ(S, U) P.localRing :=
      .of_isLocalization _ (hU'.primeIdealOf x).asIdeal.primeCompl
    exact .comp k Γ(S, U) P.localRing
  have := P.isDiscreteValuationRing_localRing
  have : Module.Free P.localRing Ω[P.localRing⁄k] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth P.localRing S.functionField :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P.localRing)
  have : Algebra.FormallySmooth k S.functionField := .comp k P.localRing S.functionField
  have := essFiniteType_functionField (sX := sS)
  have h := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k S.functionField
  have h2 := h.2.2
  rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k S.functionField),
    Nat.cast_zero, sub_zero] at h2
  have hK : Module.finrank S.functionField Ω[S.functionField⁄k] = n := by
    rw [← toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hn]
    exact_mod_cast h2.symm
  exact exists_topForms_generator_of_free
    ((finrank_kaehlerDifferential_eq_of_isFractionRing (K := S.functionField)).symm.trans hK)

/-- **The Jacobian is nonzero.** Let `σ_X` be an `n`-form on `𝒪_{X,g(η_P)}` with nonzero image
in `Ω^n_{k(X)/k}`, and let `J ∈ 𝒪_{S,P}` satisfy `g^♯σ_X = J • σ_S` for some `n`-form `σ_S` on
`𝒪_{S,P}`. Since `g` is birational, `J` is nonzero in `k(S)`. -/
public theorem algebraMap_ne_zero_of_topFormsMap_eq_smul
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsIntegral X] [IsIntegral S] [IsLocallyNoetherian S] [IsDominant g]
    (hg : IsBirationalMorphism g) {n : ℕ} (P : MMP.Mori.PrimeDivisor S)
    {σA : letI := stalkAlgebra sX (g P.genericPoint)
      ⋀[X.presheaf.stalk (g P.genericPoint)]^n Ω[X.presheaf.stalk (g P.genericPoint)⁄k]}
    (h0A : letI := stalkAlgebra sX (g P.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (g P.genericPoint)
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) X.functionField n σA ≠ 0)
    {σB : letI := stalkAlgebra (g ≫ sX) P.genericPoint
      ⋀[P.localRing]^n Ω[P.localRing⁄k]} {J : P.localRing}
    (hrel : letI := stalkAlgebra sX (g P.genericPoint)
      letI := stalkAlgebra (g ≫ sX) P.genericPoint
      letI := (g.stalkMap P.genericPoint).hom.toAlgebra
      haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) P.localRing n σA = J • σB) :
    algebraMap P.localRing S.functionField J ≠ 0 := by
  let := stalkAlgebra sX (g P.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (g P.genericPoint)
  let := stalkAlgebra (g ≫ sX) P.genericPoint
  let := functionFieldAlgebra (g ≫ sX)
  have := isScalarTower_stalk_functionField (g ≫ sX) P.genericPoint
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  let := (g.stalkMap P.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
  let : Algebra (X.presheaf.stalk (g P.genericPoint)) S.functionField :=
    ((algebraMap X.functionField S.functionField).comp
      (algebraMap (X.presheaf.stalk (g P.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (g P.genericPoint)) X.functionField S.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (g P.genericPoint)) P.localRing S.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      functionFieldMap_algebraMap_stalk g P.genericPoint a
  have : IsScalarTower k (X.presheaf.stalk (g P.genericPoint)) S.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField S.functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (g P.genericPoint)) X.functionField]
      rfl
  have hcomp : topFormsMap k X.functionField S.functionField n
        (topFormsMap k (X.presheaf.stalk (g P.genericPoint)) X.functionField n σA) =
      algebraMap P.localRing S.functionField J •
        topFormsMap k P.localRing S.functionField n σB := by
    rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
      ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := P.localRing), hrel, map_smul,
      algebraMap_smul]
  intro hJ
  rw [hJ, zero_smul] at hcomp
  -- pull back along the inverse of `g^* : k(X) ≃ k(S)`
  let e := RingEquiv.ofBijective (functionFieldMap g) hg.functionFieldMap_bijective
  let : Algebra S.functionField X.functionField := e.symm.toRingHom.toAlgebra
  have hee : ∀ a : X.functionField, e.symm (algebraMap X.functionField S.functionField a) = a :=
    e.symm_apply_apply
  have : IsScalarTower X.functionField S.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (hee a).symm
  have : IsScalarTower k S.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change _ = e.symm (algebraMap k S.functionField c)
      rw [IsScalarTower.algebraMap_apply k X.functionField S.functionField, hee]
  have h2 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (d := n)
    (A := X.functionField) (B := S.functionField) (C := X.functionField)
    (topFormsMap k (X.presheaf.stalk (g P.genericPoint)) X.functionField n σA)
  rw [hcomp, map_zero] at h2
  have h3 := MMP.Mori.topFormsMap_eq_self (k := k) (RingHom.id X.functionField) (fun _ => rfl)
    (topFormsMap k (X.presheaf.stalk (g P.genericPoint)) X.functionField n σA)
  exact h0A (h3.symm.trans h2.symm)

/-- The Jacobian is a unit where `g` is a local isomorphism. -/
private theorem isUnit_of_topFormsMap_eq_smul
    [IsIntegral X] [IsIntegral S] [IsLocallyNoetherian S] {n : ℕ} (P : MMP.Mori.PrimeDivisor S)
    {σA : letI := stalkAlgebra sX (g P.genericPoint)
      ⋀[X.presheaf.stalk (g P.genericPoint)]^n Ω[X.presheaf.stalk (g P.genericPoint)⁄k]}
    (hσA : Submodule.span (X.presheaf.stalk (g P.genericPoint)) {σA} = ⊤)
    {σB : letI := stalkAlgebra (g ≫ sX) P.genericPoint
      ⋀[P.localRing]^n Ω[P.localRing⁄k]}
    (h0B : letI := stalkAlgebra (g ≫ sX) P.genericPoint
      letI := functionFieldAlgebra (g ≫ sX)
      haveI := isScalarTower_stalk_functionField (g ≫ sX) P.genericPoint
      topFormsMap k P.localRing S.functionField n σB ≠ 0) {J : P.localRing}
    (hrel : letI := stalkAlgebra sX (g P.genericPoint)
      letI := stalkAlgebra (g ≫ sX) P.genericPoint
      letI := (g.stalkMap P.genericPoint).hom.toAlgebra
      haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) P.localRing n σA = J • σB)
    (hiso : IsIso (g.stalkMap P.genericPoint)) : IsUnit J := by
  let := stalkAlgebra sX (g P.genericPoint)
  let := stalkAlgebra (g ≫ sX) P.genericPoint
  let := (g.stalkMap P.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
  let := functionFieldAlgebra (g ≫ sX)
  have := isScalarTower_stalk_functionField (g ≫ sX) P.genericPoint
  have hbij : Function.Bijective
      (algebraMap (X.presheaf.stalk (g P.genericPoint)) P.localRing) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hiso
  have : IsLocalization (⊥ : Submonoid (X.presheaf.stalk (g P.genericPoint))) P.localRing :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Submonoid.mem_bot] at ha
      subst ha
      simp) hbij
  have hspan := span_singleton_topFormsMap (K := P.localRing) (d := n) ⊥ hσA
  rw [hrel] at hspan
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.mem_top : σB ∈ Submodule.span P.localRing {J • σB})
  have key : (c * J - 1) • σB = 0 := by rw [sub_smul, mul_smul, hc, one_smul, sub_self]
  have h1 := congrArg (topFormsMap k P.localRing S.functionField n) key
  rw [map_smul, map_zero, ← algebraMap_smul S.functionField] at h1
  have h2 := (smul_eq_zero.mp h1).resolve_right h0B
  rw [map_eq_zero_iff _ (IsFractionRing.injective P.localRing S.functionField),
    sub_eq_zero] at h2
  exact isUnit_iff_exists_inv'.mpr ⟨c, h2⟩

/-- **The coefficient of the pull-back.** Near `ξ = g(η_P)` the divisor `div_X(ω)` is the
principal divisor of the coefficient `u` of `ω` along a generator `σ_X` of `Ω^n_{𝒪_{X,ξ}/k}`, so
the coefficient of `P` in its pull-back is `ord_P(g^*u)`. -/
public theorem coeff_eq_ord_formCoeff_of_isPullback
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X] [IsIntegral X] [IsIntegral S] [IsDominant g]
    (hX : IsSmoothScheme sX) {n : ℕ} (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S, g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B') (P : MMP.Mori.PrimeDivisor S)
    {σA : letI := stalkAlgebra sX (g P.genericPoint)
      ⋀[X.presheaf.stalk (g P.genericPoint)]^n Ω[X.presheaf.stalk (g P.genericPoint)⁄k]}
    (hσA : Submodule.span (X.presheaf.stalk (g P.genericPoint)) {σA} = ⊤)
    (h0A : letI := stalkAlgebra sX (g P.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (g P.genericPoint)
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) X.functionField n σA ≠ 0) :
    letI := stalkAlgebra sX (g P.genericPoint)
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX (g P.genericPoint)
    B'.coeff P = S.ord (functionFieldMap g
      (formCoeff (k := k) (m := 1) (X.presheaf.stalk (g P.genericPoint)) hσA h0A ω))
      P.genericPoint := by
  let := stalkAlgebra sX (g P.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (g P.genericPoint)
  have hC := MMP.Fourfold.isCartier_of_isSmoothScheme hX (divisorOfForm ω)
  obtain ⟨U, hyU, φ, hφ⟩ := hC (g P.genericPoint)
  set Z0 := pointComponent (g P.genericPoint)
  obtain ⟨a, ha⟩ : ∃ a,
      formCoeff (k := k) (m := 1) (X.presheaf.stalk (g P.genericPoint)) hσA h0A ω = a :=
    ⟨_, rfl⟩
  set b := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hb
  have ha0 : a ≠ 0 := fun h0 => hω ((formCoeff_eq_zero_iff hσA h0A _).mp (ha.trans h0))
  have hb0 : b ≠ 0 := ((φ.isUnit.map _).ne_zero)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hB' hφ P hyU Z0, ha]
  have hu : ∀ Γ : MMP.Mori.PrimeDivisor X, (g P.genericPoint) ∈ Γ.support →
      X.ord (a * b⁻¹) Γ.genericPoint = 0 := by
    intro Γ hΓ
    have e1 :=
      MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX (g P.genericPoint) Γ hΓ hσA h0A ω
    have e2 := hφ Γ ⟨(g P.genericPoint), hΓ, hyU⟩
    rw [coeff_divisorOfForm, e1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at e2
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ] at e2
    rw [Scheme.ord_mul ha0 (inv_ne_zero hb0), ← zpow_neg_one, MMP.Mori.ord_zpow _ hb0, ← ha, e2,
      ← hb]
    ring
  obtain ⟨r, hr, hra⟩ :=
    MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (g P.genericPoint)
      (mul_ne_zero ha0 (inv_ne_zero hb0)) hu
  have hab : a = (a * b⁻¹) * b := by field_simp
  have hφu : S.ord (functionFieldMap g (a * b⁻¹)) P.genericPoint = 0 := by
    rw [← hra, MMP.Mori.functionFieldMap_algebraMap_stalk g P.genericPoint r]
    exact P.ord_algebraMap_of_isUnit (hr.map _)
  conv_rhs => rw [hab, map_mul]
  rw [Scheme.ord_mul ((map_ne_zero _).mpr (mul_ne_zero ha0 (inv_ne_zero hb0)))
    ((map_ne_zero _).mpr hb0), hφu, zero_add]

/-- **The Jacobian.** The coefficient of a prime divisor `P` in `div_S(g^*ω) - g^*div_X(ω)` is
the order along `P` of an element `J` of `𝒪_{S,P}`, which is a unit when `g` induces an
isomorphism of local rings at the generic point of `P`. -/
public theorem exists_coeff_sub_eq_ord
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X] [IsIntegral X] [IsIntegral S]
    [IsDominant g] (hg : IsBirationalMorphism g)
    (hX : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S,
      g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B')
    (P : MMP.Mori.PrimeDivisor S) (hP : P.genericPoint ∈ smoothLocus (g ≫ sX)) :
    ∃ J : P.localRing, algebraMap P.localRing S.functionField J ≠ 0 ∧
      P.ordForm (pullbackRationalPluriForms sX g ω) - B'.coeff P =
        S.ord (algebraMap P.localRing S.functionField J) P.genericPoint ∧
      (IsIso (g.stalkMap P.genericPoint) → IsUnit J) := by
  have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sX := (isSmoothScheme_iff sX).mp hX
  let := stalkAlgebra sX (g P.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (g P.genericPoint)
  let := stalkAlgebra (g ≫ sX) P.genericPoint
  let := functionFieldAlgebra (g ≫ sX)
  have := isScalarTower_stalk_functionField (g ≫ sX) P.genericPoint
  let := (g.stalkMap P.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX g P.genericPoint
  obtain ⟨σA, hσA, h0A⟩ :=
    MMP.Threefold.Resolution.exists_topForms_generator_stalk sX hn (g P.genericPoint)
  have hnS : topologicalKrullDim S = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg).symm.trans hn
  obtain ⟨σB, hσB, h0B⟩ := exists_topForms_generator_of_mem_smoothLocus hnS P hP
  obtain ⟨J, hJ⟩ := Submodule.mem_span_singleton.mp
    (hσB ▸ Submodule.mem_top :
      topFormsMap k (X.presheaf.stalk (g P.genericPoint)) P.localRing n σA ∈
        Submodule.span P.localRing {σB})
  have hJ0 := algebraMap_ne_zero_of_topFormsMap_eq_smul sX g hg P h0A hJ.symm
  refine ⟨J, hJ0, ?_, isUnit_of_topFormsMap_eq_smul sX g P hσA h0B hJ.symm⟩
  rw [MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sX g P hσA h0A hσB h0B J
    hJ.symm hJ0 hω, coeff_eq_ord_formCoeff_of_isPullback sX g hX ω hω hB B' hB' P hσA h0A]
  ring

/-- An element of the local ring along a prime divisor has nonnegative order. -/
private theorem ord_algebraMap_nonneg [IsIntegral S] [IsLocallyNoetherian S]
    (P : MMP.Mori.PrimeDivisor S) (J : P.localRing) :
    0 ≤ S.ord (algebraMap P.localRing S.functionField J) P.genericPoint := by
  by_cases hJ : J = 0
  · simp [hJ]
  have hz := P.coheight_genericPoint
  have hne : algebraMap P.localRing S.functionField J ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective P.localRing S.functionField)).mpr hJ
  rw [Scheme.le_ord_iff hz hne, ofAdd_zero]
  have : Ring.KrullDimLE 1 P.localRing := krullDimLE_of_coheight_le hz.le
  exact Ring.ordFrac_ge_one_of_ne_zero hJ

/-- Dimension count: `a + 1 = d` and `b + c = d` with `c ≥ 2` and `d` finite and nonempty
force `b < a`. -/
private theorem lt_of_add_one_eq_of_add_eq {a b d : WithBot ℕ∞} {c : ℕ∞} (h1 : a + 1 = d)
    (h2 : b + c = d) (hc : 2 ≤ c) (hd : d ≠ ⊤) (hd' : d ≠ ⊥) : b < a := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hd'
  | coe d =>
  induction d using ENat.recTopCoe with
  | top => exact absurd rfl hd
  | coe d =>
  induction a using WithBot.recBotCoe with
  | bot => simp at h1
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at h2
  | coe b =>
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_inj] at h1
  rw [← WithBot.coe_add, WithBot.coe_inj] at h2
  rw [WithBot.coe_lt_coe]
  induction a using ENat.recTopCoe with
  | top => simp at h1
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => simp at h2
  | coe b =>
  induction c using ENat.recTopCoe with
  | top => simp at h2
  | coe c =>
  norm_cast at h1 h2 hc ⊢
  omega

/-- If a prime divisor `P` of `S` is not `g`-exceptional, `g` is a local isomorphism at its
generic point: the image of the generic point has coheight one, so it lies in the open `W`, with
complement of codimension two, over which `g` is an isomorphism. -/
private theorem isIso_stalkMap_of_not_lt
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsNormal X] [IsProper g] [IsLocallyNoetherian S] [CompactSpace X] (hg : IsBirationalMorphism g)
    (P : MMP.Mori.PrimeDivisor S)
    (hP : ¬ topologicalKrullDim (closure (g.base '' P.support)) <
      topologicalKrullDim P.support) :
    IsIso (g.stalkMap P.genericPoint) := by
  obtain ⟨W, hW, hiso⟩ :=
    exists_two_le_closedsCodimension_compl_isIso_morphismRestrict (k := k)
      (sX := sX) ⟨inferInstance, inferInstance⟩ g inferInstance hg
  have hη : g P.genericPoint ∈ W := by
    by_contra hξ
    have h2 : 2 ≤ Order.coheight (g P.genericPoint) :=
      (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW) _ hξ
    apply hP
    have hcl : closure (g.base '' P.support) = closure {g P.genericPoint} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        closure_image_closure g.base.hom.continuous, Set.image_singleton]
    rw [hcl, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
    have : LocallyOfFiniteType (g ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
    have hS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (g ≫ sX)
      P.genericPoint
    have hX' := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
      (g P.genericPoint)
    have hd := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg
    rw [P.coheight_genericPoint] at hS
    refine lt_of_add_one_eq_of_add_eq (hS.trans hd.symm) hX' h2
      (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX)
      (Order.krullDim_ne_bot_iff.mpr
        ⟨⟨closure {g P.genericPoint}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)
  obtain ⟨y, hy⟩ : ∃ y : (g ⁻¹ᵁ W).toScheme, (g ⁻¹ᵁ W).ι y = P.genericPoint := ⟨⟨_, hη⟩, rfl⟩
  rw [← hy]
  have hoi : ∀ {U V : Scheme.{u}} (f : U ⟶ V) [IsOpenImmersion f] (x : U),
      IsIso (f.stalkMap x) := fun f _ x => (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 x
  have : IsOpenImmersion (g ∣_ W) := IsOpenImmersion.of_isIso _
  have h2 : IsIso ((g ∣_ W ≫ W.ι).stalkMap y) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hoi W.ι ((g ∣_ W) y)) (hoi (g ∣_ W) y)
  have h1 : IsIso (((g ⁻¹ᵁ W).ι ≫ g).stalkMap y) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ (morphismRestrict_ι g W).symm y]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h2
  rw [Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap ((g ⁻¹ᵁ W).ι y))
    ((g ⁻¹ᵁ W).ι.stalkMap y) (hoi (g ⁻¹ᵁ W).ι y) h1

/-- **Kollár, Theorem 2.13.** Let `g : S ⟶ X` be a proper birational morphism from a normal
variety `S` (over `k` through `g ≫ s_X`) to a smooth variety `X` of dimension `n`, such that every
prime divisor of `S` meets the smooth locus of `S`, and let `ω ≠ 0` be a rational `n`-form on `X`.
Then for the pull-back `B'` of `div_X(ω)` along `g`, the divisor `div_S(g^*ω) - B'` is effective
and `g`-exceptional. -/
@[mmp "lem_kr2a_jacobian_divisor_effective_exceptional"]
public theorem isEffective_and_isExceptional_divisorOfFormOnSmoothLocus_sub_pullback
    [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k (g ≫ sX)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian S] [CompactSpace X] [CompactSpace S]
    [IsNormal S] [IsNormal X]
    [IsProper g] [IsDominant g] (hg : IsBirationalMorphism g)
    (hX : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (hsm : ∀ P : AlgebraicGeometry.PrimeDivisor S,
      (P.support ∩ (smoothLocus (g ≫ sX) : Set S)).Nonempty)
    (ω : RationalPluriForms sX n 1) (hω : ω ≠ 0)
    (hB : ∀ Z : irreducibleComponents S,
      g (componentGenericPoint S Z) ∉ (divisorOfForm ω).supp)
    (B' : Divisor S) (hB' : (divisorOfForm ω).IsPullback g hB B') :
    (divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B').IsEffective ∧
      IsExceptionalDivisorFor g
        (divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) - B') := by
  have hsl : ∀ P : MMP.Mori.PrimeDivisor S, P.genericPoint ∈ smoothLocus (g ≫ sX) := by
    intro P
    obtain ⟨x, hxP, hx⟩ := hsm P
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
    exact (specializes_iff_mem_closure.mpr hxP).mem_open (smoothLocus (g ≫ sX)).isOpen hx
  have hfil : divisorOfFormOnSmoothLocus (pullbackRationalPluriForms sX g ω) =
      divisorOfForm (pullbackRationalPluriForms sX g ω) := by
    classical
    unfold divisorOfFormOnSmoothLocus
    convert (Finsupp.filter_eq_self_iff _ _).mpr fun P _ => hsm P
  have hc : ∀ P : MMP.Mori.PrimeDivisor S,
      (divisorOfForm (pullbackRationalPluriForms sX g ω) - B').coeff P =
        P.ordForm (pullbackRationalPluriForms sX g ω) - B'.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_sub, coeff_divisorOfForm]
  rw [hfil]
  refine ⟨fun P => ?_, fun P hP => ?_⟩
  · obtain ⟨J, -, hJ, -⟩ := exists_coeff_sub_eq_ord sX g hg hX hn ω hω hB B' hB' P (hsl P)
    rw [hc, hJ]
    exact ord_algebraMap_nonneg P J
  · by_contra hlt
    obtain ⟨J, -, hJ, hu⟩ := exists_coeff_sub_eq_ord sX g hg hX hn ω hω hB B' hB' P (hsl P)
    have h0 := Finsupp.mem_support_iff.mp hP
    change (divisorOfForm (pullbackRationalPluriForms sX g ω) - B').coeff P ≠ 0 at h0
    rw [hc, hJ] at h0
    exact h0 (P.ord_algebraMap_of_isUnit (hu (isIso_stalkMap_of_not_lt sX g hg P hlt)))

end

end MMP.Resolution
