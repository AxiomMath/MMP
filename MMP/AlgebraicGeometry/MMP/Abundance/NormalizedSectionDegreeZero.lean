module
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero

/-!
# Nowhere vanishing normalized sections in degree zero

Let `C` be a smooth connected proper curve over an algebraically closed field `k`, `Δ` a
boundary on `C` with `mΔ` integral for some `m > 0`, and suppose `deg(K_C + Δ) = 0`. Then
`Γ(C, 𝒪(12m(K_C + Δ)))` contains a normalized section (with respect to any normalization datum
for elliptic curves) which vanishes nowhere. This is case (12.2.11.3) of the proof of
[FA, 12.2.11].

## Main results

* `MMP.Flips.exists_isNormalizedSection_of_degree_eq_zero`: the nowhere vanishing normalized
  section in degree zero.
* `MMP.Flips.exists_ordForm_add_eq_zero_of_genus_zero`: its genus zero case, which needs no
  normalization datum for elliptic curves.
* `MMP.Flips.exists_principalDivisor_add_eq_zero`: on a smooth proper curve of genus zero every
  divisor of degree zero is principal.
* `MMP.Flips.zero_le_ordForm_d`, `MMP.Flips.ordForm_d_eq_zero`: `ord_P(dz) ≥ 0` when `z` is
  regular at `P`, and `ord_P(dz) = 0` when `z` is a local parameter at `P`.
* `MMP.Flips.ordForm_dlogPow_of_ord`: `div (dz/z)^{⊗n} = -n(P + Q)` when `div z = P - Q`.

## References

* [Kollár et al., *Flips and abundance for algebraic threefolds*][FA]
-/
public section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The degree of a `ℚ`-divisor on a normal locally Noetherian integral scheme agrees with the
degree of its `ℚ`-Weil divisor. -/
private theorem sum_toQWeilDivisor {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    [IsNormal C] (Δ : QDivisor C) :
    (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = Δ.sum (fun _ a => a) :=
  Finsupp.sum_subtypeDomain_index (h := fun _ a => a)
    fun Γ _ => ⟨inferInstance, Γ.isDiscreteValuationRing_localRing⟩

/-- An effective divisor of degree zero is zero. -/
private theorem eq_zero_of_nonneg_of_sum_eq_zero {α : Type*} {D : α →₀ ℤ} (h0 : 0 ≤ D)
    (hs : (D.sum fun _ a => a) = 0) : D = 0 := by
  classical
  ext P
  by_cases hP : P ∈ D.support
  · simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => h0 Q)).1 hs P hP
  · exact Finsupp.notMem_support_iff.1 hP

/-- The sum of the coefficients of an integral divisor, as an additive map. -/
private theorem sum_eq_liftAddHom {α : Type*} (D : α →₀ ℤ) :
    (D.sum fun _ a => a) = Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D := by
  rw [Finsupp.liftAddHom_apply]
  rfl

/-- The sum of the coefficients of an integral divisor commutes with the cast to `ℚ`. -/
private theorem sum_intCast {α : Type*} (D : α →₀ ℤ) :
    (D.sum fun _ a => (a : ℚ)) = ((D.sum fun _ a => a : ℤ) : ℚ) := by
  simp [Finsupp.sum]

/-- On a smooth proper curve, the divisor of a nonzero rational `m`-canonical form has degree
`m deg K`. -/
theorem sum_divisorOfForm_eq_mul_sum {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    [LocallyOfFiniteType sC] (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC)
    (hp : IsProper sC) (hdim : topologicalKrullDim C = 1) {K : Divisor C}
    (hK : K.IsCanonicalDivisor sC 1) {m : ℤ} {τ : RationalPluriForms sC 1 m} (hτ : τ ≠ 0) :
    ((divisorOfForm τ).sum fun _ a => a) = m * K.sum fun _ a => a := by
  obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hC hK hτ
  have h1 := sum_principalDivisor_eq_zero hC hsm hp hdim φ
  rw [← hφ, sum_eq_liftAddHom, map_sub, map_zsmul, ← sum_eq_liftAddHom K,
    ← sum_eq_liftAddHom, smul_eq_mul] at h1
  linarith

/-- The genus one case of `exists_isNormalizedSection_of_degree_eq_zero`. -/
private theorem exists_of_genus_one {k : Type u} [Field k] [IsAlgClosed k]
    (ε : EllipticNormalizationDatum k) {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QDivisor C} (hΔ : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sC)
    {m : ℕ} (hm : 0 < m) {G : Divisor C} (hG : Divisor.toQDivisor G = (m : ℤ) • Δ)
    (hdeg : (K.sum fun _ a => (a : ℚ)) + Δ.sum (fun _ a => a) = 0)
    (hg : K.h0 k sC = 1) (hΔ0 : MMP.Fourfold.QDivisor.toQWeilDivisor Δ = 0) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ),
      IsNormalizedSection ε sC Δ (12 * m) (12 • G) s ∧ s ≠ 0 ∧
        ∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0 := by
  classical
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  obtain rfl : Δ = 0 := MMP.Fourfold.QDivisor.toQWeilDivisor_injective (by rw [hΔ0]; rfl)
  obtain rfl : G = 0 := by
    ext P
    simpa [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply,
      DivisorWithCoeffs.coeff_apply] using congrArg (fun D : QDivisor C => D P) hG
  let E : GenusOneCurve k := ⟨C, sC, hC, hsm, hp, hdim, ⟨K, hK, hg⟩⟩
  let ε₀ : RationalPluriForms sC 1 12 := ε.ε E
  have hε₀ : ε₀ ≠ 0 := ε.ne_zero E
  have hmem : ε₀ ∈ pluricanonicalSections sC 1 12 0 ⊤ := ε.mem E
  have hnonneg : ∀ P : MMP.Mori.PrimeDivisor C, 0 ≤ P.ordForm ε₀ := fun P => by
    simpa using hmem.2 P ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, trivial⟩ hε₀
  have hKsum : (K.sum fun _ a => a) = 0 := by
    rw [Finsupp.sum_zero_index, add_zero, sum_intCast] at hdeg
    exact_mod_cast hdeg
  have hsum : ((divisorOfForm ε₀).sum fun _ a => a) = 0 := by
    simpa [hKsum] using sum_divisorOfForm_eq_mul_sum hC hsm hp hdim hK hε₀
  have hzero : ∀ P : MMP.Mori.PrimeDivisor C, P.ordForm ε₀ = 0 := fun P =>
    DFunLike.congr_fun (eq_zero_of_nonneg_of_sum_eq_zero hnonneg hsum) P
  let := functionFieldAlgebra sC
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) hdim
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hC (n := 1) (by exact_mod_cast hdim)
  set c := (ZTensorPower.basis b 12).repr ε₀ () with hc
  have hc0 : c ≠ 0 := repr_ne_zero_of_ne_zero b hε₀
  let s : RationalPluriForms sC 1 (12 * m : ℕ) :=
    c ^ (12 * m / 12) • ZTensorPower.basis b ((12 * m : ℕ) : ℤ) ()
  have hrepr : (ZTensorPower.basis b ((12 * m : ℕ) : ℤ)).repr s () = c ^ (12 * m / 12) := by
    simp [s]
  have hs0 : s ≠ 0 := smul_ne_zero (pow_ne_zero _ hc0) ((ZTensorPower.basis b _).ne_zero ())
  have hord : ∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s = 0 := by
    intro P
    obtain ⟨N, hN⟩ := P.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hN 12 ε₀ hε₀
    have e2 := hN _ s hs0
    rw [← hc, hzero P] at e1
    rw [hrepr, ← zpow_natCast, ord_zpow _ hc0, Nat.mul_div_cancel_left _ (by norm_num)] at e2
    rw [e2]
    push_cast
    linear_combination (-(m : ℤ)) * e1
  refine ⟨s, ⟨hC, hsm, hdim, by simp [DivisorWithCoeffs.IsEffective], by omega, by simp, ?_, ?_,
    ?_⟩, hs0,
    fun P => by simp [hord P]⟩
  · exact (mem_pluricanonicalSections_of_ne_bot top_ne_bot).2 fun P _ _ => by simp [hord P]
  · intro _ _ _ _
    exact ⟨by push_cast; omega, b, rfl⟩
  · intro _ P hP
    norm_num [DivisorWithCoeffs.coeff_apply] at hP

/-- **A degree-zero divisor on a smooth proper curve of genus zero is principal** (Stacks
0C6M): `𝒪_C(D)` has degree `0`, hence is trivial, so it has a nonzero global section `φ`, and
the effective divisor `div φ + D` of degree `0` vanishes. -/
theorem exists_principalDivisor_add_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (hg : K.h0 k sC = 0) (D : Divisor C) (hD : (D.sum fun _ a => a) = 0) :
    ∃ φ : (RationalFunctions C)ˣ, MMP.Mori.principalDivisor φ + D = 0 := by
  classical
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  obtain ⟨-, -, hprop, -⟩ := curve_instances hC hsm hp hdim hsm
  have hι : IsIso (smoothLocus sC).ι := by
    have h : smoothLocus sC = ⊤ := hsm
    generalize smoothLocus sC = U at h ⊢
    subst h
    rw [← Scheme.topIso_hom]
    infer_instance
  have hgC : genus sC = 0 := by
    rw [← genus_comp_iso_eq k sC (asIso (smoothLocus sC).ι)]
    exact (h0_canonical_eq_genus hC hsm hp hK).symm.trans hg
  have : AlgebraicGeometry.IsCurve k sC := (AlgebraicGeometry.isCurve_iff k sC).2 ⟨hC.1, hdim⟩
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ sC.appTop) :=
    GenusOne.isIso_globalSections_of_isAlgClosed _
  have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm D
  have := hc.isInvertibleModule_divisorialSheaf
  have hdim' : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (smoothLocus sC).ι)).isHomeomorph, hdim]
  have hdeg : invertibleCurveDegree k sC
      (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)).le
      D.divisorialSheaf = 0 := by
    have h1 := degreeOn_smoothLocus_eq_sum hC hsm hp hdim hdim' D
    change invertibleCurveDegree k ((smoothLocus sC).ι ≫ sC) hdim'
      ((Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf) = _ at h1
    rw [invertibleCurveDegree_pullback_of_isIso (smoothLocus sC).ι sC hdim' (le_of_eq hdim)]
      at h1
    rw [h1, hD]
  obtain ⟨e⟩ := isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero k sC
    D.divisorialSheaf hgC hdeg
  let σ : D.divisorialSubmodule ⊤ := (e.inv.val.app (Opposite.op ⊤)).hom (1 : Γ(C, ⊤))
  have hσ : σ ≠ 0 := by
    intro h
    have h1 : (e.hom.val.app (Opposite.op ⊤)).hom σ =
        ((e.inv ≫ e.hom).val.app (Opposite.op ⊤)).hom (1 : Γ(C, ⊤)) := rfl
    rw [e.inv_hom_id, h] at h1
    have h2 := (map_zero (e.hom.val.app (Opposite.op ⊤)).hom).symm.trans h1
    exact zero_ne_one (α := Γ(C, ⊤)) h2
  refine ⟨(Divisor.isUnit_sectionToRationalFunctions hσ).unit,
    eq_zero_of_nonneg_of_sum_eq_zero (D.zeroDivisor_nonneg σ hσ) ?_⟩
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    sum_principalDivisor_eq_zero hC hsm hp hdim, hD, add_zero]

/-- The form `b^{⊗n}` of a basis `b` of a line is the tensor power `b ⊗ ⋯ ⊗ b`, so
`(c b)^{⊗n} = cⁿ b^{⊗n}`. -/
private theorem tprod_smul_eq_smul_basis {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) (c : K) (n : ℕ) :
    ∀ τ : ZTensorPower K L (n : ℤ),
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => c • b ()) : TensorPower K n L) →
      τ = c ^ n • ZTensorPower.basis b n () := by
  rintro τ rfl
  rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  change _ = ((Basis.piTensorProduct fun _ : Fin n => b).reindex (Equiv.ofUnique _ _)) ()
  rw [Module.Basis.reindex_apply, Basis.piTensorProduct_apply]

/-- If `da = c σ` for a generator `σ` of `Ω¹_{A/k}`, then `(da)^{⊗n}` has coordinate `cⁿ`
along `σ^{⊗n}`. -/
theorem formCoeff_tprod_ιMulti_D {k A K : Type*} [CommRing k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
    {σ : ⋀[A]^1 Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K 1 σ ≠ 0)
    {a c : A} (hc : exteriorPower.ιMulti A 1 (fun _ => KaehlerDifferential.D k A a) = c • σ)
    (n : ℕ) : ∀ τ : PluriForms k K 1 n,
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => exteriorPower.ιMulti K 1
        (fun _ => KaehlerDifferential.D k K (algebraMap A K a))) : TensorPower K n _) →
      formCoeff A hσ h0 τ = algebraMap A K c ^ n := by
  intro τ hτ
  have hv : exteriorPower.ιMulti K 1 (fun _ => KaehlerDifferential.D k K (algebraMap A K a)) =
      algebraMap A K c • topFormsBasis A hσ h0 () := by
    have := congrArg (topFormsMap k A K 1) hc
    rw [topFormsMap_ιMulti, map_smul] at this
    simp only [KaehlerDifferential.map_D] at this
    rw [topFormsBasis_apply, algebraMap_smul, ← this]
  rw [hv] at hτ
  have := tprod_smul_eq_smul_basis (topFormsBasis A hσ h0) (algebraMap A K c) n τ hτ
  rw [formCoeff, this]
  simp

/-- **The differential of a regular function is regular**: if `ord_P(z) ≥ 0` then the
`1`-form `dz` has `ord_P(dz) ≥ 0` (or vanishes). -/
theorem zero_le_ordForm_d {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1)
    (P : MMP.Mori.PrimeDivisor C) (z : C.functionField) (hz : 0 ≤ C.ord z P.genericPoint) :
    letI := functionFieldAlgebra sC
    ∀ ω : RationalPluriForms sC 1 (1 : ℕ),
      ω = (PiTensorProduct.tprod C.functionField fun _ : Fin 1 =>
        exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField z) →
      ω ≠ 0 → 0 ≤ P.ordForm ω := by
  letI := functionFieldAlgebra sC
  intro ω hω hω0
  letI := stalkAlgebra sC P.genericPoint
  haveI := isScalarTower_stalk_functionField sC P.genericPoint
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  obtain ⟨σ, hσ, h0⟩ := P.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC)
    (d := 1) (by exact_mod_cast hdim)
  rcases eq_or_ne z 0 with rfl | hz0
  · refine absurd ?_ hω0
    rw [hω, map_zero]
    exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1)
      ((exteriorPower.ιMulti _ 1).map_coord_zero (0 : Fin 1) rfl)
  obtain ⟨a, rfl⟩ := (P.divisorialValuation_le_one_iff z).1 (by
    rw [P.divisorialValuation_eq_exp_neg_ord hz0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hσ ▸ Submodule.mem_top
    (x := exteriorPower.ιMulti P.localRing 1 fun _ => KaehlerDifferential.D k P.localRing a))
  have hcoeff := formCoeff_tprod_ιMulti_D hσ h0 hc.symm 1 ω hω
  rw [pow_one] at hcoeff
  have hc0 : algebraMap P.localRing C.functionField c ≠ 0 := by
    rw [← hcoeff]
    exact fun h => hω0 ((formCoeff_eq_zero_iff (m := ((1 : ℕ) : ℤ)) hσ h0 ω).1 h)
  rw [P.ordForm_eq ω hσ h0, hcoeff]
  have hv := (P.divisorialValuation_le_one_iff _).2 ⟨c, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord hc0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
  omega

/-- The generic point of a prime divisor of a one-dimensional integral scheme is closed. -/
private theorem isClosed_singleton_genericPoint {C : Scheme.{u}} [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) (P : MMP.Mori.PrimeDivisor C) :
    IsClosed ({P.genericPoint} : Set C) :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim
    fun h => by
      have h1 := P.coheight_genericPoint
      rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        at h1
      exact zero_ne_one h1

/-- In a discrete valuation ring with fraction field `K`, an element `a` with `v(a) = exp (-1)`
generates the maximal ideal. -/
theorem span_eq_maximalIdeal_of_ord_eq_one {C : Scheme.{u}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (P : MMP.Mori.PrimeDivisor C) {a : P.localRing}
    (ha : C.ord (algebraMap P.localRing C.functionField a) P.genericPoint = 1) :
    Ideal.span {a} = IsLocalRing.maximalIdeal P.localRing := by
  have := P.isDiscreteValuationRing_localRing
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hv := P.divisorialValuation_eq_exp_neg_ord (g := algebraMap P.localRing C.functionField
    (↑u * ϖ ^ n)) (by simpa using ha0)
  rw [ha, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
    P.divisorialValuation_algebraMap_of_irreducible hϖ] at hv
  have hu : P.divisorialValuation (algebraMap P.localRing C.functionField ↑u) = 1 := by
    have h1 := (P.divisorialValuation_le_one_iff
      (algebraMap P.localRing C.functionField ↑u)).2 ⟨_, rfl⟩
    have h2 := (P.divisorialValuation_le_one_iff
      (algebraMap P.localRing C.functionField ↑u⁻¹)).2 ⟨_, rfl⟩
    have h3 : P.divisorialValuation (algebraMap P.localRing C.functionField ↑u) *
        P.divisorialValuation (algebraMap P.localRing C.functionField ↑u⁻¹) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
    exact le_antisymm h1 (by
      by_contra h
      push Not at h
      have := mul_lt_one_of_lt_of_le h h2
      rw [h3] at this
      exact lt_irrefl _ this)
  rw [hu, one_mul, ← WithZero.exp_nsmul, WithZero.exp_inj] at hv
  have hn : n = 1 := by
    rw [nsmul_eq_mul] at hv
    omega
  subst hn
  rw [pow_one, Ideal.span_singleton_mul_left_unit u.isUnit]
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm

/-- **The differential of a local parameter generates**: if `ord_P(z) = 1` then `dz ≠ 0` and
`ord_P(dz) = 0`. -/
theorem ordForm_d_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1)
    (P : MMP.Mori.PrimeDivisor C) (z : C.functionField) (hz : C.ord z P.genericPoint = 1) :
    letI := functionFieldAlgebra sC
    ∀ ω : RationalPluriForms sC 1 (1 : ℕ),
      ω = (PiTensorProduct.tprod C.functionField fun _ : Fin 1 =>
        exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField z) →
      ω ≠ 0 ∧ P.ordForm ω = 0 := by
  letI := functionFieldAlgebra sC
  intro ω hω
  letI := stalkAlgebra sC P.genericPoint
  haveI := isScalarTower_stalk_functionField sC P.genericPoint
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨_, -⟩ := P.formallySmooth_localRing (sX := sC)
  obtain ⟨_, _⟩ := P.free_kaehlerDifferential_localRing (sX := sC)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by exact_mod_cast hdim)
  have hrk : Module.finrank P.localRing Ω[P.localRing⁄k] = 1 :=
    P.finrank_kaehlerDifferential_localRing.trans hd
  let e := Module.finBasisOfFinrankEq P.localRing Ω[P.localRing⁄k] hrk
  have hspanΩ : Submodule.span P.localRing {e 0} = ⊤ := by
    rw [← e.span_eq, Set.range_unique]
    rfl
  let σ : ⋀[P.localRing]^1 Ω[P.localRing⁄k] := exteriorPower.ιMulti P.localRing 1 fun _ => e 0
  have hσ : Submodule.span P.localRing {σ} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span P.localRing 1 _ hspanΩ,
      Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain rfl : f = fun _ => e 0 := funext fun i => hf ⟨i, rfl⟩
    exact Submodule.subset_span rfl
  have h0 := P.topFormsMap_ne_zero hd hσ
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨a, rfl⟩ := (P.divisorialValuation_le_one_iff z).1 (by
    rw [P.divisorialValuation_eq_exp_neg_ord hz0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  set c := e.repr (KaehlerDifferential.D k P.localRing a) 0
  have hDa : KaehlerDifferential.D k P.localRing a = c • e 0 := by
    conv_lhs => rw [← e.sum_repr (KaehlerDifferential.D k P.localRing a)]
    rw [Fin.sum_univ_one]
  have hc : exteriorPower.ιMulti P.localRing 1 (fun _ => KaehlerDifferential.D k P.localRing a) =
      c • σ := by
    rw [hDa, show (fun _ : Fin 1 => c • e 0) = fun i => (fun _ : Fin 1 => c) i •
      (fun _ : Fin 1 => e 0) i from rfl, AlternatingMap.map_smul_univ, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, pow_one]
  have hcu : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal P.localRing := (IsLocalRing.mem_maximalIdeal _).2 hcu
    have hspan := span_eq_maximalIdeal_of_ord_eq_one P hz
    have hfin := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sC P.genericPoint
      (isClosed_singleton_genericPoint hdim P)
    have : Algebra.IsSeparable k (IsLocalRing.ResidueField P.localRing) :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : Algebra.FormallyEtale k (IsLocalRing.ResidueField P.localRing) :=
      Algebra.FormallyEtale.of_isSeparable k _
    have hdimR : ringKrullDim P.localRing = (1 : ℕ) := by
      simpa using IsDiscreteValuationRing.ringKrullDim_eq_one (R := P.localRing)
    obtain ⟨ht, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular ![a]
      (by rw [Set.range_unique]; exact hspan) hdimR
    have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k ![a] ht hli
    apply hli'.ne_zero 0
    simp only [Matrix.cons_val_fin_one]
    rw [hDa, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff c).2 hcm,
      TensorProduct.zero_tmul]
  have hcoeff := formCoeff_tprod_ιMulti_D hσ h0 hc 1 ω hω
  rw [pow_one] at hcoeff
  refine ⟨fun h => ((hcu.map (algebraMap P.localRing C.functionField)).ne_zero) ?_, ?_⟩
  · rw [← hcoeff, h]
    exact (formCoeff_eq_zero_iff (m := ((1 : ℕ) : ℤ)) hσ h0 0).2 rfl
  · rw [P.ordForm_eq ω hσ h0, hcoeff]
    exact P.ord_algebraMap_of_isUnit hcu

/-- **Normalizing a unit at a point by a constant**: for `g` of order `0` at `P` there is a
nowhere vanishing constant `u` with `ord_P(g u - 1) ≥ 1`. -/
theorem exists_const_ord_mul_sub_one_pos {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1)
    (P : MMP.Mori.PrimeDivisor C) (g : C.functionField) (hg0 : g ≠ 0)
    (hg : C.ord g P.genericPoint = 0) :
    ∃ u : C.functionField, u ≠ 0 ∧ (∀ R : MMP.Mori.PrimeDivisor C, C.ord u R.genericPoint = 0) ∧
      (g * u - 1 = 0 ∨ 1 ≤ C.ord (g * u - 1) P.genericPoint) := by
  classical
  letI := functionFieldAlgebra sC
  letI := MMP.Mori.stalkAlgebra sC P.genericPoint
  haveI := MMP.Mori.isScalarTower_stalk_functionField sC P.genericPoint
  have := P.isDiscreteValuationRing_localRing
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hfin := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sC P.genericPoint
    (isClosed_singleton_genericPoint hdim P)
  obtain ⟨b, hb⟩ := (P.divisorialValuation_le_one_iff g).1 (by
    rw [P.divisorialValuation_eq_exp_neg_ord hg0, hg, neg_zero, WithZero.exp_zero])
  have hbu : IsUnit b := by
    by_contra hb'
    have := (P.divisorialValuation_algebraMap_lt_one_iff b).2
      ((IsLocalRing.mem_maximalIdeal _).2 hb')
    rw [hb, P.divisorialValuation_eq_exp_neg_ord hg0, hg, neg_zero, WithZero.exp_zero] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc⟩ := IsSepClosed.algebraMap_surjective k
    (IsLocalRing.ResidueField (C.presheaf.stalk P.genericPoint)) (IsLocalRing.residue _ b)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, IsLocalRing.residue_eq_zero_iff] at hc
    exact (IsLocalRing.mem_maximalIdeal _).1 hc hbu
  refine ⟨algebraMap k C.functionField c⁻¹, by simpa using hc0, fun R => ?_, ?_⟩
  · letI := MMP.Mori.stalkAlgebra sC R.genericPoint
    haveI := MMP.Mori.isScalarTower_stalk_functionField sC R.genericPoint
    rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk R.genericPoint) C.functionField]
    exact MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit R
      ((isUnit_iff_ne_zero.2 (inv_ne_zero hc0)).map _)
  · rcases eq_or_ne (g * algebraMap k C.functionField c⁻¹ - 1) 0 with h | hne
    · exact Or.inl h
    right
    set c' := algebraMap k (C.presheaf.stalk P.genericPoint) c
    have hc'u : IsUnit c' := (isUnit_iff_ne_zero.2 hc0).map _
    have heq : g * algebraMap k C.functionField c⁻¹ - 1 =
        algebraMap P.localRing C.functionField (b * ↑hc'u.unit⁻¹ - 1) := by
      rw [map_sub, map_mul, map_one, hb, map_inv₀,
        IsScalarTower.algebraMap_apply k (C.presheaf.stalk P.genericPoint) C.functionField,
        map_units_inv, IsUnit.unit_spec]
    have hmem : b * ↑hc'u.unit⁻¹ - 1 ∈ IsLocalRing.maximalIdeal P.localRing := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_one, ← hc]
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk P.genericPoint)
        (IsLocalRing.ResidueField _)]
      change IsLocalRing.residue _ c' * IsLocalRing.residue _ _ - 1 = 0
      rw [← map_mul, IsUnit.mul_val_inv, map_one, sub_self]
    have hlt := (P.divisorialValuation_algebraMap_lt_one_iff _).2 hmem
    rw [← heq, P.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero,
      WithZero.exp_lt_exp] at hlt
    omega

/-- `exists_principalDivisor_add_eq_zero`, read in the function field. -/
private theorem exists_ord_add_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (hg : K.h0 k sC = 0) (D : Divisor C) (hD : (D.sum fun _ a => a) = 0) :
    ∃ f : C.functionField, f ≠ 0 ∧
      ∀ R : MMP.Mori.PrimeDivisor C, C.ord f R.genericPoint + D R = 0 := by
  obtain ⟨φ, hφ⟩ := exists_principalDivisor_add_eq_zero hC hsm hp hdim hK hg D hD
  obtain ⟨f, hf0, hf⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  refine ⟨f, hf0, fun R => ?_⟩
  rw [← hf R]
  have := congrArg (fun D' : Divisor C => D' R) hφ
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
  exact this

/-- A boundary of degree `2` has two distinct points `P ≠ Q` such that either `Δ = P + Q`, or
`⌊Δ⌋ ⊆ {P}`. -/
private theorem exists_pair_of_sum_eq_two {α : Type*} (Δ : α →₀ ℚ)
    (h01 : ∀ a, 0 ≤ Δ a ∧ Δ a ≤ 1) (hs : (Δ.sum fun _ a => a) = 2) :
    ∃ P Q : α, P ≠ Q ∧ ((Δ P = 1 ∧ Δ Q = 1 ∧ ∀ R, R ≠ P → R ≠ Q → Δ R = 0) ∨
      (∀ R, 1 ≤ Δ R → R = P)) := by
  classical
  have hsub : ∀ s : Finset α, (∑ x ∈ s, Δ x) ≤ 2 := fun s => by
    rw [← hs, Finsupp.sum_of_support_subset Δ (Finset.subset_union_left (s₂ := s)) _
      (fun _ _ => rfl)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      fun x _ _ => (h01 x).1
  have hex : ∀ P : α, ∃ Q : α, Q ≠ P := by
    intro P
    by_contra! h
    have hsP : Δ.support ⊆ {P} := fun x _ => Finset.mem_singleton.2 (h x)
    have := Finsupp.sum_of_support_subset Δ hsP (fun _ a => a) (fun _ _ => rfl)
    rw [hs, Finset.sum_singleton] at this
    linarith [(h01 P).2]
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Subsingleton.elim Δ 0] at hs
  obtain ⟨a⟩ := hne
  by_cases h : ∃ P Q, P ≠ Q ∧ 1 ≤ Δ P ∧ 1 ≤ Δ Q
  · obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
    refine ⟨P, Q, hPQ, Or.inl ⟨le_antisymm (h01 P).2 hP, le_antisymm (h01 Q).2 hQ, ?_⟩⟩
    intro R hRP hRQ
    have := hsub {P, Q, R}
    rw [Finset.sum_insert (by simp [hPQ, Ne.symm hRP]), Finset.sum_insert (by simp [Ne.symm hRQ]),
      Finset.sum_singleton] at this
    linarith [(h01 R).1]
  · push Not at h
    by_cases hS : ∃ P, 1 ≤ Δ P
    · obtain ⟨P, hP⟩ := hS
      obtain ⟨Q, hQ⟩ := hex P
      refine ⟨P, Q, Ne.symm hQ, Or.inr fun R hR => ?_⟩
      by_contra hRP
      exact absurd hR (not_le.2 (h P R (Ne.symm hRP) hP))
    · push Not at hS
      obtain ⟨Q, hQ⟩ := hex a
      exact ⟨a, Q, Ne.symm hQ, Or.inr fun R hR => absurd hR (not_le.2 (hS R))⟩

/-- `(d(1/z)/(1/z))^n = (dz/z)^n` for `n` even, since `d(1/z)/(1/z) = -dz/z`. -/
theorem dlogPow_inv {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsIntegral C] (z : C.functionField) (hz : z ≠ 0) {n : ℕ} (hn : Even n) :
    dlogPow sC z⁻¹ n = dlogPow sC z n := by
  letI := functionFieldAlgebra sC
  have hv : (z⁻¹)⁻¹ • exteriorPower.ιMulti C.functionField 1
      (fun _ => KaehlerDifferential.D k C.functionField z⁻¹) =
      (-1 : C.functionField) • (z⁻¹ • exteriorPower.ιMulti C.functionField 1
        (fun _ => KaehlerDifferential.D k C.functionField z)) := by
    rw [Derivation.leibniz_inv, inv_inv, smul_smul]
    rw [show (fun _ : Fin 1 => (-(z⁻¹ ^ 2)) • KaehlerDifferential.D k C.functionField z) =
        fun i => (fun _ : Fin 1 => -(z⁻¹ ^ 2)) i •
          (fun _ : Fin 1 => KaehlerDifferential.D k C.functionField z) i from rfl,
      AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      pow_one, smul_smul]
    congr 1
    field_simp
  unfold dlogPow
  simp only
  rw [hv, show (fun _ : Fin n => (-1 : C.functionField) • (z⁻¹ • exteriorPower.ιMulti
      C.functionField 1 fun _ => KaehlerDifferential.D k C.functionField z)) =
      fun i => (fun _ : Fin n => (-1 : C.functionField)) i • (fun _ : Fin n => z⁻¹ •
        exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField z) i from rfl,
    MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hn.neg_one_pow, one_smul]

/-- `(dw/w)^{⊗1} = w⁻¹ • dw`. -/
private theorem dlogPow_one {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsIntegral C] (w : C.functionField) :
    letI := functionFieldAlgebra sC
    ∃ ω : RationalPluriForms sC 1 (1 : ℕ),
      ω = (PiTensorProduct.tprod C.functionField fun _ : Fin 1 =>
        exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField w) ∧ dlogPow sC w 1 = w⁻¹ • ω := by
  letI := functionFieldAlgebra sC
  refine ⟨_, rfl, ?_⟩
  unfold dlogPow
  simp only
  rw [show (fun _ : Fin 1 => w⁻¹ • exteriorPower.ιMulti C.functionField 1 fun _ =>
      KaehlerDifferential.D k C.functionField w) = fun i => (fun _ : Fin 1 => w⁻¹) i •
        (fun _ : Fin 1 => exteriorPower.ιMulti C.functionField 1 fun _ =>
          KaehlerDifferential.D k C.functionField w) i from rfl,
    MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    pow_one]
  rfl

/-- `ord_R((dw/w)^{⊗n}) = n · ord_R(dw/w)`, and `(dw/w)^{⊗n} ≠ 0` when `dw/w ≠ 0`. -/
theorem ordForm_dlogPow_eq_mul {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1) (w : C.functionField)
    (hw : dlogPow sC w 1 ≠ 0) (n : ℕ) :
    dlogPow sC w n ≠ 0 ∧ ∀ R : MMP.Mori.PrimeDivisor C,
      R.ordForm (dlogPow sC w n) = n * R.ordForm (dlogPow sC w 1) := by
  letI := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) hd1
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hC (n := 1) hd1
  set η : ⋀[C.functionField]^1 Ω[C.functionField⁄k] := w⁻¹ • exteriorPower.ιMulti
    C.functionField 1 fun _ => KaehlerDifferential.D k C.functionField w with hη
  set c := b.repr η () with hc
  have hηc : η = c • b () := (basis_unit_repr_smul b η).symm
  have hpow : ∀ j : ℕ, dlogPow sC w j = c ^ j • ZTensorPower.basis b j () := fun j =>
    tprod_smul_eq_smul_basis b c j _ (by unfold dlogPow; simp only; rw [← hηc])
  have hc0 : c ≠ 0 := by
    intro h
    apply hw
    rw [hpow 1, h, zero_pow one_ne_zero, zero_smul]
    rfl
  have hrepr : ∀ j : ℕ, (ZTensorPower.basis b (j : ℤ)).repr (dlogPow sC w j) () = c ^ j :=
    fun j => by rw [hpow j]; simp
  have hne : ∀ j : ℕ, dlogPow sC w j ≠ 0 := fun j => by
    rw [hpow j]
    exact smul_ne_zero (pow_ne_zero j hc0) ((ZTensorPower.basis b j).ne_zero ())
  refine ⟨hne n, fun R => ?_⟩
  obtain ⟨N, hN⟩ := R.exists_ordForm_eq_ord_add_mul hd b
  rw [hN _ _ (hne n), hN _ _ (hne 1), hrepr, hrepr, ← zpow_natCast, ← zpow_natCast,
    ord_zpow _ hc0, ord_zpow _ hc0]
  push_cast
  ring

/-- `ord(w⁻¹) = -ord(w)`. -/
private theorem ord_inv' {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    {w : C.functionField} (hw : w ≠ 0) (x : C) : C.ord w⁻¹ x = -C.ord w x := by
  rw [← zpow_neg_one, ord_zpow _ hw]
  ring

/-- At a point `R` where `ord_R(w) = 1`, `dw/w ≠ 0` and `ord_R(dw/w) = -1`. -/
theorem ordForm_dlogPow_one_of_ord_eq_one {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1)
    (R : MMP.Mori.PrimeDivisor C) (w : C.functionField) (hw : C.ord w R.genericPoint = 1) :
    dlogPow sC w 1 ≠ 0 ∧ R.ordForm (dlogPow sC w 1) = -1 := by
  letI := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨ω, hω, hdl⟩ := dlogPow_one sC w
  obtain ⟨hω0, hωR⟩ := ordForm_d_eq_zero hC hdim R w hw ω hω
  rw [hdl]
  refine ⟨smul_ne_zero (inv_ne_zero hw0) hω0, ?_⟩
  rw [R.ordForm_smul_of_topologicalKrullDim_eq hd1 (inv_ne_zero hw0) hω0, hωR, ord_inv' hw0, hw]
  rfl

open scoped Classical in
/-- **The divisor of `(dz/z)^n` for `div z = P - Q`** on a smooth proper curve of genus zero
is `-n(P + Q)`. -/
theorem ordForm_dlogPow_of_ord {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (hg : K.h0 k sC = 0) {P Q : MMP.Mori.PrimeDivisor C} (hPQ : P ≠ Q)
    (z : C.functionField) (hz0 : z ≠ 0)
    (hz : ∀ R : MMP.Mori.PrimeDivisor C, C.ord z R.genericPoint =
      (if R = P then 1 else 0) - (if R = Q then 1 else 0)) (n : ℕ) :
    dlogPow sC z n ≠ 0 ∧ ∀ R : MMP.Mori.PrimeDivisor C, R.ordForm (dlogPow sC z n) =
      -(n : ℤ) * ((if R = P then 1 else 0) + (if R = Q then 1 else 0)) := by
  letI := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hzP : C.ord z P.genericPoint = 1 := by simpa [hPQ] using hz P
  have hzQ : C.ord z⁻¹ Q.genericPoint = 1 := by
    rw [ord_inv' hz0, hz Q]; simp [Ne.symm hPQ]
  obtain ⟨h1, hfP⟩ := ordForm_dlogPow_one_of_ord_eq_one hC hdim P z hzP
  obtain ⟨h1', hfQ'⟩ := ordForm_dlogPow_one_of_ord_eq_one hC hdim Q z⁻¹ hzQ
  have hfQ : Q.ordForm (dlogPow sC z 1) = -1 := by
    have e1 := (ordForm_dlogPow_eq_mul hC hdim z h1 2).2 Q
    have e2 := (ordForm_dlogPow_eq_mul hC hdim z⁻¹ h1' 2).2 Q
    rw [dlogPow_inv sC z hz0 even_two, e1, hfQ'] at e2
    push_cast at e2
    omega
  obtain ⟨ω, hω, hdl⟩ := dlogPow_one sC z
  have hω0 : ω ≠ 0 := fun h => h1 (by rw [hdl, h, smul_zero])
  have hfR : ∀ R : MMP.Mori.PrimeDivisor C, R ≠ P → R ≠ Q →
      0 ≤ R.ordForm (dlogPow sC z 1) := fun R hRP hRQ => by
    have hzR : C.ord z R.genericPoint = 0 := by simpa [hRP, hRQ] using hz R
    rw [hdl, R.ordForm_smul_of_topologicalKrullDim_eq hd1 (inv_ne_zero hz0) hω0, ord_inv' hz0,
      hzR, neg_zero, zero_add]
    exact zero_le_ordForm_d hC hdim R z hzR.ge ω hω hω0
  have hK2 : (K.sum fun _ a => a) = -2 := by
    have h3 := sum_coeff_canonical_eq hC hsm hp hK
    rw [hg, sum_intCast] at h3
    exact_mod_cast (by simpa using h3 : ((K.sum fun _ a => a : ℤ) : ℚ) = -2)
  have hsum : ((divisorOfForm (dlogPow sC z 1)).sum fun _ a => a) = -2 := by
    simpa [hK2] using sum_divisorOfForm_eq_mul_sum hC hsm hp hdim hK h1
  set D := divisorOfForm (dlogPow sC z 1) with hD
  have hDR : ∀ R, D R = R.ordForm (dlogPow sC z 1) := fun _ => rfl
  have hD0 : D + Finsupp.single P 1 + Finsupp.single Q 1 = 0 := by
    apply eq_zero_of_nonneg_of_sum_eq_zero
    · intro R
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Finsupp.coe_zero,
        Pi.zero_apply]
      by_cases h1 : R = P
      · subst h1; simp [hPQ, Ne.symm hPQ, hDR, hfP]
      · by_cases h2 : R = Q
        · subst h2; simp [Ne.symm h1, hDR, hfQ]
        · simp [Ne.symm h1, Ne.symm h2, hDR, hfR R h1 h2]
    · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum,
        Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
      norm_num
  obtain ⟨hne, hmul⟩ := ordForm_dlogPow_eq_mul hC hdim z h1 n
  refine ⟨hne, fun R => ?_⟩
  rw [hmul R]
  have := congrArg (fun D' : Divisor C => D' R) hD0
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, Finsupp.coe_zero,
    Pi.zero_apply] at this
  rw [← hDR]
  by_cases h1 : R = P
  · subst h1
    simp only [if_pos rfl, if_neg hPQ, if_neg (Ne.symm hPQ), if_true] at this ⊢
    linear_combination (n : ℤ) * this
  · by_cases h2 : R = Q
    · subst h2
      simp only [if_pos rfl, if_neg h1, if_neg (Ne.symm h1)] at this ⊢
      linear_combination (n : ℤ) * this
    · simp only [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)] at this ⊢
      linear_combination (n : ℤ) * this

/-- If `G = mΔ` with `deg Δ = 2`, then `deg G = 2m`. -/
private theorem sum_eq_two_mul_of_toQDivisor_eq {C : Scheme.{u}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {Δ : QDivisor C} {m : ℕ} {G : Divisor C}
    (hG : Divisor.toQDivisor G = (m : ℤ) • Δ) (hΔs : (Δ.sum fun _ a => a) = 2) :
    (G.sum fun _ a => a) = 2 * m := by
  have h1 : ((G.sum fun _ a => a : ℤ) : ℚ) = (Divisor.toQDivisor G).sum fun _ a => a := by
    simp only [Finsupp.sum, Int.cast_sum, Divisor.toQDivisor,
      DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply, DivisorWithCoeffs.mapCoeffs,
      Int.coe_castAddHom, Finsupp.mapRange_apply]
    rw [Finsupp.support_mapRange_of_injective _ _ Int.cast_injective]
  have h2 : ((Divisor.toQDivisor G).sum fun _ a => a) = m * 2 := by
    rw [hG, Finsupp.sum_smul_index' (fun _ => rfl), ← hΔs, Finsupp.mul_sum]
    rfl
  have : ((G.sum fun _ a => a : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by
    rw [h1, h2]
    push_cast
    ring
  exact_mod_cast this

open scoped Classical in
/-- `f (dz/z)^{12m}` has divisor `-12 G` as soon as `div f = 12m(P + Q) - 12G`. -/
private theorem ordForm_smul_add_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [LocallyOfFiniteType sC] (hdim : topologicalKrullDim C = 1) {m : ℕ} {G : Divisor C}
    {P Q : MMP.Mori.PrimeDivisor C} {ω : RationalPluriForms sC 1 (12 * m : ℕ)} (hω0 : ω ≠ 0)
    (hω : ∀ R : MMP.Mori.PrimeDivisor C, R.ordForm ω =
      -((12 * m : ℕ) : ℤ) * ((if R = P then 1 else 0) + (if R = Q then 1 else 0)))
    {f : C.functionField} (hf : f ≠ 0)
    (hford : ∀ R : MMP.Mori.PrimeDivisor C, C.ord f R.genericPoint =
      12 * m * ((if R = P then 1 else 0) + (if R = Q then 1 else 0)) - 12 * G R)
    (R : MMP.Mori.PrimeDivisor C) : R.ordForm (f • ω) + (12 • G).coeff R = 0 := by
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  rw [R.ordForm_smul_of_topologicalKrullDim_eq hd1 hf hω0, hford R, hω R,
    show (12 • G).coeff R = 12 * G R by simp [DivisorWithCoeffs.coeff_apply]]
  push_cast
  ring

open scoped Classical in
/-- The case `Δ = P + Q` of `exists_ordForm_add_eq_zero_of_genus_zero`: `(dz/z)^{12m}` itself
is the normalized section. -/
private theorem exists_ordForm_add_eq_zero_of_eq_add {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [LocallyOfFiniteType sC] (hdim : topologicalKrullDim C = 1) {Δ : QDivisor C} {m : ℕ}
    {G : Divisor C} (hGc : ∀ P : MMP.Mori.PrimeDivisor C, ((G P : ℤ) : ℚ) = m * Δ P)
    {P Q : MMP.Mori.PrimeDivisor C} (hPQ : P ≠ Q) (hP1 : Δ P = 1) (hQ1 : Δ Q = 1)
    (h0 : ∀ R, R ≠ P → R ≠ Q → Δ R = 0) {z : C.functionField} (hz0 : z ≠ 0)
    (hz : ∀ R : MMP.Mori.PrimeDivisor C, C.ord z R.genericPoint =
      (if R = P then 1 else 0) - (if R = Q then 1 else 0))
    (hω0 : dlogPow sC z (12 * m) ≠ 0)
    (hω : ∀ R : MMP.Mori.PrimeDivisor C, R.ordForm (dlogPow sC z (12 * m)) =
      -((12 * m : ℕ) : ℤ) * ((if R = P then 1 else 0) + (if R = Q then 1 else 0))) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ), s ≠ 0 ∧
      (∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0) ∧
      ∀ R : MMP.Mori.PrimeDivisor C, 1 ≤ Δ.coeff R → ∃ w : C.functionField,
        C.ord w R.genericPoint = 1 ∧ (s - dlogPow sC w (12 * m) = 0 ∨
          1 ≤ R.ordForm (s - dlogPow sC w (12 * m)) + (12 • G).coeff R) := by
  have hGR : ∀ R : MMP.Mori.PrimeDivisor C, G R =
      m * ((if R = P then 1 else 0) + (if R = Q then 1 else 0)) := fun R => by
    have h' := hGc R
    by_cases h1 : R = P
    · subst h1
      rw [hP1] at h'
      simp only [if_neg hPQ]
      norm_num at h' ⊢
      exact_mod_cast h'
    · by_cases h2 : R = Q
      · subst h2
        rw [hQ1] at h'
        simp only [if_neg h1]
        norm_num at h' ⊢
        exact_mod_cast h'
      · rw [h0 R h1 h2] at h'
        simp only [if_neg h1, if_neg h2]
        norm_num at h' ⊢
        exact_mod_cast h'
  refine ⟨(1 : C.functionField) • dlogPow sC z (12 * m), smul_ne_zero one_ne_zero hω0,
    ordForm_smul_add_eq_zero hdim hω0 hω one_ne_zero fun R => ?_, fun R hR => ?_⟩
  · rw [(Scheme.ord_eq_iff (n := 0) R.coheight_genericPoint one_ne_zero).2 (by simp), hGR R]
    ring
  have hR' : 1 ≤ Δ R := by simpa [DivisorWithCoeffs.coeff_apply] using hR
  by_cases h1 : R = P
  · subst h1
    exact ⟨z, by simpa [hPQ] using hz R, Or.inl (by rw [one_smul, sub_self])⟩
  · by_cases h2 : R = Q
    · subst h2
      refine ⟨z⁻¹, ?_, Or.inl ?_⟩
      · rw [ord_inv' hz0, hz R]
        simp [h1]
      · rw [one_smul, dlogPow_inv sC z hz0 ⟨6 * m, by ring⟩, sub_self]
    · rw [h0 R h1 h2] at hR'
      norm_num at hR'

open scoped Classical in
/-- The case `⌊Δ⌋ ⊆ {P}` of `exists_ordForm_add_eq_zero_of_genus_zero`: a multiple
`g (dz/z)^{12m}`, normalized at `P` by a constant. -/
private theorem exists_ordForm_add_eq_zero_of_floor_subset {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C] [LocallyOfFiniteType sC]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (hg : K.h0 k sC = 0) {Δ : QDivisor C} (hΔc : ∀ P : MMP.Mori.PrimeDivisor C, Δ P ≤ 1)
    {m : ℕ} {G : Divisor C} (hGc : ∀ P : MMP.Mori.PrimeDivisor C, ((G P : ℤ) : ℚ) = m * Δ P)
    (hGs : (G.sum fun _ a => a) = 2 * m) {P Q : MMP.Mori.PrimeDivisor C} (hPQ : P ≠ Q)
    (hfloor : ∀ R, 1 ≤ Δ R → R = P) {z : C.functionField}
    (hz : ∀ R : MMP.Mori.PrimeDivisor C, C.ord z R.genericPoint =
      (if R = P then 1 else 0) - (if R = Q then 1 else 0))
    (hω0 : dlogPow sC z (12 * m) ≠ 0)
    (hω : ∀ R : MMP.Mori.PrimeDivisor C, R.ordForm (dlogPow sC z (12 * m)) =
      -((12 * m : ℕ) : ℤ) * ((if R = P then 1 else 0) + (if R = Q then 1 else 0))) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ), s ≠ 0 ∧
      (∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0) ∧
      ∀ R : MMP.Mori.PrimeDivisor C, 1 ≤ Δ.coeff R → ∃ w : C.functionField,
        C.ord w R.genericPoint = 1 ∧ (s - dlogPow sC w (12 * m) = 0 ∨
          1 ≤ R.ordForm (s - dlogPow sC w (12 * m)) + (12 • G).coeff R) := by
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  set ω := dlogPow sC z (12 * m)
  obtain ⟨g, hg0, hgord⟩ := exists_ord_add_eq_zero hC hsm hp hdim hK hg
    (12 • G - ((12 * m : ℕ) : ℤ) • (Finsupp.single P 1 + Finsupp.single Q 1)) (by
      rw [sum_eq_liftAddHom, map_sub, map_nsmul, map_zsmul, map_add,
        Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single, ← sum_eq_liftAddHom,
        hGs]
      simp only [AddMonoidHom.id_apply, smul_eq_mul]
      push_cast
      ring)
  have hgord' : ∀ R : MMP.Mori.PrimeDivisor C, C.ord g R.genericPoint =
      12 * m * ((if R = P then 1 else 0) + (if R = Q then 1 else 0)) - 12 * G R := fun R => by
    have := hgord R
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul] at this
    by_cases h1 : R = P
    · subst h1
      simp [hPQ, Ne.symm hPQ] at this ⊢
      linarith
    · by_cases h2 : R = Q
      · subst h2
        simp [h1, Ne.symm h1] at this ⊢
        linarith
      · simp [h1, h2, Ne.symm h1, Ne.symm h2] at this ⊢
        linarith
  by_cases hP1 : 1 ≤ Δ P
  · have hGP : G P = m := by
      have := hGc P
      rw [le_antisymm (hΔc P) hP1, mul_one] at this
      exact_mod_cast this
    have hgP : C.ord g P.genericPoint = 0 := by
      rw [hgord' P, if_pos rfl, if_neg hPQ, hGP]
      ring
    obtain ⟨u, hu0, huord, hu⟩ := exists_const_ord_mul_sub_one_pos hC hdim P g hg0 hgP
    refine ⟨(g * u) • ω, smul_ne_zero (mul_ne_zero hg0 hu0) hω0,
      ordForm_smul_add_eq_zero hdim hω0 hω (mul_ne_zero hg0 hu0) fun R => ?_, fun R hR => ?_⟩
    · rw [Scheme.ord_mul hg0 hu0, huord R, add_zero, hgord' R]
    have hR' : 1 ≤ Δ R := by simpa [DivisorWithCoeffs.coeff_apply] using hR
    obtain rfl := hfloor R hR'
    refine ⟨z, by simpa [hPQ] using hz R, ?_⟩
    rw [show (g * u) • ω - ω = (g * u - 1) • ω by rw [sub_smul, one_smul]]
    rcases hu with h | h
    · exact Or.inl (by rw [h, zero_smul])
    · right
      have hne1 : g * u - 1 ≠ 0 := fun h' => by rw [h'] at h; simp at h
      rw [R.ordForm_smul_of_topologicalKrullDim_eq hd1 hne1 hω0, hω R,
        show (12 • G).coeff R = 12 * G R by simp [DivisorWithCoeffs.coeff_apply], hGP]
      simp only [if_neg hPQ]
      push_cast
      linarith
  · refine ⟨g • ω, smul_ne_zero hg0 hω0, ordForm_smul_add_eq_zero hdim hω0 hω hg0 hgord',
      fun R hR => ?_⟩
    have hR' : 1 ≤ Δ R := by simpa [DivisorWithCoeffs.coeff_apply] using hR
    obtain rfl := hfloor R hR'
    exact absurd hR' hP1

/-- **A nowhere vanishing section normalized along the floor, in genus zero** (FA 12.2.11, case
(12.2.11.3), genus zero). Let `C` be a smooth proper curve of genus zero over an algebraically
closed field `k` with canonical divisor `K`, `Δ` a boundary of degree `2` and `G = mΔ` integral.
Then `𝒪(12m(K_C + Δ))` has a section `s ≠ 0` with `ord_P(s) + coeff_P(12 G) = 0` at every prime
divisor `P`, such that at every `R ∈ ⌊Δ⌋`, `s - (dw/w)^{12m}` vanishes for a local parameter `w`
at `R`. Writing `div z = P - Q` for points `P ≠ Q` carrying `⌊Δ⌋`, `s` is a multiple
`f (dz/z)^{12m}`, normalized at `P` (and at `Q`, by `dlogPow_inv`) by a constant. -/
theorem exists_ordForm_add_eq_zero_of_genus_zero {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QDivisor C} (hΔ : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sC)
    {m : ℕ} {G : Divisor C} (hG : Divisor.toQDivisor G = (m : ℤ) • Δ) (hg : K.h0 k sC = 0)
    (hΔ2 : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = 2) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ), s ≠ 0 ∧
      (∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0) ∧
      ∀ R : MMP.Mori.PrimeDivisor C, 1 ≤ Δ.coeff R → ∃ w : C.functionField,
        C.ord w R.genericPoint = 1 ∧ (s - dlogPow sC w (12 * m) = 0 ∨
          1 ≤ R.ordForm (s - dlogPow sC w (12 * m)) + (12 • G).coeff R) := by
  classical
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hΔc : ∀ P : MMP.Mori.PrimeDivisor C, 0 ≤ Δ P ∧ Δ P ≤ 1 := fun P =>
    hΔ.2.2.2 ⟨P, inferInstance, P.isDiscreteValuationRing_localRing⟩
  have hΔs : (Δ.sum fun _ a => a) = 2 := (sum_toQWeilDivisor Δ).symm.trans hΔ2
  have hGc : ∀ P : MMP.Mori.PrimeDivisor C, ((G P : ℤ) : ℚ) = m * Δ P := fun P => by
    simpa [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply] using
      congrArg (fun D : QDivisor C => D P) hG
  obtain ⟨P, Q, hPQ, hcase⟩ := exists_pair_of_sum_eq_two Δ hΔc hΔs
  obtain ⟨z, hz0, hz⟩ := exists_ord_add_eq_zero hC hsm hp hdim hK hg
    (Finsupp.single Q 1 - Finsupp.single P 1) (by
      rw [sum_eq_liftAddHom, map_sub, Finsupp.liftAddHom_apply_single,
        Finsupp.liftAddHom_apply_single]
      rfl)
  have hz' : ∀ R : MMP.Mori.PrimeDivisor C, C.ord z R.genericPoint =
      (if R = P then 1 else 0) - (if R = Q then 1 else 0) := fun R => by
    have := hz R
    simp only [Finsupp.sub_apply, Finsupp.single_apply] at this
    by_cases h1 : R = P
    · subst h1
      simp [hPQ, Ne.symm hPQ] at this ⊢
      omega
    · by_cases h2 : R = Q
      · subst h2
        simp [h1, Ne.symm h1] at this ⊢
        omega
      · simp [h1, h2, Ne.symm h1, Ne.symm h2] at this ⊢
        omega
  obtain ⟨hω0, hω⟩ := ordForm_dlogPow_of_ord hC hsm hp hdim hK hg hPQ z hz0 hz' (12 * m)
  rcases hcase with ⟨hP1, hQ1, h0⟩ | hfloor
  · exact exists_ordForm_add_eq_zero_of_eq_add hdim hGc hPQ hP1 hQ1 h0 hz0 hz' hω0 hω
  · exact exists_ordForm_add_eq_zero_of_floor_subset hC hsm hp hdim hK hg (fun P => (hΔc P).2)
      hGc (sum_eq_two_mul_of_toQDivisor_eq hG hΔs) hPQ hfloor hz' hω0 hω

/-- The genus zero case of `exists_isNormalizedSection_of_degree_eq_zero`. -/
private theorem exists_of_genus_zero {k : Type u} [Field k] [IsAlgClosed k]
    (ε : EllipticNormalizationDatum k) {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QDivisor C} (hΔ : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sC)
    {m : ℕ} (hm : 0 < m) {G : Divisor C} (hG : Divisor.toQDivisor G = (m : ℤ) • Δ)
    (hg : K.h0 k sC = 0)
    (hΔ2 : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = 2) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ),
      IsNormalizedSection ε sC Δ (12 * m) (12 • G) s ∧ s ≠ 0 ∧
        ∀ P : MMP.Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0 := by
  obtain ⟨s, hs0, hord, hnorm⟩ :=
    exists_ordForm_add_eq_zero_of_genus_zero sC hC hsm hp hdim hK hΔ hG hg hΔ2
  have hΔne : Δ ≠ 0 := by
    rintro rfl
    rw [sum_toQWeilDivisor, Finsupp.sum_zero_index] at hΔ2
    norm_num at hΔ2
  refine ⟨s, ⟨hC, hsm, hdim, fun R =>
    (hΔ.2.2.2 ⟨R, inferInstance, R.isDiscreteValuationRing_localRing⟩).1,
    Nat.mul_pos (by norm_num) hm, ?_, ?_, fun _ _ h _ => absurd h hΔne, fun _ => hnorm⟩, hs0, hord⟩
  · have h12 : Divisor.toQDivisor (12 • G) = 12 • Divisor.toQDivisor G :=
      map_nsmul (DivisorWithCoeffs.mapCoeffsAddMonoidHom (Int.castAddHom ℚ)) 12 G
    rw [h12, hG]
    ext R
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, nsmul_eq_mul,
      zsmul_eq_mul]
    push_cast
    ring
  · exact (mem_pluricanonicalSections_of_ne_bot top_ne_bot).2 fun R _ _ => by
      have := hord R
      omega

/-- **Nowhere vanishing normalized sections in degree zero** (proof of FA 12.2.11, case
(12.2.11.3)). Let `C` be a smooth connected proper curve over an algebraically closed field `k`
with canonical divisor `K`, `Δ` a boundary on `C`, `m > 0` and `G = mΔ` integral, with
`deg(K + Δ) = 0`. Then for every normalization datum `ε` for elliptic curves there is a section
`s ∈ Γ(C, 𝒪(12m(K_C + Δ)))` which is normalized (`MMP.Flips.IsNormalizedSection`) and vanishes
nowhere: `s ≠ 0` and `ord_P(s) + coeff_P(12 G) = 0` at every prime divisor `P`. -/
@[mmp "lem_fa12a_normalized_sections_degree_zero"]
public theorem exists_isNormalizedSection_of_degree_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] (ε : EllipticNormalizationDatum k) {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QDivisor C} (hΔ : (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).IsBoundary sC)
    {m : ℕ} (hm : 0 < m) {G : Divisor C} (hG : Divisor.toQDivisor G = (m : ℤ) • Δ)
    (hdeg : (K.sum fun _ a => (a : ℚ)) + Δ.sum (fun _ a => a) = 0) :
    ∃ s : RationalPluriForms sC 1 (12 * m : ℕ),
      IsNormalizedSection ε sC Δ (12 * m) (12 • G) s ∧ s ≠ 0 ∧
        ∀ P : Mori.PrimeDivisor C, P.ordForm s + (12 • G).coeff P = 0 := by
  have hdeg' : (K.sum fun _ a => (a : ℚ)) +
      (MMP.Fourfold.QDivisor.toQWeilDivisor Δ).sum (fun _ a => a) = 0 := by
    rwa [sum_toQWeilDivisor]
  classical
  rcases hΔ.degree_zero_curve_types hC hsm hp hK hdeg' with ⟨hg, hΔ0⟩ | ⟨hg, hΔ2, -⟩
  · exact exists_of_genus_one ε sC hC hsm hp hdim hK hΔ hm hG hdeg hg hΔ0
  · exact exists_of_genus_zero ε sC hC hsm hp hdim hK hΔ hm hG hg hΔ2

end MMP.Flips

end
