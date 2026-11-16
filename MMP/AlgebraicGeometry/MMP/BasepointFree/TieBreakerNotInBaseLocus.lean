module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.TieBreakerRestriction
public import MMP.AlgebraicGeometry.MMP.BasepointFree.TieBreakerNonvanishing

@[expose] public section

/-!
# The image of the tie-breaking divisor is not in the base locus of `|bD|`

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)` with a tie-breaker `(j', c)`, test boundary `A`, and `F = F_{j'}`. Then for every
integer `b ≥ max(b₁, ⌈cm + a⌉)`, with `b₁` the non-vanishing bound on `F`, the image `f(F)` is not
contained in `Bs|bD|`.

Fix a pull-back `D'` of `D`. A nonzero element of `H⁰(F, 𝒪_Y(bD' + ⌈A⌉)|_F)` is the restriction
of a section `τ` of `𝒪_Y(bD' + ⌈A⌉)`, since restriction to `F` is onto. As `⌈A⌉` is effective and
`f`-exceptional, `τ = f^*σ · s_{⌈A⌉}` for a section `σ` of `𝒪_X(bD)`. If `f(F) ⊆ Bs|bD|`, then
`F` occurs in `f^*(σ)₀`, and since `F` does not occur in `⌈A⌉` the section `τ` vanishes along `F`;
its restriction to `F` is then zero, a contradiction.

## Main results

* `MMP.Mori.IsBasepointFreeTieBreaker.exists_forall_not_image_subset_baseLocus`: for `b` large,
  `f(F_{j'})` is not contained in `Bs|bD|`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 5
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aBpfDivisorNotInBaseLocusProof

/-- **Restriction to a prime divisor kills the sections vanishing along it.** On a smooth variety
`Y`, a global section of `𝒪_Y(N + F)` that is a section of `𝒪_Y(N)` restricts to zero in
`H⁰(F, i^* 𝒪_Y(N + F))`. -/
private theorem restriction_eq_zero_of_mem {k : Type} [Field k] {Y : Scheme.{0}}
    (g : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] (hV : MMP.Mori.IsVariety k g)
    (hsm : IsSmoothScheme g) (F : MMP.Mori.PrimeDivisor Y) (N D : Divisor Y)
    (hD : D = N + Finsupp.single F 1) (x : cohomologyOverField k g D.divisorialSheaf 0)
    (τ : N.divisorialSubmodule ⊤)
    (hx : ((cohomologyOverFieldZeroLinearIso k g D.divisorialSheaf).hom x :
      D.divisorialSubmodule ⊤).1 = τ.1) :
    (cohomologyOverFieldMap k g
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          D.divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι g
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj D.divisorialSheaf) 0).inv).hom
      x = 0 := by
  subst hD
  obtain ⟨hz, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction g hV hsm F
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm N)
  obtain ⟨d, -, hfg, -, -⟩ := exists_cohomologyOverField_longExactSequence k g hS
  set x' := (cohomologyOverFieldZeroLinearIso k g N.divisorialSheaf).inv τ
  have hxx : x = cohomologyOverFieldMap k g (Divisor.divisorialSheafInclusion
      (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one) :
        N ≤ N + Finsupp.single F 1)) 0 x' := by
    apply (cohomologyOverFieldZeroLinearIso k g _).toLinearEquiv.injective
    change (cohomologyOverFieldZeroLinearIso k g _).hom x =
      (cohomologyOverFieldZeroLinearIso k g _).hom (cohomologyOverFieldMap k g _ 0 x')
    rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
    apply Subtype.ext
    rw [hx, show (cohomologyOverFieldZeroLinearIso k g N.divisorialSheaf).hom x' = τ from
      Iso.inv_hom_id_apply _ _]
    rfl
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hxx, (hfg 0).apply_apply_eq_zero, map_zero]

/-- Read at the generic points, `MMP.Fourfold.fieldMap f` is `f^*` on function fields. -/
private theorem stalkSpecializes_fieldMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (ZX : irreducibleComponents X) (ZY : irreducibleComponents Y)
    (a : X.presheaf.stalk (componentGenericPoint X ZX)) :
    Y.presheaf.stalkSpecializes (genericPoint_specializes _) (MMP.Fourfold.fieldMap f ZX ZY a) =
      functionFieldMap f (X.presheaf.stalkSpecializes (genericPoint_specializes _) a) := by
  obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq a
  rw [MMP.Fourfold.fieldMap_germ]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, MMP.Fourfold.functionFieldMap_germ]

/-- **A section of `f^*M + E` vanishes along a prime divisor mapping into `Bs |M|`.** Let
`f : Y ⟶ X` be a proper birational morphism of normal varieties, `M` a Cartier divisor on `X` with
pull-back `B'`, and `E ≥ 0` a Cartier `f`-exceptional divisor. If `P` is a prime divisor of `Y` not
in `E` with `f(η_P)` in the base locus of `M`, then every global section of `𝒪_Y(B' + E)` is a
section of `𝒪_Y(B' + E - P)`. -/
private theorem isDivisorialSection_sub_single_of_mem_baseLocus {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    (hX : MMP.Mori.IsVariety k sX) (hY : MMP.Mori.IsVariety k (f ≫ sX))
    [IsProper f] (hbir : IsBirationalMorphism f) {M : Divisor X} (hMc : M.IsCartier)
    {hM : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {B' : Divisor Y} (hB' : M.IsPullback f hM B') {E : Divisor Y} (hEc : E.IsCartier)
    (hE : 0 ≤ E)
    (hEexc : ∀ P : MMP.Mori.PrimeDivisor Y, E.coeff P ≠ 0 →
      RationalMap.IsExceptional f.toRationalMap P)
    {P : MMP.Mori.PrimeDivisor Y} (hEP : E.coeff P = 0)
    (hPM : f P.genericPoint ∈ (M.baseLocus : Set X))
    (τ : (B' + E).divisorialSubmodule ⊤) :
    (B' + E - Finsupp.single P 1).IsDivisorialSection ⊤ τ.1 := by
  haveI : IsDominant f := hbir.isDominant
  by_cases hτ : τ = 0
  · rw [hτ]
    exact ((B' + E - Finsupp.single P 1).divisorialSubmodule ⊤).zero_mem
  obtain ⟨e, he⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX f
    hX hY hbir M hMc hM B' hB' E hEc hE hEexc
  let τ' : (B' + E).divisorialSubmodule (f ⁻¹ᵁ ⊤) := ⟨τ.1, τ.2⟩
  set σ : M.divisorialSubmodule ⊤ := e.inv.app ⊤ τ'
  have hστ : (e.hom.app ⊤ σ : (B' + E).divisorialSubmodule (f ⁻¹ᵁ ⊤)) = τ' :=
    congrArg (fun φ => (φ.app ⊤).hom τ') e.inv_hom_id
  have hσ : σ ≠ 0 := by
    intro h0
    have : τ' = 0 := by
      rw [← hστ, h0]
      exact (Scheme.Modules.Hom.app e.hom ⊤).hom.map_zero
    exact hτ (Subtype.ext (congrArg Subtype.val this))
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have hφB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (principalDivisor φ).supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _
  set ψ := pullbackRationalFunction f φ hφB
  have hψ (ZY : irreducibleComponents Y) : (ψ : RationalFunctions Y) ZY = τ.1 ⟨ZY, trivial⟩ := by
    let ZX : irreducibleComponents X := pointComponent (genericPoint X)
    rw [show (ψ : RationalFunctions Y) ZY = MMP.Fourfold.fieldMap f ZX ZY (φ.1 ZX) from
      MMP.Fourfold.pullbackComponent_eq_fieldMap f hφB
        (Divisor.isLocalEquation_principalDivisor φ ⊤) ZY trivial ZX]
    apply MMP.Intersection.stalkSpecializes_injective
      (genericPoint_specializes (componentGenericPoint Y ZY))
    rw [stalkSpecializes_fieldMap]
    have h2 := (he ⊤ σ ZX trivial ZY trivial).1
    rw [hστ] at h2
    exact h2.symm
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add hMc
  have hZ' : (M.zeroDivisor σ hσ).IsPullback f
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _)
      (principalDivisor ψ + B') :=
    ((Divisor.isPullback_principalDivisor (f := f) φ hφB).add
      (Divisor.isCartier_principalDivisor φ) hMc
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _) hB').of_eq
      (Divisor.zeroDivisor_eq _ σ hσ).symm
  obtain ⟨Q, hQ0, hηQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp <|
    MMP.Flips.preimage_supp_subset_supp_of_isPullback hZc (Divisor.zeroDivisor_nonneg _ σ hσ) hZ'
      (Divisor.baseLocus_le_supp _ σ hσ hPM)
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hηQ
  have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hZc (V := ⊤)
    (fun P _ => Divisor.zeroDivisor_nonneg _ σ hσ P) hZ' Q
    ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support Q, trivial⟩
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at hQ0 hnn
  intro R hR
  by_cases hRQ : R = Q
  · subst hRQ
    refine Or.inr ?_
    rw [← hψ, R.valuation_component, WithZero.exp_le_exp]
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add, hEP,
      DivisorWithCoeffs.coeff_single_self]
    omega
  · rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hRQ),
      sub_zero]
    exact τ.2 R hR

end MMP.FourfoldProofs.Km3aBpfDivisorNotInBaseLocusProof

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aBpfDivisorNotInBaseLocusProof in
/-- **The image of the tie-breaking divisor is not in the base locus** (Kollár–Mori 3.2, Step 5).
Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)` with a tie-breaker `(j', c)`. Then there is an integer `b₂` such that for every
integer `b ≥ b₂` the image `f(F_{j'})` is not contained in the base locus `Bs|bD|`. -/
@[mmp "lem_km3a_bpf_divisor_not_in_base_locus"]
public theorem IsBasepointFreeTieBreaker.exists_forall_not_image_subset_baseLocus
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c) :
    ∃ b₂ : ℤ, ∀ b : ℤ, b₂ ≤ b →
      ¬ f.base '' (F j').support ⊆ ((b • D).baseLocus : Set X) := by
  haveI hP : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  haveI : IsProper f := h.isLogResolution.isProper
  haveI : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f D
  obtain ⟨D', hD'⟩ := h.isCartier.exists_isPullback hB
  obtain ⟨b₁, hb₁⟩ := h.exists_nontrivial_cohomologyOverField_restriction hD'
  refine ⟨max b₁ ⌈c * m + a⌉, fun b hb hsub => ?_⟩
  have hbc : c * m + a ≤ b := Int.ceil_le.mp (le_of_max_le_right hb)
  haveI := hb₁ b (le_of_max_le_left hb)
  obtain ⟨y, hy⟩ := exists_ne (0 : cohomologyOverField k ((F j').idealSheaf.subschemeι ≫ f ≫ sX)
    ((Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj
      (b • D' + A.roundUp).divisorialSheaf) 0)
  obtain ⟨x, rfl⟩ := h.surjective_restriction_pullback_add_roundUp hbc hD' y
  obtain ⟨hAeff, hAexc⟩ := h.isEffective_roundUp_tieBreakerBoundary
  have hA0 : A.roundUp.coeff (F j') = 0 := by
    rw [DivisorWithCoeffs.coeff_roundUp]
    rcases MMP.Mori.coeff_tieBreakerBoundary h.injective (fun j ↦ (rj j : ℚ)) aj pj j' c
      (F j') with h0 | ⟨j, hj, hFj, -⟩
    · rw [h0, Int.ceil_zero]
    · exact absurd (h.injective hFj) hj
  have hbD' := hD'.zsmul h.isCartier b
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  set τ := (cohomologyOverFieldZeroLinearIso k (f ≫ sX) (b • D' + A.roundUp).divisorialSheaf).hom x
  exact hy <| restriction_eq_zero_of_mem (f ≫ sX) hP.toIsVariety hsm (F j')
    (b • D' + A.roundUp - Finsupp.single (F j') 1) _ (by abel) x
    ⟨τ.1, isDivisorialSection_sub_single_of_mem_baseLocus sX f h.isProperVariety.toIsVariety
      hP.toIsVariety h.isLogResolution.isBirationalMorphism (h.isCartier.zsmul b) hbD'
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hAeff hAexc hA0
      (hsub ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support _, rfl⟩) τ⟩ rfl

end MMP.Mori
