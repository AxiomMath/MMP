module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Relative Kawamata–Viehweg vanishing for a proper birational morphism

Let `k` be an algebraically closed field of characteristic zero, `f : Y ⟶ X` a proper birational
morphism of `k`-varieties with `Y` smooth, and `A` a divisor on `Y`. Suppose that `M` is an
`f`-nef `ℚ`-divisor and `B = ∑ aᵢ Dᵢ` a simple normal crossing `ℚ`-divisor with coefficients
`0 ≤ aᵢ < 1` such that `deg_C 𝒪_Y(A) = (M · C) + ∑ aᵢ (Dᵢ · C)` for every proper curve `C ⊆ Y`
contracted by `f`. Then `R^i f_* (ω_Y ⊗ 𝒪_Y(A)) = 0` for all `i > 0`.

The divisor `A - B` is `f`-nef by the curve equality, and `f`-big because `f` is birational, so
this is the relative Kawamata–Viehweg vanishing theorem for the smooth snc pair `(Y, B)`.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_canonical_add_of_isBirationalMorphism`

## Implementation notes

The sheaf `ω_Y ⊗ 𝒪_Y(A)` is written `𝒪_Y(K + A)` for a canonical divisor `K` of `Y`
(`MMP.Mori.Divisor.IsCanonicalDivisor`): on the smooth variety `Y` the canonical sheaf is
invertible, `ω_Y ≅ 𝒪_Y(K)`, and `𝒪_Y(K) ⊗ 𝒪_Y(A) ≅ 𝒪_Y(K + A)`. The conclusion is asserted for
every canonical divisor `K`.

The family of distinct prime divisors `Dᵢ` with coefficients `aᵢ` is the `ℚ`-divisor
`B = ∑ aᵢ Dᵢ`, and "the `Dᵢ` have snc union" is `MMP.Mori.DivisorWithCoeffs.IsSNC` of `B`: it
only concerns the components with `aᵢ ≠ 0`, the only ones entering the curve equality.

Every divisor on the smooth `Y` is Cartier, so `deg_C 𝒪_Y(A)` and `(Dᵢ · C) = deg_C 𝒪_Y(Dᵢ)` are
the degrees `MMP.Mori.Divisor.degreeOn` along `C`; `(M · C)` is
`MMP.Mori.QDivisor.intersectionNumber`. The higher direct images are the right derived functors
of `AlgebraicGeometry.Scheme.Modules.pushforward f`. The instances `IsLocallyNoetherian Y` and
`IsNormal Y`, consequences of `Y` being a smooth variety, are those under which divisors and
divisorial sheaves are defined.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 2.64,
  Corollary 2.68
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori

/-- An invertible module on an integral locally noetherian scheme has full support. -/
theorem supp_eq_univ_of_isInvertible {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 F] :
    SheafOfModules.supp F = Set.univ := by
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank F 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y F
  haveI : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y F
  haveI : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have h1 : Scheme.Modules.fiberRank F (genericPoint Y) = 1 :=
    Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank F 1 _
  rw [fiberRank_eq_finrank_stalk_of_isField _ _ (isField_stalk_genericPoint Y)] at h1
  have hηmem : genericPoint Y ∈ SheafOfModules.supp F := by
    refine (SheafOfModules.mem_supp_iff_nontrivial_stalk F _).mpr ?_
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    letI := F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (genericPoint Y)
    haveI : Subsingleton (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf (genericPoint Y)) :=
      hnt
    have h0 : Module.finrank (Y.presheaf.stalk (genericPoint Y))
        (TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf (genericPoint Y)) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (genericPoint_spec Y).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηmem) (SheafOfModules.isClosed_supp F)

private theorem relativeGenericRank_eq_one_of_isBirationalMorphism {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirationalMorphism f) {d : ℕ} (hY : topologicalKrullDim Y = d)
    (hX : topologicalKrullDim X = d) (F : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 F] :
    relativeGenericRank f F = 1 := by
  classical
  have := hf.isDominant
  have hgen : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hfib : ∀ z : Y, f z = f (genericPoint Y) → z = genericPoint Y := fun z hz =>
    eq_genericPoint_of_map_eq_genericPoint_of_dim_eq f f.isClosedMap hY hX (hz.trans hgen)
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank F 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y F
  haveI : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y F
  haveI : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have h1 : Scheme.Modules.fiberRank F (genericPoint Y) = 1 :=
    Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank F 1 _
  rw [fiberRank_eq_finrank_stalk_of_isField _ _ (isField_stalk_genericPoint Y)] at h1
  have hsupp := supp_eq_univ_of_isInvertible F
  have hηmem : genericPoint Y ∈ SheafOfModules.supp F := hsupp ▸ Set.mem_univ _
  letI : Unique ↥{z : Y | f z = f (genericPoint Y) ∧ z ∈ SheafOfModules.supp F} :=
    { default := ⟨genericPoint Y, rfl, hηmem⟩
      uniq := fun z => Subtype.ext (hfib z.1 z.2.1) }
  have hcomp : (Set.univ : Set ↥(SheafOfModules.supp F)) ∈
      irreducibleComponents ↥(SheafOfModules.supp F) := by
    haveI : IrreducibleSpace ↥(SheafOfModules.supp F) :=
      ((Homeomorph.setCongr hsupp).trans (Homeomorph.Set.univ Y)).symm.surjective.irreducibleSpace
        ((Homeomorph.setCongr hsupp).trans (Homeomorph.Set.univ Y)).symm.continuous
    rw [irreducibleComponents_eq_singleton]
    rfl
  have hgenS : ∀ z : ↥{z : Y | f z = f (genericPoint Y) ∧ z ∈ SheafOfModules.supp F},
      ∃ W : irreducibleComponents (SheafOfModules.supp F : Set Y),
      IsGenericPoint z.1 (Subtype.val '' W.1 : Set Y) := by
    intro z
    refine ⟨⟨Set.univ, hcomp⟩, ?_⟩
    rw [hfib z.1 z.2.1, Subtype.coe_image_univ, hsupp]
    exact Set.top_eq_univ (α := Y) ▸ genericPoint_spec Y
  have hfield : IsField (X.presheaf.stalk (f (genericPoint Y))) := by
    rw [hgen]
    exact isField_stalk_genericPoint X
  unfold relativeGenericRank
  rw [fiberRank_eq_finrank_stalk_of_isField _ _ hfield]
  letI := Stacks.Chow.supportFibreStalkModule f F (f (genericPoint Y))
  let e := Stacks.Chow.pushforwardStalkLinearEquivPi f F (SheafOfModules.isClosed_supp F)
    (f (genericPoint Y)) (Stacks.Chow.locallyFinite_irreducibleComponents_supp F) hgenS
  refine (LinearEquiv.finrank_eq
    (e.trans (LinearEquiv.piUnique (X.presheaf.stalk (f (genericPoint Y))) _))).trans (h1 ▸ ?_)
  have hbij : Function.Bijective (f.stalkMap (genericPoint Y)).hom := by
    refine ⟨?_, MMP.Fourfold.surjective_stalkMap_of_isBirationalMorphism hf _ rfl⟩
    letI := hfield.toField
    exact RingHom.injective _
  letI := F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (genericPoint Y)
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv (f.stalkMap (genericPoint Y)).hom (AddEquiv.refl _) hbij
    fun _ _ => rfl

private theorem isRelativelyBig_of_isBirationalMorphism {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [MMP.Mori.IsVariety k sX]
    [MMP.Mori.IsVariety k sY] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsProper f]
    (hf : IsBirationalMorphism f) {D : Divisor Y} (hD : ∀ m : ℤ, (m • D).IsCartier) :
    D.IsRelativelyBig f := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := hf.isDominant
  have hne : topologicalKrullDim Y ≠ ⊤ := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
  have hbot : topologicalKrullDim Y ≠ ⊥ := fun hb =>
    ((Order.krullDim_eq_bot_iff.mp hb).false
      (TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint Y))).elim
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim Y = d := by
    induction h : topologicalKrullDim Y using WithBot.recBotCoe with
    | bot => exact absurd h hbot
    | coe a =>
      have ha : a ≠ ⊤ := by
        rintro rfl
        exact hne h
      lift a to ℕ using ha
      exact ⟨a, rfl⟩
  have hdX : topologicalKrullDim X = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sY hf).trans hd
  have hcl : closure (Set.range f.base) = Set.univ := f.denseRange.closure_eq
  refine ⟨d, d, hd, ?_, 1 / 2, by norm_num, 0, fun m _ => ?_⟩
  · rw [← hdX]
    exact ((Homeomorph.setCongr hcl).trans
      (Homeomorph.Set.univ X)).isHomeomorph.topologicalKrullDim_eq
  · haveI := (hD m).isInvertibleModule_divisorialSheaf
    rw [relativeGenericRank_eq_one_of_isBirationalMorphism f hf hd hdX, Nat.sub_self, pow_zero]
    norm_num

private theorem exists_pos_smul_mem_range_toQDivisor {Y : Scheme.{0}} (B : QDivisor Y) :
    ∃ m : ℕ, 0 < m ∧ ∃ B' : Divisor Y, Divisor.toQDivisor B' = ((m : ℤ) • B) := by
  refine ⟨∏ E ∈ B.support, (B E).den, Finset.prod_pos fun E _ => (B E).den_pos, ?_⟩
  refine (QDivisor.mem_range_toQDivisor_iff (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B)).mpr
    fun E => ?_
  by_cases hE : E ∈ B.support
  · obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun E => (B E).den) hE
    refine ⟨t * (B E).num, ?_⟩
    change (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B) E = _
    rw [Finsupp.smul_apply, ht, zsmul_eq_mul]
    push_cast
    rw [mul_comm ((B E).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  · refine ⟨0, ?_⟩
    change (((∏ E ∈ B.support, (B E).den : ℕ) : ℤ) • B) E = _
    rw [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hE, smul_zero, Int.cast_zero]

/-- If `deg_C 𝒪_Y(A) = (M · C) + ∑ E ∈ B.support, B E · deg_C 𝒪_Y(E)` for every proper curve `C`
contracted by `f`, where `M` is an `f`-nef `ℚ`-divisor and `B` is any `ℚ`-divisor on the smooth
variety `Y`, then `A - B` is `f`-nef. -/
theorem isRelativelyNef_toQDivisor_sub_of_degreeOn_eq {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsVariety k sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme sY) (f : Y ⟶ X) (A : Divisor Y) (M : QDivisor Y)
    (hM : M.IsRelativelyNef sY f) (B : QDivisor Y)
    (hAMB : ∀ C : ProperCurve sY, C.IsContractedBy f →
      (A.degreeOn k sY C.ι C.dim_le
          (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm A) : ℚ) =
        M.intersectionNumber k sY C.ι C.dim_le hM.1 +
          ∑ E ∈ B.support, B E * (Divisor.degreeOn k sY C.ι C.dim_le
            (Finsupp.single E 1)
              (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E) : ℚ)) :
    (Divisor.toQDivisor A - B).IsRelativelyNef sY f := by
  obtain ⟨m, hm, B', hB'⟩ := exists_pos_smul_mem_range_toQDivisor B
  have hD : Divisor.toQDivisor ((m : ℤ) • A - B') = (m : ℤ) • (Divisor.toQDivisor A - B) := by
    rw [map_sub, map_zsmul, hB', smul_sub]
  have hB'E : ∀ E, (B' E : ℚ) = m * B E := fun E => by
    have := congrArg (fun D : QDivisor Y => D.coeff E) hB'
    simp only [Divisor.coeff_toQDivisor] at this
    refine this.trans ?_
    change (((m : ℤ) • B) E) = _
    rw [Finsupp.smul_apply, zsmul_eq_mul]
    push_cast
    rfl
  have hDc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm ((m : ℤ) • A - B')
  have hq : (Divisor.toQDivisor A - B).IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', _, hD, hDc⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sY hq
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le _ hq hm _ hDc hD]
  let φ : Divisor Y →+ ℤ :=
    { toFun := fun D => D.degreeOn k sY C.ι C.dim_le
        (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D)
      map_zero' := Divisor.degreeOn_zero' k sY C.ι C.dim_le
      map_add' := fun D D' => Divisor.degreeOn_add k sY C.ι C.dim_le D D' _ _ }
  have hφ : ∀ D, D.degreeOn k sY C.ι C.dim_le
      (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D) = φ D := fun _ => rfl
  have hsupp : B'.support ⊆ B.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    have := hB'E E
    rw [h0, mul_zero] at this
    exact hE (by exact_mod_cast this)
  have hB'sum : φ B' = ∑ E ∈ B.support, B' E * φ (Finsupp.single E 1) := by
    conv_lhs => rw [← Finsupp.sum_single B',
      Finsupp.sum_of_support_subset B' hsupp _ (fun _ _ => Finsupp.single_zero _)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
  have key := hAMB C hC
  have hMC := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sY hM hM.1 C hC
  rw [hφ, map_sub, map_zsmul, hB'sum, smul_eq_mul]
  simp only [hφ] at key
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  refine div_nonneg ?_ hm'.le
  push_cast
  simp only [hB'E]
  rw [key]
  have : ∑ E ∈ B.support, (m : ℚ) * B E * (φ (Finsupp.single E 1) : ℚ) =
      m * ∑ E ∈ B.support, B E * (φ (Finsupp.single E 1) : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  nlinarith

/-- **Relative Kawamata–Viehweg vanishing for a proper birational morphism.** Let `k` be
algebraically closed of characteristic zero, `f : Y ⟶ X` a proper birational morphism of
`k`-varieties with `Y` smooth, `A` a divisor on `Y`, `M` an `f`-nef `ℚ`-divisor, and `B = ∑ aᵢ Dᵢ`
an snc `ℚ`-divisor with `0 ≤ aᵢ < 1`, such that `deg_C 𝒪_Y(A) = (M · C) + ∑ aᵢ deg_C 𝒪_Y(Dᵢ)`
for every proper curve `C ⊆ Y` contracted by `f`. Then for every canonical divisor `K` of `Y`,
`R^i f_* 𝒪_Y(K + A) = 0` for all `i > 0`. -/
@[mmp "thm_mmp_km2c_proper_birational_kawamata_viehweg"]
public theorem isZero_rightDerived_pushforward_canonical_add_of_isBirationalMorphism
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY)
    (f : Y ⟶ X) [IsProper f] (hfs : f ≫ sX = sY) (hf : IsBirationalMorphism f)
    (A : Divisor Y) (M : QDivisor Y) (hM : M.IsRelativelyNef sY f)
    (B : QDivisor Y) (hB : B.IsSNC sY) (hB₀ : ∀ E, 0 ≤ B E) (hB₁ : ∀ E, B E < 1)
    (hAMB : ∀ C : ProperCurve sY, C.IsContractedBy f →
      (A.degreeOn k sY C.ι C.dim_le
          (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm A) : ℚ) =
        M.intersectionNumber k sY C.ι C.dim_le hM.1 +
          ∑ E ∈ B.support, B E * (Divisor.degreeOn k sY C.ι C.dim_le
            (Finsupp.single E 1) (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E) : ℚ))
    {n : ℕ} (K : Divisor Y) (hK : K.IsCanonicalDivisor sY n) {i : ℕ} (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj (K + A).divisorialSheaf) := by
  have hgap : Divisor.toQDivisor (K + A) - (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor A - B := by
    rw [map_add]
    abel
  obtain ⟨m, hm, B', hB'⟩ := exists_pos_smul_mem_range_toQDivisor B
  have hD : Divisor.toQDivisor ((m : ℤ) • A - B') = (m : ℤ) • (Divisor.toQDivisor A - B) := by
    rw [map_sub, map_zsmul, hB', smul_sub]
  have hnef := isRelativelyNef_toQDivisor_sub_of_degreeOn_eq sY hsm f A M hM B hAMB
  have hbig : (Divisor.toQDivisor A - B).IsRelativelyBig f :=
    ⟨m, hm, _, by rw [hD, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast],
      MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _,
      isRelativelyBig_of_isBirationalMorphism sX sY f hf fun _ =>
        MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact
   isZero_rightDerived_pushforward_divisorialSheaf_of_isProper_of_isRelativelyNef_of_isRelativelyBig
    sY sX hsm f hfs hK hB₀ hB hB₁
    (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) (hgap ▸ hnef) (hgap ▸ hbig) i hi

end MMP.Mori

end
