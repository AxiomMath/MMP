module

public import MMP.AlgebraicGeometry.Resolution.LogResolutionAmpleSubtraction
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingHighMultiplicity
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport

@[expose] public section

section

/-!
# Adapted resolutions of a smooth non-vanishing datum

Let `(X, D, G, a)` be a smooth non-vanishing datum of dimension `d ≥ 1` over an algebraically
closed field of characteristic `0` with `D` not numerically trivial. A closed point `x ∉ Supp G`
and a divisor `M = e⁻¹ M'` of multiplicity `> 2d` at `x` give an adapted resolution: a projective
log resolution `f : Y → X` of `(X, G + M)` principalising the ideal of `{x} ∪ Supp G ∪ Supp M`,
with `F_0` the prime divisor of `Y` with the valuation of the exceptional divisor of the blow-up
of `x` (for `d = 1`, the strict transform of `x`), so that `b_0 = d - 1` and `r_0 ≥ mult_x M`.

## Implementation notes

The log resolution `f` is taken on `X` itself and principalises the ideal
`I_x · I_{Supp G ∪ Supp M}`. Then `f⁻¹ I_x · 𝒪_Y` is invertible, so `f` factors through the blow-up
`B_x X` by its universal property, and `F_0` is the birational transform of the exceptional divisor
of `B_x X`. Its discrepancy is `a(E_x, X, -G) = d - 1`, because valuations agree on the biregular
locus. Principalising `I_{Supp G ∪ Supp M}` puts `f⁻¹(Supp G ∪ Supp M)` into the snc boundary even
when coefficients of `G` and `M` cancel in `G + M`. A local equation of a prime divisor `P` lies in
`𝔪_x^{mult_x P}`, and `f` maps `𝔪_x` into the maximal ideal at the generic point of `F_0`; together
these give `r_0 ≥ mult_x M`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5 Steps 2–4
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.MmpFoundationKm3aNonvanishingAdaptedResolutionExistsWithSncContainmentProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Positivity -/

section Positivity

variable {k : Type} [Field k]

/-- The image of a curve that is not contracted is a curve. -/
private theorem isProper_and_isCurve_imageι {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsSeparated sW] [LocallyOfFiniteType sW] {u : V ⟶ W}
    (hu : u ≫ sW = sV) (i : C ⟶ V)
    [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- The pull-back of a nef `ℚ`-divisor is nef. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (MMP.Mori.intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isProper_and_isCurve_imageι hu i hpt
    rw [MMP.Mori.intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- A nonnegative multiple of a nef `ℚ`-divisor is nef. -/
private theorem isNef_smul {W : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] {L : QDivisor W} (hL : L.IsNef k sW) {t : ℚ}
    (ht : 0 ≤ t) : (t • L).IsNef k sW :=
  ⟨MMP.Flips.QDivisor.IsQCartier.qsmul hL.1 t, fun C i _ _ _ hC => by
    rw [MMP.Fourfold.intersectionNumber_smul sW i hC.le L hL.1 t]
    exact mul_nonneg ht (hL.2 C i hC)⟩

/-- A positive rational multiple `N⁻¹ A` of an ample `ℚ`-divisor is ample. -/
private theorem isAmple_inv_natCast_smul {W : Scheme.{0}} [IsLocallyNoetherian W] [CompactSpace W]
    [IsNormal W] {A : QDivisor W} (hA : A.IsAmple) {N : ℕ} (hN : 0 < N) :
    ((N : ℚ)⁻¹ • A).IsAmple := by
  obtain ⟨m, hm, G, hG, hGc, hGa⟩ := hA
  refine ⟨m * N, Nat.mul_pos hm hN, G, ?_, hGc, hGa⟩
  rw [hG, smul_smul, Nat.cast_mul, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hN.ne'),
    mul_one]

/-- If `B` is nef and `B - P` is ample, then so is `B - N⁻¹ P` for every `N ≥ 1`: it is
`N⁻¹ (B - P) + (1 - N⁻¹) B`. -/
private theorem isAmple_sub_inv_natCast_smul {W : Scheme.{0}} (sW : W ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sW] [IsNormal W] [IsLocallyNoetherian W] [CompactSpace W]
    {B P : QDivisor W} (hB : B.IsNef k sW) (hBP : (B - P).IsAmple) {N : ℕ}
    (hN : 0 < N) (hQ : (B - (N : ℚ)⁻¹ • P).IsQCartier) : (B - (N : ℚ)⁻¹ • P).IsAmple := by
  have heq : (N : ℚ)⁻¹ • (B - P) + ∑ _i ∈ (Finset.univ : Finset Unit), (1 - (N : ℚ)⁻¹) • B =
      B - (N : ℚ)⁻¹ • P := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    module
  refine QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sW Finset.univ
    (fun _ : Unit => (1 - (N : ℚ)⁻¹) • B) (isAmple_inv_natCast_smul hBP hN)
    (fun _ _ => isNef_smul hB (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hN)))) ?_
  rw [heq]
  exact QDivisor.NumericallyEquivalent.refl hQ

/-- If `B` is nef and `B - ∑ p_E E` is ample, then so is `½ B - ∑ (p_E / 2N) E` for `N ≥ 1`. -/
private theorem isAmple_half_sub_sum {W : Scheme.{0}} (sW : W ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sW] [IsNormal W] [IsLocallyNoetherian W] [CompactSpace W]
    {B : QDivisor W} {T : Finset (MMP.Mori.PrimeDivisor W)} {p : MMP.Mori.PrimeDivisor W → ℚ}
    (hB : B.IsNef k sW) (hBP : (B - ∑ E ∈ T, Finsupp.single E (p E)).IsAmple) {N : ℕ}
    (hN : 0 < N) (hQ : (B - (N : ℚ)⁻¹ • ∑ E ∈ T, Finsupp.single E (p E)).IsQCartier) :
    ((1 / 2 : ℚ) • B - ∑ E ∈ T, Finsupp.single E (p E / (2 * N))).IsAmple := by
  convert isAmple_inv_natCast_smul (isAmple_sub_inv_natCast_smul sW hB hBP hN hQ) (N := 2)
    two_pos using 1
  rw [smul_sub, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun E _ => ?_
    rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
    congr 1
    push_cast
    field_simp

end Positivity

/-! ### Ideal sheaves -/

section Ideals

/-- The stalk of `𝒪_Y(-A) = ∏ I_E^{a_E}` at the generic point of a prime divisor `D` is
`𝔪^{a_D}`. -/
private theorem stalk_divisorIdeal_genericPoint {Y : Scheme.{0}}
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ)
    (hfin : (Function.support A).Finite) (D : AlgebraicGeometry.PrimeDivisor Y) :
    IdealSheafData.stalk (MMP.Resolution.divisorIdeal A) D.genericPoint =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk D.genericPoint) ^ A D := by
  classical
  unfold MMP.Resolution.divisorIdeal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) fun D' hD' => by
      simpa using fun h0 => hD' (by simp [h0]), MMP.Resolution.Aux.stalk_prod,
    Finset.prod_eq_single D (fun b _ hb => ?_) (fun hD => ?_), MMP.Resolution.Aux.stalk_pow,
    MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
  · rw [MMP.Resolution.Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2,
      Ideal.top_pow, Ideal.one_eq_top]
    intro hmem
    exact hb (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem)
  · have : A D = 0 := by simpa using hD
    rw [this, pow_zero, show (1 : Y.IdealSheafData) = ⊤ from rfl, MMP.Resolution.Aux.stalk_top,
      Ideal.one_eq_top]

/-- A prime divisor whose generic point lies in the zero locus of `𝒪_Y(-A)` has `a_E ≠ 0`. -/
private theorem ne_zero_of_genericPoint_mem_support_divisorIdeal {Y : Scheme.{0}}
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ)
    (hfin : (Function.support A).Finite) (E : AlgebraicGeometry.PrimeDivisor Y)
    (hE : E.genericPoint ∈ (MMP.Resolution.divisorIdeal A).support) : A E ≠ 0 := by
  intro h0
  have h := stalk_divisorIdeal_genericPoint A hfin E
  rw [h0, pow_zero, Ideal.one_eq_top] at h
  exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 h hE

/-- The ideal sheaf `𝒪_Y(-A)` of an effective divisor on a smooth scheme is invertible. -/
private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    (A : AlgebraicGeometry.PrimeDivisor Y → ℕ) (hA : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (MMP.Resolution.divisorIdeal A) := by
  classical
  have hM : MMP.Resolution.divisorIdeal A = ∏ D ∈ hA.toFinset, D.idealSheaf ^ A D := by
    unfold MMP.Resolution.divisorIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by
      change D.idealSheaf ^ A D = 1
      rw [h0, pow_zero])
  rw [hM]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf sY hY D

end Ideals

/-! ### Pull-backs of effective divisors on a smooth variety -/

section Pullback

open MMP.Resolution

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The coefficient along `E` of the pull-back of a prime divisor `P` with invertible ideal is
`≥ 0`, vanishes unless `f(η_E) ∈ P`, and is at least `mult_{f(η_E)} P`. -/
private theorem coeff_isPullback_single {f : Y ⟶ X} (P : MMP.Mori.PrimeDivisor X)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)}
    {B' : Divisor Y} (h : Divisor.IsPullback f (Finsupp.single P 1 : Divisor X) hB B')
    (E : MMP.Mori.PrimeDivisor Y) :
    0 ≤ B'.coeff E ∧ (f E.genericPoint ∉ P.support → B'.coeff E = 0) ∧
      ((P.multiplicityAt (f E.genericPoint)).toNat : ℤ) ≤ B'.coeff E := by
  obtain ⟨m, hm, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P hP h E
  rw [hc]
  refine ⟨by positivity, fun hnot => ?_, ?_⟩
  · rw [IdealSheafData.stalk_comap,
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hnot, Ideal.map_top,
      MMP.Threefold.Resolution.idealOrder_top] at hm
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) hm.symm : m = 0)
  · have hle : P.multiplicityAt (f E.genericPoint) ≤ (m : ℕ∞) := by
      rw [← hm]
      refine iSup₂_le fun j hj => ?_
      refine le_iSup₂_of_le (f := fun (i : ℕ) (_ : IdealSheafData.stalk (P.idealSheaf.comap f)
        E.genericPoint ≤ IsLocalRing.maximalIdeal _ ^ i) => (i : ℕ∞)) j ?_ le_rfl
      rw [IdealSheafData.stalk_comap]
      rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk] at hj
      refine (Ideal.map_mono hj).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ j
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    exact_mod_cast ENat.toNat_le_of_le_coe hle

variable [CompactSpace Y] [IrreducibleSpace Y]

/-- The pull-back of `∑_{P ∈ T} c_P P` is `∑_{P ∈ T} c_P f^*P`. -/
private theorem isPullback_sum_smul_single (hX : ∀ P : MMP.Mori.PrimeDivisor X,
      Divisor.IsCartier (Finsupp.single P 1 : Divisor X))
    (f : Y ⟶ X) [IsDominant f]
    (T : Finset (MMP.Mori.PrimeDivisor X)) (c : MMP.Mori.PrimeDivisor X → ℤ) :
    Divisor.IsPullback f (∑ P ∈ T, c P • (Finsupp.single P 1 : Divisor X))
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)
      (∑ P ∈ T, c P • Divisor.pullback (Finsupp.single P 1 : Divisor X) (hX P)
        (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Divisor.isPullback_zero _
  | insert P T hPT ih =>
    rw [Finset.sum_insert hPT, Finset.sum_insert hPT]
    refine Divisor.IsPullback.add ((hX P).zsmul _) ?_
      (hB₁ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _) _
      ((Divisor.isPullback_pullback (hX P) _).zsmul (hX P) (c P)
        (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)) ih
    exact Finset.sum_induction _ Divisor.IsCartier (fun _ _ h₁ h₂ => h₁.add h₂)
      (Divisor.isCartier_zero) fun Q _ => (hX Q).zsmul _

/-- **Pull-backs of effective divisors on a smooth variety.** If `M'` is an effective divisor on
`X` all of whose prime divisors have invertible ideal sheaves, and `B' = f^*M'`, then the
coefficients of `B'` are `≥ 0`, vanish along prime divisors not lying over `Supp M'`, and are at
least `mult_{f(η_E)} M'` along `E`. -/
private theorem coeff_isPullback_of_isEffective
    (hX : ∀ P : MMP.Mori.PrimeDivisor X, Divisor.IsCartier (Finsupp.single P 1 : Divisor X))
    (hXe : ∀ P : MMP.Mori.PrimeDivisor X,
      Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    (f : Y ⟶ X) [IsDominant f] {M' : Divisor X} (hM' : M'.IsEffective)
    (hMc : M'.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M'.supp}
    {B' : Divisor Y} (h : M'.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor Y) :
    0 ≤ B'.coeff E ∧ (B'.coeff E ≠ 0 → f E.genericPoint ∈ (M'.supp : Set X)) ∧
      M'.multiplicityAt (f E.genericPoint) ≤ B'.coeff E := by
  classical
  have hM'eq : M' = ∑ P ∈ M'.support, M' P • (Finsupp.single P 1 : Divisor X) := by
    conv_lhs => rw [← Finsupp.sum_single M']
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have hsum := isPullback_sum_smul_single hX f M'.support M'
  have hB'eq := h.eq hMc (hsum.of_eq hM'eq.symm)
  set pb : MMP.Mori.PrimeDivisor X → Divisor Y := fun P =>
    Divisor.pullback (Finsupp.single P 1 : Divisor X) (hX P)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)
  have hcoef : B'.coeff E = ∑ P ∈ M'.support, M' P * (pb P).coeff E := by
    rw [hB'eq, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, DivisorWithCoeffs.coeff_apply]
  have hpbP := fun P => coeff_isPullback_single P (hXe P)
    (Divisor.isPullback_pullback (hX P)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _)) E
  refine ⟨?_, fun hne => ?_, ?_⟩
  · rw [hcoef]
    exact Finset.sum_nonneg fun P _ => mul_nonneg (hM' P) (hpbP P).1
  · rw [hcoef] at hne
    obtain ⟨P, hP, hPne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hpb0 : (pb P).coeff E ≠ 0 := fun h0 => hPne (by rw [h0, mul_zero])
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, Finsupp.mem_support_iff.mp hP,
      Classical.byContradiction fun hn => hpb0 ((hpbP P).2.1 hn)⟩
  · rw [hcoef, DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
    refine Finset.sum_le_sum fun P _ => ?_
    rw [nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hpbP P).2.2 (hM' P)

end Pullback

/-! ### Birational geometry -/

section Birational

variable {k : Type} [Field k]

/-- A proper birational morphism `g : Y ⟶ X` of varieties with `X` normal: every prime divisor `P`
of `X` is the image of a prime divisor `P'` of `Y` whose generic point maps into the biregular
locus of `g`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X) (hX : IsNormalVariety k sX)
    (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor Y, g P'.genericPoint = P.genericPoint ∧
      g P'.genericPoint ∈ biregularLocus g := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  obtain ⟨V, hV2, hVi⟩ := exists_isIso_morphismRestrict_two_le_closedsCodimension k sX (g ≫ sX)
    hX hY g rfl hg
  have hP : P.genericPoint ∈ biregularLocus g := by
    refine le_biregularLocus hVi ?_
    by_contra hP
    have hsub : ((TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint :
        TopologicalSpace.IrreducibleCloseds X) : Set X) ⊆ (V.compl : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr hP) V.compl.isClosed
    have h4 := le_closedsCodimension_iff.mp hV2 _ hsub
    rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
        P.genericPoint = (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h4
    exact absurd h4 (by decide)
  have := hg.isDominant
  obtain ⟨y, hy⟩ := g.surjective P.genericPoint
  have hco : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hy ▸ hP), hy]
    exact P.coheight_genericPoint
  set P' : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco
  have hgen : P'.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hco
  refine ⟨P', ?_⟩
  rw [hgen, hy]
  exact ⟨rfl, hP⟩

/-- Two divisors over `X` related by a morphism of models over `X` that is biregular near the
generic point of the target divisor and maps generic point to generic point have the same
valuation. -/
private theorem valuation_eq_of_comp {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (D D' : DivisorOver k sX) (g : D.Y ⟶ D'.Y) (hg : g ≫ D'.f = D.f)
    (hη : g D.E.genericPoint = D'.E.genericPoint)
    (hmem : D'.E.genericPoint ∈ biregularLocus g) : D.valuation = D'.valuation := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hU : D.E.genericPoint ∈ g ⁻¹ᵁ biregularLocus g := by
    change g D.E.genericPoint ∈ biregularLocus g
    rwa [hη]
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' (g ⁻¹ᵁ biregularLocus g)
    (biregularLocus g) hU hmem (asIso (g ∣_ biregularLocus g)) ?_ ?_
  · rw [asIso_hom, ← Category.assoc, morphismRestrict_ι, Category.assoc, hg]
  · exact Subtype.ext ((morphismRestrict_base_coe g (biregularLocus g) ⟨_, hU⟩).trans hη)

/-- A morphism `g` between irreducible schemes, with `g ≫ π` surjective, such that `g ≫ π` and `π`
are both isomorphisms over a nonempty open `W`, is birational. -/
private theorem isBirationalMorphism_of_isIso_comp {X Y Z : Scheme.{0}} [IrreducibleSpace Y]
    [IrreducibleSpace Z] (g : Y ⟶ Z) (π : Z ⟶ X) [Surjective (g ≫ π)] (W : X.Opens)
    (hW : (W : Set X).Nonempty) (hf : IsIso ((g ≫ π) ∣_ W)) (hπ : IsIso (π ∣_ W)) :
    IsBirationalMorphism g := by
  have hle : (g ≫ π) ⁻¹ᵁ W ≤ g ⁻¹ᵁ (π ⁻¹ᵁ W) := le_rfl
  obtain ⟨w, hw⟩ := hW
  obtain ⟨y, hy⟩ := (g ≫ π).surjective w
  have hyU : y ∈ (g ≫ π) ⁻¹ᵁ W := by
    change (g ≫ π) y ∈ W
    rwa [hy]
  have hcomp : g.resLE (π ⁻¹ᵁ W) ((g ≫ π) ⁻¹ᵁ W) hle ≫ (π ∣_ W) = (g ≫ π) ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have : IsIso (g.resLE (π ⁻¹ᵁ W) ((g ≫ π) ⁻¹ᵁ W) hle) := by
    have : IsIso (g.resLE (π ⁻¹ᵁ W) ((g ≫ π) ⁻¹ᵁ W) hle ≫ (π ∣_ W)) := by
      rwa [hcomp]
    exact IsIso.of_isIso_comp_right _ (π ∣_ W)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _ ⟨y, hyU⟩ ⟨g y, hle hyU⟩ hle this

end Birational

/-! ### Crepant boundaries -/

section Crepant

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic
point of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem eq_neg_coeff_of_map_genericPoint_eq [PerfectField k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : MMP.Mori.DivisorOver k sX} {P : MMP.Mori.PrimeDivisor X}
    (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

/-- Along a prime divisor `E` of `Y` lying over the generic point of a prime divisor `P` of `X`,
the crepant boundary of `(X, Δ)` on `Y` has the coefficient `coeff_P(Δ)`. -/
private theorem coeff_eq_of_isCrepantBoundary [PerfectField k] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
    {hY : MMP.Mori.IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f} {ΔY : QDivisor Y}
    (hΔ : MMP.Mori.IsCrepantBoundary sX n K Δ f hY hf ΔY) {E : MMP.Mori.PrimeDivisor Y}
    {P : MMP.Mori.PrimeDivisor X} (hP : f E.genericPoint = P.genericPoint) :
    ΔY.coeff E = Δ.coeff P :=
  neg_inj.mp (eq_neg_coeff_of_map_genericPoint_eq hX (D := ⟨Y, f, hY, hf, E⟩) hP (hΔ E))

/-- **The support of the crepant boundary.** For a birational morphism `f : Y ⟶ X` from a normal
variety, every prime divisor in the support of the crepant boundary `Δ_Y` is `f`-exceptional or
lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support [IsAlgClosed k]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
    (hP : IsPairWith sX n K Δ) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    {G : MMP.Mori.PrimeDivisor Y} (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨ f G.genericPoint ∈ (Δ.supp : Set X) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hGe
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hc' : ΔY.coeff G = Δ.coeff P := neg_injective ((hΔY G).eq hd)
    refine Or.inr ?_
    rw [hη, DivisorWithCoeffs.coe_supp]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc',
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-! ### Closed points -/

section ClosedPoint

variable {k : Type} [Field k] {X : Scheme.{0}} [IrreducibleSpace X]

/-- A closed point of a variety of dimension `n` has codimension `n`. -/
private theorem coheight_eq_of_isClosed (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {n : ℕ}
    (hdim : topologicalKrullDim X = n) {x : X} (hx : IsClosed ({x} : Set X)) :
    Order.coheight x = n := by
  have h : ringKrullDim (X.presheaf.stalk x) = (n : ℕ) := by
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX x hx,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x, hdim]
  rw [ringKrullDim_stalk_eq_coheight] at h
  have h2 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := h
  exact WithBot.coe_injective h2

/-- A closed point of a variety of positive dimension is not the generic point. -/
private theorem ne_genericPoint_of_isClosed (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    {n : ℕ} (hn : 1 ≤ n) (hdim : topologicalKrullDim X = n) {x : X} (hx : IsClosed ({x} : Set X)) :
    x ≠ genericPoint X := by
  intro hxη
  have h1 := coheight_eq_of_isClosed sX hdim hx
  have h0 : Order.coheight x = 0 := by
    refine Order.coheight_eq_zero.mpr fun b _ => ?_
    rw [hxη, Scheme.le_iff_specializes]
    exact (genericPoint_spec X).specializes trivial
  rw [h0] at h1
  exact absurd (by exact_mod_cast h1.symm : n = 0) (by omega)

end ClosedPoint

/-! ### The prime divisor `F_0` -/

section FirstComponent

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- **`F_0` for a curve.** If `X` is a normal curve and `x ∉ Supp G` a closed point, the
crepant boundary of `(X, -G)` on `Y` vanishes along the prime divisor of `Y` over `x`. -/
private theorem exists_coeff_eq_zero_of_topologicalKrullDim_eq_one (hX : IsNormalVariety k sX)
    [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {G : QDivisor X}
    (hdim : topologicalKrullDim X = 1) {x : X} (hx : IsClosed ({x} : Set X))
    (hxG : x ∉ (G.supp : Set X)) (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K (-G) f hY hf ΔY) :
    ∃ F₀ : MMP.Mori.PrimeDivisor Y, f F₀.genericPoint = x ∧ ΔY.coeff F₀ = 0 := by
  have hco : Order.coheight x = 1 := by
    exact_mod_cast coheight_eq_of_isClosed sX (n := 1) (by exact_mod_cast hdim) hx
  set Px : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hPx : Px.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  obtain ⟨F₀, hF₀, -⟩ := exists_primeDivisor_map_genericPoint_eq sX f hX hY.1 hf Px
  refine ⟨F₀, hF₀.trans hPx, ?_⟩
  rw [coeff_eq_of_isCrepantBoundary hX hΔY hF₀, DivisorWithCoeffs.coeff_neg, neg_eq_zero]
  by_contra hc
  exact hxG (DivisorWithCoeffs.mem_supp_iff.mpr
    ⟨Px, hc, hPx ▸ MMP.Flips.primeDivisor_genericPoint_mem_support Px⟩)

/-- The support of `I_x · I_{Supp G ∪ Supp M}` is `{x} ∪ Supp G ∪ Supp M`. -/
private theorem mem_support_vanishingIdeal_mul_iff {x : X} (hx : IsClosed ({x} : Set X))
    (G M : QDivisor X) (y : X) :
    y ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ *
      Scheme.IdealSheafData.vanishingIdeal (G.supp ⊔ M.supp)).support : Set X) ↔
      y = x ∨ y ∈ (G.supp : Set X) ∨ y ∈ (M.supp : Set X) := by
  rw [Scheme.IdealSheafData.support_mul]
  change y ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).support : Set X) ∨
    y ∈ ((Scheme.IdealSheafData.vanishingIdeal (G.supp ⊔ M.supp)).support : Set X) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp

/-- On a variety of positive dimension, `I_x · I_{Supp G ∪ Supp M}` is nonzero. -/
private theorem vanishingIdeal_mul_ne_bot (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    {n : ℕ} (hn : 1 ≤ n) (hdim : topologicalKrullDim X = n) {x : X}
    (hx : IsClosed ({x} : Set X)) (G M : QDivisor X) :
    Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ *
      Scheme.IdealSheafData.vanishingIdeal (G.supp ⊔ M.supp) ≠ ⊥ := by
  intro hbot
  have hη : genericPoint X ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ *
      Scheme.IdealSheafData.vanishingIdeal (G.supp ⊔ M.supp)).support : Set X) := by
    rw [hbot, Scheme.IdealSheafData.support_bot]
    trivial
  rcases (mem_support_vanishingIdeal_mul_iff hx G M _).mp hη with h1 | h1 | h1
  · exact ne_genericPoint_of_isClosed sX hn hdim hx h1.symm
  · exact MMP.Fourfold.genericPoint_notMem_supp G h1
  · exact MMP.Fourfold.genericPoint_notMem_supp M h1

/-- A `ℚ`-divisor whose support misses `x` has multiplicity `0` along `{x}`. -/
private theorem sum_neg_coeff_mul_multiplicityAlong_eq_zero {G : QDivisor X} {x : X}
    (hxG : x ∉ (G.supp : Set X)) (Z : TopologicalSpace.IrreducibleCloseds X)
    (hZ : Z.isIrreducible.genericPoint = x) :
    ((-G).sum fun Γ a => a * ((Γ.multiplicityAlong Z).toNat : ℚ)) = 0 := by
  refine Finset.sum_eq_zero fun Γ hΓ => ?_
  have hxΓ : x ∉ Γ.support := by
    intro hm
    refine hxG (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, ?_, hm⟩)
    have := Finsupp.mem_support_iff.mp hΓ
    rw [DivisorWithCoeffs.coeff_apply]
    intro h0
    exact this (by rw [Finsupp.neg_apply, h0, neg_zero])
  have key : ∀ z : X, z = x → (⨆ (s : ℕ) (_ : Γ.idealSheaf.stalkIdeal z ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ s), (s : ℕ∞)) = Γ.multiplicityAt x := by
    rintro z rfl
    rfl
  have hm : Γ.multiplicityAlong Z = 0 := by
    rw [MMP.Mori.PrimeDivisor.multiplicityAlong, key _ hZ, Γ.multiplicityAt_eq_zero_of_notMem hxΓ]
  simp [hm]

/-- **`F_0` in dimension `≥ 2`.** Let `X` be a smooth variety of dimension `n ≥ 2`, `x ∉ Supp G`
a closed point and `f : Y ⟶ X` a proper birational morphism from a normal variety such that
`f⁻¹ I_x · 𝒪_Y` is invertible. Then `f` factors through the blow-up `B_x X`, and the birational
transform `F_0` of its exceptional divisor lies over `x` with discrepancy `a(F_0, X, -G) = n - 1`.
-/
private theorem exists_neg_coeff_eq_of_two_le [Smooth sX] {n : ℕ} {K : Divisor X}
    {G : QDivisor X} (hP : IsPairWith sX n K (-G)) (hdim : topologicalKrullDim X = n)
    (h2 : 2 ≤ n) {x : X} (hx : IsClosed ({x} : Set X)) (hxG : x ∉ (G.supp : Set X))
    (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap f))
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K (-G) f hY hf ΔY) :
    ∃ F₀ : MMP.Mori.PrimeDivisor Y, f F₀.genericPoint = x ∧ -ΔY.coeff F₀ = (n : ℚ) - 1 := by
  classical
  set Ix : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  obtain ⟨hBv, hBsm, hπproj, hπbir, hπiso, -, E, hEI, -, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_vanishingIdeal_singleton sX hP.1.1 hdim
      h2 hx
  set π := blowUpToBase Ix
  have : LocallyOfFiniteType (π ≫ sX) := hBv.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp Ix) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : IsNormal (blowUp Ix) := isNormal_of_smooth_over_field (π ≫ sX)
  have : IsIntegral (blowUp Ix) := hBv.toIsIntegral
  have hBn : IsNormalVariety k (π ≫ sX) := ⟨hBv, inferInstance⟩
  set f' : Y ⟶ blowUp Ix := blowUpLift Ix f hcart
  have hf' : f' ≫ π = f := blowUpLift_comp Ix f hcart
  have : IsProper π := hπproj.isProper
  have : IsProper f' := by
    have : IsProper (f' ≫ π) := hf' ▸ inferInstance
    exact IsProper.of_comp f' π
  have hY' : MMP.Mori.IsVariety k (f' ≫ π ≫ sX) := by
    rw [← Category.assoc, hf']
    exact hY.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  -- `f'` is birational
  have hf'bir : IsBirationalMorphism f' := by
    obtain ⟨V, hV2, hVi⟩ := exists_isIso_morphismRestrict_two_le_closedsCodimension k sX (f ≫ sX)
      hP.1 hY.1 f rfl hf
    set W : X.Opens := V ⊓ ⟨{x}ᶜ, hx.isOpen_compl⟩
    have hηV : genericPoint X ∈ V := by
      obtain ⟨v, hv⟩ := MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V.compl hV2
      exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨v, trivial, by simpa using hv⟩
    have hηx : genericPoint X ∈ (⟨{x}ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
      fun h => ne_genericPoint_of_isClosed sX (by omega) hdim hx h.symm
    have : Surjective (f' ≫ π) := hf' ▸ inferInstance
    refine isBirationalMorphism_of_isIso_comp f' π W ⟨_, hηV, hηx⟩ ?_ ?_
    · rw [hf']
      exact isBiregular_iff_le_biregularLocus.mpr (inf_le_left.trans (le_biregularLocus hVi))
    · exact isBiregular_iff_le_biregularLocus.mpr (inf_le_right.trans (le_biregularLocus hπiso))
  -- the birational transform of the exceptional divisor
  obtain ⟨F₀, hF₀, hF₀V⟩ := exists_primeDivisor_map_genericPoint_eq (π ≫ sX) f' hBn hY' hf'bir E
  have hEx : π E.genericPoint = x :=
    (MMP.Threefold.Resolution.mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hx hEI _).mp
      (MMP.Flips.primeDivisor_genericPoint_mem_support E)
  have hfx : f F₀.genericPoint = x := by
    rw [← hf', Scheme.Hom.comp_apply, hF₀, hEx]
  refine ⟨F₀, hfx, ?_⟩
  -- the discrepancies
  let DY : DivisorOver k sX := ⟨Y, f, hY, hf, F₀⟩
  let DB : DivisorOver k sX := ⟨blowUp Ix, π, hBn, hπbir, E⟩
  have hv : DY.valuation = DB.valuation :=
    valuation_eq_of_comp DY DB f' hf' hF₀ (hF₀ ▸ hF₀V)
  let Z : TopologicalSpace.IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  have hZgen : Z.isIrreducible.genericPoint = x :=
    Z.isIrreducible.isGenericPoint_genericPoint_closure.eq isGenericPoint_closure
  have hc : ((n : ℕ) : ℕ∞) = codimension Z := by
    rw [codimension_eq_coheight, show Z = (irreducibleSetEquivPoints (α := X)).symm x from
      TopologicalSpace.IrreducibleCloseds.ext
        (by simp [Z, irreducibleSetEquivPoints, hx.closure_eq]),
      Order.coheight_orderIso, coheight_eq_of_isClosed sX hdim hx]
  have hj : (Stacks.Blowup.blowUpIso Ix).inv ≫ Stacks.Blowup.blowUpToBase Ix = DB.f := by
    rw [← Stacks.Blowup.blowUpIso_hom_comp, Iso.inv_hom_id_assoc]
  obtain ⟨-, hdB⟩ := MMP.Mori.isDiscrepancy_blowUp sX hP.1.1 hP.2.1 (-G) Z hc h2 DB
    (Stacks.Blowup.blowUpIso Ix).inv hj (by rwa [hZgen])
  rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hv (hΔY F₀) hdB,
    sum_neg_coeff_mul_multiplicityAlong_eq_zero hxG Z hZgen, sub_zero]

/-- **`F_0`.** Let `X` be a smooth variety of dimension `n ≥ 1`, `x ∉ Supp G` a closed point and
`f : Y ⟶ X` a proper birational morphism from a normal variety such that `f⁻¹ I_x · 𝒪_Y` is
invertible. Some prime divisor `F_0` of `Y` lies over `x` with `a(F_0, X, -G) ≤ n - 1`. -/
private theorem exists_neg_coeff_le [LocallyOfFiniteType sX] (hsm : IsSmoothScheme sX) {n : ℕ}
    {K : Divisor X} {G : QDivisor X} (hP : IsPairWith sX n K (-G))
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) {x : X} (hx : IsClosed ({x} : Set X))
    (hxG : x ∉ (G.supp : Set X)) (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap f))
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K (-G) f hY hf ΔY) :
    ∃ F₀ : MMP.Mori.PrimeDivisor Y, f F₀.genericPoint = x ∧ -ΔY.coeff F₀ ≤ (n : ℚ) - 1 := by
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · obtain ⟨F₀, h1, h2⟩ := exists_coeff_eq_zero_of_topologicalKrullDim_eq_one hP.1
      (by exact_mod_cast hdim) hx hxG f hY hf hΔY
    exact ⟨F₀, h1, by simp [h2]⟩
  · have : Smooth sX := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sX hsm
    obtain ⟨F₀, h1, h2⟩ := exists_neg_coeff_eq_of_two_le hP hdim h2 hx hxG f hY hf hcart hΔY
    exact ⟨F₀, h1, h2.le⟩

end FirstComponent

/-! ### Enumerations and coefficients -/

section Enumeration

/-- A finset `T` containing `a` is enumerated by `Fin (s + 1)` with `a` first. -/
private theorem exists_fin_enum_eq_of_mem {α : Type*} {T : Finset α} {a : α} (ha : a ∈ T) :
    ∃ (s : ℕ) (F : Fin (s + 1) → α), Function.Injective F ∧ F 0 = a ∧ (∀ j, F j ∈ T) ∧
      (∀ y ∈ T, ∃ j, F j = y) ∧
      ∀ {R : Type} [AddCommMonoid R] (g : α → R), ∑ j, g (F j) = ∑ y ∈ T, g y := by
  obtain ⟨s, hs⟩ : ∃ s, T.card = s + 1 :=
    ⟨T.card - 1, by have := Finset.card_pos.mpr ⟨a, ha⟩; omega⟩
  let ι : T ≃ Fin (s + 1) := T.equivFin.trans (finCongr hs)
  let τ : T ≃ Fin (s + 1) := ι.trans (Equiv.swap (ι ⟨a, ha⟩) 0)
  refine ⟨s, fun j => τ.symm j, Subtype.val_injective.comp τ.symm.injective, ?_,
    fun j => (τ.symm j).2, fun y hy => ⟨τ ⟨y, hy⟩, by simp⟩, fun g => ?_⟩
  · simp only [τ, Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_right,
      Equiv.symm_apply_apply]
  · rw [← Finset.sum_coe_sort T]
    exact τ.symm.sum_comp fun y : T => g y

/-- A finitely supported function supported in `T` is the sum of its terms over `T`. -/
private theorem sum_single_eq_of_support_subset {α R : Type*} [AddCommMonoid R] {T : Finset α}
    (g : α →₀ R) (hg : g.support ⊆ T) : ∑ y ∈ T, Finsupp.single y (g y) = g :=
  (Finsupp.sum_of_support_subset g hg _ (by simp)).symm.trans g.sum_single

/-- Finitely many positive `p_j` and `c_j` admit `N ≥ 1` with `p_j / (2N) < c_j`. -/
private theorem exists_nat_div_two_mul_lt {ι : Type*} [Fintype ι] (p c : ι → ℚ)
    (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) : ∃ N : ℕ, 0 < N ∧ ∀ j, p j / (2 * N) < c j := by
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ j, p j / c j)
  have h0 : ∀ j ∈ Finset.univ, 0 ≤ p j / c j := fun j _ => (div_pos (hp j) (hc j)).le
  have hN0 : (0 : ℚ) < N := (Finset.sum_nonneg h0).trans_lt hN
  refine ⟨N, by exact_mod_cast hN0, fun j => ?_⟩
  have := (div_lt_iff₀ (hc j)).mp ((Finset.single_le_sum h0 (Finset.mem_univ j)).trans_lt hN)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hc j]

end Enumeration

/-- The multiplicity at a point is `ℚ`-linear. -/
private theorem multiplicityAt_smul {X : Scheme.{0}} (c : ℚ) (B : QDivisor X) (x : X) :
    (c • B).multiplicityAt x = c * B.multiplicityAt x := by
  induction B using Finsupp.induction_linear with
  | zero => simp [DivisorWithCoeffs.multiplicityAt]
  | add B₁ B₂ h₁ h₂ =>
    rw [smul_add, DivisorWithCoeffs.multiplicityAt_add, DivisorWithCoeffs.multiplicityAt_add, h₁,
      h₂, mul_add]
  | single P q =>
    rw [Finsupp.smul_single, DivisorWithCoeffs.multiplicityAt_single,
      DivisorWithCoeffs.multiplicityAt_single, smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    ring

/-- A variety has a closed point outside the support of any `ℚ`-divisor. -/
private theorem exists_isClosed_notMem_supp {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (G : QDivisor X) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ x ∉ (G.supp : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints
    (Z := ((G.supp : Set X))ᶜ) ⟨genericPoint X, MMP.Fourfold.genericPoint_notMem_supp G⟩
    G.supp.isClosed.isOpen_compl.isLocallyClosed
  exact ⟨x, hxc, hxU⟩

/-- The core construction: from the divisor `M'` of high multiplicity, an adapted resolution. -/
private theorem exists_isNonvanishingAdaptedResolution_of_multiplicityAt_gt
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsSmoothNonvanishingDatum sX n K D G a) (hn : 1 ≤ n)
    {x : X} (hx : IsClosed ({x} : Set X)) (hxG : x ∉ (G.supp : Set X)) {q e : ℤ}
    {G' M' : Divisor X} (hq : a ≤ q) (he : 1 ≤ e) (hG' : Divisor.toQDivisor G' = e • G)
    (hM' : M'.IsEffective) (hlin : M'.LinearlyEquivalent ((e * q) • D + G' - e • K))
    (hmult : 2 * n * e < M'.multiplicityAt x) :
    ∃ (Y : Scheme.{0}) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (_ : CompactSpace Y) (f : Y ⟶ X) (s : ℕ)
      (F : Fin (s + 1) → MMP.Mori.PrimeDivisor Y) (b p r : Fin (s + 1) → ℚ),
      IsNonvanishingAdaptedResolution sX n K D G a x q e
        ((e : ℚ)⁻¹ • Divisor.toQDivisor M') f F b p r := by
  classical
  set M : QDivisor X := ((e : ℚ)⁻¹) • Divisor.toQDivisor M' with hMdef
  have : MMP.Mori.IsProjectiveVariety k sX := h.isProjectiveVariety
  have : MMP.Mori.IsProperVariety k sX := h.isProperVariety
  have hX : IsNormalVariety k sX := h.isKltPair.1.1
  have hsm : IsSmoothScheme sX := h.isSmoothScheme
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim X = n := h.isKltPair.1.2.1.topologicalKrullDim_eq
  have he0 : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  -- (i): the divisor `M = e⁻¹ M'`
  have hMe : Divisor.toQDivisor M' = e • M := by
    rw [hMdef, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_inv_cancel₀ he0.ne', one_smul]
  have hMeff : M.IsEffective := fun E => by
    rw [hMdef, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr he0.le) (by exact_mod_cast hM' E)
  have hmultEq : M.multiplicityAt x = (M'.multiplicityAt x : ℚ) / e := by
    rw [hMdef, multiplicityAt_smul, MMP.Threefold.Resolution.multiplicityAt_toQDivisor,
      inv_mul_eq_div]
  have hmultM : (2 * n : ℚ) < M.multiplicityAt x := by
    rw [hmultEq, lt_div_iff₀ he0]
    exact_mod_cast hmult
  -- the ideal of `{x} ∪ Supp G ∪ Supp M`
  set Ix : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  set J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (G.supp ⊔ M.supp)
  have hI : Ix * J ≠ ⊥ := vanishingIdeal_mul_ne_bot sX hn hdim hx G M
  -- the resolution
  set A : QDivisor X := a • Divisor.toQDivisor D + G - Divisor.toQDivisor K with hA
  obtain ⟨hAnef, hAbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sX h.isAmple
  obtain ⟨Y, f, hLR, hproj, hYln, hYn, hYc, DI, hDI0, -, hIDI, Fs, hsnc, hsub, hBsupp, fB, p,
    hfB, hp, hAmp⟩ :=
    exists_isLogResolution_isAmple_pullback_sub_sum sX (G + M) (Ix * J) hI A hAnef hAbig
  have hfres : IsSmoothResolution sX f := hLR.toIsSmoothResolution
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsProper f := hfres.isProper
  have hfbir : IsBirationalMorphism f := hfres.isBirationalMorphism
  have : IsDominant f := hfbir.isDominant
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hsmY : IsSmoothScheme (f ≫ sX) := hfres.isSmoothScheme
  have hmemF : ∀ E : MMP.Mori.PrimeDivisor Y,
      E.genericPoint ∈ ⋃ E' ∈ Fs, (E'.support : Set Y) → E ∈ Fs := fun E hE => by
    obtain ⟨E', hE', hgen⟩ := Set.mem_iUnion₂.mp hE
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE'
  set DI' : AlgebraicGeometry.PrimeDivisor Y → ℕ := fun E => (DI E).toNat
  have hDIfin : (Function.support DI').Finite := DI.support.finite_toSet.subset fun E hE => by
    simp only [Function.mem_support, DI', ne_eq] at hE
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun h0 => hE (by simp [h0])
  -- every prime divisor over `{x} ∪ Supp G ∪ Supp M` is one of the `F_j`
  have hcov : ∀ E : MMP.Mori.PrimeDivisor Y, (f E.genericPoint = x ∨
      f E.genericPoint ∈ (G.supp : Set X) ∨ f E.genericPoint ∈ (M.supp : Set X)) → E ∈ Fs := by
    intro E hE
    have h1 : E.genericPoint ∈ (((Ix * J).comap f).support : Set Y) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact (mem_support_vanishingIdeal_mul_iff hx G M _).mpr hE
    rw [hIDI] at h1
    have h2 := ne_zero_of_genericPoint_mem_support_divisorIdeal DI' hDIfin E h1
    have h3 : DI E ≠ 0 := fun h0 => h2 (by simp [DI', h0])
    exact hmemF E (hsub (Or.inr (DivisorWithCoeffs.mem_supp_iff.mpr
      ⟨E, h3, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩)))
  have hcartIx : Stacks.Divisors.IsEffectiveCartierDivisor (Ix.comap f) := by
    have h1 := isEffectiveCartierDivisor_divisorIdeal (f ≫ sX) hsmY DI' hDIfin
    rw [← hIDI, AlgebraicGeometry.comap_mul] at h1
    exact isEffectiveCartierDivisor_left_of_mul _ _ h1
  -- the crepant boundary and the prime divisor `F_0`
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary h.isKltPair.1.isPair
    h.isKltPair.1.2.1 f hY hfbir
  obtain ⟨F₀, hF₀x, hF₀b⟩ := exists_neg_coeff_le hsm h.isKltPair.1 hdim hn
    hx hxG f hY hfbir hcartIx hΔY
  -- numbering the components with `F_0` first
  obtain ⟨s, F, hFinj, hF0, hFmem, hFsurj, hsumF⟩ :=
    exists_fin_enum_eq_of_mem (hcov F₀ (Or.inl hF₀x))
  -- (iv): the coefficients `b_j`
  have hΔYsupp : ΔY.support ⊆ Fs := fun E hE => by
    rcases genericPoint_mem_exceptionalSet_or_mem_of_mem_support h.isKltPair.1 hY hfbir hΔY hE
      with h1 | h1
    · exact hmemF E (hsub (Or.inl (Or.inl h1)))
    · refine hcov E (Or.inr (Or.inl ?_))
      obtain ⟨P, hP, hPm⟩ := DivisorWithCoeffs.mem_supp_iff.mp h1
      exact DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨P, by simpa [DivisorWithCoeffs.coeff_neg] using hP, hPm⟩
  set b : Fin (s + 1) → ℚ := fun j => -ΔY (F j)
  have hb : -∑ j, Finsupp.single (F j) (b j) = ΔY := by
    simp only [b, Finsupp.single_neg, Finset.sum_neg_distrib, neg_neg]
    exact (hsumF fun E => Finsupp.single E (ΔY E)).trans
      (sum_single_eq_of_support_subset ΔY hΔYsupp)
  have hpos : ∀ j, 0 < 1 + b j := fun j => by
    have := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary h.isKltPair hY hfbir
      hΔY (F j)
    rw [DivisorWithCoeffs.coeff_apply] at this
    simp only [b]
    linarith
  -- (v): the coefficients `p_j`
  obtain ⟨N, hN0, hN⟩ := exists_nat_div_two_mul_lt (fun j => p (F j)) (fun j => 1 + b j)
    (fun j => hp _ (hFmem j)) hpos
  set pj : Fin (s + 1) → ℚ := fun j => p (F j) / (2 * N)
  -- (vi): the coefficients `r_j`
  have hMq : M.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm M
  have hBM : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f M
  set rQ : QDivisor Y := QDivisor.pullback M hMq hBM
  have hrQ : M.IsPullback f hBM rQ := QDivisor.isPullback_pullback hMq hBM
  have hM'c : M'.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M'
  have he' : ((e.toNat : ℕ) : ℤ) = e := Int.toNat_of_nonneg (by omega)
  obtain ⟨D', hD', hD'pb⟩ := hrQ e.toNat (by omega) M' (by rwa [he']) hM'c
  have hrQc : ∀ E, rQ.coeff E = (D'.coeff E : ℚ) / e := by
    intro E
    have h1 := congrArg (fun B : QDivisor Y => B.coeff E) hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, he', zsmul_eq_mul] at h1
    rw [h1, mul_div_cancel_left₀ _ he0.ne']
  have hpbM := fun E => coeff_isPullback_of_isEffective
    (fun P => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)
    (fun P => MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P)
    f hM' hM'c hD'pb E
  have hsuppM : (M'.supp : Set X) = M.supp := by
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by omega) hMe]
  have hrQsupp : rQ.support ⊆ Fs := fun E hE => by
    refine hcov E (Or.inr (Or.inr ?_))
    have h1 : rQ.coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
    rw [hrQc] at h1
    have h2 : D'.coeff E ≠ 0 := fun h0 => h1 (by rw [h0]; simp)
    rw [← hsuppM]
    exact (hpbM E).2.1 h2
  set r : Fin (s + 1) → ℚ := fun j => rQ (F j)
  have hr : ∑ j, Finsupp.single (F j) (r j) = rQ :=
    (hsumF fun E => Finsupp.single E (rQ E)).trans (sum_single_eq_of_support_subset rQ hrQsupp)
  refine ⟨Y, hYln, hYn, hYc, f, s, F, b, pj, r,
    { toIsSmoothNonvanishingDatum := h
      one_le_dim := hn
      isClosed_point := hx
      notMem_supp := hxG
      le_q := hq
      one_le_e := he
      isIntegral_smul := ⟨G', hG'⟩
      isEffective_M := hMeff
      linearlyEquivalent := ⟨M', G', hMe, hG', hlin⟩
      multiplicityAt_gt := hmultM
      isLogResolution := hLR
      isProjectiveVariety_source := hproj
      injective := hFinj
      isSNC := ?_
      subset_iUnion := ?_
      isCrepantBoundary := ⟨hY, by rwa [hb]⟩
      pos_p := fun j => div_pos (hp _ (hFmem j)) (by positivity)
      lt_one_add := ?_
      isAmple_half := ?_
      nonneg_r := ?_
      isPullback_M := ⟨hBM, by rwa [hr]⟩
      b_zero_le := ?_
      multiplicityAt_le := ?_ }⟩
  · convert hsnc using 1
    exact hsumF fun E => Finsupp.single E (1 : ℤ)
  · intro y hy
    obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.mp (hsub (Or.inl hy))
    obtain ⟨j, rfl⟩ := hFsurj E hE
    exact Set.mem_iUnion.mpr ⟨j, hyE⟩
  · exact hN
  · refine ⟨hBsupp, fB, hfB, ?_⟩
    have : MMP.Mori.IsProjectiveVariety k (f ≫ sX) := hproj
    rw [hsumF fun E => Finsupp.single E (p E / (2 * (N : ℚ)))]
    exact isAmple_half_sub_sum (f ≫ sX) (isNef_of_isPullback rfl hAnef hfB) hAmp hN0
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hsmY _)
  · intro j
    change 0 ≤ rQ (F j)
    rw [← DivisorWithCoeffs.coeff_apply, hrQc]
    exact div_nonneg (by exact_mod_cast (hpbM (F j)).1) he0.le
  · change -ΔY (F 0) ≤ (n : ℚ) - 1
    rw [hF0, ← DivisorWithCoeffs.coeff_apply]
    exact hF₀b
  · change M.multiplicityAt x ≤ rQ (F 0)
    rw [hF0, ← DivisorWithCoeffs.coeff_apply, hrQc, hmultEq]
    refine div_le_div_of_nonneg_right ?_ he0.le
    have := (hpbM F₀).2.2
    rw [hF₀x] at this
    exact_mod_cast this

end MMP.FourfoldProofs.MmpFoundationKm3aNonvanishingAdaptedResolutionExistsWithSncContainmentProof

end

section

/-!
# Existence of adapted resolutions for the non-vanishing theorem

Let `k` be an algebraically closed field of characteristic `0` and `(X, D, G, a)` a smooth
non-vanishing datum of dimension `d ≥ 1` over `k` with `D` not numerically trivial. Then
`(X, D, G, a)` has an adapted resolution `(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)`. To build
it, take a closed point `x ∉ Supp G` and a divisor `M ∼_ℚ qD + G - K_X` with `mult_x M > 2d`.
Blow up `x`, and then take a projective log resolution of the transform of `G + M` together
with the exceptional divisor. The prime divisor `F_0` is the birational transform of the
exceptional divisor of the blow-up (when `d = 1`, the point `x` itself). The boundary
`F_0 + ⋯ + F_s` only has to contain `Ex(f) ∪ f⁻¹(Supp (G + M))`: it may have extra snc
components, and on those the coefficients `b_j` and `r_j` are `0`.

## Main results

* `MMP.Mori.IsSmoothNonvanishingDatum.exists_isNonvanishingAdaptedResolution`: a smooth
  non-vanishing datum of dimension `≥ 1` whose `D` is not numerically trivial has an adapted
  resolution.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Steps 2–4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.MmpFoundationKm3aNonvanishingAdaptedResolutionExistsWithSncContainmentProof in
/-- **Adapted resolutions exist** (Kollár–Mori 3.5, Steps 2–4). Every smooth non-vanishing datum
`(X, D, G, a)` of dimension `n ≥ 1` over an algebraically closed field of characteristic `0`
whose `D` is not numerically trivial has an adapted resolution
`(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)`. -/
@[mmp "lem_mmp_foundation_km3a_nonvanishing_adapted_resolution_exists_with_snc_containment"]
public theorem IsSmoothNonvanishingDatum.exists_isNonvanishingAdaptedResolution
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsSmoothNonvanishingDatum sX n K D G a) (hn : 1 ≤ n)
    (hD : ¬ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) :
    ∃ (x : X) (q e : ℤ) (M : QDivisor X) (Y : Scheme.{0}) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (_ : CompactSpace Y) (f : Y ⟶ X) (s : ℕ)
      (F : Fin (s + 1) → PrimeDivisor Y) (b p r : Fin (s + 1) → ℚ),
      IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r := by
  have : LocallyOfFiniteType sX := h.isKltPair.1.1.1.toLocallyOfFiniteType
  obtain ⟨x, hx, hxG⟩ := exists_isClosed_notMem_supp sX G
  obtain ⟨q₀, hq₀, H⟩ := h.exists_multiplicityAt_gt hn hD hx hxG
  obtain ⟨e, G', M', he, hG', hM', hlin, hmult⟩ := H q₀ le_rfl
  obtain ⟨Y, h1, h2, h3, f, s, F, b, p, r, hres⟩ :=
    exists_isNonvanishingAdaptedResolution_of_multiplicityAt_gt h hn hx hxG hq₀ he hG' hM'
      hlin hmult
  exact ⟨x, q₀, e, _, Y, h1, h2, h3, f, s, F, b, p, r, hres⟩

end MMP.Mori

end
