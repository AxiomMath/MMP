module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve

/-!
# Relative ampleness in relative Picard number one is tested on one curve

Let `f : X ⟶ Z` be a projective contraction of normal varieties over an algebraically closed
field of characteristic zero with `ρ(X/Z) = 1`, and let `C₀ ⊆ X` be an irreducible proper curve
contracted by `f`. A `ℚ`-Cartier `ℚ`-divisor `L` on `X` is `f`-ample if and only if
`L · C₀ > 0`.

An `f`-ample divisor `∑ⱼ rⱼ Aⱼ` has `L · C₀ = ∑ⱼ rⱼ (Aⱼ · C₀) > 0`. Conversely, `f` is projective,
so it carries an `f`-ample Cartier divisor `H`, positive on every contracted curve. As
`N¹(X/Z)` is a line spanned by the class of `L` (which is nonzero, `L · C₀ ≠ 0`), `H ≡_f c L`,
and `c > 0` by evaluating on `C₀`. Hence `L` is positive on every contracted curve: it is `f`-nef
and not numerically `f`-trivial, and the relative Kleiman criterion in Picard number one makes it
`f`-ample.

## Main results

* `MMP.Flips.isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one`.

## Implementation notes

`ρ(X/Z)` is `MMP.Flips.relativePicardNumber`, contractions are `MMP.Flips.IsContraction`, and
`f`-ampleness of a `ℚ`-divisor is `MMP.Flips.IsRelativelyAmple` of its image under
`MMP.Mori.QDivisor.toRDivisor`. The intersection number `L · C₀` is
`MMP.Mori.QDivisor.intersectionNumber` along the inclusion `C₀.ι` of the curve. Projectivity is
`AlgebraicGeometry.IsProjective` (a closed immersion into `𝐏(ℰ)` for a finite type
quasi-coherent `ℰ`), the weaker of the two notions of Stacks 01W8.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 5.1
-/

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry MMP.Mori

section Normalization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme), IsCurveNormalization ν ∧ topologicalKrullDim N ≤ 1 := by
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
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
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
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
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

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) [IsDominant f] [LocallyOfFiniteType f]
    (hf : IsBirationalMorphism f) : degreeOver f = 1 := by
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- A `ℚ`-Cartier `ℚ`-divisor `L` of Cartier index `n` is `n⁻¹ (n L)` as an `ℝ`-divisor, a
one-term presentation by the Cartier divisor `n L`. -/
private theorem toRDivisor_eq_inv_cartierIndex_smul (L : QDivisor X) (hL : L.IsQCartier) :
    QDivisor.toRDivisor L = ∑ _j : Fin 1, ((L.cartierIndex hL : ℕ) : ℝ)⁻¹ •
      Divisor.toRDivisor (QDivisor.isCartierDivisor_cartierIndex_smul hL).toDivisor := by
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hL
  refine Finsupp.ext fun P => ?_
  have hP := congrArg (fun G : QDivisor X => G P) hF.toQDivisor_toDivisor
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at hP
  have hn0 : ((L.cartierIndex hL : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (QDivisor.cartierIndex_pos hL).ne'
  change ((L P : ℚ) : ℝ) = (∑ _j : Fin 1, _ • Divisor.toRDivisor hF.toDivisor) P
  simp only [Fin.sum_univ_one, Finsupp.smul_apply, smul_eq_mul]
  change ((L P : ℚ) : ℝ) = _ * ((Divisor.toQDivisor hF.toDivisor P : ℚ) : ℝ)
  rw [hP]
  push_cast
  field_simp

/-- `L · C` is the value of `D · C` computed from the one-term presentation of `L`. -/
private theorem isRIntersectionNumber_intersectionNumber (L : QDivisor X) (hL : L.IsQCartier)
    (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (QDivisor.toRDivisor L)
      (fun _ : Fin 1 => ((L.cartierIndex hL : ℕ) : ℝ)⁻¹)
      (fun _ : Fin 1 => (QDivisor.isCartierDivisor_cartierIndex_smul hL).toDivisor) C
      (L.intersectionNumber k sX C.ι C.dim_le hL : ℝ) := by
  convert isRIntersectionNumber_sum_degreeOn _ _ _
    (fun _ => (QDivisor.isCartierDivisor_cartierIndex_smul hL).isCartier_toDivisor)
    (toRDivisor_eq_inv_cartierIndex_smul L hL) C using 1
  simp only [Fin.sum_univ_one, QDivisor.intersectionNumber]
  push_cast
  ring

/-- On an integral normal scheme, every Cartier Weil divisor `D` has a Cartier divisor whose
degree on every proper curve is `deg_C 𝒪_X(D)`. -/
private theorem exists_cartierDivisor_degree_eq [IsIntegral X] (D : Divisor X)
    (hD : D.IsCartier) : ∃ E : X.CartierDivisor, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨E, fun C => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- On an integral normal scheme, every `ℚ`-Cartier `ℚ`-divisor `L` has an `ℝ`-Cartier divisor
with the same intersection numbers with every proper curve. -/
private theorem exists_kCartierDivisor_intersectionNumber_eq [IsIntegral X] (L : QDivisor X)
    (hL : L.IsQCartier) : ∃ δ : KCartierDivisor ℝ X, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber δ = (L.intersectionNumber k sX C.ι C.dim_le hL : ℝ) := by
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨E, hE⟩ := exists_cartierDivisor_degree_eq (sX := sX) hF.toDivisor hF.isCartier_toDivisor
  refine ⟨((L.cartierIndex hL : ℝ))⁻¹ • KCartierDivisor.ofCartier ℝ E, fun C => ?_⟩
  simp only [OneCycle.intersectionNumber, map_smul, LinearMap.smul_apply, smul_eq_mul] at hE ⊢
  rw [hE, QDivisor.intersectionNumber]
  push_cast
  ring

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{0}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample `ℚ`-Cartier `ℚ`-divisor has positive intersection number with every proper curve
contracted by `f`. -/
private theorem intersectionNumber_pos_of_isRelativelyAmple [CompactSpace X] {Z : Scheme.{0}}
    (f : X ⟶ Z) {L : QDivisor X} (hL : L.IsQCartier)
    (hLa : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor L)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    0 < L.intersectionNumber k sX C.ι C.dim_le hL := by
  obtain ⟨m, a, A, hm, ha, hA, hLA⟩ := hLa
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have heq := (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _
    (isRIntersectionNumber_intersectionNumber L hL C)
    (isRIntersectionNumber_sum_degreeOn _ a A hAc hLA C)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpos : (0 : ℝ) < ∑ j, a j * ((A j).degreeOn k sX C.ι C.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (by
      exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) C hC))
      Finset.univ_nonempty
  exact_mod_cast heq ▸ hpos

/-- A projective morphism carries an `ℝ`-Cartier divisor positive on every contracted curve: the
class of an `f`-ample Cartier divisor. -/
private theorem exists_kCartierDivisor_pos_of_isProjective [IsIntegral X] [CompactSpace X]
    {Z : Scheme.{0}} {f : X ⟶ Z} (hfp : IsProjective f) : ∃ δ : KCartierDivisor ℝ X,
      ∀ C : ProperCurve sX, C.IsContractedBy f → 0 < (C.cycle ℝ).intersectionNumber δ := by
  obtain ⟨⟨M, hM, hMamp, hMA⟩, -⟩ := MMP.Foundations.IsProjective.exists_isRelativelyAmple hfp
  obtain ⟨A, ⟨e⟩⟩ := hMA inferInstance
  refine ⟨KCartierDivisor.ofCartier ℝ A, fun C hC => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f M
    (MMP.Mori.IsRelativelyAmple.of_stacks f M hMamp) C hC).trans_eq
    (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- **Positivity in a one-dimensional `N¹(X/Z)`.** If `N¹(X/Z)` is one-dimensional, `δA` is
positive on every contracted curve and `δ` is positive on one contracted curve `C₀`, then `δ` is
positive on every contracted curve: `δA ≡_f c δ`, and `c > 0` by evaluating on `C₀`. -/
private theorem intersectionNumber_pos_of_finrank_eq_one {Z : Scheme.{0}} {f : X ⟶ Z}
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    {δA δ : KCartierDivisor ℝ X}
    (hA : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 < (C.cycle ℝ).intersectionNumber δA)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f) (h₀ : 0 < (C₀.cycle ℝ).intersectionNumber δ)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) : 0 < (C.cycle ℝ).intersectionNumber δ := by
  have hne : (Submodule.Quotient.mk δ : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀.ne' (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δA)
  have hmem : δA - c • δ ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  have hc' : ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.cycle ℝ).intersectionNumber δA = c * (C.cycle ℝ).intersectionNumber δ := fun C hC => by
    have := (mem_relativeNumericallyTrivialDivisors sX f).mp hmem C hC
    simp only [OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have hc0 : 0 < c := pos_of_mul_pos_left (hc' C₀ hC₀ ▸ hA C₀ hC₀) h₀.le
  exact pos_of_mul_pos_right (hc' C hC ▸ hA C hC) hc0.le

end Normalization

end MMP.Flips

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-- **Ampleness in relative Picard number one is tested on one curve.** Let `f : X ⟶ Z` be a
projective contraction of normal varieties over an algebraically closed field `k` of
characteristic zero with `ρ(X/Z) = 1`, and `C₀` a proper irreducible curve on `X` contracted by
`f`. A `ℚ`-Cartier `ℚ`-divisor `L` on `X` is `f`-ample if and only if `L · C₀ > 0`. -/
@[mmp "lem_fa5_rho_one_ample_iff_positive"]
public theorem isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : IsNormalVariety k sX) (hZ : IsNormalVariety k sZ) (f : X ⟶ Z)
    (hf : IsContraction k sZ sX f) (hfp : IsProjective f) (hρ : relativePicardNumber sX f = 1)
    (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy f) (L : QDivisor X) (hL : L.IsQCartier) :
    IsRelativelyAmple f (QDivisor.toRDivisor L) ↔
      0 < L.intersectionNumber k sX C₀.ι C₀.dim_le hL := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  refine ⟨fun h => intersectionNumber_pos_of_isRelativelyAmple f hL h C₀ hC₀, fun hpos => ?_⟩
  have hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  obtain ⟨δA, hA⟩ := exists_kCartierDivisor_pos_of_isProjective (sX := sX) hfp
  obtain ⟨δL, hδL⟩ := exists_kCartierDivisor_intersectionNumber_eq (sX := sX) L hL
  have hLpos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      (0 : ℝ) < L.intersectionNumber k sX C.ι C.dim_le hL := fun C hC =>
    hδL C ▸ intersectionNumber_pos_of_finrank_eq_one hfin hA hC₀
      (by rw [hδL]; exact_mod_cast hpos) C hC
  have hpres := toRDivisor_eq_inv_cartierIndex_smul L hL
  have hFc := (QDivisor.isCartierDivisor_cartierIndex_smul hL).isCartier_toDivisor
  have hIR := isRIntersectionNumber_intersectionNumber (sX := sX) L hL
  have hwd := fun C => (IsRIntersectionNumber.eq_and_linear k sX C).1
  refine isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one sX sZ hX hZ f hfp
    hf.comp_eq hρ _ ⟨1, _, _, fun _ => hFc, hpres⟩
    ⟨1, _, _, fun _ => hFc, hpres, fun C hC x hx => ?_⟩ ?_
  · rw [hwd C _ _ _ _ _ x _ hx (hIR C)]
    exact (hLpos C hC).le
  · rintro ⟨-, -, h⟩
    have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ) Fin.elim0
        C₀ 0 := ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
    exact (hLpos C₀ hC₀).ne' (h C₀ hC₀ 1 _ _ _ 0 Fin.elim0 Fin.elim0 0 (hIR C₀) h0)

end MMP.Flips

end
