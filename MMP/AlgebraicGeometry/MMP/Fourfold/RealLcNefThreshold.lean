module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.RealLcRadialNullRay
public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties

/-!
# An attained real lc nef threshold on a fourfold

Let `f : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
fourfold with canonical divisor `K_X`. Let `B, C ≥ 0` be real divisors, `t₀ > 0`, with
`(X, B + t₀ C)` log canonical and `K_X + B + t₀ C` nef over `Z`. If `K_X + B` is not nef over `Z`,
the nef threshold `λ = min {t ∈ [0, t₀] | K_X + B + t C nef over Z}` is positive and is attained
on an extremal ray `R` of the relative closed cone of curves `NE̅(X/Z)`:
`(K_X + B + λ C) · R = 0`, `(K_X + B) · R < 0` and `C · R > 0`.

The nef parameters in `[0, t₀]` form a closed interval with positive minimum `λ`. For `λ' < λ`
close to `λ` the adjoint `K_X + B + λ' C` is negative on some extremal ray, and
`MMP.Fourfold.exists_pos_forall_isExtremalRay_null_of_isRealLcPair` (applied at the nef level
`λ`) makes that ray null for `K_X + B + λ C`; its negative degree at `λ'` is then
`(λ' - λ) C · R`, so `C · R > 0`, and `(K_X + B) · R = -λ C · R < 0`.

## Main results

* `MMP.Fourfold.exists_isExtremalRay_nef_threshold_of_isRealLcPair`.

## Implementation notes

An `ℝ`-Cartier divisor is paired with a class `u ∈ N₁(X/Z)` through a presentation `∑ cᵢ Mᵢ` by
Cartier divisors `Mᵢ`, as `∑ cᵢ (u · 𝒪_X(Mᵢ))` computed with
`MMP.Mori.RelativeNumericalCurveClasses.degree`. The pairing does not depend on the presentation;
the conclusion asserts each of the three degree conditions for every presentation, and records
that `K_X + B` and `C` are `ℝ`-Cartier, so that presentations exist. Nefness is relative to `Z`
(`MMP.Flips.IsRelativelyNef`). The dimension of `X` is the `4` of
`MMP.Mori.Divisor.IsCanonicalDivisor`. The threshold `λ` need not be rational.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_fourfold_real_fourfold_nef_threshold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Normalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
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

/-- An integral scheme proper over `k` is a `k`-variety. -/
private theorem isVariety_of_isProper {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
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
  have hc := isCurve_comp C hν hdim
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

/-- A value of `D · C` computed from a presentation `D = ∑ⱼ rⱼ Lⱼ` is `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem eq_sum_degreeOn_of_isRIntersectionNumber {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {C : ProperCurve sX} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) :
    x = ∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j) :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r L _ _ h
    (isRIntersectionNumber_sum_degreeOn D r L hL hD C)

/-- Two presentations of the same `ℝ`-divisor give the same degree on a proper curve. -/
private theorem sum_degreeOn_eq_of_sum_eq (C : ProperCurve sX) {m n : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    {s : Fin n → ℝ} {M : Fin n → Divisor X} (hM : ∀ i, (M i).IsCartier)
    (heq : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ i, s i • Divisor.toRDivisor (M i)) :
    ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) =
      ∑ i, s i * ((M i).degreeOn k sX C.ι C.dim_le (hM i) : ℝ) :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L s M _ _
    (isRIntersectionNumber_sum_degreeOn _ r L hL rfl C)
    (isRIntersectionNumber_sum_degreeOn _ s M hM heq C)

end Normalization

section Divisors

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- The concatenation of two presentations by Cartier divisors is one. -/
private theorem isCartier_append {n m : ℕ} {M : Fin n → Divisor X} {N : Fin m → Divisor X}
    (hM : ∀ i, (M i).IsCartier) (hN : ∀ j, (N j).IsCartier) :
    ∀ i, (Fin.append M N i).IsCartier := fun i => by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; exact hM i
  · rw [Fin.append_right]; exact hN j

/-- On a `ℚ`-factorial variety every `ℝ`-divisor `D` is a real combination `∑ rⱼ Lⱼ` of effective
Cartier divisors `Lⱼ`, with `rⱼ ≥ 0` when `D` is effective. -/
private theorem exists_effective_presentation_of_isQFactorial {k : Type} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsQFactorial sX) (D : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      (∀ j P, 0 ≤ (L j).coeff P) ∧ ((∀ P, 0 ≤ D.coeff P) → ∀ j, 0 ≤ r j) ∧
      D = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun j => D (e.symm j) / m (e.symm j),
    fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor X) 1,
    fun j => hc _, fun j P => ?_, fun hD j => div_nonneg (hD _) (Nat.cast_nonneg _), ?_⟩
  · simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hterm : ∀ P : MMP.Mori.PrimeDivisor X, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X) =
        Finsupp.single P (D P) := by
    intro P
    ext E
    have hm' : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    change (D P / m P) * ((((m P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X) E : ℝ) = _
    by_cases hE : P = E
    · subst hE
      simp [hm', DivisorWithCoeffs.coeff]
    · simp [Finsupp.single_apply, hE, DivisorWithCoeffs.coeff]
  simp only [hterm]
  rw [e.symm.sum_comp (fun P : D.support => Finsupp.single (P : MMP.Mori.PrimeDivisor X) (D P)),
    Finset.sum_coe_sort D.support (fun P => Finsupp.single P (D P))]
  exact (Finsupp.sum_single D).symm

/-- A real combination of Cartier divisors is `ℝ`-Cartier. -/
private theorem isRCartier_of_eq_sum [IsIntegral X] {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) : RDivisor.IsRCartier D :=
  ⟨m, r, L, hL, fun Γ => by
    subst hD
    simp [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
    rfl⟩

end Divisors

/-- **Lowering an effective boundary keeps a pair log canonical.** On a `ℚ`-factorial variety, if
`B, C ≥ 0` and `(X, B + t C)` is log canonical then so is `(X, B + s C)` for `0 ≤ s ≤ t`: the log
discrepancies only grow, by `(t - s)` times the multiplicity of the pull-back of the effective
divisor `C`. -/
private theorem isRealLcPair_add_smul_of_le {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hXq : IsQFactorial sX)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hlc : IsRealLcPair sX (B + t • C)) :
    IsRealLcPair sX (B + s • C) := by
  obtain ⟨hN, -, ⟨n₀, K₀, hK₀, -⟩, hld⟩ := hlc
  obtain ⟨q, ρ, G, hG, hGeff, hρ, hCG⟩ := exists_effective_presentation_of_isQFactorial hXq C
  have hρ' := hρ hC
  refine ⟨hN, fun P => ?_, ⟨n₀, K₀, hK₀, ?_⟩, fun n E a ha => ?_⟩
  · have h1 := hB P
    have h2 := hC P
    simp only [DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    positivity
  · obtain ⟨m, r, L, hL, -, -, h⟩ := exists_effective_presentation_of_isQFactorial hXq
      (Divisor.toRDivisor K₀ + (B + s • C))
    exact isRCartier_of_eq_sum hL h
  obtain ⟨hN', hprop, ω, hω, hK, m, r, Cc, C', hCc, hcoeff, hpull, rfl⟩ := ha
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := by
    haveI := E.isNormalVariety.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  have hBG := fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f (G j)
  let G' := fun j => (G j).pullback (hG j) (hBG j)
  have hG' : ∀ j, 0 ≤ (G' j).coeff E.E := fun j =>
    coeff_nonneg_of_isPullback_of_isEffectiveOn (hG j) (V := ⊤) (fun P _ => hGeff j P)
      (Divisor.isPullback_pullback (hG j) (hBG j)) E.E
      ⟨E.E.genericPoint, by rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩
  have key := hld n E (1 + (E.ordPullback ω : ℝ) -
      ∑ i, Fin.append r (fun j => (t - s) * ρ j) i * ((Fin.append C' G' i).coeff E.E : ℝ))
    ⟨hN', hprop, ω, hω, hK, m + q, Fin.append r (fun j => (t - s) * ρ j), Fin.append Cc G,
      Fin.append C' G', isCartier_append hCc hG, fun Γ => ?_, fun i => ?_, rfl⟩
  · rw [Fin.sum_univ_add] at key
    simp only [Fin.append_left, Fin.append_right] at key
    have hnn : 0 ≤ ∑ j, (t - s) * ρ j * ((G' j).coeff E.E : ℝ) :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hst) (hρ' j)) (by exact_mod_cast hG' j)
    linarith
  · have h1 := hcoeff Γ
    have h2 : C.coeff Γ = ∑ j, ρ j * ((G j).coeff Γ : ℝ) := by
      rw [hCG]
      simp [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
      rfl
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, mul_assoc, ← Finset.mul_sum]
    rw [← h2]
    simp only [DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul] at h1 ⊢
    linear_combination h1
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact hpull i
    · simp only [Fin.append_right]
      exact ⟨hBG j, Divisor.isPullback_pullback (hG j) (hBG j)⟩

/-- A linear form negative at one point of an extremal ray is negative on all of its nonzero
points. -/
private theorem neg_of_mem_isExtremalRay {V : Type*} [AddCommGroup V] [Module ℝ V] {N R : Set V}
    (hR : IsExtremalRay ℝ N R) (ℓ : V →ₗ[ℝ] ℝ) {w : V} (hw : w ∈ R) (hℓ : ℓ w < 0) :
    ∀ u ∈ R, u ≠ 0 → ℓ u < 0 := by
  obtain ⟨-, v, -, rfl⟩ := hR
  obtain ⟨a, ha, rfl⟩ := hw
  rintro _ ⟨b, hb, rfl⟩ hu
  have hb' : 0 < b := lt_of_le_of_ne hb (by rintro rfl; simp at hu)
  rw [map_smul, smul_eq_mul] at hℓ ⊢
  have hv : ℓ v < 0 := by
    by_contra h
    exact absurd hℓ (not_lt.mpr (mul_nonneg ha (not_lt.mp h)))
  exact mul_neg_of_pos_of_neg hb' hv

section Pairing

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {f : X ⟶ Z}

variable (sX f) in
/-- The degree form `z ↦ (z · 𝒪_X(M))` of a Cartier divisor `M` on `N₁(X/Z)`. -/
private noncomputable def degreeForm (M : Divisor X) (hM : M.IsCartier) :
    RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
  haveI := hM.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sX f M.divisorialSheaf

private theorem degreeForm_congr {M N : Divisor X} (h : M = N) (hM : M.IsCartier)
    (hN : N.IsCartier) : degreeForm sX f M hM = degreeForm sX f N hN := by
  subst h; rfl

variable (sX f) in
/-- The pairing `z ↦ ∑ cᵢ (z · 𝒪_X(Mᵢ))` of a presentation `∑ cᵢ Mᵢ` by Cartier divisors. -/
private noncomputable def pairing {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
  ∑ i, c i • degreeForm sX f (M i) (hM i)

private theorem pairing_apply {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (u : RelativeNumericalCurveClasses sX f) :
    pairing sX f c M hM u = ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) := by
  simp [pairing, degreeForm]

variable [QuasiCompact sX]

/-- On the class of a relative 1-cycle `∑ a_Γ Γ` the pairing is `∑ a_Γ ∑ cᵢ deg_Γ 𝒪_X(Mᵢ)`. -/
private theorem pairing_relativeNumericalClass {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (Zc : relativeOneCycles sX f) :
    pairing sX f c M hM (relativeNumericalClass sX f Zc) =
      (Zc : OneCycle ℝ sX).sum fun C a =>
        a * ∑ i, c i * ((M i).degreeOn ℂ sX C.ι C.dim_le (hM i) : ℝ) := by
  simp only [pairing, degreeForm, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
    RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.degree_apply,
    smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl

/-- On the class of a contracted curve `Γ` the pairing is `∑ cᵢ deg_Γ 𝒪_X(Mᵢ)`. -/
private theorem pairing_relativeClass {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    pairing sX f c M hM (C.relativeClass f hC) =
      ∑ i, c i * ((M i).degreeOn ℂ sX C.ι C.dim_le (hM i) : ℝ) := by
  rw [ProperCurve.relativeClass, pairing_relativeNumericalClass]
  simp [ProperCurve.cycle]

/-- The pairing depends only on the divisor `∑ cᵢ Mᵢ`. -/
private theorem pairing_eq_of_sum_eq {n m : ℕ} {c : Fin n → ℝ} {M : Fin n → Divisor X}
    (hM : ∀ i, (M i).IsCartier) {d : Fin m → ℝ} {N : Fin m → Divisor X}
    (hN : ∀ j, (N j).IsCartier)
    (h : ∑ i, c i • Divisor.toRDivisor (M i) = ∑ j, d j • Divisor.toRDivisor (N j)) :
    pairing sX f c M hM = pairing sX f d N hN := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨Zc, rfl⟩ := relativeNumericalClass_surjective sX f u
  rw [pairing_relativeNumericalClass, pairing_relativeNumericalClass]
  exact Finsupp.sum_congr fun C _ => by rw [sum_degreeOn_eq_of_sum_eq C hM hN h]

/-- A nef divisor pairs nonnegatively with every contracted curve, for every presentation. -/
private theorem pairing_nonneg_of_isRelativelyNef {D : RDivisor X}
    (hD : MMP.Flips.IsRelativelyNef ℂ sX f D) {n : ℕ} {c : Fin n → ℝ} {M : Fin n → Divisor X}
    (hM : ∀ i, (M i).IsCartier) (hDM : D = ∑ i, c i • Divisor.toRDivisor (M i))
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 ≤ pairing sX f c M hM (C.relativeClass f hC) := by
  obtain ⟨m, r, L, hL, hDL, hnn⟩ := hD
  have h := hnn C hC _ (isRIntersectionNumber_sum_degreeOn D r L hL hDL C)
  rwa [pairing_relativeClass, ← sum_degreeOn_eq_of_sum_eq C hL hM (hDL.symm.trans hDM)]

/-- A divisor pairing nonnegatively with every contracted curve is nef. -/
private theorem isRelativelyNef_of_pairing_nonneg {D : RDivisor X} {n : ℕ} {c : Fin n → ℝ}
    {M : Fin n → Divisor X} (hM : ∀ i, (M i).IsCartier)
    (hDM : D = ∑ i, c i • Divisor.toRDivisor (M i))
    (h : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f),
      0 ≤ pairing sX f c M hM (C.relativeClass f hC)) :
    MMP.Flips.IsRelativelyNef ℂ sX f D :=
  ⟨n, c, M, hM, hDM, fun C hC x hx => by
    rw [eq_sum_degreeOn_of_isRIntersectionNumber hM hDM hx, ← pairing_relativeClass c M hM C hC]
    exact h C hC⟩

/-- The pairing of the concatenated presentation of `D + t E`. -/
private theorem pairing_append {n m : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (d : Fin m → ℝ) (N : Fin m → Divisor X)
    (hN : ∀ j, (N j).IsCartier) (t : ℝ) (hMN : ∀ i, (Fin.append M N i).IsCartier)
    (u : RelativeNumericalCurveClasses sX f) :
    pairing sX f (Fin.append c (t • d)) (Fin.append M N) hMN u =
      pairing sX f c M hM u + t * pairing sX f d N hN u := by
  simp only [pairing, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply, Finset.mul_sum,
    mul_assoc]

/-- The concatenated presentation of `D + t E`. -/
private theorem add_smul_eq_sum_append {n m : ℕ} {D E : RDivisor X} {c : Fin n → ℝ}
    {M : Fin n → Divisor X} {d : Fin m → ℝ} {N : Fin m → Divisor X}
    (hD : D = ∑ i, c i • Divisor.toRDivisor (M i)) (hE : E = ∑ j, d j • Divisor.toRDivisor (N j))
    (t : ℝ) :
    D + t • E = ∑ i, Fin.append c (t • d) i • Divisor.toRDivisor (Fin.append M N i) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, hD, hE,
    Finset.smul_sum, smul_smul]

/-- A linear form on `N₁(X/Z)` that is negative on the class of a contracted curve is negative on
the nonzero points of some extremal ray of `NE̅(X/Z)`: the class is a sum of points of extremal
rays, and one summand must be negative. -/
private theorem exists_isExtremalRay_neg_of_relativeClass_neg {sZ : Z ⟶ Spec (.of ℂ)}
    [MMP.Mori.IsProjectiveVariety ℂ sX] [MMP.Mori.IsProjectiveVariety ℂ sZ] (hf : f ≫ sZ = sX)
    (ℓ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ) {Γ : ProperCurve sX}
    (hΓ : Γ.IsContractedBy f) (hℓ : ℓ (Γ.relativeClass f hΓ) < 0) :
    ∃ R : Set (RelativeNumericalCurveClasses sX f),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX f :
        Set (RelativeNumericalCurveClasses sX f)) R ∧ ∀ u ∈ R, u ≠ 0 → ℓ u < 0 := by
  have hz : Γ.relativeClass f hΓ ∈ relativeClosedConeOfCurves sX f := by
    change _ ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
    rw [coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hΓ)
  obtain ⟨s, R, w, hRw, hzw⟩ :=
    exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sZ f hf hz
  obtain ⟨i, hi⟩ : ∃ i, ℓ (w i) < 0 := by
    by_contra! h
    rw [hzw, map_sum] at hℓ
    exact hℓ.not_ge (Finset.sum_nonneg fun i _ => h i)
  exact ⟨R i, (hRw i).1, neg_of_mem_isExtremalRay (hRw i).1 ℓ (hRw i).2 hi⟩

end Pairing

/-- **Comparing two levels.** If `a + l b = 0` and `a + l' b < 0` with `l' < l` and `l > 0`, then
`b > 0` and `a < 0`. -/
private theorem pos_and_neg_of_add_mul_eq_zero_of_lt {a b l l' : ℝ} (hl : 0 < l) (hl' : l' < l)
    (h₀ : a + l * b = 0) (h₁ : a + l' * b < 0) : 0 < b ∧ a < 0 := by
  have hb : 0 < b := by nlinarith
  exact ⟨hb, by nlinarith⟩

/-- **An attained real lc nef threshold in dimension four.** -/
private theorem solution : ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hlc : IsRealLcPair sX (B + t₀ • C))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + t₀ • C)))
    (hnot : ¬ MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K B)),
    ∃ l : ℝ, 0 < l ∧ l ≤ t₀ ∧
      MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + l • C)) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧ RDivisor.IsRCartier C ∧
      ∃ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + (B + l • C) = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) = 0) ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, u ≠ 0 → ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          C = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, u ≠ 0 → 0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u)) := by
  intro X Z _ _ _ _ sX sZ hX hZ f hf hXq K hK B C hB hC t₀ ht₀ hlc hnef hnot
  haveI := hX
  haveI := hZ
  -- presentations of `K + B` and `C`, and of the adjoints `K + B + t C`
  obtain ⟨m₁, a, P, hP, -, -, hKB⟩ :=
    exists_effective_presentation_of_isQFactorial hXq (Divisor.toRDivisor K + B)
  obtain ⟨m₂, b, Q, hQ, -, -, hCQ⟩ := exists_effective_presentation_of_isQFactorial hXq C
  have hPQ := isCartier_append hP hQ
  have hpres : ∀ t : ℝ, Divisor.toRDivisor K + (B + t • C) =
      ∑ i, Fin.append a (t • b) i • Divisor.toRDivisor (Fin.append P Q i) := fun t => by
    rw [← add_assoc]
    exact add_smul_eq_sum_append hKB hCQ t
  have hpair : ∀ (t : ℝ) (u : RelativeNumericalCurveClasses sX f),
      pairing sX f (Fin.append a (t • b)) (Fin.append P Q) hPQ u =
        pairing sX f a P hP u + t * pairing sX f b Q hQ u :=
    fun t u => pairing_append a P hP b Q hQ t hPQ u
  set α := pairing sX f a P hP
  set β := pairing sX f b Q hQ
  have hnefS : ∀ t : ℝ, (∀ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f),
      0 ≤ α (Γ.relativeClass f hΓ) + t * β (Γ.relativeClass f hΓ)) ↔
      MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + t • C)) :=
    fun t => ⟨fun h => isRelativelyNef_of_pairing_nonneg hPQ (hpres t) fun Γ hΓ => by
        rw [hpair]; exact h Γ hΓ,
      fun h Γ hΓ => by
        rw [← hpair]; exact pairing_nonneg_of_isRelativelyNef h hPQ (hpres t) Γ hΓ⟩
  -- the nef threshold
  let S : Set ℝ := {t | 0 ≤ t ∧ t ≤ t₀ ∧ ∀ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f),
      0 ≤ α (Γ.relativeClass f hΓ) + t * β (Γ.relativeClass f hΓ)}
  have ht₀S : t₀ ∈ S := ⟨ht₀.le, le_rfl, (hnefS t₀).2 hnef⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hSc : IsClosed S := by
    simp only [S, Set.setOf_and, Set.setOf_forall]
    exact (isClosed_le continuous_const continuous_id).inter <|
      (isClosed_le continuous_id continuous_const).inter <|
        isClosed_iInter fun Γ => isClosed_iInter fun hΓ => isClosed_le continuous_const
          (by fun_prop)
  set l := sInf S
  obtain ⟨hl0, hlt₀, hlS⟩ : l ∈ S := hSc.csInf_mem ⟨t₀, ht₀S⟩ hbdd
  have hnefl := (hnefS l).1 hlS
  have hl_pos : 0 < l := by
    refine lt_of_le_of_ne hl0 fun h0 => hnot ?_
    rw [← h0] at hlS
    simpa using (hnefS 0).1 hlS
  -- the two log canonical pairs
  have hlcl : IsRealLcPair sX (B + l • C) := isRealLcPair_add_smul_of_le hXq hB hC hl0 hlt₀ hlc
  have hlc0 : IsRealLcPair sX B := by
    simpa using isRealLcPair_add_smul_of_le hXq hB hC le_rfl ht₀.le hlc
  obtain ⟨t₁, ht₁, hnull⟩ :=
    exists_pos_forall_isExtremalRay_null_of_isRealLcPair hX hZ hf hXq hK hlcl hlc0 hnefl
  -- a level `l' < l` close to `l`
  set τ := min (t₁ / 2) (1 / 2)
  have hτ0 : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτt : τ < t₁ := min_lt_of_left_lt (half_lt_self ht₁)
  have hτ1 : τ < 1 := min_lt_of_right_lt (by norm_num)
  set l' := (1 - τ) * l with hl'
  have hl'0 : 0 ≤ l' := mul_nonneg (by linarith) hl0
  have hl'l : l' < l := by nlinarith
  have hl'S : l' ∉ S := notMem_of_lt_csInf hl'l hbdd
  obtain ⟨Γ, hΓ, hneg⟩ : ∃ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f),
      α (Γ.relativeClass f hΓ) + l' * β (Γ.relativeClass f hΓ) < 0 := by
    by_contra h
    push Not at h
    exact hl'S ⟨hl'0, by linarith, h⟩
  -- a negative extremal ray at level `l'`
  obtain ⟨R, hR, hRneg⟩ := exists_isExtremalRay_neg_of_relativeClass_neg hf
    (pairing sX f (Fin.append a (l' • b)) (Fin.append P Q) hPQ) hΓ (by rw [hpair]; exact hneg)
  -- the radial-null lemma makes it null at level `l`
  have hRnull := hnull τ hτ0 hτt R hR ⟨_, _, _, hPQ, by
      rw [← hpres l', hl']
      module,
    fun u hu hu0 => by rw [← pairing_apply _ _ hPQ]; exact hRneg u hu hu0⟩
  have hsign : ∀ u ∈ R, u ≠ 0 → 0 < β u ∧ α u < 0 := fun u hu hu0 =>
    pos_and_neg_of_add_mul_eq_zero_of_lt hl_pos hl'l
      (by rw [← hpair, pairing_apply]; exact hRnull _ _ _ hPQ (hpres l) u hu)
      (by rw [← hpair]; exact hRneg u hu hu0)
  refine ⟨l, hl_pos, hlt₀, hnefl, isRCartier_of_eq_sum hP hKB, isRCartier_of_eq_sum hQ hCQ,
    R, hR, hRnull, ?_, ?_⟩
  · intro n c M hM hKBM u hu hu0
    rw [← pairing_apply _ _ hM, pairing_eq_of_sum_eq hM hP (hKBM.symm.trans hKB)]
    exact (hsign u hu hu0).2
  · intro n c M hM hCM u hu hu0
    rw [← pairing_apply _ _ hM, pairing_eq_of_sum_eq hM hQ (hCM.symm.trans hCQ)]
    exact (hsign u hu hu0).1

end Proof_lem_fourfold_real_fourfold_nef_threshold

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **An attained real lc nef threshold in dimension four.** Let `f : X ⟶ Z` be a morphism of
projective complex varieties, `X` normal `ℚ`-factorial of dimension four with canonical divisor
`K`, let `B, C` be effective real divisors and `t₀ > 0` with `(X, B + t₀ C)` log canonical
(`MMP.Fourfold.IsRealLcPair`) and `K + B + t₀ C` nef over `Z`. If `K + B` is not nef over `Z`,
there are `0 < λ ≤ t₀` and an extremal ray `R` of `NE̅(X/Z)` such that `K + B + λ C` is nef over
`Z`, `(K + B + λ C) · R = 0`, `(K + B) · R < 0` and `C · R > 0`, the degrees being computed from
any presentation by Cartier divisors. -/
@[mmp "lem_fourfold_real_fourfold_nef_threshold"]
public theorem exists_isExtremalRay_nef_threshold_of_isRealLcPair
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hlc : IsRealLcPair sX (B + t₀ • C))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + t₀ • C)))
    (hnot : ¬ MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K B)) :
    ∃ l : ℝ, 0 < l ∧ l ≤ t₀ ∧
      MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K (B + l • C)) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧ RDivisor.IsRCartier C ∧
      ∃ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + (B + l • C) = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) = 0) ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, u ≠ 0 → ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) ∧
        (∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          C = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, u ≠ 0 → 0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u)) :=
              by revert X Z sX sZ hX hZ f hf hXq K hK B C hB hC t₀ ht₀ hlc hnef hnot; first | exact Proof_lem_fourfold_real_fourfold_nef_threshold.solution | exact Proof_lem_fourfold_real_fourfold_nef_threshold.solution _ | exact Proof_lem_fourfold_real_fourfold_nef_threshold.solution _ _ | exact Proof_lem_fourfold_real_fourfold_nef_threshold.solution _ _ _ | exact Proof_lem_fourfold_real_fourfold_nef_threshold.solution _ _ _ _

end MMP.Fourfold

