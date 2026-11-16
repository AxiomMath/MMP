module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization

/-!
# Adjoint pull-back on ample models and transforms of numerically trivial divisors

* For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, with
  `K_V = q_* K_M`, the divisor `K_V + B_V` is `ℚ`-Cartier and `K_M + B_M = q^*(K_V + B_V)`: a
  Cartier multiple of `K_M + B_M` is the pull-back of a relatively ample divisor on `V`.
* For proper birational morphisms `h : Y ⟶ Z`, `h' : Y' ⟶ Z` from normal varieties over a field
  `k`, `Y'` `ℚ`-factorial, and `ψ = h'⁻¹ ∘ h` creating no divisor, the
  transform `ψ_*G` of an `ℝ`-Cartier divisor `G ≡_h 0` is `ℝ`-Cartier and `ψ_*G ≡_{h'} 0`. The
  proof passes through a common resolution of `Y` and `Y'` over `Z` and the negativity lemma.

## Main results

* `MMP.Fourfold.IsAmpleModelDatum.isPullback_logCanonicalDivisor`: `K_M + B_M = q^*(K_V + B_V)`.
* `MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver`: birational transforms of
  numerically trivial divisors.

## Implementation notes

`q^*` is `QDivisor.IsPullback`, unique on `ℚ`-Cartier divisors, and `q_*`, `ψ_*` are the
birational transforms `RationalMap.transformDivisor`. The auxiliary lemmas of each proof live in
the namespace `Proof_<tag>` named after its label.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_oai4_c3_ample_model_adjoint_pullback

open MMP.Mori MMP.Fourfold

/-- **A `ℚ`-divisor with a Cartier multiple pulling back to a multiple of `B'` pulls back to
`B'`.** If `T = nB` is Cartier for some `n > 0` and `T` pulls back to a divisor `D'` with
`D' = nB'`, then `B` is `ℚ`-Cartier and `f^*B = B'`. -/
private theorem QDivisor.isQCartier_and_isPullback_of_zsmul {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {B : QDivisor Y} {B' : QDivisor X} {n : ℕ} (hn : 0 < n) {T : Divisor Y}
    (hTB : Divisor.toQDivisor T = (n : ℤ) • B) (hTc : T.IsCartier) {D' : Divisor X}
    {hT : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ T.supp}
    (hTp : T.IsPullback f hT D') (hD' : Divisor.toQDivisor D' = (n : ℤ) • B') :
    B.IsQCartier ∧ ∃ hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp,
      B.IsPullback f hB B' := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQC : B.IsQCartier := ⟨n, hn', T, hTB, hTc⟩
  have hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp := fun Z hZ =>
    hT Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hn' hTB])
  refine ⟨hQC, hB, ?_⟩
  have hG := QDivisor.isPullback_pullback hQC hB
  obtain ⟨D'', hD'', hp⟩ := hG n hn T hTB hTc
  rw [hp.eq hTc hTp, hD'] at hD''
  have : B.pullback hQC hB = B' := by
    ext P
    have := congrArg (fun G : QDivisor X => G.coeff P) hD''
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact (mul_left_cancel₀ (by exact_mod_cast hn') this).symm
  exact this ▸ hG

end Proof_lem_oai4_c3_ample_model_adjoint_pullback

namespace MMP.Fourfold

open Proof_lem_oai4_c3_ample_model_adjoint_pullback

open MMP.Mori

variable {X Z M V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
  [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]

/-- For an ample-model datum `(M, B_M, q, V, B_V)` of a birational contraction `f : X ⟶ Z`, and
the canonical divisor `K_V = q_* K_M` of `V`, the `ℚ`-divisor `K_V + B_V` is `ℚ`-Cartier and
`K_M + B_M = q^*(K_V + B_V)`. -/
@[mmp "lem_oai4_c3_ample_model_adjoint_pullback"]
public theorem IsAmpleModelDatum.isPullback_logCanonicalDivisor
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sM : M ⟶ Spec (.of ℂ)} [QuasiCompact sM]
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {KM : Divisor M} {BM : QDivisor M}
    {φ : X.RationalMap M} {πM : M ⟶ Z} {q : M ⟶ V} {p : V ⟶ Z} {BV : QDivisor V}
    (h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p BV)
    {KV : Divisor V} (hKV : RationalMap.transformDivisor (X := M) q.toRationalMap KM = KV) :
    (Divisor.toQDivisor KV + BV).IsQCartier ∧
      ∃ hq : ∀ T : irreducibleComponents M,
          q (componentGenericPoint M T) ∉ (Divisor.toQDivisor KV + BV).supp,
        (Divisor.toQDivisor KV + BV).IsPullback q hq (Divisor.toQDivisor KM + BM) := by
  obtain ⟨-, _, hV, hM, _, hqb⟩ := h.isProper_and_isBirationalMorphism
  obtain ⟨k, hk, D, hD, hDC, hfree, A, e, he, hind⟩ := h.isRelativeAmpleModel
  obtain ⟨d, hd, H, _, -, ⟨eH⟩⟩ := DivisorialSectionAlgebra.exists_isRelativelyAmple_pullback_iso
    h.isProjectiveVariety_target h.isGoodLogMinimalModel.isProjectiveMorphism_model hDC hfree A e
    he hind
  obtain ⟨hTc, _, hTp⟩ := isPullback_transformDivisor_of_iso hV hM hqb H eH
  refine QDivisor.isQCartier_and_isPullback_of_zsmul (Nat.mul_pos hd hk) ?_ hTc hTp ?_
  · -- `q_*` preserves the coefficient at the strict transform of each prime divisor of `V`
    refine Finsupp.ext fun P => ?_
    obtain ⟨E, -, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV hM hqb P
    have hDE : ((D E : ℤ) : ℚ) = (k : ℚ) * ((KM E : ℚ) + BM E) :=
      congrArg (fun G : QDivisor M => G E) hD
    change (((RationalMap.transformDivisor (X := M) q.toRationalMap ((d : ℤ) • D)) P : ℤ) : ℚ) =
      ((d * k : ℕ) : ℤ) • ((KV P : ℚ) + BV P)
    rw [htr, ← hKV, htr, h.boundary_eq, htr, Finsupp.smul_apply, smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [hDE]
    ring
  · rw [map_zsmul, hD, Nat.cast_mul, mul_smul]
    norm_cast

end MMP.Fourfold

namespace Proof_lem_fa18_numerically_trivial_transform

open MMP.Mori MMP.Flips

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

/-- A normalization `C'` of a proper curve with `dim C' ≤ 1` is a curve over `k`. -/
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
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by
    rw [← Category.assoc]
    infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
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

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
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
      isBirationalMorphism :=
        isBirationalMorphism_of_isBirational _ (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
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

/-- A value of `D · C` computed from a presentation `D = ∑ r_j L_j` is `∑ r_j deg_C 𝒪_X(L_j)`. -/
private theorem eq_sum_degreeOn_of_isRIntersectionNumber {C : ProperCurve sX} {D : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) :
    ∃ hL : ∀ j, (L j).IsCartier, D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
      x = ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) := by
  obtain ⟨hL, d, hD, hd, hx⟩ := id h
  refine ⟨hL, hD, ?_⟩
  have h' := isRIntersectionNumber_sum_degreeOn k sX C r L hL
  rw [← hD] at h'
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r L x _ h h'

/-- Two presentations of the same `ℝ`-divisor by Cartier divisors give the same degree on `C`. -/
private theorem sum_degreeOn_eq_of_sum_eq (C : ProperCurve sX) {m n : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    {s : Fin n → ℝ} {M : Fin n → Divisor X} (hM : ∀ i, (M i).IsCartier)
    (heq : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ i, s i • Divisor.toRDivisor (M i)) :
    ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) =
      ∑ i, s i * ((M i).degreeOn k sX C.ι C.dim_le (hM i) : ℝ) := by
  have h₁ := isRIntersectionNumber_sum_degreeOn k sX C r L hL
  have h₂ := isRIntersectionNumber_sum_degreeOn k sX C s M hM
  rw [heq] at h₁
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L s M _ _ h₁ h₂

/-- Every value of `0 · C` is `0`. -/
private theorem eq_zero_of_isRIntersectionNumber_zero {C : ProperCurve sX} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX 0 r L C x) : x = 0 := by
  obtain ⟨hL, hD, hx⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sX h
  rw [hx]
  have := sum_degreeOn_eq_of_sum_eq k sX C hL (s := Fin.elim0) (M := Fin.elim0)
    (fun i => i.elim0) (by rw [← hD]; simp)
  simpa using this

end Intersection

section Projection

variable {k : Type u} [Field k]

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `f : X ⟶ Y`: on a
proper curve `C ⊆ X` whose image is the proper curve `C₀ ⊆ Y`,
`f^*D · C = [k(C) : k(C₀)] · (D · C₀)`. -/
private theorem degreeOn_pullback_eq_mul {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (C : ProperCurve sX) (C₀ : ProperCurve sY) (hC : C₀.point = f C.point) :
    (D.pullback hD hB).degreeOn k sX C.ι C.dim_le (hD.isCartier_pullback f hB) =
      (residueFieldDegree f C.point : ℤ) * D.degreeOn k sY C₀.ι C₀.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hD hB C, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C₀.isProperCurve)]
  have hCe : (⟨f C.point, hC ▸ C₀.isProperCurve⟩ : ProperCurve sY) = C₀ := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `f : X ⟶ Y` has degree zero on a proper curve
`C ⊆ X` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (C : ProperCurve sX) (hc : ¬ IsProperCurve sY (f C.point)) :
    (D.pullback hD hB).degreeOn k sX C.ι C.dim_le (hD.isCartier_pullback f hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hD hB C, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- A one-dimensional integral closed subscheme has a point other than its generic point. -/
private theorem exists_ne_mem_closure_of_dim_eq_one {X : Scheme.{u}} (x : X)
    (h : topologicalKrullDim (curveSubschemeAt x) = 1) : ∃ y ∈ closure ({x} : Set X), y ≠ x := by
  by_contra! hcon
  have hsub : Subsingleton (curveSubschemeAt x) := by
    refine ⟨fun a b => ?_⟩
    have ha : curveSubschemeAtι x a ∈ closure ({x} : Set X) :=
      range_curveSubschemeAtι x ▸ ⟨a, rfl⟩
    have hb : curveSubschemeAtι x b ∈ closure ({x} : Set X) :=
      range_curveSubschemeAtι x ▸ ⟨b, rfl⟩
    exact (curveSubschemeAtι x).isEmbedding.injective ((hcon _ ha).trans (hcon _ hb).symm)
  have : topologicalKrullDim (curveSubschemeAt x) ≤ 0 := by
    have : Subsingleton (TopologicalSpace.IrreducibleCloseds (curveSubschemeAt x)) :=
      ⟨fun S T => TopologicalSpace.IrreducibleCloseds.ext <|
        (Subsingleton.eq_univ_of_nonempty S.isIrreducible.nonempty).trans
          (Subsingleton.eq_univ_of_nonempty T.isIrreducible.nonempty).symm⟩
    exact Order.krullDim_nonpos_of_subsingleton
  rw [h] at this
  exact absurd this (by decide)

/-- A morphism of schemes over `k` which is non-constant on a proper curve has positive residue
degree at the generic point of the curve. -/
private theorem residueFieldDegree_pos_of_not_constant {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (hnc : ¬ ∃ y : Y, Set.range (C.ι ≫ f) = {y}) : 0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree f C.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
    rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField C.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint C.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- If a morphism `f` over `k` maps the generic point of a proper curve `C` to the generic point
of a proper curve `C₀`, then `[k(C) : k(C₀)] > 0`. -/
private theorem residueFieldDegree_pos_of_map_point {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX) (C₀ : ProperCurve sY)
    (hC : f C.point = C₀.point) : 0 < residueFieldDegree f C.point := by
  refine residueFieldDegree_pos_of_not_constant f hf C fun ⟨y, hy⟩ => ?_
  obtain ⟨z, hz, hne⟩ := exists_ne_mem_closure_of_dim_eq_one C₀.point C₀.dim_eq
  have hφ : (C.ι ≫ f) ≫ sY = C.ι ≫ sX := by rw [Category.assoc, hf]
  have : IsProper ((C.ι ≫ f) ≫ sY) := hφ ▸ inferInstance
  have : IsProper (C.ι ≫ f) := IsProper.of_comp _ sY
  have hcl : IsClosed (Set.range (C.ι ≫ f)) := (C.ι ≫ f).isClosedMap.isClosed_range
  have hmem : C₀.point ∈ Set.range (C.ι ≫ f) := by
    refine ⟨genericPoint C.scheme, ?_⟩
    rw [Scheme.Hom.comp_apply, C.ι_genericPoint, hC]
  have hz' : z ∈ Set.range (C.ι ≫ f) :=
    (closure_minimal (Set.singleton_subset_iff.mpr hmem) hcl) hz
  rw [hy] at hmem hz'
  exact hne ((Set.mem_singleton_iff.mp hz').trans (Set.mem_singleton_iff.mp hmem).symm)

end Projection

section Contracted

variable {k : Type u} [Field k]

/-- If `C ⊆ X` is contracted by `g ≫ f` and `g` is closed, the image curve `g(C)` is contracted by
`f`. -/
private theorem isContractedBy_of_comp {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (g : X ⟶ Y) [IsProper g] (f : Y ⟶ W) (C : ProperCurve sX)
    (hC : C.IsContractedBy (g ≫ f)) (C₀ : ProperCurve sY) (hC₀ : C₀.point = g C.point) :
    C₀.IsContractedBy f := by
  intro x hx
  have hcl : closure ({C₀.point} : Set Y) = g '' closure {C.point} := by
    rw [← g.isClosedMap.closure_image_eq_of_continuous g.continuous, Set.image_singleton, hC₀]
  rw [hcl] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have := hC y hy
  simp only [Scheme.Hom.comp_apply] at this
  rw [this, hC₀]

/-- If `f` maps the generic point of `C` to that of a curve `C₀` contracted by `f'`, then `C` is
contracted by `f ≫ f'`. -/
private theorem isContractedBy_comp_of_map {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (f : X ⟶ Y) (f' : Y ⟶ W) (C : ProperCurve sX) (C₀ : ProperCurve sY)
    (hC : f C.point = C₀.point) (hC₀ : C₀.IsContractedBy f') : C.IsContractedBy (f ≫ f') := by
  intro x hx
  have hx' : f x ∈ closure ({C₀.point} : Set Y) := by
    rw [← hC, ← Set.image_singleton]
    exact image_closure_subset_closure_image f.continuous ⟨x, hx, rfl⟩
  simp only [Scheme.Hom.comp_apply]
  rw [hC₀ _ hx', hC]

/-- A curve contracted by `f` is contracted by `f ≫ f'`. -/
private theorem isContractedBy_comp {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (f : X ⟶ Y) (f' : Y ⟶ W) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    C.IsContractedBy (f ≫ f') := by
  intro x hx
  simp only [Scheme.Hom.comp_apply]
  rw [hC x hx]

end Contracted

section QFactorial

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor has a
Cartier multiple. -/
private theorem isCartierCombination_of_isQFactorial {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Fourfold.IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun j => D (e.symm j) / m (e.symm j),
    fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor X) 1,
    fun j => hc _, ?_⟩
  have hterm : ∀ P : MMP.Mori.PrimeDivisor X, (D P / m P) •
      DivisorWithCoeffs.mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero
        (((m P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X) = Finsupp.single P (D P) := by
    intro P
    ext E
    rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_mapCoeffs]
    have hm' : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    by_cases hE : P = E
    · subst hE
      simp [DivisorWithCoeffs.coeff, hm']
    · simp [DivisorWithCoeffs.coeff, Finsupp.single_apply, hE]
  simp only [hterm]
  rw [e.symm.sum_comp (fun P : D.support => Finsupp.single (P : MMP.Mori.PrimeDivisor X) (D P)),
    Finset.sum_coe_sort D.support (fun P => Finsupp.single P (D P))]
  exact (Finsupp.sum_single D).symm

end QFactorial

section Lifting

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [TopologicalSpace.NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over `k`: it factors through its scheme-theoretic image, which is `C'`. -/
private lemma isProper_comp_of_closure_range {k : Type u} [Field k] {X B : Scheme.{u}}
    {sB : B ⟶ Spec (.of k)} (C' : ProperCurve sB) (φ : X ⟶ B) [IsReduced X] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {C'.point}) : IsProper (φ ≫ sB) := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {C'.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB)
    rw [hker]
    exact C'.isProper_ι_comp
  have : IsProper (φ.toImage ≫ φ.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting curves.** Let `f : A ⟶ B` be a proper surjective morphism of schemes of finite type
over `k`. Every proper curve `C' ⊆ B` is the image of a proper curve `C ⊆ A`, in the sense that
`f` maps the generic point of `C` to that of `C'`. -/
private theorem ProperCurve.exists_map_point_eq {k : Type u} [Field k] {A B : Scheme.{u}}
    (sA : A ⟶ Spec (.of k)) (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] [QuasiCompact sB] (f : A ⟶ B) [IsProper f] [Surjective f]
    (hf : f ≫ sB = sA) (C' : ProperCurve sB) : ∃ C : ProperCurve sA, f C.point = C'.point := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber f.base (f.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ f
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  -- the generic fibre of `φ` is the single point `genericPoint`
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = C'.point → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hf]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  exact ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range C' φ hclr⟩, haξ⟩

end Lifting

section Graph

/-- A birational morphism from an irreducible scheme induces an isomorphism of local rings at the
generic point. -/
private theorem isIso_stalkMap_genericPoint {X S : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ S)
    (hf : IsBirationalMorphism f) : IsIso (f.stalkMap (genericPoint X)) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hW1, hW2, hWe⟩ := he
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at hWe
  have hι : X.homOfLE hW2 ≫ X.topIso.hom = W.ι := Scheme.homOfLE_ι X hW2
  have hη : genericPoint X ∈ W := by
    haveI : Nonempty X := ⟨genericPoint X⟩
    obtain ⟨w, hw⟩ : (W : Set X).Nonempty := Dense.nonempty hW
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨w, trivial, hw⟩
  have hoi1 : IsOpenImmersion (e.iso.hom ≫ e.target.ι) := inferInstance
  have hoi2 : IsOpenImmersion (X.homOfLE hW1 ≫ (e.iso.hom ≫ e.target.ι)) :=
    @IsOpenImmersion.comp _ _ _ _ _ _ hoi1
  have hEq : X.homOfLE hW1 ≫ e.iso.hom ≫ e.target.ι = W.ι ≫ f :=
    hWe.trans ((Category.assoc (X.homOfLE hW2) X.topIso.hom f).symm.trans
      (congrArg (· ≫ f) hι))
  have hoi3 : IsOpenImmersion (W.ι ≫ f) := hEq ▸ hoi2
  have h1 := Scheme.Hom.stalkMap_comp W.ι f ⟨genericPoint X, hη⟩
  have h2 := IsOpenImmersion.instIsIsoCommRingCatStalkMap (W.ι ≫ f) ⟨genericPoint X, hη⟩
  rw [h1] at h2
  have h3 := IsOpenImmersion.instIsIsoCommRingCatStalkMap W.ι ⟨genericPoint X, hη⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (f.stalkMap (W.ι ⟨genericPoint X, hη⟩))
    (W.ι.stalkMap ⟨genericPoint X, hη⟩) h3 h2

/-- If `f` is locally of finite type and induces an isomorphism of local rings at the generic point
`η` of `X`, then `η` is the only point of its fibre. -/
private theorem eq_genericPoint_of_map_eq {X S : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ S)
    [LocallyOfFiniteType f] (hf : IsIso (f.stalkMap (genericPoint X))) {x : X}
    (hx : f x = f (genericPoint X)) : x = genericPoint X := by
  set η := genericPoint X
  have hsurj : Function.Surjective (f.residueFieldMap η).hom := by
    intro y
    obtain ⟨a, rfl⟩ := X.residue_surjective η y
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap η)).2 a
    refine ⟨S.residue (f η) b, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  have hfin : letI := (f.residueFieldMap η).hom.toAlgebra
      Module.Finite (S.residueField (f η)) (X.residueField η) := by
    letI := (f.residueFieldMap η).hom.toAlgebra
    exact Module.Finite.of_surjective (Algebra.linearMap _ _) hsurj
  have hcl := (isClosed_asFiber_iff_finite_residueField f η).mpr hfin
  obtain ⟨b, rfl⟩ : x ∈ Set.range (f.fiberι (f η)) := by
    rwa [Scheme.Hom.range_fiberι]
  have hsp : f.asFiber η ⤳ b := by
    rw [← (f.fiberι (f η)).isEmbedding.specializes_iff, Scheme.Hom.fiberι_asFiber]
    exact genericPoint_specializes _
  rw [Set.mem_singleton_iff.mp (hsp.mem_closed hcl rfl), Scheme.Hom.fiberι_asFiber]

/-- A dominant morphism from an irreducible scheme maps the generic point to a generic point of
the target. -/
private theorem isGenericPoint_map_genericPoint {X S : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ S) [IsDominant f] : IsGenericPoint (f (genericPoint X)) (Set.univ : Set S) := by
  rw [IsGenericPoint, ← MMP.Flips.closure_range_eq_closure_genericPoint f,
    f.denseRange.closure_range]

/-- Functoriality of the maps of function fields along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_functionFieldMap {A B C : Scheme.{u}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    [IsDominant (a ≫ b)] (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap (a ≫ b) t := by
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact (congrArg (fun φ => φ.hom t) this).symm

/-- The normalization of a quasi-compact morphism from the spectrum of the function field of `Y`
to a Nagata scheme over `Y`, compatible with the generic point of `Y`, is finite. -/
private theorem isFinite_fromNormalization_of_comp_eq {Y T : Scheme.{u}} [IsIntegral Y]
    (g : Spec Y.functionField ⟶ T) [QuasiCompact g] [QuasiSeparated g] (hT : IsNagataScheme T)
    (f : T ⟶ Y) (hgf : g ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    IsFinite g.fromNormalization := by
  have : Finite (Spec Y.functionField) :=
    inferInstanceAs (Finite (PrimeSpectrum Y.functionField))
  refine isFinite_fromNormalization g hT
    (fun U _ => have : Finite U := Subtype.finite
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) fun x => ?_
  let := (g.residueFieldMap x.1).hom.toAlgebra
  have hsurj : Function.Surjective (g.residueFieldMap x.1).hom := by
    have h := surjective_residueFieldMap_of_surjectiveOnStalks
      (Y.fromSpecStalk (genericPoint Y)) x.1
    rw [Scheme.Hom.residueFieldMap_congr hgf.symm, Scheme.residueFieldMap_comp] at h
    exact fun z => ⟨_, (h z).choose_spec⟩
  have : Algebra.EssFiniteType (T.residueField (g x.1))
      ((Spec Y.functionField).residueField x.1) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  exact IntermediateField.fg_top _ _

/-- A dominant morphism `p` through which the generic point `Spec k(Y) ⟶ Y` factors is
birational. -/
private theorem isBirational_of_comp_eq_fromSpecStalk {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] (j : Spec Y.functionField ⟶ V) (p : V ⟶ Y) [IsDominant j] [IsDominant p]
    (hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y)) : IsBirational p := by
  letI := isDominant_fromSpecStalk_genericPoint Y
  have : IsDominant (j ≫ p) := by
    rw [hjp]
    infer_instance
  refine isBirational_of_surjective_functionFieldMap _ fun w => ?_
  have hbij : Function.Bijective (functionFieldMap (j ≫ p)) := by
    rw! (castMode := .all) [hjp]
    exact bijective_functionFieldMap_fromSpecStalk_genericPoint Y
  obtain ⟨a, ha⟩ := hbij.2 (functionFieldMap j w)
  rw [← functionFieldMap_functionFieldMap j p] at ha
  exact ⟨a, (functionFieldMap j).injective ha⟩

/-- If `p ≫ h = q ≫ h'` with `h, h'` birational and `p` maps the generic point to the generic
point, then so does `q`. -/
private theorem map_genericPoint_eq_of_comp_eq {V Y Y' Z : Scheme.{u}} [IsIntegral V]
    [IsIntegral Y] [IsIntegral Y'] {p : V ⟶ Y} {q : V ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z}
    [LocallyOfFiniteType h'] (hpq : p ≫ h = q ≫ h') (hh : IsBirationalMorphism h)
    (hh' : IsBirationalMorphism h') (hpη : p (genericPoint V) = genericPoint Y) :
    q (genericPoint V) = genericPoint Y' := by
  refine eq_genericPoint_of_map_eq h' (isIso_stalkMap_genericPoint h' hh') ?_
  haveI := hh.isDominant
  haveI := hh'.isDominant
  have e1 : h' (q (genericPoint V)) = h (genericPoint Y) := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hpη]
  rw [e1]
  exact (isGenericPoint_map_genericPoint h).eq (isGenericPoint_map_genericPoint h')

/-- If `p ≫ h = q ≫ h'` and `p`, `h`, `h'` induce isomorphisms of local rings at the relevant
points, then so does `q`. -/
private theorem isIso_stalkMap_of_comp_eq {V Y Y' Z : Scheme.{u}} {p : V ⟶ Y} {q : V ⟶ Y'}
    {h : Y ⟶ Z} {h' : Y' ⟶ Z} (hpq : p ≫ h = q ≫ h') (x : V) (hp : IsIso (p.stalkMap x))
    (hh : IsIso (h.stalkMap (p x))) (hh' : IsIso (h'.stalkMap (q x))) :
    IsIso (q.stalkMap x) := by
  have e := Scheme.Hom.stalkMap_congr_hom (q ≫ h') (p ≫ h) hpq.symm x
  have hpc : IsIso ((p ≫ h).stalkMap x) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hh hp
  have hR : IsIso ((q ≫ h').stalkMap x) := by
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hpc
  rw [Scheme.Hom.stalkMap_comp] at hR
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (h'.stalkMap (q x)) _ hh' hR

/-- If `p ≫ h = q ≫ h'` with `h, h'` birational morphisms and `p` birational, mapping the generic
point to the generic point, then `q` is birational. -/
private theorem isBirational_of_comp_eq {V Y Y' Z : Scheme.{u}} [IsIntegral V] [IsIntegral Y]
    [IsIntegral Y'] {p : V ⟶ Y} {q : V ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z}
    [LocallyOfFiniteType h'] (hpq : p ≫ h = q ≫ h') (hh : IsBirationalMorphism h)
    (hh' : IsBirationalMorphism h') (hpB : IsBirational p)
    (hpη : p (genericPoint V) = genericPoint Y) : IsBirational q := by
  have hqη := map_genericPoint_eq_of_comp_eq hpq hh hh' hpη
  refine isBirational_of_bijOn_of_isIso_stalkMap q ?_ fun x hx => ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hqη
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    refine isIso_stalkMap_of_comp_eq hpq _ (hpB.2 _ (by rw [genericPoints_eq_singleton]; rfl))
      ?_ ?_
    · rw [hpη]
      exact isIso_stalkMap_genericPoint h hh
    · rw [hqη]
      exact isIso_stalkMap_genericPoint h' hh'

/-- **The normalized graph.** For proper birational morphisms `h : Y ⟶ Z`, `h' : Y' ⟶ Z` from
normal varieties over `k` and the map `ψ : Y ⤏ Y'` over `Z`, the normalization `V` of the closure
of the graph of `ψ` in `Y ×_Z Y'` is a normal variety with proper birational projections
`p : V ⟶ Y`, `q : V ⟶ Y'` and `p ≫ h = q ≫ h'`; its generic point `j : Spec k(Y) ⟶ V` lies over
the generic point of `Y` and over `ψ`. -/
private theorem exists_normalizedGraph {k : Type u} [Field k] {Y Y' Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (hY' : IsNormalVariety k sY') {h : Y ⟶ Z} {h' : Y' ⟶ Z}
    [IsProper h] [IsProper h']
    (hh : IsBirationalMorphism h) (hh' : IsBirationalMorphism h')
    {ψ : Y.RationalMap Y'} (hψ : MMP.Flips.RationalMap.IsOver h h' ψ) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    ∃ (V : Scheme.{u}) (p : V ⟶ Y) (q : V ⟶ Y') (j : Spec Y.functionField ⟶ V),
      IsNormalVariety k (p ≫ sY) ∧ p ≫ h = q ≫ h' ∧ IsProper p ∧ IsProper q ∧
      IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
      j ≫ p = Y.fromSpecStalk (genericPoint Y) ∧ j ≫ q = ψ.fromFunctionField := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral Y' := hY'.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  have hcond : ψ.fromFunctionField ≫ h' = Y.fromSpecStalk (genericPoint Y) ≫ h := by
    rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hψ,
      MMP.Flips.RationalMap.fromFunctionField_hom]
  let gp : Spec Y.functionField ⟶ Limits.pullback h' h := Limits.pullback.lift _ _ hcond
  haveI : QuasiCompact gp := quasiCompact_of_isField (Field.toIsField _) _
  haveI : QuasiSeparated gp := QuasiSeparated.of_quasiSeparatedSpace _
  have hgfst : gp ≫ Limits.pullback.fst h' h = ψ.fromFunctionField :=
    Limits.pullback.lift_fst _ _ _
  have hgsnd : gp ≫ Limits.pullback.snd h' h = Y.fromSpecStalk (genericPoint Y) :=
    Limits.pullback.lift_snd _ _ _
  have hjν : gp.toNormalization ≫ gp.fromNormalization = gp :=
    Scheme.Hom.toNormalization_fromNormalization gp
  haveI : IsFinite gp.fromNormalization := isFinite_fromNormalization_of_comp_eq gp
    (isNagataScheme_of_locallyOfFiniteType (Limits.pullback.snd h' h ≫ sY)
      (isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_field)) _ hgsnd
  haveI : IsNormal gp.normalization :=
    isNormal_normalization_of_isField (Field.toIsField _) _
  set V := gp.normalization
  set j := gp.toNormalization
  set p : V ⟶ Y := gp.fromNormalization ≫ Limits.pullback.snd h' h with hp_def
  set q : V ⟶ Y' := gp.fromNormalization ≫ Limits.pullback.fst h' h with hq_def
  have hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y) := by
    rw [hp_def, ← Category.assoc, hjν, hgsnd]
  have hjq : j ≫ q = ψ.fromFunctionField := by
    rw [hq_def, ← Category.assoc, hjν, hgfst]
  have hpq : p ≫ h = q ≫ h' := by
    simp only [hp_def, hq_def, Category.assoc, Limits.pullback.condition]
  haveI : IsProper p := by
    rw [hp_def]
    infer_instance
  haveI : IsProper q := by
    rw [hq_def]
    infer_instance
  letI := isDominant_fromSpecStalk_genericPoint Y
  have : IsDominant (j ≫ p) := by
    rw [hjp]
    infer_instance
  haveI : IsDominant p := IsDominant.of_comp j _
  have hpB := isBirational_of_comp_eq_fromSpecStalk j p hjp
  have hqB := isBirational_of_comp_eq hpq hh hh' hpB (map_genericPoint_of_isDominant p)
  have hV : IsNormalVariety k (p ≫ sY) :=
    ⟨(MMP.Mori.isVariety_iff k (p ≫ sY)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨V, p, q, j, hV, hpq, inferInstance, inferInstance,
    isBirationalMorphism_of_isBirational p hpB, isBirationalMorphism_of_isBirational q hqB,
    hjp, hjq⟩

end Graph

section Coefficients

/-- In an integral scheme, a point has coheight zero iff it is the generic point. -/
private theorem coheight_eq_zero_iff_eq_genericPoint {X : Scheme.{u}} [IrreducibleSpace X]
    (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  refine ⟨fun h ↦ Specializes.antisymm (Order.coheight_eq_zero.mp h (genericPoint_specializes x))
    (genericPoint_specializes x) |>.eq, ?_⟩
  rintro rfl
  exact Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z

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

/-- A prime divisor `F` of `Y` which is not exceptional over the normal variety `X` maps to a
point of coheight at most one. -/
private theorem coheight_lt_two_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) (hF : ¬ IsExceptionalPrimeDivisor sX g F) :
    Order.coheight (g F.genericPoint) < 2 := by
  by_contra h2
  rw [not_lt] at h2
  refine hF ⟨hY, hg, inferInstance, ?_⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  exact (withBot_add_two_le_iff hd).mpr h2

/-- A prime divisor `F` of `Y` which is not exceptional over the normal variety `X` maps to a
point of coheight exactly one. -/
private theorem coheight_eq_one_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (g : Y ⟶ X) (hY : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) [IsProper g] (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ IsExceptionalPrimeDivisor sX g F) : Order.coheight (g F.genericPoint) = 1 := by
  haveI : IsDominant g := hg.isDominant
  have hne : g F.genericPoint ≠ genericPoint X := by
    intro h0
    have h1 : F.genericPoint = genericPoint Y := eq_genericPoint_of_map_eq g
      (isIso_stalkMap_genericPoint g hg) (h0.trans (map_genericPoint_of_isDominant g).symm)
    have h2 := F.coheight_genericPoint
    rw [h1, (coheight_eq_zero_iff_eq_genericPoint _).mpr rfl] at h2
    exact zero_ne_one h2
  exact le_antisymm
    (Order.le_of_lt_add_one (coheight_lt_two_of_not_isExceptionalPrimeDivisor hX g hY hg F hF))
    (ENat.one_le_iff_ne_zero.mpr fun h0 => hne ((coheight_eq_zero_iff_eq_genericPoint _).mp h0))

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
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
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ,
    TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- A representative of `φ` defined at the generic point of `P` maps it to the generic point of
`φ_*P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}}
    [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- Morphisms from the spectrum of a domain `R` to an affine scheme agree once they agree on the
spectrum of its fraction field. -/
private theorem spec_hom_ext_of_isFractionRing {R K : Type u} [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] {A : CommRingCat.{u}}
    {a b : Spec (.of R) ⟶ Spec A}
    (hab : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b) : a = b := by
  obtain ⟨a', rfl⟩ : ∃ a', Spec.map a' = a := ⟨_, Spec.map_preimage a⟩
  obtain ⟨b', rfl⟩ : ∃ b', Spec.map b' = b := ⟨_, Spec.map_preimage b⟩
  rw [← Spec.map_comp, ← Spec.map_comp] at hab
  have h'' := Spec.map_injective hab
  congr 1
  ext c
  exact IsFractionRing.injective R K (congrArg (fun r => r.hom c) h'')

/-- The canonical map `Spec 𝒪_{X,x} ⟶ U` sends the closed point to `x`. -/
private theorem fromSpecStalkOfMem_closedPoint {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hx : x ∈ U) :
    (U.fromSpecStalkOfMem x hx).base (IsLocalRing.closedPoint (X.presheaf.stalk x)) =
      ⟨x, hx⟩ := by
  apply Subtype.ext
  have := congrArg (fun φ : Spec (X.presheaf.stalk x) ⟶ X =>
    φ.base (IsLocalRing.closedPoint (X.presheaf.stalk x))) (U.fromSpecStalkOfMem_ι x hx)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.fromSpecStalk_closedPoint] at this
  exact this

/-- **A point of the graph over a codimension-one point.** In the normalized graph `V` of
`ψ : Y ⤏ Y'`, with `j : Spec k(Y) ⟶ V` over the generic point of `Y` and over `ψ`, let `P` be a
prime divisor of `Y` with `ψ_*P = Q'`. Then some point of `V` lies over `η_P` and over
`η_{Q'}`. -/
private theorem exists_map_eq_genericPoint {k : Type u} [Field k] {Y Y' V : Scheme.{u}}
    {sY' : Y' ⟶ Spec (.of k)} [IsSeparated sY'] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {ψ : Y.RationalMap Y'} (p : V ⟶ Y) (q : V ⟶ Y') [IsProper p]
    (j : Spec Y.functionField ⟶ V) (hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y))
    (hjq : j ≫ q = ψ.fromFunctionField) {P : MMP.Mori.PrimeDivisor Y}
    {Q' : MMP.Mori.PrimeDivisor Y'}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some Q') :
    ∃ x : V, p x = P.genericPoint ∧ q x = Q'.genericPoint := by
  have : IsSeparated (Y' ↘ ⊤_ Scheme) := by
    rw [show (Y' ↘ ⊤_ Scheme) = sY' ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨g, hgP, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hP).1
  have hgQ := genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hgP
  set R := Y.presheaf.stalk P.genericPoint
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing R := inferInstance
  have hgen : genericPoint Y ⤳ P.genericPoint := (genericPoint_spec Y).specializes trivial
  have hsq0 : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫
      Y.fromSpecStalk P.genericPoint = Y.fromSpecStalk (genericPoint Y) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen
  have hex : ValuativeCriterion.Existence p := by
    have h : @IsProper _ _ p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq p :=
    { R := R
      domain := inferInstance
      K := Y.functionField
      i₁ := j
      i₂ := Y.fromSpecStalk P.genericPoint
      commSq := ⟨by rw [hjp, hsq0]⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l = j := hl₁
  have hl₂' : l ≫ p = Y.fromSpecStalk P.genericPoint := hl₂
  refine ⟨l (IsLocalRing.closedPoint R), ?_, ?_⟩
  · change (l ≫ p) _ = _
    rw [hl₂', Scheme.fromSpecStalk_closedPoint]
  -- the extension of `ψ` to `Spec 𝒪_{Y,P}`
  have hηg : genericPoint Y ∈ g.domain :=
    hgen.mem_open g.domain.isOpen hgP
  let m := g.fromSpecStalkOfMem hgP
  have hm0 : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ m =
      ψ.fromFunctionField := by
    rw [← hg, Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact (MMP.Flips.RationalMap.fromSpecStalkOfMem_specializes g hgen hgP hηg).symm
  have hsep : l ≫ q = m := by
    let S' : ValuativeCommSq sY' :=
      { R := R
        domain := inferInstance
        K := Y.functionField
        i₁ := ψ.fromFunctionField
        i₂ := l ≫ q ≫ sY'
        commSq := ⟨by rw [← Category.assoc, ← Category.assoc, hl₁', hjq]⟩ }
    have hS := IsSeparated.valuativeCriterion sY' S'
    let L : S'.commSq.LiftStruct := ⟨l ≫ q, by rw [← Category.assoc, hl₁', hjq], rfl⟩
    let L' : S'.commSq.LiftStruct := ⟨m, hm0,
      spec_hom_ext_of_isFractionRing (R := R) (K := Y.functionField) (by
        rw [← Category.assoc, hm0, ← Category.assoc, ← Category.assoc, hl₁', hjq])⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  change (l ≫ q) _ = _
  rw [hsep, hgQ]
  change g.hom.base ((g.domain.fromSpecStalkOfMem P.genericPoint hgP).base
    (IsLocalRing.closedPoint (Y.presheaf.stalk P.genericPoint))) = _
  rw [fromSpecStalkOfMem_closedPoint]

/-- **Coefficients along a prime divisor of the graph not exceptional over `Y'`.** In the setting
of the normalized graph `p : V ⟶ Y`, `q : V ⟶ Y'` of `ψ = h'⁻¹ ∘ h`, a prime divisor `E` of `V`
not exceptional over `Y'` lies over a prime divisor `Q'` of `Y'`, which is `ψ_*P` for a prime
divisor `P` of `Y` over which `E` also lies. So the coefficient along `E` of the pull-back of a
Cartier divisor is its coefficient along `Q'`, resp. `P`, and the coefficient of `ψ_*D` along `Q'`
is that of `D` along `P`. -/
private theorem exists_coeff_pullback_eq {k : Type u} [Field k] {Y Y' V : Scheme.{u}}
    {sY' : Y' ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (hY' : IsNormalVariety k sY') {ψ : Y.RationalMap Y'}
    (hψP : ∀ P' : MMP.Mori.PrimeDivisor Y', ∃ P : MMP.Mori.PrimeDivisor Y,
      MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some P')
    (p : V ⟶ Y) (q : V ⟶ Y') (hV : IsNormalVariety k (q ≫ sY')) [IsProper p] [IsProper q]
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (j : Spec Y.functionField ⟶ V) (hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y))
    (hjq : j ≫ q = ψ.fromFunctionField)
    (E : MMP.Mori.PrimeDivisor V) (hE : ¬ IsExceptionalPrimeDivisor sY' q E) :
    ∃ (Q' : MMP.Mori.PrimeDivisor Y') (P : MMP.Mori.PrimeDivisor Y),
      (∀ (L : Divisor Y') (hL : L.IsCartier)
          (hB : ∀ W : irreducibleComponents V, q (componentGenericPoint V W) ∉ L.supp),
          (L.pullback hL hB).coeff E = L.coeff Q') ∧
      (∀ (M : Divisor Y) (hM : M.IsCartier)
          (hB : ∀ W : irreducibleComponents V, p (componentGenericPoint V W) ∉ M.supp),
          (M.pullback hM hB).coeff E = M.coeff P) ∧
      ∀ D : RDivisor Y, (MMP.Mori.RationalMap.transformDivisor ψ D).coeff Q' = D.coeff P := by
  classical
  haveI : IsSeparated sY' := hY'.1.toIsSeparated
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  have hbp := hp.functionFieldMap_bijective
  have hbq := hq.functionFieldMap_bijective
  -- `E` lies over a prime divisor `Q'` of `Y'`
  have h1 := coheight_eq_one_of_not_isExceptionalPrimeDivisor hY' q hV hq E hE
  let Q' : MMP.Mori.PrimeDivisor Y' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hQ' : q E.genericPoint = Q'.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm
  have := Q'.isDiscreteValuationRing_localRing
  have hvq : ValuationRing (Y'.presheaf.stalk (q E.genericPoint)) := by
    rw [hQ']
    infer_instance
  have hqE := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbq E.genericPoint
  -- every `P` with `ψ_*P = Q'` lies under `E`
  have hunder : ∀ P : MMP.Mori.PrimeDivisor Y,
      MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some Q' →
        p E.genericPoint = P.genericPoint := by
    intro P hP
    obtain ⟨x, hxp, hxq⟩ := exists_map_eq_genericPoint (sY' := sY') p q j hjp hjq hP
    have hvx : ValuationRing (Y'.presheaf.stalk (q x)) := by
      rw [hxq]
      infer_instance
    have hqx := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbq x
    rw [MMP.Positivity.eq_of_isIso_stalkMap q hbq (x₁ := E.genericPoint) (x₂ := x)
      (hxq.trans hQ'.symm), hxp]
  obtain ⟨P, hP⟩ := hψP Q'
  have hpE := hunder P hP
  have := P.isDiscreteValuationRing_localRing
  have hvp : ValuationRing (Y.presheaf.stalk (p E.genericPoint)) := by
    rw [hpE]
    infer_instance
  have hpEi := MMP.Positivity.isIso_stalkMap_of_valuationRing p hbp E.genericPoint
  refine ⟨Q', P, fun L hL hB => ?_, fun M hM hB => ?_, fun D => ?_⟩
  · exact MMP.Positivity.coeff_eq_of_isPullback E Q' hQ' hL (Divisor.isPullback_pullback hL hB)
  · exact MMP.Positivity.coeff_eq_of_isPullback E P hpE hM (Divisor.isPullback_pullback hM hB)
  · refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP (fun P₂ hP₂ => ?_) D
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hunder P₂ hP₂).symm.trans hpE)

end Coefficients

section Negativity

variable {k : Type u} [Field k]

/-- **Projection formula for a combination of pull-backs.** On a proper curve `C ⊆ X` whose image
under `f` is the proper curve `C₀`, `(∑ r_j f^*L_j) · C = [k(C) : k(C₀)] · (∑ r_j L_j) · C₀`. -/
private theorem sum_degreeOn_pullback_eq_mul {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (hf : f ≫ sY = sX) {m : ℕ} (r : Fin m → ℝ) {L : Fin m → Divisor Y}
    (hL : ∀ j, (L j).IsCartier)
    (hB : ∀ j, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (L j).supp)
    (C : ProperCurve sX) (C₀ : ProperCurve sY) (hC : C₀.point = f C.point) :
    ∑ j, r j * (((L j).pullback (hL j) (hB j)).degreeOn k sX C.ι C.dim_le
        ((hL j).isCartier_pullback f (hB j)) : ℝ) =
      residueFieldDegree f C.point *
        ∑ j, r j * ((L j).degreeOn k sY C₀.ι C₀.dim_le (hL j) : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [degreeOn_pullback_eq_mul f hf (hL j) (hB j) C C₀ hC]
  push_cast
  ring

/-- **Pull-backs of numerically trivial divisors.** If `G = ∑ s_i M_i` is numerically trivial over
`h : Y ⟶ Z`, then `f^*G · C = 0` for every proper curve `C ⊆ X` contracted by `f ≫ h`. -/
private theorem sum_degreeOn_pullback_eq_zero {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (h : Y ⟶ Z) {m : ℕ} (s : Fin m → ℝ)
    {M : Fin m → Divisor Y} (hM : ∀ i, (M i).IsCartier)
    (hB : ∀ i, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (M i).supp)
    (hG : IsNumericallyTrivialOver k sY h (∑ i, s i • Divisor.toRDivisor (M i)))
    (C : ProperCurve sX) (hC : C.IsContractedBy (f ≫ h)) :
    ∑ i, s i * (((M i).pullback (hM i) (hB i)).degreeOn k sX C.ι C.dim_le
        ((hM i).isCartier_pullback f (hB i)) : ℝ) = 0 := by
  by_cases hc : IsProperCurve sY (f C.point)
  · let C₀ : ProperCurve sY := ⟨_, hc⟩
    rw [sum_degreeOn_pullback_eq_mul f hf s hM hB C C₀ rfl,
      hG.2.2 C₀ (isContractedBy_of_comp f h C hC C₀ rfl) m s M _ 0 Fin.elim0 Fin.elim0 0
        (isRIntersectionNumber_sum_degreeOn k sY C₀ s M hM)
        ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩, mul_zero]
  · exact Finset.sum_eq_zero fun i _ => by
      rw [degreeOn_pullback_eq_zero f hf (hM i) (hB i) C hc, Int.cast_zero, mul_zero]

/-- **A numerically trivial divisor with trivial push-forward vanishes.** Let `q : V ⟶ Y'` be a
proper birational morphism of normal varieties and `F = ∑ R_t L_t` an `ℝ`-Cartier divisor on `V`
whose coefficients along the prime divisors not exceptional over `Y'` vanish, with `F · C = 0` for
every curve `C` contracted by `q`. Then `F = 0`. -/
private theorem sum_smul_toRDivisor_eq_zero {Y' V : Scheme.{u}} (sY' : Y' ⟶ Spec (.of k))
    (sV : V ⟶ Spec (.of k)) [QuasiCompact sV] [IsLocallyNoetherian Y'] [IsNormal Y']
    [IsLocallyNoetherian V] [IsNormal V] (hY' : IsNormalVariety k sY') (hV : IsNormalVariety k sV)
    (q : V ⟶ Y') (hqs : q ≫ sY' = sV) [IsProper q] (hq : IsBirationalMorphism q) {n : ℕ}
    (R : Fin n → ℝ) (L : Fin n → Divisor V) (hL : ∀ t, (L t).IsCartier)
    (hcoeff : ∀ E : MMP.Mori.PrimeDivisor V, ¬ IsExceptionalPrimeDivisor sY' q E →
      (∑ t, R t • Divisor.toRDivisor (L t)).coeff E = 0)
    (hdeg : ∀ C : ProperCurve sV, C.IsContractedBy q →
      ∑ t, R t * ((L t).degreeOn k sV C.ι C.dim_le (hL t) : ℝ) = 0) :
    ∑ t, R t • Divisor.toRDivisor (L t) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sV
  set F := ∑ t, R t • Divisor.toRDivisor (L t)
  have hpres (c : ℝ) : c • F = ∑ t, (c * R t) • Divisor.toRDivisor (L t) := by
    simp only [F, Finset.smul_sum, smul_smul]
  have hzc : IsCartierCombination (0 : RDivisor V) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have heff (c : ℝ) : (c • F).IsEffective := by
    have hBc : IsCartierCombination (c • F) :=
      ⟨n, _, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hpres c⟩
    refine isEffective_of_isNumericallyEquivalentOver_pullback k sY' sV hY' hV q hqs hq
      (L := 0) ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩ (L' := 0)
      ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0,
        by simp⟩ hzc
      ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun C _ x hx => by
        rw [eq_zero_of_isRIntersectionNumber_zero k sV hx]⟩ hBc
      (fun E hE => by
        rw [DivisorWithCoeffs.coeff_smul, hcoeff E hE, smul_zero]) ⟨hzc, by rwa [zero_add],
        fun C hC _ _ _ _ _ _ _ _ h₁ h₂ => ?_⟩
    obtain ⟨hL₂, hD₂, hx₂⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sV h₂
    rw [zero_add, hpres c] at hD₂
    rw [eq_zero_of_isRIntersectionNumber_zero k sV h₁, hx₂,
      ← sum_degreeOn_eq_of_sum_eq k sV C hL hL₂ hD₂]
    simp_rw [mul_assoc, ← Finset.mul_sum, hdeg C hC, mul_zero]
  ext E
  have h1 := heff 1 E
  have h2 := heff (-1) E
  simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1 h2
  rw [DivisorWithCoeffs.coeff_zero]
  linarith

end Negativity

end Proof_lem_fa18_numerically_trivial_transform

namespace MMP.Flips

open Proof_lem_fa18_numerically_trivial_transform

open MMP.Mori

/-- **Birational transforms of numerically trivial divisors** (FA, Chapter 18). Let
`h : Y ⟶ Z`, `h' : Y' ⟶ Z` be proper birational morphisms from normal varieties over a field `k`,
with `Y'` `ℚ`-factorial, and let `ψ : Y ⤏ Y'` be the rational map
`h'⁻¹ ∘ h` (that is, `h' ∘ ψ = h`). Suppose every prime divisor of `Y'` is the birational
transform under `ψ` of a prime divisor of `Y`. If `G` is an `ℝ`-Cartier divisor on `Y` with
`G ≡_h 0`, then `ψ_*G` is `ℝ`-Cartier and `ψ_*G ≡_{h'} 0`. -/
@[mmp "lem_fa18_numerically_trivial_transform"]
public theorem IsNumericallyTrivialOver.transformDivisor_of_isOver
    {k : Type u} [Field k] {Y Y' Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    {sY : Y ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)} [QuasiCompact sY] [QuasiCompact sY']
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hY : IsNormalVariety k sY) (hY' : MMP.Fourfold.IsQFactorial sY')
    {h : Y ⟶ Z} {h' : Y' ⟶ Z} (hsY : h ≫ sZ = sY) (hsY' : h' ≫ sZ = sY')
    [IsProper h] [IsProper h'] (hh : IsBirationalMorphism h) (hh' : IsBirationalMorphism h')
    {ψ : Y.RationalMap Y'} (hψ : RationalMap.IsOver h h' ψ)
    (hψP : ∀ P' : Mori.PrimeDivisor Y', ∃ P : Mori.PrimeDivisor Y,
      Mori.RationalMap.transformPrimeDivisor ψ P = some P')
    {G : RDivisor Y} (hGc : IsCartierCombination G) (hG : IsNumericallyTrivialOver k sY h G) :
    IsCartierCombination (Mori.RationalMap.transformDivisor ψ G) ∧
      IsNumericallyTrivialOver k sY' h' (Mori.RationalMap.transformDivisor ψ G) := by
  classical
  have hY'n : IsNormalVariety k sY' := hY'.1
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral Y' := hY'n.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sY' := hY'n.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated sY' := hY'n.1.toIsSeparated
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace sY'
  obtain ⟨V, p, q, j, hV, hpq, hpP, hqP, hp, hq, hjp, hjq⟩ :=
    exists_normalizedGraph hY hY'n hh hh' hψ
  have hqs : q ≫ sY' = p ≫ sY := by
    rw [← hsY', ← hsY, ← Category.assoc, ← Category.assoc, hpq]
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sY) := hV.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sY) := hV.1.toQuasiCompact
  haveI : IsNormal V := hV.2
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sY)
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  -- presentations of `G` and of `ψ_*G`
  obtain ⟨m, s, M, hM, hGeq⟩ := hGc
  have hGeq' : G = ∑ i, s i • Divisor.toRDivisor (M i) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hGeq
  have hD'c := isCartierCombination_of_isQFactorial hY'
    (MMP.Mori.RationalMap.transformDivisor ψ G)
  obtain ⟨n, r, L, hL, hDeq⟩ := id hD'c
  have hDeq' : MMP.Mori.RationalMap.transformDivisor ψ G =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hDeq
  -- the pull-backs `p^*G` and `q^*ψ_*G`
  have hBp : ∀ i, ∀ W : irreducibleComponents V, p (componentGenericPoint V W) ∉ (M i).supp :=
    fun i => map_componentGenericPoint_notMem_supp_of_isDominant p (M i)
  have hBq : ∀ j, ∀ W : irreducibleComponents V, q (componentGenericPoint V W) ∉ (L j).supp :=
    fun j => map_componentGenericPoint_notMem_supp_of_isDominant q (L j)
  let Mp : Fin m → Divisor V := fun i => (M i).pullback (hM i) (hBp i)
  let Lq : Fin n → Divisor V := fun j => (L j).pullback (hL j) (hBq j)
  have hMp : ∀ i, (Mp i).IsCartier := fun i => (hM i).isCartier_pullback p (hBp i)
  have hLq : ∀ j, (Lq j).IsCartier := fun j => (hL j).isCartier_pullback q (hBq j)
  let Gp : RDivisor V := ∑ i, s i • Divisor.toRDivisor (Mp i)
  let Dq : RDivisor V := ∑ j, r j • Divisor.toRDivisor (Lq j)
  have hK := sum_degreeOn_pullback_eq_zero p rfl h s hM hBp (hGeq' ▸ hG)
  -- `q^*ψ_*G = p^*G`, by the negativity lemma applied to their difference
  let R : Fin (n + m) → ℝ := Fin.append r fun i => -s i
  let LL : Fin (n + m) → Divisor V := Fin.append Lq Mp
  have hLL : ∀ t, (LL t).IsCartier := fun t =>
    Fin.addCases (motive := fun t => (LL t).IsCartier)
      (fun j => by simpa [LL] using hLq j) (fun i => by simpa [LL] using hMp i) t
  have hpres : Dq - Gp = ∑ t, R t • Divisor.toRDivisor (LL t) := by
    simp only [R, LL, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Dq, Gp, neg_smul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hF : Dq = Gp := by
    refine sub_eq_zero.mp (hpres ▸ sum_smul_toRDivisor_eq_zero sY' (p ≫ sY) hY'n hV q hqs hq
      R LL hLL (fun E hE => ?_) fun C hC => ?_)
    · obtain ⟨Q', P, hQ', hP, hψE⟩ := exists_coeff_pullback_eq hY'n hψP p q
        (by rw [hqs]; exact hV) hp hq j hjp hjq E hE
      have h1 : Dq.coeff E = Gp.coeff E := by
        simp only [Dq, Gp, coeff_sum_smul_toRDivisor, Lq, Mp, hQ', hP]
        rw [← coeff_sum_smul_toRDivisor, ← coeff_sum_smul_toRDivisor, ← hDeq', ← hGeq', hψE]
      rw [← hpres, DivisorWithCoeffs.coeff_sub, h1, sub_self]
    · have hCc : C.IsContractedBy (p ≫ h) := by
        rw [hpq]
        exact isContractedBy_comp q h' C hC
      simp only [R, LL, Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_mul,
        Finset.sum_neg_distrib]
      rw [Finset.sum_eq_zero fun j _ => ?_, zero_add, neg_eq_zero]
      · exact hK C hCc
      · rw [Divisor.degreeOn_pullback_eq_zero_of_isContractedBy q hqs (hL j) (hBq j) C hC,
          Int.cast_zero, mul_zero]
  -- `ψ_*G ≡_{h'} 0`
  refine ⟨hD'c, hD'c, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C' hC' m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [eq_zero_of_isRIntersectionNumber_zero k sY' h₂]
  obtain ⟨hL₁, hD₁, hx₁⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sY' h₁
  haveI : Surjective q := ⟨by
    have h1 : Set.range q = Set.univ := by
      rw [← q.isClosedMap.isClosed_range.closure_eq, q.denseRange.closure_range]
    exact fun y => h1.ge (Set.mem_univ y)⟩
  obtain ⟨C, hC⟩ := ProperCurve.exists_map_point_eq (p ≫ sY) sY' q hqs C'
  have hB₁ : ∀ j, ∀ W : irreducibleComponents V, q (componentGenericPoint V W) ∉ (L₁ j).supp :=
    fun j => map_componentGenericPoint_notMem_supp_of_isDominant q (L₁ j)
  have hpb : ∑ j, r₁ j • Divisor.toRDivisor ((L₁ j).pullback (hL₁ j) (hB₁ j)) = Dq :=
    IsRCartierPullback.eq q
      ⟨m₁, r₁, L₁, _, hL₁, hD₁, fun j => ⟨hB₁ j, Divisor.isPullback_pullback _ _⟩, rfl⟩
      ⟨n, r, L, Lq, hL, hDeq', fun j => ⟨hBq j, Divisor.isPullback_pullback _ _⟩, rfl⟩
  have hsum := sum_degreeOn_eq_of_sum_eq k (p ≫ sY) C
    (fun j => (hL₁ j).isCartier_pullback q (hB₁ j)) hMp (hpb.trans hF)
  rw [sum_degreeOn_pullback_eq_mul q hqs r₁ hL₁ hB₁ C C' hC.symm,
    hK C (by rw [hpq]; exact isContractedBy_comp_of_map q h' C C' hC hC')] at hsum
  rw [hx₁]
  exact (mul_eq_zero.mp hsum).resolve_left
    (Nat.cast_ne_zero.mpr (residueFieldDegree_pos_of_map_point q hqs C C' hC).ne')

end MMP.Flips
