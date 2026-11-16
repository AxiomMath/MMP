module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic

/-!
# Null and exceptional divisors under proper birational morphisms

Two consequences of the negativity lemma for `ℚ`-Cartier `ℚ`-divisors
(`MMP.Mori.QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg`).

An effective `ℚ`-Cartier divisor supported on the exceptional prime divisors of a proper
birational morphism `g : X' ⟶ X` of normal varieties is never `g`-nef unless it is zero: its
pushforward vanishes, so the negativity lemma applied to `-G` makes `-G` effective.

Let `Y`, `Z` be normal `ℚ`-factorial projective varieties over a base `S` with a common
resolution `p : W ⟶ Y`, `q : W ⟶ Z`, and nef adjoints `L_Y`, `L_Z` whose pull-backs have the same
zero-degree curves over `S`. A `ℚ`-Cartier divisor `H` on `Y` null on the `L_Y`-trivial curves
descends: `H_Z = q_* p^* H` is `ℚ`-Cartier with `p^* H = q^* H_Z`, and `H_Z` is nef over `S`
whenever `H` is. The difference `p^*H - q^*H_Z` is `q`-exceptional and numerically trivial over
`Z`, so the negativity lemma applied to it and to its negative makes it zero.

## Main results

* `MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef`: an effective exceptional
  `g`-nef divisor is zero.
* `MMP.Fourfold.isQCartier_and_isPullback_transformDivisor_of_null`: numerical descent of a
  null divisor across a common resolution.
* `MMP.Flips.exists_isCartierIntersectionNumber`,
  `MMP.Flips.IsCartierIntersectionNumber.eq_degreeOn`: every Cartier divisor has an
  intersection number with a proper curve, and it is the degree `MMP.Mori.Divisor.degreeOn`
  along the curve.
* `MMP.Flips.IsNumericallyTrivialOver.degree_eq_zero`: a Cartier multiple of a numerically
  `f`-trivial `ℚ`-divisor has degree zero on every curve contracted by `f`.

## Implementation notes

Relative nefness of a `ℚ`-divisor is `MMP.Mori.QDivisor.IsRelativelyNef`; the pull-backs of the
real adjoints are `ℝ`-divisors given with `MMP.Flips.IsRCartierPullback`, and their degrees are
the relation `MMP.Flips.IsRIntersectionNumber`, compared in the proof with
`MMP.Mori.Divisor.degreeOn` through a normalization of the curve. The push-forward `q_*` is the
birational transform `MMP.Mori.RationalMap.transformDivisor`. Each result's auxiliary lemmas live
in a namespace `Proof_<tag>` named after its label, opened only for that result.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of 17.10
-/

@[expose] public section

universe u

open AlgebraicGeometry MMP.Mori in
/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := hD
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

namespace Proof_lem_fa17_effective_exceptional_not_nef

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

/-- A prime divisor of `X'` exceptional over `X` has no transform under `g`. -/
private theorem transformPrimeDivisor_eq_none_of_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) [IsReduced X']
    (g : X' ⟶ X) {P : MMP.Mori.PrimeDivisor X'} (hP : IsExceptionalPrimeDivisor sX g P) :
    RationalMap.transformPrimeDivisor (X := X') g.toRationalMap P = none := by
  have := hX.1.toIsIntegral
  have := hX.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  rcases h : RationalMap.transformPrimeDivisor (X := X') g.toRationalMap P with _ | Q
  · rfl
  exfalso
  have hgQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g P Q).mp h
  obtain ⟨hY, hf, hp, hexc⟩ := hP
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint] at hexc
  change topologicalKrullDim (closure {g P.genericPoint} : Set X) + 2 ≤ _ at hexc
  have hdim := topologicalKrullDim_closure_singleton_add_coheight sX (g P.genericPoint)
  have hn := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX (g P.genericPoint)
  rw [hgQ, Q.coheight_genericPoint] at hdim
  rw [hgQ] at hexc hn
  rw [← hdim, hn] at hexc
  generalize (Stacks.Chow.relativeDimension _ _ _).toNat = m at hexc
  push_cast at hexc
  have := Nat.cast_le.mp (WithBot.coe_le_coe.mp hexc)
  simp only at this
  omega

/-- The pushforward of a divisor supported on the prime divisors exceptional over `X` vanishes. -/
private theorem transformDivisor_eq_zero_of_forall_isExceptionalPrimeDivisor {k : Type u}
    [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    [IsReduced X'] (g : X' ⟶ X) {G : QDivisor X'}
    (hGexc : ∀ P : MMP.Mori.PrimeDivisor X', ¬ IsExceptionalPrimeDivisor sX g P → G.coeff P = 0) :
    RationalMap.transformDivisor (X := X') g.toRationalMap G = 0 := by
  classical
  rw [← Finsupp.sum_single G, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun P hP => ?_
  refine RationalMap.transformDivisor_single_of_eq_none
    (transformPrimeDivisor_eq_none_of_isExceptionalPrimeDivisor sX hX g ?_) _
  by_contra h
  exact Finsupp.mem_support_iff.mp hP (hGexc P h)

end Proof_lem_fa17_effective_exceptional_not_nef

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips
  Proof_lem_fa17_effective_exceptional_not_nef

/-- **An effective exceptional divisor is never relatively nef** (FA, proof of 17.10). Let
`g : X' ⟶ X` be a proper birational morphism of normal varieties over `k`, and `G` a `ℚ`-Cartier
`ℚ`-divisor on `X'` supported on the prime divisors exceptional over `X`. If `G` is effective and
`g`-nef, then `G = 0`. -/
@[mmp "lem_fa17_effective_exceptional_not_nef"]
public theorem QDivisor.eq_zero_of_isEffective_of_isRelativelyNef
    (k : Type u) [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) [QuasiCompact sX'] [IsLocallyNoetherian X'] [IsNormal X']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    (g : X' ⟶ X) (hg : g ≫ sX = sX') [IsProper g] (hgb : IsBirationalMorphism g)
    {G : QDivisor X'} (hG : G.IsQCartier)
    (hGexc : ∀ P : PrimeDivisor X', ¬ IsExceptionalPrimeDivisor sX g P → G.coeff P = 0)
    (hGeff : G.IsEffective) (hnef : G.IsRelativelyNef sX' g) : G = 0 := by
  have := hX'.1.toIsIntegral
  have h := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sX sX' hX hX' g hg hgb (E := -G)
    (isQCartier_neg hG)
    (by rwa [neg_neg])
    (by
      rw [map_neg, transformDivisor_eq_zero_of_forall_isExceptionalPrimeDivisor sX hX g hGexc,
        neg_zero]
      exact DivisorWithCoeffs.isEffective_zero)
  exact le_antisymm (neg_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp h))
    (DivisorWithCoeffs.isEffective_iff_nonneg.mp hGeff)

end MMP.Mori

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry MMP.Mori

/-! ### Intersection numbers of Cartier divisors as degrees along the curve -/

section CartierIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve has more than one point. -/
private theorem not_subsingleton_scheme (C : ProperCurve sX) : ¬ Subsingleton C.scheme := by
  intro _
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine not_subsingleton_scheme C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
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
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν
    ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
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
public theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν)
    ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
public theorem IsCartierIntersectionNumber.eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with every proper curve. -/
public theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, IsCartierIntersectionNumber k sX C L hL d := by
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
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A Cartier multiple `D = m L` of a numerically `f`-trivial `ℚ`-divisor `L` has degree zero
on every proper curve contracted by `f`. -/
public theorem IsNumericallyTrivialOver.degree_eq_zero {Y : Scheme.{u}} {f : X ⟶ Y}
    {L : QDivisor X} (hL : IsNumericallyTrivialOver k sX f (QDivisor.toRDivisor L)) {m : ℕ}
    (hm : 0 < m) {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • L) (hDc : D.IsCartier)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D.divisorialSheaf]
    (C : ProperCurve sX) (hC : C.IsContractedBy f) : C.degree k D.divisorialSheaf = 0 := by
  obtain ⟨d, hd⟩ := exists_isCartierIntersectionNumber C D hDc
  have hm' : (m : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hm.ne')
  have hLD : QDivisor.toRDivisor L = (m : ℝ)⁻¹ • Divisor.toRDivisor D := by
    rw [← QDivisor.toRDivisor_toQDivisor, hD, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul,
      Int.cast_natCast, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  have h := hL.2.2 C hC 1 (fun _ => (m : ℝ)⁻¹) (fun _ => D) ((m : ℝ)⁻¹ * d) 0 Fin.elim0
    Fin.elim0 0 ⟨fun _ => hDc, fun _ => d, by simpa using hLD, fun _ => hd, by simp⟩
    ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
  rw [hd.eq_degreeOn] at h
  exact_mod_cast (mul_eq_zero.mp h).resolve_left hm'

end CartierIntersection

end MMP.Flips

namespace Proof_lem_fourfold_descend_null_divisor_qfactorial

open CategoryTheory AlgebraicGeometry MMP.Mori

/-! ### `ℝ`-intersection numbers as degrees along the curve -/

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => MMP.Flips.exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [(hd j).eq_degreeOn]

/-- `D · C = 0` for every presentation of `D` if and only if one presentation gives
`∑ rⱼ deg_C 𝒪_X(Lⱼ) = 0`. -/
private theorem forall_eq_zero_iff (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    (∀ (m' : ℕ) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sX D r' L' C x → x = 0) ↔
      ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) = 0 := by
  refine ⟨fun h => h _ r L _ (isRIntersectionNumber_sum C r L hL hD), fun h m' r' L' x hx => ?_⟩
  rw [← h]
  exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 D r' L' r L x _ hx
    (isRIntersectionNumber_sum C r L hL hD)

end RIntersection

/-! ### Degrees of pulled-back divisors on curves -/

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_map (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- If `u ≫ π` contracts a curve `Γ` that `u` does not contract, then `π` contracts the image
curve `u(Γ)`. -/
private theorem isContractedBy_map {S : Scheme.{u}} (u : V ⟶ T) (hu : u ≫ sT = sV) (π : T ⟶ S)
    (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) (hΓ : Γ.IsContractedBy (u ≫ π)) :
    (⟨u Γ.point, isProperCurve_map u hu Γ h⟩ : ProperCurve sT).IsContractedBy π := by
  intro y hy
  change y ∈ closure {u Γ.point} at hy
  rw [← ProperCurve.range_comp u hu Γ] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : Γ.ι x ∈ closure {Γ.point} := Γ.range_ι ▸ ⟨x, rfl⟩
  have h1 := hΓ _ hx
  simp only [Scheme.Hom.comp_apply] at h1 ⊢
  exact h1

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

variable [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- The pull-back of a Cartier divisor has degree zero on a contracted curve. -/
private theorem degreeOn_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hD hB Γ hΓ

/-- **Projection formula.** On a curve `Γ` not contracted by `u`, with image the proper curve
`Γ'`, `deg_Γ u^*D = [k(Γ) : k(Γ')] · deg_{Γ'} D`. -/
private theorem degreeOn_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) =
      (residueFieldDegree u Γ.point : ℤ) * D.degreeOn k sT Γ'.ι Γ'.dim_le hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward u hu hD hB Γ, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hΓ' ▸ Γ'.isProperCurve)]
  obtain ⟨pt, hpt⟩ := Γ'
  simp only at hΓ'
  subst hΓ'
  simp [OneCycle.degree, Finsupp.linearCombination_single, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor has intersection number zero with a contracted
curve. -/
private theorem intersectionNumber_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) = 0 := by
  obtain ⟨D, D', hDc, hDB, -, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', degreeOn_isPullback_eq_zero u hu hDc hp Γ hΓ]
  simp

/-- **Projection formula** for `ℚ`-Cartier `ℚ`-divisors:
`(u^*L · Γ) = [k(Γ) : k(Γ')] · (L · Γ')` for the image curve `Γ'` of `Γ`. -/
private theorem intersectionNumber_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV)
    {L : QDivisor T} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hB L') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    L'.intersectionNumber k sV Γ.ι Γ.dim_le (h.isQCartier hL) =
      (residueFieldDegree u Γ.point : ℚ) * L.intersectionNumber k sT Γ'.ι Γ'.dim_le hL := by
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hL
  rw [QDivisor.intersectionNumber_eq_of_smul k sV Γ.ι _ _ _ (QDivisor.cartierIndex_pos hL) D'
    (hp.isCartier hDc) hD', QDivisor.intersectionNumber_eq_of_smul k sT Γ'.ι _ _ _
    (QDivisor.cartierIndex_pos hL) D hDc hD, degreeOn_isPullback_eq_mul u hu hDc hp Γ Γ' hΓ']
  push_cast
  ring

/-- An `ℝ`-Cartier pull-back is numerically trivial on every curve the morphism contracts. -/
private theorem forall_eq_zero_of_isRCartierPullback (u : V ⟶ T) (hu : u ≫ sT = sV)
    {D : RDivisor T} {D' : RDivisor V} (h : MMP.Flips.IsRCartierPullback u D D')
    (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sV D' r L Γ x → x = 0 := by
  obtain ⟨m, r, L, L', hL, -, hpb, hD'⟩ := h
  choose hB hpb using hpb
  refine (forall_eq_zero_iff Γ r L' (fun j => (hpb j).isCartier (hL j)) hD').2
    (Finset.sum_eq_zero fun j _ => ?_)
  rw [degreeOn_isPullback_eq_zero u hu (hL j) (hpb j) Γ hΓ, Int.cast_zero, mul_zero]

/-- **Projection formula** for numerical triviality: on a curve `Γ` not contracted by `u`, with
image the proper curve `Γ'`, an `ℝ`-Cartier pull-back `u^*D` is numerically trivial on `Γ` if
and only if `D` is numerically trivial on `Γ'`. -/
private theorem forall_eq_zero_iff_of_isRCartierPullback (u : V ⟶ T) (hu : u ≫ sT = sV)
    {D : RDivisor T} {D' : RDivisor V} (h : MMP.Flips.IsRCartierPullback u D D')
    (Γ : ProperCurve sV) (hΓ : ¬ Γ.IsContractedBy u) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sV D' r L Γ x → x = 0) ↔
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor T) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sT D r L Γ' x → x = 0 := by
  obtain ⟨m, r, L, L', hL, hD, hpb, hD'⟩ := h
  choose hB hpb using hpb
  have hj : ∀ j, ((L' j).degreeOn k sV Γ.ι Γ.dim_le ((hpb j).isCartier (hL j)) : ℝ) =
      residueFieldDegree u Γ.point * ((L j).degreeOn k sT Γ'.ι Γ'.dim_le (hL j) : ℝ) :=
    fun j => by rw [degreeOn_isPullback_eq_mul u hu (hL j) (hpb j) Γ Γ' hΓ']; push_cast; rfl
  have hc : (residueFieldDegree u Γ.point : ℝ) ≠ 0 := by
    exact_mod_cast (residueFieldDegree_pos u hu Γ hΓ).ne'
  rw [forall_eq_zero_iff Γ r L' (fun j => (hpb j).isCartier (hL j)) hD',
    forall_eq_zero_iff Γ' r L hL hD]
  simp only [hj, mul_left_comm (r _), ← Finset.mul_sum, mul_eq_zero, hc, false_or]

end Pullback

/-! ### Nefness read on intersection numbers -/

section Nef

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A `ℚ`-Cartier `ℚ`-divisor with nonnegative intersection number on every curve contracted by
`f` is `f`-nef. -/
private theorem isRelativelyNef_of_intersectionNumber_nonneg {f : X ⟶ Y} {D : QDivisor X}
    (hD : D.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD) :
    D.IsRelativelyNef sX f := by
  refine ⟨hD, fun C hC => ?_⟩
  have key := h C hC
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD _
    (D.cartierIndexSMul hD).2 (QDivisor.toQDivisor_cartierIndexSMul D hD)] at key
  have hm : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have hdeg : (0 : ℚ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℚ) := by
    have := mul_nonneg key hm.le
    rwa [div_mul_cancel₀ _ hm.ne'] at this
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  have hdeg' : (0 : ℝ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℝ) := by exact_mod_cast hdeg
  have hm' : (0 : ℝ) ≤ (((1 / (D.cartierIndex hD : ℚ)) • (1 : ℚ) : ℚ) : ℝ) := by
    simp only [smul_eq_mul, mul_one, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    positivity
  exact mul_nonneg hm' hdeg'

/-- `(-D) · C = -(D · C)`. -/
private theorem intersectionNumber_neg {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X} (hD : D.IsQCartier)
    (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -D.intersectionNumber k sX i hdim hD := by
  have h1 : ((-1 : ℚ) • D).IsQCartier := by rwa [neg_one_smul]
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim hD' h1 (neg_one_smul ℚ D).symm,
    MMP.Fourfold.intersectionNumber_smul sX i hdim D hD (-1) h1]
  ring

end Nef

/-! ### Curves of the target lifted to the source -/

section Lift

variable {k : Type u} [Field k] {V T S : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} (u : V ⟶ T) [IsProper u] {Γ : ProperCurve sV} {C : ProperCurve sT}

/-- If `u` maps the closure of `Γ` onto the closure of `C`, it maps the generic point of `Γ` to
that of `C`. -/
private theorem point_eq_of_image_closure_eq (h : u '' closure {Γ.point} = closure {C.point}) :
    C.point = u Γ.point := by
  rw [← u.isClosedMap.closure_image_eq_of_continuous u.continuous, Set.image_singleton] at h
  exact (inseparable_iff_closure_eq.mpr h.symm).eq

/-- A curve mapped by `u` onto a curve is not contracted by `u`. -/
private theorem not_isContractedBy_of_image_closure_eq
    (h : u '' closure {Γ.point} = closure {C.point}) : ¬ Γ.IsContractedBy u := by
  intro hcon
  have hr : ∀ t, C.ι t = C.point := fun t => by
    have ht : C.ι t ∈ closure {C.point} := C.range_ι ▸ ⟨t, rfl⟩
    obtain ⟨x, hx, hxt⟩ := h.ge ht
    rw [← hxt, hcon x hx, point_eq_of_image_closure_eq u h]
  exact MMP.Flips.not_subsingleton_scheme C
    ⟨fun a b => C.ι.isEmbedding.injective ((hr a).trans (hr b).symm)⟩

/-- A curve mapped by `u` onto a curve contracted by `π` is contracted by `u ≫ π`. -/
private theorem isContractedBy_comp_of_image_closure_eq {π : T ⟶ S}
    (h : u '' closure {Γ.point} = closure {C.point}) (hC : C.IsContractedBy π) :
    Γ.IsContractedBy (u ≫ π) := fun x hx => by
  have hux : u x ∈ closure {C.point} := h ▸ ⟨x, hx, rfl⟩
  simp only [Scheme.Hom.comp_apply, hC _ hux, point_eq_of_image_closure_eq u h]

end Lift

/-- **Two-sided negativity.** A `ℚ`-Cartier divisor on `T` of degree zero on every curve
contracted by a proper birational morphism `q : T ⟶ V` of normal varieties, whose transform
`q_* A` vanishes, is zero. -/
private theorem eq_zero_of_transformDivisor_eq_zero {k : Type u} [Field k] {T V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) [QuasiCompact sT] [IsLocallyNoetherian T]
    [IsNormal T] (hV : IsNormalVariety k sV) (hT : IsNormalVariety k sT) (q : T ⟶ V)
    (hq : q ≫ sV = sT) [IsProper q] (hqb : IsBirationalMorphism q) {A : QDivisor T}
    (hA : A.IsQCartier) (htr : RationalMap.transformDivisor q.toRationalMap A = 0)
    (h0 : ∀ Γ : ProperCurve sT, Γ.IsContractedBy q →
      A.intersectionNumber k sT Γ.ι Γ.dim_le hA = 0) :
    A = 0 := by
  have hAn := isQCartier_neg hA
  have h1 := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sV sT hV hT q hq hqb hA
    (isRelativelyNef_of_intersectionNumber_nonneg sT hAn fun Γ hΓ => by
      rw [intersectionNumber_neg sT Γ.ι Γ.dim_le hA hAn, h0 Γ hΓ, neg_zero])
    (by rw [htr]; exact DivisorWithCoeffs.isEffective_iff_nonneg.mpr le_rfl)
  have h2 := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sV sT hV hT q hq hqb hAn
    (by rw [neg_neg]; exact isRelativelyNef_of_intersectionNumber_nonneg sT hA fun Γ hΓ =>
      (h0 Γ hΓ).ge)
    (by rw [map_neg, htr, neg_zero]; exact DivisorWithCoeffs.isEffective_iff_nonneg.mpr le_rfl)
  exact le_antisymm (neg_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp h2))
    (DivisorWithCoeffs.isEffective_iff_nonneg.mp h1)

end Proof_lem_fourfold_descend_null_divisor_qfactorial

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori Proof_lem_fourfold_descend_null_divisor_qfactorial

/-- **Numerical descent of a null divisor.** Let `Y`, `Z` be normal `ℚ`-factorial projective
varieties over `k`, over a base `S` via `πY`, `πZ`, with a common resolution: a smooth variety
`W` with projective birational morphisms `p : W ⟶ Y`, `q : W ⟶ Z` over `S`. Let `K_Y + C_Y` and
`K_Z + C_Z` be real adjoints nef over `S` whose pull-backs `D_Y`, `D_Z` to `W` have the same
zero-degree curves over `S`. Let `H` be a `ℚ`-Cartier `ℚ`-divisor on `Y` with `H · Γ = 0` for
every curve `Γ ⊆ Y` over a point of `S` with `(K_Y + C_Y) · Γ = 0`, and `H_W = p^*H`. Then
`H_Z = q_* H_W` is `ℚ`-Cartier, `q^*H_Z = H_W`, and `H_Z` is nef over `S` if `H` is. -/
@[mmp "lem_fourfold_descend_null_divisor_qfactorial"]
public theorem isQCartier_and_isPullback_transformDivisor_of_null
    {k : Type u} [Field k] {W Y Z S : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (sW : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [QuasiCompact sW] [QuasiCompact sY] [QuasiCompact sZ]
    (hW : MMP.Mori.IsVariety k sW) (hWs : MMP.Mori.IsSmoothScheme sW)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (hZ : IsQFactorial sZ) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y) (q : W ⟶ Z)
    (hpY : p ≫ sY = sW) (hqZ : q ≫ sZ = sW) (hpq : p ≫ πY = q ≫ πZ)
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    (hq : IsProjectiveMorphism q) (hqb : IsBirationalMorphism q)
    {KY : Divisor Y} {CY : RDivisor Y} {KZ : Divisor Z} {CZ : RDivisor Z}
    (hKY : ∃ m : ℕ, KY.IsCanonicalDivisor sY m) (hKZ : ∃ m : ℕ, KZ.IsCanonicalDivisor sZ m)
    (hLY : MMP.Flips.IsRelativelyNef k sY πY (MMP.Flips.logCanonicalDivisor KY CY))
    (hLZ : MMP.Flips.IsRelativelyNef k sZ πZ (MMP.Flips.logCanonicalDivisor KZ CZ))
    {DY DZ : RDivisor W}
    (hDY : MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY CY) DY)
    (hDZ : MMP.Flips.IsRCartierPullback q (MMP.Flips.logCanonicalDivisor KZ CZ) DZ)
    (hzero : ∀ Γ : ProperCurve sW, Γ.IsContractedBy (p ≫ πY) →
      ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
          MMP.Flips.IsRIntersectionNumber k sW DY r L Γ x → x = 0) ↔
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
          MMP.Flips.IsRIntersectionNumber k sW DZ r L Γ x → x = 0))
    {H : QDivisor Y} (hH : H.IsQCartier)
    (hnull : ∀ Γ : ProperCurve sY, Γ.IsContractedBy πY →
      (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
          MMP.Flips.IsRIntersectionNumber k sY (MMP.Flips.logCanonicalDivisor KY CY) r L Γ x →
            x = 0) →
        H.intersectionNumber k sY Γ.ι Γ.dim_le hH = 0)
    {HW : QDivisor W} (hHW : ∃ hB, H.IsPullback p hB HW) :
    QDivisor.IsQCartier (MMP.Mori.RationalMap.transformDivisor q.toRationalMap HW) ∧
      (∃ hB, QDivisor.IsPullback q
        (MMP.Mori.RationalMap.transformDivisor q.toRationalMap HW) hB HW) ∧
      (H.IsRelativelyNef sY πY → QDivisor.IsRelativelyNef sZ πZ
        (MMP.Mori.RationalMap.transformDivisor q.toRationalMap HW)) := by
  haveI : AlgebraicGeometry.IsVariety k sW := hW
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hq
  haveI : IsDominant q := hqb.isDominant
  set HZ : QDivisor Z := RationalMap.transformDivisor q.toRationalMap HW
  have hHZ := MMP.Fourfold.isQCartier_of_isQFactorial sZ hZ HZ
  obtain ⟨hBp, hHWp⟩ := hHW
  have hHWq : HW.IsQCartier := hHWp.isQCartier hH
  have hBq : ∀ Z' : irreducibleComponents W, q (componentGenericPoint W Z') ∉ HZ.supp :=
    fun Z' => by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant q]
      exact MMP.Fourfold.genericPoint_notMem_supp _
  have := QuasiCompact.compactSpace_of_compactSpace sW
  set G : QDivisor W := HZ.pullback hHZ hBq
  have hG : HZ.IsPullback q hBq G := QDivisor.isPullback_pullback hHZ hBq
  have hGq := hG.isQCartier hHZ
  -- `p^*H` is null on every curve contracted by `q`
  have hHW0 : ∀ Γ : ProperCurve sW, Γ.IsContractedBy q →
      HW.intersectionNumber k sW Γ.ι Γ.dim_le hHWq = 0 := fun Γ hΓ => by
    by_cases hpc : Γ.IsContractedBy p
    · exact intersectionNumber_isPullback_eq_zero p hpY hH hHWp Γ hpc
    have hΓS : Γ.IsContractedBy (p ≫ πY) := fun x hx => by
      simp only [hpq, Scheme.Hom.comp_apply, hΓ x hx]
    have hY0 := (hzero Γ hΓS).2 (forall_eq_zero_of_isRCartierPullback q hqZ hDZ Γ hΓ)
    rw [intersectionNumber_isPullback_eq_mul p hpY hH hHWp Γ
        ⟨p Γ.point, isProperCurve_map p hpY Γ hpc⟩ rfl,
      hnull _ (isContractedBy_map p hpY πY Γ hpc hΓS)
        ((forall_eq_zero_iff_of_isRCartierPullback p hpY hDY Γ hpc _ rfl).1 hY0), mul_zero]
  -- `p^*H - q^*H_Z` is `q`-trivial with `q_*`-transform zero, hence zero
  have hEq : HW = G := by
    have hGn := isQCartier_neg hGq
    refine add_neg_eq_zero.mp (eq_zero_of_transformDivisor_eq_zero sZ sW hZ.1 ⟨hW, inferInstance⟩
      q hqZ hqb (hHWq.add hGn) ?_ fun Γ hΓ => ?_)
    · rw [map_add, map_neg, MMP.Positivity.transformDivisor_of_isPullback hZ.1
        (hqZ ▸ ⟨hW, inferInstance⟩) hqb hHZ hBq hG]
      exact add_neg_cancel _
    · rw [QDivisor.intersectionNumber_add' k sW Γ.ι Γ.dim_le HW _ hHWq hGn,
        intersectionNumber_neg sW Γ.ι Γ.dim_le hGq hGn, hHW0 Γ hΓ,
        intersectionNumber_isPullback_eq_zero q hqZ hHZ hG Γ hΓ, neg_zero, add_zero]
  refine ⟨hHZ, ⟨hBq, hEq ▸ hG⟩, fun hHn => ?_⟩
  -- nefness: lift a curve `C` of `Z` over a point of `S` to a curve `Γ` of `W`
  refine isRelativelyNef_of_intersectionNumber_nonneg sZ hHZ fun C hC => ?_
  obtain ⟨Γ, hΓ⟩ := ProperCurve.exists_image_closure_eq_of_surjective hW hZp.toIsVariety q hqZ C
  have hqc := not_isContractedBy_of_image_closure_eq q hΓ
  have hΓS : Γ.IsContractedBy (p ≫ πY) := hpq ▸ isContractedBy_comp_of_image_closure_eq q hΓ hC
  have hHWΓ : 0 ≤ HW.intersectionNumber k sW Γ.ι Γ.dim_le hHWq := by
    by_cases hpc : Γ.IsContractedBy p
    · rw [intersectionNumber_isPullback_eq_zero p hpY hH hHWp Γ hpc]
    · rw [intersectionNumber_isPullback_eq_mul p hpY hH hHWp Γ
        ⟨p Γ.point, isProperCurve_map p hpY Γ hpc⟩ rfl]
      exact mul_nonneg (by positivity)
        (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sY hHn hH _
          (isContractedBy_map p hpY πY Γ hpc hΓS))
  rw [MMP.Fourfold.intersectionNumber_congr sW Γ.ι Γ.dim_le hHWq hGq hEq,
    intersectionNumber_isPullback_eq_mul q hqZ hHZ hG Γ C
      (point_eq_of_image_closure_eq q hΓ)] at hHWΓ
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast residueFieldDegree_pos q hqZ Γ hqc)).mp
    hHWΓ

end MMP.Fourfold

end
