module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineIdealOfEquations
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction

/-!
# Exceptional `ℝ`-Cartier divisors: fibre support and the equality criterion

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k` and `F` an
`ℝ`-Cartier divisor on `Y` supported on the prime divisors exceptional over `X`, with `-F`
`f`-nef. Then `F` is effective, and every fibre of `f` is contained in `Supp F` or disjoint from
it (Kollár et al., *Flips and abundance*, 17.4.2). If moreover `F` is numerically trivial on a
fibre `f⁻¹(b)`, that fibre is disjoint from `Supp F` (*Flips and abundance*, 2.28.2.2).

## Main results

* `MMP.Flips.isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg`:
  effectivity and the fibre alternative for exceptional `F` with `-F` relatively nef.
* `MMP.Flips.disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint`: numerical
  triviality of `F` over a point forces the fibre to miss `Supp F`; over an arbitrary field this
  is `MMP.Flips.disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field`.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result. Effectivity is the negativity lemma
`MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback` applied with `L = 0`; the fibre
alternative is `MMP.Flips.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg`.
The equality criterion is proved by induction on `dim W`, cutting down along the normalization of
a prime divisor of the base found by prime avoidance; it uses neither resolution nor Bertini, so
it holds over any field
(`MMP.Flips.disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field`); the
hypotheses `[IsAlgClosed k] [CharZero k]` of the source's setting are kept on
`MMP.Flips.disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint`. "`F` is supported
on the exceptional prime divisors" is the condition that `F.coeff P = 0` for every prime divisor
`P` not exceptional over the base
(`MMP.Flips.IsExceptionalPrimeDivisor`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19,
  2.28.2.2, 17.4.2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_mmp_foundation_fa17_real_negativity_fibres

open MMP MMP.Mori MMP.Flips

/-- The zero divisor is `ℝ`-Cartier, by the empty presentation. -/
private lemma isCartierCombination_zero {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] :
    IsCartierCombination (0 : RDivisor X) :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

end Proof_lem_mmp_foundation_fa17_real_negativity_fibres

namespace MMP.Flips

open MMP.Mori
open Proof_lem_mmp_foundation_fa17_real_negativity_fibres

/-- **Negativity lemma for exceptional `ℝ`-Cartier divisors.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties over `k`, and `F` an `ℝ`-Cartier divisor on `Y` supported
on the prime divisors exceptional over `X`, with `-F` `f`-nef. Then `F` is effective, and every
fibre `f⁻¹(x)` is either contained in `Supp F` or disjoint from `Supp F`. -/
@[mmp "lem_mmp_foundation_fa17_real_negativity_fibres"]
public theorem isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    {F : RDivisor Y} (hF : IsCartierCombination F)
    (hFexc : ∀ P : Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sX f P → F.coeff P = 0)
    (hnef : IsRelativelyNef k sY f (-F)) :
    F.IsEffective ∧
      ∀ x : X, f.base ⁻¹' {x} ⊆ (F.supp : Set Y) ∨ Disjoint (f.base ⁻¹' {x}) (F.supp : Set Y) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNormal X := hX.2
  have hnegF : IsCartierCombination (-F) :=
    let ⟨m, r, L, hL, hD, _⟩ := hnef; ⟨m, r, L, hL, hD⟩
  have hFeff : F.IsEffective :=
    isEffective_of_isNumericallyEquivalentOver_pullback k sX sY hX hY f hf hfb
      isCartierCombination_zero (Fourfold.isRCartierPullback_zero f) hnegF hnef hF
      (fun P hP => (hFexc P hP).ge)
      (by
        rw [neg_add_cancel]
        exact ⟨isCartierCombination_zero, isCartierCombination_zero,
          fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ h₁ h₂ =>
            (IsRIntersectionNumber.eq_and_linear k sY C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩)
  exact ⟨hFeff, preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sX sY hX hY f
    hf hfb hF hFeff hnef⟩

end MMP.Flips

namespace Proof_lem_fa2_negativity_equality_criterion

open MMP MMP.Mori MMP.Flips

section Helpers

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

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

/-- A normalization of a proper curve is a curve. -/
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
  let := (functionFieldMap f).toAlgebra
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
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
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

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
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

end Intersection

/-- **Degrees can be computed on an open subscheme.** Let `V ⊆ Y` be an integral open subscheme,
`L` a Cartier divisor on `Y` and `C` a proper curve of `Y` lying in `V`, which is the proper curve
`C_V` of `V`. Then the degree of the restriction `L|_V` (the pull-back along `V ⟶ Y`) along `C_V`
is the degree of `L` along `C`. -/
private theorem degreeOn_pullback_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (V : Y.Opens) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)) (hC : V.ι CV.point = C.point)
    (hCV : closure ({C.point} : Set Y) ⊆ V) :
    have := QuasiCompact.compactSpace_of_compactSpace sY
    (L.pullback hL hB).degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le (hL.isCartier_pullback V.ι hB) =
      L.degreeOn k sY C.ι C.dim_le hL := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hL.isInvertibleModule_divisorialSheaf
  have hLV := hL.isCartier_pullback V.ι hB
  have := hLV.isInvertibleModule_divisorialSheaf
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι CV.point hC (by
    rwa [Scheme.Opens.range_ι])
  have : IsProper ((CV.ι ≫ V.ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sY C.ι (CV.ι ≫ V.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) L.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp k sY V.ι CV.ι CV.dim_le L.divisorialSheaf
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL V.ι hB
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (V.ι ≫ sY) CV.ι CV.dim_le e₂
  exact (h1.trans (h2.trans h3.symm)).symm

/-- The coefficient of the restriction `L|_V` of a Cartier divisor along a prime divisor `E` of
the open subscheme `V` is the coefficient of `L` along the closure of `E`. -/
private theorem coeff_pullback_ι {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (V : Y.Opens) [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (E : MMP.Mori.PrimeDivisor V) :
    (L.pullback hL hB).coeff E = L.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) :=
  MMP.Positivity.coeff_eq_of_isPullback E _
    (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm hL
    (Divisor.isPullback_pullback hL hB)

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- An integral scheme, compact and locally of finite type over a field, has finite dimension. -/
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

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **Pulling back a divisor nonpositive on contracted curves.** Let `h : Y' ⟶ Y` be proper and
`B = ∑ s_j N_j` a combination of Cartier divisors with `B · C ≤ 0` on every curve contracted by
`f : Y ⟶ X`. Then `-h^*B = -∑ s_j h^*N_j` is `(h ≫ f)`-nef. -/
private theorem isRelativelyNef_neg_sum_pullback {k : Type u} [Field k] {X Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [IsProper h] [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ X) {m : ℕ} (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hNB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp)
    (hBC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0) :
    IsRelativelyNef k (h ≫ sY) (h ≫ f)
      (-∑ j, s j • Divisor.toRDivisor ((N j).pullback (hN j) (hNB j))) := by
  have hN'c : ∀ j, ((N j).pullback (hN j) (hNB j)).IsCartier := fun j =>
    (hN j).isCartier_pullback h (hNB j)
  refine ⟨m, fun j => -s j, _, hN'c, by simp [← Finset.sum_neg_distrib], fun C' hC' x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (h ≫ sY) C' (fun j => -s j) _ hN'c
  rw [(IsRIntersectionNumber.eq_and_linear k (h ≫ sY) C').1 _ _ _ _ _ _ _ hx
    (by simpa [← Finset.sum_neg_distrib] using hx0)]
  by_cases hc : IsProperCurve sY (h C'.point)
  · -- `h(C')` is a curve `C`, contracted by `f`
    let C : ProperCurve sY := ⟨_, hc⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      have hsub : closure ({h C'.point} : Set Y) ⊆ h '' closure ({C'.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    simp only [degreeOn_pullback_eq_mul h (hN _) (hNB _) C' C rfl, Int.cast_mul, Int.cast_natCast,
      Finset.sum_neg_distrib, mul_left_comm (s _), ← Finset.mul_sum, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hBC C hCf)
  · -- `h(C')` is a point
    simp [degreeOn_pullback_eq_zero h (hN _) (hNB _) C' hc]

/-- The intersection number of `-D` is the negative of that of `D`, for the negated
presentation. -/
private theorem isRIntersectionNumber_neg {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {C : ProperCurve sX}
    {x : ℝ} (h : IsRIntersectionNumber k sX D r L C x) :
    IsRIntersectionNumber k sX (-D) (fun j => -r j) L C (-x) := by
  obtain ⟨hL, d, hD, hd, hx⟩ := h
  refine ⟨hL, d, ?_, hd, ?_⟩
  · rw [hD, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  · rw [hx, ← Finset.sum_neg_distrib]
    simp [neg_mul]

/-- If `-D` is `f`-nef, then `D · C ≤ 0` for every curve `C` contracted by `f`. -/
private theorem nonpos_of_isRelativelyNef_neg {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    {D : RDivisor X} (hnef : IsRelativelyNef k sX f (-D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX D r L C x) : x ≤ 0 := by
  obtain ⟨m', r', L', hL', hpres, hall⟩ := hnef
  have hy := isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hpres] at hy
  have := (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _
    (isRIntersectionNumber_neg hx) hy
  linarith [hall C hC _ hy]

/-- The negative of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (hD : IsCartierCombination D) : IsCartierCombination (-D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  exact ⟨m, fun j => -r j, L, hL, by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- The restriction of a birational morphism over an open set it hits is birational. -/
private theorem isBirationalMorphism_morphismRestrict {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {f : Y ⟶ X} (hf : IsBirationalMorphism f) (U : X.Opens) [Nonempty (f ⁻¹ᵁ U)] :
    IsBirationalMorphism (f ∣_ U) := by
  obtain ⟨W, hWne, hW⟩ := hf.exists_isOpenImmersion
  let S : (f ⁻¹ᵁ U).toScheme.Opens := (f ⁻¹ᵁ U).ι ⁻¹ᵁ W
  have hSne : (S : Set (f ⁻¹ᵁ U)).Nonempty := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (f ⁻¹ᵁ U)›
    have hd : Dense (W : Set Y) := W.isOpen.dense hWne
    obtain ⟨z, hzU, hzW⟩ := hd.inter_open_nonempty _ (f ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    exact ⟨⟨z, hzU⟩, hzW⟩
  have hS : Dense (S : Set (f ⁻¹ᵁ U)) := S.isOpen.dense hSne
  have : Nonempty S := hSne.to_subtype
  have hrange : Set.range (S.ι ≫ (f ⁻¹ᵁ U).ι) ⊆ Set.range W.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let h := IsOpenImmersion.lift W.ι (S.ι ≫ (f ⁻¹ᵁ U).ι) hrange
  let g : S.toScheme ⟶ U := S.ι ≫ (f ∣_ U)
  have hg : g ≫ U.ι = h ≫ W.ι ≫ f := by
    simp only [g, h, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
  have : IsOpenImmersion (g ≫ U.ι) := by rw [hg]; infer_instance
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g U.ι
  have : IsDominant g := by
    have : Nonempty U := ⟨g (Classical.arbitrary S)⟩
    have : IsIntegral U.toScheme := inferInstance
    have : IrreducibleSpace U.toScheme := inferInstance
    exact ⟨IsOpen.dense (X := U.toScheme) g.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)⟩
  have hd : Dense (g.opensRange : Set U) := g.denseRange
  have hgdef : g = S.ι ≫ f ∣_ U := rfl
  clear_value g
  refine ⟨⟨S, hS, g.opensRange, hd,
    g.isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨S, hS, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι, hgdef, Scheme.topIso_hom]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- A prime divisor `F` of `Y` is exceptional over the normal variety `X` exactly when its image
`g(η_F)` has coheight at least two. -/
private theorem isExceptionalPrimeDivisor_iff_two_le_coheight {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX g F ↔ 2 ≤ Order.coheight (g F.genericPoint) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  constructor
  · rintro ⟨_, _, _, hexc⟩
    unfold ProperDivisorOver.IsExceptional at hexc
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn] at hexc
    exact (withBot_add_two_le_iff hd).mp hexc
  · intro h2
    refine ⟨hY, hg, ‹_›, ?_⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn]
    exact (withBot_add_two_le_iff hd).mpr h2

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor_of_coheight_eq_one {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := fun hexc => by
  obtain ⟨hY, hg, _, -⟩ := id hexc
  have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hX g hY hg F).mp hexc
  rw [hF] at h2
  exact absurd h2 (by decide)

/-- A proper curve of an open subscheme `V ⊆ Y` is a proper curve of `Y`, contained in `V`. -/
private theorem exists_properCurve_of_opens {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} [IsSeparated s] (V : Y.Opens) (C' : ProperCurve (V.ι ≫ s)) :
    ∃ C : ProperCurve s, V.ι C'.point = C.point ∧ closure ({C.point} : Set Y) ⊆ V := by
  have : IsProper ((C'.ι ≫ V.ι) ≫ s) := by rw [Category.assoc]; exact C'.isProper_ι_comp
  have : IsProper (C'.ι ≫ V.ι) := IsProper.of_comp _ s
  have hrange : Set.range (C'.ι ≫ V.ι) = V.ι '' closure {C'.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C'.range_ι]
  have hcl : closure ({V.ι C'.point} : Set Y) ⊆ Set.range V.ι := by
    have hclosed : IsClosed (Set.range (C'.ι ≫ V.ι)) := (C'.ι ≫ V.ι).isClosedMap.isClosed_range
    refine (closure_minimal ?_ hclosed).trans ?_
    · rw [Set.singleton_subset_iff, hrange]; exact ⟨_, subset_closure rfl, rfl⟩
    · rw [hrange]; exact Set.image_subset_range _ _
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι C'.point rfl hcl
  refine ⟨⟨V.ι C'.point, ⟨?_, ?_⟩⟩, rfl, by rwa [Scheme.Opens.range_ι] at hcl⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C'.dim_eq
  · have he' : curveSubschemeAtι (V.ι C'.point) = e.inv ≫ curveSubschemeAtι C'.point ≫ V.ι := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [he', Category.assoc, Category.assoc]
    have : IsProper (curveSubschemeAtι C'.point ≫ V.ι ≫ s) := C'.isProper_ι_comp
    infer_instance

/-- A contracted curve maps to a closed point. -/
private theorem isClosed_singleton_of_isContractedBy {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) [UniversallyClosed f] (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : IsClosed ({f C.point} : Set Y) := by
  have : f.base '' closure {C.point} = {f C.point} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, subset_closure rfl, rfl⟩,
      fun y ⟨x, hx, hxy⟩ => hxy ▸ hC x hx⟩
  rw [← this]
  exact f.isClosedMap _ isClosed_closure

/-! ### Cutting by a prime divisor -/

/-- A morphism from a reduced scheme whose image lies in the support of an ideal sheaf `I`
kills `I`. -/
private theorem le_ker_of_range_subset {X Y : Scheme.{u}} [IsReduced X] (I : Y.IdealSheafData)
    (f : X ⟶ Y) (h : Set.range f ⊆ I.support) : I ≤ f.ker := by
  have hk : f.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
    rw [← Category.id_comp f, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot_of_isIso,
      ← Scheme.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    simp [Set.image_univ]
  rwa [hk, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    TopologicalSpace.Closeds.closure_le]

/-- **Prime avoidance.** On an affine Noetherian integral scheme, a point `b` other than the
generic point lies on a prime divisor which contains none of finitely many given proper
generizations of `b`. -/
private theorem exists_primeDivisor_specializes_and_not_specializes {Z : Scheme.{u}}
    [IsAffine Z] [IsIntegral Z] [IsLocallyNoetherian Z] (b : Z) (S : Finset Z)
    (hS : ∀ s ∈ S, s ⤳ b ∧ s ≠ b) (hb : b ≠ genericPoint Z) :
    ∃ Q : MMP.Mori.PrimeDivisor Z, Q.genericPoint ⤳ b ∧ ∀ s ∈ S, ¬ Q.genericPoint ⤳ s := by
  classical
  let e := Z.isoSpec
  have : IsNoetherianRing Γ(Z, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩
  have hsp : ∀ x y : Z, x ⤳ y ↔ (e.hom x).asIdeal ≤ (e.hom y).asIdeal := fun x y => by
    rw [← e.hom.isOpenEmbedding.isInducing.specializes_iff]
    exact (PrimeSpectrum.le_iff_specializes _ _).symm
  let I : Z → Ideal Γ(Z, ⊤) := fun z => (e.hom z).asIdeal
  let T := insert (genericPoint Z) S
  have hnot : ¬ ((I b : Set Γ(Z, ⊤)) ⊆ ⋃ i ∈ (T : Set Z), (I i : Set Γ(Z, ⊤))) := by
    rw [Ideal.subset_union_prime (genericPoint Z) (genericPoint Z)
      (fun i _ _ _ => (e.hom i).isPrime)]
    rintro ⟨i, hi, hle⟩
    have hib : b ⤳ i := (hsp b i).mpr hle
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hb (hib.antisymm (genericPoint_specializes b)).eq
    · obtain ⟨hsb, hne⟩ := hS i hi
      exact hne (hsb.antisymm hib).eq
  obtain ⟨g, hgb, hgT⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_iUnion, not_exists] at hgT
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {g}) (J := I b)
    (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hgb)
  have h𝔓prime : 𝔓.IsPrime := h𝔓min.1.1
  have hg𝔓 : g ∈ 𝔓 := h𝔓min.1.2 (Ideal.subset_span rfl)
  have hht : 𝔓.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) 𝔓 h𝔓min
  let q : Spec Γ(Z, ⊤) := ⟨𝔓, h𝔓prime⟩
  let z : Z := e.inv q
  have hez : e.hom z = q := by
    change (e.inv ≫ e.hom) q = q
    rw [Iso.inv_hom_id]; rfl
  have hgz : ∀ i ∈ T, ¬ z ⤳ i := fun i hi hzi =>
    hgT i hi (by
      have := (hsp z i).mp hzi
      rw [hez] at this
      exact this hg𝔓)
  have hcz : Order.coheight z = 1 := by
    have h1 : Order.coheight z = Order.coheight q := by
      rw [← hez]; exact (coheight_eq_of_isOpenImmersion e.hom).symm
    have h2 : Order.coheight q = 𝔓.height := (idealHeight_eq_coheight _ q).symm
    have h0 : Order.coheight z ≠ 0 := by
      rw [Ne, Order.coheight_eq_zero]
      intro hmax
      exact hgz (genericPoint Z) (Finset.mem_insert_self _ _) (hmax (genericPoint_specializes z))
    exact le_antisymm (by rwa [h1, h2]) (Order.one_le_iff_ne_zero.mpr h0)
  have hQ : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcz) = z :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcz
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcz, ?_, fun s hs => ?_⟩
  · rw [hQ, hsp, hez]; exact h𝔓le
  · rw [hQ]; exact hgz s (Finset.mem_insert_of_mem hs)

/-- The closed immersion of a prime divisor maps the generic point to its generic point. -/
private theorem subschemeι_genericPoint {X : Scheme.{u}} (P : MMP.Mori.PrimeDivisor X) :
    have := P.integral
    P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := rfl

/-- **The normalization of a prime divisor** of a variety: a normal variety, finite, surjective
and birational over the divisor, through which every dominant morphism from a normal integral
scheme lifts. -/
private theorem exists_normalization_primeDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (P : MMP.Mori.PrimeDivisor X) :
    have := P.integral
    ∃ (N : Scheme.{u}) (ν : N ⟶ P.idealSheaf.subscheme),
      IsNormalVariety k (ν ≫ P.idealSheaf.subschemeι ≫ sX) ∧ IsFinite ν ∧ Surjective ν ∧
      IsBirational ν ∧ ∀ (V : Scheme.{u}) [IsIntegral V] [IsNormal V]
        (f : V ⟶ P.idealSheaf.subscheme) [IsDominant f], ∃ g : V ⟶ N, g ≫ ν = f := by
  have := P.integral
  have := hX.1
  have : AlgebraicGeometry.IsVariety k (P.idealSheaf.subschemeι ≫ sX) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvar, hnorm, hfin, hsurj, -⟩, -, hUP, -, -⟩ :=
    MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)
  exact ⟨_, _, ⟨hvar, hnorm⟩, hfin, hsurj, Scheme.isBirational_normalization _ _,
    fun V _ _ f _ => (hUP V f).exists⟩

/-- A morphism of integral schemes is birational if its composite with a birational morphism is,
and it maps the generic point to the generic point. -/
private theorem isBirational_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : IsBirational (f ≫ g)) (hg : IsBirational g)
    (hf : f (genericPoint X) = genericPoint Y) : IsBirational f := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hf]
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have h1 := hfg.2 _ (by rw [genericPoints_eq_singleton]; rfl)
    have h2 : IsIso (g.stalkMap (f (genericPoint X))) :=
      hg.2 _ (by rw [hf, genericPoints_eq_singleton]; rfl)
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap _) (f.stalkMap _) h2 h1

/-- For a finite morphism, the closure of a point has at most the dimension of the closure of its
image. -/
private theorem topologicalKrullDim_closure_le_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) ≤
      topologicalKrullDim (closure ({f x} : Set Y)) := by
  have hmaps : Set.MapsTo f.base (closure {x}) (closure {f x}) := fun y hy =>
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hy).map f.base.hom.continuous)
  have : QuasiSober (closure ({x} : Set X)) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  exact MMP.Flips.topologicalKrullDim_le_of_specializes_imp_eq
    (f := hmaps.restrict) (f.base.hom.continuous.restrict hmaps) fun a b hab heq =>
      Subtype.ext (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite f
        ((subtype_specializes_iff _ _).mp hab) (congrArg Subtype.val heq))

/-- On a variety, the dimension of the closure of a point and its coheight are natural numbers
adding up to the dimension. -/
private theorem exists_nat_closure_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] (x : X) :
    ∃ a c n : ℕ, topologicalKrullDim (closure ({x} : Set X)) = a ∧ Order.coheight x = c ∧
      topologicalKrullDim X = n ∧ a + c = n := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  have ha := Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX x
  set a := (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation k).dimensionFunction
    sX x).toNat
  rw [ha, hn] at hd
  have hd' : (a : ℕ∞) + Order.coheight x = n := by exact_mod_cast hd
  have hc : Order.coheight x ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hd'
    exact ENat.top_ne_natCast n hd'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hc
  rw [← hc] at hd'
  exact ⟨a, c, n, ha, hc.symm, hn, by exact_mod_cast hd'⟩

/-- A morphism `φ : E ⟶ Q` of prime divisors lying over `h` maps the generic point to the
generic point when `h(η_E) = η_Q`. -/
private theorem map_genericPoint_of_comp_eq_comp {W Z : Scheme.{u}} (h : W ⟶ Z)
    (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (φ : E.idealSheaf.subscheme ⟶ Q.idealSheaf.subscheme)
    (hφ : φ ≫ Q.idealSheaf.subschemeι = E.idealSheaf.subschemeι ≫ h)
    (hη : h E.genericPoint = Q.genericPoint) :
    have := E.integral
    have := Q.integral
    φ (genericPoint E.idealSheaf.subscheme) = genericPoint Q.idealSheaf.subscheme := by
  apply Q.idealSheaf.subschemeι.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply, subschemeι_genericPoint, hη,
    subschemeι_genericPoint]

/-- A scheme finite and surjective over a prime divisor `P` has the dimension of `P`. -/
private theorem topologicalKrullDim_eq_of_surjective {X N : Scheme.{u}}
    (P : MMP.Mori.PrimeDivisor X) (ν : N ⟶ P.idealSheaf.subscheme) [IsFinite ν] [Surjective ν] :
    topologicalKrullDim N = topologicalKrullDim (closure ({P.genericPoint} : Set X)) := by
  rw [topologicalKrullDim_eq_of_isIntegralHom_of_surjective ν,
    (P.idealSheaf.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph
      |>.topologicalKrullDim_eq,
    Scheme.IdealSheafData.range_subschemeι]
  change topologicalKrullDim (P.support : Set X) = _
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- **The restriction to a strict transform is birational.** If `h(η_E) = η_Q` and `h` is an
isomorphism on the stalks at `η_E`, the morphism `φ : E ⟶ Q` induced by `h` on the reduced
closed subschemes is birational. -/
private theorem isBirational_of_comp_eq_comp {W Z : Scheme.{u}} (h : W ⟶ Z)
    (E : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (φ : E.idealSheaf.subscheme ⟶ Q.idealSheaf.subscheme)
    (hφ : φ ≫ Q.idealSheaf.subschemeι = E.idealSheaf.subschemeι ≫ h)
    (hη : h E.genericPoint = Q.genericPoint) (hiso : IsIso (h.stalkMap E.genericPoint)) :
    have := E.integral
    have := Q.integral
    IsBirational φ := by
  have := E.integral
  have := Q.integral
  have hφη := map_genericPoint_of_comp_eq_comp h E Q φ hφ hη
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hφη]
    exact Set.bijOn_singleton.mpr rfl
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
  subst hx
  have h3 := Scheme.Hom.stalkMap_congr_hom _ _ hφ (genericPoint E.idealSheaf.subscheme)
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h3
  have hsurj : Function.Surjective
      (φ.stalkMap (genericPoint E.idealSheaf.subscheme)).hom := by
    have hh : Function.Surjective (h.stalkMap E.genericPoint).hom :=
      (ConcreteCategory.bijective_of_isIso (h.stalkMap E.genericPoint)).2
    have he := E.idealSheaf.subschemeι.stalkMap_surjective (genericPoint E.idealSheaf.subscheme)
    have hR : Function.Surjective (Q.idealSheaf.subschemeι.stalkMap
        (φ (genericPoint E.idealSheaf.subscheme)) ≫
          φ.stalkMap (genericPoint E.idealSheaf.subscheme)).hom := by
      rw [h3]
      have hisurj : ∀ {A B : CommRingCat.{u}} (e : A ≅ B), Function.Surjective e.hom.hom :=
        fun e y => ⟨e.inv y, by rw [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply]⟩
      exact he.comp (hh.comp (hisurj _))
    exact Function.Surjective.of_comp hR
  have hinj : Function.Injective (φ.stalkMap (genericPoint E.idealSheaf.subscheme)).hom := by
    have hfield : IsField (Q.idealSheaf.subscheme.presheaf.stalk
        (φ (genericPoint E.idealSheaf.subscheme))) := by
      rw [hφη]; exact Field.toIsField Q.idealSheaf.subscheme.functionField
    let := hfield.toField
    exact (φ.stalkMap (genericPoint E.idealSheaf.subscheme)).hom.injective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-! ### Positive presentations of effective `ℝ`-Cartier divisors -/

/-- **Rational positive decomposition.** A real vector `r` lying in an open cone `O` is a positive
combination of rational vectors in `O` satisfying every integral linear relation that `r`
satisfies. -/
private theorem exists_pos_rat_combination {m : ℕ} (r : Fin m → ℝ) {O : Set (Fin m → ℝ)}
    (hO : IsOpen O) (hr : r ∈ O) (hcone : ∀ t ∈ O, ∀ c : ℝ, 0 < c → c • t ∈ O) :
    ∃ (p : ℕ) (l : Fin p → ℝ) (q : Fin p → Fin m → ℚ), (∀ u, 0 < l u) ∧
      (∀ u, (fun j => (q u j : ℝ)) ∈ O) ∧
      (∀ u (c : Fin m → ℤ), ∑ j, (c j : ℝ) * r j = 0 → ∑ j, (c j : ℚ) * q u j = 0) ∧
      r = ∑ u, l u • (fun j => (q u j : ℝ)) := by
  classical
  let V := Submodule.span ℚ (Set.range r)
  have : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range r)
  set d := Module.finrank ℚ V
  let b := Module.finBasis ℚ V
  let v : Fin m → V := fun j => ⟨r j, Submodule.subset_span ⟨j, rfl⟩⟩
  let a : Fin m → Fin d → ℚ := fun j i => b.repr (v j) i
  let A : Matrix (Fin m) (Fin d) ℝ := fun j i => (a j i : ℝ)
  let Φ := Matrix.mulVecLin A
  have hΦapp : ∀ t j, Φ t j = ∑ i, (a j i : ℝ) * t i := fun t j => rfl
  have hΦc : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
  let ω : Fin d → ℝ := fun i => ((b i : V) : ℝ)
  have hω : Φ ω = r := by
    funext j
    have h := congrArg Subtype.val (b.sum_repr (v j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] at h
    rwa [hΦapp]
  have hrel : ∀ c : Fin m → ℤ, ∑ j, (c j : ℝ) * r j = 0 → ∀ i, ∑ j, (c j : ℚ) * a j i = 0 := by
    intro c hc i
    have hV : ∑ j, (c j : ℚ) • v j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, v, Rat.cast_intCast,
        Submodule.coe_zero]
      exact hc
    simpa [map_sum, a] using congrArg (fun w => b.repr w i) hV
  -- rational points of the parameter space
  let qv : (Fin d → ℚ) → Fin m → ℚ := fun t j => ∑ i, a j i * t i
  have hqv : ∀ t : Fin d → ℚ, (fun j => (qv t j : ℝ)) = Φ (fun i => (t i : ℝ)) := fun t => by
    funext j; simp [qv, hΦapp]
  have hqrel : ∀ (t : Fin d → ℚ) (c : Fin m → ℤ), ∑ j, (c j : ℝ) * r j = 0 →
      ∑ j, (c j : ℚ) * qv t j = 0 := by
    intro t c hc
    calc ∑ j, (c j : ℚ) * qv t j = ∑ i, t i * ∑ j, (c j : ℚ) * a j i := by
          simp only [qv, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hrel c hc]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `V = 0`, so `r = 0`
    refine ⟨0, Fin.elim0, Fin.elim0, fun u => u.elim0, fun u => u.elim0, fun u => u.elim0, ?_⟩
    rw [← hω]
    funext j
    rw [hΦapp]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
    have : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    simp
  -- a small rational box around `ω`
  have hO' : IsOpen (Φ ⁻¹' O) := hO.preimage hΦc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO' ω (by rw [Set.mem_preimage, hω]; exact hr)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn (div_pos hε (by linarith : (0 : ℝ) < d + 1))
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδε' : ((d : ℝ) + 1) * δ < ε := by
    rw [lt_div_iff₀ (by linarith)] at hδε; linarith
  have hdense : DenseRange (fun t : Fin d → ℚ => fun i => (t i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨t, ht⟩ := hdense.exists_dist_lt ω hδ0'
  have hti : ∀ i, |ω i - t i| < δ := fun i => by
    have := (dist_le_pi_dist ω (fun i => (t i : ℝ)) i).trans_lt ht
    rwa [Real.dist_eq] at this
  -- the vertices `t / d ± δ eᵢ` and their weights
  let u : Fin d × Bool → Fin d → ℚ := fun p =>
    (1 / (d : ℚ)) • t + (if p.2 then δ else -δ) • Pi.single p.1 1
  let α : Fin d → ℝ := fun i => (1 + (ω i - t i) / δ) / 2
  let wt : Fin d × Bool → ℝ := fun p => if p.2 then α p.1 else 1 - α p.1
  have hα : ∀ i, 0 < α i ∧ α i < 1 := fun i => by
    have h1 := hti i
    rw [abs_lt] at h1
    have h2 : -1 < (ω i - t i) / δ := by rw [lt_div_iff₀ hδ0']; linarith
    have h3 : (ω i - t i) / δ < 1 := by rw [div_lt_iff₀ hδ0']; linarith
    constructor <;> simp only [α] <;> linarith
  have hwt : ∀ p, 0 < wt p := fun p => by
    simp only [wt]; split_ifs
    exacts [(hα p.1).1, by linarith [(hα p.1).2]]
  have hucast : ∀ p, (fun i => ((u p i : ℚ) : ℝ)) =
      (1 / (d : ℝ)) • (fun i => (t i : ℝ)) +
        (if p.2 then (δ : ℝ) else -(δ : ℝ)) • (Pi.single p.1 (1 : ℝ) : Fin d → ℝ) := fun p => by
    funext i
    simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = p.1
    · subst hi; split_ifs <;> push_cast <;> simp
    · split_ifs <;> push_cast <;> simp [hi]
  have hsum : ∑ p, wt p • (fun i => ((u p i : ℚ) : ℝ)) = ω := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hucast, Pi.add_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, wt, ite_true, Bool.false_eq_true, ite_false]
    have : ∀ j : Fin d, α j * (1 / (d : ℝ) * (t i : ℝ) + δ * (Pi.single j (1 : ℝ) : Fin d → ℝ) i) +
        (1 - α j) * (1 / (d : ℝ) * (t i : ℝ) + -δ * (Pi.single j (1 : ℝ) : Fin d → ℝ) i) =
        1 / (d : ℝ) * (t i : ℝ) + (2 * α j - 1) * δ * (Pi.single j (1 : ℝ) : Fin d → ℝ) i :=
      fun j => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hsingle : ∑ j : Fin d, (2 * α j - 1) * (δ : ℝ) * (Pi.single j (1 : ℝ) : Fin d → ℝ) i =
        (2 * α i - 1) * δ := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
        (by simp)]
      simp
    rw [hsingle]
    simp only [α]
    field_simp
    ring
  -- the vertices lie in `Φ⁻¹ O`
  have hmem : ∀ p, Φ (fun i => ((u p i : ℚ) : ℝ)) ∈ O := fun p => by
    have hball' : (d : ℝ) • (fun i => ((u p i : ℚ) : ℝ)) ∈ Metric.ball ω ε := by
      rw [hucast, smul_add, smul_smul, mul_one_div_cancel hdR.ne', one_smul, smul_smul,
        Metric.mem_ball]
      set y : Fin d → ℝ := ((d : ℝ) * if p.2 then (δ : ℝ) else -δ) •
        (Pi.single p.1 (1 : ℝ) : Fin d → ℝ) with hy
      have hyn : ‖y‖ ≤ d * δ := by
        have h1 : ‖(Pi.single p.1 (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg zero_le_one]
          intro i; by_cases hi : i = p.1 <;> simp [hi]
        rw [hy, norm_smul]
        calc ‖((d : ℝ) * if p.2 then (δ : ℝ) else -δ)‖ * ‖(Pi.single p.1 (1 : ℝ) : Fin d → ℝ)‖
            ≤ ‖((d : ℝ) * if p.2 then (δ : ℝ) else -δ)‖ * 1 :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = d * δ := by
              rw [mul_one, norm_mul]
              split_ifs <;> simp only [norm_neg, Real.norm_eq_abs, abs_of_pos hδ0', abs_of_pos hdR]
      calc dist ((fun i => (t i : ℝ)) + y) ω
          ≤ dist (fun i => (t i : ℝ)) ω + ‖y‖ := by
            rw [dist_eq_norm, dist_eq_norm,
              show (fun i => (t i : ℝ)) + y - ω = ((fun i => (t i : ℝ)) - ω) + y by abel]
            exact norm_add_le _ _
        _ < δ + d * δ := add_lt_add_of_lt_of_le (by rw [dist_comm]; exact ht) hyn
        _ < ε := by linarith
    have h1 := hcone _ (hball hball') (1 / (d : ℝ)) (by positivity)
    rwa [← map_smul, smul_smul, one_div_mul_cancel hdR.ne', one_smul] at h1
  -- reindex by `Fin p`
  let e := Fintype.equivFin (Fin d × Bool)
  refine ⟨Fintype.card (Fin d × Bool), fun n => wt (e.symm n), fun n => qv (u (e.symm n)),
    fun n => hwt _, fun n => by rw [hqv]; exact hmem _, fun n c hc => hqrel _ c hc, ?_⟩
  rw [← hω, ← hsum, map_sum, ← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, hqv]

/-- Clearing denominators of finitely many rationals. -/
private lemma exists_pos_nat_mul_eq_intCast {m : ℕ} (q : Fin m → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ n : Fin m → ℤ, ∀ j, (N : ℚ) * q j = n j := by
  refine ⟨∏ j, (q j).den, Finset.prod_pos fun j _ => (q j).den_pos, ?_⟩
  have h : ∀ j, ∃ K : ℕ, ∏ i, (q i).den = (q j).den * K := fun j =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  choose K hK using h
  refine ⟨fun j => K j * (q j).num, fun j => ?_⟩
  rw [hK j]
  push_cast
  rw [mul_comm ((q j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- **Positive presentation.** An effective `ℝ`-Cartier divisor `F` on a normal scheme is a
combination `∑ s_u D_u` with `s_u > 0` of effective Cartier divisors `D_u` with
`Supp D_u = Supp F`. -/
private theorem exists_pos_presentation {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {F : RDivisor X} (hF : IsCartierCombination F) (hFeff : F.IsEffective) :
    ∃ (p : ℕ) (s : Fin p → ℝ) (D : Fin p → Divisor X), (∀ u, 0 < s u) ∧
      (∀ u, (D u).IsCartier) ∧ (∀ u, 0 ≤ D u) ∧ (∀ u, (D u).supp = F.supp) ∧
      F = ∑ u, s u • Divisor.toRDivisor (D u) := by
  classical
  obtain ⟨m, r, L, hL, hFeq⟩ := hF
  have hFeq' : F = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hFeq
  have hFP : ∀ P, F P = ∑ j, r j * (L j P) := fun P => by
    rw [hFeq']
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    rfl
  let O : Set (Fin m → ℝ) := {t | ∀ P ∈ F.support, 0 < ∑ j, t j * (L j P)}
  have hOopen : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    exact isOpen_biInter_finset fun P _ => isOpen_lt continuous_const (by fun_prop)
  have hrO : r ∈ O := fun P hP => by
    rw [← hFP]
    exact lt_of_le_of_ne (hFeff P) (Ne.symm (Finsupp.mem_support_iff.mp hP))
  have hcone : ∀ t ∈ O, ∀ c : ℝ, 0 < c → c • t ∈ O := fun t ht c hc P hP => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    exact mul_pos hc (ht P hP)
  obtain ⟨p, l, q, hl, hqO, hqrel, hrq⟩ := exists_pos_rat_combination r hOopen hrO hcone
  choose N hN n hn using fun u => exists_pos_nat_mul_eq_intCast (q u)
  let D : Fin p → Divisor X := fun u => ∑ j, n u j • L j
  have hDc : ∀ u, (D u).IsCartier := fun u =>
    Divisor.cartierSubgroup.sum_mem fun j _ => (hL j).zsmul (n u j)
  have hDP : ∀ u P, ((D u P : ℤ) : ℚ) = N u * ∑ j, q u j * (L j P) := fun u P => by
    simp only [D, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_sum,
      Int.cast_mul, Finset.mul_sum, ← hn, mul_assoc]
  have hzero : ∀ u P, P ∉ F.support → ∑ j, q u j * (L j P) = 0 := fun u P hP => by
    have hrel := hqrel u (fun j => L j P) (by
      rw [Finsupp.notMem_support_iff, hFP] at hP
      rw [← hP]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [← hrel]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hpos : ∀ u P, P ∈ F.support → 0 < ∑ j, q u j * (L j P) := fun u P hP => by
    have h : (0 : ℝ) < ∑ j, (q u j : ℝ) * ((L j P : ℤ) : ℝ) := hqO u P hP
    exact_mod_cast h
  have hNq : ∀ u, (0 : ℚ) < N u := fun u => by exact_mod_cast hN u
  have hDzero : ∀ u P, P ∉ F.support → D u P = 0 := fun u P hP => by
    have : ((D u P : ℤ) : ℚ) = 0 := by rw [hDP, hzero u P hP, mul_zero]
    exact_mod_cast this
  have hDsupp' : ∀ u, (D u).support = F.support := fun u => by
    ext P
    rw [Finsupp.mem_support_iff]
    refine ⟨fun hD => by_contra fun hP => hD (hDzero u P hP), fun hP hD => ?_⟩
    have := hDP u P
    rw [hD, Int.cast_zero] at this
    exact (mul_pos (hNq u) (hpos u P hP)).ne' this.symm
  refine ⟨p, fun u => l u / N u, D, fun u => div_pos (hl u) (by exact_mod_cast hN u), hDc,
    fun u P => ?_, fun u => by simp only [DivisorWithCoeffs.supp, hDsupp' u], ?_⟩
  · by_cases hP : P ∈ F.support
    · have : (0 : ℚ) ≤ D u P := by rw [hDP]; exact (mul_pos (hNq u) (hpos u P hP)).le
      exact_mod_cast this
    · exact (hDzero u P hP).ge
  · have hr : ∀ j, r j = ∑ u, l u * q u j := fun j => by
      simpa [Finset.sum_apply] using congrFun hrq j
    have hDR : ∀ u P, ((D u P : ℤ) : ℝ) = N u * ∑ j, (q u j : ℝ) * (L j P) := fun u P => by
      have := congrArg (fun z : ℚ => (z : ℝ)) (hDP u P)
      push_cast at this
      exact this
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, hFP]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    change _ = ∑ u, l u / N u * ((D u P : ℤ) : ℝ)
    simp only [hDR, hr]
    have hNr : ∀ u, ((N u : ℕ) : ℝ) ≠ 0 := fun u => by exact_mod_cast (hN u).ne'
    simp only [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ (hNr _)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => ?_
    field_simp

end Helpers

section Main

/-- The criterion for normal varieties `W` of dimension `d`. -/
private def EqCrit (k : Type u) [Field k] (d : WithBot ℕ∞) : Prop :=
  ∀ (Z W : Scheme.{u}) (sZ : Z ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [QuasiCompact sW]
    [IsLocallyNoetherian W] [IsNormal W], IsNormalVariety k sZ → IsNormalVariety k sW →
    ∀ (h : W ⟶ Z), h ≫ sZ = sW → IsProper h → IsBirationalMorphism h →
    ∀ (F : RDivisor W), IsCartierCombination F → F.IsEffective →
      (∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → F.coeff P = 0) →
      IsRelativelyNef k sW h (-F) → ∀ b : Z, IsNumericallyTrivialOverPoint k sW h F b →
      topologicalKrullDim W = d → Disjoint (h.base ⁻¹' {b}) (F.supp : Set W)

/-- **All components over `b`.** If every component of `F` has generic point mapping to `b`, and
`F · C = 0` for every contracted curve whose image lies in `closure {b}`, then `Supp F` is
empty. -/
private theorem false_of_forall_map_genericPoint_eq (k : Type u) [Field k] {Z W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W]
    [IsNormal W] (hZ : IsNormalVariety k sZ) (hW : IsNormalVariety k sW) (h : W ⟶ Z)
    (hh : h ≫ sZ = sW) [IsProper h] (hhb : IsBirationalMorphism h) {F : RDivisor W}
    (hF : IsCartierCombination F) (hFeff : F.IsEffective)
    (hnef : IsRelativelyNef k sW h (-F)) (b : Z)
    (hall : ∀ P : Mori.PrimeDivisor W, F.coeff P ≠ 0 → h P.genericPoint = b)
    (htriv : ∀ C : ProperCurve sW, C.IsContractedBy h → h C.point ∈ closure {b} →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
        IsRIntersectionNumber k sW F r L C x → x = 0)
    (hFexc : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → F.coeff P = 0)
    (w : W) (hw : w ∈ F.supp) : False := by
  classical
  -- `F · C = 0` on every contracted curve
  have hzero : ∀ C : ProperCurve sW, C.IsContractedBy h →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
        IsRIntersectionNumber k sW F r L C x → x = 0 := by
    intro C hC m r L x hx
    by_cases hz : h C.point ∈ closure {b}
    · exact htriv C hC hz m r L x hx
    · have hCS : C.point ∉ F.supp := by
        intro hmem
        obtain ⟨P, hP, hCP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
        apply hz
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hCP
        rw [← hall P hP]
        exact specializes_iff_mem_closure.mp
          ((specializes_iff_mem_closure.mpr hCP).map h.continuous)
      have h1 := IsRIntersectionNumber.nonneg_of_isEffective k sW hW F hF hFeff C hCS r L hx
      linarith [nonpos_of_isRelativelyNef_neg hnef C hC hx]
  -- so `F` is `h`-nef, and the negativity lemma applies to `-F`
  have hFnef : IsRelativelyNef k sW h F := by
    obtain ⟨m, r, L, hL, hFeq⟩ := hF
    refine ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hFeq,
      fun C hC x hx => (hzero C hC m r L x hx).ge⟩
  have hneg := (isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    k sZ sW hZ hW h hh hhb (isCartierCombination_neg hF)
    (fun P hP => by rw [DivisorWithCoeffs.coeff_neg, hFexc P hP, neg_zero])
    (by rwa [neg_neg])).1
  obtain ⟨P, hP, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
  have h2 := hneg P
  rw [DivisorWithCoeffs.coeff_neg] at h2
  exact hP (le_antisymm (by linarith) (hFeff P))

/-- **Some component over a larger set.** If some component of `F` maps to a point other than `b`,
the fibre over `b` cannot meet `Supp F`, assuming the criterion in all lower dimensions. -/
private theorem false_of_exists_map_genericPoint_ne (k : Type u) [Field k] {d : WithBot ℕ∞}
    (ih : ∀ d' < d, EqCrit k d') {Z W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W]
    [IsNormal W] (hZ : IsNormalVariety k sZ) (hW : IsNormalVariety k sW) (h : W ⟶ Z)
    (hh : h ≫ sZ = sW) [IsProper h] (hhb : IsBirationalMorphism h) {F : RDivisor W}
    (hF : IsCartierCombination F) (hFeff : F.IsEffective)
    (hFexc : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → F.coeff P = 0)
    (hnef : IsRelativelyNef k sW h (-F)) (b : Z) [IsAffine Z]
    (hgen : ∀ P : Mori.PrimeDivisor W, F.coeff P ≠ 0 → h P.genericPoint ⤳ b)
    (P₀ : Mori.PrimeDivisor W) (hP₀ : F.coeff P₀ ≠ 0) (hP₀b : h P₀.genericPoint ≠ b)
    (htriv : ∀ C : ProperCurve sW, C.IsContractedBy h → h C.point ∈ closure {b} →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
        IsRIntersectionNumber k sW F r L C x → x = 0)
    (hdim : topologicalKrullDim W ≤ d) (w : W) (hwb : h w = b) (hw : w ∈ F.supp) : False := by
  classical
  have := hZ.1
  have := hW.1
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsIntegral W := hW.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  have : IsSeparated sW := hW.1.toIsSeparated
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have hWh : IsNormalVariety k (h ≫ sZ) := hh ▸ hW
  -- coheights of the images of the components
  obtain ⟨nZ, hnZ⟩ := exists_topologicalKrullDim_eq_natCast sZ
  have hfin : ∀ z : Z, Order.coheight z < ⊤ := fun z => by
    obtain ⟨a, c, n, -, hc, -, -⟩ := exists_nat_closure_coheight sZ z
    rw [hc]
    exact ENat.natCast_lt_top c
  have hexc2 : ∀ P : Mori.PrimeDivisor W, F.coeff P ≠ 0 → 2 ≤ Order.coheight (h P.genericPoint) :=
    fun P hP => (isExceptionalPrimeDivisor_iff_two_le_coheight hZ h hWh hhb P).mp
      (not_not.mp (mt (hFexc P) hP))
  have hlt_of : ∀ {x y : Z}, x ⤳ y → x ≠ y → Order.coheight x < Order.coheight y :=
    fun {x y} hxy hne => Order.coheight_strictAnti
      ⟨hxy, fun hyx => hne (hxy.antisymm hyx).eq⟩ (hfin x)
  have hb3 : 3 ≤ Order.coheight b :=
    Order.add_one_le_of_lt ((hexc2 P₀ hP₀).trans_lt (hlt_of (hgen P₀ hP₀) hP₀b))
  have hbη : b ≠ genericPoint Z := by
    rintro rfl
    have h0 : Order.coheight (genericPoint Z) = 0 :=
      Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
    rw [h0] at hb3
    exact absurd hb3 (by decide)
  -- the prime divisor `Q`
  let S : Finset Z := (F.support.filter fun P => h P.genericPoint ≠ b).image
    fun P => h P.genericPoint
  have hS : ∀ s ∈ S, s ⤳ b ∧ s ≠ b := by
    intro s hs
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hP1, hP2⟩ := Finset.mem_filter.mp hP
    exact ⟨hgen P (Finsupp.mem_support_iff.mp hP1), hP2⟩
  obtain ⟨Q, hQb, hQS⟩ := exists_primeDivisor_specializes_and_not_specializes b S hS hbη
  have hQnot : ∀ P : Mori.PrimeDivisor W, F.coeff P ≠ 0 → h P.genericPoint ≠ b →
      ¬ Q.genericPoint ⤳ h P.genericPoint := fun P hP hPb =>
    hQS _ (Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hP, hPb⟩,
      rfl⟩)
  have hQc : Order.coheight Q.genericPoint = 1 := Q.coheight_genericPoint
  -- the strict transform `E` of `Q`
  obtain ⟨E, hEQ, hEiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hZ hWh hhb Q
  have hFE : F.coeff E = 0 :=
    hFexc E (not_isExceptionalPrimeDivisor_of_coheight_eq_one hZ h E (by rw [hEQ]; exact hQc))
  have hηE : E.genericPoint ∉ F.supp := genericPoint_notMem_supp_of_coeff_eq_zero hFE
  -- `F = ∑ s_u D_u`
  obtain ⟨p, s, D, hs, hDc, hD0, hDsupp, hFD⟩ := exists_pos_presentation hF hFeff
  -- the normalizations `W₁ = E^ν` and `Z₁ = Q^ν`, and `h₁ : W₁ ⟶ Z₁`
  have := E.integral
  have := Q.integral
  obtain ⟨W₁, νE, hW₁, hνEfin, hνEsurj, hνEb, -⟩ := exists_normalization_primeDivisor sW hW E
  obtain ⟨Z₁, νQ, hZ₁, hνQfin, hνQsurj, hνQb, hUPQ⟩ := exists_normalization_primeDivisor sZ hZ Q
  have : IsIntegral W₁ := hW₁.1.toIsIntegral
  have : IsNormal W₁ := hW₁.2
  have : IsIntegral Z₁ := hZ₁.1.toIsIntegral
  have : IsNormal Z₁ := hZ₁.2
  have hrange : Set.range (E.idealSheaf.subschemeι ≫ h) ⊆ Q.idealSheaf.support := by
    rintro _ ⟨x, rfl⟩
    have hx : E.idealSheaf.subschemeι x ∈ closure {E.genericPoint} := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact (E.idealSheaf.range_subschemeι ▸ Set.mem_range_self x :)
    have : h (E.idealSheaf.subschemeι x) ∈ closure {Q.genericPoint} := by
      rw [← hEQ]
      exact map_mem_closure h.continuous hx fun y hy => by rw [Set.mem_singleton_iff.mp hy]; rfl
    rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
  let φ := IsClosedImmersion.lift Q.idealSheaf.subschemeι (E.idealSheaf.subschemeι ≫ h)
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_ker_of_range_subset _ _ hrange)
  have hφ : φ ≫ Q.idealSheaf.subschemeι = E.idealSheaf.subschemeι ≫ h :=
    IsClosedImmersion.lift_fac _ _ _
  have hφb : IsBirational φ := isBirational_of_comp_eq_comp h E Q φ hφ hEQ hEiso
  have hb' : IsBirational (νE ≫ φ) := hνEb.comp hφb
  have : IsDominant (νE ≫ φ) := hb'.isDominant
  obtain ⟨h₁, hh₁⟩ := hUPQ W₁ (νE ≫ φ)
  set j : W₁ ⟶ W := νE ≫ E.idealSheaf.subschemeι with hj
  set ν : Z₁ ⟶ Z := νQ ≫ Q.idealSheaf.subschemeι with hν
  have hcomm : h₁ ≫ ν = j ≫ h := by
    rw [hν, hj, ← Category.assoc, hh₁, Category.assoc, hφ, Category.assoc]
  have : IsFinite j := by rw [hj]; infer_instance
  have : IsFinite ν := by rw [hν]; infer_instance
  have : IsProper (h₁ ≫ ν) := by rw [hcomm]; infer_instance
  have : IsProper h₁ := IsProper.of_comp h₁ ν
  have hW₁' : IsNormalVariety k (j ≫ sW) := by rw [hj, Category.assoc]; exact hW₁
  have hZ₁' : IsNormalVariety k (ν ≫ sZ) := by rw [hν, Category.assoc]; exact hZ₁
  have hh₁s : h₁ ≫ ν ≫ sZ = j ≫ sW := by rw [← Category.assoc, hcomm, Category.assoc, hh]
  have : QuasiCompact (j ≫ sW) := hW₁'.1.toQuasiCompact
  have : LocallyOfFiniteType (j ≫ sW) := hW₁'.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W₁ := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sW)
  have : CompactSpace W₁ := QuasiCompact.compactSpace_of_compactSpace (j ≫ sW)
  have : LocallyOfFiniteType (ν ≫ sZ) := hZ₁'.1.toLocallyOfFiniteType
  have : QuasiCompact (ν ≫ sZ) := hZ₁'.1.toQuasiCompact
  have : CompactSpace Z₁ := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sZ)
  -- generic points
  have : IsDominant νE := hνEb.isDominant
  have : IsDominant νQ := hνQb.isDominant
  have hνEη : νE (genericPoint W₁) = genericPoint E.idealSheaf.subscheme :=
    genericPoint_eq_of_isDominant νE
  have hνQη : νQ (genericPoint Z₁) = genericPoint Q.idealSheaf.subscheme :=
    genericPoint_eq_of_isDominant νQ
  have hjη : j (genericPoint W₁) = E.genericPoint := by
    rw [hj, Scheme.Hom.comp_apply, hνEη]; rfl
  have hφη := map_genericPoint_of_comp_eq_comp h E Q φ hφ hEQ
  have hh₁η : h₁ (genericPoint W₁) = genericPoint Z₁ := by
    have h1 : νQ (h₁ (genericPoint W₁)) = νQ (genericPoint Z₁) := by
      rw [← Scheme.Hom.comp_apply, hh₁, Scheme.Hom.comp_apply, hνEη, hφη, hνQη]
    exact (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite νQ (genericPoint_specializes _)
      h1.symm).symm
  have hh₁bir : IsBirational h₁ := isBirational_of_comp h₁ νQ (hh₁ ▸ hb') hνQb hh₁η
  have hh₁b : IsBirationalMorphism h₁ := isBirationalMorphism_of_isBirational h₁ hh₁bir
  -- the pull-back `F₁ = ∑ s_u j^* D_u`
  have hBu : ∀ u, ∀ Z' : irreducibleComponents W₁, j (componentGenericPoint W₁ Z') ∉ (D u).supp :=
    fun u Z' => by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjη, hDsupp u]; exact hηE
  let D₁ : Fin p → Divisor W₁ := fun u => (D u).pullback (hDc u) (hBu u)
  have hD₁c : ∀ u, (D₁ u).IsCartier := fun u => (hDc u).isCartier_pullback j (hBu u)
  have hD₁pb : ∀ u, (D u).IsPullback j (hBu u) (D₁ u) := fun u =>
    Divisor.isPullback_pullback (hDc u) (hBu u)
  have hgenmem : ∀ P : Mori.PrimeDivisor W₁, P.genericPoint ∈ P.support := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hD₁0 : ∀ u, 0 ≤ D₁ u := fun u E₁ =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hDc u) (V := ⊤)
      (fun P _ => hD0 u P) (hD₁pb u) E₁ ⟨E₁.genericPoint, hgenmem E₁, trivial⟩
  have hD₁supp : ∀ u, ((D₁ u).supp : Set W₁) = j ⁻¹' (F.supp : Set W) := fun u => by
    rw [MMP.Flips.supp_eq_preimage_supp_of_isPullback (hDc u)
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (hD0 u)) (hD₁pb u), hDsupp u]
  set F₁ : RDivisor W₁ := ∑ u, s u • Divisor.toRDivisor (D₁ u) with hF₁def
  have hF₁ : IsCartierCombination F₁ :=
    ⟨p, s, D₁, hD₁c, by simp only [hF₁def, toRDivisor_eq_mapCoeffs]⟩
  have hF₁P : ∀ P, F₁.coeff P = ∑ u, s u * ((D₁ u P : ℤ) : ℝ) := fun P => by
    rw [hF₁def]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rfl
  have hsD₁ : ∀ u P, 0 ≤ s u * ((D₁ u P : ℤ) : ℝ) := fun u P =>
    mul_nonneg (hs u).le (by exact_mod_cast hD₁0 u P)
  have hF₁eff : F₁.IsEffective := fun P => by
    rw [hF₁P]; exact Finset.sum_nonneg fun u _ => hsD₁ u P
  have hF₁supp : ∀ w₁ : W₁, w₁ ∈ F₁.supp → j w₁ ∈ F.supp := by
    intro w₁ hw₁
    obtain ⟨P, hP, hwP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw₁
    rw [hF₁P] at hP
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
    have hDu : (D₁ u).coeff P ≠ 0 := fun h0 => hu (by
      rw [DivisorWithCoeffs.coeff_apply] at h0; rw [h0]; simp)
    have : w₁ ∈ ((D₁ u).supp : Set W₁) := DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hDu, hwP⟩
    rwa [hD₁supp] at this
  have hF₁supp' : ∀ w₁ : W₁, j w₁ ∈ F.supp → ∀ u₀ : Fin p, w₁ ∈ F₁.supp := by
    intro w₁ hw₁ u₀
    have : w₁ ∈ ((D₁ u₀).supp : Set W₁) := by rw [hD₁supp]; exact hw₁
    obtain ⟨P, hP, hwP⟩ := DivisorWithCoeffs.mem_supp_iff.mp this
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, hwP⟩
    rw [hF₁P]
    have h0 : (0 : ℝ) < ((D₁ u₀ P : ℤ) : ℝ) := by
      have h1 := hD₁0 u₀ P
      exact_mod_cast lt_of_le_of_ne h1 (Ne.symm hP)
    exact (lt_of_lt_of_le (mul_pos (hs u₀) h0)
      (Finset.single_le_sum (fun u _ => hsD₁ u P) (Finset.mem_univ u₀))).ne'
  -- `ν` lands in `Q`
  have hνQ : ∀ z₁ : Z₁, Q.genericPoint ⤳ ν z₁ := fun z₁ => by
    have : ν z₁ ∈ Q.support := by
      rw [hν, Scheme.Hom.comp_apply]
      exact (Q.idealSheaf.range_subschemeι ▸ Set.mem_range_self _ :)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
    exact specializes_iff_mem_closure.mpr this
  have hνh₁ : ∀ x : W₁, ν (h₁ x) = h (j x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  -- dimensions of `Z₁`
  obtain ⟨aQ, cQ, nQ, haQ, hcQ, hnQ, hacnQ⟩ := exists_nat_closure_coheight sZ Q.genericPoint
  have hnQ' : nQ = nZ := by rw [hnZ] at hnQ; exact_mod_cast hnQ.symm
  have hcQ1 : cQ = 1 := by rw [hQc] at hcQ; exact_mod_cast hcQ.symm
  have hdimZ₁ : topologicalKrullDim Z₁ = aQ := by
    rw [topologicalKrullDim_eq_of_surjective Q νQ, haQ]
  -- the components of `F₁` are exceptional over `Z₁`
  have hZ₁h : IsNormalVariety k (h₁ ≫ ν ≫ sZ) := hh₁s ▸ hW₁'
  have hF₁exc : ∀ P₁ : Mori.PrimeDivisor W₁, ¬ IsExceptionalPrimeDivisor (ν ≫ sZ) h₁ P₁ →
      F₁.coeff P₁ = 0 := by
    intro P₁ hP₁
    by_contra hne
    apply hP₁
    rw [isExceptionalPrimeDivisor_iff_two_le_coheight hZ₁' h₁ hZ₁h hh₁b P₁]
    have hηP₁ : P₁.genericPoint ∈ F₁.supp :=
      DivisorWithCoeffs.mem_supp_iff.mpr ⟨P₁, hne, hgenmem P₁⟩
    obtain ⟨P, hP, hjP⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hF₁supp _ hηP₁)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hjP
    have hPy : h P.genericPoint ⤳ ν (h₁ P₁.genericPoint) := by
      rw [hνh₁]; exact (specializes_iff_mem_closure.mpr hjP).map h.continuous
    have hy3 : 3 ≤ Order.coheight (ν (h₁ P₁.genericPoint)) := by
      by_cases hPb : h P.genericPoint = b
      · rw [hPb] at hPy; exact hb3.trans (Order.coheight_anti hPy)
      · have hne' : h P.genericPoint ≠ ν (h₁ P₁.genericPoint) := fun heq =>
          hQnot P hP hPb (heq ▸ hνQ _)
        exact Order.add_one_le_of_lt ((hexc2 P hP).trans_lt (hlt_of hPy hne'))
    obtain ⟨a, c, n, ha, hc, hn, hacn⟩ := exists_nat_closure_coheight sZ (ν (h₁ P₁.genericPoint))
    obtain ⟨a₁, c₁, n₁, ha₁, hc₁, hn₁, hacn₁⟩ :=
      exists_nat_closure_coheight (ν ≫ sZ) (h₁ P₁.genericPoint)
    have hn' : n = nZ := by rw [hnZ] at hn; exact_mod_cast hn.symm
    have h1 : a₁ ≤ a := by
      have := topologicalKrullDim_closure_le_of_isFinite ν (h₁ P₁.genericPoint)
      rw [ha₁, ha] at this
      exact_mod_cast this
    have h2 : n₁ = aQ := by rw [hdimZ₁] at hn₁; exact_mod_cast hn₁.symm
    have h3 : 3 ≤ c := by rw [hc] at hy3; exact_mod_cast hy3
    rw [hc₁]
    have : 2 ≤ c₁ := by omega
    exact_mod_cast this
  -- `-F₁` is `h₁`-nef
  have hBC : ∀ C : ProperCurve sW, C.IsContractedBy h →
      ∑ u, s u * ((D u).degreeOn k sW C.ι C.dim_le (hDc u) : ℝ) ≤ 0 := fun C hC =>
    nonpos_of_isRelativelyNef_neg hnef C hC
      (hFD ▸ isRIntersectionNumber_sum_degreeOn k sW C s D hDc)
  have hcontr₁ : ∀ C₁ : ProperCurve (j ≫ sW), C₁.IsContractedBy h₁ → C₁.IsContractedBy (j ≫ h) :=
    fun C₁ hC₁ x hx => by
      have h1 : ν (h₁ x) = ν (h₁ C₁.point) := by rw [hC₁ x hx]
      rwa [hνh₁, hνh₁] at h1
  have hnef₁ : IsRelativelyNef k (j ≫ sW) h₁ (-F₁) := by
    obtain ⟨m', r', L', hL', hpres, hall⟩ := isRelativelyNef_neg_sum_pullback j h s D hDc hBu hBC
    exact ⟨m', r', L', hL', hpres, fun C₁ hC₁ x hx => hall C₁ (hcontr₁ C₁ hC₁) x hx⟩
  -- a point `b₁` of `Z₁` over `b`, and `F₁` is numerically trivial over it
  obtain ⟨b₀, hb₀⟩ : b ∈ Set.range Q.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change b ∈ Q.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hQb
  obtain ⟨b₁, hb₁⟩ := νQ.surjective b₀
  have hνb₁ : ν b₁ = b := by rw [hν, Scheme.Hom.comp_apply, hb₁, hb₀]
  have htriv₁ : IsNumericallyTrivialOverPoint k (j ≫ sW) h₁ F₁ b₁ := by
    refine ⟨hF₁, ⊤, trivial, fun C₁ hC₁ _ hcl _ m' r' L' x hx => ?_⟩
    have hx0 := isRIntersectionNumber_sum_degreeOn k (j ≫ sW) C₁ s D₁ hD₁c
    rw [(IsRIntersectionNumber.eq_and_linear k (j ≫ sW) C₁).1 _ _ _ _ _ _ _ hx hx0]
    by_cases hc : IsProperCurve sW (j C₁.point)
    · let C : ProperCurve sW := ⟨_, hc⟩
      have hCh : C.IsContractedBy h := by
        intro y hy
        have hsub : closure ({j C₁.point} : Set W) ⊆ j '' closure ({C₁.point} : Set W₁) :=
          closure_minimal (Set.singleton_subset_iff.2 ⟨C₁.point, subset_closure rfl, rfl⟩)
            (j.isClosedMap _ isClosed_closure)
        obtain ⟨z, hz, rfl⟩ := hsub hy
        simpa only [Scheme.Hom.comp_apply] using hcontr₁ C₁ hC₁ z hz
      have hCb : h C.point ∈ closure {b} := by
        change h (j C₁.point) ∈ closure {b}
        rw [← hνh₁, ← hνb₁]
        exact map_mem_closure ν.continuous hcl fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]; rfl
      have hF0 := htriv C hCh hCb p s D _ (by
        rw [hFD]; exact isRIntersectionNumber_sum_degreeOn k sW C s D hDc)
      simp only [D₁, degreeOn_pullback_eq_mul j (hDc _) (hBu _) C₁ C rfl, Int.cast_mul,
        Int.cast_natCast, mul_left_comm (s _), ← Finset.mul_sum, hF0, mul_zero]
    · simp [D₁, degreeOn_pullback_eq_zero j (hDc _) (hBu _) C₁ hc]
  -- `dim W₁ < dim W`
  obtain ⟨aE, cE, nW, haE, hcE, hnW, hacnE⟩ := exists_nat_closure_coheight sW E.genericPoint
  have hcE1 : cE = 1 := by rw [E.coheight_genericPoint] at hcE; exact_mod_cast hcE.symm
  have hdimW₁ : topologicalKrullDim W₁ = aE := by
    rw [topologicalKrullDim_eq_of_surjective E νE, haE]
  have hlt : topologicalKrullDim W₁ < d := by
    refine lt_of_lt_of_le ?_ hdim
    rw [hdimW₁, hnW]
    exact_mod_cast (show aE < nW by omega)
  -- the induction hypothesis
  have hdisj := ih _ hlt Z₁ W₁ (ν ≫ sZ) (j ≫ sW) hZ₁' hW₁' h₁ hh₁s inferInstance hh₁b F₁ hF₁
    hF₁eff hF₁exc hnef₁ b₁ htriv₁ rfl
  -- but `h₁⁻¹(b₁)` meets `Supp F₁`
  have hfib : h.base ⁻¹' {b} ⊆ (F.supp : Set W) :=
    (preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sZ sW hZ hW h hh hhb hF
      hFeff hnef b).resolve_right fun hd =>
        Set.disjoint_left.mp hd (show w ∈ h.base ⁻¹' {b} from hwb) hw
  have : IsDominant h₁ := hh₁b.isDominant
  have hsurj₁ : Function.Surjective h₁ := by
    rw [← Set.range_eq_univ, ← h₁.isClosedMap.isClosed_range.closure_eq]
    exact h₁.denseRange.closure_range
  obtain ⟨w₁, hw₁⟩ := hsurj₁ b₁
  have hjw : j w₁ ∈ F.supp := hfib (show h (j w₁) = b by rw [← hνh₁, hw₁, hνb₁])
  have hp : 0 < p := Nat.pos_of_ne_zero fun hp0 => by
    subst hp0
    rw [hFD, Finset.univ_eq_empty, Finset.sum_empty, DivisorWithCoeffs.supp_zero] at hw
    exact hw
  exact Set.disjoint_left.mp hdisj (show w₁ ∈ h₁.base ⁻¹' {b₁} from hw₁) (hF₁supp' w₁ hjw ⟨0, hp⟩)

/-- If the equality criterion holds in every dimension `< d`, it holds in dimension `d`. -/
private theorem eqCrit_of_forall_lt (k : Type u) [Field k] {d : WithBot ℕ∞}
    (ih : ∀ d' < d, EqCrit k d') : EqCrit k d := by
  intro Z W sZ sW _ _ _ hZ hW h hh hp hhb F hF hFeff hFexc hnef b htriv hd
  classical
  have := hZ.1
  have := hW.1
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsIntegral W := hW.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsSeparated sW := hW.1.toIsSeparated
  rw [Set.disjoint_left]
  intro w hwb hwF
  have hwb' : h w = b := hwb
  obtain ⟨-, U, hbU, hU⟩ := htriv
  -- the images of the components of `F` not passing through `b`
  let S := F.support.filter (fun P => ¬ h P.genericPoint ⤳ b)
  let Bad : Set Z := ⋃ P ∈ S, closure {h P.genericPoint}
  have hBad : IsClosed Bad := S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
  have hbBad : b ∉ Bad := by
    simp only [Bad, Set.mem_iUnion, not_exists]
    intro P hP hbP
    exact (Finset.mem_filter.mp hP).2 (specializes_iff_mem_closure.mpr hbP)
  obtain ⟨V, hVa, hbV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (x := b)
    (U := U ⊓ ⟨Badᶜ, hBad.isOpen_compl⟩) ⟨hbU, hbBad⟩
  have hVU : ∀ z ∈ V, z ∈ U ∧ z ∉ Bad := fun z hz => hVsub hz
  -- the restricted situation over `V`
  set W' := h ⁻¹ᵁ V
  set h' : W'.toScheme ⟶ V.toScheme := h ∣_ V
  have hι : ∀ y, V.ι (h' y) = h (W'.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hwW' : w ∈ W' := show h w ∈ V by rw [hwb']; exact hbV
  have : Nonempty W' := ⟨⟨w, hwW'⟩⟩
  have : Nonempty V := ⟨⟨b, hbV⟩⟩
  have : IsAffine V := hVa
  have : IsDominant W'.ι := Opens.isDominant_ι (W'.isOpen.dense ⟨w, hwW'⟩)
  have hW'v := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sW W'
  have hV'v := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sZ V
  have : IsIntegral W' := hW'v.toIsIntegral
  have : IsNormal W' := isNormal_of_isOpenImmersion W'.ι
  have : IsNormal V := isNormal_of_isOpenImmersion V.ι
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace h'
  have : QuasiCompact (W'.ι ≫ sW) := quasiCompact_of_compactSpace _
  have hZ' : IsNormalVariety k (V.ι ≫ sZ) := ⟨hV'v, inferInstance⟩
  have hW' : IsNormalVariety k (W'.ι ≫ sW) := ⟨hW'v, inferInstance⟩
  have hh' : h' ≫ V.ι ≫ sZ = W'.ι ≫ sW := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hh]
  have hh'b : IsBirationalMorphism h' := isBirationalMorphism_morphismRestrict hhb V
  -- the restriction `F' = F|_{W'}`
  obtain ⟨m, r, L, hL, hFeq⟩ := id hF
  have hFeq' : F = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hFeq
  have hBj : ∀ j, ∀ Z' : irreducibleComponents W',
      W'.ι (componentGenericPoint W' Z') ∉ (L j).supp := fun j =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' W'.ι (L j)
  let L' : Fin m → Divisor W' := fun j => (L j).pullback (hL j) (hBj j)
  have hL' : ∀ j, (L' j).IsCartier := fun j => (hL j).isCartier_pullback W'.ι (hBj j)
  set F' : RDivisor W' := ∑ j, r j • Divisor.toRDivisor (L' j) with hF'def
  have hF'coeff : ∀ E, F'.coeff E = F.coeff (OpenWeilRestriction.primeDivisorMap W'.ι E) := by
    intro E
    rw [hF'def, hFeq']
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := coeff_pullback_ι W' (hL j) (hBj j) E
    simp only [DivisorWithCoeffs.coeff_apply] at this
    change r j * ((L' j E : ℤ) : ℝ) = r j * ((L j _ : ℤ) : ℝ)
    rw [this]
  have hF' : IsCartierCombination F' :=
    ⟨m, r, L', hL', by simp only [hF'def, toRDivisor_eq_mapCoeffs]⟩
  -- curves of `W'` and their intersection numbers
  have hcontr : ∀ (C' : ProperCurve (W'.ι ≫ sW)) (C : ProperCurve sW), W'.ι C'.point = C.point →
      closure ({C.point} : Set W) ⊆ W' → C'.IsContractedBy h' → C.IsContractedBy h := by
    intro C' C hC hsub hC' y hy
    obtain ⟨y', rfl⟩ : y ∈ Set.range W'.ι := by rw [Scheme.Opens.range_ι]; exact hsub hy
    have hy' : y' ∈ closure ({C'.point} : Set W') := by
      rw [W'.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
        Set.mem_preimage, hC]
      exact hy
    rw [← hι, ← hC, ← hι, hC' y' hy']
  have hdeg : ∀ (C' : ProperCurve (W'.ι ≫ sW)) (C : ProperCurve sW), W'.ι C'.point = C.point →
      closure ({C.point} : Set W) ⊆ W' → ∀ j,
        ((L' j).degreeOn k (W'.ι ≫ sW) C'.ι C'.dim_le (hL' j) : ℝ) =
          (L j).degreeOn k sW C.ι C.dim_le (hL j) := fun C' C hC hsub j => by
    exact_mod_cast degreeOn_pullback_ι W' (hL j) (hBj j) C C' hC hsub
  have hval : ∀ (C' : ProperCurve (W'.ι ≫ sW)) (C : ProperCurve sW), W'.ι C'.point = C.point →
      closure ({C.point} : Set W) ⊆ W' → ∀ (s : Fin m → ℝ) {m' : ℕ} (r' : Fin m' → ℝ)
        (L'' : Fin m' → Divisor W') (x : ℝ),
        IsRIntersectionNumber k (W'.ι ≫ sW) (∑ j, s j • Divisor.toRDivisor (L' j)) r' L'' C' x →
          IsRIntersectionNumber k sW (∑ j, s j • Divisor.toRDivisor (L j)) s L C x := by
    intro C' C hC hsub s m' r' L'' x hx
    have h1 := isRIntersectionNumber_sum_degreeOn k (W'.ι ≫ sW) C' s L' hL'
    have hxe := (IsRIntersectionNumber.eq_and_linear k (W'.ι ≫ sW) C').1 _ _ _ _ _ _ _ hx h1
    have h2 := isRIntersectionNumber_sum_degreeOn k sW C s L hL
    rw [hxe]
    simpa only [hdeg C' C hC hsub] using h2
  -- the hypotheses over `V`
  have hnef' : IsRelativelyNef k (W'.ι ≫ sW) h' (-F') := by
    have hnegF' : -F' = ∑ j, (fun j => -r j) j • Divisor.toRDivisor (L' j) := by
      rw [hF'def, ← Finset.sum_neg_distrib]; simp [neg_smul]
    refine ⟨m, fun j => -r j, L', hL', hnegF', fun C' hC' x hx => ?_⟩
    obtain ⟨C, hC, hsub⟩ := exists_properCurve_of_opens W' C'
    rw [hnegF'] at hx
    have hx' := hval C' C hC hsub (fun j => -r j) _ L' x hx
    obtain ⟨m₁, r₁, L₁, hL₁, hpres, hall⟩ := hnef
    have hy := isRIntersectionNumber_sum_degreeOn k sW C r₁ L₁ hL₁
    rw [← hpres] at hy
    have hneg : (∑ j, (fun j => -r j) j • Divisor.toRDivisor (L j)) = -F := by
      rw [hFeq', ← Finset.sum_neg_distrib]; simp [neg_smul]
    rw [hneg] at hx'
    rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx' hy]
    exact hall C (hcontr C' C hC hsub hC') _ hy
  have hW'h : IsNormalVariety k (h' ≫ V.ι ≫ sZ) := hh' ▸ hW'
  have hWh : IsNormalVariety k (h ≫ sZ) := hh ▸ hW
  have hF'exc : ∀ E : Mori.PrimeDivisor W', ¬ IsExceptionalPrimeDivisor (V.ι ≫ sZ) h' E →
      F'.coeff E = 0 := by
    intro E hE
    by_contra hne
    rw [hF'coeff] at hne
    have hP := not_not.mp (mt (hFexc _) hne)
    have hη : h (Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap W'.ι E)) =
        V.ι (h' E.genericPoint) := by
      rw [hι]; exact congrArg h (OpenWeilRestriction.genericPoint_primeDivisorMap _ _)
    rw [isExceptionalPrimeDivisor_iff_two_le_coheight hZ h hWh hhb, hη,
      coheight_eq_of_isOpenImmersion] at hP
    exact hE ((isExceptionalPrimeDivisor_iff_two_le_coheight hZ' h' hW'h hh'b E).mpr hP)
  let b' : V.toScheme := ⟨b, hbV⟩
  have hgen' : ∀ E : Mori.PrimeDivisor W', F'.coeff E ≠ 0 → h' E.genericPoint ⤳ b' := by
    intro E hE
    rw [hF'coeff] at hE
    set P := OpenWeilRestriction.primeDivisorMap W'.ι E
    have hPη : h P.genericPoint = V.ι (h' E.genericPoint) := by
      rw [hι]; exact congrArg h (OpenWeilRestriction.genericPoint_primeDivisorMap _ _)
    have hsp : h P.genericPoint ⤳ b := by
      by_contra hns
      refine (hVU _ (show V.ι (h' E.genericPoint) ∈ V from (h' E.genericPoint).2)).2 ?_
      rw [← hPη]
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hE, hns⟩)
        (subset_closure rfl)
    rw [hPη] at hsp
    exact (V.ι.isOpenEmbedding.isInducing.specializes_iff).mp hsp
  have htriv' : ∀ C' : ProperCurve (W'.ι ≫ sW), C'.IsContractedBy h' →
      h' C'.point ∈ closure {b'} →
      ∀ (m' : ℕ) (r' : Fin m' → ℝ) (L'' : Fin m' → Divisor W') (x : ℝ),
        IsRIntersectionNumber k (W'.ι ≫ sW) F' r' L'' C' x → x = 0 := by
    intro C' hC' hcl m' r' L'' x hx
    obtain ⟨C, hC, hsub⟩ := exists_properCurve_of_opens W' C'
    have hx' := hval C' C hC hsub r r' L'' x hx
    rw [← hFeq'] at hx'
    have hCh := hcontr C' C hC hsub hC'
    have hz : h C.point = V.ι (h' C'.point) := by rw [hι, hC]
    refine hU C hCh ?_ ?_ (isClosed_singleton_of_isContractedBy h C hCh) m r L x hx'
    · rw [hz]; exact (hVU _ (h' C'.point).2).1
    · rw [hz]
      exact map_mem_closure V.ι.continuous hcl fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]; rfl
  have hdim' : topologicalKrullDim W' ≤ d := hd ▸ topologicalKrullDim_subspace_le W (W' : Set W)
  let w' : W'.toScheme := ⟨w, hwW'⟩
  have hw'b : h' w' = b' := V.ι.isOpenEmbedding.injective (by rw [hι]; exact hwb')
  have hw'F : w' ∈ F'.supp := by
    obtain ⟨P, hP, hwP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hwF
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwP
    have hsp : P.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hwP
    have hηW' : P.genericPoint ∈ W' := hsp.mem_open W'.isOpen hwW'
    obtain ⟨E, hE⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq W' P hηW'
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, by rw [hF'coeff, hE]; exact hP, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine specializes_iff_mem_closure.mp ((W'.ι.isOpenEmbedding.isInducing.specializes_iff).mp ?_)
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hE]
    exact hsp
  have hF'eff : F'.IsEffective := fun E => by rw [hF'coeff]; exact hFeff _
  by_cases hA : ∀ E : Mori.PrimeDivisor W', F'.coeff E ≠ 0 → h' E.genericPoint = b'
  · exact false_of_forall_map_genericPoint_eq k (V.ι ≫ sZ) (W'.ι ≫ sW) hZ' hW' h' hh' hh'b hF'
      hF'eff hnef' b' hA htriv' hF'exc w' hw'F
  · push Not at hA
    obtain ⟨E₀, hE₀, hE₀b⟩ := hA
    exact false_of_exists_map_genericPoint_ne k ih (V.ι ≫ sZ) (W'.ι ≫ sW) hZ' hW' h' hh' hh'b
      hF' hF'eff hF'exc hnef' b' hgen' E₀ hE₀ hE₀b htriv' hdim' w' hw'b hw'F

private theorem eqCrit (k : Type u) [Field k] (d : WithBot ℕ∞) : EqCrit k d := by
  induction d using WellFoundedLT.induction with
  | _ d ih => exact eqCrit_of_forall_lt k ih

end Main

end Proof_lem_fa2_negativity_equality_criterion

namespace MMP.Flips

open MMP.Mori
open Proof_lem_fa2_negativity_equality_criterion

/-- **Numerical triviality over a point and the negativity lemma**, over an arbitrary field. Let
`h : W ⟶ Z` be a proper birational morphism of normal varieties over a field `k`, and `F` an
effective `ℝ`-Cartier divisor on `W` whose components are all exceptional over `Z`, with `-F`
`h`-nef. If `F` is numerically trivial on `h⁻¹(b)`, then `h⁻¹(b)` is disjoint from `Supp F`. -/
public theorem disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field
    (k : Type u) [Field k] {Z W : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    (hZ : IsNormalVariety k sZ) (hW : IsNormalVariety k sW)
    (h : W ⟶ Z) (hh : h ≫ sZ = sW) [IsProper h] (hhb : IsBirationalMorphism h)
    {F : RDivisor W} (hF : IsCartierCombination F) (hFeff : F.IsEffective)
    (hFexc : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → F.coeff P = 0)
    (hnef : IsRelativelyNef k sW h (-F)) (b : Z)
    (htriv : IsNumericallyTrivialOverPoint k sW h F b) :
    Disjoint (h.base ⁻¹' {b}) (F.supp : Set W) :=
  eqCrit k _ Z W sZ sW hZ hW h hh inferInstance hhb F hF hFeff hFexc hnef b htriv rfl

/-- **Numerical triviality over a point and the negativity lemma.** Let `h : W ⟶ Z` be a proper
birational morphism of normal varieties over an algebraically closed field `k` of characteristic
zero, and `F` an effective `ℝ`-Cartier divisor on `W` whose components are all exceptional over
`Z`, with `-F` `h`-nef. If `F` is numerically trivial on `h⁻¹(b)`, then `h⁻¹(b)` is disjoint
from `Supp F`. This is the case of
`disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field` over such `k`. -/
@[mmp "lem_fa2_negativity_equality_criterion"]
public theorem disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {Z W : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (sW : W ⟶ Spec (.of k)) [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    (hZ : IsNormalVariety k sZ) (hW : IsNormalVariety k sW)
    (h : W ⟶ Z) (hh : h ≫ sZ = sW) [IsProper h] (hhb : IsBirationalMorphism h)
    {F : RDivisor W} (hF : IsCartierCombination F) (hFeff : F.IsEffective)
    (hFexc : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → F.coeff P = 0)
    (hnef : IsRelativelyNef k sW h (-F)) (b : Z)
    (htriv : IsNumericallyTrivialOverPoint k sW h F b) :
    Disjoint (h.base ⁻¹' {b}) (F.supp : Set W) :=
  disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field k sZ sW hZ hW h hh
    hhb hF hFeff hFexc hnef b htriv

end MMP.Flips
