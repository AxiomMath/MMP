module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# A log canonical model of a relative weak log canonical model is reached by a morphism

Let `f : (X, D_X) ⟶ Z` be a relative weak log canonical model and `g : (Y, D_{𝓕,Y}) ⟶ Z` a log
canonical model of `f` through the rational map `φ : X ⤏ Y`, everything a variety over a field
of characteristic zero. Then `φ` is a morphism: it is the rational map of a morphism `X ⟶ Y`.

## Main results

* `MMP.Flips.IsLogCanonicalModelOf.exists_toRationalMap_eq_of_isRelativeWeakLogCanonicalModel`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.24.3
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips

universe u

namespace MMP.Flips.Fa2WeakLcModelMorphism

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
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
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

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
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
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
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

/-- **Projection formula** for a pull-back `L₁ = h^*D` of a Cartier divisor `D` along
`h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`L₁ · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- A divisor `L₁` given as a pull-back along `h` has degree zero on a proper curve whose image is
not a proper curve. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (hnc : ¬ IsProperCurve sY (h C'.point)) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hnc, map_zero]

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  exact ⟨m, r, L', fun j => (hpb j).2.isCartier (hL j),
    by simp only [toRDivisor_eq_mapCoeffs]⟩

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

section CommonModel

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U := by
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  exact (_root_.genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- The point `Spec k(X) ⟶ Y` of a partial map defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

end CommonModel

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_self {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} {D : RDivisor W} (hD : IsCartierCombination D) :
    IsNumericallyEquivalentOver k sW p D D :=
  ⟨hD, hD, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-! ### Intersection numbers of negatives, pull-backs and lifted curves -/

section Curves

variable {k : Type u} [Field k]

/-- If `q ≫ g` contracts `C'`, then `g` contracts the image curve `C = q(C')`. -/
private theorem isContractedBy_of_comp {W Y Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (q : W ⟶ Y) [IsProper q] (g : Y ⟶ Z) (C' : ProperCurve sW)
    (C : ProperCurve sY) (hC : C.point = q C'.point) (hC' : C'.IsContractedBy (q ≫ g)) :
    C.IsContractedBy g := by
  intro y hy
  rw [hC] at hy
  have hsub : closure ({q C'.point} : Set Y) ⊆ q '' closure ({C'.point} : Set W) :=
    closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
      (q.isClosedMap _ isClosed_closure)
  obtain ⟨z, hz, rfl⟩ := hsub hy
  rw [hC]
  simpa only [Scheme.Hom.comp_apply] using hC' z hz

/-- The generic point of a proper curve is not a closed point. -/
private theorem exists_specializes_ne_of_isProperCurve {G : Scheme.{u}} (sG : G ⟶ Spec (.of k))
    (p : G) (h : IsProperCurve sG p) : ∃ w, p ⤳ w ∧ w ≠ p := by
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (closure ({p} : Set G)) := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext
    ((hcon a (specializes_iff_mem_closure.mpr ha)).trans
      (hcon b (specializes_iff_mem_closure.mpr hb)).symm)⟩
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h2 := @topologicalKrullDim_zero_of_discreteTopology (closure ({p} : Set G)) _
    (@Subsingleton.discreteTopology _ _ hsub)
  rw [h1] at h2
  exact absurd h2 (by decide)

variable {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} [IsSeparated sT]
  [LocallyOfFiniteType sT]

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
      rwa [Scheme.Hom.toImage_imageι]
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

end Curves

/-- **Projection formula** for a pull-back `G = q^*N` of an `ℝ`-Cartier divisor: on a proper
curve `C' ⊆ W` whose image is the proper curve `C`, `G · C' = [k(C') : k(C)] (N · C)`, for all
presentations of `G` and `N`. -/
private theorem isRIntersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (C : ProperCurve sY)
    (hC : C.point = q C'.point) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY N r' L' C x) :
    x' = residueFieldDegree q C'.point * x := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hNpres, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => (hpb j).2.isCartier (hL₀ j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  have hy0 := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
  rw [← hNpres] at hy0
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hy0]
  have hdeg : ∀ j, ((L₁ j).degreeOn k (q ≫ sY) C'.ι C'.dim_le (hL₁ j) : ℝ) =
      (residueFieldDegree q C'.point : ℝ) * (L₀ j).degreeOn k sY C.ι C.dim_le (hL₀ j) :=
    fun j => by
      rw [degreeOn_eq_mul_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' C hC]
      push_cast
      ring
  simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]

/-- A pull-back `G = q^*N` of an `ℝ`-Cartier divisor has intersection number `0` with a proper
curve `C' ⊆ W` whose image is not a proper curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hnc : ¬ IsProperCurve sY (q C'.point))
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') : x' = 0 := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, -, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => (hpb j).2.isCartier (hL₀ j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hnc]

/-- A curve contracted by `p` is contracted by `p ≫ f`. -/
private theorem isContractedBy_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} {p : W ⟶ X} (f : X ⟶ Z) {C : ProperCurve sW}
    (hC : C.IsContractedBy p) : C.IsContractedBy (p ≫ f) :=
  fun z hz => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]

/-- A `(p ≫ f)`-nef divisor is `p`-nef. -/
private theorem isRelativelyNef_of_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} (f : X ⟶ Z) {D : RDivisor W}
    (hD : IsRelativelyNef k sW (p ≫ f) D) : IsRelativelyNef k sW p D :=
  let ⟨m, r, L, hL, hpres, hall⟩ := hD
  ⟨m, r, L, hL, hpres, fun C hC => hall C (isContractedBy_comp f hC)⟩

/-- **Pull-backs of relatively nef divisors.** Let `q : W ⟶ Y` be proper and `N` a `g`-nef
`ℝ`-Cartier divisor on `Y`. Then `q^*N` is `(q ≫ g)`-nef: on a proper curve `C' ⊆ W` contracted
by `q ≫ g`, the projection formula gives `q^*N · C' = [k(C') : k(q C')] (N · q C')` when `q(C')`
is a curve, which is contracted by `g`, and `q^*N · C' = 0` when `q(C')` is a point. -/
private theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {N : RDivisor Y}
    (hN : IsRelativelyNef k sY g N) {G : RDivisor W} (hG : IsRCartierPullback q N G) :
    IsRelativelyNef k sW (q ≫ g) G := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_of_isRCartierPullback hG
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C' hC' x hx => ?_⟩
  by_cases hc : IsProperCurve sY (q C'.point)
  · let C : ProperCurve sY := ⟨_, hc⟩
    obtain ⟨m', r', L', hL', hNpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    rw [← hNpres] at hy
    rw [isRIntersectionNumber_pullback_eq_mul q hq hG C' C rfl hx hy]
    exact mul_nonneg (Nat.cast_nonneg _) (hall C (isContractedBy_of_comp q g C' C rfl hC') _ hy)
  · exact (isRIntersectionNumber_pullback_eq_zero q hq hG C' hc hx).ge

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D)
    (hDc : D.IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

section FibreCurves

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- In a Noetherian quasi-sober space, a connected closed set `F` meeting a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected_of_inter_nonempty {Y : Type*}
    [TopologicalSpace Y] [NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : _root_.IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
  by_cases hdis : (closure T ∩ S).Nonempty
  · obtain ⟨s, hsT, hsS⟩ := hdis
    obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
        (isClosed_closure : IsClosed (closure T))
    have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
      refine closure_minimal (fun y hy => ?_) ?_
      · have : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
        obtain ⟨z, hz, hyz⟩ := this
        exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
      · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
    obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
    have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
    exact ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS),
      s, hsS, hζ.specializes hsz⟩
  · obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => by
        by_cases haS : a ∈ S
        · exact Or.inr haS
        · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact (hdis ⟨w, hwT, hwS⟩).elim

/-- The fibre of a proper morphism `f : Y ⟶ X` over a closed point of a scheme `X` locally of
finite type over `k` is proper over `k`. -/
private theorem isProper_fiberι_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    (hf : f ≫ sX = sY) [IsProper f] {x : X} (hx : IsClosed ({x} : Set X)) :
    IsProper (f.fiberι x ≫ sY) := by
  rw [show f.fiberι x ≫ sY = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) by
    simp only [← hf, Scheme.Hom.fiber_fac_assoc]]
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  haveI : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  infer_instance

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ :=
    exists_specializes_of_isConnected_of_inter_nonempty hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  -- the scheme-theoretic fibre, proper over `k`
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsProper sF := isProper_fiberι_comp k sX sY f hf hx
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : MMP.Mori.ProperCurve sF := ⟨y', hy'⟩
  -- its image in `Y` is a proper curve of `Y`
  have hCι : ¬ C'.IsContractedBy ι := fun h => by
    obtain ⟨w, hw, hne⟩ := exists_specializes_ne_of_isProperCurve sF y' hy'
    exact hne (hemb.injective (h w (specializes_iff_mem_closure.mp hw)))
  let C : MMP.Mori.ProperCurve sY := ⟨ι y', isProperCurve_map ι rfl C' hCι⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← C'.range_comp ι rfl, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz =>
    Eq.trans (hclF hz) (hclF (subset_closure rfl : ι y' ∈ closure {ι y'})).symm
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [hrC]
    exact fun h => hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end FibreCurves

/-! ### A rational map is defined where a common model has a constant second projection -/

/-- **Rigidity at a point.** Let `p : W ⟶ X` be a proper dominant morphism of integral schemes
with `p_* 𝒪_W = 𝒪_X`, inducing an isomorphism of function fields, and let `q : W ⟶ Y` agree with
the rational map `φ : X ⤏ Y` through `p` at the generic point. If `q` maps the fibre `p⁻¹(y)` to
a single point `c`, then `φ` is defined at `y`: for an affine open `V ∋ c` there is an open
`U ∋ y` with `p⁻¹(U) ⊆ q⁻¹(V)`, and the map `Γ(V, 𝒪_Y) ⟶ Γ(p⁻¹ U, 𝒪_W) ≅ Γ(U, 𝒪_X)` is a
morphism `U ⟶ V` representing `φ`. -/
private theorem mem_domain_of_forall_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] [IsProper p] (q : W ⟶ Y)
    (hbij : Function.Bijective (functionFieldMap p)) (hiso : ∀ U : X.Opens, IsIso (p.app U))
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {y : X} {c : Y} (hc : ∀ w, p w = y → q w = c) : y ∈ φ.domain := by
  obtain ⟨V, hV, hcV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ c)
  have hK : IsClosed (p '' ((q ⁻¹ᵁ V : W.Opens) : Set W)ᶜ) :=
    p.isClosedMap _ (q ⁻¹ᵁ V).isOpen.isClosed_compl
  let U : X.Opens := ⟨_, hK.isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨w, hw, rfl⟩
    exact hw (show q w ∈ V by rwa [hc w rfl])
  have hUV : p ⁻¹ᵁ U ≤ q ⁻¹ᵁ V := fun w hw => Classical.byContradiction fun h => hw ⟨w, h, rfl⟩
  haveI : IsAffine V.toScheme := hV
  let h' : (p ⁻¹ᵁ U).toScheme ⟶ V.toScheme := W.homOfLE hUV ≫ (q ∣_ V)
  haveI : IsIso (p ∣_ U).appTop := by
    rw [morphismRestrict_appTop]
    have h2 : IsIso (W.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤)).op) :=
      inferInstance
    exact IsIso.comp_isIso' (hiso _) h2
  let ψV : U.toScheme ⟶ V.toScheme :=
    U.toScheme.toSpecΓ ≫ Spec.map (h'.appTop ≫ inv (p ∣_ U).appTop) ≫ V.toScheme.isoSpec.inv
  have hψ : (p ∣_ U) ≫ ψV = h' := by
    have e1 := Scheme.toSpecΓ_naturality (p ∣_ U)
    have e2 := Scheme.toSpecΓ_naturality h'
    simp only [ψV]
    rw [reassoc_of% e1, ← Spec.map_comp_assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, ← reassoc_of% e2]
    change h' ≫ V.toScheme.isoSpec.hom ≫ V.toScheme.isoSpec.inv = h'
    rw [Iso.hom_inv_id, Category.comp_id]
  have hψ' : (p ∣_ U) ≫ ψV ≫ V.ι = (p ⁻¹ᵁ U).ι ≫ q := by
    rw [← Category.assoc, hψ]
    simp only [h', Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  refine Scheme.RationalMap.mem_domain.mpr ⟨⟨U, U.isOpen.dense ⟨y, hyU⟩, ψV ≫ V.ι⟩, hyU, ?_⟩
  have hηX : genericPoint X ∈ U := (genericPoint_specializes y).mem_open U.isOpen hyU
  have hηW : genericPoint W ∈ p ⁻¹ᵁ U := by
    change p (genericPoint W) ∈ U
    rwa [map_genericPoint_of_isDominant]
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), KF]
  have key : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      U.fromSpecStalkOfMem (genericPoint X) hηX =
      (p ⁻¹ᵁ U).fromSpecStalkOfMem (genericPoint W) hηW ≫ (p ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  change Spec.map _ ≫ U.fromSpecStalkOfMem (genericPoint X) hηX ≫ ψV ≫ V.ι = _
  rw [reassoc_of% key, hψ', ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- If the rational map `φ` satisfies the hypothesis of `mem_domain_of_forall_eq` at every closed
point of the Jacobson scheme `X`, then `φ` is defined everywhere. -/
private theorem domain_eq_top_of_forall_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [JacobsonSpace X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] [IsProper p] (q : W ⟶ Y)
    (hbij : Function.Bijective (functionFieldMap p)) (hiso : ∀ U : X.Opens, IsIso (p.app U))
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (hc : ∀ y : X, IsClosed ({y} : Set X) → ∃ c : Y, ∀ w, p w = y → q w = c) :
    φ.domain = ⊤ := by
  by_contra hne
  obtain ⟨y₀, -, hy₀⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  obtain ⟨y, hyφ, hyc⟩ := nonempty_inter_closedPoints
    (⟨y₀, hy₀⟩ : ((φ.domain : Set X)ᶜ).Nonempty) φ.domain.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨c, hc⟩ := hc y (mem_closedPoints_iff.mp hyc)
  exact hyφ (mem_domain_of_forall_eq φ p q hbij hiso KF hc)

/-! ### Intersection numbers on curves contracted over the source -/

/-- A pull-back `G = q^*N` has intersection number `0` with every proper curve contracted by
`q`: its image is a closed point, not a curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero_of_isContractedBy {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) {N : RDivisor Y}
    {G : RDivisor W} (hG : IsRCartierPullback q N G) (C : ProperCurve sW)
    (hC : C.IsContractedBy q) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C x) : x = 0 := by
  refine isRIntersectionNumber_pullback_eq_zero q hq hG C (fun hc => ?_) hx
  obtain ⟨w, hspec, hne⟩ := exists_specializes_ne_of_isProperCurve sY _ hc
  have hcl : IsClosed ({q C.point} : Set Y) := by
    have h1 : q '' closure ({C.point} : Set W) = {q C.point} :=
      (Set.image_subset_iff.mpr hC).antisymm
        (Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩)
    rw [← h1]
    exact q.isClosedMap _ isClosed_closure
  exact hne (hspec.mem_closed hcl rfl)

/-- An `f`-ample `ℝ`-Cartier divisor is positive on every proper curve contracted by `f`. -/
private theorem pos_of_isRelativelyAmple {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {g : Y ⟶ Z} {A : RDivisor Y} (hA : IsRelativelyAmple g A)
    (C : ProperCurve sY) (hC : C.IsContractedBy g) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY A r L C x) : 0 < x := by
  obtain ⟨m', r', L', hm, hr, hL, rfl⟩ := hA
  have hLc : ∀ j, (L' j).IsCartier := fun j => (hL j).1
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx
    (isRIntersectionNumber_sum_degreeOn k sY C r' L' hLc)]
  refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier g (hL j) (hLc j) C hC

section Realized

/-- The generic point of `A` lies over every dense open of `X`, for dominant `a : A ⟶ X`. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a _ ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense hU

/-- The partial map `a⁻¹(dom g) ⟶ dom g ⟶ Y` is, at the generic point, `Spec k(A) ⟶ Spec k(X)`
followed by `g`. -/
private theorem fromFunctionField_morphismRestrict_comp {A X Y : Scheme.{u}} [IsIntegral A]
    [IsIntegral X] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) :
    (Scheme.PartialMap.mk (a ⁻¹ᵁ g.domain)
      ((a ⁻¹ᵁ g.domain).isOpen.dense ⟨_, genericPoint_mem_preimage a g.dense_domain⟩)
      ((a ∣_ g.domain) ≫ g.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField := by
  rw [partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain),
    partialMap_fromFunctionField_eq _ (genericPoint_mem_of_dense g.dense_domain)]
  change _ ≫ (a ∣_ g.domain) ≫ g.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk a).symm

/-- If `p' = g ∘ a` on `a⁻¹(dom g)` for a dominant `a : A ⟶ X`, then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` along `g` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  rw [← fromFunctionField_morphismRestrict_comp, ← hcomm,
    partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain)]
  exact Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _

/-- A ring isomorphism `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y`, read off a pair
`p : A ⟶ X`, `q : A ⟶ Y` inducing isomorphisms of function fields along which `m` is `q`; it
satisfies `p^* ∘ θ = q^*`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, (functionFieldMap p).comp θ = functionFieldMap q ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, hθ', ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

/-- A prime divisor `F_W` of `W` over the generic point of a prime divisor `F` of `Y`, along which
`q : W ⟶ Y` is a local isomorphism, pulls `ord_F` back from `ord_{F_W}`. -/
private theorem comap_divisorialValuation_of_isIso_stalkMap {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian W] [IsLocallyNoetherian Y] [IsNormal W] [IsNormal Y]
    (q : W ⟶ Y) [IsDominant q] (FW : Mori.PrimeDivisor W) (F : Mori.PrimeDivisor Y)
    (heq : q FW.genericPoint = F.genericPoint) [IsIso (q.stalkMap FW.genericPoint)] :
    FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso q FW F heq t]

/-- The transform of a prime divisor `P` under `φ`, when `φ` is defined at `η_P`, is the closure
of the image of `η_P`. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
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
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

end Realized

section CommonModel'

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- **A morphism agreeing with a rational map at the generic point agrees with each of its
representatives.** Let `a : W ⟶ X` be dominant, `b : W ⟶ Y`, and `χ : X ⤏ Y` with
`χ ∘ a = b` at the generic point of `W`. Then for every representative `g` of `χ`,
`b = g ∘ a` on `a⁻¹(dom g)`. -/
private theorem preimage_ι_comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] (a : W ⟶ X) [IsDominant a]
    (b : W ⟶ Y) (χ : X.RationalMap Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ χ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ b)
    (g : X.PartialMap Y) (hg : g.toRationalMap = χ) :
    (a ⁻¹ᵁ g.domain).ι ≫ b = (a ∣_ g.domain) ≫ g.hom := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense g.dense_domain
  have hA : genericPoint W ∈ a ⁻¹ᵁ g.domain := genericPoint_mem_preimage a g.dense_domain
  refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint W) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
    Category.assoc, ← partialMap_fromFunctionField_eq g hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg]
  exact H.symm

/-- If `θ` induces `φ` at the generic points and `ψ` is inverse to `φ`, then
`Spec k(X) ⟶ Spec k(Y) ⟶ X` along `θ` and `ψ` is the canonical map. -/
private theorem specMap_comp_fromFunctionField_of_isInverse {X M : Scheme.{u}} [IsIntegral X]
    [IsIntegral M] {φ : X.RationalMap M} {ψ : M.RationalMap X}
    (hinv : Mori.RationalMap.IsInverse φ ψ) (θ : M.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ M.fromSpecStalk (genericPoint M) =
      φ.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ) ≫ ψ.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_dense e.dense_source
  have hy : genericPoint M ∈ e.target := genericPoint_mem_of_dense e.dense_target
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint M) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ) ≫ e.target.fromSpecStalkOfMem (genericPoint M) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ, hφ,
      Category.assoc]
  rw [hψ, ← Category.assoc, c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- If `φ_*P = E` and `g` is a representative of `φ` defined at `η_P`, then `η_E = g(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- **A common model maps points compatibly.** If `q = φ ∘ p` at the generic point of `W`, then
for every representative `g` of `φ` defined at `x = p(w)`, `q(w) = g(x)`. -/
private theorem apply_eq_hom_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) {w : W} {x : X} (hx : x ∈ g.domain)
    (hp : p w = x) : q w = g.hom ⟨x, hx⟩ := by
  let w' : (p ⁻¹ᵁ g.domain).toScheme := ⟨w, show p w ∈ g.domain from hp ▸ hx⟩
  calc q w = ((p ⁻¹ᵁ g.domain).ι ≫ q) w' := rfl
    _ = g.hom ((p ∣_ g.domain) w') := by
      rw [preimage_ι_comp_eq_of_specMap_fromFunctionField_eq p q φ H g hg]
      rfl
    _ = g.hom ⟨x, hx⟩ :=
      congrArg g.hom (Subtype.ext ((morphismRestrict_base_coe p g.domain w').trans hp))

/-- **Strict transforms on a common model.** If `q = φ ∘ p` at the generic point of `W` and
`φ_*Q = Q'`, then every point of `W` over `η_Q` lies over `η_{Q'}`. -/
private theorem apply_eq_genericPoint_of_transformPrimeDivisor_eq_some {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hT : Mori.RationalMap.transformPrimeDivisor φ Q = some Q') {w : W}
    (hp : p w = Q.genericPoint) : q w = Q'.genericPoint := by
  obtain ⟨g, hQg, hg⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hT).1
  exact (apply_eq_hom_of_specMap_fromFunctionField_eq H g hg hQg hp).trans
    (genericPoint_eq_of_transformPrimeDivisor_eq_some hT g hg hQg).symm

/-- The stalk of `Y` at the generic point of a prime divisor is a valuation ring. -/
private theorem valuationRing_stalk_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (Q : Mori.PrimeDivisor Y) {y : Y}
    (h : y = Q.genericPoint) : ValuationRing (Y.presheaf.stalk y) := by
  have := Q.isDiscreteValuationRing_localRing
  subst h
  infer_instance

/-- A birational morphism mapping `w` to the generic point of a prime divisor is a local
isomorphism at `w`. -/
private theorem isIso_stalkMap_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w : W}
    (h : q w = Q.genericPoint) : IsIso (q.stalkMap w) :=
  have := valuationRing_stalk_of_eq_genericPoint Q h
  MMP.Positivity.isIso_stalkMap_of_valuationRing q hq w

/-- A separated birational morphism has at most one point over the generic point of a prime
divisor. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w₁ w₂ : W}
    (h₁ : q w₁ = Q.genericPoint) (h₂ : q w₂ = Q.genericPoint) : w₁ = w₂ :=
  have := valuationRing_stalk_of_eq_genericPoint Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₂
  MMP.Positivity.eq_of_isIso_stalkMap q hq (h₂.trans h₁.symm)

end CommonModel'

/-! ### Discrepancies along divisors that are not exceptional -/

/-- Let `G = φ_*D_X + ∑_{F ∈ Fs} c_F F`, with `Fs` the `φ⁻¹`-exceptional prime divisors of `Y`. If
`Q` is the only prime divisor of `X` with `φ_*Q = Q'`, then `ord_{Q'}` has the same discrepancy
with respect to `(Y, G)` as `ord_Q` with respect to `(X, D_X)`: both are `-coeff_Q(D_X)`. -/
private theorem isDiscrepancy_eq_of_transformPrimeDivisor_eq_some {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {Fs : Finset (Mori.PrimeDivisor Y)}
    (hFs : ∀ F, F ∈ Fs ↔ RationalMap.IsInverseExceptional φ F)
    (hG : G = Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F))
    {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hT : Mori.RationalMap.transformPrimeDivisor φ Q = some Q')
    (huniq : ∀ Q₁, Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q' → Q₁ = Q) {a a' : ℝ}
    (ha : IsDiscrepancy sY n K_Y G Q'.divisorialValuation a)
    (ha' : IsDiscrepancy sX n K_X D_X Q.divisorialValuation a') : a = a' := by
  have hQ'Fs : Q' ∉ Fs := fun h => (hFs Q').mp h Q hT
  have hcoef : G.coeff Q' = D_X.coeff Q := by
    rw [hG]
    change (Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F)) Q' =
      D_X Q
    rw [Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finset.sum_eq_zero fun F hF =>
        Finsupp.single_eq_of_ne' fun h : F = Q' => hQ'Fs (h ▸ hF),
      add_zero]
    exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hT huniq D_X
  linarith [ha.eq_neg_coeff, ha'.eq_neg_coeff]

/-- On a common model `(W, p, q)` of `φ`, let `P` be a prime divisor of `W` lying over the generic
points of the prime divisors `Q` of `X` and `Q'` of `Y`. Then `Q` is the only prime divisor of `X`
with `φ_*Q = Q'`. -/
private theorem eq_of_transformPrimeDivisor_eq_some {k : Type u} [Field k] [PerfectField k]
    {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {φ : X.RationalMap Y} (hXn : IsNormalVariety k sX) {p : W ⟶ X} {q : W ⟶ Y}
    [IsProper p] [IsProper q] [IsDominant p] [IsDominant q] (hWp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {P : Mori.PrimeDivisor W} {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hpQ : p P.genericPoint = Q.genericPoint) (hqP : q P.genericPoint = Q'.genericPoint)
    (Q₁ : Mori.PrimeDivisor X) (hT₁ : Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q') :
    Q₁ = Q := by
  obtain ⟨P₁, hp₁, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWp hpb Q₁
  have heq := eq_of_apply_eq_genericPoint q hqb.functionFieldMap_bijective Q' hqP
    (apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT₁ hp₁)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp₁.symm.trans (heq ▸ hpQ))

/-- **FA 2.23.3, along the divisors that are not exceptional over the source.** Let
`g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of `f : (X, D_X) ⟶ Z` through `φ`, and
`p : W ⟶ X`, `q : W ⟶ Y` proper birational morphisms from a normal variety with `q = φ ∘ p` at the
generic point. For a prime divisor `P` of `W` not exceptional over `X`,
`a(ord_P, D_X) ≤ a(ord_P, D_{𝓕,Y})`. -/
private theorem isDiscrepancy_le_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (KF : haveI := hpb.isDominant
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
        W.fromSpecStalk (genericPoint W) ≫ q)
    (P : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hWp, isBirationalMorphism := hpb, E := P,
        isProper := inferInstance }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hWq, isBirationalMorphism := hqb, E := P,
        isProper := inferInstance }
    ¬ EX.IsExceptional →
      ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
        IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  intro EX EY hEX a a' ha ha'
  obtain ⟨-, -, -, hFB, -, -, hexc⟩ := hM
  obtain ⟨hXn, hYn, hφb, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI := isSeparated_toTerminal sX
  haveI := isSeparated_toTerminal sY
  -- `Q = p(P)` is a prime divisor of `X` with `ord_P = ord_Q`.
  obtain ⟨Q, -, hpQ, -, hEXv⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXn EX hEX
  change p P.genericPoint = Q.genericPoint at hpQ
  rw [hEXv] at ha'
  rcases hT : Mori.RationalMap.transformPrimeDivisor φ Q with _ | Q'
  · -- `φ_*Q = 0`: the inequality is part of the definition of a weak log canonical model.
    obtain ⟨θ, hθq, hθ⟩ := exists_ringHom_of_specMap _ p q hpb.functionFieldMap_bijective KF
    have hψθ := specMap_comp_fromFunctionField_of_isInverse hφb.isInverse_inverse θ hθ
    have KF' : Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫
        hφb.inverse.fromFunctionField = W.fromSpecStalk (genericPoint W) ≫ p := by
      rw [← hθq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψθ]
      exact functionFieldMap_fromSpecStalk p
    obtain ⟨g', hg'⟩ := hφb.inverse.exists_rep
    exact hexc hφb Q hT EY a a' ⟨g', p, hpb, hg',
      preimage_ι_comp_eq_of_specMap_fromFunctionField_eq q p _ KF' g' hg', hEXv⟩ ha ha'
  · -- `φ_*Q = Q'`: both discrepancies are `-coeff_Q(D_X)`.
    have hqP := apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT hpQ
    have : IsIso (q.stalkMap P.genericPoint) :=
      isIso_stalkMap_of_apply_eq_genericPoint q hqb.functionFieldMap_bijective Q' hqP
    rw [show EY.valuation = Q'.divisorialValuation from
      comap_divisorialValuation_of_isIso_stalkMap q P Q' hqP] at ha
    exact (isDiscrepancy_eq_of_transformPrimeDivisor_eq_some hFs hG hT
      (eq_of_transformPrimeDivisor_eq_some hXn hWp hpb hqb KF hpQ hqP) ha ha').ge

/-- **FA 2.23.3, along the divisors that are not exceptional over the target, when the target
extracts no divisor.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of
`f : (X, D_X) ⟶ Z` through `φ` such that no prime divisor of `Y` is `φ⁻¹`-exceptional, and
`p : W ⟶ X`, `q : W ⟶ Y` proper birational morphisms from a normal variety with `q = φ ∘ p` at the
generic point. For a prime divisor `P` of `W` not exceptional over `Y`,
`a(ord_P, D_{𝓕,Y}) ≤ a(ord_P, D_X)`; both are `-coeff_Q(D_X)` for the prime divisor `Q = p(P)`. -/
private theorem isDiscrepancy_le_of_not_isExceptional_target {k : Type u} [Field k]
    [PerfectField k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    (hexc : ∀ F : Mori.PrimeDivisor Y, ¬ RationalMap.IsInverseExceptional φ F) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (KF : haveI := hpb.isDominant
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
        W.fromSpecStalk (genericPoint W) ≫ q)
    (P : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hWp, isBirationalMorphism := hpb, E := P,
        isProper := inferInstance }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hWq, isBirationalMorphism := hqb, E := P,
        isProper := inferInstance }
    ¬ EY.IsExceptional →
      ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
        IsDiscrepancy sX n K_X D_X EX.valuation a' → a ≤ a' := by
  intro EX EY hEY a a' ha ha'
  obtain ⟨-, -, -, hFB, -, -, -⟩ := hM
  obtain ⟨hXn, hYn, -, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI := isSeparated_toTerminal sX
  haveI := isSeparated_toTerminal sY
  -- `Q' = q(P)` is a prime divisor of `Y` with `ord_P = ord_{Q'}`.
  obtain ⟨Q', -, hqQ', -, hEYv⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hYn EY hEY
  change q P.genericPoint = Q'.genericPoint at hqQ'
  rw [hEYv] at ha
  -- `Q'` is the strict transform `φ_*Q` of a prime divisor `Q` of `X`.
  obtain ⟨Q, hT⟩ : ∃ Q, Mori.RationalMap.transformPrimeDivisor φ Q = some Q' := by
    by_contra h
    exact hexc Q' fun Q hQ => h ⟨Q, hQ⟩
  -- `p(P) = Q`: the point of `W` over `η_Q` lies over `η_{Q'}`, as does `η_P`.
  obtain ⟨P₁, hp₁, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWp hpb Q
  have hPP₁ := eq_of_apply_eq_genericPoint q hqb.functionFieldMap_bijective Q' hqQ'
    (apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT hp₁)
  have hpQ : p P.genericPoint = Q.genericPoint := hPP₁ ▸ hp₁
  have : IsIso (p.stalkMap P.genericPoint) :=
    isIso_stalkMap_of_apply_eq_genericPoint p hpb.functionFieldMap_bijective Q hpQ
  rw [show EX.valuation = Q.divisorialValuation from
    comap_divisorialValuation_of_isIso_stalkMap p P Q hpQ] at ha'
  exact (isDiscrepancy_eq_of_transformPrimeDivisor_eq_some hFs hG hT
    (eq_of_transformPrimeDivisor_eq_some hXn hWp hpb hqb KF hpQ hqQ') ha ha').le

/-- The divisors of two nonzero rational top forms on a normal variety are linearly equivalent;
the two forms may be given for equal structure morphisms. -/
private theorem linearlyEquivalent_divisorOfForm_of_eq {k : Type u} [Field k] [PerfectField k]
    {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {s₁ s₂ : W ⟶ Spec (.of k)} (hs : s₁ = s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (hW : IsNormalVariety k s₁) {n : ℕ} (hn : topologicalKrullDim W = n)
    {τ : RationalPluriForms s₁ n 1} {ω : RationalPluriForms s₂ n 1} (hτ : τ ≠ 0) (hω : ω ≠ 0) :
    Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  subst hs
  let := functionFieldAlgebra s₁
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := s₁) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hW hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- On a common normal model `(W, p, q)` of `X` and `Y`, the divisors of the pull-backs of nonzero
rational top forms on `X` and on `Y` are linearly equivalent. -/
private theorem linearlyEquivalent_zero_divisorOfForm_pullback {k : Type u} [Field k]
    [PerfectField k] {X Y W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [LocallyOfFiniteType sX] [IsIntegral Y] [LocallyOfFiniteType sY]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {p : W ⟶ X}
    {q : W ⟶ Y} [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sY)] (hWp : IsNormalVariety k (p ≫ sX)) (hpq : p ≫ sX = q ≫ sY)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) {n : ℕ}
    (hnX : topologicalKrullDim X = n) (hnY : topologicalKrullDim Y = n)
    {ωX : RationalPluriForms sX n 1} {ωY : RationalPluriForms sY n 1} (hωX : ωX ≠ 0)
    (hωY : ωY ≠ 0) :
    (divisorOfForm (pullbackRationalPluriForms sY q ωY) -
      divisorOfForm (pullbackRationalPluriForms sX p ωX)).LinearlyEquivalent 0 := by
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := sX), hnX]
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq hpq.symm (hpq ▸ hWp) hnW
    (pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hnY) hωY)
    (pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hnX) hωX)
  exact ⟨φ, by rwa [sub_zero]⟩

/-! ### The crepant identity on a common model -/

/-- **FA 2.24.3, the crepant identity.** Let `f : (X, D_X) ⟶ Z` be a relative weak log canonical
model and `g : (Y, G) ⟶ Z` a log canonical model of `f` through `φ`, with `K_X = div ω_X` and
`K_Y = div ω_Y`, and let `(W, p, q)` be a common normal model of `φ` with `p ≫ f = q ≫ g`. Then
`q^*(K_Y + G) = p^*(K_X + D_X) + L₁` with `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)`.

The difference `Δ = p^*(K_X + D_X) - q^*(K_Y + G) + L₁` has coefficient `a(P, G) - a(P, D_X)`
along a prime divisor `P` of `W`. The negativity lemma along `p` gives `Δ ≥ 0`, and along `q`,
where no prime divisor of `Y` is `φ⁻¹`-exceptional because `(X, D_X)` is lc, it gives `-Δ ≥ 0`. -/
private theorem isRCartierPullback_eq_add {k : Type u} [Field k] [CharZero k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ} {ωX : RationalPluriForms sX n 1}
    {ωY : RationalPluriForms sY n 1} (hωX : ωX ≠ 0) (hωY : ωY ≠ 0) {D_X : Mori.RDivisor X}
    {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ}
    {G : Mori.RDivisor Y}
    (hf : IsRelativeWeakLogCanonicalModel sX n (divisorOfForm ωX) D_X f)
    (hM : IsLogCanonicalModelOf sY sX n (divisorOfForm ωX) D_X (divisorOfForm ωY) f g φ c G)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {p : W ⟶ X}
    {q : W ⟶ Y} [IsProper p] [IsProper q] [IsDominant p] [IsDominant q]
    [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)] [LocallyOfFiniteType (q ≫ sY)]
    [QuasiCompact (q ≫ sY)] (hWp : IsNormalVariety k (p ≫ sX)) (hpq : p ≫ sX = q ≫ sY)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hcomm : p ≫ f = q ≫ g)
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {G_X G_Y : Mori.RDivisor W}
    (hGX : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + D_X) G_X)
    (hGY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωY) + G) G_Y) :
    G_Y = G_X + Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY) -
      divisorOfForm (pullbackRationalPluriForms sX p ωX)) := by
  obtain ⟨-, hXlc, hfnef⟩ := hf
  obtain ⟨hexc, -⟩ := hM.not_isInverseExceptional_and_eq_transformDivisor hXlc
  obtain ⟨hWLC, -⟩ := hM
  obtain ⟨-, -, -, hFB, hYc, ⟨-, hYlc, hAY⟩, -⟩ := id hWLC
  obtain ⟨hXn, hYn, -, -, hKX, hXc, -⟩ := id hFB
  have hKY := hYlc.2.1
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  have hWq : IsNormalVariety k (q ≫ sY) := hpq ▸ hWp
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms sY q ωY) -
        divisorOfForm (pullbackRationalPluriForms sX p ωX) := ⟨_, rfl⟩
  rw [← hL₁_def]
  have hL₁ : L₁.LinearlyEquivalent 0 := hL₁_def ▸
    linearlyEquivalent_zero_divisorOfForm_pullback hWp hpq hpb hqb hKX.topologicalKrullDim_eq
      hKY.topologicalKrullDim_eq hωX hωY
  have hL₁r := isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL₁
  have hGXc := isCartierCombination_of_isRCartierPullback hGX
  have hGYc := isCartierCombination_of_isRCartierPullback hGY
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ωX) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ωX hωX hKX hXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hωY hKY hYc q hWq hqb hGY P
  -- `Δ = p^*(K_X + D_X) - q^*(K_Y + G) + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  set Δ : RDivisor W := G_X - G_Y + Divisor.toRDivisor L₁ with hΔ
  have hcoeff : ∀ P, Δ.coeff P =
      (dY.coeff P - G_Y.coeff P) - (dX.coeff P - G_X.coeff P) := by
    intro P
    rw [hΔ, hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have hBc := isCartierCombination_add (isCartierCombination_sub hGXc hGYc) hL₁r
  -- the negativity lemma along `p`: `Δ ≥ 0`
  have hMnef : IsRelativelyNef k (p ≫ sX) p (G_Y - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_eq_zero (isRelativelyNef_of_comp f (by
      rw [hcomm]; exact isRelativelyNef_of_isRCartierPullback q hpq.symm g hAY hGY)) hL₁r
      fun C _ _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁ C hx
  have hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sX p P →
      0 ≤ Δ.coeff P := by
    intro P hP
    rw [hcoeff P, sub_nonneg]
    exact isDiscrepancy_le_of_not_isExceptional hWLC hWp hWq hpb hqb KF P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
  have hΔeff := isEffective_of_isNumericallyEquivalentOver_pullback k sX (p ≫ sX) hXn hWp p rfl
    hpb hXc hGX (isCartierCombination_sub hGYc hL₁r) hMnef hBc hBG (by
      rw [sub_add_add_cancel, add_sub_cancel]
      exact isNumericallyEquivalentOver_self hGXc)
  -- the negativity lemma along `q`: `-Δ ≥ 0`, with the principal divisor `-L₁`
  have hL₂ : (-L₁).LinearlyEquivalent 0 := by simpa using hL₁.neg
  have hL₂r := isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL₂
  have hMnef' : IsRelativelyNef k (q ≫ sY) q (G_X - Divisor.toRDivisor (-L₁)) :=
    isRelativelyNef_sub_of_eq_zero (isRelativelyNef_of_comp g (by
      rw [← hcomm]; exact isRelativelyNef_of_isRCartierPullback p hpq f hfnef hGX)) hL₂r
      fun C _ _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₂ C hx
  have hBG' : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sY q P →
      0 ≤ (-Δ).coeff P := by
    intro P hP
    have := isDiscrepancy_le_of_not_isExceptional_target hWLC hexc hWp hWq hpb hqb KF P
      (fun h => hP ⟨hWq, hqb, inferInstance, h⟩) _ _ (haY P) (haX P)
    have h := hcoeff P
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.neg_apply] at h this ⊢
    linarith
  have eB : G_Y - G_X - Divisor.toRDivisor L₁ = -Δ := by rw [hΔ]; abel
  have hΔeff' := isEffective_of_isNumericallyEquivalentOver_pullback k sY (q ≫ sY) hYn hWq q rfl
    hqb hYc hGY (isCartierCombination_sub hGXc hL₂r) hMnef'
    (eB ▸ isCartierCombination_sub (isCartierCombination_sub hGYc hGXc) hL₁r) hBG' (by
      rw [show G_X - Divisor.toRDivisor (-L₁) + -Δ = G_Y by rw [hΔ, map_neg]; abel]
      exact isNumericallyEquivalentOver_self hGYc)
  have hΔ0 : Δ = 0 :=
    le_antisymm (neg_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp hΔeff'))
      (DivisorWithCoeffs.isEffective_iff_nonneg.mp hΔeff)
  rwa [hΔ0, neg_zero, sub_sub, sub_eq_zero] at eB

/-! ### The fibres of the source projection -/

/-- **No curve in a fibre of `p` escapes `q`.** On a common model `(W, p, q)` with
`p ≫ f = q ≫ g`, let `G_X = p^*N_X` and `G_Y = q^*N_Y` with `N_Y` `g`-ample, and suppose
`G_Y = G_X + L` for a principal divisor `L`. Then every proper curve `C ⊆ W` contracted by `p` is
contracted by `q`: otherwise `q(C)` is a proper curve contracted by `g`, and
`0 = G_X · C = G_Y · C = [k(C) : k(q C)] (N_Y · q(C)) > 0`. -/
private theorem isContractedBy_of_isContractedBy {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsSeparated sY]
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {f : X ⟶ Z} {g : Y ⟶ Z} {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    [QuasiCompact (p ≫ sX)] (hpq : p ≫ sX = q ≫ sY) (hcomm : p ≫ f = q ≫ g)
    {N_X : RDivisor X} {N_Y : RDivisor Y} (hN_Y : IsCartierCombination N_Y)
    (hamp : IsRelativelyAmple g N_Y) {G_X G_Y : RDivisor W} (hGX : IsRCartierPullback p N_X G_X)
    (hGY : IsRCartierPullback q N_Y G_Y) {L : Divisor W} (hL : L.LinearlyEquivalent 0)
    (hcrep : G_Y = G_X + Divisor.toRDivisor L) (C : ProperCurve (p ≫ sX))
    (hCp : C.IsContractedBy p) : C.IsContractedBy q := by
  by_contra hCq
  let C' : ProperCurve sY := ⟨q C.point, isProperCurve_map q hpq.symm C hCq⟩
  obtain ⟨_, _, _, x₁, hx₁⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hGX) C
  obtain ⟨_, _, _, x₄, hx₄⟩ := exists_isRIntersectionNumber (k := k)
    (isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL) C
  obtain ⟨_, _, _, y, hy⟩ := exists_isRIntersectionNumber (k := k) hN_Y C'
  have hx₂ := (IsRIntersectionNumber.eq_and_linear k _ C).2 _ _ _ _ _ _ _ _ 1 1 hx₁ hx₄
  rw [one_smul, one_smul, ← hcrep] at hx₂
  have e := isRIntersectionNumber_pullback_eq_mul q hpq.symm hGY C C' rfl hx₂ hy
  rw [isRIntersectionNumber_pullback_eq_zero_of_isContractedBy p rfl hGX C hCp hx₁,
    eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL C hx₄] at e
  have hC'g : C'.IsContractedBy g :=
    isContractedBy_of_comp q g C C' rfl (hcomm ▸ isContractedBy_comp f hCp)
  have := mul_pos (Nat.cast_pos.mpr (residueFieldDegree_pos q hpq.symm C hCq) : (0 : ℝ) < _)
    (pos_of_isRelativelyAmple hamp C' hC'g hy)
  linarith

/-- **`q` is constant on the fibres of `p`.** Let `p : W ⟶ X` be a proper birational morphism of
normal varieties and `q : W ⟶ Y` a proper morphism contracting every proper curve that `p`
contracts. Then `q` is constant on the fibre of `p` over each closed point: that fibre is connected
and proper, so if `q` took a second value on it besides `c`, it would contain a proper curve
contracted by `p` meeting `q⁻¹(c)` without lying in it. -/
private theorem exists_forall_eq_of_isContractedBy {k : Type u} [Field k] {X Y W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hXn : IsNormalVariety k sX) [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} [IsProper p] [IsDominant p] {q : W ⟶ Y} [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) [QuasiCompact (p ≫ sX)] (hpb : IsBirationalMorphism p)
    (hcurve : ∀ C : ProperCurve (p ≫ sX), C.IsContractedBy p → C.IsContractedBy q)
    {y : X} (hy : IsClosed ({y} : Set X)) : ∃ c : Y, ∀ w, p w = y → q w = c := by
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (p ≫ sX)
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  have hFcl : IsClosed (p.base ⁻¹' {y}) := hy.preimage p.continuous
  obtain ⟨w', hw'⟩ := Surjective.surj (f := p) y
  obtain ⟨w₀, hw₀F, hw₀c⟩ := nonempty_inter_closedPoints
    (⟨w', hw'⟩ : (p.base ⁻¹' {y}).Nonempty) hFcl.isLocallyClosed
  refine ⟨q w₀, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨w₁, hw₁, hqw₁⟩ := h
  have hqcl : IsClosed ({q w₀} : Set Y) := by
    rw [← Set.image_singleton]
    exact q.isClosedMap _ (mem_closedPoints_iff.mp hw₀c)
  obtain ⟨C, hCp, hCS, c₀, hc₀R, hc₀S⟩ := exists_properCurve_isContractedBy k sX (p ≫ sX) hXn
    hWp p rfl hpb y hy (hFcl.inter (hqcl.preimage q.continuous)) ⟨w₀, hw₀F, hw₀F, rfl⟩
    fun h => hqw₁ (h (show w₁ ∈ p.base ⁻¹' {y} from hw₁)).2
  rw [C.range_ι] at hCS hc₀R
  exact hCS fun z hz => ⟨(hCp z hz).trans ((hCp c₀ hc₀R).symm.trans hc₀S.1),
    (hcurve C hCp z hz).trans ((hcurve C hCp c₀ hc₀R).symm.trans hc₀S.2)⟩

/-- A rational map from a reduced scheme to a separated scheme which is defined everywhere is a
morphism. -/
private theorem exists_toRationalMap_eq_of_domain_eq_top {X Y : Scheme.{u}} [IsReduced X]
    [Y.IsSeparated] (φ : X.RationalMap Y) (h : φ.domain = ⊤) :
    ∃ g : X ⟶ Y, g.toRationalMap = φ := by
  refine ⟨X.topIso.inv ≫ X.homOfLE h.ge ≫ φ.toPartialMap.hom, ?_⟩
  conv_rhs => rw [← φ.toRationalMap_toPartialMap]
  change (Scheme.Hom.toPartialMap _).toRationalMap = _
  congr 1
  refine Scheme.PartialMap.ext _ _ h.symm ?_
  simp
  congr 1

end MMP.Flips.Fa2WeakLcModelMorphism

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori Fa2WeakLcModelMorphism

/-- **FA 2.24.3.** Over a field of characteristic zero, let `f : (X, D_X) ⟶ Z` be a relative weak
log canonical model (`MMP.Flips.IsRelativeWeakLogCanonicalModel`) and `g : (Y, G) ⟶ Z` a log
canonical model of `f` through `φ : X ⤏ Y` with respect to `c`
(`MMP.Flips.IsLogCanonicalModelOf`), where `X`, `Y`, `Z` are varieties and `f`, `g` are
morphisms over `k`. Then `φ` is a morphism: `φ = h.toRationalMap` for some `h : X ⟶ Y`. -/
@[mmp "thm_fa2_weak_lc_model_to_lc_model_morphism"]
public theorem IsLogCanonicalModelOf.exists_toRationalMap_eq_of_isRelativeWeakLogCanonicalModel
    {k : Type u} [Field k] [CharZero k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hX : Mori.IsVariety k sX) (hY : Mori.IsVariety k sY) (hZ : Mori.IsVariety k sZ)
    {f : X ⟶ Z} {g : Y ⟶ Z} (hfZ : f ≫ sZ = sX) (hgZ : g ≫ sZ = sY)
    {n : ℕ} {K_X : Divisor X} {D_X : RDivisor X} {K_Y : Divisor Y} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : RDivisor Y}
    (hf : IsRelativeWeakLogCanonicalModel sX n K_X D_X f)
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G) :
    ∃ h : X ⟶ Y, h.toRationalMap = φ := by
  obtain ⟨hWLC, -, -, hamp⟩ := id hM
  obtain ⟨hfP, hgP, hmod, hFB, hYc, ⟨-, hYlc, -⟩, -⟩ := id hWLC
  obtain ⟨hXn, hYn, -, -, hKX, hXc, -⟩ := id hFB
  haveI := hfP
  haveI := hgP
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  -- a common normal model `(W, p, q)` of `φ` with `p ≫ f = q ≫ g`
  obtain ⟨W, p, q, hWp, hpP, hqP, hpb, hqb, ⟨φ', hφ', hrel⟩, hcomm⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism hXn hYn f g φ hmod.1 hmod.2
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hpq : p ≫ sX = q ≫ sY := by
    rw [← hfZ, ← hgZ, ← Category.assoc, hcomm, Category.assoc]
  haveI : LocallyOfFiniteType (q ≫ sY) := hpq ▸ inferInstance
  haveI : QuasiCompact (q ≫ sY) := hpq ▸ inferInstance
  have KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q :=
    hφ' ▸ specMap_functionFieldMap_fromFunctionField p φ' q hrel
  -- forms `ω_X`, `ω_Y` with `K_X = div ω_X` and `K_Y = div ω_Y`
  obtain ⟨ωX, hωX, hωXK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hKX
  obtain ⟨ωY, hωY, hωYK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hYlc.2.1
  obtain rfl : divisorOfForm ωX = K_X := Finsupp.ext hωXK
  obtain rfl : divisorOfForm ωY = K_Y := Finsupp.ext hωYK
  -- `q^*(K_Y + G) = p^*(K_X + D_X) + L₁` with `L₁` principal, so curves contracted by `p` are
  -- contracted by `q`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hYc
  have hcurve := isContractedBy_of_isContractedBy hpq hcomm hYc hamp hGX hGY
    (linearlyEquivalent_zero_divisorOfForm_pullback hWp hpq hpb hqb hKX.topologicalKrullDim_eq
      hYlc.2.1.topologicalKrullDim_eq hωX hωY)
    (isRCartierPullback_eq_add hωX hωY hf hM hWp hpq hpb hqb hcomm KF hGX hGY)
  -- so `φ` is defined at every closed point, hence everywhere
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hiso : ∀ U : X.Opens, IsIso (p.app U) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (p ≫ sX) sX hWp.1
      hXn p hpb).1
  haveI : Y.IsSeparated := ⟨isSeparated_toTerminal sY⟩
  exact exists_toRationalMap_eq_of_domain_eq_top φ <|
    domain_eq_top_of_forall_eq φ p q hpb.functionFieldMap_bijective hiso KF fun _ hy =>
      exists_forall_eq_of_isContractedBy hXn hWp hpb hcurve hy

end MMP.Flips
