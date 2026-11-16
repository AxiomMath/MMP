module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.MMP.Contraction.Defs
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# A log canonical model of a weak log canonical model is crepant

Let `f : (X, D_X) ⟶ Z` be a relative weak log canonical model and `g : (Y, D_{𝓕,Y}) ⟶ Z` a
log canonical model of `f` through `φ : X ⤏ Y`. On any common model `p : W ⟶ X`, `q : W ⟶ Y`
of `φ`, with canonical divisors `K_X = div_X ω`, `K_Y = div_Y ω_Y` for arbitrary nonzero
rational forms, the two pull-backs agree up to the principal divisor comparing the forms on `W`:
`q^*(K_Y + D_{𝓕,Y}) = p^*(K_X + D_X) + (div_W(q^*ω_Y) - div_W(p^*ω))`. When the canonical
divisors are compatible, `div_W(p^*ω) = div_W(q^*ω_Y)`, this is the crepant identity
`q^*(K_Y + D_{𝓕,Y}) = p^*(K_X + D_X)`.

## Main results

* `MMP.Flips.IsLogCanonicalModelOf.isRCartierPullback_eq_of_isRelativeWeakLogCanonicalModel`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of 2.24.3
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips
open scoped WithZero

universe u

namespace MMP.Flips.Fa2WeakLcModelCrepant

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
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
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

/-- `g.fromFunctionField` factors through `dom g` when `g` is defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_refl {k : Type u} [Field k] {W X : Scheme.{u}}
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

/-- A `(p ≫ f)`-nef divisor is `p`-nef. -/
private theorem isRelativelyNef_of_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} (f : X ⟶ Z) {D : RDivisor W}
    (hD : IsRelativelyNef k sW (p ≫ f) D) : IsRelativelyNef k sW p D :=
  let ⟨m, r, L, hL, hpres, hall⟩ := hD
  ⟨m, r, L, hL, hpres, fun C hC => hall C fun z hz => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]⟩

/-- **Pull-backs of relatively nef divisors.** Let `q : W ⟶ Y` be proper and `N` a `g`-nef
`ℝ`-Cartier divisor on `Y`. Then `q^*N` is `(q ≫ g)`-nef. -/
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

/-- The generic point of `A` lies over every dense open of `X`, for dominant `a : A ⟶ X`. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a _ ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense _ hU

/-- If `p : A ⟶ X` induces an isomorphism of function fields and `Spec(p^*) ≫ m` is `q` at the
generic point of `A`, then some `θ : k(Y) → k(X)` with `p^* ∘ θ = q^*` induces `m`. -/
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
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

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
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] (a : W ⟶ X) [IsDominant a] (b : W ⟶ Y)
    (χ : X.RationalMap Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ χ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ b)
    (g : X.PartialMap Y) (hg : g.toRationalMap = χ) :
    (a ⁻¹ᵁ g.domain).ι ≫ b = (a ∣_ g.domain) ≫ g.hom := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense _ g.dense_domain
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
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_dense _ e.dense_source
  have hy : genericPoint M ∈ e.target := genericPoint_mem_of_dense _ e.dense_target
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
      rw [comp_eq_of_specMap_fromFunctionField_eq p q φ H g hg]
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
      comp_eq_of_specMap_fromFunctionField_eq q p _ KF' g' hg', hEXv⟩ ha ha'
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

/-! ### The common model over the base -/

/-- The composite `p⁻¹(dom φ₀) ⟶ dom φ₀ ⟶ Y` is, at the generic point, `Spec k(W) ⟶ Spec k(X)`
followed by `φ₀`. -/
private theorem fromFunctionField_resLE_comp {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    (p : W ⟶ X) [IsDominant p] (φ₀ : X.PartialMap Y)
    (hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W)) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ₀.fromFunctionField := by
  have hx : genericPoint X ∈ φ₀.domain := genericPoint_mem_of_dense _ φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := genericPoint_mem_of_dense _ hd
  rw [partialMap_fromFunctionField_eq _ hW, partialMap_fromFunctionField_eq _ hx]
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
    p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- **A common model, at the generic point.** If `q = φ ∘ p` as maps for a dominant `p`, then
`Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_fromFunctionField_eq_of_comp_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨φ₀, rfl, hd, heq⟩ := H
  have h1 := congrArg Scheme.RationalMap.fromFunctionField heq
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom] at h1

/-- **A common model lies over the base.** If `q = φ ∘ p` at the generic point of `W` and
`g ∘ φ = f`, then `p ≫ f = q ≫ g`, for `W` integral and `Z` separated. -/
private theorem comp_eq_comp_of_specMap_fromFunctionField_eq {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Z ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hφ : φ.compHom g = f.toRationalMap) (p : W ⟶ X) [IsDominant p]
    (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    p ≫ f = q ≫ g := by
  have h1 : (p ≫ f).toRationalMap = (q ≫ g).toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom,
      ← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
      ← MMP.Flips.RationalMap.fromFunctionField_hom f, ← hφ,
      MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc, H, Category.assoc]
  obtain ⟨U, hU, hUl, hUr, e⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h1
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  have : Z.IsSeparated := ⟨‹_›⟩
  refine ext_of_isDominant (ι := U.ι) ?_
  simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom,
    Category.assoc] at e
  exact (Scheme.homOfLE_ι_assoc W hUl _).symm.trans (e.trans (Scheme.homOfLE_ι_assoc W hUr _))

/-! ### The negativity step on a common model -/

/-- **The negativity step on a common square.** Let `p : W ⟶ X` and `q : W ⟶ Y` be proper, with
`p` birational, `p ≫ sX = q ≫ sY` and `p ≫ f = q ≫ g`; let `G_X = p^*A_X` and `G_Y = q^*A_Y`
with `A_Y` `g`-nef, and let `L` be a principal divisor on `W`. If `G_Y ≤ G_X + L` along every
prime divisor of `W` that is not exceptional over `X`, then `G_Y ≤ G_X + L`. -/
private theorem le_add_of_forall_not_isExceptional_le {k : Type u} [Field k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hXn : IsNormalVariety k sX)
    [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p) (hpq : p ≫ sX = q ≫ sY)
    {f : X ⟶ Z} {g : Y ⟶ Z} (hcomm : p ≫ f = q ≫ g) {A_X : RDivisor X}
    (hAX : IsCartierCombination A_X) {A_Y : RDivisor Y} (hAY : IsRelativelyNef k sY g A_Y)
    {G_X G_Y : RDivisor W} (hGX : IsRCartierPullback p A_X G_X)
    (hGY : IsRCartierPullback q A_Y G_Y) {L : Divisor W} (hL : L.LinearlyEquivalent 0)
    (hle : ∀ P, ¬ IsExceptionalPrimeDivisor sX p P →
      G_Y.coeff P ≤ G_X.coeff P + (Divisor.toRDivisor L).coeff P) :
    G_Y ≤ G_X + Divisor.toRDivisor L := by
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  have hLc := isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL
  have hGXc := isCartierCombination_of_isRCartierPullback hGX
  have hGYc := isCartierCombination_of_isRCartierPullback hGY
  have hnef : IsRelativelyNef k (p ≫ sX) p G_Y := isRelativelyNef_of_comp f (by
    rw [hcomm]; exact isRelativelyNef_of_isRCartierPullback q hpq.symm g hAY hGY)
  have hB := isEffective_of_isNumericallyEquivalentOver_pullback k sX (p ≫ sX) hXn hWp p rfl hpb
    hAX hGX (isCartierCombination_sub hGYc hLc)
    (isRelativelyNef_sub_of_linearlyEquivalent_zero hnef hL)
    (B := G_X + Divisor.toRDivisor L - G_Y)
    (isCartierCombination_sub (isCartierCombination_add hGXc hLc) hGYc)
    (fun P hP => by
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Finsupp.add_apply] at hle ⊢
      linarith [hle P hP])
    (by rw [sub_add_sub_cancel', add_sub_cancel_right]; exact isNumericallyEquivalentOver_refl hGXc)
  exact sub_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp hB)

end MMP.Flips.Fa2WeakLcModelCrepant

namespace MMP.Flips

open Fa2WeakLcModelCrepant in
/-- **FA, proof of 2.24.3.** Let `f : (X, D_X) ⟶ Z` be a relative weak log canonical model
(`MMP.Flips.IsRelativeWeakLogCanonicalModel`) and `g : (Y, G) ⟶ Z` a log canonical model of `f`
through `φ : X ⤏ Y` with respect to `c` (`MMP.Flips.IsLogCanonicalModelOf`), over a field of
characteristic zero, where `K_X = div_X ω` and `K_Y = div_Y ωY` for nonzero rational `n`-forms.
Let `(W, p, q)` be a common model of `φ` (`MMP.Flips.IsCommonModel`). If `G_X = p^*(K_X + D_X)`
and `G_Y = q^*(K_Y + G)` (`MMP.Flips.IsRCartierPullback`), then
`G_Y = G_X + (div_W(q^*ωY) - div_W(p^*ω))`; in particular `G_Y = G_X` when the canonical divisors
are compatible on `W`. -/
@[mmp "lem_fa2_weak_lc_model_to_lc_model_crepant"]
public theorem IsLogCanonicalModelOf.isRCartierPullback_eq_of_isRelativeWeakLogCanonicalModel
    {k : Type u} [Field k] [CharZero k] {X Y Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {n : ℕ}
    (ω : RationalPluriForms sX n 1) (ωY : RationalPluriForms sY n 1) (hω : ω ≠ 0) (hωY : ωY ≠ 0)
    {D_X : RDivisor X} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : RDivisor Y}
    (hf : IsRelativeWeakLogCanonicalModel sX n (divisorOfForm ω) D_X f)
    (hM : IsLogCanonicalModelOf sY sX n (divisorOfForm ω) D_X (divisorOfForm ωY) f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sY)]
    {G_X G_Y : RDivisor W}
    (hGX : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + D_X) G_X)
    (hGY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωY) + G) G_Y) :
    haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
    haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
    G_Y = G_X + Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY) -
      divisorOfForm (pullbackRationalPluriForms sX p ω)) := by
  obtain ⟨-, hXlc, hfnef⟩ := hf
  obtain ⟨hexc, -⟩ := hM.not_isInverseExceptional_and_eq_transformDivisor hXlc
  obtain ⟨hWLC, -, -, -⟩ := hM
  obtain ⟨-, -, -, hFB, hYc, ⟨-, hYlc, hAY⟩, -⟩ := id hWLC
  obtain ⟨hXn, hYn, -, -, hKX, hXc, -⟩ := id hFB
  have hKY := hYlc.2.1
  have hpb := hW.isBirationalMorphism_p
  have hqb := hW.isBirationalMorphism_q
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := hW.isVariety_Z.toIsSeparated
  haveI := isSeparated_toTerminal sZ
  have hWp : IsNormalVariety k (p ≫ sX) := hW.comp_p ▸ hW.isNormalVariety
  have hWq : IsNormalVariety k (q ≫ sY) := hW.comp_q ▸ hW.isNormalVariety
  have hpq : p ≫ sX = q ≫ sY := hW.comp_p.trans hW.comp_q.symm
  have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  have hcomm : p ≫ f = q ≫ g :=
    comp_eq_comp_of_specMap_fromFunctionField_eq hW.isModificationOf.2 p q KF
  have hL₁ := linearlyEquivalent_zero_divisorOfForm_pullback hWp hpq hpb hqb
    hKX.topologicalKrullDim_eq hKY.topologicalKrullDim_eq hω hωY
  -- the discrepancies `a(P, X, D_X)` and `a(P, Y, G)`, read off the two pull-backs
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ω) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ω hω hKX hXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hωY hKY hYc q hWq hqb hGY P
  have hcoeff : ∀ P, (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY) -
      divisorOfForm (pullbackRationalPluriForms sX p ω))).coeff P = dY.coeff P - dX.coeff P :=
    fun P => by rw [map_sub]; rfl
  refine le_antisymm (le_add_of_forall_not_isExceptional_le hXn hWp hpb hpq hcomm hXc hAY hGX hGY
    hL₁ fun P hP => ?_) (le_sub_iff_add_le.mp ?_)
  · have := isDiscrepancy_le_of_not_isExceptional hWLC hWp hWq hpb hqb KF P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
    linarith [hcoeff P]
  · rw [sub_eq_add_neg, ← map_neg]
    refine le_add_of_forall_not_isExceptional_le hYn hWq hqb hpq.symm hcomm.symm hYc hfnef hGY hGX
      (by simpa using hL₁.neg) fun P hP => ?_
    have := isDiscrepancy_le_of_not_isExceptional_target hWLC hexc hWp hWq hpb hqb KF P
      (fun h => hP ⟨hWq, hqb, inferInstance, h⟩) _ _ (haY P) (haX P)
    rw [map_neg]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.neg_apply] at hcoeff this ⊢
    linarith [hcoeff P]

end MMP.Flips
