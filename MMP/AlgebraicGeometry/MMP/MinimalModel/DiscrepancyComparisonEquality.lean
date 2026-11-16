module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical

/-!
# Equality in the comparison of discrepancies over a common base

Let `f : X ⟶ Z` and `g : Y ⟶ Z` be proper birational morphisms of normal varieties, `D` an
`ℝ`-divisor on `Z`, and `E_X`, `E_Y` `ℝ`-divisors on `X`, `Y` supported on the prime divisors
exceptional over `Z`. Put `B_X = f⁻¹_*D + E_X`, `B_Y = g⁻¹_*D + E_Y`, `A_X = K_X + B_X`,
`A_Y = K_Y + B_Y` for compatible canonical divisors, and assume that `-A_X` is `ℝ`-Cartier and
`f`-nef and that `A_Y` is `ℝ`-Cartier and `g`-nef. For a divisor `B` of `k(Z)` with nonempty
center on `Z`, `a(B, X, B_X) ≤ a(B, Y, B_Y)` (`MMP.Flips.isDiscrepancy_le_of_isRelativelyNef`).
If `b` is the generic point of `Center_Z(B)`, equality holds if and only if `A_X` is numerically
trivial on `f⁻¹(b)` and `A_Y` is numerically trivial on `g⁻¹(b)`.

On a common normal model `p : W ⟶ X`, `q : W ⟶ Y`, `h = p ≫ f = q ≫ g`, on which `B = ord_{P₀}`
for a prime divisor `P₀` of `W`, the `ℝ`-divisor
`F = p^*A_X - q^*A_Y + (div_W(q^*ω_Y) - div_W(p^*ω_X))` has coefficient
`a(P, Y, B_Y) - a(P, X, B_X)` along every prime divisor `P` of `W`, vanishes along the prime
divisors not exceptional over `Z`, and has `-F` `h`-nef. By the negativity lemma it is effective
and every fibre of `h` lies in `Supp F` or misses it; and `h(η_{P₀}) = b`. So equality holds iff
`η_{P₀} ∉ Supp F` iff `h⁻¹(b) ∩ Supp F = ∅`.

If `h⁻¹(b)` misses `Supp F`, take the open `U = Z ∖ h(Supp F) ∋ b`. A curve `C ⊆ X` contracted
by `f` to a point of `U` lifts to a curve `C' ⊆ W` with `p(C') = C`, contracted by `h` and
disjoint from `Supp F`, so `F · C' = 0`. Since `p^*A_X · C' ≤ 0`, `q^*A_Y · C' ≥ 0` and the
principal part has degree zero, both vanish, and the projection formula
`p^*A_X · C' = [k(C') : k(C)] (A_X · C)` gives `A_X · C = 0`; likewise for `A_Y`. Conversely, if
`A_X` and `A_Y` are numerically trivial over `b`, the projection formula makes `F` numerically
trivial over `b`, and
`MMP.Flips.disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field`
gives `h⁻¹(b) ∩ Supp F = ∅`.

## Main results

* `MMP.Flips.isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint`.

## Implementation notes

The setting is that of `MMP.Flips.isDiscrepancy_le_of_isRelativelyNef`: `X` and `Y` are
`k`-varieties through `f ≫ s_Z` and `g ≫ s_Z`, the canonical divisors are `K_X = div_X(f^*ω)`
and `K_Y = div_Y(g^*ω)` for one rational top form `ω` on `Z`, and the divisor `B` is a valuation
`v` of `k(Z)` with transports `v_X`, `v_Y` to `k(X)`, `k(Y)`. The center `Center_Z(B)` is that of
a proper divisor `(Y', π, E)` over `Z` with valuation `v`, and `b` is its generic point. The
discrepancies are given as values `a`, `a'` of the predicate `MMP.Flips.IsDiscrepancy`. The
source works over `ℂ`; the statement is made over a perfect field.

The discrepancies are computed with forms `ω_X`, `ω_Y` with `div ω_X = K_X`,
`div ω_Y = K_Y`; the principal divisor `div_W(q^*ω_Y) - div_W(p^*ω_X)` is Cartier and of degree
zero on every proper curve. Curves are lifted along `p` and `q` by
`MMP.Mori.ProperCurve.exists_image_closure_eq_of_surjective`, which holds over any field.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.28.2.2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.Flips

open MMP MMP.Mori

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
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] {f : Y ⟶ Z}
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  rw [← (AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    hf.functionFieldMap_bijective).toLinearEquiv.finrank_eq, Module.finrank_self]

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
  rw [degreeOver_eq_one hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rwa [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]

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

/-- **Projection formula** for a divisor `L₁` given as the pull-back of a Cartier divisor `D`
along `h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
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

/-! ### Intersection numbers of negatives, pull-backs and lifted curves -/

section Curves

variable {k : Type u} [Field k]

/-- Negating a presentation negates the intersection number. -/
private theorem isRIntersectionNumber_neg {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {C : ProperCurve sX} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) : IsRIntersectionNumber k sX (-D) (-r) L C (-x) := by
  obtain ⟨hL, d, rfl, hd, rfl⟩ := h
  exact ⟨hL, d, by simp [neg_smul, Finset.sum_neg_distrib], hd,
    by simp [Finset.sum_neg_distrib]⟩

/-- An `ℝ`-Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_isRIntersectionNumber {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : RDivisor X}
    (hD : IsCartierCombination D) (C : ProperCurve sX) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX D r L C x := by
  obtain ⟨m, r, L, hL, hpres⟩ := hD
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  subst hpres
  exact ⟨m, r, L, _, isRIntersectionNumber_sum_degreeOn k sX C r L hL⟩

/-- If `-D` is `f`-nef, then `D · C ≤ 0` for every curve `C` contracted by `f`. -/
private theorem nonpos_of_isRelativelyNef_neg {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef k sX f (-D)) (C : ProperCurve sX) (hC : C.IsContractedBy f) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber k sX D r L C x) :
    x ≤ 0 := by
  obtain ⟨m', r', L', hL', hpres, hall⟩ := h
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hpres] at h1
  have h2 := (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _
    (isRIntersectionNumber_neg hx) h1
  have h3 := hall C hC _ h1
  linarith

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
private theorem exists_specializes_ne_of_isProperCurve {G : Scheme.{u}} {sG : G ⟶ Spec (.of k)}
    {p : G} (h : IsProperCurve sG p) : ∃ w, p ⤳ w ∧ w ≠ p := by
  by_contra hcon
  push Not at hcon
  have hsub : Subsingleton (closure ({p} : Set G)) :=
    ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext ((hcon a (specializes_iff_mem_closure.mpr ha)).trans
      (hcon b (specializes_iff_mem_closure.mpr hb)).symm)⟩
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h2 := @topologicalKrullDim_zero_of_discreteTopology (closure ({p} : Set G)) _
    (@Subsingleton.discreteTopology _ _ hsub)
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **Curve lifting.** Let `p : W ⟶ X` be a proper surjective morphism of varieties and `C ⊆ X` a
proper curve contracted by `f : X ⟶ Z`. Then there is a proper curve `C' ⊆ W` with `p(C') = C`;
it is contracted by `p ≫ f` and not by `p`. -/
private theorem exists_properCurve_lift {W X Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} (hW : Mori.IsVariety k sW) (hX : Mori.IsVariety k sX) (p : W ⟶ X)
    (hp : p ≫ sX = sW) [IsProper p] [Surjective p] (f : X ⟶ Z) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    ∃ C' : ProperCurve sW, p C'.point = C.point ∧ C'.IsContractedBy (p ≫ f) ∧
      ¬ C'.IsContractedBy p := by
  obtain ⟨C', hC'⟩ := MMP.Mori.ProperCurve.exists_image_closure_eq_of_surjective hW hX p hp C
  have hpt : p C'.point = C.point := by
    have h1 : closure {p C'.point} = closure {C.point} := by
      rw [← hC', ← Set.image_singleton, p.isClosedMap.closure_image_eq_of_continuous p.continuous]
    exact (inseparable_iff_closure_eq.2 h1).eq
  refine ⟨C', hpt, fun w hw => ?_, fun hcon => ?_⟩
  · have : p w ∈ closure {C.point} := hC' ▸ ⟨w, hw, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hC _ this, hpt]
  · obtain ⟨y, hy, hne⟩ := exists_specializes_ne_of_isProperCurve C.isProperCurve
    obtain ⟨w, hw, rfl⟩ : y ∈ p '' closure {C'.point} :=
      hC' ▸ specializes_iff_mem_closure.mp hy
    exact hne (by rw [hcon w hw, hpt])

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
  rw [ht, Scheme.Hom.comp_apply] at h1 h2
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
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) (hpb j).2]
    exact (hL₀ j).isCartier_pullback q (hpb j).1
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
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) (hpb j).2]
    exact (hL₀ j).isCartier_pullback q (hpb j).1
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hnc]

/-- **Pull-backs of relatively nef divisors are nef over the base.** Let `q : W ⟶ Y` be proper,
`g : Y ⟶ Z`, `N` a `g`-nef `ℝ`-Cartier divisor on `Y` and `G = q^*N`. Then `G · C' ≥ 0` for every
proper curve `C' ⊆ W` contracted by `q ≫ g`, for every presentation of `G`: by the projection
formula, `G · C' = [k(C') : k(q C')] (N · q C')` when `q(C')` is a curve, which is contracted by
`g`, and `G · C' = 0` when `q(C')` is a point. -/
private theorem nonneg_of_isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {h : W ⟶ Z}
    (hqg : q ≫ g = h) {N : RDivisor Y} (hN : IsRelativelyNef k sY g N) {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hC' : C'.IsContractedBy h) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C' x) : 0 ≤ x := by
  subst hqg
  by_cases hc : IsProperCurve sY (q C'.point)
  · obtain ⟨C, hCq⟩ : ∃ C : ProperCurve sY, C.point = q C'.point := ⟨⟨_, hc⟩, rfl⟩
    obtain ⟨m', r', L', hL', hpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    rw [← hpres] at hy
    rw [isRIntersectionNumber_pullback_eq_mul q hq hG C' C hCq hx hy]
    exact mul_nonneg (Nat.cast_nonneg _)
      (hall C (isContractedBy_of_comp q g C' C hCq hC') _ hy)
  · rw [isRIntersectionNumber_pullback_eq_zero q hq hG C' hc hx]

/-- If `N · C = 0` for every proper curve `C = q(C')` contracted by `g`, then `q^*N · C' = 0` for
a proper curve `C'` contracted by `q ≫ g`. -/
private theorem eq_zero_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {N : RDivisor Y}
    {G : RDivisor W} (hG : IsRCartierPullback q N G) (C' : ProperCurve sW)
    (hC' : C'.IsContractedBy (q ≫ g))
    (H : ∀ C : ProperCurve sY, C.point = q C'.point → C.IsContractedBy g →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber k sY N r L C x → x = 0)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') : x' = 0 := by
  by_cases hc : IsProperCurve sY (q C'.point)
  · obtain ⟨C, hCq⟩ : ∃ C : ProperCurve sY, C.point = q C'.point := ⟨⟨_, hc⟩, rfl⟩
    obtain ⟨m₀, r₀, L₀, -, hL₀, hNpres, -, -⟩ := id hG
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
    rw [← hNpres] at hy
    rw [isRIntersectionNumber_pullback_eq_mul q hq hG C' C hCq hx' hy,
      H C hCq (isContractedBy_of_comp q g C' C hCq hC') _ _ _ _ hy, mul_zero]
  · exact isRIntersectionNumber_pullback_eq_zero q hq hG C' hc hx'

/-- The pull-back of `-N` is the negative of the pull-back of `N`. -/
private theorem isRCartierPullback_neg {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {N : RDivisor X} {G : RDivisor Y}
    (h : IsRCartierPullback f N G) : IsRCartierPullback f (-N) (-G) := by
  obtain ⟨m, r, L, L', hL, rfl, hpb, rfl⟩ := h
  exact ⟨m, fun j => -r j, L, L', hL, by simp [neg_smul, Finset.sum_neg_distrib], hpb,
    by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  refine ⟨m, r, L', fun j => ?_, by simp only [toRDivisor_eq_mapCoeffs]⟩
  rw [← Divisor.IsPullback.pullback_eq (hL j) (hpb j).2]
  exact (hL j).isCartier_pullback f (hpb j).1

/-- The difference of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D - D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r (fun j => -r' j), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The sum of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_add {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add]

/-- A Cartier divisor `L₀` linearly equivalent to `0` has intersection number `0` with every proper
curve, for every presentation. -/
private theorem eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {L₀ : Divisor X} (hc : L₀.IsCartier) (h : L₀.LinearlyEquivalent 0)
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) r L C x) : x = 0 := by
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L₀)
    (fun _ => hc)
  have e : ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ = Divisor.toRDivisor L₀ := by simp
  rw [e] at h1
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1]
  simp [MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h]

/-- **Nefness of `q^*A_Y - p^*A_X - N`.** If `A_Y` is `g`-nef and `-A_X` is `f`-nef, then for
`p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g = h` and an `ℝ`-Cartier divisor `N` on `W` with
`N · C = 0` for every proper curve `C`, the divisor `q^*A_Y - p^*A_X - N` is `h`-nef. -/
private theorem isRelativelyNef_sub_of_isRCartierPullback {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (p : W ⟶ X) (q : W ⟶ Y) [IsProper p] [IsProper q] (hp : p ≫ sX = sW)
    (hq : q ≫ sY = sW) (f : X ⟶ Z) (g : Y ⟶ Z) {h : W ⟶ Z} (hpf : p ≫ f = h) (hqg : q ≫ g = h)
    {A_X : RDivisor X} {A_Y : RDivisor Y} (hAX : IsRelativelyNef k sX f (-A_X))
    (hAY : IsRelativelyNef k sY g A_Y) {G_X : RDivisor W} {G_Y : RDivisor W}
    (hGX : IsRCartierPullback p A_X G_X) (hGY : IsRCartierPullback q A_Y G_Y) {N : RDivisor W}
    (hNc : IsCartierCombination N)
    (hN0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW h (G_Y - G_X - N) := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_sub
    (isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY)
      (isCartierCombination_of_isRCartierPullback hGX)) hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mY, rY, LY, hLY, hYpres⟩ := isCartierCombination_of_isRCartierPullback hGY
  obtain ⟨mX, rX, LX, hLX, hXpres⟩ :=
    isCartierCombination_of_isRCartierPullback (isRCartierPullback_neg hGX)
  obtain ⟨mN, rN, LN, hLN, hNpres⟩ := hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hYpres hXpres hNpres
  have hY := isRIntersectionNumber_sum_degreeOn k sW C rY LY hLY
  have hX := isRIntersectionNumber_sum_degreeOn k sW C rX LX hLX
  have hN := isRIntersectionNumber_sum_degreeOn k sW C rN LN hLN
  rw [← hYpres] at hY
  rw [← hXpres] at hX
  rw [← hNpres] at hN
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hY hX
  have hsum' := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hsum hN
  have e : (1 : ℝ) • ((1 : ℝ) • G_Y + (1 : ℝ) • -G_X) + (-1 : ℝ) • N = G_Y - G_X - N := by
    simp only [one_smul, neg_one_smul]
    abel
  rw [e] at hsum'
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum']
  have h1 := nonneg_of_isRelativelyNef_of_isRCartierPullback q hq g hqg hAY hGY C hC hY
  have h2 := nonneg_of_isRelativelyNef_of_isRCartierPullback p hp f hpf hAX
    (isRCartierPullback_neg hGX) C hC hX
  rw [hN0 C hN]
  linarith

/-- Two nonzero rational top forms on a normal variety of dimension `n` over a perfect field have
linearly equivalent divisors. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ τ' : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr τ' () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 τ' hτ'
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, Scheme.ord_mul he (inv_ne_zero hc),
    ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm, coeff_divisorOfForm, e1, e2]
  ring

/-- The divisors of two nonzero rational top forms on a normal variety `X`, for two equal
structure morphisms, are linearly equivalent. -/
private theorem linearlyEquivalent_divisorOfForm_of_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {s₁ s₂ : X ⟶ Spec (.of k)} (e : s₁ = s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (hX : IsNormalVariety k s₂) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms s₁ n 1} {τ' : RationalPluriForms s₂ n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  subst e
  exact linearlyEquivalent_divisorOfForm hX hn hτ hτ'

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

/-- The valuation of `E` over `C` through `a ≫ b` is that over `B` through `a`, restricted along
`b^*`. -/
private theorem comap_valuationOver {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) (a : A ⟶ B)
    (b : B ⟶ C)
    [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    (E.valuationOver a).comap (functionFieldMap b) = E.valuationOver (a ≫ b) := by
  ext t
  change E.divisorialValuation (functionFieldMap a (functionFieldMap b t)) =
    E.divisorialValuation (functionFieldMap (a ≫ b) t)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of `E` over `C` through a morphism depends only on the morphism. -/
private theorem valuationOver_congr {A C : Scheme.{u}} [IsIntegral A] [IsIntegral C]
    [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) {h₁ h₂ : A ⟶ C} (e : h₁ = h₂)
    [IsDominant h₁] [IsDominant h₂] : E.valuationOver h₁ = E.valuationOver h₂ := by
  subst e
  rfl

section InverseTransform

variable {X Y : Scheme.{u}}

private theorem source_ι_comp_eq_of_toRationalMap_eq [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_terminal_from {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Conversely, let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If
`f` sends the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`,
then the strict transform of `P` under `f⁻¹` is `E`: the map `f⁻¹` is defined at `η_P`
(`MMP.Flips.RationalMap.isMorphismInCodimOne_inverse`), and `f` is injective on the points over
`η_P`, whose local ring is a valuation ring. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

end InverseTransform

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

/-- Let `p : W ⟶ X`, `f : X ⟶ Z` be proper birational morphisms of normal varieties and `P` a
prime divisor of `W` whose image in `Z` is the generic point of a prime divisor `Q`. Then there is
a prime divisor `P_X` of `X` with `ord_P = ord_{P_X}` and `f(η_{P_X}) = η_Q`, which is not
exceptional over `Z`. -/
private theorem exists_primeDivisor_valuation_eq_of_map_genericPoint_eq {k : Type u} [Field k]
    {W X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] (hZ : IsNormalVariety k sZ) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} [IsProper f] (hX : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} [IsProper p]
    (hWp : IsNormalVariety k (p ≫ f ≫ sZ)) (hpb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (hPQ : f (p P.genericPoint) = Q.genericPoint) :
    ∃ P_X : MMP.Mori.PrimeDivisor X,
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).valuation = P_X.divisorialValuation ∧
      f P_X.genericPoint = Q.genericPoint ∧ ¬ IsExceptionalPrimeDivisor sZ f P_X := by
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant p := hpb.isDominant
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (f (p P.genericPoint))) := by
    rw [hPQ]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    (p P.genericPoint)
  have hco : Order.coheight (p P.genericPoint) = 1 := by
    have h1 : ringKrullDim (X.presheaf.stalk (p P.genericPoint)) =
        ringKrullDim (Z.presheaf.stalk (f (p P.genericPoint))) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (f.stalkMap (p P.genericPoint))).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hPQ,
      Q.coheight_genericPoint] at h1
    exact_mod_cast h1
  have hne : ¬ (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).IsExceptional := fun h => by
    have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hX p hWp hpb P).mp
      ⟨hWp, hpb, inferInstance, h⟩
    rw [hco] at h2
    exact absurd h2 (by decide)
  obtain ⟨P_X, -, hη, -, hval⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hX _ hne
  have hfη : f P_X.genericPoint = Q.genericPoint := by
    rw [← hPQ]
    exact congrArg f hη.symm
  refine ⟨P_X, hval, hfη, fun h => ?_⟩
  have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hZ f hX hf P_X).mp h
  rw [hfη, Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, the birational map
`φ = g⁻¹ ∘ f : X ⇢ Y` satisfies `g ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    ∃ φ : X.RationalMap Y, Mori.RationalMap.IsBirational φ ∧ φ.compHom g = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hg
  set e := e₁.trans e₂.symm
  have h : e.IsOver f g := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ g =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

/-- A valuation of `k(Y)` is determined by its restriction to `k(Z)` along a birational
morphism `g : Y ⟶ Z`. -/
private theorem valuation_eq_of_comap_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {g : Y ⟶ Z} (hg : IsBirationalMorphism g) [IsDominant g]
    {v w : Valuation Y.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap g) = w.comap (functionFieldMap g)) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hg.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

/-- A divisor `v` of `k(Z)` with nonempty center on `Z` is, through a proper birational morphism
`f : X ⟶ Z`, the valuation of a divisor over `X`. -/
private theorem exists_valuation_eq_of_comap_eq {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsIntegral X] (hZ : IsNormalVariety k sZ)
    {f : X ⟶ Z} [IsProper f] (hX : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f)
    {v : Valuation Z.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sZ v)
    {vX : Valuation X.functionField ℤᵐ⁰}
    (hvX : haveI : IsDominant f := hf.isDominant
      vX.comap (functionFieldMap f) = v) :
    ∃ D₁ : ProperDivisorOver k (f ≫ sZ), D₁.valuation = vX := by
  haveI : IsDominant f := hf.isDominant
  obtain ⟨-, DZ, hDZ⟩ := hv
  obtain ⟨D₁, hD₁, -⟩ :=
    ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZ.1 f hX.1 hf DZ
  exact ⟨D₁, valuation_eq_of_comap_eq hf (hD₁.trans (hDZ.trans hvX.symm))⟩

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- The generic point of a prime divisor `E` lies in the support of every divisor in which `E`
has nonzero coefficient. -/
private theorem genericPoint_mem_supp_of_coeff_ne_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E ≠ 0) : E.genericPoint ∈ D.supp :=
  DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hDE, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩

/-- Over a prime divisor `P` of a model `p : W ⟶ X` lying over the generic point of a prime
divisor `Q` of `Z`, the discrepancy of `(X, f⁻¹_*D + E_X)` is `-coeff_Q D` when `E_X` is
supported on the prime divisors exceptional over `Z`. -/
private theorem isDiscrepancy_eq_neg_of_map_genericPoint_eq {k : Type u} [Field k]
    [PerfectField k] {W X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (hZ : IsNormalVariety k sZ) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Z} [IsProper f]
    [LocallyOfFiniteType (f ≫ sZ)] (hX : IsNormalVariety k (f ≫ sZ))
    (hf : IsBirationalMorphism f) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} [IsProper p]
    (hWp : IsNormalVariety k (p ≫ f ≫ sZ)) (hpb : IsBirationalMorphism p) {n : ℕ}
    {K_X : Divisor X} {D : RDivisor Z} {E_X : RDivisor X}
    (hEX : ∀ P : Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZ f P → E_X.coeff P = 0)
    {P : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor Z}
    (hPQ : f (p P.genericPoint) = Q.genericPoint) {a : ℝ}
    (ha : IsDiscrepancy (f ≫ sZ) n K_X (birationalInverseTransform f hf D + E_X)
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).valuation a) :
    a = -D Q := by
  obtain ⟨P_X, hv, hfX, hnX⟩ :=
    exists_primeDivisor_valuation_eq_of_map_genericPoint_eq hZ hX hf hWp hpb P Q hPQ
  rw [hv] at ha
  rw [ha.eq_neg_coeff, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply,
    birationalInverseTransform_apply_of_genericPoint_eq hZ f hX.1 hf D hfX,
    show E_X P_X = 0 from hEX P_X hnX, add_zero]

/-- If `L` is numerically trivial on the proper curve `C`, then
`(G - G' + L) · C = G · C - G' · C`. -/
private theorem isRIntersectionNumber_sub_add_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {G G' L : RDivisor W} (hLc : IsCartierCombination L) (C : ProperCurve sW)
    (hL0 : ∀ {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    {m₁ : ℕ} {r₁ : Fin m₁ → ℝ} {L₁ : Fin m₁ → Divisor W} {x₁ : ℝ}
    {m₂ : ℕ} {r₂ : Fin m₂ → ℝ} {L₂ : Fin m₂ → Divisor W} {x₂ : ℝ}
    {m₃ : ℕ} {r₃ : Fin m₃ → ℝ} {L₃ : Fin m₃ → Divisor W} {x₃ : ℝ}
    (hx₁ : IsRIntersectionNumber k sW G r₁ L₁ C x₁)
    (hx₂ : IsRIntersectionNumber k sW G' r₂ L₂ C x₂)
    (hx₃ : IsRIntersectionNumber k sW (G - G' + L) r₃ L₃ C x₃) : x₃ = x₁ - x₂ := by
  obtain ⟨_, _, _, x₄, hx₄⟩ := exists_isRIntersectionNumber (k := k) hLc C
  have hlin := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
  have hlin' := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hlin hx₄
  rw [show (1 : ℝ) • ((1 : ℝ) • G + (-1 : ℝ) • G') + (1 : ℝ) • L = G - G' + L by
    simp only [one_smul, neg_one_smul]; abel] at hlin'
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx₃ hlin', hL0 hx₄]
  ring

/-- **Vanishing on curves off `Supp F`.** Let `p : W ⟶ X`, `q : W ⟶ Y` be proper with
`p ≫ f = q ≫ g = h`, `-A_X` `f`-nef, `A_Y` `g`-nef, and `F = p^*A_X - q^*A_Y + L` with `L`
numerically trivial, `F` effective and `-F` `h`-nef. On a proper curve `C'` contracted by `h`
and not contained in `Supp F`, both `p^*A_X · C'` and `q^*A_Y · C'` vanish: `F · C' ≥ 0` by
effectivity, `F · C' ≤ 0` by nefness, and `F · C' = p^*A_X · C' - q^*A_Y · C'` is a difference
of a nonpositive and a nonnegative number. -/
private theorem eq_zero_of_notMem_supp {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (hW : IsNormalVariety k sW) (p : W ⟶ X) (q : W ⟶ Y) [IsProper p]
    [IsProper q] (hp : p ≫ sX = sW) (hq : q ≫ sY = sW) (f : X ⟶ Z) (g : Y ⟶ Z) {h : W ⟶ Z}
    (hpf : p ≫ f = h) (hqg : q ≫ g = h) {A_X : RDivisor X} {A_Y : RDivisor Y}
    (hAX : IsRelativelyNef k sX f (-A_X)) (hAY : IsRelativelyNef k sY g A_Y)
    {G_X G_Y : RDivisor W} (hGX : IsRCartierPullback p A_X G_X)
    (hGY : IsRCartierPullback q A_Y G_Y) {L : RDivisor W} (hLc : IsCartierCombination L)
    (hL0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    (hFeff : (G_X - G_Y + L).IsEffective) (hFnef : IsRelativelyNef k sW h (-(G_X - G_Y + L)))
    (C' : ProperCurve sW) (hC' : C'.IsContractedBy h) (hCS : C'.point ∉ (G_X - G_Y + L).supp) :
    (∀ {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
        IsRIntersectionNumber k sW G_X r L' C' x → x = 0) ∧
      (∀ {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
        IsRIntersectionNumber k sW G_Y r L' C' x → x = 0) := by
  have hGXc := isCartierCombination_of_isRCartierPullback hGX
  have hGYc := isCartierCombination_of_isRCartierPullback hGY
  have hFc := isCartierCombination_add (isCartierCombination_sub hGXc hGYc) hLc
  obtain ⟨_, _, _, x₁, hx₁⟩ := exists_isRIntersectionNumber (k := k) hGXc C'
  obtain ⟨_, _, _, x₂, hx₂⟩ := exists_isRIntersectionNumber (k := k) hGYc C'
  obtain ⟨_, _, _, x₃, hx₃⟩ := exists_isRIntersectionNumber (k := k) hFc C'
  have h3 := IsRIntersectionNumber.nonneg_of_isEffective k sW hW _ hFc hFeff C' hCS _ _ hx₃
  have h3' := nonpos_of_isRelativelyNef_neg hFnef C' hC' hx₃
  have hd := isRIntersectionNumber_sub_add_eq hLc C' (hL0 C') hx₁ hx₂ hx₃
  have hX0 := nonneg_of_isRelativelyNef_of_isRCartierPullback p hp f hpf hAX
    (isRCartierPullback_neg hGX) C' hC' (isRIntersectionNumber_neg hx₁)
  have hY0 := nonneg_of_isRelativelyNef_of_isRCartierPullback q hq g hqg hAY hGY C' hC' hx₂
  exact ⟨fun hx => ((IsRIntersectionNumber.eq_and_linear k sW C').1 _ _ _ _ _ _ _ hx
    hx₁).trans (by linarith), fun hx => ((IsRIntersectionNumber.eq_and_linear k sW C').1 _ _ _ _
    _ _ _ hx hx₂).trans (by linarith)⟩

/-- **Descent along a lifted curve.** If the pull-back `G = q^*N` is numerically trivial on a
proper curve `C' ⊆ W` not contracted by `q`, then `N` is numerically trivial on `C = q(C')`: by
the projection formula `0 = G · C' = [k(C') : k(C)] (N · C)`, and the degree is positive. -/
private theorem eq_zero_of_isRCartierPullback_of_eq_zero {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hnc : ¬ C'.IsContractedBy q)
    (C : ProperCurve sY) (hC : C.point = q C'.point)
    (h0 : ∀ {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW G r L C' x → x = 0)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor Y} {x : ℝ}
    (hx : IsRIntersectionNumber k sY N r L C x) : x = 0 := by
  obtain ⟨_, _, _, x', hx'⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hG) C'
  have e := isRIntersectionNumber_pullback_eq_mul q hq hG C' C hC hx' hx
  rw [h0 hx'] at e
  have hpos : (0 : ℝ) < residueFieldDegree q C'.point :=
    Nat.cast_pos.mpr (residueFieldDegree_pos q hq C' hnc)
  exact (mul_eq_zero.mp e.symm).resolve_left hpos.ne'

/-- If a proper divisor `D` over a variety `Z` has the same valuation as `Bv` and `b` is the
generic point of the center of `Bv`, then `D` maps its generic point to `b`. -/
private theorem map_genericPoint_eq_of_valuation_eq {k : Type u} [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ)
    {D Bv : ProperDivisorOver k sZ} (h : D.valuation = Bv.valuation) {b : Z}
    (hb : IsGenericPoint b (Bv.center : Set Z)) :
    D.toDivisorOver.f D.toDivisorOver.E.genericPoint = b := by
  rw [← ProperDivisorOver.center_eq_of_valuation_eq hZ h,
    ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint] at hb
  exact (hb.eq isGenericPoint_closure).symm

/-- **Numerical triviality over `b` off `Supp F`.** In the setting of `eq_zero_of_notMem_supp`,
with `p`, `q` surjective, if the fibre `h⁻¹(b)` misses `Supp F` then `A_X` is numerically trivial
on `f⁻¹(b)` and `A_Y` on `g⁻¹(b)`: a curve contracted over `U = Z ∖ h(Supp F)` lifts to `W`. -/
private theorem isNumericallyTrivialOverPoint_of_disjoint_supp {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (hW : IsNormalVariety k sW)
    (hXv : Mori.IsVariety k sX) (hYv : Mori.IsVariety k sY) (p : W ⟶ X) (q : W ⟶ Y) [IsProper p]
    [IsProper q] [Surjective p] [Surjective q] (hp : p ≫ sX = sW) (hq : q ≫ sY = sW)
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsProper f] (hcomm : p ≫ f = q ≫ g) {A_X : RDivisor X}
    {A_Y : RDivisor Y} (hAXc : IsCartierCombination A_X) (hAYc : IsCartierCombination A_Y)
    (hAX : IsRelativelyNef k sX f (-A_X)) (hAY : IsRelativelyNef k sY g A_Y)
    {G_X G_Y : RDivisor W} (hGX : IsRCartierPullback p A_X G_X)
    (hGY : IsRCartierPullback q A_Y G_Y) {L : RDivisor W} (hLc : IsCartierCombination L)
    (hL0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    (hFeff : (G_X - G_Y + L).IsEffective)
    (hFnef : IsRelativelyNef k sW (p ≫ f) (-(G_X - G_Y + L))) {b : Z}
    (hdisj : Disjoint ((p ≫ f).base ⁻¹' {b}) ((G_X - G_Y + L).supp : Set W)) :
    IsNumericallyTrivialOverPoint k sX f A_X b ∧ IsNumericallyTrivialOverPoint k sY g A_Y b := by
  let U : Z.Opens := ⟨((p ≫ f).base '' ((G_X - G_Y + L).supp : Set W))ᶜ,
    ((p ≫ f).isClosedMap _ (G_X - G_Y + L).supp.isClosed).isOpen_compl⟩
  have hbU : b ∈ U := fun ⟨w, hw, hwb⟩ => Set.disjoint_left.mp hdisj hwb hw
  have hzero (C' : ProperCurve sW) (hC' : C'.IsContractedBy (p ≫ f))
      (hU : (p ≫ f) C'.point ∈ U) :=
    eq_zero_of_notMem_supp hW p q hp hq f g rfl hcomm.symm hAX hAY hGX hGY hLc hL0
      hFeff hFnef C' hC' fun hm => hU ⟨_, hm, rfl⟩
  refine ⟨⟨hAXc, U, hbU, fun C hC hCU _ _ m r L' x hx => ?_⟩,
    ⟨hAYc, U, hbU, fun C hC hCU _ _ m r L' x hx => ?_⟩⟩
  · obtain ⟨C', hpt, hC', hnc⟩ := exists_properCurve_lift hW.1 hXv p hp f C hC
    exact eq_zero_of_isRCartierPullback_of_eq_zero p hp hGX C' hnc C hpt.symm
      (hzero C' hC' (by rwa [Scheme.Hom.comp_apply, hpt])).1 hx
  · obtain ⟨C', hpt, hC', hnc⟩ := exists_properCurve_lift hW.1 hYv q hq g C hC
    rw [← hcomm] at hC'
    exact eq_zero_of_isRCartierPullback_of_eq_zero q hq hGY C' hnc C hpt.symm
      (hzero C' hC' (by rwa [hcomm, Scheme.Hom.comp_apply, hpt])).2 hx

/-- If `A_X` is numerically trivial on `f⁻¹(b)` and `A_Y` on `g⁻¹(b)`, then
`F = p^*A_X - q^*A_Y + L`, with `L` numerically trivial, is numerically trivial on `h⁻¹(b)` for
`h = p ≫ f = q ≫ g`. -/
private theorem isNumericallyTrivialOverPoint_sub_add {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (p : W ⟶ X) (q : W ⟶ Y)
    [IsProper p] [IsProper q] (hp : p ≫ sX = sW) (hq : q ≫ sY = sW) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hcomm : p ≫ f = q ≫ g) {A_X : RDivisor X} {A_Y : RDivisor Y} {G_X G_Y : RDivisor W}
    (hGX : IsRCartierPullback p A_X G_X) (hGY : IsRCartierPullback q A_Y G_Y) {L : RDivisor W}
    (hLc : IsCartierCombination L)
    (hL0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0) {b : Z}
    (hXb : IsNumericallyTrivialOverPoint k sX f A_X b)
    (hYb : IsNumericallyTrivialOverPoint k sY g A_Y b) :
    IsNumericallyTrivialOverPoint k sW (p ≫ f) (G_X - G_Y + L) b := by
  obtain ⟨-, UX, hbX, hallX⟩ := hXb
  obtain ⟨-, UY, hbY, hallY⟩ := hYb
  have hGXc := isCartierCombination_of_isRCartierPullback hGX
  have hGYc := isCartierCombination_of_isRCartierPullback hGY
  refine ⟨isCartierCombination_add (isCartierCombination_sub hGXc hGYc) hLc, UX ⊓ UY,
    ⟨hbX, hbY⟩, fun C' hC' hU hcl hclosed m r L' x hx => ?_⟩
  obtain ⟨_, _, _, x₁, hx₁⟩ := exists_isRIntersectionNumber (k := k) hGXc C'
  obtain ⟨_, _, _, x₂, hx₂⟩ := exists_isRIntersectionNumber (k := k) hGYc C'
  have hq' : ∀ w : W, (p ≫ f) w = g (q w) := fun w => by rw [hcomm, Scheme.Hom.comp_apply]
  rw [isRIntersectionNumber_sub_add_eq hLc C' (hL0 C') hx₁ hx₂ hx,
    eq_zero_of_isRCartierPullback p hp f hGX C' hC'
      (fun C hC _ m r L x hx => hallX C ‹_› (by rw [hC]; exact hU.1) (by rwa [hC])
        (by rwa [hC]) m r L x hx) hx₁,
    eq_zero_of_isRCartierPullback q hq g hGY C' (hcomm ▸ hC')
      (fun C hC _ m r L x hx => hallY C ‹_› (by rw [hC, ← hq']; exact hU.2)
        (by rwa [hC, ← hq']) (by rwa [hC, ← hq']) m r L x hx) hx₂,
    sub_zero]

/-- **Vanishing along `P₀` and numerical triviality over `b`.** In the setting of
`isNumericallyTrivialOverPoint_of_disjoint_supp`, with `h = p ≫ f` proper birational onto a normal
variety `Z`, `F = p^*A_X - q^*A_Y + L` supported on `h`-exceptional primes and `h(η_{P₀}) = b`,
the coefficient of `F` along `P₀` vanishes if and only if `A_X` is numerically trivial on `f⁻¹(b)`
and `A_Y` on `g⁻¹(b)`. -/
private theorem coeff_eq_zero_iff_isNumericallyTrivialOverPoint {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ)
    (hW : IsNormalVariety k sW) (hXv : Mori.IsVariety k sX) (hYv : Mori.IsVariety k sY)
    (p : W ⟶ X) (q : W ⟶ Y) [IsProper p] [IsProper q] [Surjective p] [Surjective q]
    (hp : p ≫ sX = sW) (hq : q ≫ sY = sW) (f : X ⟶ Z) (g : Y ⟶ Z) [IsProper f]
    (hWZ : (p ≫ f) ≫ sZ = sW) (hhb : IsBirationalMorphism (p ≫ f)) (hcomm : p ≫ f = q ≫ g)
    {A_X : RDivisor X} {A_Y : RDivisor Y} (hAXc : IsCartierCombination A_X)
    (hAYc : IsCartierCombination A_Y) (hAX : IsRelativelyNef k sX f (-A_X))
    (hAY : IsRelativelyNef k sY g A_Y) {G_X G_Y : RDivisor W} (hGX : IsRCartierPullback p A_X G_X)
    (hGY : IsRCartierPullback q A_Y G_Y) {L : RDivisor W} (hLc : IsCartierCombination L)
    (hL0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    (hFexc : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ (p ≫ f) P →
      (G_X - G_Y + L).coeff P = 0)
    (hFnef : IsRelativelyNef k sW (p ≫ f) (-(G_X - G_Y + L))) {P₀ : Mori.PrimeDivisor W} {b : Z}
    (hηb : (p ≫ f) P₀.genericPoint = b) :
    (G_X - G_Y + L).coeff P₀ = 0 ↔
      IsNumericallyTrivialOverPoint k sX f A_X b ∧ IsNumericallyTrivialOverPoint k sY g A_Y b := by
  have hFc := isCartierCombination_add (isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGX)
    (isCartierCombination_of_isRCartierPullback hGY)) hLc
  obtain ⟨hFeff, hfib⟩ :=
    isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sZ sW hZ hW
      (p ≫ f) hWZ hhb hFc hFexc hFnef
  have hηb' : (p ≫ f).base P₀.genericPoint ∈ ({b} : Set Z) := hηb
  refine ⟨fun h0 => ?_, fun ⟨hXb, hYb⟩ => ?_⟩
  · exact isNumericallyTrivialOverPoint_of_disjoint_supp hW hXv hYv p q hp hq f g hcomm hAXc hAYc
      hAX hAY hGX hGY hLc hL0 hFeff hFnef <| (hfib b).resolve_left fun hsub =>
        genericPoint_notMem_supp_of_coeff_eq_zero h0 (hsub hηb')
  · by_contra h0
    exact Set.disjoint_left.mp
      (disjoint_preimage_singleton_supp_of_isNumericallyTrivialOverPoint_of_field k sZ sW hZ hW
        (p ≫ f) hWZ hhb hFc hFeff hFexc hFnef b
        (isNumericallyTrivialOverPoint_sub_add p q hp hq f g hcomm hGX hGY hLc hL0 hXb hYb))
      hηb' (genericPoint_mem_supp_of_coeff_ne_zero h0)

/-- **Equality in the comparison of discrepancies** (FA 2.28.2.2). In the setting of
`MMP.Flips.isDiscrepancy_le_of_isRelativelyNef` — `f : X ⟶ Z`, `g : Y ⟶ Z` proper birational
morphisms of normal varieties over a perfect field, `K_X = div_X(f^*ω)`, `K_Y = div_Y(g^*ω)`,
`B_X = f⁻¹_*D + E_X`, `B_Y = g⁻¹_*D + E_Y` with `E_X`, `E_Y` exceptional over `Z`,
`-(K_X + B_X)` `ℝ`-Cartier and `f`-nef, `K_Y + B_Y` `ℝ`-Cartier and `g`-nef — let `v` be a
divisor of `k(Z)` with nonempty center on `Z`, `v_X`, `v_Y` the same divisor of `k(X)`, `k(Y)`,
and `b` the generic point of the center of `v` on `Z`. Then `a(v_X, X, B_X) = a(v_Y, Y, B_Y)` if
and only if `K_X + B_X` is numerically trivial on `f⁻¹(b)` and `K_Y + B_Y` is numerically
trivial on `g⁻¹(b)`. -/
@[mmp "prop_fa2_discrepancy_comparison_equality"]
public theorem isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint {k : Type u} [Field k]
    [PerfectField k] {X Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z]
    [QuasiCompact sZ] [LocallyOfFiniteType sZ] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hZ : IsNormalVariety k sZ) {f : X ⟶ Z} {g : Y ⟶ Z} [IsProper f] [IsProper g]
    (hX : IsNormalVariety k (f ≫ sZ)) (hY : IsNormalVariety k (g ≫ sZ))
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g)
    {n : ℕ} {ω : RationalPluriForms sZ n 1} {K_X : Divisor X} {K_Y : Divisor Y}
    (hKX : haveI : IsDominant f := hf.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ f ω) = K_X)
    (hKY : haveI : IsDominant g := hg.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ g ω) = K_Y)
    {D : RDivisor Z} {E_X : RDivisor X} {E_Y : RDivisor Y}
    (hEX : ∀ P : Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZ f P → E_X.coeff P = 0)
    (hEY : ∀ P : Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sZ g P → E_Y.coeff P = 0)
    (hAX : IsRelativelyNef k (f ≫ sZ) f
      (-logCanonicalDivisor K_X (birationalInverseTransform f hf D + E_X)))
    (hAY : IsRelativelyNef k (g ≫ sZ) g
      (logCanonicalDivisor K_Y (birationalInverseTransform g hg D + E_Y)))
    {v : Valuation Z.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sZ v)
    {vX : Valuation X.functionField ℤᵐ⁰} {vY : Valuation Y.functionField ℤᵐ⁰}
    (hvX : haveI : IsDominant f := hf.isDominant
      vX.comap (functionFieldMap f) = v)
    (hvY : haveI : IsDominant g := hg.isDominant
      vY.comap (functionFieldMap g) = v)
    {Bv : ProperDivisorOver k sZ} (hBv : Bv.valuation = v)
    {b : Z} (hb : IsGenericPoint b (Bv.center : Set Z)) {a a' : ℝ}
    (ha : IsDiscrepancy (f ≫ sZ) n K_X (birationalInverseTransform f hf D + E_X) vX a)
    (ha' : IsDiscrepancy (g ≫ sZ) n K_Y (birationalInverseTransform g hg D + E_Y) vY a') :
    a = a' ↔
      IsNumericallyTrivialOverPoint k (f ≫ sZ) f
          (logCanonicalDivisor K_X (birationalInverseTransform f hf D + E_X)) b ∧
        IsNumericallyTrivialOverPoint k (g ≫ sZ) g
          (logCanonicalDivisor K_Y (birationalInverseTransform g hg D + E_Y)) b := by
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant g := hg.isDominant
  obtain ⟨D₁, hD₁⟩ := exists_valuation_eq_of_comap_eq hZ hX hf hv hvX
  -- a common normal model `W` of `X` and `Y` over `Z` on which `B` is a prime divisor `P₀`
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hg
  obtain ⟨W, p, q, hWp, hpb, hpP, hqP, hqb, -, hcomm, P₀, hP₀⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hY
      f g φ hφ hφS D₁.toDivisorOver
  haveI := hpP
  haveI := hqP
  have hqW : q ≫ g ≫ sZ = p ≫ f ≫ sZ := by rw [← Category.assoc, ← hcomm, Category.assoc]
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ f ≫ sZ) := hWp.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ f ≫ sZ)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ f ≫ sZ)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWq : IsNormalVariety k (q ≫ g ≫ sZ) := hqW ▸ hWp
  haveI := hWq.1.toLocallyOfFiniteType
  haveI := hX.1.toLocallyOfFiniteType
  haveI := hY.1.toLocallyOfFiniteType
  haveI := hX.1.toQuasiCompact
  haveI := hY.1.toQuasiCompact
  haveI := hX.1.toIsSeparated
  haveI := hY.1.toIsSeparated
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hhb : IsBirationalMorphism (p ≫ f) := isBirationalMorphism_comp_of_isBirational f p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb)
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  haveI : Surjective q := surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  -- `B` is `ord_{P₀}` on `X` and on `Y`
  have hvalX : (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P₀⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).valuation = vX := hP₀.trans hD₁
  have hvalY : (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P₀⟩ inferInstance :
      ProperDivisorOver k (g ≫ sZ)).valuation = vY := by
    refine valuation_eq_of_comap_eq hg ?_
    rw [hvY, ← hvX, ← hvalX]
    change (P₀.valuationOver q).comap (functionFieldMap g) =
      (P₀.valuationOver p).comap (functionFieldMap f)
    rw [comap_valuationOver, comap_valuationOver]
    exact valuationOver_congr P₀ hcomm.symm
  -- `h(η_{P₀}) = b`
  have hWZ : IsNormalVariety k ((p ≫ f) ≫ sZ) := by rwa [Category.assoc]
  have hηb : (p ≫ f) P₀.genericPoint = b := by
    have hvalZ : (ProperDivisorOver.mk ⟨W, p ≫ f, hWZ, hhb, P₀⟩ inferInstance :
        ProperDivisorOver k sZ).valuation = Bv.valuation := by
      rw [hBv, ← hvX, ← hvalX]
      change P₀.valuationOver (p ≫ f) = (P₀.valuationOver p).comap (functionFieldMap f)
      rw [comap_valuationOver]
    exact map_genericPoint_eq_of_valuation_eq hZ.1 hvalZ hb
  -- the forms `ω_X`, `ω_Y` with `K_X = div ω_X`, `K_Y = div ω_Y` used in the discrepancies
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha'
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := f ≫ sZ) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := g ≫ sZ)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ f ≫ sZ),
      ← trdeg_functionField_eq_of_bijective (f ≫ sZ) p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := f ≫ sZ), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  -- `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms (g ≫ sZ) q ωY) -
        divisorOfForm (pullbackRationalPluriForms (f ≫ sZ) p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq hqW hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  have hL₁c : L₁.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hL₁ Divisor.isCartier_zero
  -- `p^*A_X`, `q^*A_Y` and `F = p^*A_X - q^*A_Y + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  have haX := fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hX ωX hwX.2.2.1 hKXc hBXc p
    hWp hpb hGX P
  have haY := fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hY ωY hwY.2.2.1 hKYc hBYc q
    hWq hqb hGY P
  obtain ⟨aX, haX_def⟩ : ∃ aX : MMP.Mori.PrimeDivisor W → ℝ, ∀ P, aX P =
      ((ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).toDivisorOver.ordPullback ωX : ℝ) - G_X.coeff P :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aY, haY_def⟩ : ∃ aY : MMP.Mori.PrimeDivisor W → ℝ, ∀ P, aY P =
      ((ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
        ProperDivisorOver k (g ≫ sZ)).toDivisorOver.ordPullback ωY : ℝ) - G_Y.coeff P :=
    ⟨_, fun _ => rfl⟩
  replace haX := fun P => (haX_def P) ▸ haX P
  replace haY := fun P => (haY_def P) ▸ haY P
  have hX1 : ∀ P, ((ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).toDivisorOver.ordPullback ωX : ℝ) =
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (f ≫ sZ) p ωX)) P :=
    fun _ => rfl
  have hY1 : ∀ P, ((ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
      ProperDivisorOver k (g ≫ sZ)).toDivisorOver.ordPullback ωY : ℝ) =
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (g ≫ sZ) q ωY)) P :=
    fun _ => rfl
  set F : RDivisor W := G_X - G_Y + Divisor.toRDivisor L₁ with hF_def
  have hcoeff : ∀ P, F.coeff P = aY P - aX P := by
    intro P
    rw [hF_def, haX_def, haY_def, hX1, hY1, hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have h1 : a = aX P₀ := ha.eq (hvalX ▸ haX P₀)
  have h2 : a' = aY P₀ := ha'.eq (hvalY ▸ haY P₀)
  -- `-F = q^*A_Y - p^*A_X - L₁` is nef over `Z`
  have hL₁r : IsCartierCombination (Divisor.toRDivisor L₁) :=
    ⟨1, fun _ => 1, fun _ => L₁, fun _ => hL₁c, by simp [← toRDivisor_eq_mapCoeffs]⟩
  have hL₁0 : ∀ (C : ProperCurve (p ≫ f ≫ sZ)) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W}
      {x : ℝ}, IsRIntersectionNumber k _ (Divisor.toRDivisor L₁) r L C x → x = 0 :=
    fun C _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx
  have hFnef : IsRelativelyNef k (p ≫ f ≫ sZ) (p ≫ f) (-F) := by
    rw [show -F = G_Y - G_X - Divisor.toRDivisor L₁ by rw [hF_def]; abel]
    exact isRelativelyNef_sub_of_isRCartierPullback p q rfl hqW f g rfl hcomm.symm hAX hAY hGX hGY
      hL₁r hL₁0
  -- the coefficients of `F` along prime divisors not exceptional over `Z` vanish
  have hFexc : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ (p ≫ f) P →
      F.coeff P = 0 := by
    intro P hP
    have hne : ¬ (ProperDivisorOver.mk ⟨W, p ≫ f, hWZ, hhb, P⟩ inferInstance :
        ProperDivisorOver k sZ).IsExceptional := fun h => hP ⟨hWZ, hhb, inferInstance, h⟩
    obtain ⟨Q, -, hQ, -, -⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hZ _ hne
    have hQX : f (p P.genericPoint) = Q.genericPoint := hQ
    have hQY : g (q P.genericPoint) = Q.genericPoint := by
      rwa [← Scheme.Hom.comp_apply, ← hcomm]
    rw [hcoeff P, isDiscrepancy_eq_neg_of_map_genericPoint_eq hZ hY hg hWq hqb hEY hQY (haY P),
      isDiscrepancy_eq_neg_of_map_genericPoint_eq hZ hX hf hWp hpb hEX hQX (haX P), sub_self]
  rw [show a = a' ↔ F.coeff P₀ = 0 by rw [hcoeff, h1, h2]; exact (sub_eq_zero.trans eq_comm).symm]
  exact coeff_eq_zero_iff_isNumericallyTrivialOverPoint hZ hWp hX.1 hY.1 p q rfl hqW f g
    (Category.assoc _ _ _) hhb hcomm hBXc hBYc hAX hAY hGX hGY hL₁r hL₁0 hFexc hFnef hηb

end MMP.Flips
