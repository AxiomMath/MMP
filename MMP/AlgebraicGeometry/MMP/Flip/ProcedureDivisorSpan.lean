module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Deminormal.Dualizing
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.RegularImmersion.StalkDimension
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.QuasiSeparated
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction

/-!
# The divisor of a procedure datum generates the relative Néron–Severi space

Let `P = (π, (F_j), H')` be a procedure datum (`MMP.Flips.ProcedureDatum`) for `(X, D, f)`, with
`f : X ⟶ Z`, and let `h : Y ⟶ Z` be a proper birational morphism from a normal `ℚ`-factorial
variety `Y`. Then `N¹(Y/Z)` is spanned by the classes of the irreducible components of the strict
transform `h⁻¹_*H'` and of the `h`-exceptional prime divisors of `Y`: every `ℝ`-Cartier divisor
on `Y` is numerically `h`-equivalent to a real combination of these prime divisors.

On a log resolution `p : V ⟶ Y`, `q : V ⟶ Z'` of the graph of `Y ⤏ Z'`, a Cartier divisor `L`
on `Y` has `p^*L = q^*G + ∑ c_l Q_l` with `Q_l` `q`-exceptional; the span condition on the `F_j`
and the transform of numerically trivial divisors
(`MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver`) give
`L ≡_Z ∑ c'_j p_*q^*F_j + ∑ c_l p_*Q_l`, and condition (18.12.1.3) puts every non-exceptional
component of the right-hand side in `h⁻¹_*H'`.

## Main results

* `MMP.Flips.ProcedureDatum.exists_isNumericallyEquivalentOver_of_isQFactorial`.

## Implementation notes

As in the span condition `MMP.Flips.ProcedureDatum.span_F`, "the classes of the prime divisors
in a set `S` span `N¹(Y/Z)`" is stated as: every `ℝ`-Cartier divisor `L` on `Y` is numerically
`h`-equivalent (`MMP.Flips.IsNumericallyEquivalentOver`) to an `ℝ`-divisor supported on `S`. On a
`ℚ`-factorial `Y` such a divisor is `ℝ`-Cartier, so this is the spanning of
`MMP.Flips.RelativeNumericalDivisorClasses` by the classes of the members of `S`. The source
works over `ℂ`; the statement is made over an arbitrary field.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 18.12.1.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

universe u

namespace ProcedureDivisorSpan

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
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

/-- A normalization of a proper curve, of dimension at most one, is a curve. -/
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
private theorem degreeOn_comp_eq_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
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
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_comp_eq_of_isCurveNormalization C hν hdim _).symm

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

end Contracted

section QFactorial

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
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

section Graph

/-- A birational morphism from an irreducible scheme induces an isomorphism of local rings at the
generic point: it agrees with an open immersion on a dense open. -/
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
`η` of `X`, then `η` is the only point of its fibre: it is closed in the fibre, its residue field
being finite over that of `f(η)`, and it specializes to every point of `X`. -/
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
  have hxr : x ∈ Set.range (f.fiberι (f η)) := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  obtain ⟨b, rfl⟩ := hxr
  have hsp : f.asFiber η ⤳ b := by
    rw [← (f.fiberι (f η)).isEmbedding.specializes_iff, Scheme.Hom.fiberι_asFiber]
    exact genericPoint_specializes _
  have := hsp.mem_closed hcl rfl
  rw [Set.mem_singleton_iff] at this
  rw [this, Scheme.Hom.fiberι_asFiber]

/-- A dominant morphism from an irreducible scheme maps the generic point to a generic point of
the target. -/
private theorem isGenericPoint_map_genericPoint {X S : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ S) [IsDominant f] : IsGenericPoint (f (genericPoint X)) (Set.univ : Set S) := by
  rw [IsGenericPoint, ← MMP.Flips.closure_range_eq_closure_genericPoint f,
    f.denseRange.closure_range]

/-- Functoriality of the maps of function fields along dominant morphisms of integral schemes. -/
private theorem functionFieldMap_comp_apply' {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] {c : A ⟶ C}
    [IsDominant c] (hc : a ≫ b = c) (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap c t := by
  subst hc
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact (congrArg (fun φ => φ.hom t) this).symm

/-- The normalization of `Y' ×_Z Y` in `Spec k(Y)`, along a lift `gp` of the generic point of `Y`,
is finite over `Y' ×_Z Y`: the fibre product is Nagata and `k(Y)` is a finitely generated field
extension of every residue field below it. -/
private theorem isFinite_fromNormalization_lift {k : Type u} [Field k] {Y Y' Z : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [IsSeparated sY] [QuasiCompact sY]
    [IsIntegral Y] {h : Y ⟶ Z} {h' : Y' ⟶ Z} [IsProper h] [IsProper h']
    (gp : Spec Y.functionField ⟶ Limits.pullback h' h) [QuasiCompact gp] [QuasiSeparated gp]
    (hgsnd : gp ≫ Limits.pullback.snd h' h = Y.fromSpecStalk (genericPoint Y)) :
    IsFinite gp.fromNormalization := by
  have hP : IsNagataScheme (Limits.pullback h' h) :=
    isNagataScheme_of_locallyOfFiniteType (Limits.pullback.snd h' h ≫ sY)
      (isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_field)
  have : Finite (Spec Y.functionField) :=
    inferInstanceAs (Finite (PrimeSpectrum Y.functionField))
  refine isFinite_fromNormalization gp hP
    (fun U _ => have : Finite U := Subtype.finite
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) fun x => ?_
  let := (gp.residueFieldMap x.1).hom.toAlgebra
  have hsurj : Function.Surjective (gp.residueFieldMap x.1).hom := by
    have h := surjective_residueFieldMap_of_surjectiveOnStalks
      (Y.fromSpecStalk (genericPoint Y)) x.1
    rw [Scheme.Hom.residueFieldMap_congr hgsnd.symm, Scheme.residueFieldMap_comp] at h
    exact fun z => ⟨_, (h z).choose_spec⟩
  have : Algebra.EssFiniteType (Limits.pullback h' h |>.residueField (gp x.1))
      ((Spec Y.functionField).residueField x.1) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
  exact IntermediateField.fg_top _ _

/-- A dominant morphism `p : V ⟶ Y` of integral schemes through which the generic point
`Spec k(Y) ⟶ Y` factors is birational. -/
private theorem isBirational_of_comp_eq_fromSpecStalk {V Y : Scheme.{u}} [IsIntegral V]
    [IsIntegral Y] (j : Spec Y.functionField ⟶ V) [IsDominant j] (p : V ⟶ Y) [IsDominant p]
    [IsDominant (j ≫ p)] (hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y)) : IsBirational p := by
  refine isBirational_of_surjective_functionFieldMap _ fun w => ?_
  have hbij : Function.Bijective (functionFieldMap (j ≫ p)) := by
    rw! (castMode := .all) [hjp]
    exact bijective_functionFieldMap_fromSpecStalk_genericPoint Y
  obtain ⟨a, ha⟩ := hbij.2 (functionFieldMap j w)
  rw [← functionFieldMap_comp_apply' j p rfl] at ha
  exact ⟨a, (functionFieldMap j).injective ha⟩

/-- If `p ≫ h = q ≫ h'` and `p`, `h`, `h'` induce isomorphisms of local rings at `x`, `p x` and
`q x`, then so does `q` at `x`. -/
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

/-- A morphism of irreducible schemes sending the generic point to the generic point and inducing
an isomorphism of local rings there is birational. -/
private theorem isBirational_of_isIso_stalkMap_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (hf : IsIso (f.stalkMap (genericPoint X))) : IsBirational f := by
  refine isBirational_of_bijOn_of_isIso_stalkMap f ?_ fun x hx => ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hη
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact hf

/-- **The normalized graph over a lift of the generic point.** Let `h : Y ⟶ Z` and `h' : Y' ⟶ Z`
be proper birational morphisms, `Y` a normal variety over `k` and `Y'` integral, and let
`g₀ : Spec k(Y) ⟶ Y'` lift `Spec k(Y) ⟶ Y ⟶ Z`. The normalization `V` of the closure of the
image of `g₀` in `Y ×_Z Y'` is a normal variety with proper birational projections
`p : V ⟶ Y`, `q : V ⟶ Y'` and `p ≫ h = q ≫ h'`. -/
private theorem exists_normalizedGraph {k : Type u} [Field k] {Y Y' Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) [IsIntegral Y] [IsIntegral Y']
    {h : Y ⟶ Z} {h' : Y' ⟶ Z} [IsProper h] [IsProper h']
    (hh : IsBirationalMorphism h) (hh' : IsBirationalMorphism h')
    (g₀ : Spec Y.functionField ⟶ Y')
    (hcond : g₀ ≫ h' = Y.fromSpecStalk (genericPoint Y) ≫ h) :
    ∃ (V : Scheme.{u}) (p : V ⟶ Y) (q : V ⟶ Y'),
      IsNormalVariety k (p ≫ sY) ∧ p ≫ h = q ≫ h' ∧ IsProper p ∧ IsProper q ∧
      IsBirational p ∧ IsBirational q := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  let gp : Spec Y.functionField ⟶ Limits.pullback h' h := Limits.pullback.lift _ _ hcond
  haveI : QuasiCompact gp := quasiCompact_of_isField (Field.toIsField _) _
  haveI : QuasiSeparated gp := QuasiSeparated.of_quasiSeparatedSpace _
  have hgsnd : gp ≫ Limits.pullback.snd h' h = Y.fromSpecStalk (genericPoint Y) :=
    Limits.pullback.lift_snd _ _ _
  have hjν : gp.toNormalization ≫ gp.fromNormalization = gp :=
    Scheme.Hom.toNormalization_fromNormalization gp
  haveI : IsFinite gp.fromNormalization := isFinite_fromNormalization_lift sY gp hgsnd
  haveI : IsNormal gp.normalization :=
    isNormal_normalization_of_isField (Field.toIsField _) _
  set V := gp.normalization
  set j := gp.toNormalization
  set p : V ⟶ Y := gp.fromNormalization ≫ Limits.pullback.snd h' h with hp_def
  set q : V ⟶ Y' := gp.fromNormalization ≫ Limits.pullback.fst h' h with hq_def
  have hjp : j ≫ p = Y.fromSpecStalk (genericPoint Y) := by
    rw [hp_def, ← Category.assoc, hjν, hgsnd]
  have hpq : p ≫ h = q ≫ h' := by
    simp only [hp_def, hq_def, Category.assoc, Limits.pullback.condition]
  haveI : IsProper p := by rw [hp_def]; infer_instance
  haveI : IsProper q := by rw [hq_def]; infer_instance
  -- `p` is birational
  letI := isDominant_fromSpecStalk_genericPoint Y
  have : IsDominant (j ≫ p) := by rw [hjp]; infer_instance
  haveI : IsDominant p := IsDominant.of_comp j _
  have hpB : IsBirational p := isBirational_of_comp_eq_fromSpecStalk j p hjp
  have hpη : p (genericPoint V) = genericPoint Y := map_genericPoint_of_isDominant p
  -- `q` maps the generic point of `V` to that of `Y'`
  have hqη : q (genericPoint V) = genericPoint Y' := by
    refine eq_genericPoint_of_map_eq h' (isIso_stalkMap_genericPoint h' hh') ?_
    haveI := hh.isDominant
    haveI := hh'.isDominant
    have e1 : h' (q (genericPoint V)) = h (genericPoint Y) := by
      rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hpη]
    rw [e1]
    exact (isGenericPoint_map_genericPoint h).eq (isGenericPoint_map_genericPoint h')
  -- `q` induces an isomorphism of local rings at the generic point
  have hqstalk := isIso_stalkMap_of_comp_eq hpq (genericPoint V)
    (hpB.2 _ (by rw [genericPoints_eq_singleton]; rfl))
    (by rw [hpη]; exact isIso_stalkMap_genericPoint h hh)
    (by rw [hqη]; exact isIso_stalkMap_genericPoint h' hh')
  have hqB : IsBirational q := isBirational_of_isIso_stalkMap_genericPoint q hqη hqstalk
  have hV : IsNormalVariety k (p ≫ sY) :=
    ⟨(MMP.Mori.isVariety_iff k (p ≫ sY)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨V, p, q, hV, hpq, inferInstance, inferInstance, hpB, hqB⟩

/-- **A lift of the generic point along a birational morphism.** For a birational morphism
`π : Z' ⟶ Z` of integral schemes and a morphism `h : Y ⟶ Z` from an integral scheme sending the
generic point of `Y` to that of `Z`, the point `Spec k(Y) ⟶ Y ⟶ Z` lifts to `Z'`: `π` induces an
isomorphism `𝒪_{Z,η} ≅ k(Z')` at the generic points. -/
private theorem exists_comp_eq_fromSpecStalk {Y Z Z' : Scheme.{u}} [IsIntegral Y] [IsIntegral Z']
    (h : Y ⟶ Z) (π : Z' ⟶ Z) (hπ : IsBirationalMorphism π)
    (hη : h (genericPoint Y) = π (genericPoint Z')) :
    ∃ g₀ : Spec Y.functionField ⟶ Z', g₀ ≫ π = Y.fromSpecStalk (genericPoint Y) ≫ h := by
  haveI := isIso_stalkMap_genericPoint π hπ
  have hs : h (genericPoint Y) ⤳ π (genericPoint Z') := hη ▸ specializes_rfl
  refine ⟨Spec.map (inv (π.stalkMap (genericPoint Z')) ≫ Z.presheaf.stalkSpecializes hs ≫
    h.stalkMap (genericPoint Y)) ≫ Z'.fromSpecStalk (genericPoint Z'), ?_⟩
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

end Graph

section Separated

/-- **Separatedness descends along universally closed surjections.** If `h : Y ⟶ Z` is
universally closed and surjective and `h ≫ s` is separated, then `s` is separated: the diagonal
of `s` has closed image, the image of the diagonal of `h ≫ s` under the closed map `h ×_S h`. -/
private theorem isSeparated_of_surjective {Y Z S : Scheme.{u}} (h : Y ⟶ Z) (s : Z ⟶ S)
    [UniversallyClosed h] [Surjective h] [IsSeparated (h ≫ s)] : IsSeparated s := by
  let m := Limits.pullback.map (h ≫ s) (h ≫ s) s s h h (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) inferInstance inferInstance rfl rfl
  have key : Limits.pullback.diagonal (h ≫ s) ≫ m = h ≫ Limits.pullback.diagonal s := by
    ext <;> simp [m]
  have hrange : Set.range (Limits.pullback.diagonal s) =
      m '' Set.range (Limits.pullback.diagonal (h ≫ s)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := ‹Surjective h›.surj z
      exact ⟨_, ⟨y, rfl⟩, by rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨h y, by rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply]⟩
  have hcl : IsClosed (Set.range (Limits.pullback.diagonal s)) := by
    rw [hrange]
    exact m.isClosedMap _ (Limits.pullback.diagonal (h ≫ s)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

end Separated

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

private theorem coe_transform_eq_closure_singleton [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
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

/-- If the strict transform of `P` under `φ` is `E` and `g'` represents `φ` at `η_P`, then
`η_E = g'(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    MMP.Mori.RationalMap.definedAt_iff.mp
      (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

private theorem isSeparated_toTerminal_of_isSeparated {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

end InverseTransform

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

/-- **Pull-backs of numerically trivial combinations.** If `∑ s_i M_i` is numerically trivial over
`π : Y ⟶ Z`, then `∑ s_i f^*M_i` is numerically trivial over `g = f ≫ π`. -/
private theorem isNumericallyTrivialOver_sum_pullback {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) {π : Y ⟶ Z} {g : X ⟶ Z} (hg : g = f ≫ π)
    {m : ℕ} (s : Fin m → ℝ) {M : Fin m → Divisor Y} (hM : ∀ i, (M i).IsCartier)
    (hB : ∀ i, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (M i).supp)
    (hG : IsNumericallyTrivialOver k sY π (∑ i, s i • Divisor.toRDivisor (M i))) :
    IsNumericallyTrivialOver k sX g
      (∑ i, s i • Divisor.toRDivisor ((M i).pullback (hM i) (hB i))) := by
  have hMf : ∀ i, ((M i).pullback (hM i) (hB i)).IsCartier :=
    fun i => (hM i).isCartier_pullback f (hB i)
  refine ⟨⟨m, s, _, hMf, by simp only [toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [eq_zero_of_isRIntersectionNumber_zero k sX h₂]
  obtain ⟨hL₁, hD₁, hx₁⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sX h₁
  rw [hx₁, sum_degreeOn_eq_of_sum_eq k sX C hL₁ hMf hD₁.symm]
  exact sum_degreeOn_pullback_eq_zero f hf π s hM hB hG C (by rw [← hg]; exact hC)

end Negativity

/-- In an integral scheme, a point has coheight zero iff it is the generic point. -/
private theorem coheight_eq_zero_iff_eq_genericPoint {X : Scheme.{u}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  refine ⟨fun h ↦ Specializes.antisymm (Order.coheight_eq_zero.mp h (genericPoint_specializes x))
    (genericPoint_specializes x) |>.eq, ?_⟩
  rintro rfl
  exact Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z

section Codimension

/-- A prime divisor `F` of `Y` which is not exceptional over `Z`, for a proper birational
morphism `g : Y ⟶ Z` from a normal variety, maps to a point of coheight less than two: the
closure of `g(η_F)` has dimension the height of `g(η_F)`, and height plus coheight is at most
`dim Z`. -/
private theorem coheight_lt_two_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} (g : Y ⟶ Z) (hY : IsNormalVariety k (g ≫ sZ))
    (hg : IsBirationalMorphism g) [IsProper g] (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ IsExceptionalPrimeDivisor sZ g F) : Order.coheight (g F.genericPoint) < 2 := by
  by_contra! h2
  refine hF ⟨hY, hg, inferInstance, ?_⟩
  unfold ProperDivisorOver.IsExceptional
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, topologicalKrullDim_closure_singleton_eq_height]
  set z := g F.genericPoint
  haveI : Nonempty Z := ⟨z⟩
  rw [show topologicalKrullDim Z = Order.krullDim Z from
    Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  calc ((Order.height z : ℕ∞) : WithBot ℕ∞) + 2
      ≤ ((Order.height z + Order.coheight z : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        gcongr
        have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight z : WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr h2
        simpa using this
    _ ≤ Order.krullDim Z := by
        rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
        exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) z)

/-- A prime divisor `F` of `Y` which is not exceptional over `Z`, for a proper birational
morphism `g : Y ⟶ Z` of integral schemes from a normal variety, maps to a point of coheight one. -/
private theorem coheight_eq_one_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)} (g : Y ⟶ Z)
    (hY : IsNormalVariety k (g ≫ sZ)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) (hF : ¬ IsExceptionalPrimeDivisor sZ g F) :
    Order.coheight (g F.genericPoint) = 1 := by
  haveI : IsDominant g := hg.isDominant
  refine le_antisymm (Order.le_of_lt_add_one
    (coheight_lt_two_of_not_isExceptionalPrimeDivisor g hY hg F hF))
    (ENat.one_le_iff_ne_zero.mpr fun h0 => ?_)
  have h1 : F.genericPoint = genericPoint Y :=
    eq_genericPoint_of_map_eq g (isIso_stalkMap_genericPoint g hg)
      (((coheight_eq_zero_iff_eq_genericPoint _).mp h0).trans
        (map_genericPoint_of_isDominant g).symm)
  have h2 := F.coheight_genericPoint
  rw [h1, (coheight_eq_zero_iff_eq_genericPoint _).mpr rfl] at h2
  exact zero_ne_one h2

/-- A prime divisor `P₁` whose support contains the generic point of a prime divisor `P₀` is
`P₀`: both generic points have coheight one. -/
private theorem eq_of_genericPoint_mem_support {Z : Scheme.{u}}
    {P₀ P₁ : MMP.Mori.PrimeDivisor Z} (hmem : P₀.genericPoint ∈ P₁.support) : P₁ = P₀ := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have hsp : P₁.genericPoint ⤳ P₀.genericPoint := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
    exact specializes_iff_mem_closure.mpr hmem
  have hle : P₀.genericPoint ≤ P₁.genericPoint := Scheme.le_iff_specializes.mpr hsp
  have hnlt : ¬ P₀.genericPoint < P₁.genericPoint := fun hlt => by
    have h3 := Order.coheight_strictAnti hlt
      (by rw [P₁.coheight_genericPoint]; exact ENat.one_lt_top)
    rw [P₀.coheight_genericPoint, P₁.coheight_genericPoint] at h3
    exact lt_irrefl _ h3
  exact (hsp.antisymm (Scheme.le_iff_specializes.mp
    (not_not.mp fun H => hnlt (lt_of_le_not_ge hle H)))).eq

end Codimension

section InverseTransformAt

/-- Let `h : Y ⟶ Z` be a proper birational morphism of integral separated schemes with `Z`
normal and locally Noetherian. If `h` sends the generic point of a prime divisor `E` of `Y` to
that of a prime divisor `P` of `Z`, then the strict transform of `P` under `h⁻¹` is `E`: the map
`h⁻¹` is defined at `η_P` (a point of codimension one of the normal `Z`, and `h` is proper), and
`h` is injective on the points over `η_P`, whose local ring is a valuation ring. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] (h : Y ⟶ Z) [IsProper h]
    (hh : IsBirationalMorphism h) {P : MMP.Mori.PrimeDivisor Z} {E : MMP.Mori.PrimeDivisor Y}
    (hE : h E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hh) P =
      some E := by
  have : IsDominant h := hh.isDominant
  have hbij := hh.functionFieldMap_bijective
  obtain ⟨e, he, hinv⟩ := hh.isInverse_inverse
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ h :=
    (source_ι_comp_eq_of_toRationalMap_eq h e he).symm
  have hover : (MMP.Mori.RationalMap.IsBirational.inverse hh).compHom h =
      Scheme.Hom.toRationalMap (𝟙 Z) := by
    rw [← hinv]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change Z.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ h = Z.homOfLE _ ≫ Z.topIso.hom ≫ 𝟙 Z
    rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
    simp
  have hdef : P.genericPoint ∈ (MMP.Mori.RationalMap.IsBirational.inverse hh).domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Z) h _ hover
      P.coheight_genericPoint.le
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse h e he g' (hg'.trans hinv.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Z.presheaf.stalk (h E.genericPoint)) := by rw [hE]; infer_instance
  have : ValuationRing (Z.presheaf.stalk (h (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap h hbij (hy.trans hE.symm)

end InverseTransformAt

/-- An `ℝ`-Cartier divisor is a real combination `∑ r_j L_j` of Cartier divisors. -/
private theorem exists_eq_sum_of_isCartierCombination {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {N : RDivisor X} (h : IsCartierCombination N) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      N = ∑ j, r j • Divisor.toRDivisor (L j) := by
  obtain ⟨m, r, L, hL, hN⟩ := h
  exact ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hN⟩

section NumericalEquivalence

variable {k : Type u} [Field k] {X W : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The difference `∑ r₁ L₁ - ∑ r₂ L₂` is the sum over the concatenated presentation
`Fin.append r₁ (-r₂)`, `Fin.append L₁ L₂`. -/
private theorem sum_sub_sum_eq_sum_append {m₁ m₂ : ℕ} (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor X)
    (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor X) :
    ∑ j, r₁ j • Divisor.toRDivisor (L₁ j) - ∑ j, r₂ j • Divisor.toRDivisor (L₂ j) =
      ∑ t, Fin.append r₁ (-r₂) t • Divisor.toRDivisor (Fin.append L₁ L₂ t) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem isCartier_append {m₁ m₂ : ℕ} {L₁ : Fin m₁ → Divisor X} {L₂ : Fin m₂ → Divisor X}
    (hL₁ : ∀ j, (L₁ j).IsCartier) (hL₂ : ∀ j, (L₂ j).IsCartier) :
    ∀ t, (Fin.append L₁ L₂ t).IsCartier := fun t =>
  Fin.addCases (motive := fun t => (Fin.append L₁ L₂ t).IsCartier)
    (fun j => by simpa using hL₁ j) (fun j => by simpa using hL₂ j) t

/-- A value of `(∑ r₁ L₁ - ∑ r₂ L₂) · C` is the difference of the degrees of the two
presentations along `C`. -/
private theorem eq_sub_of_isRIntersectionNumber_sub {C : ProperCurve sX} {m₁ m₂ : ℕ}
    {r₁ : Fin m₁ → ℝ} {L₁ : Fin m₁ → Divisor X} (hL₁ : ∀ j, (L₁ j).IsCartier)
    {r₂ : Fin m₂ → ℝ} {L₂ : Fin m₂ → Divisor X} (hL₂ : ∀ j, (L₂ j).IsCartier)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX
      (∑ j, r₁ j • Divisor.toRDivisor (L₁ j) - ∑ j, r₂ j • Divisor.toRDivisor (L₂ j)) r L C x) :
    x = ∑ j, r₁ j * ((L₁ j).degreeOn k sX C.ι C.dim_le (hL₁ j) : ℝ) -
      ∑ j, r₂ j * ((L₂ j).degreeOn k sX C.ι C.dim_le (hL₂ j) : ℝ) := by
  obtain ⟨hL, hD, hxe⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sX hx
  rw [hxe, sum_degreeOn_eq_of_sum_eq k sX C hL (isCartier_append hL₁ hL₂)
    (hD.symm.trans (sum_sub_sum_eq_sum_append r₁ L₁ r₂ L₂)), Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

/-- For `ℝ`-Cartier divisors, `N₁ ≡_f N₂` if and only if `N₁ - N₂ ≡_f 0`. -/
private theorem isNumericallyEquivalentOver_iff_isNumericallyTrivialOver_sub (f : X ⟶ W)
    {N₁ N₂ : RDivisor X} (h₁ : IsCartierCombination N₁) (h₂ : IsCartierCombination N₂) :
    IsNumericallyEquivalentOver k sX f N₁ N₂ ↔ IsNumericallyTrivialOver k sX f (N₁ - N₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hN₁⟩ := exists_eq_sum_of_isCartierCombination h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hN₂⟩ := exists_eq_sum_of_isCartierCombination h₂
  have hsub : IsCartierCombination (N₁ - N₂) :=
    ⟨m₁ + m₂, Fin.append r₁ (-r₂), Fin.append L₁ L₂, isCartier_append hL₁ hL₂, by
      simpa only [toRDivisor_eq_mapCoeffs, hN₁, hN₂] using
        sum_sub_sum_eq_sum_append r₁ L₁ r₂ L₂⟩
  refine ⟨fun H => ?_, fun H => ?_⟩
  · refine ⟨hsub, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
      fun C hC m r L x m' r' L' x' hx hx' => ?_⟩
    rw [eq_zero_of_isRIntersectionNumber_zero k sX hx']
    rw [hN₁, hN₂] at hx
    rw [eq_sub_of_isRIntersectionNumber_sub sX hL₁ hL₂ hx, sub_eq_zero]
    refine H.2.2 C hC _ r₁ L₁ _ _ r₂ L₂ _ ?_ ?_
    · rw [hN₁]
      exact isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
    · rw [hN₂]
      exact isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
  · refine ⟨h₁, h₂, fun C hC m₁' r₁' L₁' x₁ m₂' r₂' L₂' x₂ hx₁ hx₂ => ?_⟩
    obtain ⟨hL₁', hD₁, hx₁e⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sX hx₁
    obtain ⟨hL₂', hD₂, hx₂e⟩ := eq_sum_degreeOn_of_isRIntersectionNumber k sX hx₂
    have hv := isRIntersectionNumber_sum_degreeOn k sX C (Fin.append r₁' (-r₂'))
      (Fin.append L₁' L₂') (isCartier_append hL₁' hL₂')
    rw [← sum_sub_sum_eq_sum_append, ← hD₁, ← hD₂] at hv
    have h0 := H.2.2 C hC _ _ _ _ 0 Fin.elim0 Fin.elim0 0 hv
      ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
    rw [hD₁, hD₂] at hv
    have h3 := eq_sub_of_isRIntersectionNumber_sub sX hL₁' hL₂' hv
    rw [← hx₁e, ← hx₂e] at h3
    linarith

end NumericalEquivalence

section CommonResolution

/-- A point `x` over the generic point of a prime divisor, at which `f` induces an isomorphism of
local rings, has coheight one. -/
private theorem coheight_eq_one_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    [IsIso (f.stalkMap x)] {P : MMP.Mori.PrimeDivisor Y} (hx : f x = P.genericPoint) :
    Order.coheight x = 1 := by
  have h1 : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
    (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
    P.coheight_genericPoint] at h1
  exact_mod_cast h1

/-- The coefficient of `∑ r_i f^*L_i` along a prime divisor `E` over the prime divisor `P`, at
which `f` induces an isomorphism of local rings, is the coefficient of `∑ r_i L_i` along `P`. -/
private theorem coeff_sum_pullback_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace X] {f : X ⟶ Y} {m : ℕ} (r : Fin m → ℝ)
    {L : Fin m → Divisor Y} (hL : ∀ i, (L i).IsCartier)
    (hB : ∀ i, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (L i).supp)
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = P.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    (∑ i, r i • Divisor.toRDivisor ((L i).pullback (hL i) (hB i))) E =
      (∑ i, r i • Divisor.toRDivisor (L i)) P := by
  change DivisorWithCoeffs.coeff (∑ i, r i • Divisor.toRDivisor ((L i).pullback (hL i) (hB i))) E =
    DivisorWithCoeffs.coeff (∑ i, r i • Divisor.toRDivisor (L i)) P
  rw [coeff_sum_smul_toRDivisor, coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MMP.Positivity.coeff_eq_of_isPullback E P heq (hL i)
    (Divisor.isPullback_pullback (hL i) (hB i))]

/-- Every prime divisor of `Y` is the transform of a prime divisor of `V`, for a proper birational
morphism `p : V ⟶ Y` of normal varieties. -/
private theorem exists_transformPrimeDivisor_eq_some {k : Type u} [Field k] {V Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)]
    (hY : IsNormalVariety k sY) {p : V ⟶ Y} (hV : IsNormalVariety k (p ≫ sY)) [IsProper p]
    (hp : IsBirationalMorphism p) (P : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor V,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := V) p.toRationalMap E = some P := by
  obtain ⟨E, hE, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hV hp P
  exact ⟨E, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p E P).mpr hE⟩

/-- **A prime divisor over `E` on a common resolution.** Let `p : V ⟶ Y`, `q : V ⟶ Z'` be proper
birational morphisms of normal varieties and `π : Z' ⟶ Z` a birational morphism with
`p ≫ h = q ≫ π`. If `h` maps the generic point of a prime divisor `E` of `Y` to that of a prime
divisor `P₀` of `Z`, the strict transform `E'` of `E` on `V` lies over a prime divisor `Q'` of
`Z'` over `P₀`, and the transforms along `p` and `q` read their coefficients off `E'`. -/
private theorem exists_primeDivisor_of_comp_eq {k : Type u} [Field k] {V Y Z Z' : Scheme.{u}}
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Z'] [IsLocallyNoetherian Z'] [IsNormal Z']
    {sY : Y ⟶ Spec (.of k)} {sZ' : Z' ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    {p : V ⟶ Y} (hV : IsNormalVariety k (p ≫ sY)) (hZ' : IsNormalVariety k sZ') {q : V ⟶ Z'}
    (hVq : IsNormalVariety k (q ≫ sZ')) [IsProper p] [IsProper q] (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) {h : Y ⟶ Z} {π : Z' ⟶ Z} (hπ : IsBirationalMorphism π)
    (hpq : p ≫ h = q ≫ π) {E : MMP.Mori.PrimeDivisor Y} {P₀ : MMP.Mori.PrimeDivisor Z}
    (hE : h E.genericPoint = P₀.genericPoint) :
    ∃ (E' : MMP.Mori.PrimeDivisor V) (Q' : MMP.Mori.PrimeDivisor Z'),
      p E'.genericPoint = E.genericPoint ∧ q E'.genericPoint = Q'.genericPoint ∧
      π Q'.genericPoint = P₀.genericPoint ∧ IsIso (p.stalkMap E'.genericPoint) ∧
      IsIso (q.stalkMap E'.genericPoint) ∧
      (∀ D : RDivisor V,
        MMP.Mori.RationalMap.transformDivisor (X := V) p.toRationalMap D E = D E') ∧
      ∀ D : RDivisor V,
        MMP.Mori.RationalMap.transformDivisor (X := V) q.toRationalMap D Q' = D E' := by
  haveI := hπ.isDominant
  haveI := hq.isDominant
  have := P₀.isDiscreteValuationRing_localRing
  obtain ⟨E', hE'p, hE'iso, hE'tr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hV hp E
  have hπw : π (q E'.genericPoint) = P₀.genericPoint := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hE'p, hE]
  have : ValuationRing (Z.presheaf.stalk (π (q E'.genericPoint))) := by
    rw [hπw]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing π hπ.functionFieldMap_bijective
    (q E'.genericPoint)
  have hw1 := coheight_eq_one_of_isIso_stalkMap π hπw
  set Q' : MMP.Mori.PrimeDivisor Z' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hw1
  have hQ' : q E'.genericPoint = Q'.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hw1).symm
  have := Q'.isDiscreteValuationRing_localRing
  have : ValuationRing (Z'.presheaf.stalk (q E'.genericPoint)) := by
    rw [hQ']; infer_instance
  have hbijq := hq.functionFieldMap_bijective
  have hqiso := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbijq E'.genericPoint
  obtain ⟨E'', hE''q, hE''iso, hE''tr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hZ' hVq hq Q'
  have hE'' : E'' = E' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap q hbijq (x₁ := E'.genericPoint)
      (x₂ := E''.genericPoint) (hE''q.trans hQ'.symm)).symm
  refine ⟨E', Q', hE'p, hQ', by rw [← hQ']; exact hπw, hE'iso, hqiso, hE'tr,
    fun D => ?_⟩
  rw [hE''tr, hE'']

end CommonResolution

end ProcedureDivisorSpan

namespace MMP.Flips

open ProcedureDivisorSpan

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Components of `h⁻¹_* H'`.** Let `h` map the generic point of a prime divisor `E` of `Y` to
that of a prime divisor `P₀` of `Z`, and let `Q` be a prime divisor of `Z'` over `P₀` along which
some `∑ c_j F_j` does not vanish. Then `E` is a component of `h⁻¹_* H'`, by (18.12.1.3). -/
private theorem ProcedureDatum.birationalInverseTransform_ne_zero_of_coeff_ne_zero
    {k : Type u} [Field k] {X Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Z]
    [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z} (P : ProcedureDatum k sZ D f) [IsIntegral Y]
    [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] (h : Y ⟶ Z)
    [IsProper h] (hh : IsBirationalMorphism h) {E : MMP.Mori.PrimeDivisor Y}
    {P₀ : MMP.Mori.PrimeDivisor Z} (hE : h E.genericPoint = P₀.genericPoint)
    {Q : MMP.Mori.PrimeDivisor P.resolution} (hQ : P.π Q.genericPoint = P₀.genericPoint)
    {c : Fin P.r → ℝ} (hc : (∑ j, c j • Divisor.toRDivisor (P.F j)) Q ≠ 0) :
    birationalInverseTransform h hh P.H' E ≠ 0 := by
  rw [show (∑ j, c j • Divisor.toRDivisor (P.F j)) Q = ∑ j, c j * ((P.F j).coeff Q : ℝ) from
    coeff_sum_smul_toRDivisor c P.F Q] at hc
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hQmem : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hmem : P₀.genericPoint ∈ P.H'.supp := by
    rw [← hQ]
    exact P.image_component_subset j Q (fun h0 => hj (by simp [h0])) ⟨Q.genericPoint, hQmem, rfl⟩
  obtain ⟨P₁, hP₁, hmem₁⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  rw [birationalInverseTransform, MMP.Mori.RationalMap.transformDivisor,
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq h hh hE) (fun P₂ hP₂ => ?_)]
  · rwa [← eq_of_genericPoint_mem_support hmem₁]
  · exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hh hP₂).symm.trans hE)

/-- `ProcedureDatum.exists_isNumericallyEquivalentOver_of_isQFactorial` on a common resolution:
given proper birational `p : V ⟶ Y`, `q : V ⟶ Z'` from a normal variety with `p ≫ h = q ≫ π`,
the divisor is `L - p_* q^* D'`, where `D' = q_* p^* L - ∑ c_j F_j ≡_π 0`. -/
private theorem ProcedureDatum.exists_isNumericallyEquivalentOver_of_comp_eq
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Fourfold.IsQFactorial sY)
    {h : Y ⟶ Z} (hsY : h ≫ sZ = sY) [IsProper h] (hh : IsBirationalMorphism h)
    [IsIntegral Y] [LocallyOfFiniteType sY] [IsSeparated sY] [CompactSpace Y] [IsDominant h]
    [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    [IsLocallyNoetherian P.resolution] [IsNormal P.resolution] [IsIntegral P.resolution]
    [LocallyOfFiniteType (P.π ≫ sZ)] [QuasiCompact (P.π ≫ sZ)] [IsSeparated (P.π ≫ sZ)]
    [CompactSpace P.resolution] [IsProper P.π] [IsDominant P.π]
    (hZ'q : MMP.Fourfold.IsQFactorial (P.π ≫ sZ)) {V : Scheme.{u}} [IsIntegral V] [IsNormal V]
    [IsLocallyNoetherian V] [CompactSpace V] {p : V ⟶ Y} {q : V ⟶ P.resolution} [IsProper p]
    [IsProper q] [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sY)]
    [QuasiCompact (p ≫ sY)] [IsSeparated (p ≫ sY)] (hV : IsNormalVariety k (p ≫ sY))
    (hpq : p ≫ h = q ≫ P.π) (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hpB : IsBirational p) {L : RDivisor Y} (hL : IsCartierCombination L) :
    ∃ G : RDivisor Y,
      (∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
        birationalInverseTransform h hh P.H' E ≠ 0 ∨ IsExceptionalPrimeDivisor sZ h E) ∧
      IsNumericallyEquivalentOver k sY h L G := by
  classical
  have hYn : IsNormalVariety k sY := hY.1
  have hqs : q ≫ (P.π ≫ sZ) = p ≫ sY := by rw [← Category.assoc, ← hpq, Category.assoc, hsY]
  have hVq : IsNormalVariety k (q ≫ P.π ≫ sZ) := hqs ▸ hV
  have hphb : IsBirationalMorphism (p ≫ h) :=
    isBirationalMorphism_comp_of_isBirational h p (isBirational_of_isIso_stalkMap_genericPoint h
      (map_genericPoint_of_isDominant h) (isIso_stalkMap_genericPoint h hh)) hpB
  obtain ⟨m, r, Ls, hLs, hLeq⟩ := exists_eq_sum_of_isCartierCombination hL
  have hBp : ∀ i, ∀ W : irreducibleComponents V, p (componentGenericPoint V W) ∉ (Ls i).supp :=
    fun i => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (Ls i)
  set Lp : RDivisor V := ∑ i, r i • Divisor.toRDivisor ((Ls i).pullback (hLs i) (hBp i))
    with hLp
  set A : RDivisor P.resolution :=
    MMP.Mori.RationalMap.transformDivisor (X := V) q.toRationalMap Lp with hA
  obtain ⟨c, hc⟩ := P.span_F A (isCartierCombination_of_isQFactorial hZ'q A)
  set D' : RDivisor P.resolution := A - ∑ j, c j • Divisor.toRDivisor (P.F j) with hD'
  have hD'triv : IsNumericallyTrivialOver k (P.π ≫ sZ) P.π D' :=
    (isNumericallyEquivalentOver_iff_isNumericallyTrivialOver_sub (P.π ≫ sZ) P.π
      (isCartierCombination_of_isQFactorial hZ'q A)
      (isCartierCombination_of_isQFactorial hZ'q _)).mp hc
  obtain ⟨n, s, M, hM, hD'eq⟩ :=
    exists_eq_sum_of_isCartierCombination (isCartierCombination_of_isQFactorial hZ'q D')
  have hBq : ∀ i, ∀ W : irreducibleComponents V, q (componentGenericPoint V W) ∉ (M i).supp :=
    fun i => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (M i)
  set MV : RDivisor V := ∑ i, s i • Divisor.toRDivisor ((M i).pullback (hM i) (hBq i))
    with hMV
  have hMVt : IsNumericallyTrivialOver k (p ≫ sY) (p ≫ h) MV :=
    isNumericallyTrivialOver_sum_pullback q hqs hpq s hM hBq (hD'eq ▸ hD'triv)
  obtain ⟨-, hpM⟩ := IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hV hY
    (h := p ≫ h) (by rw [Category.assoc, hsY]) hsY hphb hh
    (Scheme.RationalMap.compHom_toRationalMap p.toPartialMap h).symm
    (exists_transformPrimeDivisor_eq_some hYn hV hpb) hMVt.1 hMVt
  set T : RDivisor Y := MMP.Mori.RationalMap.transformDivisor (X := V) p.toRationalMap MV with hT
  refine ⟨L - T, fun E hE => ?_,
    (isNumericallyEquivalentOver_iff_isNumericallyTrivialOver_sub sY h hL
      (isCartierCombination_of_isQFactorial hY (L - T))).mpr (by rwa [sub_sub_cancel])⟩
  by_cases hex : IsExceptionalPrimeDivisor sZ h E
  · exact Or.inr hex
  have hYZ : IsNormalVariety k (h ≫ sZ) := hsY ▸ hYn
  have hz1 := coheight_eq_one_of_not_isExceptionalPrimeDivisor h hYZ hh E hex
  have hP0 := (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz1).symm
  obtain ⟨E', Q', hE'p, hQ', hπQ, hpi, hqi, hpE, hqQ⟩ := exists_primeDivisor_of_comp_eq hYn hV
    hZ'q.1 hVq hpb hqb P.isBirationalMorphism hpq hP0
  refine Or.inl (P.birationalInverseTransform_ne_zero_of_coeff_ne_zero h hh hP0 hπQ (c := c) ?_)
  rwa [Finsupp.sub_apply, hT, hpE, hMV, coeff_sum_pullback_eq s hM hBq E' Q' hQ', ← hD'eq, hD',
    Finsupp.sub_apply, hA, hqQ, hLp, coeff_sum_pullback_eq r hLs hBp E' E hE'p, ← hLeq,
    sub_sub_cancel] at hE

/-- `ProcedureDatum.exists_isNumericallyEquivalentOver_of_isQFactorial` for integral separated
`Y` and `Z`: pass to the normalized graph of `Y ⤏ Z'`. -/
private theorem ProcedureDatum.exists_isNumericallyEquivalentOver_of_isIntegral
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Fourfold.IsQFactorial sY)
    {h : Y ⟶ Z} (hsY : h ≫ sZ = sY) [IsProper h] (hh : IsBirationalMorphism h)
    [IsIntegral Y] [LocallyOfFiniteType sY] [IsSeparated sY] [CompactSpace Y] [IsDominant h]
    [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {L : RDivisor Y} (hL : IsCartierCombination L) :
    ∃ G : RDivisor Y,
      (∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
        birationalInverseTransform h hh P.H' E ≠ 0 ∨ IsExceptionalPrimeDivisor sZ h E) ∧
      IsNumericallyEquivalentOver k sY h L G := by
  haveI := P.isLocallyNoetherian_resolution
  haveI := P.isNormal_resolution
  haveI := P.quasiCompact_resolution
  have hZ'n : IsNormalVariety k (P.π ≫ sZ) := ⟨P.isVariety_resolution, P.isNormal_resolution⟩
  haveI : IsIntegral P.resolution := hZ'n.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.π ≫ sZ) := hZ'n.1.toLocallyOfFiniteType
  haveI : IsSeparated (P.π ≫ sZ) := hZ'n.1.toIsSeparated
  haveI : CompactSpace P.resolution := QuasiCompact.compactSpace_of_compactSpace (P.π ≫ sZ)
  haveI : IsProper P.π := isProper_of_isProjectiveMorphism _ P.isProjectiveMorphism
  haveI : IsDominant P.π := P.isBirationalMorphism.isDominant
  have hZ'q : MMP.Fourfold.IsQFactorial (P.π ≫ sZ) :=
    ⟨hZ'n, fun D => ⟨1, one_pos, by
      simpa using
        MMP.Threefold.Resolution.isCartier_of_isSmoothScheme P.isSmoothScheme_resolution D⟩⟩
  have hηZ : h (genericPoint Y) = P.π (genericPoint P.resolution) := by
    rw [map_genericPoint_of_isDominant h, map_genericPoint_of_isDominant P.π]
  obtain ⟨g₀, hg₀⟩ := exists_comp_eq_fromSpecStalk h P.π P.isBirationalMorphism hηZ
  obtain ⟨V, p, q, hV, hpq, hpP, hqP, hpB, hqB⟩ :=
    exists_normalizedGraph hY.1 hh P.isBirationalMorphism g₀ hg₀
  haveI : IsIntegral V := hV.1.toIsIntegral
  have hpb : IsBirationalMorphism p := isBirationalMorphism_of_isBirational p hpB
  have hqb : IsBirationalMorphism q := isBirationalMorphism_of_isBirational q hqB
  haveI : LocallyOfFiniteType (p ≫ sY) := hV.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sY) := hV.1.toQuasiCompact
  haveI : IsSeparated (p ≫ sY) := hV.1.toIsSeparated
  haveI : IsNormal V := hV.2
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sY)
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  exact P.exists_isNumericallyEquivalentOver_of_comp_eq hY hsY hh hZ'q hV hpq hpb hqb hpB hL

/-- **The divisor of a procedure datum generates `N¹(Y/Z)`** (FA 18.12.1.4). Let `P` be a
procedure datum for `(X, D, f)`, with divisor `H'` on `Z`, over a field `k`, and
let `h : Y ⟶ Z` be a proper birational morphism from a normal `ℚ`-factorial variety
`Y`. Then every `ℝ`-Cartier divisor `L` on `Y` is numerically `h`-equivalent to an `ℝ`-divisor
`G` each of whose components is an irreducible component of the strict transform `h⁻¹_*H'` or
an `h`-exceptional prime divisor. -/
@[mmp "lem_fa18_procedure_divisor_generates_relative_neron_severi"]
public theorem ProcedureDatum.exists_isNumericallyEquivalentOver_of_isQFactorial
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Fourfold.IsQFactorial sY)
    {h : Y ⟶ Z} (hsY : h ≫ sZ = sY) [IsProper h] (hh : IsBirationalMorphism h)
    {L : RDivisor Y} (hL : IsCartierCombination L) :
    ∃ G : RDivisor Y,
      (∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
        birationalInverseTransform h hh P.H' E ≠ 0 ∨ IsExceptionalPrimeDivisor sZ h E) ∧
      IsNumericallyEquivalentOver k sY h L G := by
  have hYn : IsNormalVariety k sY := hY.1
  haveI : IsIntegral Y := hYn.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsDominant h := hh.isDominant
  haveI : Surjective h := inferInstance
  haveI : IsSeparated (h ≫ sZ) := by rw [hsY]; infer_instance
  haveI : IsSeparated sZ := isSeparated_of_surjective h sZ
  haveI : IrreducibleSpace Z :=
    Function.Surjective.irreducibleSpace h.continuous ‹Surjective h›.surj
  haveI : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  haveI := isSeparated_toTerminal_of_isSeparated sZ
  haveI := isSeparated_toTerminal_of_isSeparated sY
  exact P.exists_isNumericallyEquivalentOver_of_isIntegral hY hsY hh hL

end MMP.Flips
