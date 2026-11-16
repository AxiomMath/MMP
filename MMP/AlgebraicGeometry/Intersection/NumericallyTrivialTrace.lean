module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible

/-!
# Comparison divisors on a common model and numerically trivial full traces

Let `p : W ⟶ Y` and `q : W ⟶ Z` be projective birational morphisms of normal projective varieties
over a field `k`, over a common base. Two consequences of the negativity lemma
(`MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback`) for divisors pulled back to `W`:

* if `L` is `ℝ`-Cartier on `Y`, `M` is `ℝ`-Cartier on `Z` and nef over the base, and the
  push-forward `p_*(p^*L - q^*M)` is effective, then `p^*L - q^*M` is effective: `q^*M` is
  `p`-nef, by the projection formula on the curves contracted by `p`;
* if `Y` is `ℚ`-factorial and `N` is an `ℝ`-Cartier divisor on `X` numerically trivial over the
  base `Z`, then the full trace `N_Y = q_*(p^*N)` is numerically trivial over `Z` and
  `q^*N_Y = p^*N`: the difference `q^*N_Y - p^*N` and its negative are `q`-nef and have no
  coefficient along a prime divisor not exceptional over `Y`.

## Main results

* `MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub`: effectivity of `p^*L - q^*M` from that
  of its push-forward.
* `MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback`: numerically
  trivial full traces.

## Implementation notes

The pull-backs are `ℝ`-divisors on `W` given with `MMP.Flips.IsRCartierPullback`, as in
`MMP.Fourfold.IsNefWeakModel`; the push-forward along a birational morphism is the birational
transform `MMP.Mori.RationalMap.transformDivisor` along it viewed as a rational map. Nefness and
numerical triviality over a base are `MMP.Flips.IsRelativelyNef` and
`MMP.Flips.IsNumericallyTrivialOver` for the structure morphism to the base. The auxiliary lemmas
of each proof live in the namespace `Proof_<tag>` of its card.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

universe u

namespace Proof_lem_fourfold_generic_comparison_effective

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := Set.range_eq_univ.mpr ν.surjective
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

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [IsDominant f] [LocallyOfFiniteType f] (hf : IsBirationalMorphism f) : degreeOver f = 1 := by
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
  have hc2 := isCurve_ι (k := k) C
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

/-- The degree of `𝒪_X(L)` along a proper curve `C` is an intersection number `L · C`. -/
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

section Divisors

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback [IsIntegral Y] [CompactSpace X]
    [CompactSpace Y] {f : Y ⟶ X} {D : RDivisor X} {G : RDivisor Y}
    (h : IsRCartierPullback f D G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, hG⟩ := h
  refine ⟨m, r, L', fun j => ?_, by simpa only [toRDivisor_eq_mapCoeffs] using hG⟩
  obtain ⟨hBj, hj⟩ := hpb j
  rw [← Divisor.IsPullback.pullback_eq (hL j) hj]
  exact (hL j).isCartier_pullback f hBj

/-- A difference of `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {D₁ D₂ : RDivisor Y} (h₁ : IsCartierCombination D₁)
    (h₂ : IsCartierCombination D₂) : IsCartierCombination (D₁ - D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ (-r₂), Fin.append L₁ L₂, fun j => ?_, ?_⟩
  · exact Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier)
      (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
  · simp [Fin.sum_univ_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]

end Divisors

section StrictTransform

/-- A prime divisor `E` of `W` that is not exceptional over `Y` lies over a prime divisor `P` of
`Y`, `q` is a local isomorphism at its generic point, and the coefficient of `P` in a push-forward
`q_* D` is the coefficient of `E` in `D`. -/
private theorem exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
    {k : Type u} [Field k] {W Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    (q : W ⟶ Y) (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hqb : IsBirationalMorphism q)
    (E : MMP.Mori.PrimeDivisor W) (hE : ¬ IsExceptionalPrimeDivisor sY q E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, q E.genericPoint = P.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) ∧
      ∀ D : RDivisor W, MMP.Mori.RationalMap.transformDivisor q.toRationalMap D P = D E := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated q := IsSeparated.of_comp q sY
  haveI : IsDominant q := hqb.isDominant
  set DE : ProperDivisorOver k sY := ProperDivisorOver.mk ⟨W, q, hW, hqb, E⟩ inferInstance
  have hnot : ¬ DE.IsExceptional := fun h => hE ⟨hW, hqb, inferInstance, h⟩
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    intro h2
    refine hnot ?_
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (DE.toDivisorOver.f DE.toDivisorOver.E.genericPoint)
    rw [← hd]
    gcongr
    rw [← WithBot.coe_ofNat]
    exact WithBot.coe_le_coe.mpr h2
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  have hEP : q E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv
  obtain ⟨E', hE'P, hiso', htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hqb P
  have hbij := hqb.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hEP]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (q E'.genericPoint)) := by rw [hE'P]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij E.genericPoint
  have hEE' : E'.genericPoint = E.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hEP.trans hE'P.symm)
  have hEE : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEE'
  subst hEE
  exact ⟨P, hEP, hiso, htr⟩

end StrictTransform

section Nef

/-- **The projection formula for the pull-back of a Cartier divisor.** If `L'` is the pull-back of
the Cartier divisor `L` along `f` and `f(C') = C` is a proper curve, then
`(L' · C') = [k(C') : k(C)] (L · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {L : Divisor Y} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : Divisor X} (h : L.IsPullback f hB L') (hc : L'.IsCartier) (C' : ProperCurve sX)
    (C : ProperCurve sY) (hC : f C'.point = C.point) :
    (L'.degreeOn k sX C'.ι C'.dim_le hc : ℝ) =
      (residueFieldDegree f C'.point : ℝ) * (L.degreeOn k sY C.ι C.dim_le hL : ℝ) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain rfl := Divisor.IsPullback.pullback_eq hL h
  obtain ⟨c, hcC⟩ := C
  dsimp only at hC
  subst hC
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hL hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos hcC]
  simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul]
  push_cast
  rfl

/-- If `L'` is the pull-back of the Cartier divisor `L` along `f` and `f(C')` is not a proper
curve, then `(L' · C') = 0`. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {L : Divisor Y} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : Divisor X} (h : L.IsPullback f hB L') (hc : L'.IsCartier) (C' : ProperCurve sX)
    (hC : ¬ IsProperCurve sY (f C'.point)) : L'.degreeOn k sX C'.ι C'.dim_le hc = 0 := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain rfl := Divisor.IsPullback.pullback_eq hL h
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hL hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hC, map_zero]

/-- **Pull-backs of divisors nef over a base are nef along morphisms over it.** Let
`p : W ⟶ Y` and `q : W ⟶ Z` be morphisms with `p ≫ πY = q ≫ πZ` for `πY : Y ⟶ S`,
`πZ : Z ⟶ S`, and `q` proper. If `M` is an `ℝ`-Cartier divisor on `Z` nef over `S`, its pull-back
`q^*M` is `p`-nef. -/
private theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z S : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
    [LocallyOfFiniteType sZ] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y)
    (q : W ⟶ Z) [IsProper q] [QuasiCompact (q ≫ sZ)] (hpq : p ≫ πY = q ≫ πZ)
    {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsRelativelyNef k (q ≫ sZ) p M' := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  obtain ⟨m, r, L₀, L₁, hL₀, hMeq, hpb, hM'eq⟩ := hM'
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  refine ⟨m, r, _, hL₁c, hM'eq, fun C hC x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) C r _ hL₁c
  rw [← hM'eq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) C).1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sZ (q C.point)
  · obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ProperCurve sZ, C₀.point = q C.point := ⟨⟨_, hc⟩, rfl⟩
    have hC₀c : C₀.IsContractedBy πZ := by
      intro z hz
      rw [hC₀] at hz ⊢
      have hsub : closure ({q C.point} : Set Z) ⊆ q '' closure ({C.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨w, hw, rfl⟩ := hsub hz
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, hC w hw]
    have hdeg : ∀ j, ((((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) : ℤ) : ℝ) =
        (residueFieldDegree q C.point : ℝ) * (L₀ j).degreeOn k sZ C₀.ι C₀.dim_le (hL₀ j) :=
      fun j => degreeOn_eq_mul_of_isPullback q rfl (hL₀ j) (hpbj j) (hL₁c j) C C₀ hC₀.symm
    obtain ⟨mM, rM, LM, hLM, hMeq', hMall⟩ := hM
    have hMx := isRIntersectionNumber_sum_degreeOn k sZ C₀ rM LM hLM
    rw [← hMeq'] at hMx
    have h0 := isRIntersectionNumber_sum_degreeOn k sZ C₀ r L₀ hL₀
    rw [← hMeq] at h0
    have hnn := hMall C₀ hC₀c _ hMx
    rw [(IsRIntersectionNumber.eq_and_linear k sZ C₀).1 _ _ _ _ _ _ _ hMx h0] at hnn
    simp only [hdeg, mul_left_comm (r _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) hnn
  · have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) = 0 := fun j =>
      degreeOn_eq_zero_of_isPullback q rfl (hL₀ j) (hpbj j) (hL₁c j) C hc
    simp [hdeg]

end Nef

end Proof_lem_fourfold_generic_comparison_effective

namespace MMP.Fourfold

open MMP.Mori
open Proof_lem_fourfold_generic_comparison_effective

/-- **A comparison divisor is effective if its push-forward is.** Let `p : W ⟶ Y` and
`q : W ⟶ Z` be projective birational morphisms of normal projective varieties over `k`, all over a
base `S` via `πY`, `πZ`. Let `L` be an `ℝ`-Cartier divisor on `Y` with pull-back `L' = p^*L`, and
`M` an `ℝ`-Cartier divisor on `Z`, nef over `S`, with pull-back `M' = q^*M`. If
`p_*(L' - M') ≥ 0`, then `L' - M' ≥ 0`. -/
@[mmp "lem_fourfold_generic_comparison_effective"]
public theorem nonneg_sub_of_nonneg_transformDivisor_sub
    {k : Type u} [Field k] {W Y Z S : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (sW : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ]
    (hW : IsNormalVariety k sW) (hWp : MMP.Mori.IsProjectiveVariety k sW)
    (hY : IsNormalVariety k sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (hZ : IsNormalVariety k sZ) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y) (q : W ⟶ Z)
    (hpY : p ≫ sY = sW) (hqZ : q ≫ sZ = sW) (hpq : p ≫ πY = q ≫ πZ)
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    (hq : IsProjectiveMorphism q) (hqb : IsBirationalMorphism q)
    {L : RDivisor Y} (hL : MMP.Flips.IsCartierCombination L)
    {M : RDivisor Z} (hM : MMP.Flips.IsRelativelyNef k sZ πZ M)
    {L' M' : RDivisor W} (hL' : MMP.Flips.IsRCartierPullback p L L')
    (hM' : MMP.Flips.IsRCartierPullback q M M')
    (hpush : 0 ≤ MMP.Mori.RationalMap.transformDivisor p.toRationalMap (L' - M')) :
    0 ≤ L' - M' := by
  classical
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hp
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hq
  haveI : QuasiCompact sW := by rw [← hqZ]; infer_instance
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hL'c := isCartierCombination_of_isRCartierPullback hL'
  have hM'c := isCartierCombination_of_isRCartierPullback hM'
  rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
  refine MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback k sY sW hY hW p hpY hpb hL
    hL' hM'c ?_ (isCartierCombination_sub hL'c hM'c) ?_ ?_
  · subst hqZ
    haveI : IsSeparated sZ := hZ.1.toIsSeparated
    haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
    exact isRelativelyNef_of_isRCartierPullback πY πZ p q hpq hM hM'
  · intro P hP
    have hW' : IsNormalVariety k (p ≫ sY) := by rw [hpY]; exact hW
    obtain ⟨Q, -, -, hQ⟩ :=
      exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hY p hW' hpb P hP
    simpa only [DivisorWithCoeffs.coeff_apply, hQ] using
      DivisorWithCoeffs.isEffective_iff_nonneg.mpr hpush Q
  · rw [add_sub_cancel]
    exact ⟨hL'c, hL'c, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ h₁ h₂ =>
      (IsRIntersectionNumber.eq_and_linear k sW C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩

end MMP.Fourfold

namespace Proof_lem_fourfold_numerically_trivial_full_trace

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- Every value of `D · C` is `∑ r_j (L_j · C)`, for any presentation `D = ∑ r_j L_j`. -/
private theorem eq_sum_degreeOn_of_isRIntersectionNumber (C : ProperCurve sX) {D : RDivisor X}
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber k sX D r' L' C x) :
    x = ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) := by
  subst hD
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r' L' r L _ _ hx
    (Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
      k sX C r L hL)

/-- The empty presentation of `0` computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- A combination `a D₁ + b D₂` of `ℝ`-Cartier divisors is `f`-nef as soon as
`a (D₁ · C) + b (D₂ · C) ≥ 0` for every curve `C` contracted by `f`. -/
private theorem isRelativelyNef_smul_add_smul {Y : Scheme.{u}} (f : X ⟶ Y) {D₁ D₂ : RDivisor X}
    {m₁ m₂ : ℕ} (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor X) (hL₁ : ∀ j, (L₁ j).IsCartier)
    (hD₁ : D₁ = ∑ j, r₁ j • Divisor.toRDivisor (L₁ j))
    (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor X) (hL₂ : ∀ j, (L₂ j).IsCartier)
    (hD₂ : D₂ = ∑ j, r₂ j • Divisor.toRDivisor (L₂ j)) (a b : ℝ)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ a * ∑ j, r₁ j * ((L₁ j).degreeOn k sX C.ι C.dim_le (hL₁ j) : ℝ) +
        b * ∑ j, r₂ j * ((L₂ j).degreeOn k sX C.ι C.dim_le (hL₂ j) : ℝ)) :
    IsRelativelyNef k sX f (a • D₁ + b • D₂) := by
  have hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier := fun j =>
    Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier)
      (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
  have hD : a • D₁ + b • D₂ =
      ∑ j, Fin.append (a • r₁) (b • r₂) j • Divisor.toRDivisor (Fin.append L₁ L₂ j) := by
    subst hD₁ hD₂
    simp [Fin.sum_univ_add, Finset.smul_sum, smul_smul]
  refine ⟨m₁ + m₂, Fin.append (a • r₁) (b • r₂), Fin.append L₁ L₂, hL, hD, fun C hC x hx => ?_⟩
  have h₁ : IsRIntersectionNumber k sX D₁ r₁ L₁ C _ :=
    hD₁ ▸ Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
      k sX C r₁ L₁ hL₁
  have h₂ : IsRIntersectionNumber k sX D₂ r₂ L₂ C _ :=
    hD₂ ▸ Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
      k sX C r₂ L₂ hL₂
  have h' := (IsRIntersectionNumber.eq_and_linear k sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ _ _ a b h₁ h₂
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ x _ hx h']
  exact h C hC

end Intersection

section Geometry

/-- A combination of Cartier divisors, written with `Divisor.toRDivisor`, is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_eq_sum {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] {D : RDivisor Y} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsCartierCombination D :=
  ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Fourfold.IsQFactorial sY) (D : RDivisor Y) : IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine isCartierCombination_of_eq_sum (fun j => D (e.symm j) / m (e.symm j))
    (fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1)
    (fun j => hc _) ?_
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- **Two-sided negativity.** Let `q : W ⟶ Y` be a proper birational morphism of normal varieties.
An `ℝ`-divisor `F` on `W` with `F` and `-F` both `q`-nef and with vanishing coefficients along
the prime divisors not exceptional over `Y` is zero. -/
private theorem eq_zero_of_isRelativelyNef_of_isRelativelyNef_neg {k : Type u} [Field k]
    {W Y : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y]
    {sW : W ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sW]
    (hY : IsNormalVariety k sY) (hW : IsNormalVariety k sW) (q : W ⟶ Y) (hqY : q ≫ sY = sW)
    [IsProper q] (hqb : IsBirationalMorphism q) {F : RDivisor W}
    (h₁ : IsRelativelyNef k sW q F) (h₂ : IsRelativelyNef k sW q (-F))
    (hexc : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sY q P → F.coeff P = 0) :
    F = 0 := by
  have h0Y : IsCartierCombination (0 : RDivisor Y) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have h0W : IsCartierCombination (0 : RDivisor W) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpull : IsRCartierPullback q (0 : RDivisor Y) (0 : RDivisor W) :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hnum : ∀ D : RDivisor W, IsNumericallyEquivalentOver k sW q 0 (-D + D) := fun D => by
    rw [neg_add_cancel]
    exact ⟨h0W, h0W, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ e₁ e₂ =>
      (IsRIntersectionNumber.eq_and_linear k sW C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ e₁ e₂⟩
  have heff : ∀ D : RDivisor W, IsRelativelyNef k sW q D → IsRelativelyNef k sW q (-D) →
      (∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sY q P → D.coeff P = 0) →
      D.IsEffective := fun D ⟨_, r, L, hL, hD, _⟩ hnD hexcD =>
    let ⟨_, r', L', hL', hnD', _⟩ := hnD
    isEffective_of_isNumericallyEquivalentOver_pullback k sY sW hY hW q hqY hqb h0Y hpull
      (isCartierCombination_of_eq_sum r' L' hL' hnD') hnD (isCartierCombination_of_eq_sum r L hL hD)
      (fun P hP => (hexcD P hP).ge) (hnum D)
  refine DivisorWithCoeffs.ext' fun P => ?_
  have e₁ := heff F h₁ h₂ hexc P
  have e₂ := heff (-F) h₂ (by rwa [neg_neg]) (fun P hP => by
    rw [DivisorWithCoeffs.coeff_neg, hexc P hP, neg_zero]) P
  rw [DivisorWithCoeffs.coeff_neg] at e₂
  change _ = (0 : ℝ)
  linarith

end Geometry

section CurveLifting

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [TopologicalSpace.NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp
    ((Topology.IsInducing.subtypeVal.specializes_iff.mp hab :
      (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩).mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

variable {k : Type u} [Field k]

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over `k`: it factors through its scheme-theoretic image, which is `C'`. -/
private lemma isProper_comp_of_closure_range {X B : Scheme.{u}}
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
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting proper curves.** Let `h : A ⟶ B` be a proper surjective morphism of schemes of
finite type over `k`. Every proper curve `C'` on `B` is `h(C)` for a proper curve `C` on `A`
whose function field is a finite extension of that of `C'`. -/
private theorem exists_properCurve_map_eq {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k))
    (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] [QuasiCompact sB] (h : A ⟶ B) [IsProper h] [Surjective h]
    (hh : h ≫ sB = sA) (C' : ProperCurve sB) :
    ∃ C : ProperCurve sA, h C.point = C'.point ∧ residueFieldDegree h C.point ≠ 0 := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base (h.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
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
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  refine ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range C' φ hclr⟩, haξ, ?_⟩
  -- `a` is a closed point of its fibre, so `κ(a)` is finite over `κ(h(a))`
  have : LocallyOfFiniteType h := by
    have : LocallyOfFiniteType (h ≫ sB) := hh ▸ inferInstance
    exact locallyOfFiniteType_of_comp h sB
  have hcl : IsClosed ({h.asFiber a} : Set (h.fiber (h a))) := by
    have hsub : IsClosed ({⟨a, rfl⟩} : Set (h.base ⁻¹' {h a})) := by
      refine isClosed_of_closure_subset fun b hb => ?_
      have hab : (⟨a, rfl⟩ : h.base ⁻¹' {h a}) ⤳ b := specializes_iff_mem_closure.mpr hb
      exact Subtype.ext (hamax b.1 ((Set.mem_singleton_iff.mp b.2).trans haξ)
        (hab.map continuous_subtype_val))
    have hpre : ({h.asFiber a} : Set (h.fiber (h a))) = h.fiberHomeo (h a) ⁻¹' {⟨a, rfl⟩} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        simp [Scheme.Hom.asFiber]
      · intro hz
        rw [Scheme.Hom.asFiber, ← hz, Homeomorph.symm_apply_apply]
    rw [hpre]
    exact (h.fiberHomeo (h a)).isClosed_preimage.mpr hsub
  have hfin := (isClosed_asFiber_iff_finite_residueField h a).mp hcl
  letI := (h.residueFieldMap a).hom.toAlgebra
  exact Module.finrank_pos.ne'

end CurveLifting

section FullTrace

/-- If `N = ∑ r_j L_j` is numerically trivial over `Z` and `L'_j = p^*L_j`, then
`∑ r_j (L'_j · C) = 0` for every curve `C` of `W` contracted by `p ≫ πX`. -/
private theorem sum_degreeOn_eq_zero_of_isNumericallyTrivialOver {k : Type u} [Field k]
    {W X Z : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian X] [IsNormal X] {sW : W ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sW] [QuasiCompact sX] [IsSeparated sX]
    [LocallyOfFiniteType sX] (πX : X ⟶ Z) (p : W ⟶ X) [IsProper p] (hpX : p ≫ sX = sW)
    {N : RDivisor X} (hN : IsNumericallyTrivialOver k sX πX N) {n : ℕ} (r : Fin n → ℝ)
    (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hNeq : N = ∑ j, r j • Divisor.toRDivisor (L j))
    {hB : ∀ j, ∀ Z' : irreducibleComponents W, p (componentGenericPoint W Z') ∉ (L j).supp}
    {L' : Fin n → Divisor W} (hL' : ∀ j, (L j).IsPullback p (hB j) (L' j))
    (hL'c : ∀ j, (L' j).IsCartier) (C : ProperCurve sW) (hC : C.IsContractedBy (p ≫ πX)) :
    ∑ j, r j * ((L' j).degreeOn k sW C.ι C.dim_le (hL'c j) : ℝ) = 0 := by
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  by_cases hCX : IsProperCurve sX (p C.point)
  · set CX : ProperCurve sX := ⟨p C.point, hCX⟩
    haveI : IsProper (CX.ι ≫ sX) := CX.isProper_ι_comp
    have hdeg : ∀ j, ((L' j).degreeOn k sW C.ι C.dim_le (hL'c j) : ℝ) =
        (residueFieldDegree p C.point : ℝ) * ((L j).degreeOn k sX CX.ι CX.dim_le (hL j) : ℝ) :=
      fun j => Proof_lem_fourfold_generic_comparison_effective.degreeOn_eq_mul_of_isPullback p hpX
        (hL j) (hL' j) (hL'c j) C CX rfl
    have hCXc : CX.IsContractedBy πX := by
      intro x hx
      have hx' : x ∈ p.base '' closure {C.point} := by
        rw [← p.isClosedMap.closure_image_eq_of_continuous p.continuous, Set.image_singleton]
        exact hx
      obtain ⟨y, hy, rfl⟩ := hx'
      simpa only [Scheme.Hom.comp_apply] using hC y hy
    have hzero : ∑ j, r j * ((L j).degreeOn k sX CX.ι CX.dim_le (hL j) : ℝ) = 0 :=
      hN.2.2 CX hCXc n r L _ 0 Fin.elim0 Fin.elim0 0
        (hNeq ▸ Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
          k sX CX r L hL)
        (isRIntersectionNumber_zero k sX CX)
    simp only [hdeg, mul_left_comm (r _), ← Finset.mul_sum, hzero, mul_zero]
  · have hdeg : ∀ j, (L' j).degreeOn k sW C.ι C.dim_le (hL'c j) = 0 :=
      fun j => Proof_lem_fourfold_generic_comparison_effective.degreeOn_eq_zero_of_isPullback p hpX
        (hL j) (hL' j) (hL'c j) C hCX
    simp [hdeg]

open Proof_lem_fourfold_generic_comparison_effective in
/-- **Two-sided negativity for the full trace.** If `N_W = ∑ r_j L'_j` has degree zero on every
curve contracted by `q`, and `q_* N_W = ∑ s_j M_j`, then `G = ∑ s_j q^*M_j` equals `N_W`. -/
private theorem eq_of_transformDivisor_eq_sum {k : Type u} [Field k] {W Y : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sW : W ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sW] [QuasiCompact sY] [IsSeparated sY]
    [LocallyOfFiniteType sY] (hY : IsNormalVariety k sY) (hW : IsNormalVariety k sW) (q : W ⟶ Y)
    (hqY : q ≫ sY = sW) [IsProper q] (hqb : IsBirationalMorphism q) {m : ℕ} (s : Fin m → ℝ)
    (M : Fin m → Divisor Y) (hM : ∀ j, (M j).IsCartier)
    (hB : ∀ j, ∀ Z' : irreducibleComponents W, q (componentGenericPoint W Z') ∉ (M j).supp)
    {G : RDivisor W}
    (hG : G = ∑ j, s j • Divisor.toRDivisor ((M j).pullback (hM j) (hB j)))
    {NW : RDivisor W} {n : ℕ} (r : Fin n → ℝ) (L' : Fin n → Divisor W)
    (hL'c : ∀ j, (L' j).IsCartier) (hNW : NW = ∑ j, r j • Divisor.toRDivisor (L' j))
    (hNY : RationalMap.transformDivisor q.toRationalMap NW = ∑ j, s j • Divisor.toRDivisor (M j))
    (hzero : ∀ C : ProperCurve sW, C.IsContractedBy q →
      ∑ j, r j * ((L' j).degreeOn k sW C.ι C.dim_le (hL'c j) : ℝ) = 0) :
    G = NW := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  set M' : Fin m → Divisor W := fun j => (M j).pullback (hM j) (hB j)
  have hM'p : ∀ j, (M j).IsPullback q (hB j) (M' j) := fun j =>
    Divisor.isPullback_pullback (hM j) (hB j)
  have hM'c : ∀ j, (M' j).IsCartier := fun j => (hM j).isCartier_pullback q (hB j)
  have hMzero : ∀ C : ProperCurve sW, C.IsContractedBy q →
      ∑ j, s j * ((M' j).degreeOn k sW C.ι C.dim_le (hM'c j) : ℝ) = 0 := by
    intro C hC
    have : ∀ j, (M' j).degreeOn k sW C.ι C.dim_le (hM'c j) = 0 := fun j =>
      Divisor.degreeOn_pullback_eq_zero_of_isContractedBy q hqY (hM j) (hB j) C hC
    simp [this]
  have hWq : IsNormalVariety k (q ≫ sY) := by
    rw [hqY]
    exact hW
  have hexcF : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sY q P →
      (G - NW).coeff P = 0 := by
    intro P hP
    obtain ⟨Q, hPQ, hiso, htr⟩ :=
      exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hY q hWq hqb P hP
    have hGP : G.coeff P = (RationalMap.transformDivisor q.toRationalMap NW).coeff Q := by
      rw [hNY, hG]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := MMP.Positivity.coeff_eq_of_isPullback P Q hPQ (hM j) (hM'p j)
      simp only [DivisorWithCoeffs.coeff_apply] at this
      change s j • ((M' j P : ℤ) : ℝ) = s j • ((M j Q : ℤ) : ℝ)
      rw [this]
    rw [DivisorWithCoeffs.coeff_sub, hGP]
    exact sub_eq_zero.mpr (htr NW)
  have hdeg : ∀ (a b : ℝ) (C : ProperCurve sW), C.IsContractedBy q →
      0 ≤ a * ∑ j, s j * ((M' j).degreeOn k sW C.ι C.dim_le (hM'c j) : ℝ) +
        b * ∑ j, r j * ((L' j).degreeOn k sW C.ι C.dim_le (hL'c j) : ℝ) := fun a b C hC => by
    simp [hMzero C hC, hzero C hC]
  refine sub_eq_zero.mp (eq_zero_of_isRelativelyNef_of_isRelativelyNef_neg hY hW q hqY hqb
    ?_ ?_ hexcF)
  · rw [show G - NW = (1 : ℝ) • G + (-1 : ℝ) • NW by module]
    exact isRelativelyNef_smul_add_smul k sW q s M' hM'c hG r L' hL'c hNW 1 (-1) (hdeg 1 (-1))
  · rw [show -(G - NW) = (-1 : ℝ) • G + (1 : ℝ) • NW by module]
    exact isRelativelyNef_smul_add_smul k sW q s M' hM'c hG r L' hL'c hNW (-1) 1 (hdeg (-1) 1)

/-- **Numerical triviality descends along a proper surjection.** If `D = ∑ s_j M_j` on `Y` and
`∑ s_j (q^*M_j · C') = 0` for every curve `C'` of `W` contracted by `q ≫ πY`, then `D` is
numerically trivial over `Z`. -/
private theorem isNumericallyTrivialOver_of_sum_degreeOn_pullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sW : W ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sW] [LocallyOfFiniteType sW] [QuasiCompact sY] [IsSeparated sY]
    [LocallyOfFiniteType sY] (πY : Y ⟶ Z) (q : W ⟶ Y) [IsProper q] [IsDominant q]
    (hqY : q ≫ sY = sW) {D : RDivisor Y} {m : ℕ} (s : Fin m → ℝ) (M : Fin m → Divisor Y)
    (hM : ∀ j, (M j).IsCartier) (hD : D = ∑ j, s j • Divisor.toRDivisor (M j))
    {hB : ∀ j, ∀ Z' : irreducibleComponents W, q (componentGenericPoint W Z') ∉ (M j).supp}
    {M' : Fin m → Divisor W} (hM' : ∀ j, (M j).IsPullback q (hB j) (M' j))
    (hM'c : ∀ j, (M' j).IsCartier)
    (h : ∀ C' : ProperCurve sW, C'.IsContractedBy (q ≫ πY) →
      ∑ j, s j * ((M' j).degreeOn k sW C'.ι C'.dim_le (hM'c j) : ℝ) = 0) :
    IsNumericallyTrivialOver k sY πY D := by
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  refine ⟨isCartierCombination_of_eq_sum s M hM hD,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, ?_⟩
  intro C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂
  rw [eq_sum_degreeOn_of_isRIntersectionNumber k sY C s M hM hD h₁,
    (IsRIntersectionNumber.eq_and_linear k sY C).1 0 r₂ L₂ _ _ x₂ 0 h₂
      (isRIntersectionNumber_zero k sY C)]
  obtain ⟨C', hC'pt, hd⟩ := exists_properCurve_map_eq sW sY q hqY C
  have hC'c : C'.IsContractedBy (q ≫ πY) := by
    intro y hy
    have hqy : q y ∈ closure {C.point} := by
      rw [← hC'pt]
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hy).map q.continuous)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC (q y) hqy,
      hC (q C'.point) (by rw [hC'pt]; exact subset_closure rfl)]
  have hdeg : ∀ j, ((M' j).degreeOn k sW C'.ι C'.dim_le (hM'c j) : ℝ) =
      (residueFieldDegree q C'.point : ℝ) * ((M j).degreeOn k sY C.ι C.dim_le (hM j) : ℝ) :=
    fun j => Proof_lem_fourfold_generic_comparison_effective.degreeOn_eq_mul_of_isPullback q hqY
      (hM j) (hM' j) (hM'c j) C' C hC'pt
  simpa only [hdeg, mul_left_comm (s _), ← Finset.mul_sum, mul_eq_zero, Nat.cast_eq_zero, hd,
    false_or] using h C' hC'c

end FullTrace

end Proof_lem_fourfold_numerically_trivial_full_trace

namespace MMP.Fourfold

open MMP.Mori
open Proof_lem_fourfold_numerically_trivial_full_trace

/-- **Numerically trivial full traces.** Let `p : W ⟶ X` and `q : W ⟶ Y` be projective birational
morphisms of normal projective varieties over `k`, over a projective base `Z` via `πX`, `πY`, with
`Y` `ℚ`-factorial. Let `N` be an `ℝ`-Cartier divisor on `X`, numerically trivial over `Z`, with
pull-back `N_W = p^*N`. Then `N_Y = q_* N_W` is numerically trivial over `Z` and `q^*N_Y = N_W`. -/
@[mmp "lem_fourfold_numerically_trivial_full_trace"]
public theorem isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback
    {k : Type u} [Field k] {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sW : W ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sY]
    (hW : IsNormalVariety k sW) (hWp : MMP.Mori.IsProjectiveVariety k sW)
    (hX : IsNormalVariety k sX) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hY : IsQFactorial sY) (hYp : MMP.Mori.IsProjectiveVariety k sY)
    (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    (πX : X ⟶ Z) (πY : Y ⟶ Z) (hπX : πX ≫ sZ = sX) (hπY : πY ≫ sZ = sY)
    (p : W ⟶ X) (q : W ⟶ Y)
    (hpX : p ≫ sX = sW) (hqY : q ≫ sY = sW) (hpq : p ≫ πX = q ≫ πY)
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    (hq : IsProjectiveMorphism q) (hqb : IsBirationalMorphism q)
    {N : RDivisor X} (hN : MMP.Flips.IsNumericallyTrivialOver k sX πX N)
    {NW : RDivisor W} (hNW : MMP.Flips.IsRCartierPullback p N NW) :
    MMP.Flips.IsNumericallyTrivialOver k sY πY
        (MMP.Mori.RationalMap.transformDivisor q.toRationalMap NW) ∧
      MMP.Flips.IsRCartierPullback q
        (MMP.Mori.RationalMap.transformDivisor q.toRationalMap NW) NW := by
  classical
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hp
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hq
  haveI : QuasiCompact sW := by rw [← hqY]; infer_instance
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hYn : IsNormalVariety k sY := hY.1
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : IsDominant q := hqb.isDominant
  set NY := MMP.Mori.RationalMap.transformDivisor q.toRationalMap NW
  obtain ⟨n, r, L, L', hL, hNeq, hpbL, hNWeq⟩ := hNW
  choose hBL hL' using hpbL
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL j) (hL' j)]
    exact (hL j).isCartier_pullback p (hBL j)
  have hNWzero :=
    sum_degreeOn_eq_zero_of_isNumericallyTrivialOver πX p hpX hN r L hL hNeq hL' hL'c
  obtain ⟨m, s, M, hM, hNYeq⟩ := isCartierCombination_of_isQFactorial hY NY
  simp only [← toRDivisor_eq_mapCoeffs] at hNYeq
  have hBM : ∀ j, ∀ Z' : irreducibleComponents W, q (componentGenericPoint W Z') ∉ (M j).supp :=
    fun j Z' => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q
      (M j) Z'
  set M' : Fin m → Divisor W := fun j => (M j).pullback (hM j) (hBM j)
  have hM'p : ∀ j, (M j).IsPullback q (hBM j) (M' j) := fun j =>
    Divisor.isPullback_pullback (hM j) (hBM j)
  have hM'c : ∀ j, (M' j).IsCartier := fun j => (hM j).isCartier_pullback q (hBM j)
  set G : RDivisor W := ∑ j, s j • Divisor.toRDivisor (M' j) with hGdef
  have hG : IsRCartierPullback q NY G :=
    ⟨m, s, M, M', hM, hNYeq, fun j => ⟨hBM j, hM'p j⟩, rfl⟩
  have hGeq : G = NW := eq_of_transformDivisor_eq_sum hYn hW q hqY hqb s M hM hBM hGdef r L'
    hL'c hNWeq hNYeq fun C hC => hNWzero C fun x hx => by
      rw [hpq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  refine ⟨isNumericallyTrivialOver_of_sum_degreeOn_pullback πY q hqY s M hM hNYeq hM'p hM'c
    fun C' hC' => ?_, hGeq ▸ hG⟩
  rw [← hNWzero C' (by rwa [hpq])]
  refine (IsRIntersectionNumber.eq_and_linear k sW C').1 NW s M' r L' _ _ ?_ ?_
  · rw [← hGeq]
    exact Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
      k sW C' s M' hM'c
  · rw [hNWeq]
    exact Proof_lem_fourfold_generic_comparison_effective.isRIntersectionNumber_sum_degreeOn
      k sW C' r L' hL'c

end MMP.Fourfold

end
