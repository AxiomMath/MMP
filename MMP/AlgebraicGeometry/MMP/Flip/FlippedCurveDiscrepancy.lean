module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization

/-!
# Discrepancies increase strictly along flipped curves

Let `X` be a normal variety over a perfect field `k` with canonical divisor `K`, `D` a
`ℚ`-divisor with `K_X + D` `ℚ`-Cartier, and `φ⁺ : X⁺ ⟶ Z` with `g : X ⤏ X⁺` a flip of the small
contraction `φ : X ⟶ Z` with respect to `K_X + D`. Put `D⁺ = g_*D` and `K_{X⁺} = g_*K`. If
`C ⊆ X⁺` is a flipped curve and `E` is a divisor with `Center_{X⁺}(E) = C`, then
`a(E, X, D) < a(E, X⁺, D⁺)`, where the function fields `k(X)` and `k(X⁺)` are identified over
`k(Z)`.

Both `φ` and `φ⁺` are isomorphisms in codimension one, so `K_X = div(φ^*τ)`,
`g_*K_X = div(φ⁺^*τ)` for a rational top form `τ` on `Z`, and `D = φ⁻¹_*D_Z`,
`g_*D = φ⁺⁻¹_*D_Z` for `D_Z = φ_*D`. The comparison of discrepancies over `Z` gives
`a(E, X, D) ≤ a(E, X⁺, g_*D)`. The center of `E` on `Z` is the closed point `z = φ⁺(C)`, and
equality would force `K_{X⁺} + g_*D` to be numerically trivial on `φ⁺⁻¹(z)`; but this divisor is
`φ⁺`-ample, so it has positive degree on any proper curve in the positive-dimensional fibre
`φ⁺⁻¹(z)`.

## Main results

* `MMP.Flips.IsFlippedCurveOf.isDiscrepancy_lt`: `a(E, X, D) < a(E, X⁺, g_*D)` for a divisor `E`
  with center a flipped curve.
* `MMP.Flips.IsRelativelyAmple.isRelativelyNef`: an `f`-ample `ℝ`-divisor is `f`-nef.
* `MMP.Flips.isSmall_id`: the identity of a variety is a small contraction.
* `MMP.Flips.IsSmall.exists_divisorOfForm_pullback_eq_transformDivisor`: for small contractions
  `φ : X ⟶ Z`, `φ⁺ : X⁺ ⟶ Z` and `g : X ⤏ X⁺` over `Z`, a canonical divisor is `K = div(φ^*τ)`
  with `g_*K = div(φ⁺^*τ)` for a nonzero rational top form `τ` on `Z`.
* `MMP.Flips.IsSmall.isCanonicalDivisor_transformDivisor`: `g_*K` is a canonical divisor of `X⁺`.

## Implementation notes

The divisor `E` is a divisor `(Y, f, E)` over `X⁺` (`MMP.Flips.ProperDivisorOver`) with center
`C`; its valuation `ord_E` lives on `k(X⁺)`, and is identified with the valuation `ν` of `k(X)`
satisfying `ν ∘ φ^* = ord_E ∘ φ⁺^*` on `k(Z)`. The inequality is stated for every such `ν` and
all values of the two discrepancies.

The source works over a field of characteristic zero; the statement holds over any perfect
field, which is what the comparison of discrepancies along birational maps requires.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.13.1,
  2.28.2
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-! ### Prime divisors under maps which are isomorphisms in codimension one -/

/-- The identity of a variety is a small contraction. -/
public theorem isSmall_id {k : Type u} [Field k] {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsVariety k sZ) : IsSmall k sZ sZ (𝟙 Z) where
  isVariety_target := hZ
  isVariety_source := hZ
  comp_eq := Category.id_comp sZ
  isProper := inferInstance
  isIso_app _ := inferInstance
  dim_eq := rfl
  exists_isIso := ⟨⊥, ⊥, le_closedsCodimension_iff_le_coheight.mpr (by simp),
    le_closedsCodimension_iff_le_coheight.mpr (by simp), le_rfl, by
      simp only [Scheme.Hom.resLE_id, Scheme.homOfLE_rfl]
      infer_instance⟩

/-- The inverse `f⁻¹ : Z ⤏ Y` of a birational morphism `f : Y ⟶ Z` to a separated scheme is a map
over `Z`: `f ∘ f⁻¹ = 𝟙_Z`. -/
private theorem isModificationOf_inverse {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [Z.IsSeparated] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) :
    IsModificationOf (𝟙 Z) f (MMP.Mori.RationalMap.IsBirational.inverse hf) := by
  refine ⟨hf.isBirational_inverse, ?_⟩
  obtain ⟨e, he, hinv⟩ := hf.isInverse_inverse
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) f
  rw [MMP.Flips.RationalMap.IsOver, ← hinv]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
    ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
  change Z.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ f = Z.homOfLE _ ≫ Z.topIso.hom ≫ 𝟙 Z
  rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
  simp

/-- If a map `h` sends every prime divisor `P` to `e P` for a bijection `e` of prime divisors,
then the coefficient of `h_* D` along `e P` is that of `D` along `P`. -/
private theorem transformDivisor_apply_of_equiv {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R]
    {h : X.RationalMap Y} (e : MMP.Mori.PrimeDivisor X ≃ MMP.Mori.PrimeDivisor Y)
    (he : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor h P = some (e P))
    (D : MMP.Mori.DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Mori.RationalMap.transformDivisor h D (e P) = D P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (he P)
    (fun P' hP' => e.injective (Option.some_injective _ ((he P').symm.trans hP'))) D

/-- A prime divisor of a normal variety `Y` is determined by its divisorial valuation restricted
along a morphism `f : Y ⟶ Z` with `f^*` surjective on function fields. -/
private theorem primeDivisor_eq_of_comap_eq {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ Z} [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P Q : MMP.Mori.PrimeDivisor Y}
    (h : P.divisorialValuation.comap (functionFieldMap f) =
      Q.divisorialValuation.comap (functionFieldMap f)) : P = Q := by
  have hv : P.divisorialValuation = Q.divisorialValuation := Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hf t
    exact congrArg (fun w => w s) h
  have h1 := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
    (D := DivisorOver.ofPrimeDivisor k hY P) (D' := DivisorOver.ofPrimeDivisor k hY Q)
    (by
      ext t
      change P.divisorialValuation (functionFieldMap (𝟙 Y) t) =
        Q.divisorialValuation (functionFieldMap (𝟙 Y) t)
      rw [functionFieldMap_id_apply, hv])
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective h1

/-- If a prime divisor `P` of `Y` and a prime divisor `Q` of `Z` induce the same valuation of
`k(Z)` through a birational morphism `f : Y ⟶ Z`, then `f(η_P) = η_Q`. -/
private theorem map_genericPoint_eq_of_comap_eq {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ) [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z] {f : Y ⟶ Z}
    (hY : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f) [IsDominant f]
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor Z}
    (h : P.divisorialValuation.comap (functionFieldMap f) =
      Q.divisorialValuation.comap (functionFieldMap (𝟙 Z))) :
    f P.genericPoint = Q.genericPoint :=
  MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ.1
    (D := ⟨Y, f, hY, hf, P⟩) (D' := DivisorOver.ofPrimeDivisor k hZ Q) h

/-! ### Rational top forms along birational morphisms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral Y] [IsIntegral Z] [LocallyOfFiniteType sZ] {f : Y ⟶ Z} [IsDominant f]

/-- Along a birational morphism `f : Y ⟶ Z`, every nonzero rational `n`-form on `Y` is the
pull-back of a nonzero one on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {ω : RationalPluriForms (f ≫ sZ) n 1} (hω : ω ≠ 0) :
    ∃ τ : RationalPluriForms sZ n 1, τ ≠ 0 ∧ pullbackRationalPluriForms sZ f τ = ω := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hf hd
  obtain ⟨c, hc⟩ := hf.2 ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  let τ : RationalPluriForms sZ n 1 :=
    c • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sZ f τ = ω := by
    change pullbackForms (K := Z.functionField) (K' := Y.functionField) 1 _ = ω
    rw [pullbackForms_eq hω₀, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    change functionFieldMap f c • _ = ω
    rw [hc]
    exact basis_unit_repr_smul _ ω
  refine ⟨τ, fun h0 => hω ?_, hpull⟩
  rw [← hpull, h0]
  change pullbackForms (K := Z.functionField) (K' := Y.functionField) 1 0 = 0
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp

/-- Along a birational morphism `f : Y ⟶ Z`, the pull-back of a nonzero rational `n`-form on `Z`
is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {τ : RationalPluriForms sZ n 1} (hτ : τ ≠ 0) : pullbackRationalPluriForms sZ f τ ≠ 0 := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sZ f hf
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn)
  rw [show pullbackRationalPluriForms sZ f τ = pullbackFormsAlong (K' := Y.functionField) hω 1 τ
    from pullbackForms_eq hω 1 τ]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ 1).ne_zero ())

variable [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]

/-- `ord_P(f^*τ) = ord_Q(τ)` for a birational morphism `f` with `f(η_P) = η_Q`. -/
private theorem ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor Z}
    (h : f P.genericPoint = Q.genericPoint) (τ : RationalPluriForms sZ n 1) :
    P.ordForm (pullbackRationalPluriForms sZ f τ) = Q.ordForm τ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (f P.genericPoint)) := by rw [h]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P.genericPoint
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hf
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn) P Q h τ

end Forms

/-! ### Proper curves are not points -/

/-- A space of Krull dimension one has two distinct points. -/
private theorem not_subsingleton_of_topologicalKrullDim_eq_one {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T = 1) : ¬ Subsingleton T := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology T
  rw [h] at h0
  exact absurd h0 (by decide)

/-! ### Intersection numbers with proper curves -/

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  refine not_subsingleton_of_topologicalKrullDim_eq_one C.dim_eq ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
  obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
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
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
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

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample Cartier divisor has positive intersection number with every proper curve
contracted by `f`. -/
private theorem pos_of_isCartierIntersectionNumber [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {L : Divisor X} (hLa : IsRelativelyAmpleCartier f L) {hL : L.IsCartier}
    {C : ProperCurve sX} (hC : C.IsContractedBy f) {d : ℤ}
    (h : IsCartierIntersectionNumber k sX C L hL d) : 0 < d := by
  rw [eq_degreeOn_of_isCartierIntersectionNumber k sX h]
  exact degreeOn_pos_of_isRelativelyAmpleCartier k sX f hLa hL C hC

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a regular proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
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
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

end Curves

/-! ### Contracted curves in fibres -/

section ContractedCurves

/-- In a Noetherian quasi-sober space, a closed connected set `F` that meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  obtain ⟨s, hsT, hsS⟩ : (closure T ∩ S).Nonempty := by
    obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => (em (a ∈ S)).symm.imp
        (fun haS => subset_closure (show a ∈ T from ⟨ha, haS⟩)) id)
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact ⟨w, hw⟩
  obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure T))
  have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
    refine closure_minimal (fun y hy => ?_) ?_
    · obtain ⟨z, hz, hyz⟩ : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
      exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
    · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
  obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
  have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
  exact ⟨ζ, closure_minimal Set.sdiff_subset hF (hzT hζ.mem),
    fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS), s, hsS, hζ.specializes hsz⟩

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp (k : Type u) [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : IsNormalVariety k sX) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    refine not_subsingleton_of_topologicalKrullDim_eq_one C.dim_eq
      ⟨fun a b => C.ι.isEmbedding.injective (hι ?_)⟩
    have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
    have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
    simpa using ha.trans hb.symm
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S`. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ (Set.range C.ι ∩ S).Nonempty := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := exists_specializes_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp k sX f hX x hx
  have : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
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
  obtain ⟨y', -, hy'p', -, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : ProperCurve sF := ⟨y', hy'⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  let C : ProperCurve sY := ⟨ι y', isProperCurve_of_injective sY ι ι.isEmbedding.injective C'⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← hrange, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι y' ∈ closure {ι y'})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, p, ?_, hpS⟩
  rw [hrC, ← hp']
  exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end ContractedCurves

/-! ### Relative ampleness and centers -/

/-- An `f`-ample `ℝ`-divisor is `f`-nef. -/
public theorem IsRelativelyAmple.isRelativelyNef {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X}
    (hA : IsRelativelyAmple f A) : IsRelativelyNef k sX f A := by
  obtain ⟨m, r, L, -, hr, hLa, hAL⟩ := hA
  refine ⟨m, r, L, fun j => (hLa j).1, hAL, fun C hC x hx' => ?_⟩
  obtain ⟨hL, d, -, hd, hx⟩ := hx'
  rw [hx]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le
    (by exact_mod_cast (pos_of_isCartierIntersectionNumber k sX f (hLa j) hC (hd j)).le)

/-- An `f`-ample `ℝ`-divisor has a positive intersection number with every proper curve
contracted by `f`. -/
private theorem exists_isRIntersectionNumber_pos {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X}
    (hA : IsRelativelyAmple f A) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX A r L C x ∧ 0 < x := by
  obtain ⟨m, r, L, hm, hr, hLa, hAL⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hLa j).1
  choose d hd using fun j => exists_isCartierIntersectionNumber k sX C (L j) (hLc j)
  refine ⟨m, r, L, ∑ j, r j * d j, ⟨hLc, d, hAL, hd, rfl⟩, ?_⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hr j)
    (by exact_mod_cast pos_of_isCartierIntersectionNumber k sX f (hLa j) hC (hd j)))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩

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

/-- The valuation of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-! ### Descending the flip to the base -/

/-- For small contractions `φ : X ⟶ Z`, `φ⁺ : X⁺ ⟶ Z` and a map `g : X ⤏ X⁺` over `Z`, a
canonical divisor `K` and a boundary `D` of `X` descend to `Z`: there are a nonzero rational top
form `τ` on `Z` and an `ℝ`-divisor `D_Z` with `K = div(φ^*τ)`, `g_*K = div(φ⁺^*τ)`, `D = φ⁻¹_*D_Z`,
`g_*D = φ⁺⁻¹_*D_Z`, and `g_*` commutes with forming `K + D`. -/
private theorem exists_form_and_boundary_of_isSmall {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] [IsIntegral Z]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ]
    [IsDominant φp] [LocallyOfFiniteType (φ ≫ sZ)] [LocallyOfFiniteType (φp ≫ sZ)]
    {g : X.RationalMap X'} (hZ : IsNormalVariety k sZ)
    (hX : IsNormalVariety k (φ ≫ sZ)) (hX' : IsNormalVariety k (φp ≫ sZ))
    (hφ : IsSmall k sZ (φ ≫ sZ) φ) (hφp : IsSmall k sZ (φp ≫ sZ) φp)
    (hg : IsModificationOf φ φp g) (hK : K.IsCanonicalDivisor (φ ≫ sZ) n) :
    ∃ (τ : RationalPluriForms sZ n 1) (DZ : RDivisor Z), τ ≠ 0 ∧
      divisorOfForm (pullbackRationalPluriForms sZ φ τ) = K ∧
      divisorOfForm (pullbackRationalPluriForms sZ φp τ) = Mori.RationalMap.transformDivisor g K ∧
      birationalInverseTransform φ hφ.surjective_and_isBirational.2 DZ = QDivisor.toRDivisor D ∧
      birationalInverseTransform φp hφp.surjective_and_isBirational.2 DZ =
        QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D) ∧
      Mori.RationalMap.transformDivisor g (logCanonicalDivisor K (QDivisor.toRDivisor D)) =
        logCanonicalDivisor (Mori.RationalMap.transformDivisor g K)
          (QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)) := by
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  have hbφ : IsBirationalMorphism φ := hφ.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφp.surjective_and_isBirational.2
  have hnZ : topologicalKrullDim Z = n := hφ.dim_eq.symm.trans hK.topologicalKrullDim_eq
  -- the bijections of prime divisors induced by `g`, `φ⁻¹` and `φ⁺⁻¹`
  have he := (exceptional_hasNonemptyCenter_iff_of_isSmall _ _ sZ φ φp hφ hφp).2 g hg
  set e := primeDivisorEquivOfModification hφ hφp hg
  have he₂ := (exceptional_hasNonemptyCenter_iff_of_isSmall sZ _ sZ (𝟙 Z) φ
    (isSmall_id hZ.1) hφ).2 _ (isModificationOf_inverse φ hbφ)
  set e₂ := primeDivisorEquivOfModification (isSmall_id hZ.1) hφ (isModificationOf_inverse φ hbφ)
  have he₃ := (exceptional_hasNonemptyCenter_iff_of_isSmall sZ _ sZ (𝟙 Z) φp
    (isSmall_id hZ.1) hφp).2 _ (isModificationOf_inverse φp hbφp)
  set e₃ := primeDivisorEquivOfModification (isSmall_id hZ.1) hφp (isModificationOf_inverse φp hbφp)
  have he₃e : ∀ Q, e₃ Q = e (e₂ Q) := fun Q => primeDivisor_eq_of_comap_eq hX'
    hbφp.functionFieldMap_bijective.2 ((he₃ Q).2.trans ((he (e₂ Q)).2.trans (he₂ Q).2).symm)
  have hcoeff : ∀ {R : Type} [AddCommMonoid R] (B : MMP.Mori.DivisorWithCoeffs R X) P,
      MMP.Mori.RationalMap.transformDivisor g B (e P) = B P :=
    fun B P => transformDivisor_apply_of_equiv e (fun P => (he P).1) B P
  have hord : ∀ τ : RationalPluriForms sZ n 1, ∀ Q,
      (e₂ Q).ordForm (pullbackRationalPluriForms sZ φ τ) =
        (e₃ Q).ordForm (pullbackRationalPluriForms sZ φp τ) := fun τ Q => by
    rw [ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq hbφ.functionFieldMap_bijective
        hnZ (map_genericPoint_eq_of_comap_eq hZ hX hbφ (he₂ Q).2) τ,
      ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq hbφp.functionFieldMap_bijective
        hnZ (map_genericPoint_eq_of_comap_eq hZ hX' hbφp (he₃ Q).2) τ]
  -- `K = div(φ^*τ)` for a rational top form `τ` on `Z`
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨τ, hτ0, hτ⟩ := exists_pullbackRationalPluriForms_eq hbφ.functionFieldMap_bijective
    hnZ hω0
  let DZ : RDivisor Z := Finsupp.equivMapDomain e₂.symm (QDivisor.toRDivisor D)
  have hDZ : ∀ Q, DZ Q = QDivisor.toRDivisor D (e₂ Q) := fun Q => by
    simp [DZ, Finsupp.equivMapDomain_apply]
  refine ⟨τ, DZ, hτ0, by rw [hτ]; exact DivisorWithCoeffs.ext' hω, ?_, ?_, ?_, ?_⟩
  · refine DivisorWithCoeffs.ext' fun P' => ?_
    obtain ⟨Q, rfl⟩ := e₃.surjective P'
    rw [coeff_divisorOfForm, ← hord]
    change _ = MMP.Mori.RationalMap.transformDivisor g K (e₃ Q)
    rw [he₃e, hcoeff, hτ]
    exact hω (e₂ Q)
  · refine Finsupp.ext fun P => ?_
    obtain ⟨Q, rfl⟩ := e₂.surjective P
    exact (transformDivisor_apply_of_equiv e₂ (fun Q => (he₂ Q).1) DZ Q).trans (hDZ Q)
  · refine Finsupp.ext fun P' => ?_
    obtain ⟨Q, rfl⟩ := e₃.surjective P'
    refine (transformDivisor_apply_of_equiv e₃ (fun Q => (he₃ Q).1) DZ Q).trans ?_
    rw [hDZ, he₃e]
    change _ = ((MMP.Mori.RationalMap.transformDivisor g D (e (e₂ Q)) : ℚ) : ℝ)
    rw [hcoeff]
    rfl
  · refine Finsupp.ext fun P' => ?_
    obtain ⟨P, rfl⟩ := e.surjective P'
    rw [hcoeff]
    change ((K P : ℤ) : ℝ) + ((D P : ℚ) : ℝ) =
      ((MMP.Mori.RationalMap.transformDivisor g K (e P) : ℤ) : ℝ) +
        ((MMP.Mori.RationalMap.transformDivisor g D (e P) : ℚ) : ℝ)
    rw [hcoeff, hcoeff]

section Canonical

variable {k : Type u} [Field k] [PerfectField k] {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X']
  [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z] {n : ℕ} {K : Divisor X}
  {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ] [IsDominant φp] [LocallyOfFiniteType (φ ≫ sZ)]
  [LocallyOfFiniteType (φp ≫ sZ)] {g : X.RationalMap X'}

/-- For small contractions `φ : X ⟶ Z`, `φ⁺ : X⁺ ⟶ Z` and a map `g : X ⤏ X⁺` over `Z`, a
canonical divisor `K` of `X` is `div(φ^*τ)` for a nonzero rational top form `τ` on `Z`, and then
`g_*K = div(φ⁺^*τ)`. -/
public theorem IsSmall.exists_divisorOfForm_pullback_eq_transformDivisor
    (hφ : IsSmall k sZ (φ ≫ sZ) φ) (hφp : IsSmall k sZ (φp ≫ sZ) φp)
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (φ ≫ sZ))
    (hX' : IsNormalVariety k (φp ≫ sZ)) (hg : IsModificationOf φ φp g)
    (hK : K.IsCanonicalDivisor (φ ≫ sZ) n) :
    ∃ τ : RationalPluriForms sZ n 1, τ ≠ 0 ∧
      divisorOfForm (pullbackRationalPluriForms sZ φ τ) = K ∧
      divisorOfForm (pullbackRationalPluriForms sZ φp τ) =
        Mori.RationalMap.transformDivisor g K := by
  obtain ⟨τ, -, hτ, h1, h2, -⟩ :=
    exists_form_and_boundary_of_isSmall (D := 0) hZ hX hX' hφ hφp hg hK
  exact ⟨τ, hτ, h1, h2⟩

/-- **The canonical divisor across a small modification.** For small contractions `φ : X ⟶ Z`,
`φ⁺ : X⁺ ⟶ Z` of normal varieties over a perfect field and a map `g : X ⤏ X⁺` over `Z`, the
transform `g_*K` of a canonical divisor `K` of `X` is a canonical divisor of `X⁺`. -/
public theorem IsSmall.isCanonicalDivisor_transformDivisor
    (hφ : IsSmall k sZ (φ ≫ sZ) φ) (hφp : IsSmall k sZ (φp ≫ sZ) φp)
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (φ ≫ sZ))
    (hX' : IsNormalVariety k (φp ≫ sZ)) (hg : IsModificationOf φ φp g)
    (hK : K.IsCanonicalDivisor (φ ≫ sZ) n) :
    Divisor.IsCanonicalDivisor (φp ≫ sZ) n (Mori.RationalMap.transformDivisor g K) := by
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  obtain ⟨τ, hτ, -, h⟩ := hφ.exists_divisorOfForm_pullback_eq_transformDivisor hφp hZ hX hX' hg hK
  have hnZ : topologicalKrullDim Z = n := hφ.dim_eq.symm.trans hK.topologicalKrullDim_eq
  obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor _ hX'
    (hφp.dim_eq.trans hnZ)
  have hbφp : IsBirationalMorphism φp := hφp.surjective_and_isBirational.2
  have hl := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX' hK'
    (pullbackRationalPluriForms_ne_zero hbφp.functionFieldMap_bijective hnZ hτ)
  rw [one_zsmul, h] at hl
  exact hK'.of_linearlyEquivalent hl

end Canonical

/-- A proper divisor `E` over `X⁺` is, through a birational morphism `φ⁺ : X⁺ ⟶ Z`, a proper
divisor over `Z` with valuation `v_E ∘ φ⁺^*` and center the closure of `φ⁺(η_E)`. -/
private theorem exists_properDivisorOver_comp {k : Type u} [Field k] {X' Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X'] [IsIntegral Z] [IsLocallyNoetherian X'] [IsNormal X']
    [IsLocallyNoetherian Z] [IsNormal Z] {φp : X' ⟶ Z} [IsDominant φp] [IsProper φp]
    (hφp : IsBirationalMorphism φp)
    (E : ProperDivisorOver k (φp ≫ sZ)) :
    ∃ B : ProperDivisorOver k sZ, B.valuation = E.valuation.comap (functionFieldMap φp) ∧
      IsGenericPoint (φp (E.f E.E.genericPoint)) (B.center : Set Z) := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := E.isProper
  have hb : IsBirationalMorphism (E.f ≫ φp) := isBirationalMorphism_comp_of_isBirational φp E.f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hφp)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism E.isBirationalMorphism)
  let B : ProperDivisorOver k sZ :=
    ⟨⟨E.Y, E.f ≫ φp, by rw [Category.assoc]; exact E.isNormalVariety, hb, E.E⟩, inferInstance⟩
  refine ⟨B, (comap_valuationOver E.E E.f φp).symm, ?_⟩
  rw [B.center_eq_toDivisorOver_center, B.toDivisorOver.center_eq_closure_genericPoint]
  rfl

/-! ### Relatively ample divisors over a point with a positive-dimensional fibre -/

/-- Let `f : Y ⟶ Z` be a proper birational morphism of normal varieties and `z ∈ Z` a closed
point whose fibre contains a set of positive dimension. Then no `f`-ample `ℝ`-divisor is
numerically trivial over `z`. -/
private theorem not_isNumericallyTrivialOverPoint_of_isRelativelyAmple {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [QuasiCompact sZ] (hZ : IsNormalVariety k sZ) {f : Y ⟶ Z} [IsProper f]
    (hY : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f) {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {z : Z} (hz : IsClosed ({z} : Set Z)) {C : Set Y}
    (hCz : C ⊆ f.base ⁻¹' {z}) (hC : 0 < topologicalKrullDim C) :
    ¬ IsNumericallyTrivialOverPoint k (f ≫ sZ) f A z := by
  haveI : QuasiCompact (f ≫ sZ) := hY.1.toQuasiCompact
  haveI : LocallyOfFiniteType (f ≫ sZ) := hY.1.toLocallyOfFiniteType
  rintro ⟨-, U, hzU, hU⟩
  -- a proper curve `C₀` in the fibre `f⁻¹(z)`
  obtain ⟨C₀, hC₀, hC₀z⟩ : ∃ C₀ : ProperCurve (f ≫ sZ), C₀.IsContractedBy f ∧ f C₀.point = z := by
    obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ : ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ := by
      by_contra! hsub
      haveI : Subsingleton C := ⟨fun x y => Subtype.ext (hsub x x.2 y y.2)⟩
      exact (hC.trans_le (topologicalKrullDim_zero_of_discreteTopology C)).false
    haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (f ≫ sZ)
    have hFcl : IsClosed (f.base ⁻¹' {z}) := hz.preimage f.continuous
    obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
      ⟨c₁, (show c₁ ∈ closure {c₁} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
    have hpF : p ∈ f.base ⁻¹' {z} :=
      closure_minimal (Set.singleton_subset_iff.mpr (hCz hc₁)) hFcl hps
    obtain ⟨C₀, hC₀, q, hq, rfl⟩ := exists_properCurve_isContractedBy k sZ (f ≫ sZ) hZ hY
      f rfl hf z hz (S := {p}) (mem_closedPoints_iff.mp hpc) ⟨p, hpF, rfl⟩ fun h => hne <|
        (h (hCz hc₁)).trans (h (hCz hc₂)).symm
    rw [C₀.range_ι] at hq
    exact ⟨C₀, hC₀, (hC₀ _ hq).symm.trans hpF⟩
  obtain ⟨m, r, L, x, hx, hxpos⟩ := exists_isRIntersectionNumber_pos (f ≫ sZ) hA C₀ hC₀
  exact hxpos.ne' (hU C₀ hC₀ (hC₀z ▸ hzU) (hC₀z ▸ subset_closure rfl) (hC₀z ▸ hz) m r L x hx)

/-- **Discrepancies increase strictly along flipped curves** (FA 4.13.1). Let `X` be a normal
variety of dimension `n` over a perfect field `k` with canonical divisor `K`, `D` a `ℚ`-divisor
with `K_X + D` `ℚ`-Cartier, and let `C ⊆ X⁺` be a flipped curve of a flip `φ⁺ : X⁺ ⟶ Z`,
`g : X ⤏ X⁺`, of the small contraction `φ : X ⟶ Z` with respect to `K_X + D`
(`MMP.Flips.IsFlippedCurveOf`). Let `E'` be a divisor over `X⁺` with `Center_{X⁺}(E') = C`, and
`ν` the valuation of `k(X)` corresponding to `ord_{E'}` over `k(Z)`. Then every discrepancy `a`
of `ν` with respect to `(X, D)` is strictly smaller than every discrepancy `a'` of `ord_{E'}`
with respect to `(X⁺, g_*D)`, computed with the canonical divisor `g_*K`. -/
@[mmp "lem_fa4_flipped_curve_log_discrepancy_increase"]
public theorem IsFlippedCurveOf.isDiscrepancy_lt {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsIntegral Z]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ]
    [IsDominant φp] {g : X.RationalMap X'} {C : Set X'}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hD : (Divisor.toQDivisor K + D).IsQCartier)
    (hC : IsFlippedCurveOf k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g C)
    (E' : ProperDivisorOver k sX') (hE' : (E'.center : Set X') = C)
    {ν : Valuation X.functionField ℤᵐ⁰}
    (hν : ν.comap (functionFieldMap φ) = E'.valuation.comap (functionFieldMap φp))
    {a a' : ℝ} (ha : IsDiscrepancy sX n K (QDivisor.toRDivisor D) ν a)
    (ha' : IsDiscrepancy sX' n (Mori.RationalMap.transformDivisor g K)
      (QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)) E'.valuation a') :
    a < a' := by
  obtain ⟨hflip, -, -, -, -, z, hzc, hCmax, hCdim⟩ := hC
  have hφs : IsSmall k sZ sX φ := hflip.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hflip.isSmall
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  have hX'n : IsNormalVariety k sX' := hflip.isNormalVariety_flip
  obtain rfl : φ ≫ sZ = sX := hφs.comp_eq
  obtain rfl : φp ≫ sZ = sX' := hφps.comp_eq
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper φ := hφs.isProper
  haveI : IsProper φp := hφps.isProper
  haveI : QuasiCompact (φ ≫ sZ) := hX.1.toQuasiCompact
  haveI : QuasiCompact (φp ≫ sZ) := hX'n.1.toQuasiCompact
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  obtain ⟨τ, DZ, -, hdivX, hdivX', hbit1, hbit2, hlog⟩ :=
    exists_form_and_boundary_of_isSmall (D := D) hZn hX hX'n hφs hφps hflip.isModificationOf hK
  have hlogX' : logCanonicalDivisor (Mori.RationalMap.transformDivisor g K)
      (birationalInverseTransform φp hbφp DZ + 0) =
      Mori.RationalMap.transformDivisor g (logCanonicalDivisor K (QDivisor.toRDivisor D)) := by
    rw [hbit2, add_zero, hlog]
  have hAX : IsRelativelyNef k (φ ≫ sZ) φ
      (-logCanonicalDivisor K (birationalInverseTransform φ hbφ DZ + 0)) := by
    rw [hbit1, add_zero]
    exact hflip.isRelativelyAntiAmple.isRelativelyNef _
  have hAY : IsRelativelyNef k (φp ≫ sZ) φp
      (logCanonicalDivisor (Mori.RationalMap.transformDivisor g K)
        (birationalInverseTransform φp hbφp DZ + 0)) := by
    rw [hlogX']
    exact hflip.isRelativelyAmple_transform.isRelativelyNef _
  -- the divisor `E` over `Z`, whose center is the closed point `z = φ⁺(C)`
  obtain ⟨Bv, hBv, hb⟩ := exists_properDivisorOver_comp hbφp E'
  have hbz : φp (E'.f E'.E.genericPoint) = z := by
    refine hCmax.prop.2 ?_
    rw [← hE', E'.coe_center]
    refine ⟨_, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hvZ := hBv ▸ hasNonemptyCenter_valuation Bv
  have ha₁ : IsDiscrepancy (φ ≫ sZ) n K (birationalInverseTransform φ hbφ DZ + 0) ν a := by
    rwa [hbit1, add_zero]
  have ha₁' : IsDiscrepancy (φp ≫ sZ) n (Mori.RationalMap.transformDivisor g K)
      (birationalInverseTransform φp hbφp DZ + 0) E'.valuation a' := by
    rwa [hbit2, add_zero]
  -- the comparison of discrepancies over `Z`, and its equality case
  refine lt_of_le_of_ne ((isDiscrepancy_le_of_isRelativelyNef hZn hX hX'n hbφ hbφp hdivX hdivX'
    (E_X := 0) (E_Y := 0) (fun _ _ => rfl) (fun _ _ => rfl) hAX hAY hvZ hν rfl).2.2
    _ _ ha₁ ha₁') fun h => ?_
  have htriv := ((isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint hZn hX hX'n hbφ hbφp hdivX
    hdivX' (E_X := 0) (E_Y := 0) (fun _ _ => rfl) (fun _ _ => rfl) hAX hAY hvZ hν rfl
    hBv hb ha₁ ha₁').mp h).2
  rw [hbz, hlogX'] at htriv
  exact not_isNumericallyTrivialOverPoint_of_isRelativelyAmple hZn hX'n hbφp
    hflip.isRelativelyAmple_transform hzc (fun x hx => hCmax.prop.2 hx) hCdim htriv

end MMP.Flips

end
