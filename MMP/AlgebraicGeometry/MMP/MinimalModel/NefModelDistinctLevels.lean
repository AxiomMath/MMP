module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.RealKltRationalDecomposition
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.StalkValuationRing

/-!
# Distinct ordered levels give inequivalent nef models

Let `X` and `X'` be normal `ℚ`-factorial projective threefolds over a base `S`, and let
`ψ : X ⤏ X'` be an isomorphism in codimension one over `S`. Put `K' = ψ_* K`, `B' = ψ_* B`,
`H' = ψ_* H`. Suppose that `(X, B + t H)` and `(X', B' + t' H')` are klt pairs whose adjoints
`K + B + t H` and `K' + B' + t' H'` are nef over `S`, that `t > t' ≥ 0`, and that some curve
`C ⊆ X` over a point of `S` has `(K + B + t H) · C = 0` and `H · C > 0`. Then the two nef models
are not equivalent.

Indeed, if they were, a rational null decomposition of `K' + B' + t' H'` would descend
summand by summand to `X` along the common resolution, and its weighted sum would be
`K + B + t' H`, nef over `S`; but its degree on `C` is `(t' - t) (H · C) < 0`.

## Main results

* `MMP.Fourfold.not_isNefModelEquivalent_of_lt_of_isRIntersectionNumber_pos`.

## Implementation notes

Klt pairs with real boundary are `MMP.Fourfold.IsRealKltPair` together with effectivity of the
boundary; nefness over `S` is `MMP.Flips.IsRelativelyNef`, and equivalence of nef models is
`MMP.Fourfold.IsNefModelEquivalent` along `ψ`. The two degree conditions on `C` are each asked of
one presentation of the divisor as a real combination of Cartier divisors
(`MMP.Flips.IsRIntersectionNumber`); the degree does not depend on the presentation. The base
field is any algebraically closed field of characteristic zero.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### `ℝ`-intersection numbers as degrees along the curve -/

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve has more than one point. -/
private theorem not_subsingleton (C : ProperCurve sX) : ¬ Subsingleton C.scheme := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine not_subsingleton C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
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
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
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
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [eq_degreeOn (hd j)]

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
  rw [ht, Scheme.Hom.comp_apply] at h1 h2
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

/-- Let `D = ∑ cᵢ Eᵢ` with each `Eᵢ` null on every proper curve on which `D` is null. Then each
pull-back `u^* Eᵢ` is null on every proper curve on which `u^* D` is null. -/
private theorem degreeOn_isPullback_eq_zero_of_forall_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV)
    {D : RDivisor T} {D' : RDivisor V} (hD' : MMP.Flips.IsRCartierPullback u D D') {s : ℕ}
    (c : Fin s → ℝ) {E : Fin s → Divisor T} (hE : ∀ i, (E i).IsCartier)
    (hD : D = ∑ i, c i • Divisor.toRDivisor (E i))
    (hnull : ∀ Γ' : ProperCurve sT,
      ∑ j, c j * ((E j).degreeOn k sT Γ'.ι Γ'.dim_le (hE j) : ℝ) = 0 →
        ∀ i, (E i).degreeOn k sT Γ'.ι Γ'.dim_le (hE i) = 0)
    {hB : ∀ i, ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ (E i).supp}
    {G : Fin s → Divisor V} (hG : ∀ i, (E i).IsPullback u (hB i) (G i)) (i : Fin s)
    (Γ : ProperCurve sV)
    (hΓ : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sV D' r L Γ x → x = 0) :
    (G i).degreeOn k sV Γ.ι Γ.dim_le ((hG i).isCartier (hE i)) = 0 := by
  by_cases hq : Γ.IsContractedBy u
  · exact degreeOn_isPullback_eq_zero u hu (hE i) (hG i) Γ hq
  set Γ' : ProperCurve sT := ⟨u Γ.point, isProperCurve_map u hu Γ hq⟩
  rw [degreeOn_isPullback_eq_mul u hu (hE i) (hG i) Γ Γ' rfl, hnull Γ'
    ((forall_eq_zero_iff Γ' c E hE hD).1
      ((forall_eq_zero_iff_of_isRCartierPullback u hu hD' Γ hq Γ' rfl).1 hΓ)) i, mul_zero]

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

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, h⟩ := hD
  exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩

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
  exact not_subsingleton C ⟨fun a b => C.ι.isEmbedding.injective ((hr a).trans (hr b).symm)⟩

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

/-! ### Points of a common resolution over codimension-one points -/

section Points

open CategoryTheory.Limits

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A dominant morphism of integral schemes with normal target inducing an isomorphism of function
fields is a local isomorphism at every point over a point of coheight at most one. -/
private theorem isIso_stalkMap_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : Order.coheight (f x) ≤ 1) :
    IsIso (f.stalkMap x) := by
  have := MMP.valuationRing_stalk hx
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

/-- Two points over a point of coheight at most one coincide. -/
private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := MMP.valuationRing_stalk hx
  have := isIso_stalkMap_of_coheight_le_one f hf hx
  have := isIso_stalkMap_of_coheight_le_one f hf (h ▸ hx)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- Two partial maps with the same domain representing the same rational map to a separated
scheme are equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

/-- The partial map given by the inclusion of a dense open `U`, composed with `q`, represents
`q`. -/
private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  have hp : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he1)).symm
  rw [hp, Iso.inv_hom_id_assoc, Category.comp_id]

/-- If a representative of `φ` defined at `η_P` sends it to `η_E`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A partial map `g` represents an inverse `h` of the morphism `p`: then `p ∘ g` is the
identity on the domain of `g`. -/
private theorem apply_hom_eq_of_isInverse {Y V : Scheme.{u}} [IsReduced Y] [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (g : Y.PartialMap V)
    (hg : g.toRationalMap = h) {y : Y} (hy : y ∈ g.domain) : p (g.hom ⟨y, hy⟩) = y := by
  have he : g.hom ≫ p = g.domain.ι ≫ 𝟙 Y :=
    hom_eq_of_toRationalMap_eq g.dense_domain <| by
      rw [toRationalMap_ι_comp]
      change (g.compHom p).toRationalMap = _
      rw [Scheme.RationalMap.compHom_toRationalMap, hg, compHom_eq_of_isInverse hinv]
  calc p (g.hom ⟨y, hy⟩) = (g.hom ≫ p) ⟨y, hy⟩ := (Scheme.Hom.comp_apply _ _ _).symm
    _ = y := by
      rw [he]
      simp

/-- A rational map `Y ⤏ V` inverse to a proper morphism `p : V ⟶ Y` is defined at the generic
point of every prime divisor of `Y`. -/
private theorem exists_rep_mem_domain {Y V : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsReduced V] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p]
    {h : Y.RationalMap V} (hinv : RationalMap.IsInverse p.toRationalMap h)
    (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ g : Y.PartialMap V, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
  obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Y) p h
      (compHom_eq_of_isInverse hinv) Q.coheight_genericPoint.le)
  exact ⟨g, hg', hg⟩

/-- **The point over a source prime.** Let `p : V ⟶ Y` be proper with inverse `h`, and
`q : V ⟶ T` with `q ∘ h = φ`. If `φ_* R = P`, then some point of `V` lies over `η_R` and over
`η_P`. -/
private theorem exists_apply_eq_genericPoint {Y V T : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p]
    {q : V ⟶ T} {h : Y.RationalMap V} {φ : Y.RationalMap T}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    {R : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor T}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some P) :
    ∃ w : V, q w = P.genericPoint ∧ p w = R.genericPoint := by
  obtain ⟨g, hg, hRg⟩ := exists_rep_mem_domain hinv R
  exact ⟨g.hom ⟨R.genericPoint, hRg⟩, (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hR
    (g.compHom q) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg, hq]) hRg).symm,
    apply_hom_eq_of_isInverse hinv g hg hRg⟩

end Points

/-! ### Prime divisors matched across a common resolution -/

section Matching

open CategoryTheory.Limits

/-- A morphism which is a local isomorphism at `x` preserves the coheight of `x`. -/
private theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    Order.coheight x = Order.coheight (f x) := by
  have h1 : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
    (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1

/-- **Matching prime divisors across a common resolution.** Let `p : W ⟶ X` and `q : W ⟶ X'` be
proper birational morphisms of normal varieties and `ψ = q ∘ p⁻¹` a birational map with no
exceptional divisor. For a prime divisor `P` of `X`, its strict transform `E` on `W` lies over a
prime divisor `P'` of `X'` at which `q` is a local isomorphism at `η_E`, the coefficient of `P`
in `p_* D` is that of `E` in `D`, and the coefficient of `P'` in `ψ_* D` is that of `P` in `D`. -/
private theorem exists_primeDivisor_forall_transformDivisor_apply {k : Type u} [Field k]
    {X X' W : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hW : IsNormalVariety k sW)
    (p : W ⟶ X) (q : W ⟶ X') (hp : p ≫ sX = sW) [IsProper p] [IsProper q]
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    {ψ : X.RationalMap X'} (hψ : h.compHom q = ψ)
    (hψc : ∀ P : MMP.Mori.PrimeDivisor X, ¬ MMP.Mori.RationalMap.IsExceptional ψ P)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor W) (P' : MMP.Mori.PrimeDivisor X'),
      q E.genericPoint = P'.genericPoint ∧ IsIso (q.stalkMap E.genericPoint) ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W),
        RationalMap.transformDivisor p.toRationalMap D P = D E) ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        RationalMap.transformDivisor ψ D P' = D P := by
  have := hX.1
  have := hX'.1
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal sX'
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  obtain ⟨E, hEP, hisoE, htrE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX (f := p)
      (hp ▸ hW) hpb P
  obtain ⟨g, hg, hPg⟩ := exists_rep_mem_domain hinv P
  set w := g.hom ⟨P.genericPoint, hPg⟩ with hwdef
  have hw : p w = P.genericPoint := apply_hom_eq_of_isInverse hinv g hg hPg
  have hwE : w = E.genericPoint :=
    eq_of_apply_eq_of_coheight_le_one p hpbij (hEP.trans hw.symm)
      (hw ▸ P.coheight_genericPoint.le)
  -- `ψ` is represented at `η_P` by `q ∘ g`, which sends `η_P` to `q(w)`
  set g' : X.PartialMap X' := g.compHom q
  have hg' : g'.toRationalMap = ψ := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg, hψ]
  have hPg' : P.genericPoint ∈ g'.domain := hPg
  have hg'w : g'.hom ⟨P.genericPoint, hPg'⟩ = q w := rfl
  -- `q(w)` has coheight at most one since `ψ` does not contract `P`
  have hqw : Order.coheight (q w) ≤ 1 := by
    have hnex := hψc P
    rw [RationalMap.isExceptional_iff, not_imp] at hnex
    obtain ⟨-, h2⟩ := hnex
    have htr := MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hPg'
    rw [hg'w] at htr
    have hcl : RationalMap.transform ψ P.idealSheaf.support =
        ⟨((TopologicalSpace.IrreducibleCloseds.closureSingleton (q w) :
            TopologicalSpace.IrreducibleCloseds X') : Set X'),
          (TopologicalSpace.IrreducibleCloseds.closureSingleton (q w)).isClosed⟩ :=
      TopologicalSpace.Closeds.ext htr
    rw [hcl, closedsCodimension_coe, codimension_eq_coheight,
      show TopologicalSpace.IrreducibleCloseds.closureSingleton (q w) =
        (irreducibleSetEquivPoints (α := X')).symm (q w) from rfl,
      Order.coheight_orderIso] at h2
    exact ENat.lt_two_iff.mp (not_le.mp h2)
  have hisoq : IsIso (q.stalkMap w) := isIso_stalkMap_of_coheight_le_one q hqbij hqw
  have hco : Order.coheight (q w) = 1 := by
    rw [← coheight_eq_of_isIso_stalkMap q w, hwE]
    exact E.coheight_genericPoint
  set P' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (q w) hco
  have hP' : P'.genericPoint = q w :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hψP : MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some P' :=
    transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hPg' (hP'.trans hg'w.symm)
  refine ⟨E, P', hwE ▸ hP'.symm, hwE ▸ hisoq, htrE, fun D => ?_⟩
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hψP (fun Q hQ => ?_) D
  obtain ⟨w', hw'q, hw'p⟩ := exists_apply_eq_genericPoint hinv hψ hQ
  have hww : w = w' := eq_of_apply_eq_of_coheight_le_one q hqbij (hw'q.trans hP') hqw
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hw'p.symm.trans (hww ▸ hw))

end Matching

/-! ### Descent of a null Cartier divisor -/

/-- **Descent of a null divisor.** Let `p : W ⟶ X` be a projective birational morphism from a
normal variety onto a normal `ℚ`-factorial variety, and `G` a Cartier divisor on `W` of degree
zero on every curve contracted by `p`. Then `F = p_* G` is `ℚ`-Cartier and `G = p^* F`; so on a
curve `Γ` mapped onto a curve `C`, `deg_Γ G = [k(Γ) : k(C)] (F · C)`. -/
private theorem exists_degreeOn_eq_mul_intersectionNumber {k : Type u} [Field k]
    {X W : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (sX : X ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sW]
    (hX : IsNormalVariety k sX) (hW : IsNormalVariety k sW) (hQ : IsQFactorial sX)
    (p : W ⟶ X) (hp : p ≫ sX = sW) [IsProper p] (hpb : IsBirationalMorphism p)
    {G : Divisor W} (hG : G.IsCartier)
    (h0 : ∀ Γ : ProperCurve sW, Γ.IsContractedBy p → G.degreeOn k sW Γ.ι Γ.dim_le hG = 0) :
    ∃ hF : QDivisor.IsQCartier
        (RationalMap.transformDivisor p.toRationalMap (Divisor.toQDivisor G)),
      ∀ (Γ : ProperCurve sW) (C : ProperCurve sX), C.point = p Γ.point →
        (G.degreeOn k sW Γ.ι Γ.dim_le hG : ℚ) = residueFieldDegree p Γ.point *
          QDivisor.intersectionNumber k sX C.ι C.dim_le
            (RationalMap.transformDivisor p.toRationalMap (Divisor.toQDivisor G)) hF := by
  have := hX.1
  have := hW.1
  have : IsDominant p := hpb.isDominant
  set F : QDivisor X := RationalMap.transformDivisor p.toRationalMap (Divisor.toQDivisor G)
  have hF := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ F
  have hBF : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ F.supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant p]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have := QuasiCompact.compactSpace_of_compactSpace sW
  set P : QDivisor W := F.pullback hF hBF
  have hP : F.IsPullback p hBF P := QDivisor.isPullback_pullback hF hBF
  have hPq := hP.isQCartier hF
  have hGq : (Divisor.toQDivisor G).IsQCartier := QDivisor.isQCartier_toQDivisor hG
  have hEq : Divisor.toQDivisor G = P := by
    have hPn := isQCartier_neg hPq
    refine add_neg_eq_zero.mp (eq_zero_of_transformDivisor_eq_zero sX sW hX hW
      p hp hpb (hGq.add hPn) ?_ fun Γ hΓ => ?_)
    · rw [map_add, map_neg, MMP.Positivity.transformDivisor_of_isPullback hX
        (hp ▸ hW) hpb hF hBF hP]
      exact add_neg_cancel _
    · rw [QDivisor.intersectionNumber_add' k sW Γ.ι Γ.dim_le _ _ hGq hPn,
        intersectionNumber_neg sW Γ.ι Γ.dim_le hPq hPn,
        intersectionNumber_isPullback_eq_zero p hp hF hP Γ hΓ,
        QDivisor.intersectionNumber_toQDivisor k sW Γ.ι Γ.dim_le G hG hGq, h0 Γ hΓ]
      simp
  refine ⟨hF, fun Γ C hC => ?_⟩
  rw [← QDivisor.intersectionNumber_toQDivisor k sW Γ.ι Γ.dim_le G hG hGq,
    MMP.Fourfold.intersectionNumber_congr sW Γ.ι Γ.dim_le hGq hPq hEq,
    intersectionNumber_isPullback_eq_mul p hp hF hP Γ C hC]

/-! ### The main argument -/

/-- An equality `M = q • F` of `ℚ`-divisors is an equality of `ℝ`-divisors. -/
private theorem toRDivisor_eq_smul {X : Scheme.{u}} {M : Divisor X} {F : QDivisor X} {q : ℚ}
    (h : Divisor.toQDivisor M = q • F) :
    Divisor.toRDivisor M = (q : ℝ) • QDivisor.toRDivisor F := by
  rw [← QDivisor.toRDivisor_toQDivisor, h]
  ext P
  simp [DivisorWithCoeffs.coeff_smul]

/-- A real combination `∑ cᵢ Fᵢ` of `ℚ`-Cartier `ℚ`-divisors with `Fᵢ · C = 0` is numerically
trivial on `C`. -/
private theorem forall_eq_zero_of_eq_sum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) {D : RDivisor X} {s : ℕ} (c : Fin s → ℝ) (F : Fin s → QDivisor X)
    (hF : ∀ i, (F i).IsQCartier) (hD : D = ∑ i, c i • QDivisor.toRDivisor (F i))
    (h0 : ∀ i, (F i).intersectionNumber k sX C.ι C.dim_le (hF i) = 0) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sX D r L C x → x = 0 := by
  choose n hn M hM hMc using fun i => (hF i).exists_pos
  refine (forall_eq_zero_iff C (fun i => c i / n i) M hMc ?_).2
    (Finset.sum_eq_zero fun i _ => ?_)
  · rw [hD]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hn0 : (n i : ℝ) ≠ 0 := by exact_mod_cast (hn i).ne'
    rw [toRDivisor_eq_smul (q := (n i : ℚ))
        (by rw [hM i]; exact (Int.cast_smul_eq_zsmul ℚ _ _).symm),
      smul_smul, Rat.cast_natCast, div_mul_cancel₀ _ hn0]
  · have h := h0 i
    rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le (F i) (hF i) (hn i) (M i)
      (hMc i) (hM i), div_eq_zero_iff] at h
    have hn0 := (hn i).ne'
    simp_all

/-- **Distinct ordered levels are inequivalent.** Let `X`, `X'` be normal `ℚ`-factorial
projective threefolds over `S` and `ψ : X ⤏ X'` an isomorphism in codimension one over `S`, with
`K' = ψ_* K`, `B' = ψ_* B`, `H' = ψ_* H` for a canonical divisor `K` of `X`. If
`(X, B + t H)` and `(X', B' + t' H')` are klt pairs with `K + B + t H` and `K' + B' + t' H'` nef
over `S`, `t' < t`, `0 ≤ t'`, and a curve `C` of `X` over a point of `S` has
`(K + B + t H) · C = 0` and `H · C > 0`, then these nef models are not equivalent
(`MMP.Fourfold.IsNefModelEquivalent`) along `ψ`. -/
@[mmp "lem_fourfold_distinct_levels_inequivalent"]
public theorem not_isNefModelEquivalent_of_lt_of_isRIntersectionNumber_pos
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X X' S : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sX']
    (sS : S ⟶ Spec (.of k)) (π : X ⟶ S) (π' : X' ⟶ S)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hX' : MMP.Mori.IsProjectiveVariety k sX')
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    (hdim : topologicalKrullDim X = 3) (hdim' : topologicalKrullDim X' = 3)
    (hπ : π ≫ sS = sX) (hπ' : π' ≫ sS = sX')
    (ψ : X.RationalMap X') (hψ : MMP.Mori.RationalMap.IsIsomorphismInCodimOne ψ)
    (hψS : MMP.Flips.RationalMap.IsOver π π' ψ)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) {B H : RDivisor X}
    {K' : Divisor X'} {B' H' : RDivisor X'}
    (hK' : K' = MMP.Mori.RationalMap.transformDivisor ψ K)
    (hB' : B' = MMP.Mori.RationalMap.transformDivisor ψ B)
    (hH' : H' = MMP.Mori.RationalMap.transformDivisor ψ H)
    {t t' : ℝ} (htt' : t' < t) (ht' : 0 ≤ t')
    (heff : 0 ≤ B + t • H) (heff' : 0 ≤ B' + t' • H')
    (hklt : IsRealKltPair sX (B + t • H)) (hklt' : IsRealKltPair sX' (B' + t' • H'))
    (hnef : MMP.Flips.IsRelativelyNef k sX π (MMP.Flips.logCanonicalDivisor K (B + t • H)))
    (hnef' : MMP.Flips.IsRelativelyNef k sX' π' (MMP.Flips.logCanonicalDivisor K' (B' + t' • H')))
    (C : ProperCurve sX) (hC : C.IsContractedBy π)
    (hzero : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      MMP.Flips.IsRIntersectionNumber k sX (MMP.Flips.logCanonicalDivisor K (B + t • H)) r L C 0)
    (hpos : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sX H r L C x ∧ 0 < x) :
    ¬ IsNefModelEquivalent sX sX' sS π π' K (B + t • H) K' (B' + t' • H') ψ := by
  rintro ⟨hXn, -, -, -, -, hX'n, -, -, ⟨n', hK'c⟩, -, -, -, hres⟩
  obtain ⟨W, _, _, _, sW, _, p₁, p₂, h, hWv, -, hp₁s, hp₂s, hp₁, hp₂, hp₁b, hp₂b, hinv, hhψ,
    D₁, D₂, hD₁, hD₂, hzW⟩ := hres
  have : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁
  have : IsProper p₂ := isProper_of_isProjectiveMorphism p₂ hp₂
  have : IsDominant p₁ := hp₁b.isDominant
  have : IsDominant p₂ := hp₂b.isDominant
  have := hXn.1
  have := hX'n.1
  have := hWv
  have hWn : IsNormalVariety k sW := ⟨hWv, inferInstance⟩
  have := QuasiCompact.compactSpace_of_compactSpace sW
  have := QuasiCompact.compactSpace_of_compactSpace sX'
  -- the rational null decomposition of `K' + B' + t' H'`
  obtain ⟨s, Bs, r, m, E, hE, -, -, hr, -, hm, hdec, hEm, hnull⟩ :=
    exists_convexCombination_isKltPair_of_isRealKltPair sX' hX' hQ' K' hK'c (B' + t' • H')
      heff' hklt'
  set c : Fin s → ℝ := fun i => r i / m with hc
  have hA' : MMP.Flips.logCanonicalDivisor K' (B' + t' • H') =
      ∑ i, c i • Divisor.toRDivisor (E i) := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    refine hdec.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [toRDivisor_eq_smul (hEm i), map_add, QDivisor.toRDivisor_toQDivisor, smul_smul, hc,
      Rat.cast_natCast, div_mul_cancel₀ _ hm0]
  -- the pull-backs `q^* Eᵢ`
  have hB₂ : ∀ i, ∀ Z : irreducibleComponents W, p₂ (componentGenericPoint W Z) ∉ (E i).supp :=
    fun i Z => by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant p₂]
      exact MMP.Fourfold.genericPoint_notMem_supp _
  set G : Fin s → Divisor W := fun i => (E i).pullback (hE i) (hB₂ i)
  have hGp : ∀ i, (E i).IsPullback p₂ (hB₂ i) (G i) := fun i =>
    Divisor.isPullback_pullback (hE i) (hB₂ i)
  have hGc : ∀ i, (G i).IsCartier := fun i => (hGp i).isCartier (hE i)
  -- each `q^* Eᵢ` is null on every curve on which `q^*(K' + B' + t' H')` is null
  have hnull' : ∀ Γ' : ProperCurve sX',
      ∑ j, c j * ((E j).degreeOn k sX' Γ'.ι Γ'.dim_le (hE j) : ℝ) = 0 →
        ∀ i, (E i).degreeOn k sX' Γ'.ι Γ'.dim_le (hE i) = 0 := by
    intro Γ' hsum i
    refine hnull Γ' (∑ j, Finsupp.single ⟨E j, Divisor.mem_cartierSubgroup.mpr (hE j)⟩ (c j))
      ?_ ?_ i
    · rw [map_sum]
      simp only [CartierDivisorWithCoeffs.toDivisorWithCoeffs_single]
      exact hA'.symm
    · rw [← Finsupp.sum_finset_sum_index]
      · exact (Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_mul _)).trans hsum
      · exact fun _ => zero_mul _
      · exact fun _ _ _ => add_mul _ _ _
  have hG0 := degreeOn_isPullback_eq_zero_of_forall_eq_zero p₂ hp₂s hD₂ c hE hA' hnull' hGp
  -- descent: `q^* Eᵢ = p^* Fᵢ`, as `q^* Eᵢ` is null on the curves contracted by `p`
  choose hF hFdeg using fun i =>
    exists_degreeOn_eq_mul_intersectionNumber sX sW hXn hWn hQ p₁ hp₁s hp₁b (hGc i)
      fun Γ hΓ => hG0 i Γ <| (hzW Γ fun x hx => by simp only [Scheme.Hom.comp_apply, hΓ x hx]).1
        (forall_eq_zero_of_isRCartierPullback p₁ hp₁s hD₁ Γ hΓ)
  set F : Fin s → QDivisor X := fun i =>
    RationalMap.transformDivisor p₁.toRationalMap (Divisor.toQDivisor (G i))
  -- `∑ cᵢ Fᵢ = K + B + t' H`
  have hN : MMP.Flips.logCanonicalDivisor K (B + t' • H) =
      ∑ i, c i • QDivisor.toRDivisor (F i) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    obtain ⟨Ew, P', hp₂E, hiso, htr₁, htrψ⟩ :=
      exists_primeDivisor_forall_transformDivisor_apply hXn hX'n hWn p₁ p₂ hp₁s hp₁b hp₂b hinv
        hhψ hψ.2.1 P
    have hFP : ∀ i, (F i) P = ((E i).coeff P' : ℚ) := fun i => by
      change RationalMap.transformDivisor p₁.toRationalMap (Divisor.toQDivisor (G i)) P = _
      rw [htr₁ (Divisor.toQDivisor (G i))]
      change (((G i).coeff Ew : ℤ) : ℚ) = _
      rw [MMP.Positivity.coeff_eq_of_isPullback Ew P' hp₂E (hE i) (hGp i)]
    have hA'P : (Divisor.toRDivisor K' + (B' + t' • H')).coeff P' =
        (∑ i, c i • Divisor.toRDivisor (E i)).coeff P' := by
      rw [← hA']; rfl
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      Finsupp.add_apply, smul_eq_mul] at hA'P ⊢
    rw [show (Divisor.toRDivisor K') P' = (K'.coeff P' : ℝ) from rfl, hK', hB', hH',
      show ((RationalMap.transformDivisor ψ K).coeff P' : ℤ) = K.coeff P from htrψ K,
      htrψ B, htrψ H] at hA'P
    change ((K.coeff P : ℤ) : ℝ) + (B P + t' * H P) = _
    refine hA'P.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [show (QDivisor.toRDivisor (F i)) P = ((F i P : ℚ) : ℝ) from rfl, hFP i]
    push_cast
    rfl
  -- a lift `Γ` of `C` to `W`
  obtain ⟨Γ, hΓ⟩ := ProperCurve.exists_image_closure_eq_of_surjective hWv hX.toIsVariety p₁ hp₁s C
  have hp₁Γ := not_isContractedBy_of_image_closure_eq p₁ hΓ
  have hΓS : Γ.IsContractedBy (p₁ ≫ π) := isContractedBy_comp_of_image_closure_eq p₁ hΓ hC
  have hCΓ := point_eq_of_image_closure_eq p₁ hΓ
  obtain ⟨m₀, r₀, L₀, h₀⟩ := hzero
  -- `(q^*(K' + B' + t' H')) · Γ = 0`
  have hD₂Γ : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sW D₂ r L Γ x → x = 0 := by
    refine (hzW Γ hΓS).1 ((forall_eq_zero_iff_of_isRCartierPullback p₁ hp₁s hD₁ Γ hp₁Γ C
      hCΓ).2 fun _ _ _ _ hx =>
        (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h₀)
  -- `(K + B + t' H) · C = ∑ cᵢ (Fᵢ · C) = 0`, since `[k(Γ) : k(C)] (Fᵢ · C) = deg_Γ q^* Eᵢ = 0`
  have hNC := forall_eq_zero_of_eq_sum C c F hF hN fun i => by
    have h := hFdeg i Γ C hCΓ
    rw [hG0 i Γ hD₂Γ, Int.cast_zero, eq_comm, mul_eq_zero] at h
    exact h.resolve_left (by exact_mod_cast (residueFieldDegree_pos p₁ hp₁s Γ hp₁Γ).ne')
  -- but `(K + B + t' H) · C = (t' - t) (H · C) < 0`
  obtain ⟨m₁, r₁, L₁, x, h₁, hx⟩ := hpos
  have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ r₀ L₀ r₁ L₁ 0 x 1
    (t' - t) h₀ h₁
  have hND : (1 : ℝ) • MMP.Flips.logCanonicalDivisor K (B + t • H) + (t' - t) • H =
      MMP.Flips.logCanonicalDivisor K (B + t' • H) := by
    simp only [MMP.Flips.logCanonicalDivisor, one_smul, sub_smul]
    abel
  rw [hND] at hlin
  have := hNC _ _ _ _ hlin
  nlinarith

end MMP.Fourfold
