module

import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaAffineBase
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Morphisms.IntegralModification
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective

/-!
# Finite dimensionality of `N₁(X)` for proper varieties

Let `k` be an algebraically closed field of characteristic zero and `X` a proper variety over
`k`. The real vector space `N₁(X)` of numerical classes of real 1-cycles on `X`
(`MMP.Mori.NumericalCurveClasses`) is finite dimensional. Only numerical equivalence is
involved: no statement about the Néron–Severi group or algebraic equivalence is made.

By Chow's lemma there are a projective variety `Y` and a proper surjective morphism
`π : Y ⟶ X`: take a Chow modification of `X` and the reduced closure of the inverse image of its
dense isomorphism open. The push-forward `π_* : N₁(Y) ⟶ N₁(X)` is surjective: every proper curve
`C ⊆ X` is the image of a proper curve `C' ⊆ Y`, and `π_*[C'] = [k(C') : k(C)] · [C]` with a
positive degree. Since `N₁(Y)` is finite dimensional, so is `N₁(X)`.

## Main results

* `MMP.Mori.NumericalCurveClasses.finiteDimensional_of_isProperVariety`: `N₁(X)` is finite
  dimensional over `ℝ` for a proper variety `X` over an algebraically closed field of
  characteristic zero.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Chapter 1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Mori

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Chow's lemma for a proper variety.** A proper variety `X` over `k` is the image of a
projective variety under a proper surjective morphism. -/
private theorem exists_isProjectiveVariety_surjective {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProperVariety k sX] :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ X), MMP.Mori.IsProjectiveVariety k (π ≫ sX) ∧ IsProper π ∧
      Surjective π := by
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  obtain ⟨n, Y₀, π₀, i, U, hπ, -, hi, hcomm, hU, hiso⟩ :=
    AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_isAffine sX
  have : IsProper π₀ := hπ
  have : IsImmersion i := hi
  obtain ⟨Y, j, hj, hY, hsurj⟩ :=
    MMP.exists_isIntegral_closedImmersion_surjective π₀ U hU
  have : IsClosedImmersion j := hj
  refine ⟨Y, j ≫ π₀, ?_, inferInstance, hsurj⟩
  exact { toIsVariety := { toIsIntegral := hY }
          isProjective := isProjectiveMorphism_of_isImmersion_projectiveSpaceOver (j ≫ i)
            (by rw [Category.assoc, ← hcomm, Category.assoc]) }

/-- A nonempty space with at most one point has dimension zero. -/
private theorem topologicalKrullDim_eq_zero_of_subsingleton (T : Type*) [TopologicalSpace T]
    [Nonempty T] [Subsingleton T] : topologicalKrullDim T = 0 := by
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology T) ?_
  obtain ⟨x⟩ := ‹Nonempty T›
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- The closure of the point of a proper curve, being one-dimensional, is not a single point. -/
private theorem ProperCurve.closure_point_ne_singleton {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (x : X) : closure {C.point} ≠ ({x} : Set X) := by
  intro h
  have h1 : topologicalKrullDim (closure {C.point} : Set X) = 1 := by
    rw [← C.range_ι, ← C.dim_eq]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
  rw [h, topologicalKrullDim_eq_zero_of_subsingleton] at h1
  exact zero_ne_one h1

/-! ### The degree of a proper curve over its image -/

section CurveImage

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {f : X ⟶ Y} [IsSeparated sY] [LocallyOfFiniteType sY]
  (hf : f ≫ sY = sX)

include hf

/-- A proper curve `C ⊆ X` is proper over `k` through `f`. -/
private theorem isProper_properCurve_ι_comp_comp (C : ProperCurve sX) :
    IsProper ((C.ι ≫ f) ≫ sY) := by
  rw [Category.assoc, hf]
  infer_instance

/-- A proper curve `C ⊆ X`, with the `k`-structure through `f`, is a curve over `k`. -/
private theorem isCurve_properCurve_ι_comp (C : ProperCurve sX) :
    MMP.Mori.IsCurve k ((C.ι ≫ f) ≫ sY) := by
  rw [Category.assoc, hf]
  exact C.isCurve

/-- The residue degree of `f` at the generic point of a proper curve `C ⊆ X` is the degree of `C`
over its image `f(C)`. -/
private theorem residueFieldDegree_eq_degreeOver_toImage (C : ProperCurve sX)
    [IsProper (C.ι ≫ f)] :
    residueFieldDegree f C.point = degreeOver (C.ι ≫ f).toImage := by
  have := isProper_properCurve_ι_comp_comp hf C
  have := isCurve_properCurve_ι_comp hf C
  have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
  rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι,
    mul_one] at h1
  have h2 := residueDegree_comp (C.ι ≫ f).toImage (C.ι ≫ f).imageι (genericPoint C.scheme)
  rw [Scheme.Hom.toImage_imageι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (C.ι ≫ f).imageι, one_mul,
    residueDegree_genericPoint_eq_degreeOver (C.ι ≫ f).toImage] at h2
  exact h1.symm.trans h2

/-- A `k`-morphism to a separated `k`-scheme which is non-constant on a proper curve `C` has
positive residue degree at the generic point of `C`. -/
private theorem residueFieldDegree_pos_of_not_constant (C : ProperCurve sX)
    (hnc : ¬ ∃ y : Y, Set.range (C.ι ≫ f) = {y}) : 0 < residueFieldDegree f C.point := by
  have := isProper_properCurve_ι_comp_comp hf C
  have := IsProper.of_comp (C.ι ≫ f) sY
  have := isCurve_properCurve_ι_comp hf C
  letI := (functionFieldMap (C.ι ≫ f).toImage).toAlgebra
  have : Module.Finite (C.ι ≫ f).image.functionField C.scheme.functionField :=
    finite_functionField_image sY (C.ι ≫ f) hnc
  rw [residueFieldDegree_eq_degreeOver_toImage hf C, degreeOver_eq_finrank _
    (congrArg CommRingCat.Hom.hom (stalkMap_cast_target (C.ι ≫ f).toImage
      (genericPoint C.scheme) (map_genericPoint_of_isDominant _))).symm]
  exact Module.finrank_pos

end CurveImage

/-! ### Lifting proper curves along a proper surjective morphism -/

/-- The reduced closure of a point is homeomorphic to the closure as a subspace, so the two
have the same dimension. -/
private theorem topologicalKrullDim_curveSubschemeAt {X : Scheme.{0}} (x : X) :
    topologicalKrullDim (curveSubschemeAt x) = topologicalKrullDim (closure ({x} : Set X)) := by
  have hmem (t) : curveSubschemeAtι x t ∈ closure ({x} : Set X) :=
    range_curveSubschemeAtι x ▸ ⟨t, rfl⟩
  refine IsHomeomorph.topologicalKrullDim_eq (Set.codRestrict _ _ hmem) <|
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨(curveSubschemeAtι x).isClosedEmbedding.isEmbedding.codRestrict _ hmem, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨t, rfl⟩ := (range_curveSubschemeAtι x).symm ▸ hy
  exact ⟨t, rfl⟩

/-- The image of `{v}⁻` under any morphism `u` has closure `{u v}⁻`. -/
private theorem closure_range_curveSubschemeAtι_comp {V W : Scheme.{0}} (u : V ⟶ W) (v : V) :
    closure (Set.range (curveSubschemeAtι v ≫ u)) = closure {u v} := by
  have : Set.range (curveSubschemeAtι v ≫ u) = u '' Set.range (curveSubschemeAtι v) := by
    rw [← Set.range_comp]; rfl
  rw [this, range_curveSubschemeAtι, closure_image_closure u.continuous, Set.image_singleton]

/-- Over every point `η` of the image of a quasi-compact morphism `u` there is a point `v` with
`u v = η` that is closed in its fibre. -/
private theorem exists_apply_eq_and_closed_in_fiber_of_mem_range {V W : Scheme.{0}} (u : V ⟶ W)
    [QuasiCompact u] {η : W} (hη : η ∈ Set.range u) :
    ∃ v, u v = η ∧ ∀ w, v ⤳ w → u w = u v → w = v := by
  have : CompactSpace (u ⁻¹' {η}) := (u.fiberHomeo η).compactSpace
  obtain ⟨x, hx⟩ := hη
  obtain ⟨p, -, hp⟩ := IsClosed.exists_closed_singleton (X := u ⁻¹' {η}) isClosed_univ
    ⟨⟨x, hx⟩, trivial⟩
  refine ⟨p.1, p.2, fun w hvw hw => congrArg Subtype.val
    (?_ : (⟨w, hw.trans p.2⟩ : u ⁻¹' {η}) = p)⟩
  have := specializes_iff_mem_closure.mp
    (Topology.IsInducing.subtypeVal.specializes_iff.mp hvw : p ⤳ ⟨w, hw.trans p.2⟩)
  rwa [hp.closure_eq] at this

/-- For `u : V ⟶ W` over `k` (both locally of finite type) and `v ∈ V` closed in its fibre,
`{v}⁻` and `{u v}⁻` have the same dimension. -/
private theorem topologicalKrullDim_curveSubschemeAt_eq (k : Type) [Field k]
    {V W : Scheme.{0}} (u : V ⟶ W) {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    (hu : u ≫ sW = sV) [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] {v : V}
    (hv : ∀ w, v ⤳ w → u w = u v → w = v) :
    topologicalKrullDim (curveSubschemeAt v) = topologicalKrullDim (curveSubschemeAt (u v)) := by
  set ι := curveSubschemeAtι v
  have : IsIntegral (curveSubschemeAt v) :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure v
  have hgen : ι (genericPoint _) = v :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure v
  rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range (ι ≫ u) k (ι ≫ sV) sW
    (by rw [Category.assoc, hu]), closure_range_curveSubschemeAtι_comp,
    topologicalKrullDim_curveSubschemeAt]
  have hfib : (ι ≫ u) ⁻¹' {(ι ≫ u) (genericPoint _)} ⊆ {genericPoint _} := fun c hc =>
    ι.isClosedEmbedding.injective <| (hv _
      (by have := (genericPoint_specializes c).map ι.continuous; rwa [hgen] at this)
      ((hc : u (ι c) = u (ι (genericPoint _))).trans (congrArg u hgen))).trans hgen.symm
  have e := (ι ≫ u).fiberHomeo ((ι ≫ u) (genericPoint _))
  have := (Set.subsingleton_singleton.anti hfib).coe_sort
  have : Subsingleton ((ι ≫ u).fiber ((ι ≫ u) (genericPoint _))) := e.injective.subsingleton
  have : Nonempty ((ι ≫ u).fiber ((ι ≫ u) (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  rw [topologicalKrullDim_eq_zero_of_subsingleton, zero_add]

/-- For `u : V ⟶ W` proper over `S` and `v ∈ V`, if `{u v}⁻` is proper over `S` then so is
`{v}⁻`. -/
private theorem isProper_curveSubschemeAtι_comp {S V W : Scheme.{0}} (u : V ⟶ W) {sV : V ⟶ S}
    {sW : W ⟶ S} (hu : u ≫ sW = sV) [IsProper u] (v : V)
    [IsProper (curveSubschemeAtι (u v) ≫ sW)] : IsProper (curveSubschemeAtι v ≫ sV) := by
  set φ := curveSubschemeAtι v ≫ u
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {u v}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (Closeds.ext (by
      rw [Closeds.coe_closure, Closeds.coe_closure, closure_range_curveSubschemeAtι_comp]))
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  have : IsProper (φ.imageι ≫ sW) := by
    change IsProper (φ.ker.subschemeι ≫ sW)
    rwa [hker]
  rw [← hu, ← Category.assoc]
  change IsProper (φ ≫ sW)
  rw [← φ.toImage_imageι, Category.assoc]
  infer_instance

/-- A proper surjective morphism of `k`-schemes locally of finite type lifts every proper curve
`C ⊆ W` to a proper curve `C' ⊆ V` whose generic point maps to that of `C`. -/
private theorem ProperCurve.exists_point_eq_of_surjective {k : Type} [Field k]
    {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] (u : V ⟶ W) (hu : u ≫ sW = sV)
    [IsProper u] [Surjective u] (C : ProperCurve sW) :
    ∃ C' : ProperCurve sV, u C'.point = C.point := by
  obtain ⟨η, hη⟩ := C
  obtain ⟨v, rfl, hv⟩ := exists_apply_eq_and_closed_in_fiber_of_mem_range u (u.surjective η)
  have := hη.isProper
  exact ⟨⟨v, (topologicalKrullDim_curveSubschemeAt_eq k u hu hv).trans hη.dim_eq,
    isProper_curveSubschemeAtι_comp u hu v⟩, rfl⟩

/-- Push-forward of real 1-cycles along a proper surjective morphism of `k`-schemes, locally of
finite type with separated target, is surjective: a proper curve `C ⊆ W` lifts to a proper curve
`C' ⊆ V`, and `u_*[C'] = [k(C') : k(C)] · [C]` with a positive degree. -/
private theorem OneCycle.pushforward_surjective {k : Type} [Field k] {V W : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sV] [IsSeparated sW]
    [LocallyOfFiniteType sW] (u : V ⟶ W) (hu : u ≫ sW = sV) [IsProper u] [Surjective u] :
    Function.Surjective (OneCycle.pushforward ℝ sV sW u) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro Z -
  induction Z using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | single C r =>
    obtain ⟨C', hpt⟩ := ProperCurve.exists_point_eq_of_surjective u hu C
    have hpos := residueFieldDegree_pos_of_not_constant hu C' fun ⟨t, ht⟩ =>
      C.closure_point_ne_singleton t
        (by rw [← hpt, ← C'.range_comp u hu]; exact ht)
    have hprop : IsProperCurve sW (u C'.point) := hpt ▸ C.isProperCurve
    have hC : (⟨u C'.point, hprop⟩ : ProperCurve sW) = C := ProperCurve.ext hpt
    refine LinearMap.mem_range.mpr ⟨Finsupp.single C' (r / residueFieldDegree u C'.point), ?_⟩
    rw [OneCycle.pushforward, Finsupp.linearCombination_single, cyclePushforwardOfPoint,
      dif_pos hprop, hC, Finsupp.smul_single, smul_eq_mul,
      div_mul_cancel₀ _ (by exact_mod_cast hpos.ne')]

end Helpers

/-- For a proper variety `X` over an algebraically closed field `k` of characteristic zero, the
real vector space `N₁(X)` of numerical classes of curves is finite dimensional. -/
@[mmp "lem_mmp_foundation_proper_n1_finite_alg_closed_char_zero"]
theorem NumericalCurveClasses.finiteDimensional_of_isProperVariety
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    FiniteDimensional ℝ (NumericalCurveClasses sX) := by
  obtain ⟨Y, π, hY, hπ, hsurj⟩ := exists_isProjectiveVariety_surjective sX
  have := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety (π ≫ sX)
  have : LocallyOfFiniteType (π ≫ sX) := hY.toLocallyOfFiniteType
  refine Module.Finite.of_surjective (NumericalCurveClasses.pushforward π rfl) fun z => ?_
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.pushforward_surjective (sV := π ≫ sX) π rfl Z
  exact ⟨OneCycle.numericalClass (π ≫ sX) Z', rfl⟩

end MMP.Mori
