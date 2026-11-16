module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Curves.LineBundleDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochMeromorphic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# Kollár's degree of a line bundle on a projective curve is the Euler-characteristic degree

Let `k` be a field, `C` an integral projective curve over `k` and `L` an invertible sheaf on `C`.
Kollár's degree `deg_C L = ∑_p e_p(s)` of 1.20, computed with the local multiplicities of a
nonzero rational section `s ∈ L_η`, equals the degree `χ(C, L) - χ(C, 𝒪_C)`, so that

`χ(C, L) = deg_C L + χ(C, 𝒪_C)`.

At a closed point `p` the multiplicity `e_p(s)` is `ord_p(φ) · [κ(p) : k]`, where `s = φ σ` for
a generator `σ` of `L_p`; the sum of these is the degree of the divisor cycle `div(s)` of the
meromorphic section `s`, and the degree of `div(s)` is `χ(C, L) - χ(C, 𝒪_C)` by Riemann–Roch
in divisor form.

## Main results

* `MMP.Resolution.degree_eq_invertibleCurveDegree`: `deg_C L = χ(C, L) - χ(C, 𝒪_C)`.
* `MMP.Resolution.eulerCharacteristic_eq_degree_add`: `χ(C, L) = deg_C L + χ(C, 𝒪_C)`.

## Implementation notes

The degree on the right is `AlgebraicGeometry.invertibleCurveDegree`, and the comparison goes
through the divisor form of Riemann–Roch,
`AlgebraicGeometry.curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve`: the
degree of the zero cycle `div(s)` is the sum over the points of `C` of its coefficients weighted
by their residue degrees, and the coefficient at a closed point is the order of vanishing of a
coordinate of `s` there, which is the coordinate whose multiplicity `e_p` Kollár's degree sums.
Both constructions read `s` in the generic stalk `L_η` and trivialize `L` by a basis of the
stalk `L_p`, so no comparison of rational sections is needed.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AZ2](https://stacks.math.columbia.edu/tag/0AZ2)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Order Stacks.Chow Stacks.Divisors

namespace MMP.Resolution

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (L : C.Modules)

/-- An invertible sheaf on an integral scheme has a nonzero rational section. -/
theorem exists_genericStalk_ne_zero [IsIntegral C] [Stacks.Ample.IsInvertibleModule C L] :
    ∃ s : L.presheaf.stalk (genericPoint C), s ≠ 0 := by
  have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L := ‹_›
  have := Stacks.Divisors.isInvertible_presheaf L
  obtain ⟨W, hW, t, ht⟩ := isTrivializedNear_of_isInvertible L (genericPoint C)
  refine ⟨L.presheaf.germ W _ hW t, fun h => ?_⟩
  have hb := (ht _ hW).injective
  have : (1 : C.presheaf.stalk (genericPoint C)) = 0 :=
    hb (show (1 : C.presheaf.stalk (genericPoint C)) • L.presheaf.germ W _ hW t =
      (0 : C.presheaf.stalk (genericPoint C)) • L.presheaf.germ W _ hW t by
        rw [h, smul_zero, smul_zero])
  exact one_ne_zero this

variable {L} in
/-- A basis of the stalk `L_p` generates it. -/
theorem isStalkGenerator_of_isStalkBasis {p : C} {m : L.presheaf.stalk p}
    (hm : IsStalkBasis L p m) : IsStalkGenerator L p m := by
  let := stalkModule L p
  exact (Submodule.span_singleton_eq_top_iff _ _).2 hm.surjective

open Classical in
/-- The term at `x` of the degree of the divisor cycle of `s` is Kollár's multiplicity `e_x(s)`
at a closed point and `0` at the generic point. -/
private theorem coeff_mul_eq_sectionMult [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] [IsLocallyNoetherian C]
    [Stacks.Ample.IsInvertibleModule C L] (s : L.presheaf.stalk (genericPoint C)) (hs : s ≠ 0)
    (x : C) :
    have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L := ‹_›
    ((meromorphicDivisorCycle (fieldChowSituation k) sC
        (schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one k sC
          (IsCurve.topologicalKrullDim_eq_one sC))
        (fun x ↦
          have := Stacks.Divisors.isInvertible_presheaf L
          isTrivializedNear_of_isInvertible L x) s).val :
          CycleGroup (fieldChowSituation k) sC 0).1 x *
      (if relativeDimension (fieldChowSituation k).dimensionFunction sC x =
          relativeDimension (fieldChowSituation k).dimensionFunction
            (𝟙 (fieldChowSituation k).S) (sC.base x)
        then (sC.residueDegree x : ℤ) else 0) =
      if IsClosed ({x} : Set C) then sectionMult sC L s x else 0 := by
  intro hinv
  have hdim1 : topologicalKrullDim C = 1 := IsCurve.topologicalKrullDim_eq_one sC
  have hproj : IsProjectiveMorphism sC := IsProjectiveVariety.isProjective (k := k)
  have hC : Stacks.HProjective.IsQuasiProjective sC :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective sC).mp hproj.isQuasiProjective
  set α := ((meromorphicDivisorCycle (fieldChowSituation k) sC
        (schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one k sC
          (IsCurve.topologicalKrullDim_eq_one sC))
        (fun x ↦
          have := Stacks.Divisors.isInvertible_presheaf L
          isTrivializedNear_of_isInvertible L x) s).val :
          CycleGroup (fieldChowSituation k) sC 0) with hα
  by_cases hx : x = genericPoint C
  · subst hx
    have hnc : ¬ IsClosed ({genericPoint C} : Set C) := fun h =>
      ne_genericPoint_of_isClosed_of_dim_eq_one hdim1 h rfl
    simp only [hnc, ↓reduceIte]
    have h0 : α.1 (genericPoint C) = 0 := by
      refine meromorphicDivisorCycle_eq_zero _ _ _ _ _ _ fun Z hZ => ?_
      have h1 := Z.coheight_genericPoint
      rw [hZ] at h1
      have : IsMax (genericPoint C) := fun b _ => genericPoint_specializes b
      rw [Order.coheight_eq_zero.2 this] at h1
      exact zero_ne_one h1
    rw [h0, zero_mul]
  · have hcl : IsClosed ({x} : Set C) :=
      Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C hdim1 hx
    simp only [hcl, ↓reduceIte]
    have hco : coheight x = 1 := IsCurve.coheight_eq_one sC hx
    have hTx : IsTrivializedNear L x := by
      have := Stacks.Divisors.isInvertible_presheaf L
      exact isTrivializedNear_of_isInvertible L x
    obtain ⟨a, m, hm, hsa⟩ := exists_isCoordinateAt hTx s
    have ha0 : a ≠ 0 := IsCoordinateAt.ne_zero ⟨m, hm, hsa⟩ hs
    have hαx : α.1 x = C.ord a x := by
      have h1 := meromorphicDivisorCycle_genericPoint (fieldChowSituation k) sC
        (schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one k sC
          (IsCurve.topologicalKrullDim_eq_one sC))
        (fun x ↦
          have := Stacks.Divisors.isInvertible_presheaf L
          isTrivializedNear_of_isInvertible L x) s
        (Stacks.Divisors.PrimeDivisor.ofCoheightOne x hco)
      rw [Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne] at h1
      rw [hα, h1]
      have h2 := orderOfVanishing_eq (L := L) (s := s)
        (Z := Stacks.Divisors.PrimeDivisor.ofCoheightOne x hco)
        (a := a) (by rw [Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne]; exact hTx)
        (by rw [Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne]; exact ⟨m, hm, hsa⟩)
      rw [h2, Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne]
    have hsm : sectionMult sC L s x = C.ord a x * (sC.residueDegree x : ℤ) := by
      rw [← eMultAt_eq_sectionMult sC L s m (isStalkGenerator_of_isStalkBasis hm) a ha0 hsa,
        eMultAt_singleton_eq sC hC hcl ha0]
    rw [hsm, hαx]
    by_cases hord : C.ord a x = 0
    · rw [hord, zero_mul, zero_mul]
    · have hrel : relativeDimension (fieldChowSituation k).dimensionFunction sC x = 0 :=
        (mem_cyclesOfDimension_iff_forall_point _ _ _ _).1 α.2 x (by rw [hαx]; exact hord)
      have hrel' : relativeDimension (fieldChowSituation k).dimensionFunction
          (𝟙 (fieldChowSituation k).S) (sC.base x) = 0 := by
        rw [relativeDimension_id]
        rfl
      simp only [hrel.trans hrel'.symm, ↓reduceIte]

/-- **Kollár's degree is the Euler-characteristic degree.** For an invertible sheaf `L` on an
integral projective curve `C` over `k`, Kollár's degree `deg_C L` of 1.20 is
`χ(C, L) - χ(C, 𝒪_C)`. -/
theorem degree_eq_invertibleCurveDegree [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] [Stacks.Ample.IsInvertibleModule C L]
    (hdim : topologicalKrullDim C ≤ 1) :
    degree sC L = invertibleCurveDegree k sC hdim L := by
  classical
  have : IsIntegral C := ‹MMP.Mori.IsCurve k sC›.toIsIntegral
  have : LocallyOfFiniteType sC := ‹MMP.Mori.IsCurve k sC›.toLocallyOfFiniteType
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L := ‹_›
  obtain ⟨s, hs⟩ := exists_genericStalk_ne_zero L
  have hdeg : degree sC L = degreeWRT sC L s := by
    have h : ∃ s : L.presheaf.stalk (genericPoint C), s ≠ 0 := ⟨s, hs⟩
    rw [degree, dite_eq_left h]
    exact degreeWRT_eq sC L h.choose_spec hs
  rw [hdeg, invertibleCurveDegree_eq_curveDegree_one,
    curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve k sC hdim L s hs]
  erw [cycleDegree_apply, properPushforward_apply]
  have hfiber : sC.base ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  erw [hfiber, finsum_mem_univ]
  simp_rw [coeff_mul_eq_sectionMult sC L s hs]
  have hfin := finite_sectionMult_ne_zero sC L s hs
  rw [degreeWRT, dite_eq_left_of_eq_true (eq_true hfin),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by
    intro x hx
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    simpa using hx)]
  refine Finset.sum_congr rfl fun x hx => ?_
  simp only [((Set.Finite.mem_toFinset _).1 hx).1, ↓reduceIte]

/-- **`χ(C, L) = deg_C L + χ(C, 𝒪_C)`.** For an invertible sheaf `L` on an integral projective
curve `C` over `k`, `χ(C, L) = deg_C L + χ(C, 𝒪_C)`, where `deg_C L` is Kollár's degree of
1.20. Both coherence hypotheses always hold
here (`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank` and
`Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`); they are what
`AlgebraicGeometry.eulerCharacteristic` takes. -/
@[mmp "lem_mmp_threefold_curve_degree_euler"]
theorem eulerCharacteristic_eq_degree_add [MMP.Mori.IsCurve k sC]
    [MMP.Mori.IsProjectiveVariety k sC] [Stacks.Ample.IsInvertibleModule C L] [L.IsCoherent]
    [(SheafOfModules.unit C.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k sC L =
      degree sC L + eulerCharacteristic k sC (SheafOfModules.unit C.ringCatSheaf) := by
  have hdim : topologicalKrullDim C ≤ 1 := (IsCurve.topologicalKrullDim_eq_one sC).le
  rw [degree_eq_invertibleCurveDegree sC L hdim, invertibleCurveDegree_eq_eulerCharacteristic_sub]
  ring

end MMP.Resolution
