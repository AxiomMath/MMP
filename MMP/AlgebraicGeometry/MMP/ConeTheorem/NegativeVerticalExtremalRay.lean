module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.MMP.ConeTheorem.BoundedCurveClasses

/-!
# A negative vertical extremal ray

Let `h : X ⟶ S` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, and let `D` be an `ℝ`-Cartier divisor on `X` which is not nef over `S`. Then
the closed cone of curves `NE̅(X)` has an extremal ray `R` on which `D` is negative (`(z · D) < 0`
for every nonzero `z ∈ R`) and which is vertical: every curve `C ⊆ X` with `[C] ∈ R` is contracted
by `h`. No singularity hypothesis is needed, and the ray is not claimed to be spanned by the class
of a curve.

The argument is by convexity. For ample `A` on `X` and `H` on `S`, the nef class `h^* H` cuts out
the extremal face `F = NE̅(X) ∩ (h^* H)^⊥`, on which `D` takes a negative value; the slice
`F ∩ {A = 1}` is compact, the minimisers of `D` on it form a nonempty compact face, and an extreme
point of that face spans an extremal ray of `F`, hence of `NE̅(X)`. A curve with class on this ray
has `(h^* H · C) = 0`, so by the projection formula `h(C)` is a point.

## Main results

* `MMP.Mori.exists_isExtremalRay_neg_contractedBy_of_not_isRelativelyNef`: the ray exists.

## Implementation notes

The divisor is an `ℝ`-Cartier divisor; the source's rational Cartier divisor is the case of
rational coefficients. Taking `S = Spec k` recovers a `D`-negative extremal ray of `NE̅(X)` for
every non-nef `D`.

The extreme point is produced by the Krein–Milman theorem
(`IsCompact.extremePoints_nonempty`) for the numerical topology on `N₁(X)`, which is a Hausdorff
locally convex topology: it is the initial topology of the degree forms, which separate points.
The source instead lowers the affine dimension of the face of minimisers one step at a time;
both arguments give an extreme point of a nonempty compact face.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.18, 3.27
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

section Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### An extremal ray from a compact slice -/

section Convex

/-- Rescaling a nonzero point `z` of `N` with `a z > 0` and `ℓ z = 0` lands in the slice
`{a = 1, ℓ = 0}` of `N`. -/
private theorem inv_smul_mem_slice {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} {a ℓ : V →ₗ[ℝ] ℝ} {z : V} (hz : z ∈ N) (ha : 0 < a z) (hℓ : ℓ z = 0) :
    (a z)⁻¹ • z ∈ {z | z ∈ N ∧ a z = 1 ∧ ℓ z = 0} :=
  ⟨N.smul_mem (inv_nonneg.2 ha.le) hz, by simp [ha.ne'], by simp [hℓ]⟩

/-- Let `v` be an extreme point of the set of minimisers of `d` on the slice
`{z ∈ N | a z = 1, ℓ z = 0}` of a cone `N` on which `a > 0` off `0` and `ℓ ≥ 0`. If `u + w = c v`
with `u, w ∈ N` and `c ≥ 0`, then `u` lies on the ray `ℝ_{≥0} v`. -/
private theorem mem_ray_of_add_eq_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} {a ℓ d : V →ₗ[ℝ] ℝ} {m : ℝ}
    (hapos : ∀ z ∈ N, z ≠ 0 → 0 < a z) (hℓ : ∀ z ∈ N, 0 ≤ ℓ z)
    (hm : ∀ z ∈ {z | z ∈ N ∧ a z = 1 ∧ ℓ z = 0}, m ≤ d z) {v : V}
    (hv : v ∈ ({z | z ∈ N ∧ a z = 1 ∧ ℓ z = 0} ∩ {z | d z = m}).extremePoints ℝ) {u w : V}
    (hu : u ∈ N) (hw : w ∈ N) {c : ℝ} (hc : 0 ≤ c) (huw : u + w = c • v) :
    ∃ c' : ℝ, 0 ≤ c' ∧ c' • v = u := by
  obtain ⟨⟨⟨-, hav, hℓv⟩, hdv : d v = m⟩, hext⟩ := hv
  rcases eq_or_ne u 0 with rfl | hu0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨c, hc, by simpa using huw.symm⟩
  have hα := hapos u hu hu0
  have hβ := hapos w hw hw0
  have hℓsum : ℓ u + ℓ w = 0 := by simpa [hℓv] using congrArg ℓ huw
  have hasum : a u + a w = c := by simpa [hav] using congrArg a huw
  have hdsum : d u + d w = (a u + a w) * m := by simpa [hdv, hasum] using congrArg d huw
  have hu' := inv_smul_mem_slice (ℓ := ℓ) hu hα (by linarith [hℓ u hu, hℓ w hw])
  have hw' := inv_smul_mem_slice (ℓ := ℓ) hw hβ (by linarith [hℓ u hu, hℓ w hw])
  have hdu := hm _ hu'
  have hdw := hm _ hw'
  rw [map_smul, smul_eq_mul, le_inv_mul_iff₀ hα] at hdu
  rw [map_smul, smul_eq_mul, le_inv_mul_iff₀ hβ] at hdw
  have hcpos : 0 < a u + a w := by linarith
  have heq := hext ⟨hu', show d _ = m by
      rw [map_smul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hα.ne']
      linarith⟩
    ⟨hw', show d _ = m by
      rw [map_smul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hβ.ne']
      linarith⟩
    ⟨a u / (a u + a w), a w / (a u + a w), by positivity, by positivity, by field_simp, by
      rw [← inv_smul_smul₀ hcpos.ne' v, hasum, ← huw]
      match_scalars <;> field_simp⟩
  exact ⟨a u, hα.le, by rw [← heq, smul_inv_smul₀ hα.ne']⟩

/-- Let `N` be a cone in a Hausdorff locally convex space, `a`, `ℓ`, `d` continuous linear forms
with `a > 0` on `N \ {0}`, `ℓ ≥ 0` on `N` and the slice `N ∩ {a ≤ 1}` compact. If `d` is negative
somewhere on `N ∩ {ℓ = 0}`, then `N` has an extremal ray on which `ℓ` vanishes and `d` is negative
off `0`. -/
private theorem exists_isExtremalRay_of_isCompact {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] (N : PointedCone ℝ V) (a ℓ d : V →ₗ[ℝ] ℝ) (ha : Continuous a)
    (hℓc : Continuous ℓ) (hd : Continuous d)
    (hcpt : IsCompact ((N : Set V) ∩ {z | a z ≤ 1}))
    (hapos : ∀ z ∈ N, z ≠ 0 → 0 < a z) (hℓ : ∀ z ∈ N, 0 ≤ ℓ z)
    (hz₀ : ∃ z ∈ N, ℓ z = 0 ∧ d z < 0) :
    ∃ R : Set V, IsExtremalRay ℝ (N : Set V) R ∧ (∀ z ∈ R, z ≠ 0 → d z < 0) ∧
      ∀ z ∈ R, ℓ z = 0 := by
  obtain ⟨z₀, hz₀N, hℓz₀, hdz₀⟩ := hz₀
  have haz₀ := hapos z₀ hz₀N (by rintro rfl; simp at hdz₀)
  set K₀ : Set V := {z | z ∈ N ∧ a z = 1 ∧ ℓ z = 0}
  have hK₀ : K₀ = ((N : Set V) ∩ {z | a z ≤ 1}) ∩ ({z | a z = 1} ∩ {z | ℓ z = 0}) := by
    ext z
    simp only [K₀, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2.le⟩, h2, h3⟩, fun ⟨⟨h1, _⟩, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hK₀c : IsCompact K₀ := hK₀ ▸ hcpt.inter_right
    ((isClosed_eq ha continuous_const).inter (isClosed_eq hℓc continuous_const))
  have hy₀ := inv_smul_mem_slice hz₀N haz₀ hℓz₀
  obtain ⟨x, hxK, hxmin⟩ := hK₀c.exists_isMinOn ⟨_, hy₀⟩ hd.continuousOn
  have hm : d x < 0 := (hxmin hy₀).trans_lt <| by
    simpa using mul_neg_of_pos_of_neg (inv_pos.mpr haz₀) hdz₀
  obtain ⟨v, hv⟩ := (hK₀c.inter_right (isClosed_eq hd continuous_const)).extremePoints_nonempty
    ⟨x, hxK, rfl⟩
  obtain ⟨⟨⟨hvN, hav, hℓv⟩, hdv : d v = d x⟩, -⟩ := id hv
  refine ⟨{w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}, ⟨⟨?_, ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩, ?_, ?_⟩,
    v, by rintro rfl; simp at hav, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact N.smul_mem hc hvN
  · rintro _ ⟨c, hc, rfl⟩ c' hc'
    exact ⟨c' * c, mul_nonneg hc'.le hc, by rw [smul_smul]⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact ⟨c + c', add_nonneg hc hc', add_smul _ _ _⟩
  · rintro u hu w hw ⟨c, hc, huw⟩
    exact ⟨mem_ray_of_add_eq_smul hapos hℓ hxmin hv hu hw hc huw.symm,
      mem_ray_of_add_eq_smul hapos hℓ hxmin hv hw hu hc ((add_comm w u).trans huw.symm)⟩
  · rintro _ ⟨c, hc, rfl⟩ hz
    rw [map_smul, smul_eq_mul, hdv]
    exact mul_neg_of_pos_of_neg (hc.lt_of_ne (by rintro rfl; simp at hz)) hm
  · rintro _ ⟨c, hc, rfl⟩
    simp [hℓv]

end Convex

/-! ### The numerical topology -/

section Topology

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Addition and negation are continuous for the numerical topology. -/
private theorem isTopologicalAddGroup_numericalCurveClasses :
    IsTopologicalAddGroup (NumericalCurveClasses sX) :=
  isTopologicalAddGroup_iInf fun L => isTopologicalAddGroup_iInf fun h =>
    haveI := h; isTopologicalAddGroup_induced (NumericalCurveClasses.degree sX L)

/-- Scalar multiplication is jointly continuous for the numerical topology. -/
private theorem continuousSMul_numericalCurveClasses :
    ContinuousSMul ℝ (NumericalCurveClasses sX) :=
  continuousSMul_iInf fun L => continuousSMul_iInf fun h =>
    haveI := h; continuousSMul_induced (NumericalCurveClasses.degree sX L)

/-- The numerical topology is locally convex. -/
private theorem locallyConvexSpace_numericalCurveClasses :
    LocallyConvexSpace ℝ (NumericalCurveClasses sX) :=
  LocallyConvexSpace.iInf fun L => LocallyConvexSpace.iInf fun h =>
    haveI := h; LocallyConvexSpace.induced (NumericalCurveClasses.degree sX L)

/-- The numerical topology is Hausdorff: the degree forms separate numerical classes. -/
private theorem t2Space_numericalCurveClasses : T2Space (NumericalCurveClasses sX) := by
  refine T2Space.of_injective_continuous (f := fun z (p : Σ' L : X.Modules,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) =>
      haveI := p.2; NumericalCurveClasses.degree sX p.1 z) ?_
    (continuous_pi fun p => haveI := p.2; NumericalCurveClasses.continuous_degree sX p.1)
  intro z z' hzz'
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  exact OneCycle.numericalClass_eq_iff.mpr fun L hL => congrFun hzz' ⟨L, hL⟩

/-- `(z · ∑ⱼ cⱼ Eⱼ) = ∑ⱼ cⱼ (z · 𝒪_X(Eⱼ))` on `N₁(X)`. -/
private theorem intersectionNumber_eq_sum_degree (D : KCartierDivisor ℝ X)
    (z : NumericalCurveClasses sX) :
    NumericalCurveClasses.intersectionNumber D z = D.sum fun E c =>
      c * NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) z := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  simp only [NumericalCurveClasses.intersectionNumber_numericalClass,
    NumericalCurveClasses.degree_numericalClass, OneCycle.intersectionNumber,
    OneCycle.intersectionPairing, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, OneCycle.cartierDegree]

/-- The form `z ↦ (z · D)` of an `ℝ`-Cartier divisor is continuous. -/
private theorem continuous_intersectionNumber (D : KCartierDivisor ℝ X) :
    Continuous (NumericalCurveClasses.intersectionNumber (sX := sX) D) := by
  refine Continuous.congr ?_ fun z => (intersectionNumber_eq_sum_degree sX D z).symm
  exact continuous_finsetSum _ fun E _ =>
    continuous_const.mul (NumericalCurveClasses.continuous_degree sX _)

end Topology

/-- A projective variety carries a Cartier divisor whose invertible sheaf is ample. -/
private theorem exists_isAmple_sheaf {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
    [h : AlgebraicGeometry.IsProjectiveVariety k sX] :
    ∃ D : X.CartierDivisor, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf D) := by
  obtain ⟨⟨L, hL, hrel, hA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple h.isProjective.isProjective
  obtain ⟨A, ⟨e⟩⟩ := hA h.toIsIntegral
  exact ⟨A, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mpr
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hrel)⟩

/-- An ample Cartier divisor on a projective variety is positive on the nonzero classes of the
closed cone of curves. -/
private theorem intersectionNumber_ofCartier_pos {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsProjectiveVariety k sY] {E : Y.CartierDivisor}
    (hE : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf E))
    {z : NumericalCurveClasses sY} (hz : z ∈ closedConeOfCurves sY) (hz0 : z ≠ 0) :
    0 < NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) z := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sY z
  rw [NumericalCurveClasses.intersectionNumber_numericalClass]
  exact closedConeOfCurves_diff_zero_subset_posHalfspace sY E hE ⟨hz, hz0⟩ Z rfl

/-! ### Curves and push-forward -/

section Curves

variable {k : Type u} [Field k] {X S : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sS : S ⟶ Spec (.of k)}

variable [IsSeparated sS] [LocallyOfFiniteType sS]

/-- The image of a proper curve that is not a point is a proper curve. -/
private theorem isProperCurve_of_not_range_eq_singleton (h : X ⟶ S) (hh : h ≫ sS = sX)
    (C : ProperCurve sX) (hpt : ¬ ∃ y : S, Set.range (C.ι ≫ h) = {y}) :
    IsProperCurve sS (h C.point) := by
  set φ := C.ι ≫ h with hφdef
  have hφ : φ ≫ sS = C.ι ≫ sX := by rw [hφdef, Category.assoc, hh]
  have : IsProper (φ ≫ sS) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sS
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sS) := hφ ▸ inferInstance
  have hcurve := isCurve_imageι_comp sS φ hpt
  have hker := C.ker_comp h
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (h C.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (h C.point) ≫ sS) := by
    have h1 : IsProper (φ.imageι ≫ sS) := isProper_imageι_comp φ sS
    change IsProper (φ.ker.subschemeι ≫ sS) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- The image of a proper curve that is not a point has a positive residue degree. -/
private theorem residueFieldDegree_pos (h : X ⟶ S) (hh : h ≫ sS = sX) (C : ProperCurve sX)
    (hpt : ¬ ∃ y : S, Set.range (C.ι ≫ h) = {y}) :
    0 < residueFieldDegree h C.point := by
  set φ := C.ι ≫ h with hφdef
  have hφ : φ ≫ sS = C.ι ≫ sX := by rw [hφdef, Category.assoc, hh]
  have : IsProper (φ ≫ sS) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sS
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sS) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree h C.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp C.ι h (genericPoint C.scheme)
    rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  apply degreeOver_pos
  rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
  exact finite_functionField_image sS φ hpt

/-- A curve whose image under `h` is a single point is contracted by `h`. -/
private theorem isContractedBy_of_range_eq_singleton (h : X ⟶ S) (C : ProperCurve sX) {y : S}
    (hy : Set.range (C.ι ≫ h) = {y}) : C.IsContractedBy h := by
  have hmem : ∀ x ∈ closure ({C.point} : Set X), h x = y := fun x hx => by
    rw [← C.range_ι] at hx
    obtain ⟨c, rfl⟩ := hx
    have : (C.ι ≫ h) c ∈ Set.range (C.ι ≫ h) := ⟨c, rfl⟩
    rwa [hy, Scheme.Hom.comp_apply] at this
  exact fun x hx => (hmem x hx).trans (hmem _ (subset_closure rfl)).symm

/-- If the image of a curve `C` under `h` is not a point, then `h_*[C]` has positive degree
against an ample divisor `H` on `S`: it is a positive multiple of the class of the curve
`h(C)`. -/
private theorem intersectionNumber_cyclePushforwardOfPoint_pos
    (hSv : AlgebraicGeometry.IsVariety k sS) (h : X ⟶ S) (hh : h ≫ sS = sX) {H : S.CartierDivisor}
    (hH : Stacks.Ample.IsAmple S (MMP.CartierDivisor.sheaf H)) (C : ProperCurve sX)
    (hpt : ¬ ∃ y : S, Set.range (C.ι ≫ h) = {y}) :
    0 < (cyclePushforwardOfPoint ℝ sS h C.point).intersectionNumber
      (KCartierDivisor.ofCartier ℝ H) := by
  have hC' := isProperCurve_of_not_range_eq_singleton h hh C hpt
  have hdeg := MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hSv H hH
    (⟨h C.point, hC'⟩ : ProperCurve sS)
  have hcyc : cyclePushforwardOfPoint ℝ sS h C.point =
      (residueFieldDegree h C.point : ℝ) • (⟨h C.point, hC'⟩ : ProperCurve sS).cycle ℝ := by
    rw [cyclePushforwardOfPoint, dite_eq_left hC', ProperCurve.cycle, Finsupp.smul_single,
      smul_eq_mul, mul_one]
  rw [hcyc, OneCycle.intersectionNumber_ofCartier, map_smul, OneCycle.cartierDegree,
    OneCycle.degree_cycle, smul_eq_mul]
  exact mul_pos (mod_cast residueFieldDegree_pos h hh C hpt) (mod_cast hdeg)

end Curves

end Helpers

/-- **A negative vertical extremal ray.** Let `h : X ⟶ S` be a morphism of projective varieties
over an algebraically closed field `k` of characteristic zero, and `D` an `ℝ`-Cartier divisor on
`X` which is not nef over `S`. Then `NE̅(X)` has an extremal ray `R` with `(z · D) < 0` for every
nonzero `z ∈ R`, such that every curve `C ⊆ X` whose class lies in `R` is contracted by `h`. -/
@[mmp "lem_mmp_projective_negative_vertical_extremal_ray"]
public theorem exists_isExtremalRay_neg_contractedBy_of_not_isRelativelyNef {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sS : S ⟶ Spec (.of k)} (hX : IsProjectiveVariety k sX) (hS : IsProjectiveVariety k sS)
    {h : X ⟶ S} (hh : h ≫ sS = sX) {D : KCartierDivisor ℝ X}
    (hD : ¬ D.IsRelativelyNef sX h) :
    ∃ R : Set (NumericalCurveClasses sX),
      IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R ∧
      (∀ z ∈ R, z ≠ 0 → NumericalCurveClasses.intersectionNumber D z < 0) ∧
      ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.IsContractedBy h := by
  have := hX
  have := hS
  have hSv : AlgebraicGeometry.IsVariety k sS := hS.toIsVariety
  have : IsSeparated sS := hSv.toIsSeparated
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have := isTopologicalAddGroup_numericalCurveClasses sX
  have := continuousSMul_numericalCurveClasses sX
  have := locallyConvexSpace_numericalCurveClasses sX
  have := t2Space_numericalCurveClasses sX
  obtain ⟨A, hA⟩ := exists_isAmple_sheaf (sX := sX)
  obtain ⟨H, hH⟩ := exists_isAmple_sheaf (sX := sS)
  set φ := NumericalCurveClasses.pushforward h hh
  set ℓ : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
    (NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ H)).comp φ with hℓ
  have hℓC : ∀ C : ProperCurve sX, ℓ (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (cyclePushforwardOfPoint ℝ sS h C.point).intersectionNumber
        (KCartierDivisor.ofCartier ℝ H) := fun C => by
    rw [hℓ, LinearMap.comp_apply, NumericalCurveClasses.isNumericalPushforward_pushforward h hh,
      NumericalCurveClasses.intersectionNumber_numericalClass, OneCycle.pushforward_cycle]
  have hℓnn : ∀ z ∈ closedConeOfCurves sX, 0 ≤ ℓ z := fun z hz => by
    rcases eq_or_ne (φ z) 0 with h0 | h0
    · simp [hℓ, h0]
    · exact (intersectionNumber_ofCartier_pos hH (image_closedConeOfCurves_subset h hh
        (NumericalCurveClasses.isNumericalPushforward_pushforward h hh) ⟨z, hz, rfl⟩) h0).le
  have hz₀ : ∃ z ∈ closedConeOfCurves sX,
      ℓ z = 0 ∧ NumericalCurveClasses.intersectionNumber D z < 0 := by
    simp only [KCartierDivisor.IsRelativelyNef, not_forall, not_le] at hD
    obtain ⟨C, hC, hneg⟩ := hD
    refine ⟨_, coneOfCurves_le_closedConeOfCurves sX
      (numericalClass_cycle_mem_coneOfCurves sX C), ?_, hneg⟩
    rw [hℓC, ← OneCycle.pushforward_cycle,
      C.pushforward_cycle_eq_zero_of_isContractedBy ℝ h hh hC]
    simp [OneCycle.intersectionNumber]
  obtain ⟨R, hR, hRneg, hRℓ⟩ := exists_isExtremalRay_of_isCompact (closedConeOfCurves sX)
    (NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ A)) ℓ
    (NumericalCurveClasses.intersectionNumber D) (continuous_intersectionNumber sX _)
    ((continuous_intersectionNumber sS _).comp (NumericalCurveClasses.continuous_pushforward h hh))
    (continuous_intersectionNumber sX _)
    (isCompact_closedConeOfCurves_inter_le_and_finite sX A hA 1).1
    (fun _ => intersectionNumber_ofCartier_pos hA) hℓnn hz₀
  refine ⟨R, hR, hRneg, fun C hCR => ?_⟩
  by_cases hpt : ∃ y : S, Set.range (C.ι ≫ h) = {y}
  · exact isContractedBy_of_range_eq_singleton h C hpt.choose_spec
  · exact absurd ((hℓC C).symm.trans (hRℓ _ hCR))
      (intersectionNumber_cyclePushforwardOfPoint_pos hSv h hh hH C hpt).ne'

end MMP.Mori
