module

public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.MMP.Contraction.ExceptionalDivisorNegativeOnRay

/-!
# A prime divisor in the exceptional set of an extremal contraction is the whole exceptional set

Let `X` be a normal projective `ℚ`-factorial variety over a field `k`, `R ⊆ NE̅(X)` an extremal
ray and `f : X ⟶ Y` a birational contraction of `R`. If the exceptional set `Ex(f)` contains a
prime divisor `E`, then `E = Ex(f)`. Every closed point of `Ex(f)` lies on an irreducible curve
`C` contracted by `f`; such a curve has `(E · C) < 0`
(`MMP.Mori.intersectionNumber_single_neg_of_isContractionOfFace`), which forces `C ⊆ E` since
`E` is effective.

## Main results

* `MMP.Mori.point_mem_support_of_intersectionNumber_neg`: a proper curve on which a prime
  divisor `E` is negative lies in `E`.
* `MMP.Mori.exists_properCurve_isContractedBy_of_image_eq_singleton`: a closed irreducible curve
  with a point as image is the closure of the generic point of a contracted proper curve.
* `MMP.Mori.support_eq_exceptionalSet_of_isContractionOfFace`: `E = Ex(f)`.

## Implementation notes

"`E = Ex(f)`" is the equality of `E.support` with the underlying set of
`MMP.Mori.exceptionalSet f`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Proposition 2.5
-/

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

@[expose] public section

universe u

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry

section

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve on which a prime divisor `E` is negative lies in `E`. -/
theorem point_mem_support_of_intersectionNumber_neg [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (hX : MMP.Fourfold.IsQFactorial sX) (E : PrimeDivisor X)
    (C : ProperCurve sX)
    (hneg : QDivisor.intersectionNumber k sX C.ι C.dim_le (Finsupp.single E (1 : ℚ))
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hX _) < 0) :
    C.point ∈ E.support := by
  by_contra hC
  exact hneg.not_ge (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX _ _
    (Finsupp.single_nonneg.mpr zero_le_one) C
    fun h => hC (DivisorWithCoeffs.supp_single_le E 1 h)).1

/-- A closed irreducible curve `C` of a proper `k`-scheme with `f '' C` a point is a proper curve
contracted by `f`, with generic point `η` and `closure {η} = C`. -/
theorem exists_properCurve_isContractedBy_of_image_eq_singleton (sX : X ⟶ Spec (.of k))
    [IsProper sX] (f : X ⟶ Y) {C : Set X} (hCc : IsClosed C) (hCi : IsIrreducible C)
    (hCd : topologicalKrullDim C = 1) {y : Y} (hy : f '' C = {y}) :
    ∃ Γ : ProperCurve sX, Γ.IsContractedBy f ∧ closure {Γ.point} = C := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hCi hCc
  have hη' : closure ({η} : Set X) = C := hη
  have hf : ∀ z ∈ C, f z = y := fun z hz => hy.subset ⟨z, hz, rfl⟩
  refine ⟨⟨η, isProperCurve_of_isProper sX (by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hη', hCd])⟩, fun z hz => ?_, hη'⟩
  rw [hf z (hη' ▸ hz), hf η (hη' ▸ subset_closure rfl)]

end

/-- **A prime divisor in the exceptional set of an extremal contraction is all of it.** Let `X`
be a normal projective `ℚ`-factorial variety over `k`, `R ⊆ NE̅(X)` an extremal ray and
`f : X ⟶ Y` a birational contraction of `R`. If a prime divisor `E` of `X` is contained in the
exceptional set `MMP.Mori.exceptionalSet f`, then its support is the whole exceptional set. -/
@[mmp "lem_km2a_divisor_in_exceptional_set_is_exceptional_set"]
theorem support_eq_exceptionalSet_of_isContractionOfFace
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (hX : MMP.Fourfold.IsQFactorial sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Y} (hf : IsContractionOfFace k sX sY R f) (hbir : IsBirationalMorphism f)
    (E : PrimeDivisor X) (hE : E.support ⊆ (exceptionalSet f : Set X)) :
    E.support = (exceptionalSet f : Set X) := by
  haveI := hf.isProjectiveVariety_source
  haveI := hf.isProjectiveVariety_target
  haveI : IsProper f := by
    have : IsProper (f ≫ sY) := hf.comp_eq ▸ inferInstance
    exact IsProper.of_comp f sY
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hEc : IsClosed E.support := E.idealSheaf.support.isClosed
  refine hE.antisymm ?_
  rw [← closure_inter_closedPoints (isClosed_exceptionalSet f)]
  refine closure_minimal ?_ hEc
  rintro x ⟨hx, hxc⟩
  obtain ⟨C, hCc, hCi, hCd, hxC, y, hy⟩ :=
    exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet
      hf.isProjectiveVariety_source.toIsVariety hf.isProjectiveVariety_target.toIsVariety f
      hf.comp_eq hbir hf.isIso_app hxc hx
  obtain ⟨Γ, hΓ, rfl⟩ :=
    exists_properCurve_isContractedBy_of_image_eq_singleton sX f hCc hCi hCd hy
  exact hEc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
    (point_mem_support_of_intersectionNumber_neg hX E Γ
      (intersectionNumber_single_neg_of_isContractionOfFace hX hR hf hbir E hE Γ hΓ))) hxC

end MMP.Mori

end
