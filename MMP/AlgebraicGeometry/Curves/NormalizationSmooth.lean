module

public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationProperProjective
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic

/-!
# The normalization of a curve over a perfect field is a smooth curve

Let `K` be a perfect field and `p : Z ⟶ Spec K` a curve. Its normalization
`ν : Z̃ ⟶ Z` (`AlgebraicGeometry.normalizationOverField`) is finite and surjective, `Z̃` is
again a curve over `K`, and `Z̃` is normal of dimension one, hence regular, hence smooth over the
perfect field `K`: smooth of relative dimension one. If `Z` is projective over `K`, so is `Z̃`.

## Main results

* `MMP.exists_smoothOfRelativeDimension_isFinite_surjective_of_isCurve`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], I.6.
* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- **The normalization of a curve over a perfect field is a smooth curve.** For a curve
`p : Z ⟶ Spec K` over a perfect field there are a curve `Γ` over `K`, smooth of relative
dimension one, and a finite surjective morphism `ν : Γ ⟶ Z` over `K`; if `Z` is projective over
`K`, then so is `Γ`. -/
theorem exists_smoothOfRelativeDimension_isFinite_surjective_of_isCurve (K : Type u) [Field K]
    [PerfectField K] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [IsCurve K p] :
    ∃ (Γ : Scheme.{u}) (_ : Γ.Over (Spec (.of K))) (ν : Γ ⟶ Z),
      IsFinite ν ∧ Surjective ν ∧ ν ≫ p = Γ ↘ Spec (.of K) ∧ IsCurve K (Γ ↘ Spec (.of K)) ∧
        SmoothOfRelativeDimension 1 (Γ ↘ Spec (.of K)) ∧
        (IsProjectiveMorphism p → IsProjectiveMorphism (Γ ↘ Spec (.of K))) := by
  have hZ := finite_irreducibleComponents_of_locallyOfFiniteType K p
  haveI hc : IsCurve K (normalizationOverField K p ≫ p) := isCurve_normalizationOverField_comp K p
  letI : (normalizationSchemeOverField K p).Over (Spec (.of K)) :=
    ⟨normalizationOverField K p ≫ p⟩
  haveI : IsCurve K ((normalizationSchemeOverField K p) ↘ Spec (.of K)) := hc
  haveI hlft : LocallyOfFiniteType (normalizationOverField K p ≫ p) :=
    hc.toIsVariety.toLocallyOfFiniteType
  haveI : IsNormal (normalizationSchemeOverField K p) := Scheme.isNormal_normalizationScheme Z hZ
  haveI : IsLocallyNoetherian (normalizationSchemeOverField K p) :=
    LocallyOfFiniteType.isLocallyNoetherian (normalizationOverField K p ≫ p)
  have hreg : IsRegular (normalizationSchemeOverField K p) :=
    isRegular_of_isNormal_of_topologicalKrullDim_le_one _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := normalizationOverField K p ≫ p)).le
  haveI : Smooth ((normalizationSchemeOverField K p) ↘ Spec (.of K)) :=
    smooth_of_isRegular_of_perfectField K (normalizationOverField K p ≫ p) hreg
  refine ⟨normalizationSchemeOverField K p, inferInstance, normalizationOverField K p,
    isFinite_normalizationOverField K p, Scheme.surjective_normalization Z hZ, rfl,
    inferInstance, smoothOfRelativeDimension_one_of_isCurve K _, fun hproj ↦ ?_⟩
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hproj
  exact (isProjective_iff_isProjectiveMorphism_of_isAffine (normalizationOverField K p ≫ p)).mp
    ((isProper_and_isProjective_normalizationOverField K p).2
      ((isProjective_iff_isProjectiveMorphism_of_isAffine p).mpr hproj))

end MMP
