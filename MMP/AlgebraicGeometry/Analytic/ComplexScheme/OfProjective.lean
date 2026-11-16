module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Variety.SmoothEmbedding
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# A scheme projective over `ℂ` is a complex scheme

A scheme `X` projective over `ℂ` is a complex scheme in Fulton's sense (§19.1): a projective
morphism to the smooth variety `Spec ℂ` factors through a closed immersion into a smooth variety
(`MMP.exists_isClosedImmersion_isSmoothVariety_of_isProjective`, a projective bundle over
`Spec ℂ`, that is, projective space), and `X` is proper over `ℂ`, hence of finite type.

## Main results

* `MMP.Analytic.isComplexScheme_of_isProjective`: a scheme projective over `ℂ` is a complex
  scheme.

## References

* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MMP

namespace MMP.Analytic

/-- A scheme projective over `ℂ` is a complex scheme: it admits a closed immersion over `ℂ` into
a smooth variety over `ℂ`. -/
theorem isComplexScheme_of_isProjective (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    (h : IsProjective (X ↘ Spec (.of ℂ))) : IsComplexScheme X := by
  haveI : IsProper (X ↘ Spec (.of ℂ)) := h.isProper
  haveI : IsSmoothVariety ℂ (𝟙 (Spec (.of ℂ))) := { }
  obtain ⟨N, t, j, hN, hj, hjt⟩ := exists_isClosedImmersion_isSmoothVariety_of_isProjective
    (𝟙 (Spec (.of ℂ))) (𝟙 (Spec (.of ℂ))) (X ↘ Spec (.of ℂ)) h
  letI : N.Over (Spec (.of ℂ)) := ⟨t⟩
  refine { exists_isClosedImmersion := ⟨N, inferInstance, hN, j, ⟨?_⟩, hj⟩ }
  rw [Category.comp_id, Category.comp_id] at hjt
  exact hjt

end MMP.Analytic
