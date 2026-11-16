module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Japanese
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Normalization.Over
public import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import MMP.AlgebraicGeometry.Variety.SmoothEmbedding

/-!
# A scheme finite over a complex scheme is a complex scheme

Let `X` be a complex scheme (Fulton, §19.1): an algebraic scheme over `ℂ` with a closed imbedding
`i : X → M` into a smooth variety `M`. If `f : Y → X` is a finite morphism over `ℂ`, then `Y` is
again a complex scheme: `Y` is finite, in particular affine and of finite type, over the closed
subscheme `X` of `M`, so it imbeds as a closed subscheme of a vector bundle over `M`, which is a
smooth variety (`MMP.exists_isClosedImmersion_isSmoothVariety_of_isFinite`, using the resolution
property of `M`).

In particular the normalization `X̃` of a complex variety `X` is a complex scheme, the
normalization morphism `X̃ → X` being finite.

## Main results

* `MMP.IsComplexScheme.of_isFinite`: a scheme finite over a complex scheme is a complex scheme.
* `MMP.isComplexScheme_normalizationScheme`: the normalization of an integral complex scheme is a
  complex scheme.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Appendix B.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP

/-- A scheme finite over a complex scheme is a complex scheme: if `X` is a complex scheme and
`f : Y → X` is a finite morphism over `ℂ`, then `Y` is a complex scheme. -/
theorem IsComplexScheme.of_isFinite {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] (f : Y ⟶ X) [IsFinite f]
    [f.IsOver (Spec (.of ℂ))] : IsComplexScheme Y := by
  obtain ⟨M, _, hM, i, hi, hic⟩ := (inferInstance : IsComplexScheme X).exists_isClosedImmersion
  obtain ⟨N, t, j, hN, hj, hjt⟩ :=
    exists_isClosedImmersion_isSmoothVariety_of_isFinite (M ↘ Spec (.of ℂ)) i f
  have hover : j ≫ t = Y ↘ Spec (.of ℂ) := by
    rw [hjt, hi.comp_over]
    exact (Scheme.Hom.isOver_iff (Spec (.of ℂ))).1 inferInstance
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    hover ▸ (inferInstance : LocallyOfFiniteType (j ≫ t))
  haveI : QuasiCompact (Y ↘ Spec (.of ℂ)) := hover ▸ (inferInstance : QuasiCompact (j ≫ t))
  letI : N.Over (Spec (.of ℂ)) := ⟨t⟩
  exact { exists_isClosedImmersion := ⟨N, inferInstance, hN, j, ⟨hover⟩, hj⟩ }

/-- The normalization of an integral complex scheme is a complex scheme. -/
instance isComplexScheme_normalizationScheme (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsIntegral X] :
    IsComplexScheme (X.normalizationScheme (MMP.finite_irreducibleComponents_of_isIntegral X)) :=
  haveI : IsFinite (X.normalization (MMP.finite_irreducibleComponents_of_isIntegral X)) :=
    normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
      (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (X ↘ Spec (.of ℂ))))
  IsComplexScheme.of_isFinite (X.normalization (MMP.finite_irreducibleComponents_of_isIntegral X))

end MMP
