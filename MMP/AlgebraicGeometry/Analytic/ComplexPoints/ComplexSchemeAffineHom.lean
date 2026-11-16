module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Finite

/-!
# A scheme affine of finite type over a complex scheme is a complex scheme

For a closed imbedding `X → M` of a complex scheme into a smooth variety, a scheme `Y` affine and
of finite type over `X` imbeds as a closed subscheme of a vector bundle over `M`, a smooth variety
(`MMP.exists_isClosedImmersion_isSmoothVariety`).

## Main results

* `MMP.IsComplexScheme.of_isAffineHom`: a scheme affine and of finite type over a complex scheme
  is a complex scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP

/-- **A scheme affine of finite type over a complex scheme is a complex scheme.** Let `X` be a
complex scheme and `f : Y → X` an affine morphism of finite type over `ℂ`. Then `Y` is a complex
scheme: for a closed imbedding `X → M` into a smooth variety, `Y` imbeds over `M` in a vector
bundle over `M`, a smooth variety. -/
theorem IsComplexScheme.of_isAffineHom {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] (f : Y ⟶ X) [IsAffineHom f]
    [LocallyOfFiniteType f] [f.IsOver (Spec (.of ℂ))] : IsComplexScheme Y := by
  obtain ⟨M, _, hM, i, hi, hic⟩ := (inferInstance : IsComplexScheme X).exists_isClosedImmersion
  obtain ⟨N, t, j, hN, hj, hjt⟩ :=
    exists_isClosedImmersion_isSmoothVariety (M ↘ Spec (.of ℂ)) i f
  have hover : j ≫ t = Y ↘ Spec (.of ℂ) := by
    rw [hjt, hi.comp_over]
    exact (Scheme.Hom.isOver_iff (Spec (.of ℂ))).1 inferInstance
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    hover ▸ (inferInstance : LocallyOfFiniteType (j ≫ t))
  haveI : QuasiCompact (Y ↘ Spec (.of ℂ)) := hover ▸ (inferInstance : QuasiCompact (j ≫ t))
  letI : N.Over (Spec (.of ℂ)) := ⟨t⟩
  exact { exists_isClosedImmersion := ⟨N, inferInstance, hN, j, ⟨hover⟩, hj⟩ }

end MMP
