module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Closed subschemes of complex schemes

## Main results

* `MMP.isComplexScheme_subscheme`: a closed subscheme of a complex scheme is a complex scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped MMP.SubschemeOver

namespace MMP

/-- A closed subscheme of a complex scheme is a complex scheme. -/
instance isComplexScheme_subscheme {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (I : X.IdealSheafData) : IsComplexScheme I.subscheme where
  toLocallyOfFiniteType := by
    rw [← comp_over (I.subschemeι) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (I.subschemeι) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨W, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    exact ⟨W, inferInstance, inferInstance, I.subschemeι ≫ j, inferInstance, inferInstance⟩

end MMP
