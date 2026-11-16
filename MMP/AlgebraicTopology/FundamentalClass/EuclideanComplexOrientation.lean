module

public import MMP.AlgebraicTopology.ThomClass.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The complex orientation of the Euclidean space `ℂⁿ`

The complex structure of `ℂⁿ` orients its underlying real vector space by the real basis
`e₁, i e₁, e₂, i e₂, …, e_n, i e_n` (`MMP.ThomClass.complexOrientationBasis`). This file transports
that basis to the Euclidean space `EuclideanSpace ℂ (Fin n)`, the model space of complex manifolds
of dimension `n`.

## Main definitions

* `MMP.FundamentalClass.euclideanComplexOrientationBasis`: the real basis
  `e₁, i e₁, …, e_n, i e_n` of `ℂⁿ`, as the Euclidean space `EuclideanSpace ℂ (Fin n)`.
-/

@[expose] public noncomputable section

namespace MMP

namespace FundamentalClass

open ThomClass

/-- The real basis `e₁, i e₁, e₂, i e₂, …, e_n, i e_n` of the Euclidean space `ℂⁿ`: it defines
the orientation of `ℂⁿ` given by its complex structure. -/
def euclideanComplexOrientationBasis (n : ℕ) :
    Module.Basis (Fin (2 * n)) ℝ (EuclideanSpace ℂ (Fin n)) :=
  (complexOrientationBasis n).map ((WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.restrictScalars ℝ)

/-- The `i`-th vector of `euclideanComplexOrientationBasis n` is the `i`-th vector of
`complexOrientationBasis n`, viewed in `EuclideanSpace ℂ (Fin n)`. -/
@[simp]
lemma euclideanComplexOrientationBasis_apply (n : ℕ) (i : Fin (2 * n)) :
    euclideanComplexOrientationBasis n i = WithLp.toLp 2 (complexOrientationBasis n i) :=
  rfl

end FundamentalClass

end MMP
