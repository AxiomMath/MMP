module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent

/-!
# The residue degree of a birational morphism at the generic point

Let `f : X ⟶ Y` be a dominant birational morphism of integral schemes. The residue fields at the
generic points are the function fields, and `f` induces an isomorphism `R(Y) ≅ R(X)`, so the
residue degree of `f` at the generic point of `X` is one.

## Main results

* `MMP.residueDegree_genericPoint_eq_one_of_isBirational`

## References

* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP

/-- **A birational morphism has degree one.** For a dominant birational morphism `f : X ⟶ Y` of
integral schemes, the residue degree `[κ(η_X) : κ(η_Y)] = [R(X) : R(Y)]` at the generic point is
one. -/
theorem residueDegree_genericPoint_eq_one_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (hf : IsBirational f) :
    f.residueDegree (genericPoint X) = 1 := by
  let := (dominantFunctionFieldMap f).toAlgebra
  rw [← Stacks.Chow.finrank_functionField_eq_residueDegree f]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    (Stacks.Chow.bijective_dominantFunctionFieldMap_of_isBirational f hf)

end MMP
