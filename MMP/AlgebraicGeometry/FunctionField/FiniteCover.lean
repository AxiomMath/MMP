module

public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTrace

/-!
# The extension of function fields of a finite cover

For a finite surjective morphism `f : Y ⟶ X` of integral schemes, the extension `k(X) ⊆ k(Y)`
given by `AlgebraicGeometry.functionFieldMap f` is finite; over a field of characteristic zero it
is separable. These are the finiteness and separability facts under which the trace of forms
along `f` is defined.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.finiteDimensional_functionFieldMap`: finiteness.
* `MMP.FourfoldProofs.FractionalLogComplexProof.isSeparable_functionFieldMap`: separability in
  characteristic zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- For a finite surjective morphism `f : Y ⟶ X` of integral schemes, `k(Y)` is
finite-dimensional over `k(X)` via `functionFieldMap f`. -/
theorem finiteDimensional_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsFinite f] [Surjective f] :
    letI := MMP.Mori.functionFieldMapAlgebra f
    FiniteDimensional X.functionField Y.functionField := by
  convert AlgebraicGeometry.SeparableGoUp.finiteDimensional_functionField f using 3
  exact congrArg RingHom.toAlgebra (MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap f).symm

/-- If `X` is a scheme over a field `k` of characteristic zero and `f : Y ⟶ X` is a finite
surjective morphism of integral schemes, then `k(Y)` is separable over `k(X)` via
`functionFieldMap f`. -/
theorem isSeparable_functionFieldMap {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsFinite f]
    [Surjective f] :
    letI := MMP.Mori.functionFieldMapAlgebra f
    Algebra.IsSeparable X.functionField Y.functionField := by
  let := MMP.Mori.functionFieldAlgebra sX
  have : CharZero X.functionField :=
    charZero_of_injective_algebraMap (algebraMap k X.functionField).injective
  have := finiteDimensional_functionFieldMap f
  infer_instance

end MMP.FourfoldProofs.FractionalLogComplexProof
