module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base

/-!
# The Chow situation of a field

Stacks' Chow homology over a field `K` works in the situation `Stacks.Chow.fieldChowSituation K`,
the base `Spec K` with the zero dimension function (Stacks 02QM). Many of its results need the base
to be a Jacobson space; this file records that `Spec K` is one, as an instance on the base of the
situation, so that instance search finds it through the `fieldChowSituation` wrapper.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP

/-- The base `Spec K` of the Chow situation of a field is a Jacobson space. -/
instance jacobsonSpace_fieldChowSituation (K : Type u) [Field K] :
    JacobsonSpace (Stacks.Chow.fieldChowSituation K).S :=
  inferInstanceAs (JacobsonSpace (Spec (.of K)))

end MMP
