module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Closed subschemes of locally Noetherian schemes

A closed subscheme `I.subscheme` of a locally Noetherian scheme `Y` is locally Noetherian: its
inclusion is a closed immersion, hence locally of finite type.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP

/-- A closed subscheme of a locally Noetherian scheme is locally Noetherian. -/
instance isLocallyNoetherian_subscheme {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) : IsLocallyNoetherian I.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian I.subschemeι

end MMP
