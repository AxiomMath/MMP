module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The reduced closed subscheme on a closed set, over a base

For a closed set `Z` of a scheme `X` over `S`, the reduced closed subscheme
`(vanishingIdeal Z).subscheme` is a scheme over `S` through its inclusion into `X`, and that
inclusion is a morphism over `S`. (Its reducedness is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`.)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace MMP

variable {X : Scheme.{u}}

/-- The reduced closed subscheme on a closed set of a scheme over `S` is a scheme over `S`. -/
instance instOverSubschemeVanishingIdeal {S : Scheme.{u}} [X.Over S] (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Over S :=
  ⟨(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ X ↘ S⟩

/-- The inclusion of the reduced closed subscheme on a closed set is a morphism over `S`. -/
instance isOver_subschemeι_vanishingIdeal {S : Scheme.{u}} [X.Over S] (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.IsOver S :=
  ⟨rfl⟩

end MMP
