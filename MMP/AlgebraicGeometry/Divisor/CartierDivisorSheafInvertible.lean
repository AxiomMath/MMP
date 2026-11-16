module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic

/-!
# `𝒪_X(D)` is an invertible module

The sheaf `𝒪_X(D)` of a Cartier divisor (`MMP.CartierDivisor.sheaf`) is finite locally free of
rank one (`MMP.CartierDivisor.isFiniteLocallyFreeOfRank_sheaf`), hence invertible by Stacks
Tag 0B8M (`Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`).

## Main results

* `MMP.CartierDivisor.isInvertible_sheaf`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.CartierDivisor

/-- **`𝒪_X(D)` is invertible** (Stacks Tag 0B8M (1)): it is finite locally free of rank one. -/
@[mmp "lem_p01a_line_bundle_of_divisor_invertible"]
theorem isInvertible_sheaf {X : Scheme.{u}} (D : X.CartierDivisor) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (CartierDivisor.sheaf D) :=
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

end MMP.CartierDivisor
