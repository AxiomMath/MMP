module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Datum

/-!
# Locally free modules of rank one are finite locally free

Stacks proves that a module locally free of rank `r` is finite locally free
(`Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_rank`) as a lemma; this file makes the rank one
case an instance, so that instance search finds it for line bundles.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP

/-- A module locally free of rank one is finite locally free. -/
instance isFiniteLocallyFree_of_rank_one {W : Scheme.{u}} (ℱ : W.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℱ 1] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℱ :=
  Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_rank ℱ 1

end MMP
