module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
public import MMP.AlgebraicGeometry.Divisor.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapNoetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Proper birational morphisms of smooth surfaces factor into point blowups

Let `k` be an algebraically closed field and `h : Y' ⟶ Y` a proper birational morphism of smooth
surfaces over `k`. Then `h` is, up to an isomorphism of its source over `Y`, a finite composite of
blowups at closed points.

## Main results

* `MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface`: the factorization.

## Implementation notes

* A *smooth surface* `Y` over `k`, with structure morphism `sY`, is `IsVariety k sY`,
  `MMP.Mori.IsSmoothScheme sY` and `topologicalKrullDim Y = 2`, as in
  `MMP.Resolution.Bridges.Castelnuovo`. Birationality is `AlgebraicGeometry.IsBirational`
  (Stacks 01RO).
* The factorization is `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups Y Set.univ Y' h`: a
  finite `Stacks.ResolutionOfSurfaces.PointBlowupChain` `Y_n ⟶ ⋯ ⟶ Y_0 = Y` of blowups at closed
  points and an isomorphism `e : Y' ≅ Y_n` with `e ≫ (Y_n ⟶ Y) = h`; the empty chain is the case
  that `h` is an isomorphism. The library theorem is
  `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_isProper_of_isBirational` (Stacks 0C5R),
  for integral Noetherian regular schemes of dimension two.
* This module also re-exports
  `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_isNoetherian`
  (Stacks 0C5H): a rational map over `S` from a Noetherian scheme whose local rings are regular of
  dimension at most two to a proper `S`-scheme is resolved by a finite chain of blowups at closed
  points outside its domain.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution.Bridges

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A smooth surface over a field is an integral Noetherian scheme, regular of dimension two. -/
private theorem isIntegralRegularSurface_of_isSmoothSurface (k : Type u) [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsVariety k sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) :
    Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface Y := by
  have hi := hY.toIsIntegral
  have hreg := isRegular_of_isSmoothScheme sY hYs
  have : IsLocallyNoetherian Y := ((isRegular_iff_regular_stalks Y).1 hreg).1
  have := hY.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact ⟨hi, ⟨⟩, hreg, hYd⟩

/-- **Proper birational maps of smooth surfaces factor into point blowups.** Let `k` be an
algebraically closed field and `h : Y' ⟶ Y` a proper birational morphism of smooth surfaces over
`k`. Then there are a finite chain of blowups at closed points `Y_n ⟶ ⋯ ⟶ Y_0 = Y` and an
isomorphism `Y' ≅ Y_n` over `Y` identifying the composite of the chain with `h`. -/
@[mmp "lem_mmp_foundation_smooth_surface_point_blowup_factorization"]
theorem factorsAsPointBlowups_of_isSmoothSurface (k : Type u) [Field k] [IsAlgClosed k]
    {Y Y' : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)}
    (hY : IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (hY' : IsVariety k sY') (hY's : MMP.Mori.IsSmoothScheme sY')
    (hY'd : topologicalKrullDim Y' = 2) (h : Y' ⟶ Y) (_hh : h ≫ sY = sY') [IsProper h]
    (hb : IsBirational h) :
    Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups Y Set.univ Y' h :=
  Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_isProper_of_isBirational h
    (isIntegralRegularSurface_of_isSmoothSurface k hY hYs hYd)
    (isIntegralRegularSurface_of_isSmoothSurface k hY' hY's hY'd) ‹IsProper h› hb

end MMP.Resolution.Bridges
