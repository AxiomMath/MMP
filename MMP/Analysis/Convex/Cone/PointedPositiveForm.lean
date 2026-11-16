module

public import MMP.Attr
public import MMP.Analysis.Convex.Cone.CompactSlices

/-!
# Positive linear forms on pointed cones

A closed convex cone `C` in a finite-dimensional real vector space is pointed when
`C ∩ (-C) = {0}`; such a cone admits a linear form that is strictly positive on `C ∖ {0}`.
This file attaches the project's references for that statement to the theorem that proves it.

## Main results

* `MMP.Positivity.exists_dual_pos_of_salient`: a closed convex cone `C` with `C ∩ (-C) = {0}` in
  a finite-dimensional real vector space has a linear form positive on `C ∖ {0}`.
-/

@[expose] public section

attribute [mmp "lem_mmp_foundation_pointed_closed_cone_positive"]
  MMP.Positivity.exists_dual_pos_of_salient

attribute [mmp "lem_mmp_foundation_km3b_pointed_positive"]
  MMP.Positivity.exists_dual_pos_of_salient
