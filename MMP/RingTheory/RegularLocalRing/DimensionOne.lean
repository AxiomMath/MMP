module

public import MMP.Attr
public import MMP.RingTheory.DiscreteValuationRing.Integrality

/-!
# Regular local rings of dimension one

## Main results

* `MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one`: a regular local ring
  of Krull dimension one is a discrete valuation ring (Fulton's convention for regularity is
  Mathlib's `IsRegularLocalRing`: Noetherian local with `spanFinrank 𝔪 = dim`).
-/

@[expose] public section

attribute [mmp "lem_mmp_foundation_regular_curve_dvr"]
  MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one
