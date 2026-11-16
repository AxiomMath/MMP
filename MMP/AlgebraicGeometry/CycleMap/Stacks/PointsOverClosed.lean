module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts

/-!
# The complex points over a closed subset are locally contractible

For a closed subset `T` of a scheme `S` locally of finite type over `ℂ`, the complex points
`T(ℂ) = {p ∈ S(ℂ) | p lies over T}` are the underlying space of the reduced closed subscheme on
`T`, so they have bases of open contractible neighbourhoods.

## Main results

* `MMP.Chow.hasOpenContractibleBasis_setOf_mem_closeds`: `T(ℂ)` has bases of open contractible
  neighbourhoods.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.UnderlyingSpace

namespace MMP.Chow

/-- The complex points `T(ℂ) = {p | p lies over T}` of a closed subset `T` of a scheme `S` locally
of finite type over `ℂ` have bases of open contractible neighbourhoods: `T(ℂ)` is the underlying
space of the reduced closed subscheme on `T`. -/
theorem hasOpenContractibleBasis_setOf_mem_closeds (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (S ↘ Spec (.of ℂ))] (T : Closeds S) :
    HasOpenContractibleBasis
      {p : UnderlyingSpace ℂ S | p.toHom (IsLocalRing.closedPoint ℂ) ∈ (T : Set S)} := by
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ S ↘ Spec (.of ℂ)⟩
  have : I.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ S ↘ Spec (.of ℂ)))
  have hr : Set.range (map (K := ℂ) I.subschemeι) =
      {p : UnderlyingSpace ℂ S | p.toHom (IsLocalRing.closedPoint ℂ) ∈ (T : Set S)} := by
    rw [show Set.range (map (K := ℂ) I.subschemeι) = Set.range (mapFun (K := ℂ) I.subschemeι)
      from rfl, range_mapFun_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (UnderlyingSpace.hasOpenContractibleBasis I.subscheme).of_homeomorph
    ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) I.subschemeι).isEmbedding.toHomeomorph
      |>.trans (Homeomorph.setCongr hr))

end MMP.Chow
