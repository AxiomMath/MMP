module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible

/-!
# Proper neighbourhood retractions in complex schemes

The underlying space of a complex scheme has a closed imbedding in some `ℝᴺ`
(`lem_ext_c19_complex_scheme_locally_contractible`), so a closed, locally contractible subset of
it has a closed neighbourhood with a proper retraction onto it.

## Main results

* `MMP.UnderlyingSpace.exists_isClosed_isProperMap_retraction`.
-/

@[expose] public section

open Topology AlgebraicGeometry

namespace MMP

open MMP

namespace UnderlyingSpace

/-- **A closed neighbourhood with a proper retraction in a complex scheme** (Fulton, §19.1). A
closed subset `X` of the underlying space of a complex scheme, every point of which has a basis of
open contractible neighbourhoods in `X`, has a closed neighbourhood `N` with a proper retraction
`r : N → X`. -/
theorem exists_isClosed_isProperMap_retraction (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [IsComplexScheme S] {X : Set (UnderlyingSpace ℂ S)} (hX : IsClosed X)
    (hXc : ∀ x : X, (𝓝 x).HasBasis (fun V : Set X ↦ IsOpen V ∧ x ∈ V ∧ ContractibleSpace V) id) :
    ∃ N : Set (UnderlyingSpace ℂ S), IsClosed N ∧ X ⊆ interior N ∧
      ∃ r : C(N, X), IsProperMap r ∧
        ∀ y : N, (y : UnderlyingSpace ℂ S) ∈ X → (r y : UnderlyingSpace ℂ S) = y := by
  obtain ⟨-, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  exact MMP.exists_isClosed_isProperMap_retraction hF hX hXc

end UnderlyingSpace

end MMP
