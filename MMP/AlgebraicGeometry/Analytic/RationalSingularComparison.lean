module

public import MMP.AlgebraicGeometry.Analytic.BorelMoore

/-!
# The complex realization is metrizable and locally contractible

Let `X` be a scheme separated, of finite type over `ℂ`. Its complex realization `X^an` is
homeomorphic to Fulton's underlying space `X(ℂ)`
(`MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace`), which is Hausdorff, weakly locally
compact, second countable and has a basis of contractible open neighbourhoods. A locally compact
Hausdorff space is regular, and a regular second countable space is metrizable; so `X^an` is
metrizable and strongly, hence classically, locally contractible. These are the hypotheses under
which sheaf cohomology of the constant sheaf on `X^an` is singular cohomology
(`MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology`).

## Main results

* `MMP.Analytic.ComplexPoints.metrizableSpace_and_stronglyLocallyContractibleSpace`.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace MMP.Analytic.ComplexPoints

/-- The complex realization of a separated scheme of finite type over `ℂ` is metrizable and
strongly locally contractible. -/
theorem metrizableSpace_and_stronglyLocallyContractibleSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] :
    MetrizableSpace (ComplexPoints sX) ∧ StronglyLocallyContractibleSpace (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : IsSeparated (X ↘ Spec (.of ℂ)) := ‹IsSeparated sX›
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have : QuasiCompact (X ↘ Spec (.of ℂ)) := ‹QuasiCompact sX›
  let e : ComplexPoints sX ≃ₜ UnderlyingSpace ℂ X := homeomorphUnderlyingSpace
  have : T2Space (UnderlyingSpace ℂ X) := UnderlyingSpace.t2Space_of_isSeparated X
  exact ⟨e.isEmbedding.metrizableSpace, e.isOpenEmbedding.stronglyLocallyContractibleSpace⟩

end MMP.Analytic.ComplexPoints
