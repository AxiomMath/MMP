module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksClass
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic

/-!
# An orientation datum gives an orientation class, for Stacks vector bundles

Let `D = (ℰ, σ, V, Q)` be orientation data of a closed imbedding `i : X → Y` of complex schemes
(`MMP.Modules.RegularImbeddingOrientationDatum`). The Thom class `u_Q` of `Q` exists
(Thom's theorem, `MMP.ThomClass.existsUnique_isThomClass`), and since `X(ℂ)` is closed in `Y(ℂ)`
and `V ⊇ X(ℂ)` is open, restriction `H^{2d}(Y, Y - X) → H^{2d}(V, V - X)` is an isomorphism
(excision); so the class corresponding to `σ̄^* u_Q` is an orientation class of `i`.

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.isRegularImbeddingOrientationClass_inv`:
  the class `excision⁻¹ (σ̄^* u_Q)` is an orientation class.
* `MMP.Modules.RegularImbeddingOrientationDatum.exists_isRegularImbeddingOrientationClass`:
  an orientation datum gives an orientation class.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle

namespace MMP.Modules

open UnderlyingSpace

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ} (R : Type) [CommRing R]

/-- For a closed immersion `i : X ⟶ Y`, the image of `X(ℂ)` in `Y(ℂ)` is closed. -/
lemma isClosed_range_map [IsClosedImmersion i] :
    IsClosed (range (UnderlyingSpace.map (K := ℂ) i)) :=
  (isClosedEmbedding_map_of_isClosedImmersion i).isClosed_range

/-- The excision isomorphism `H^{2d}(Y, Y - X) ≅ H^{2d}(V, V - X)` of an orientation datum. -/
def excision [IsClosedImmersion i] (D : RegularImbeddingOrientationDatum i d) :=
  cohomologyWithSupports.excisionIso R (Y := TopCat.of (UnderlyingSpace ℂ Y)) D.isOpen_nbhd
    isClosed_range_map D.range_subset_nbhd (2 * d : ℕ)

/-- The forward map of the excision isomorphism is restriction from `(Y, Y - X)` to
`(V, V - X)`. -/
lemma excision_hom [IsClosedImmersion i] (D : RegularImbeddingOrientationDatum i d) :
    (D.excision R).hom = excisionRestrict R _ D.nbhd _ :=
  rfl

/-- The class corresponding under excision to `σ̄^* u_Q` is an orientation class. -/
theorem isRegularImbeddingOrientationClass_inv [IsClosedImmersion i]
    (D : RegularImbeddingOrientationDatum i d) :
    IsRegularImbeddingOrientationClass R i d
      ((D.excision R).inv.hom ((D.thomPullback R).hom (MMP.ThomClass.thomClass R D.F D.Q))) := by
  refine ⟨D, MMP.ThomClass.thomClass R D.F D.Q, MMP.ThomClass.isThomClass_thomClass D.F D.Q, ?_⟩
  change (D.excision R).hom.hom ((D.excision R).inv.hom _) = _
  exact Iso.inv_hom_id_apply (D.excision R) _

/-- **Existence of orientation classes**: an orientation datum gives an orientation class. -/
theorem exists_isRegularImbeddingOrientationClass [IsClosedImmersion i]
    (D : RegularImbeddingOrientationDatum i d) :
    ∃ u, IsRegularImbeddingOrientationClass R i d u :=
  ⟨_, D.isRegularImbeddingOrientationClass_inv R⟩

end RegularImbeddingOrientationDatum

end MMP.Modules
