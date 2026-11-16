module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction

/-!
# The complex points over a subset of a scheme

For a subset `T` of a scheme `X` over a field `K`, `pointsOver T ⊆ X(K)` is the set of `K`-points
whose image lies in `T`. It is closed when `T` is (`MMP.UnderlyingSpace.isClosed_pointsOver`), and
for `K = ℂ` and `T` closed it has bases of open contractible neighbourhoods and proper
neighbourhood deformations (`MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open MMP.UnderlyingSpace

namespace MMP

namespace UnderlyingSpace

section PointsOver

variable {K : Type} [Field K] {X : Scheme.{0}} [X.Over (Spec (.of K))]

/-- The points `T(K) ⊆ X(K)` of the underlying space lying over a subset `T` of the scheme `X`:
the `K`-points whose image lies in `T`. -/
def pointsOver (T : Set X) : Set (UnderlyingSpace K X) :=
  {p | p.toHom (IsLocalRing.closedPoint K) ∈ T}

/-- A point lies in `pointsOver T` if and only if its image lies in `T`. -/
lemma mem_pointsOver {T : Set X} {p : UnderlyingSpace K X} :
    p ∈ pointsOver T ↔ p.toHom (IsLocalRing.closedPoint K) ∈ T :=
  Iff.rfl

/-- `pointsOver` is monotone: `T ⊆ T'` implies `T(K) ⊆ T'(K)`. -/
lemma pointsOver_mono {T T' : Set X} (h : T ⊆ T') :
    pointsOver (K := K) T ⊆ pointsOver T' :=
  fun _ hp ↦ h hp

/-- `pointsOver` commutes with intersections: `(T ∩ T')(K) = T(K) ∩ T'(K)`. -/
lemma pointsOver_inter (T T' : Set X) :
    pointsOver (K := K) (T ∩ T') = pointsOver T ∩ pointsOver T' :=
  rfl

/-- The points of a closed immersion `i : Z → X` are the points over its image. -/
lemma range_map_of_isClosedImmersion [TopologicalSpace K] {Z : Scheme.{0}} [Z.Over (Spec (.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of K))] :
    Set.range (map (K := K) i) = pointsOver (Set.range i) :=
  range_mapFun_of_isClosedImmersion i

variable [TopologicalSpace K]

/-- `T(K)` is closed in `X(K)` when `T` is closed in `X`. -/
lemma isClosed_pointsOver {T : Set X} (hT : IsClosed T) :
    IsClosed (pointsOver (K := K) T) := by
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  convert (isOpen_setOf_le_preimage (K := K) U).isClosed_compl using 1
  ext p
  rw [Set.mem_compl_iff, Set.mem_setOf_eq, top_le_preimage_iff]
  simp [U, mem_pointsOver]

end PointsOver

/-- The complex points `T(ℂ)` of a closed subset `T` of a scheme `S` locally of finite type over
`ℂ` form a space with bases of open contractible neighbourhoods. -/
theorem hasOpenContractibleBasis_pointsOver (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (S ↘ Spec (.of ℂ))] (T : Closeds S) :
    HasOpenContractibleBasis (pointsOver (K := ℂ) (T : Set S)) := by
  let I := Scheme.IdealSheafData.vanishingIdeal T
  letI : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ S ↘ Spec (.of ℂ)⟩
  haveI : I.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (I.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ S ↘ Spec (.of ℂ)))
  have he := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) I.subschemeι
  have hr : Set.range (map (K := ℂ) I.subschemeι) = pointsOver (T : Set S) := by
    rw [range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (hasOpenContractibleBasis I.subscheme).of_homeomorph
    (he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr))

/-- **Fulton, §19.1.** For a closed subset `T` of a complex scheme `X`, the complex points
`T(ℂ) ⊆ X(ℂ)` have arbitrarily small proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_pointsOver (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (T : Closeds X) :
    HasProperNeighbourhoodDeformations (pointsOver (K := ℂ) (T : Set X)) :=
  hasProperNeighbourhoodDeformations X (isClosed_pointsOver T.isClosed)
    (hasOpenContractibleBasis_pointsOver X T)

end UnderlyingSpace

end MMP
