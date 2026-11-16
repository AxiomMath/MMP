module

public import MMP.AlgebraicGeometry.Variety.ParameterPoint
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.DeformationNeighbourhood

/-!
# Complex points of the fibre over a parameter point

Let `f : V → T` be a morphism of schemes over `ℂ`, with `T` locally of finite type, and let `t`
be a parameter point of `T`, with complex point `t ∈ T(ℂ)`. The complex points of the
scheme-theoretic fibre `V_t = f⁻¹(t)` map by a closed embedding into `f⁻¹(t) ⊆ V(ℂ)`, which
has arbitrarily small proper neighbourhood deformations.

## Main definitions

* `MMP.ParameterPoint.complexPoint`: the complex point of a parameter point.
* `MMP.ParameterPoint.fibreComplexPointsHom`: `V_t(ℂ) → f⁻¹(t) ⊆ V(ℂ)`.

## Main results

* `MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_singleton`.
* `MMP.ParameterPoint.isClosedEmbedding_fibreComplexPointsHom`.
* `MMP.ParameterPoint.isProperMap_fibreComplexPointsHom`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open MMP.UnderlyingSpace

namespace MMP

/-- The scheme-theoretic fibre of a morphism from a complex scheme is a complex scheme. -/
instance ParameterPoint.isComplexScheme_fibre {V T : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] (f : V ⟶ T) (t : ParameterPoint T) :
    IsComplexScheme (ParameterPoint.fibre f t) :=
  IsComplexScheme.of_isClosedImmersion (ParameterPoint.fibreι f t)

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [LocallyOfFiniteType (T ↘ Spec (.of ℂ))]
variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] (f : V ⟶ T) [f.IsOver (Spec (.of ℂ))]

namespace UnderlyingSpace

/-- Two complex points of `T` are equal if and only if they have the same image point in `T`. -/
lemma eq_iff_toHom_closedPoint_eq {p q : UnderlyingSpace ℂ T} :
    p = q ↔ p.toHom (IsLocalRing.closedPoint ℂ) = q.toHom (IsLocalRing.closedPoint ℂ) := by
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ (equivClosedPoints T).injective (Subtype.ext ?_)⟩
  rw [equivClosedPoints_apply, equivClosedPoints_apply, h]

/-- The fibre `f⁻¹(y) ⊆ V(ℂ)` of the map on complex points has arbitrarily small proper
neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_preimage_singleton [IsComplexScheme V]
    (y : UnderlyingSpace ℂ T) :
    HasProperNeighbourhoodDeformations ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {y}) := by
  change HasProperNeighbourhoodDeformations (map (K := ℂ) f ⁻¹' {y})
  rw [preimage_map_singleton]
  exact hasProperNeighbourhoodDeformations_pointsOver V (fibreCloseds f y)

end UnderlyingSpace

namespace ParameterPoint

/-- The complex point `t ∈ T(ℂ)` corresponding to a parameter point `t` of `T`. -/
def complexPoint (t : ParameterPoint T) : UnderlyingSpace ℂ T :=
  (equivClosedPoints T).symm ⟨t.point, t.isClosed_point⟩

/-- The complex point of a parameter point `t` has image point `t.point` in `T`. -/
@[simp]
lemma complexPoint_toHom_closedPoint (t : ParameterPoint T) :
    t.complexPoint.toHom (IsLocalRing.closedPoint ℂ) = t.point := by
  rw [← equivClosedPoints_apply, complexPoint, Equiv.apply_symm_apply]

variable (t : ParameterPoint T)

/-- A complex point of the fibre `V_t` maps into `f⁻¹(t) ⊆ V(ℂ)`. -/
lemma map_fibreι_mem_preimage (p : UnderlyingSpace ℂ (fibre f t)) :
    map (K := ℂ) (fibreι f t) p ∈ (TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {t.complexPoint} := by
  change map (K := ℂ) (fibreι f t) p ∈ map (K := ℂ) f ⁻¹' {t.complexPoint}
  rw [preimage_map_singleton, mem_pointsOver, complexPoint_toHom_closedPoint]
  exact (range_fibreι f t).subset ⟨_, rfl⟩

/-- The map `V_t(ℂ) → f⁻¹(t) ⊆ V(ℂ)` from the complex points of the scheme-theoretic fibre. -/
def fibreComplexPointsHom :
    TopCat.of (UnderlyingSpace ℂ (fibre f t)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {t.complexPoint}) :=
  TopCat.ofHom ⟨fun p ↦ ⟨map (K := ℂ) (fibreι f t) p, map_fibreι_mem_preimage f t p⟩,
    (map (K := ℂ) (fibreι f t)).continuous.subtype_mk _⟩

/-- The underlying point of `fibreComplexPointsHom f t p` is the image of `p` under the fibre
inclusion. -/
@[simp]
lemma coe_fibreComplexPointsHom_apply (p : UnderlyingSpace ℂ (fibre f t)) :
    (fibreComplexPointsHom f t p : UnderlyingSpace ℂ V) = map (K := ℂ) (fibreι f t) p :=
  rfl

/-- Composing `V_t(ℂ) → f⁻¹(t)` with the inclusion `f⁻¹(t) ⊆ V(ℂ)` gives the map on complex
points induced by the fibre inclusion `V_t → V`. -/
lemma fibreComplexPointsHom_comp_subsetInclusion :
    fibreComplexPointsHom f t ≫ borelMooreHomology.subsetInclusion
        ((TopCat.ofHom (map (K := ℂ) f)).hom ⁻¹' {t.complexPoint}) =
      TopCat.ofHom (map (K := ℂ) (fibreι f t)) :=
  rfl

/-- The map `V_t(ℂ) → f⁻¹(t) ⊆ V(ℂ)` is a closed embedding. -/
lemma isClosedEmbedding_fibreComplexPointsHom :
    Topology.IsClosedEmbedding (fibreComplexPointsHom f t) :=
  Topology.IsClosedEmbedding.of_comp (f := fibreComplexPointsHom f t)
    Topology.IsEmbedding.subtypeVal
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (fibreι f t))

/-- The map `V_t(ℂ) → f⁻¹(t) ⊆ V(ℂ)` is proper. -/
lemma isProperMap_fibreComplexPointsHom : IsProperMap (fibreComplexPointsHom f t) :=
  (isClosedEmbedding_fibreComplexPointsHom f t).isProperMap

end ParameterPoint

end MMP
