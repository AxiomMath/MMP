module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Proper neighbourhood deformations in the deformation of Fulton's Theorem 19.2

The cap products in the proof of Fulton's Theorem 19.2
(`pushforward_interFibre_capProductSupportPullback_eq_of_isRegularImbeddingOrientationClass`) are
taken along closed subsets of `M(ℂ)` for a complex scheme `M` with a morphism `ρ : M → T` and a
closed immersion `e : W → M`: the range `A` of `e`, the fibres `M_s = ρ⁻¹ s`, the intersections
`A ∩ M_s`, and `A ∩ M_s` read inside `M_s` or inside `A`. All of them are the complex points of
closed subsets of `M`, read inside the complex points of another closed subset, and these have
arbitrarily small proper neighbourhood deformations: the complex points of a closed subset of `M`
form a locally contractible space (the underlying space of the reduced closed subscheme on it),
with a closed imbedding in some `ℝᴺ` through `M(ℂ)`.

## Main results

* `MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_pointsOver`:
  `A(ℂ)` inside `Z(ℂ)`, for closed subsets `Z`, `A` of a complex scheme.
* `MMP.UnderlyingSpace.preimage_map_singleton`: the fibre of `ρ(ℂ)` over `s` is the
  set of complex points over the scheme-theoretic fibre over the closed point `s`.
* `MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_trivialFamily`: the five
  hypotheses `hAd`, `hZd`, `hAZd`, `hd₁`, `hd₂` of
  `pushforward_interFibre_capProductSupportPullback_eq_of_isRegularImbeddingOrientationClass`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set

namespace MMP

namespace UnderlyingSpace

open borelMooreHomology

/-- For closed subsets `Z`, `A` of a complex scheme `S`, the complex points of `A`, read inside the
complex points of `Z`, have arbitrarily small proper neighbourhood deformations in `Z(ℂ)`. -/
theorem hasProperNeighbourhoodDeformations_preimage_pointsOver (S : Scheme.{0})
    [S.Over (Spec (.of ℂ))] [IsComplexScheme S] (Z A : Closeds S) :
    HasProperNeighbourhoodDeformations
      (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ S)) (pointsOver (Z : Set S)) ⁻¹'
        pointsOver (K := ℂ) (A : Set S)) := by
  obtain ⟨-, N, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  let e : ((Subtype.val ⁻¹' pointsOver (K := ℂ) (A : Set S) :
        Set (pointsOver (K := ℂ) (Z : Set S)))) ≃ₜ
      (pointsOver (K := ℂ) ((Z ⊓ A : Closeds S) : Set S)) :=
    { toFun := fun z ↦ ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact hasProperNeighbourhoodDeformations_of_isClosedEmbedding
    (hF.comp (isClosed_pointsOver (K := ℂ) Z.isClosed).isClosedEmbedding_subtypeVal)
    ((isClosed_pointsOver (K := ℂ) A.isClosed).preimage continuous_subtype_val)
    ((hasOpenContractibleBasis_pointsOver S (Z ⊓ A)).of_homeomorph e.symm)
    (hasOpenContractibleBasis_pointsOver S Z)

variable {M T : Scheme.{0}} [M.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]

/-- The fibre of `ρ(ℂ) : M(ℂ) → T(ℂ)` over a point `s` is the set of complex points of `M` over
the scheme-theoretic fibre `ρ⁻¹(s)` of the closed point `s` of `T`. -/
lemma preimage_map_singleton [LocallyOfFiniteType (T ↘ Spec (.of ℂ))] (ρ : M ⟶ T)
    [ρ.IsOver (Spec (.of ℂ))] (s : UnderlyingSpace ℂ T) :
    map (K := ℂ) ρ ⁻¹' {s} =
      pointsOver (ρ.base ⁻¹' {s.toHom (IsLocalRing.closedPoint ℂ)}) := by
  ext p
  simp only [mem_preimage, mem_singleton_iff, mem_pointsOver]
  rw [← (equivClosedPoints (K := ℂ) T).injective.eq_iff, ← Subtype.coe_inj,
    equivClosedPoints_apply, equivClosedPoints_apply]
  rfl

/-- The scheme-theoretic fibre `ρ⁻¹(s)` over a complex point `s` of `T`, as a closed subset of
`M`. -/
def fibreCloseds [LocallyOfFiniteType (T ↘ Spec (.of ℂ))] (ρ : M ⟶ T)
    (s : UnderlyingSpace ℂ T) : Closeds M :=
  ⟨ρ.base ⁻¹' {s.toHom (IsLocalRing.closedPoint ℂ)},
    ((equivClosedPoints (K := ℂ) T s).2.preimage ρ.base.hom.continuous)⟩

/-- The underlying set of `fibreCloseds ρ s` is the preimage under `ρ` of the closed point `s`
of `T`. -/
@[simp]
lemma coe_fibreCloseds [LocallyOfFiniteType (T ↘ Spec (.of ℂ))] (ρ : M ⟶ T)
    (s : UnderlyingSpace ℂ T) :
    (fibreCloseds ρ s : Set M) = ρ.base ⁻¹' {s.toHom (IsLocalRing.closedPoint ℂ)} :=
  rfl

/-- **The proper-neighbourhood-deformation hypotheses of Fulton's Theorem 19.2.** For a complex
scheme `M`, a morphism `ρ : M → T` over `ℂ` to a scheme locally of finite type over `ℂ`, and a
closed immersion `e : W → M` over `ℂ`, with `A = e(W(ℂ))` and `M_s = ρ(ℂ)⁻¹ s`: the sets `A`,
`M_s`, `A ∩ M_s`, `A` inside `M_s` and `M_s` inside `A` have arbitrarily small proper
neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_trivialFamily [IsComplexScheme M]
    [LocallyOfFiniteType (T ↘ Spec (.of ℂ))] {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    (e : W ⟶ M) [IsClosedImmersion e] [e.IsOver (Spec (.of ℂ))]
    (ρ : M ⟶ T) [ρ.IsOver (Spec (.of ℂ))] :
    HasProperNeighbourhoodDeformations (range (UnderlyingSpace.map (K := ℂ) e)) ∧
    (∀ s, HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s})) ∧
    (∀ s, HasProperNeighbourhoodDeformations
      (range (UnderlyingSpace.map (K := ℂ) e) ∩ (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s})) ∧
    (∀ s, HasProperNeighbourhoodDeformations
      (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}) ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) e))) ∧
    (∀ s, HasProperNeighbourhoodDeformations
      (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
        (range (UnderlyingSpace.map (K := ℂ) e)) ⁻¹'
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}))) := by
  let E : Closeds M := ⟨range e, e.isClosedEmbedding.isClosed_range⟩
  have hE : range (UnderlyingSpace.map (K := ℂ) e) = pointsOver (E : Set M) :=
    range_map_of_isClosedImmersion e
  have hF : ∀ s, ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}) =
      pointsOver (fibreCloseds ρ s : Set M) :=
    fun s ↦ preimage_map_singleton ρ s
  refine ⟨?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩
  · rw [hE]
    exact hasProperNeighbourhoodDeformations_pointsOver M E
  · rw [hF s]
    exact hasProperNeighbourhoodDeformations_pointsOver M _
  · rw [hE, hF s, ← pointsOver_inter]
    exact hasProperNeighbourhoodDeformations_pointsOver M (E ⊓ fibreCloseds ρ s)
  · rw [hE, hF s]
    exact hasProperNeighbourhoodDeformations_preimage_pointsOver M _ E
  · rw [hE, hF s]
    exact hasProperNeighbourhoodDeformations_preimage_pointsOver M E _

end UnderlyingSpace

end MMP
