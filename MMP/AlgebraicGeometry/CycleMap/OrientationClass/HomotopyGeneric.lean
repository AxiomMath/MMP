module

public import MMP.AlgebraicTopology.SingularCohomology.Relative
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomotopyInfraGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected

/-!
# Relative cohomology, connectedness of complex points, and change of support

This file proves that maps of relative singular cohomology compose elementwise, that the complex
points of a smooth complex variety form a connected space, and that the support cap product is
compatible with replacing the support by an equal set.

## Main results

* `MMP.relativeSingularCohomology.map_hom_map_hom`: composing two maps of relative singular
  cohomology, applied to an element.
* `MMP.UnderlyingSpace.connectedSpace_of_isSmoothVariety`: the complex points of a smooth complex
  variety form a connected space.
* `MMP.borelMooreHomology.capProductSupport_forget_of_eq`: for `Z = Z'`, the cap product with a
  class forgotten from support `Z` to `Z'` is the pushforward of the cap product along `Z ⊆ Z'`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2(c).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

namespace relativeSingularCohomology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- For maps of pairs `g : (Y'', A'') ⟶ (Y', A')` and `f : (Y', A') ⟶ (Y, A)`, applying the induced
map of `f` and then that of `g` to a relative cohomology class equals applying the map induced by
`g ≫ f`. -/
lemma map_hom_map_hom {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology R M Y A j) :
    (map R M g hg j).hom ((map R M f hf j).hom x) =
      (map R M (g ≫ f) (fun _ hx ↦ hf (hg hx)) j).hom x := by
  rw [map_comp]
  rfl

end relativeSingularCohomology

namespace UnderlyingSpace

/-- The complex points of a smooth complex variety form a connected space, provided they are
nonempty. -/
theorem connectedSpace_of_isSmoothVariety {T : Scheme.{0}} [T.Over (Spec (.of ℂ))]
    [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] (t : UnderlyingSpace ℂ T) :
    ConnectedSpace (UnderlyingSpace ℂ T) := by
  have h : regularPart ℂ T = Set.univ :=
    Set.eq_univ_of_forall fun p ↦ mem_regularPart_of_isSmoothVariety p
  have hp := isPreconnected_regularPart (X := T)
  rw [h] at hp
  exact connectedSpace_iff_univ.2 ⟨⟨t, trivial⟩, hp⟩

end UnderlyingSpace

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- **Changing the support to an equal set.** For `Z = Z'`, the cap product with
`c ∈ H^j(Y, Y - Z)` viewed in `H^j(Y, Y - Z')` is the cap product with `c` transported along
`Z ⊆ Z'`. -/
theorem capProductSupport_forget_of_eq (Y : TopCat.{u}) {Z Z' : Set Y} (h : Z = Z')
    (hZ : IsClosed Z) (hZ' : IsClosed Z') (hZd : HasProperNeighbourhoodDeformations Z)
    (hZ'd : HasProperNeighbourhoodDeformations Z') (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProductSupport R Y hZ' hZ'd j k
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y h.le j).hom c) a =
      (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset h.le)
        (isProperMap_subsetInclusionOfSubset hZ h.le) (k - j)).hom
        (capProductSupport R Y hZ hZd j k c a) := by
  subst h
  have e : subsetInclusionOfSubset (le_refl Z) = 𝟙 (TopCat.of Z) := rfl
  rw [show cohomologyWithSupports.forget R (ModuleCat.of R R) Y (le_refl Z) j = 𝟙 _ from
      cohomologyWithSupports.forget_refl R _ Y Z j,
    pushforward_congr' R e _ (by simpa using isProperMap_id), pushforward_id]
  rfl

end borelMooreHomology

end MMP
