module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage

/-!
# An integral closed subscheme dominating the base of a modification

Let `π : Y ⟶ X` be proper, with `X` integral and Noetherian, and an isomorphism over a dense
open `U ⊆ X`. The scheme-theoretic image `X'` of the section `U ≅ π⁻¹(U) ⊆ Y` is an integral
closed subscheme of `Y`, and `X' ⟶ Y ⟶ X` is surjective. This is the step of Chow's lemma
([Stacks, Tag 0200]) that makes the modification integral.

## Main definitions

* `MMP.sectionOver`: the section `U ⟶ Y` of a morphism that is an isomorphism over `U`.

## Main results

* `MMP.exists_isIntegral_closedImmersion_surjective`: some integral closed subscheme of `Y`
  maps onto `X`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

variable {X Y : Scheme.{u}}

/-- The section `U ≅ π⁻¹(U) ⊆ Y` of a morphism `π : Y ⟶ X` that is an isomorphism over `U`. -/
def sectionOver (π : Y ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] : U.toScheme ⟶ Y :=
  inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι

/-- The section `sectionOver π U` composed with `π` is the open immersion `U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem sectionOver_comp (π : Y ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] :
    sectionOver π U ≫ π = U.ι := by
  rw [sectionOver, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- If `π : Y ⟶ X` is proper, `X` is integral and Noetherian, and `π` is an isomorphism over a
dense open `U`, then some integral closed subscheme `X'` of `Y` maps onto `X`: the
scheme-theoretic image of the section `U ⟶ Y`. -/
theorem exists_isIntegral_closedImmersion_surjective (π : Y ⟶ X) [IsProper π] [IsIntegral X]
    [IsNoetherian X] (U : X.Opens) (hU : Dense (U : Set X)) [IsIso (π ∣_ U)] :
    ∃ (X' : Scheme.{u}) (j : X' ⟶ Y), IsClosedImmersion j ∧ IsIntegral X' ∧
      Surjective (j ≫ π) := by
  have : Nonempty U := hU.nonempty.to_subtype
  let s := sectionOver π U
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian U.toScheme := ⟨⟩
  let p := s.imageι ≫ π
  have hgp : s.toImage ≫ p = U.ι := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, sectionOver_comp]
  refine ⟨s.image, s.imageι, inferInstance, Stacks.Chow.isIntegral_image s, ⟨fun x => ?_⟩⟩
  have hsub : (U : Set X) ⊆ Set.range p := by
    rw [← U.range_ι, ← hgp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  exact p.isClosedMap.isClosed_range.closure_subset_iff.mpr hsub (hU.closure_eq ▸ Set.mem_univ x)

end MMP
