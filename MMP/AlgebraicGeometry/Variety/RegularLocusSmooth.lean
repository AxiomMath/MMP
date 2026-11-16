module

public import MMP.AlgebraicGeometry.Properties.RegularLocus

/-!
# Smooth morphisms reflect regular points

Let `K` be a perfect field and `g : Z → Spec K` locally of finite type. If `f : Y → Z` is smooth
and `f y` is a regular point of `Z`, then `y` is a regular point of `Y`: the regular locus
`Z° ⊆ Z` is open and regular, hence smooth over `K`; so `f⁻¹(Z°)` is smooth over `K`, hence
regular, and it is an open subscheme of `Y`.

## Main results

* `MMP.mem_regularLocus_of_smooth`.

## References

* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S),
  [Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

/-- A smooth morphism `f : Y ⟶ Z` reflects regular points when `Z` is locally of finite type over
a perfect field: if `f y` is in the regular locus of `Z`, then `y` is in the regular locus
of `Y`. -/
theorem mem_regularLocus_of_smooth (K : Type u) [Field K] [PerfectField K] {Y Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [LocallyOfFiniteType g] (f : Y ⟶ Z) [Smooth f] (y : Y)
    (hy : f y ∈ regularLocus Z) : y ∈ regularLocus Y := by
  set U := MMP.regularLocusOpens K g
  have hU : Smooth (U.ι ≫ g) :=
    smooth_of_isRegular_over_perfectField (U.ι ≫ g) (MMP.isRegular_regularLocusOpens K g)
  have hfU : Smooth ((f ∣_ U) ≫ U.ι ≫ g) := inferInstance
  have hreg := isRegular_of_smooth_over_field ((f ∣_ U) ≫ U.ι ≫ g)
  have hy' : y ∈ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    exact hy
  obtain ⟨y', rfl⟩ := hy'
  refine (MMP.mem_regularLocus_iff_of_isOpenImmersion (f ⁻¹ᵁ U).ι y').mpr ?_
  have h12 := (isRegular_tfae (f ⁻¹ᵁ U).toScheme).out 1 2
  exact (h12.mp hreg).2 y'

end MMP
