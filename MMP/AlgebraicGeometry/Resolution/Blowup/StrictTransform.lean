module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# The canonical lift along a closed immersion, and strict transforms of integral subschemes

For a closed immersion `j : S ⟶ X` and a closed subscheme `Z ⊆ X`, the canonical lift
`j̃_Z : B_{j⁻¹Z}S ⟶ B_ZX` is a closed immersion. If moreover `S` is integral and not contained in
`Z`, its image is the closure of `π⁻¹(S ∖ Z)` in `B_ZX` (`π = π_{Z,X}`), and the closed subscheme
it cuts out is the reduced induced structure on that closure: `B_{j⁻¹Z}S` is the birational
transform `π⁻¹_* S`.

## Main results

* `MMP.Resolution.Bridges.isClosedImmersion_canonicalLift`: the canonical lift of a closed
  immersion is a closed immersion.
* `MMP.Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal`: the image
  of `j̃_Z` is the closure of `π⁻¹(S ∖ Z)`, with its reduced structure.

## Implementation notes

The closed subscheme cut out by `j̃_Z` is its scheme-theoretic image, with ideal sheaf
`(canonicalLift j Z).ker`; "the closure with its reduced structure" is the vanishing ideal sheaf
`Scheme.IdealSheafData.vanishingIdeal` of that closed set. The source's hypothesis that `X` be
locally noetherian only restricts the domain and is dropped.

## References

* [R. Hartshorne, *Algebraic geometry*, II.7.15]
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace MMP.Resolution.Bridges

open MMP.Resolution (canonicalLift canonicalLift_comp_blowUpToBase
  exists_isClosedImmersion_canonicalLift_factor)

variable {X S : Scheme.{u}}

/-- **The induced map between blowups of a closed subscheme is a closed immersion.** For a
closed immersion `j : S ⟶ X` and a closed subscheme `Z ⊆ X`, the canonical lift
`j̃_Z : B_{j⁻¹Z}S ⟶ B_ZX` is a closed immersion. -/
@[mmp "lem_mmp_foundation_blowup_closed_subscheme_lift"]
theorem isClosedImmersion_canonicalLift (j : S ⟶ X) [IsClosedImmersion j]
    (Z : X.IdealSheafData) : IsClosedImmersion (canonicalLift j Z) := by
  obtain ⟨g, hg, -, hfst⟩ := exists_isClosedImmersion_canonicalLift_factor j Z
  rw [← hfst]
  infer_instance

/-- The image under the canonical lift of the locus off `j⁻¹Z` is `π⁻¹(S ∖ Z)`. -/
theorem image_canonicalLift_preimage_compl_support (j : S ⟶ X) (Z : X.IdealSheafData) :
    canonicalLift j Z '' (blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ) =
      blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)) := by
  have hsq : ∀ v, blowUpToBase Z (canonicalLift j Z v) = j (blowUpToBase (Z.comap j) v) :=
    fun v ↦ by rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
    rw [hsq v]
    simpa using hv
  · rintro ⟨⟨s, hs⟩, hyZ⟩
    have hs' : s ∉ ((Z.comap j).support : Set S) := by simpa [hs] using hyZ
    obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
    refine ⟨v, by simpa [hv] using hs', ?_⟩
    have hfv : blowUpToBase Z (canonicalLift j Z v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
    exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv

/-- **The blowup of an integral closed subscheme is its reduced strict transform.** Let
`Z ⊆ X` be a closed subscheme, `π = π_{Z,X}`, and `j : S ⟶ X` a closed immersion of an integral
scheme with `S ⊄ Z`. Then the image of the closed immersion `j̃_Z : B_{j⁻¹Z}S ⟶ B_ZX` is the
closure of `π⁻¹(S ∖ Z)` in `B_ZX`, and the closed subscheme it cuts out is that closure with its
reduced structure (the birational transform `π⁻¹_* S`). -/
@[mmp "lem_mmp_foundation_integral_strict_transform_blowup"]
theorem range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal (j : S ⟶ X)
    [IsClosedImmersion j] [IsIntegral S] (Z : X.IdealSheafData)
    (hSZ : ¬ Set.range j ⊆ (Z.support : Set X)) :
    Set.range (canonicalLift j Z) =
        closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))) ∧
      (canonicalLift j Z).ker = Scheme.IdealSheafData.vanishingIdeal
        (.closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)))) := by
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀⟩ := Set.not_subset.mp hSZ
  have hs₀' : s₀ ∉ ((Z.comap j).support : Set S) := by simpa using hs₀
  have : IsIntegral (blowUp (Z.comap j)) :=
    isIntegral_blowUp (Z.comap j) fun h ↦ hs₀' (by simp [h])
  have : IsClosedImmersion (canonicalLift j Z) := isClosedImmersion_canonicalLift j Z
  have hVdense : closure (blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ) =
      Set.univ := by
    obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs₀'
    exact ((Z.comap j).support.isClosed.isOpen_compl.preimage
      (blowUpToBase (Z.comap j)).continuous).dense ⟨v, by simpa [hv] using hs₀'⟩ |>.closure_eq
  have hrange : Set.range (canonicalLift j Z) =
      closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))) := by
    rw [← image_canonicalLift_preimage_compl_support]
    refine subset_antisymm ?_ ?_
    · rw [← Set.image_univ, ← hVdense]
      exact image_closure_subset_closure_image (canonicalLift j Z).continuous
    · exact closure_minimal (Set.image_subset_range _ _)
        (canonicalLift j Z).isClosedEmbedding.isClosed_range
  refine ⟨hrange, ?_⟩
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange]
  congr 1
  exact Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, closure_closure])

end MMP.Resolution.Bridges
