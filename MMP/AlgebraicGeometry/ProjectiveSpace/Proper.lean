module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective spaces and their closed subschemes are proper

Every closed subscheme of `ℙ^ι_K` (`ι` finite; Fulton's `ℙⁿ_K` is `ι = ULift (Fin (n + 1))`) is
complete over `K`, and for every `K`-scheme `X` the projection `X ×_K ℙ^ι_K ⟶ X` is proper.

## Implementation notes

* Projective space is `MMP.Intersection.ProjSpace K ι` with structure morphism
  `MMP.Intersection.ProjSpace.toSpec K ι`; a closed subscheme is given by its ideal sheaf
  `Z : (ProjSpace K ι).IdealSheafData`, a `K`-scheme through `Z.subschemeι ≫ toSpec`.
  Completeness is `MMP.Intersection.IsComplete` (Fulton B.2.4).
* The product `X × ℙⁿ` is the fibre product over `Spec K` for any morphism `X ⟶ Spec K`; no
  separatedness or finiteness hypothesis is put on `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Resolution.Bridges

open MMP.Intersection (ProjSpace IsComplete)

variable (K : Type u) [Field K] (ι : Type u) [Finite ι]

attribute [local instance] MvPolynomial.gradedAlgebra in
omit [Finite ι] in
private theorem algebraMap_homogeneous_zero_bijective :
    Function.Bijective (algebraMap K (MvPolynomial.homogeneousSubmodule ι K 0)) := by
  refine ⟨fun a b h => MvPolynomial.C_injective _ _ (congrArg Subtype.val h), ?_⟩
  rintro ⟨x, hx⟩
  rw [MvPolynomial.mem_homogeneousSubmodule] at hx
  by_cases h0 : x = 0
  · exact ⟨0, Subtype.ext (by simp [h0])⟩
  · have := hx.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at this
    exact ⟨x.coeff 0, Subtype.ext (by simpa using this.symm)⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem isProper_projSpace_toSpec : IsProper (ProjSpace.toSpec K ι) := by
  have : IsIso (CommRingCat.ofHom
      (algebraMap K (MvPolynomial.homogeneousSubmodule ι K 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (algebraMap_homogeneous_zero_bijective K ι)
  unfold ProjSpace.toSpec
  infer_instance

/-- **Closed subschemes of projective space are complete.** Every closed subscheme `Z` of
`ℙ^ι_K` (`ι` finite) is complete over `K`, i.e. `Z ⟶ ℙ^ι_K ⟶ Spec K` is proper. -/
@[mmp "lem_mmp_foundation_fulton_projective_complete"]
theorem isComplete_subscheme_projSpace (Z : (ProjSpace K ι).IdealSheafData) :
    letI : Z.subscheme.Over (Spec (.of K)) := ⟨Z.subschemeι ≫ ProjSpace.toSpec K ι⟩
    IsComplete K Z.subscheme := by
  have := isProper_projSpace_toSpec K ι
  unfold MMP.Intersection.IsComplete
  change IsProper (Z.subschemeι ≫ ProjSpace.toSpec K ι)
  infer_instance

/-- **Projections from projective space are proper.** For every scheme `X` over `K`, the
projection `X ×_K ℙ^ι_K ⟶ X` (`ι` finite) is proper. -/
@[mmp "lem_mmp_foundation_fulton_projective_complete"]
theorem isProper_pullback_fst_projSpace {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) :
    IsProper (pullback.fst g (ProjSpace.toSpec K ι)) := by
  have := isProper_projSpace_toSpec K ι
  infer_instance

end MMP.Resolution.Bridges
