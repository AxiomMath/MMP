module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme

/-!
# Normalization of an integral scheme

The relative normalization `AlgebraicGeometry.Scheme.normalization` of a scheme `X` in the
canonical morphism to `X` from the spectra of the residue fields at its generic points needs every
quasi-compact open of `X` to have finitely many irreducible components. An integral scheme has one
generic point `η`, so the source of that morphism is `Spec R(X)`, `R(X) = κ(η)`.

## Main results

* `MMP.finite_irreducibleComponents_of_isIntegral`: every open of an integral scheme has at most
  one irreducible component, the hypothesis of `AlgebraicGeometry.Scheme.normalization`.
* `MMP.specFunctionFieldToGenericPointResidueSpectrum`: the inclusion of `Spec R(X)` into the
  coproduct of the spectra of the residue fields at the generic points, an isomorphism.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace MMP

/-- Every open of an integral scheme has finitely many irreducible components: at most one. -/
theorem finite_irreducibleComponents_of_isIntegral (X : Scheme.{u}) [IsIntegral X] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  cases isEmpty_or_nonempty U with
  | inl hU =>
      rw [Set.finite_def]
      exact ⟨⟨∅, fun C ↦ isEmptyElim C.2.1.nonempty.some⟩⟩
  | inr hU =>
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _

variable (X : Scheme.{u}) [IsIntegral X]

/-- The generic point of an integral scheme, as an element of the set of its generic points. -/
def genericPointOfIsIntegral : genericPoints X :=
  ⟨genericPoint X, by rw [genericPoints_eq_singleton]; rfl⟩

/-- An integral scheme has exactly one generic point. -/
@[instance_reducible]
def uniqueGenericPointsOfIsIntegral : Unique (genericPoints X) where
  default := genericPointOfIsIntegral X
  uniq η := by
    have h : genericPoints X = {genericPoint X} := genericPoints_eq_singleton
    exact Subtype.ext (Set.mem_singleton_iff.mp (h ▸ η.2))

/-- The inclusion of `Spec R(X)` into the coproduct of the spectra of the residue fields at the
generic points of an integral scheme `X`. -/
def specFunctionFieldToGenericPointResidueSpectrum :
    Spec (X.residueField (genericPoint X)) ⟶ X.genericPointResidueSpectrum :=
  Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
    (genericPointOfIsIntegral X)

/-- An integral scheme has one generic point, so `Spec R(X)` is the whole coproduct. -/
instance isIso_specFunctionFieldToGenericPointResidueSpectrum :
    IsIso (specFunctionFieldToGenericPointResidueSpectrum X) := by
  letI := uniqueGenericPointsOfIsIntegral X
  have := coproductUniqueIso_inv (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
  unfold specFunctionFieldToGenericPointResidueSpectrum
  rw [show Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
    (genericPointOfIsIntegral X) = _ from this.symm]
  exact Iso.isIso_inv _

/-- The inclusion of `Spec R(X)` followed by the canonical morphism to `X` is the canonical
morphism `Spec κ(η) ⟶ X` at the generic point. -/
@[reassoc]
theorem specFunctionFieldToGenericPointResidueSpectrum_comp :
    specFunctionFieldToGenericPointResidueSpectrum X ≫ X.fromGenericPointResidueFields =
      X.fromSpecResidueField (genericPoint X) :=
  Scheme.genericPointResidueSpectrum_ι_fromGenericPointResidueFields X
    (genericPointOfIsIntegral X)

end MMP
