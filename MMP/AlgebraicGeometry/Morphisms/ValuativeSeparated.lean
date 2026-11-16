module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Uniqueness in the valuative criterion over an affine base

Two morphisms `Spec R → Y`, for a valuation ring `R` with fraction field `L` and `Y` separated over
an affine scheme `Spec K`, agree as soon as they agree on `Spec L`
(`MMP.ext_of_isSeparated_of_valuationRing`, a consequence of Mathlib's
`IsSeparated.valuativeCriterion`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

variable {Y : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R] {L : Type u} [Field L]
  [Algebra R L] [IsFractionRing R L]

/-- Two morphisms `Spec R → Y`, for a valuation ring `R` with fraction field `L`, to a separated
scheme `Y` over `Spec K` agree as soon as they agree on `Spec L`. -/
theorem ext_of_isSeparated_of_valuationRing (K : Type u) [CommRing K] [Y.Over (Spec (.of K))]
    [IsSeparated (Y ↘ Spec (.of K))] [ValuationRing R] (l l' : Spec (.of R) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l') : l = l' := by
  set p := Y ↘ Spec (.of K)
  have hp : l ≫ p = l' ≫ p := by
    rw [← Spec.map_preimage (l ≫ p), ← Spec.map_preimage (l' ≫ p)]
    congr 1
    have h' : Spec.map (Spec.preimage (l ≫ p) ≫ CommRingCat.ofHom (algebraMap R L)) =
        Spec.map (Spec.preimage (l' ≫ p) ≫ CommRingCat.ofHom (algebraMap R L)) := by
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
        reassoc_of% h]
    ext t
    exact IsFractionRing.injective R L (congrArg (fun g => g.hom t) (Spec.map_inj.mp h'))
  let S : ValuativeCommSq p :=
    ⟨R, L, Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l, l ≫ p, ⟨by simp⟩⟩
  have hu : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion p S
  exact congrArg CommSq.LiftStruct.l (hu.elim ⟨l, rfl, rfl⟩ ⟨l', h.symm, hp.symm⟩)

end MMP
