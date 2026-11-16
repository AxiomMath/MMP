module

public import MMP.AlgebraicGeometry.Morphisms.PointLocalHom

/-!
# Roots of regular functions at the points of a cover

Let `R` be an integrally closed local domain with fraction field `L`. An element `λ ∈ L` whose
`N`-th power (`N ≥ 1`) lies in `R` lies in `R`; if the power lies in the maximal ideal, so does
`λ`. At a point `y` of a normal integral scheme `Y` with a dominant morphism `f : Y ⟶ X`,
`f y = x`, this applies to `λ` with `λ^N = f^* a`, `a ∈ 𝒪_{X,x}`: the pull-back of `a` is the
image of `a` under the local homomorphism `𝒪_{X,x} → 𝒪_{Y,y}`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_of_pow_eq`: roots in an
  integrally closed local domain.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_stalk_eq_of_pow_eq_functionFieldMap`: roots of
  pull-backs at a point of a cover.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- **Roots in an integrally closed local domain.** If `x ∈ L` satisfies `x ^ N = a` with
`a ∈ R` and `N ≠ 0`, then `x` is the image of some `r ∈ R`, and `r` lies in the maximal ideal if
`a` does. -/
theorem exists_algebraMap_eq_of_pow_eq {R L : Type*} [CommRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] [Field L] [Algebra R L] [IsFractionRing R L] {N : ℕ} (hN : N ≠ 0)
    {x : L} {a : R} (hx : x ^ N = algebraMap R L a) :
    ∃ r : R, algebraMap R L r = x ∧ (a ∈ maximalIdeal R → r ∈ maximalIdeal R) := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (Nat.pos_of_ne_zero hN) (hx ▸ isIntegral_algebraMap)
  refine ⟨r, hr, fun ha => ?_⟩
  have hrN : r ^ N = a :=
    IsFractionRing.injective R L (by rw [map_pow, hr, hx])
  rw [← hrN] at ha
  exact (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem N ha

/-- **Roots of pull-backs at a point of a cover.** Let `f : Y ⟶ X` be dominant, `Y` normal, and
`f y = x`. An element `λ` of the function field of `Y` with `λ^N = f^* a`, `a ∈ 𝒪_{X,x}`, is the
image of an element of `𝒪_{Y,y}`, in the maximal ideal if `a` is. -/
theorem exists_stalk_eq_of_pow_eq_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f] {y : Y} {x : X} (h : f y = x)
    {N : ℕ} (hN : N ≠ 0) {lam : Y.functionField} {a : X.presheaf.stalk x}
    (hlam : lam ^ N =
      AlgebraicGeometry.functionFieldMap f (algebraMap (X.presheaf.stalk x) X.functionField a)) :
    ∃ r : Y.presheaf.stalk y, algebraMap (Y.presheaf.stalk y) Y.functionField r = lam ∧
      (a ∈ maximalIdeal (X.presheaf.stalk x) → r ∈ maximalIdeal (Y.presheaf.stalk y)) := by
  have : IsIntegrallyClosed (Y.presheaf.stalk y) := IsNormal.stalk_normal y
  rw [← algebraMap_placeHom f h] at hlam
  obtain ⟨r, hr, hm⟩ := exists_algebraMap_eq_of_pow_eq hN hlam
  exact ⟨r, hr, fun ha => hm (map_nonunit (placeHom f h).hom a ha)⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
