module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks

/-!
# Algebraic Hartogs for functions and units on an open set

Let `X` be a normal integral locally Noetherian scheme (for instance a normal variety over a
field), `U ⊆ X` a nonempty open and `φ ∈ k(X)` a rational function. If
`ord_Γ φ ≥ 0` for every prime divisor `Γ` meeting `U`, then `φ` is regular on `U`: it is the image
of a section of `𝒪_X` over `U`. If moreover `φ ≠ 0` and all these orders vanish, then `φ` is the
image of an invertible section over `U`.

## Main results

* `MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord`: a rational
  function with nonnegative order along every prime divisor meeting `U` is regular on `U`.
* `MMP.Threefold.Bridges.exists_units_germToFunctionField_eq_of_forall_ord_eq_zero`: a nonzero
  rational function with order zero along every prime divisor meeting `U` is a unit on `U`.

## Implementation notes

The order `ord_Γ φ` is Mathlib's `AlgebraicGeometry.Scheme.ord` at the generic point of `Γ`; it
takes the junk value `0` at `φ = 0`, so the unit statement assumes `φ ≠ 0`, which in the source is
part of the hypothesis "all orders are zero" (the order of `0` being `+∞`).

Regularity on `U` is membership in the image of `Γ(X, U) → k(X)`, which requires `U ≠ ∅`; over
the empty open the statement is vacuous.

The proof is pointwise: at `x ∈ U`, every height-one prime of the Noetherian normal domain
`𝒪_{X,x}` is the centre of a prime divisor through `x`, which therefore meets `U`, so `φ` lies in
every height-one localization of `𝒪_{X,x}` and hence in `𝒪_{X,x}` (Stacks Tag 031T). The local
regular functions glue because `Γ(X, U) → k(X)` is injective.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [R. Hartshorne, *Algebraic geometry*][Har77], II.6.3A
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Threefold.Bridges

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- At a point `x`, a rational function with nonnegative order along every prime divisor through
`x` lies in the local ring `𝒪_{X,x}`. -/
theorem exists_algebraMap_stalk_eq_of_forall_zero_le_ord (x : X) {g : X.functionField}
    (hg : g ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → 0 ≤ X.ord g Γ.genericPoint) :
    ∃ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r = g := by
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  refine Stacks.AlgebraicGeometry.UnitsNormalProper.exists_algebraMap_eq_of_forall_height_eq_one
    X.functionField fun q hq => ?_
  have hξ1 : Order.coheight (X.fromSpecStalk x q) = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans hq
  set E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hξ1
  have hEξ : E.genericPoint = X.fromSpecStalk x q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hξ1
  have hspec : E.genericPoint ⤳ x := hEξ ▸ Stacks.Chow.specializes_fromSpecStalk x q
  have hxE : x ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hspec
  have hv : E.divisorialValuation g ≤ 1 := by
    rw [E.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h E hxE]
  obtain ⟨b, hb⟩ := (E.divisorialValuation_le_one_iff g).mp hv
  let := (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc := Stacks.Chow.isLocalization_stalk_of_specializes hspec q hEξ.symm
  obtain ⟨⟨a, s⟩, hab⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl b
  change IsLocalization.mk' E.localRing a s = b at hab
  refine ⟨a, s, s.2, ?_⟩
  have hspec' := IsLocalization.mk'_spec E.localRing a s
  rw [hab] at hspec'
  have h2 := congrArg (algebraMap E.localRing X.functionField) hspec'
  rw [map_mul, hb] at h2
  change g * algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom s) =
    algebraMap E.localRing X.functionField ((X.presheaf.stalkSpecializes hspec).hom a) at h2
  rwa [MMP.Mori.algebraMap_stalkSpecializes, MMP.Mori.algebraMap_stalkSpecializes] at h2

/-- **Algebraic Hartogs for functions.** On a normal integral locally Noetherian scheme `X`, a
rational function `φ` with `ord_Γ φ ≥ 0` along every prime divisor `Γ` meeting the nonempty open
`U` is regular on `U`: it is the image of a section of `𝒪_X` over `U`. -/
@[mmp "lem_mmp_threefold_normal_hartogs"]
theorem exists_germToFunctionField_eq_of_forall_zero_le_ord (U : X.Opens) [Nonempty U]
    (φ : X.functionField)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      0 ≤ X.ord φ Γ.genericPoint) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = φ := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, map_zero _⟩
  refine exists_germToFunctionField_eq_of_forall_mem_range X U φ fun x => ?_
  exact exists_algebraMap_stalk_eq_of_forall_zero_le_ord x.1 hφ fun Γ hΓ => h Γ ⟨x.1, hΓ, x.2⟩

/-- **Algebraic Hartogs for units.** On a normal integral locally Noetherian scheme `X`, a nonzero
rational function `φ` with `ord_Γ φ = 0` along every prime divisor `Γ` meeting the nonempty open
`U` is a unit on `U`: it is the image of an invertible section of `𝒪_X` over `U`. -/
@[mmp "lem_mmp_threefold_normal_hartogs"]
theorem exists_units_germToFunctionField_eq_of_forall_ord_eq_zero (U : X.Opens) [Nonempty U]
    {φ : X.functionField} (hφ : φ ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      X.ord φ Γ.genericPoint = 0) :
    ∃ s : Γ(X, U)ˣ, X.germToFunctionField U s = φ := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_zero_le_ord U φ fun Γ hΓ =>
    (h Γ hΓ).symm.le
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_forall_zero_le_ord U φ⁻¹ fun Γ hΓ => by
    have := MMP.Mori.ord_zpow Γ.genericPoint hφ (-1)
    rw [zpow_neg, zpow_one] at this
    rw [this, h Γ hΓ, mul_zero]
  have hab : a * b = 1 := X.germToFunctionField_injective U (by
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hφ])
  exact ⟨⟨a, b, hab, mul_comm b a ▸ hab⟩, ha⟩

end MMP.Threefold.Bridges
