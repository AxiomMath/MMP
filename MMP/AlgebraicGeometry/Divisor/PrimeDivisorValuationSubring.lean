module

public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The valuation ring of a prime divisor inside the function field

Let `X` be an integral, locally Noetherian, normal scheme and `E` a prime divisor on `X`. The
local ring `𝒪_{X,E}` at the generic point of `E` is a discrete valuation ring with fraction field
the function field `K(X)`; its image in `K(X)` is a valuation subring of `K(X)`. An element of
`K(X)` coming from the stalk at the generic point of the component of `E` lies in this valuation
subring exactly when its order of vanishing along `E` is non-negative.

## Main definitions

* `MMP.Mori.PrimeDivisor.valuationSubring`: the valuation subring `𝒪_{X,E}` of `K(X)`.

## Main results

* `MMP.Mori.PrimeDivisor.algebraMap_mem_valuationSubring_iff`: `f ∈ 𝒪_{X,E}` if and only if
  `v_E(f) ≥ 0`.
* `MMP.Mori.PrimeDivisor.valuationSubringEquiv`: `𝒪_{X,E}` is isomorphic to the stalk at the
  generic point of `E`, so it is a discrete valuation ring.
* `MMP.Mori.PrimeDivisor.finite_notMem_valuationSubring`: a nonzero element of `K(X)` is a unit
  of `𝒪_{X,E}` for all but finitely many `E`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori.PrimeDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (E : PrimeDivisor X)

/-- The valuation ring `𝒪_{X,E}` of a prime divisor `E`, as a valuation subring of the function
field `K(X)`: the image of the stalk at the generic point of `E`. -/
def valuationSubring : ValuationSubring X.functionField where
  toSubring := (algebraMap E.localRing X.functionField).range
  mem_or_inv_mem' x :=
    haveI := E.isDiscreteValuationRing_localRing
    ValuationRing.isInteger_or_isInteger E.localRing x

/-- An element of `K(X)` lies in `𝒪_{X,E}` if and only if it is the image of an element of the
stalk at the generic point of `E`. -/
theorem mem_valuationSubring_iff (x : X.functionField) :
    x ∈ E.valuationSubring ↔ ∃ a : E.localRing, algebraMap E.localRing X.functionField a = x :=
  Iff.rfl

/-- The valuation subring `𝒪_{X,E}` of `K(X)` is isomorphic to the stalk at the generic point
of `E`. -/
def valuationSubringEquiv : E.localRing ≃+* E.valuationSubring :=
  RingEquiv.ofBijective ((algebraMap E.localRing X.functionField).rangeRestrict)
    ⟨fun a b h => IsFractionRing.injective E.localRing X.functionField (congrArg Subtype.val h),
      (algebraMap E.localRing X.functionField).rangeRestrict_surjective⟩

/-- The valuation subring `𝒪_{X,E}` of `K(X)` is a discrete valuation ring. -/
instance isDiscreteValuationRing_valuationSubring : IsDiscreteValuationRing E.valuationSubring :=
  haveI := E.isDiscreteValuationRing_localRing
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.valuationSubringEquiv

@[simp]
theorem coe_valuationSubringEquiv_apply (a : E.localRing) :
    (E.valuationSubringEquiv a : X.functionField) = algebraMap E.localRing X.functionField a :=
  rfl

/-- The map `E.toComponent` from the stalk at the generic point of `E` to the stalk at the generic
point of the component of `E` commutes with the maps of both stalks to `K(X)`. -/
theorem algebraMap_toComponent (a : E.localRing) :
    algebraMap (X.presheaf.stalk (componentGenericPoint X E.component)) X.functionField
      (E.toComponent.hom a) = algebraMap E.localRing X.functionField a := by
  change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes _).hom a) =
    (X.presheaf.stalkSpecializes _).hom a
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

/-- **Membership in `𝒪_{X,E}` is non-negative order of vanishing along `E`.** -/
theorem algebraMap_mem_valuationSubring_iff
    (f : X.presheaf.stalk (componentGenericPoint X E.component)) :
    algebraMap _ X.functionField f ∈ E.valuationSubring ↔ E.OrdGE 0 f := by
  rw [mem_valuationSubring_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [← algebraMap_toComponent] at ha
    rw [← IsFractionRing.injective _ X.functionField ha]
    obtain rfl | ha0 := eq_or_ne a 0
    · exact Or.inl (map_zero _)
    · exact Or.inr (by simpa using E.one_le_valuation_toComponent ha0)
  · rintro (rfl | hf)
    · exact ⟨0, by simp⟩
    · obtain ⟨b, hb⟩ := E.exists_toComponent_eq_of_one_le_valuation (by simpa using hf)
      exact ⟨b, by rw [← algebraMap_toComponent, hb]⟩

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- For an irreducible component `Z`, the map from the stalk at the generic point of `Z` to the
function field `K(X)` is surjective. -/
theorem algebraMap_stalk_componentGenericPoint_surjective (Z : irreducibleComponents X) :
    Function.Surjective
      (algebraMap (X.presheaf.stalk (componentGenericPoint X Z)) X.functionField) :=
  letI := (RationalFunctions.isField_stalk X Z).toField
  IsFractionRing.surjective_iff_isField.mpr (RationalFunctions.isField_stalk X Z)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A nonzero element `x` of the function field comes from a unit `φ` of `RationalFunctions X`:
every component of `φ` maps to `x` in `K(X)`. -/
theorem exists_units_algebraMap_eq {x : X.functionField} (hx : x ≠ 0) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ Z : irreducibleComponents X,
      algebraMap _ X.functionField ((φ : RationalFunctions X) Z) = x := by
  choose a ha using fun Z => algebraMap_stalk_componentGenericPoint_surjective (X := X) Z x
  have hu : IsUnit (a : RationalFunctions X) := by
    refine Pi.isUnit_iff.mpr fun Z => ?_
    letI := (RationalFunctions.isField_stalk X Z).toField
    refine isUnit_iff_ne_zero.mpr fun h0 => hx ?_
    rw [← ha Z, h0, map_zero]
  exact ⟨hu.unit, ha⟩

/-- For a unit `φ` of `RationalFunctions X`, the image in `K(X)` of its component at `E` lies in
`𝒪_{X,E}` if and only if `0 ≤ ord_E φ`. -/
theorem algebraMap_units_mem_valuationSubring_iff (φ : (RationalFunctions X)ˣ) :
    algebraMap _ X.functionField ((φ : RationalFunctions X) E.component) ∈ E.valuationSubring ↔
      0 ≤ E.ord φ := by
  rw [algebraMap_mem_valuationSubring_iff, OrdGE, E.valuation_component, WithZero.exp_le_exp]
  exact or_iff_right (φ.isUnit.map (RationalFunctions.component X E.component)).ne_zero

/-- A nonzero element of the function field is a unit of `𝒪_{X,E}` for all but finitely many
prime divisors `E`. -/
theorem finite_notMem_valuationSubring [CompactSpace X] {x : X.functionField} (hx : x ≠ 0) :
    {E : PrimeDivisor X | x ∉ E.valuationSubring ∨ x⁻¹ ∉ E.valuationSubring}.Finite := by
  obtain ⟨φ, hφ⟩ := exists_units_algebraMap_eq hx
  refine (finite_ord_ne_zero φ).subset fun E hE h0 => ?_
  have h1 : x ∈ E.valuationSubring := by
    rw [← hφ E.component, algebraMap_units_mem_valuationSubring_iff, h0]
  have h2 : x⁻¹ ∈ E.valuationSubring := by
    have hinv : x⁻¹ = algebraMap _ X.functionField
        (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) E.component) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← hφ E.component, ← map_mul, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Pi.one_apply, map_one]
    rw [hinv, algebraMap_units_mem_valuationSubring_iff, ord_inv, h0, neg_zero]
  exact hE.elim (· h1) (· h2)

end MMP.Mori.PrimeDivisor
