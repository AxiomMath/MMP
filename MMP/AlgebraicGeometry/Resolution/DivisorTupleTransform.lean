module

public import MMP.AlgebraicGeometry.Resolution.DivisorTuple

/-!
# Order-one transformations of ordered divisor tuples

For an ordered divisor tuple `(V, (I_1, …, I_m), E)` and a smooth centre `C` having normal
crossings with `E`, the order-one transformation under the blow-up `π : Bl_C V → V` with
blow-up divisor `F` replaces each `I_j` by `π^*I_j·𝒪(F)` when `C ⊆ cosupp I_j` and by `π^*I_j`
otherwise, and `E` by its total transform, adding `F` when it is a new boundary component.

## Main definitions

* `MMP.Resolution.OrderedDivisorTuple.transform`: the order-one transformation.
* `MMP.Resolution.OrderedDivisorTuple.IsTransformCentre`: `C` is smooth over `k` and has simple
  normal crossings with `E`.

## Implementation notes

`π^*I_j·𝒪(F)` is the ideal quotient `(π^*I_j : I_F)`, `I_F = π^*I_C`, the birational transform of
the marked ideal `(I_j, 1)` (`MMP.Resolution.MarkedIdeal.birationalTransform`); the total
transform of `E` is `MMP.Resolution.OrderedDivisor.totalTransform`, whose last entry is the
union of the `π⁻¹(C_i)` over the components `C_i` of `C` that are not components of `Supp E`.
The centre condition only restricts the domain and is a separate predicate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

namespace OrderedDivisorTuple

variable {V : Scheme.{u}} (T : OrderedDivisorTuple V)

/-- The *order-one transformation* of an ordered divisor tuple under the blow-up
`π : Bl_C V → V` of a centre `C` with blow-up divisor `F = π⁻¹(C)`: each `I_j` is replaced by
`π^*I_j·𝒪(F) = (π^*I_j : I_F)` when `C ⊆ cosupp I_j` and by `π^*I_j` otherwise, and `E` by its
total transform `π⁻¹_tot E`, which adds `F` as a new last entry when it is a new boundary
component. -/
@[mmp "def_mmp_divisor_tuple_transform"]
def transform (C : V.IdealSheafData) : OrderedDivisorTuple (blowUp C) where
  m := T.m
  I j := by
    classical
    exact if (C.support : Set V) ⊆ (T.I j).support then
      (MarkedIdeal.birationalTransform C ⟨T.I j, 1⟩).I
    else (T.I j).comap (blowUpToBase C)
  E := T.E.totalTransform C

/-- `C` is a centre of an order-one transformation of the tuple: `C` is smooth over `k` and has
simple normal crossings with the boundary `E`. -/
@[mmp "def_mmp_divisor_tuple_transform"]
def IsTransformCentre {k : Type u} [Field k] (sV : V ⟶ Spec (.of k)) (C : V.IdealSheafData) :
    Prop :=
  MMP.Mori.IsSmoothScheme (C.subschemeι ≫ sV) ∧ HasSNCWith T.E.E C

/-- If `C ⊆ cosupp I_j`, the `j`-th ideal of the order-one transformation is the ideal quotient
`(π^*I_j : π^*I_C)`. -/
theorem transform_I_of_le (C : V.IdealSheafData) (j : Fin T.m)
    (h : (C.support : Set V) ⊆ (T.I j).support) :
    (T.transform C).I j =
      idealColon ((T.I j).comap (blowUpToBase C)) (C.comap (blowUpToBase C)) := by
  simp [transform, h, MarkedIdeal.birationalTransform]

/-- If `C ⊄ cosupp I_j`, the `j`-th ideal of the order-one transformation is the pullback
`π^*I_j`. -/
theorem transform_I_of_not_le (C : V.IdealSheafData) (j : Fin T.m)
    (h : ¬ (C.support : Set V) ⊆ (T.I j).support) :
    (T.transform C).I j = (T.I j).comap (blowUpToBase C) := by
  simp [transform, h]

/-- The boundary of the order-one transformation is the total transform of `E`. -/
theorem transform_E (C : V.IdealSheafData) : (T.transform C).E = T.E.totalTransform C := rfl

end OrderedDivisorTuple

end MMP.Resolution
