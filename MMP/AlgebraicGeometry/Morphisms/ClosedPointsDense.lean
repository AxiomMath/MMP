module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Opens containing all closed points of a scheme of finite type over a field

A scheme locally of finite type over a field is a Jacobson space: every nonempty locally closed
subset contains a closed point. Hence an open subset containing every closed point is everything,
and more generally a closed subset `C` with every closed point of `C` in an open `V` lies in `V`.

## Main results

* `MMP.Resolution.Bridges.subset_of_inter_closedPoints_subset`: in a Jacobson space, a closed `C`
  whose closed points lie in an open `V` is contained in `V`.
* `MMP.Resolution.Bridges.subset_of_closedPoints_subset_of_locallyOfFiniteType`,
  `MMP.Resolution.Bridges.eq_top_of_closedPoints_subset`: the statement for schemes locally of
  finite type over a field.

## Implementation notes

The source assumes `Y` of finite type over the field; local finite type is enough.
-/

@[expose] public section

universe u

open AlgebraicGeometry Topology

namespace MMP.Resolution.Bridges

/-- In a Jacobson space, a closed subset `C` whose closed points all lie in an open subset `V` is
contained in `V`: otherwise `C \ V` is a nonempty locally closed set, so it has a closed point. -/
theorem subset_of_inter_closedPoints_subset {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {C V : Set X} (hC : IsClosed C) (hV : IsOpen V) (h : C ∩ closedPoints X ⊆ V) : C ⊆ V := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints (Z := C \ V) (Set.diff_nonempty.2 hne)
    (hC.sdiff hV).isLocallyClosed
  exact hx.1.2 (h ⟨hx.1.1, hx.2⟩)

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **Closed subsets are detected on closed points.** Let `Y` be a scheme (locally) of finite type
over a field, `C ⊆ Y` closed and `V ⊆ Y` open with every closed point of `Y` lying in `C` also
lying in `V`. Then `C ⊆ V`. -/
@[mmp "lem_mmp_foundation_open_containing_all_closed_points"]
theorem subset_of_closedPoints_subset_of_locallyOfFiniteType (f : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {C : Set Y} (hC : IsClosed C)
    (V : Y.Opens) (h : C ∩ closedPoints Y ⊆ V) : C ⊆ V :=
  haveI := LocallyOfFiniteType.jacobsonSpace f
  subset_of_inter_closedPoints_subset hC V.isOpen h

/-- **An open containing every closed point is everything.** Let `Y` be a scheme (locally) of
finite type over a field and `V ⊆ Y` an open subset containing every closed point of `Y`. Then
`V = Y`. -/
@[mmp "lem_mmp_foundation_open_containing_all_closed_points"]
theorem eq_top_of_closedPoints_subset (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (V : Y.Opens) (h : closedPoints Y ⊆ V) : V = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  exact subset_of_closedPoints_subset_of_locallyOfFiniteType f isClosed_univ V
    (fun x hx => h hx.2) (Set.mem_univ y)

end MMP.Resolution.Bridges
