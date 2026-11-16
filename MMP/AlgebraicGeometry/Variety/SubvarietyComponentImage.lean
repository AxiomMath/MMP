module

public import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Irreducible components as subvarieties, and the support of an image subvariety

## Main definitions

* `MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent`: an irreducible component of a
  scheme with its reduced induced structure, as a subvariety.

## Main results

* `MMP.Intersection.Scheme.Subvariety.support_image_eq_closure_genericPoint`: the support of the
  image subvariety `\overline{f(V)}` is the closure of the image of the generic point of `V`.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Intersection.Scheme.Subvariety

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- An irreducible component `Z` of a scheme `X` with its reduced induced closed subscheme
structure, as a subvariety of `X`. -/
def ofIrreducibleComponent (Z : irreducibleComponents X) : Subvariety X :=
  ofIrreducibleCloseds ⟨Z.1, Z.2.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩

/-- The ideal sheaf of the subvariety of a component `Z` is the vanishing ideal of `Z`. -/
@[simp]
theorem ideal_ofIrreducibleComponent (Z : irreducibleComponents X) :
    (ofIrreducibleComponent Z).ideal =
      .vanishingIdeal ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩ := rfl

/-- The support of the subvariety of a component is the component. -/
@[simp]
theorem support_ofIrreducibleComponent (Z : irreducibleComponents X) :
    (ofIrreducibleComponent Z).support = Z.1 :=
  support_ofIrreducibleCloseds _

/-- The closure of the generic point of the subvariety of a component is the component. -/
theorem closure_genericPoint_ofIrreducibleComponent (Z : irreducibleComponents X) :
    closure {(ofIrreducibleComponent Z).genericPoint} = Z.1 := by
  rw [closure_genericPoint, support_ofIrreducibleComponent]

/-- The support of the image subvariety `\overline{f(V)}` is the closure of `f '' V`. -/
theorem support_image (V : Subvariety X) (f : X ⟶ Y) :
    (V.image f).support = closure (f '' V.support) :=
  AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The support of the image subvariety `\overline{f(V)}` is the closure of the image of the
generic point of `V`. -/
theorem support_image_eq_closure_genericPoint (V : Subvariety X) (f : X ⟶ Y) :
    (V.image f).support = closure {f V.genericPoint} := by
  rw [← closure_genericPoint, genericPoint_image]

end MMP.Intersection.Scheme.Subvariety
