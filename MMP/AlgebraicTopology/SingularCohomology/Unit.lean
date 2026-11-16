module

public import MMP.AlgebraicTopology.SingularCohomology.Contractible
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison

/-!
# The unit class of singular cohomology

For a space `Y` and a commutative ring `R`, the constant `0`-cochain with value `1` is a cocycle:
its coboundary on a singular `1`-simplex is `1 - 1 = 0`, and it vanishes on the simplices of the
empty set. Its class is the unit `1 ∈ H^0 Y = H^0(Y, Y - Y; R)`.

## Main definitions

* `MMP.cohomologyWithSupports.one`: the unit `1 ∈ H^0 Y`.

## Main results

* `MMP.cohomologyWithSupports.relativeSingularCohomologyEquiv_one`: `1` is the
  class of the constant cocycle `1`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u

namespace MMP

open SingularCochain PoincareAlexander

variable (R : Type u) [CommRing R]

namespace cohomologyWithSupports

variable {R} in
/-- The constant `0`-cochain `1` is a cocycle of `Y` relative to `Y - Y = ∅`. -/
lemma constCochain_one_mem_relCocycles_compl_univ (Y : TopCat.{u}) :
    constCochain (Z := Y) 0 (1 : R) ∈ relCocycles R (Set.univᶜ : Set Y) 0 := by
  rw [compl_univ]
  exact constCochain_zero_mem_relCocycles 1

/-- The unit `1 ∈ H^0 Y`, as a class with supports in `Y`: the class of the constant
`0`-cocycle `1`. -/
def one (Y : TopCat.{u}) : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ 0 :=
  (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) 0).symm
    (Submodule.Quotient.mk ⟨constCochain 0 1, constCochain_one_mem_relCocycles_compl_univ Y⟩)

/-- The unit `1 ∈ H^0 Y` is the class of the constant cocycle `1`. -/
lemma relativeSingularCohomologyEquiv_one (Y : TopCat.{u}) :
    relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) 0 (one R Y) =
      Submodule.Quotient.mk ⟨constCochain 0 1, constCochain_one_mem_relCocycles_compl_univ Y⟩ :=
  LinearEquiv.apply_symm_apply _ _

end cohomologyWithSupports

end MMP
