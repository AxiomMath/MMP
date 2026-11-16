module

public import MMP.AlgebraicTopology.SingularCohomology.Unit
public import MMP.AlgebraicTopology.OrientationClass.CapCodimZero

/-!
# The unit class of singular cohomology and its cap product

For a space `Y` and a commutative ring `R`, the constant `0`-cochain with value `1` is a cocycle:
its coboundary on a singular `1`-simplex is `1 - 1 = 0`, and it vanishes on the simplices of the
empty set. Its class is the unit `1 ∈ H^0 Y = H^0(Y, Y - Y; R)`.

At the level of chains, the cap product of the constant `0`-cochain `1` with a simplex `σ` is the
weight of the back `0`-face, `1`, times the front `n`-face, which is `σ` itself. Hence
`1 ∩ a = a` for every Borel–Moore class `a ∈ H_k Y`
(`borelMooreHomology.capProduct_eq_congrDegree_of_eq_one`).

The unit `MMP.cohomologyWithSupports.one` itself is defined in `SingularCohomology.Unit`.

## Main results

* `MMP.borelMooreHomology.capProduct_one`: `1 ∩ a = a` for every `a ∈ H_k Y`, `k : ℤ`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

universe u

namespace MMP

open BorelMooreCross

variable (R : Type u) [CommRing R]

namespace borelMooreHomology

/-- **The cap product with the unit.** `1 ∩ a = a` for every `a ∈ H_k Y`, `k : ℤ` (for `k < 0`
both sides lie in `H_k Y = 0`). -/
theorem capProduct_one (Y : TopCat.{u}) (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProduct R Y Set.univ 0 k (cohomologyWithSupports.one R Y) a =
      congrDegree R Y (sub_zero k).symm a := by
  rcases lt_or_ge k 0 with hk | hk
  · have : Subsingleton (borelMooreHomology R (ModuleCat.of R R) Y (k - 0)) :=
      (ModuleCat.isZero_iff_subsingleton).1
        (isZero_borelMooreHomology_of_neg R _ Y (by omega))
    exact Subsingleton.elim _ _
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  exact capProduct_eq_congrDegree_of_eq_one R Y Set.univ m _ _ _
    (cohomologyWithSupports.relativeSingularCohomologyEquiv_one R Y) (fun _ ↦ rfl) _ a

end borelMooreHomology

end MMP
