module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleCohomologyAbelianComparison

/-!
# Injective sheaves of `ℚ`-vector spaces are injective abelian sheaves

A `ℚ`-vector space is a divisible abelian group, hence an injective abelian group. So forgetting
the `ℚ`-module structure preserves injective objects, and the same holds for sheaves of
`ℚ`-vector spaces on a topological space: an injective sheaf of `ℚ`-vector spaces is an injective
abelian sheaf. Together with the exactness of the forgetful functor on sheaves
(`Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂` and
`Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂`), this means that an
injective resolution of a sheaf of `ℚ`-vector spaces is, after forgetting, an injective
resolution of the underlying abelian sheaf (`CategoryTheory.Functor.mapInjectiveResolution`), so
that sheaf cohomology with rational coefficients may be computed in abelian sheaves.

## Main results

* `MMP.Topology.preservesInjectiveObjects_forget₂_rat`: the forgetful functor from `ℚ`-vector
  spaces to abelian groups preserves injective objects.
* `MMP.Topology.preservesInjectiveObjects_sheafCompose_forget₂_rat`: so does the forgetful
  functor from sheaves of `ℚ`-vector spaces on a space to abelian sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace MMP.Topology

/-- A `ℚ`-vector space is a divisible, hence injective, abelian group: the forgetful functor
from `ℚ`-vector spaces to abelian groups preserves injective objects. -/
theorem preservesInjectiveObjects_forget₂_rat :
    (forget₂ (ModuleCat.{u} ℚ) AddCommGrpCat.{u}).PreservesInjectiveObjects :=
  ⟨fun {M} _ => by
    let _ : DivisibleBy M ℤ :=
      { div := fun a n => (n : ℚ)⁻¹ • a
        div_zero := fun a => by simp
        div_cancel := fun {n} a hn => by
          rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn),
            one_smul] }
    exact AddCommGrpCat.injective_of_divisible M⟩

/-- An injective sheaf of `ℚ`-vector spaces on a topological space is an injective abelian
sheaf. -/
theorem preservesInjectiveObjects_sheafCompose_forget₂_rat (X : TopCat.{u}) :
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} ℚ) AddCommGrpCat.{u})).PreservesInjectiveObjects := by
  have := preservesInjectiveObjects_forget₂_rat.{u}
  exact sheafCompose_preservesInjectiveObjects _ _

end MMP.Topology
