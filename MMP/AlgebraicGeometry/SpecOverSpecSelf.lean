module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The structure morphism of `Spec R` over itself

Mathlib makes `Spec A` a scheme over `Spec R` for every `R`-algebra `A`
(`AlgebraicGeometry.specOverSpec`), with structure morphism `Spec.map (algebraMap R A)`. For
`A = R` the algebra is `Algebra.id`, so the structure morphism of `Spec R` over itself is the
identity.

## Main results

* `MMP.specOverSpec_over_self`: `(Spec R ↘ Spec R) = 𝟙 _`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- The structure morphism of `Spec K` over itself (via `specOverSpec` and `Algebra.id`) is the
identity. -/
theorem specOverSpec_over_self (K : Type u) [CommRing K] :
    (Spec (.of K) ↘ Spec (.of K)) = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

end MMP
