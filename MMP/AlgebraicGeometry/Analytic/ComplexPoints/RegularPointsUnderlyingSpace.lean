module

public import MMP.AlgebraicGeometry.Variety.SingularLocus
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts

/-!
# Regular points on the underlying space of a scheme

When `X` is locally of finite type over an algebraically closed field `K` the closed points of
`X` are the `K`-points `X(K)`, the underlying space of Fulton §19.1. So the set `X_reg` of
regular points of `X` is a subset `X_reg(K)` of `X(K)`.

For a Zariski open `U ⊆ X` the points of `X(K)` landing in `U` form a classically open set.
Hence for `X` locally of finite type over `K` the regular part `X_reg(K)` is classically open,
and so is `X_reg(K) - Z` for every Zariski closed `Z ⊆ X`.

## Main definitions

* `MMP.UnderlyingSpace.regularPart`: the set `X_reg(K) ⊆ X(K)` of `K`-points
  whose closed point lies in the regular locus of `X`.

## Main results

* `MMP.UnderlyingSpace.mem_regularPart_iff`: `p ∈ X_reg(K)` iff its closed point lies in
  `X_reg`.
* `MMP.UnderlyingSpace.isOpen_preimage_of_isOpen`: points landing in a Zariski open
  subset form a classically open set.
* `MMP.UnderlyingSpace.isOpen_regularPart`,
  `MMP.UnderlyingSpace.isOpen_regularPart_diff`: `X_reg(K)` and `X_reg(K) - Z` are
  classically open.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- The `K`-points landing in a Zariski open subset `U` of `X` form a classically open subset
of `X(K)`. -/
theorem isOpen_preimage_of_isOpen [TopologicalSpace K] {U : Set X} (hU : IsOpen U) :
    IsOpen {p : UnderlyingSpace K X | p.toHom (IsLocalRing.closedPoint K) ∈ U} := by
  convert isOpen_setOf_le_preimage (K := K) (X := X) ⟨U, hU⟩ using 1
  ext p
  exact (top_le_preimage_iff p ⟨U, hU⟩).symm

variable (K X) in
/-- The *regular part* `X_reg(K)` of the underlying space: the `K`-points whose closed point of
`X` is a regular point, i.e. lies in the regular locus `X_reg`. -/
def regularPart : Set (UnderlyingSpace K X) :=
  {p | p.toHom (IsLocalRing.closedPoint K) ∈ regularLocus X}

/-- A `K`-point lies in `X_reg(K)` if and only if its closed point lies in the regular locus of
`X`. -/
theorem mem_regularPart_iff (p : UnderlyingSpace K X) :
    p ∈ regularPart K X ↔ p.toHom (IsLocalRing.closedPoint K) ∈ regularLocus X :=
  Iff.rfl

variable [TopologicalSpace K] [LocallyOfFiniteType (X ↘ Spec (.of K))]

/-- For `X` locally of finite type over `K`, the regular part `X_reg(K)` is classically open. -/
theorem isOpen_regularPart : IsOpen (regularPart K X) :=
  isOpen_preimage_of_isOpen (isOpen_regularLocus_of_isAlgebraicScheme K X)

/-- For `X` locally of finite type over `K` and a Zariski closed `Z ⊆ X`, the set `X_reg(K) - Z`
of regular `K`-points off `Z` is classically open. -/
theorem isOpen_regularPart_diff {Z : Set X} (hZ : IsClosed Z) :
    IsOpen (regularPart K X \ {p | p.toHom (IsLocalRing.closedPoint K) ∈ Z}) :=
  isOpen_regularPart.inter (isOpen_preimage_of_isOpen hZ.isOpen_compl)

end UnderlyingSpace

end MMP
