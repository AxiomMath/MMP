module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import MMP.Topology.KrullDimensionProperClosed

/-!
# The singular locus of a variety is a proper closed subset

Let `X` be an algebraic scheme over a field `K`. A scheme locally of finite type over a field is
J-2 (Stacks, Tag 07R5), so the regular locus of `X`, the set of points at which the local ring
of `X` is regular, is open, and the singular locus `X_sing` is closed. A point `P` of `X` (a
`0`-dimensional subvariety) is a regular point exactly when its generic point, a closed point of
`X`, lies in the regular locus.

If `X` is a variety, the local ring at the generic point is the function field of `X`, a field,
hence regular; so `X_sing` is a proper closed subset of the irreducible space `X`, and since
`X` is finite-dimensional, `dim X_sing < dim X`.

## Main results

* `MMP.isOpen_regularLocus_of_isAlgebraicScheme`: the regular locus of an algebraic
  scheme is open.
* `MMP.genericPoint_mem_regularLocus`: the generic point of an integral scheme is a
  regular point.
* `MMP.setDimension_singularLocus_lt_dimension`: for a variety `X`,
  `dim X_sing < dim X`.
* `MMP.exists_isClosed_singularPoints`: for a variety `X`, the singular points of
  `X` are the closed points of a Zariski closed subset of dimension `< dim X`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.1.3.
* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- The regular locus of an algebraic scheme over a field is open (Stacks, Tag 07R5). -/
theorem isOpen_regularLocus_of_isAlgebraicScheme (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    IsOpen (regularLocus X) := by
  haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  exact (Scheme.isJ2_of_locallyOfFiniteType_over_field K (X ↘ Spec (.of K))).isOpen_regularLocus
    (𝟙 X)

/-- The singular locus of an algebraic scheme over a field is Zariski closed. -/
theorem isClosed_singularLocus_of_isAlgebraicScheme (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    IsClosed (singularLocus X) :=
  (isOpen_regularLocus_of_isAlgebraicScheme K X).isClosed_compl

/-- The generic point of an integral scheme is a regular point: its local ring is the function
field. -/
theorem genericPoint_mem_regularLocus (X : Scheme.{u}) [IsIntegral X] :
    genericPoint X ∈ regularLocus X :=
  inferInstanceAs (IsRegularLocalRing X.functionField)

/-- The singular locus of an integral scheme is not the whole scheme. -/
theorem singularLocus_ne_univ (X : Scheme.{u}) [IsIntegral X] : singularLocus X ≠ Set.univ :=
  fun h ↦ (h ▸ Set.mem_univ (genericPoint X) : genericPoint X ∈ singularLocus X)
    (genericPoint_mem_regularLocus X)

/-- In an integral scheme, the regular locus is dense as soon as it is open. -/
theorem dense_regularLocus (X : Scheme.{u}) [IsIntegral X] (hX : IsOpen (regularLocus X)) :
    Dense (regularLocus X) :=
  hX.dense ⟨_, genericPoint_mem_regularLocus X⟩

/-- For a variety `X` over a field, the singular locus has dimension `< dim X`. -/
theorem setDimension_singularLocus_lt_dimension (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] :
    topologicalKrullDim (singularLocus X) < topologicalKrullDim X :=
  MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ
    (isClosed_singularLocus_of_isAlgebraicScheme K X)
    (singularLocus_ne_univ X)
    (ne_top_of_le_ne_top (have : CompactSpace X :=
        QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
      AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType K (X ↘ Spec (.of K)))
      (topologicalKrullDim_subspace_le X _))

/-- **The singular points of a variety form a Zariski closed set of smaller dimension.** For a
variety `X` over a field, there is a Zariski closed `S ⊆ X`, namely the singular locus, whose
closed points are exactly the points of `X` that are not regular, and `dim S < dim X`. -/
theorem exists_isClosed_singularPoints (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] :
    ∃ S : Set X, IsClosed S ∧ (∀ x : X, IsClosed ({x} : Set X) → (x ∉ regularLocus X ↔ x ∈ S)) ∧
      topologicalKrullDim S < topologicalKrullDim X :=
  ⟨singularLocus X, isClosed_singularLocus_of_isAlgebraicScheme K X, fun _ _ ↦ Iff.rfl,
    setDimension_singularLocus_lt_dimension K X⟩

end MMP
