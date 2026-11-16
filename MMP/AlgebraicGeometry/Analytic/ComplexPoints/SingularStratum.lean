module
public import MMP.AlgebraicGeometry.Variety.SingularLocus
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The singular stratum of a scheme (Fulton, §19.1)

Let `X` be a scheme with irreducible components `X₁, …, X_r`, each with its reduced structure.
The *singular stratum* of `X` is

`S_X = ⋃ⱼ (Xⱼ)_sing ∪ ⋃_{j ≠ l} (Xⱼ ∩ X_l)`,

where `(Xⱼ)_sing` is the set of points at which the local ring of the reduced scheme `Xⱼ` is not
regular. For each `j`, `Uⱼ = X - (S_X ∪ ⋃_{l ≠ j} X_l)`. When `X` is an algebraic scheme over a
field (for instance a complex scheme), `X` has finitely many irreducible components and the
singular locus of each `Xⱼ` is Zariski closed (Stacks, Tag 07R5), so `S_X` is Zariski closed and
each `Uⱼ` is Zariski open.

## Main definitions

* `MMP.irreducibleComponentScheme`: an irreducible component of `X` with its
  reduced structure.
* `MMP.singularStratum`: the singular stratum `S_X ⊆ X`.
* `MMP.singularStratumComplement`: the open set `Uⱼ`.

## Main results

* `MMP.isClosed_singularStratum`: `S_X` is Zariski closed for an algebraic scheme.
* `MMP.isOpen_singularStratumComplement`: each `Uⱼ` is Zariski open.

## Implementation notes

The definitions are made for an arbitrary scheme, and closedness is proved for an algebraic
scheme over an arbitrary field; Fulton's complex schemes are a special case. `S_X` is a set of
(scheme-theoretic) points of `X`; its reduced structure is
`(Scheme.IdealSheafData.vanishingIdeal (singularStratumCloseds K X)).subscheme`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped MMP.SubschemeOver

universe u

namespace MMP

variable (X : Scheme.{u})

/-- An irreducible component `Z` of a scheme `X` with its reduced structure: the closed subscheme
cut out by the vanishing ideal of `Z`. -/
abbrev irreducibleComponentScheme (Z : irreducibleComponents X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subscheme

/-- The inclusion of an irreducible component, with its reduced structure, into `X`. -/
abbrev irreducibleComponentι (Z : irreducibleComponents X) : irreducibleComponentScheme X Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- A component of a scheme locally of finite type over `K` is locally of finite type over `K`. -/
instance locallyOfFiniteType_irreducibleComponentScheme {K : Type u} [Field K]
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (Z : irreducibleComponents X) :
    LocallyOfFiniteType (irreducibleComponentScheme X Z ↘ Spec (.of K)) :=
  inferInstanceAs (LocallyOfFiniteType (irreducibleComponentι X Z ≫ X ↘ Spec (.of K)))

/-- A component of a scheme quasi-compact over `K` is quasi-compact over `K`. -/
instance quasiCompact_irreducibleComponentScheme {K : Type u} [Field K]
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] (Z : irreducibleComponents X) :
    QuasiCompact (irreducibleComponentScheme X Z ↘ Spec (.of K)) :=
  inferInstanceAs (QuasiCompact (irreducibleComponentι X Z ≫ X ↘ Spec (.of K)))

/-- The image in `X` of the reduced structure of a component is the component. -/
theorem range_irreducibleComponentι (Z : irreducibleComponents X) :
    Set.range (irreducibleComponentι X Z).base = Z.1 := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The *singular stratum* `S_X` of a scheme `X` (Fulton, §19.1): the union of the singular loci
`(Xⱼ)_sing` of the irreducible components `Xⱼ` of `X` (with their reduced structure), viewed in
`X`, and of the pairwise intersections `Xⱼ ∩ X_l`, `j ≠ l`. -/
def singularStratum : Set X :=
  (⋃ Z : irreducibleComponents X,
    (irreducibleComponentι X Z).base '' singularLocus (irreducibleComponentScheme X Z)) ∪
  ⋃ (Z : irreducibleComponents X) (W : irreducibleComponents X) (_ : Z ≠ W), Z.1 ∩ W.1

/-- The open set `Uⱼ = X - (S_X ∪ ⋃_{l ≠ j} X_l)` attached to an irreducible component `Xⱼ`
(Fulton, §19.1). -/
def singularStratumComplement (Z : irreducibleComponents X) : Set X :=
  (singularStratum X ∪ ⋃ (W : irreducibleComponents X) (_ : W ≠ Z), W.1)ᶜ

variable {X}

/-- A point `x` lies in `S_X` if and only if it is the image of a singular point of the reduced
structure of some irreducible component, or it lies in two distinct irreducible components. -/
theorem mem_singularStratum_iff {x : X} : x ∈ singularStratum X ↔
    (∃ Z : irreducibleComponents X, x ∈ (irreducibleComponentι X Z).base ''
      singularLocus (irreducibleComponentScheme X Z)) ∨
    ∃ Z W : irreducibleComponents X, Z ≠ W ∧ x ∈ Z.1 ∧ x ∈ W.1 := by
  simp only [singularStratum, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]

/-- A point of `Uⱼ` lies in `Xⱼ`. -/
theorem singularStratumComplement_subset (Z : irreducibleComponents X) :
    singularStratumComplement X Z ⊆ Z.1 := by
  intro x hx
  obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  replace hxW := hxW rfl
  by_contra hxZ
  refine hx (Or.inr (Set.mem_iUnion₂.mpr ⟨⟨W, hW⟩, fun h ↦ hxZ ?_, hxW⟩))
  rw [← h]
  exact hxW

/-- `Uⱼ` does not meet `S_X`. -/
theorem disjoint_singularStratumComplement (Z : irreducibleComponents X) :
    Disjoint (singularStratumComplement X Z) (singularStratum X) :=
  Set.disjoint_left.mpr fun _ hx hS ↦ hx (Or.inl hS)

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]

include K

/-- An algebraic scheme has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_isAlgebraicScheme :
    (irreducibleComponents X).Finite := by
  haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance
  haveI : IsNoetherian X := (isNoetherian_iff X).mpr ⟨inferInstance, inferInstance⟩
  exact NoetherianSpace.finite_irreducibleComponents

/-- **The singular stratum is Zariski closed** (Fulton, §19.1): for an algebraic scheme `X` over a
field, `S_X` is a closed subset of `X`. -/
theorem isClosed_singularStratum : IsClosed (singularStratum X) := by
  haveI := (finite_irreducibleComponents_of_isAlgebraicScheme K X).to_subtype
  refine IsClosed.union (isClosed_iUnion_of_finite fun Z ↦ ?_)
    (isClosed_iUnion_of_finite fun Z ↦ isClosed_iUnion_of_finite fun W ↦
      isClosed_iUnion_of_finite fun _ ↦ (isClosed_of_mem_irreducibleComponents _ Z.2).inter
        (isClosed_of_mem_irreducibleComponents _ W.2))
  exact (irreducibleComponentι X Z).isClosedEmbedding.isClosedMap _
    (isClosed_singularLocus_of_isAlgebraicScheme K _)

/-- The singular stratum of an algebraic scheme, as a closed subset; its reduced structure is
`(Scheme.IdealSheafData.vanishingIdeal (singularStratumCloseds K X)).subscheme`. -/
def singularStratumCloseds : Closeds X :=
  ⟨singularStratum X, isClosed_singularStratum K X⟩

/-- **The sets `Uⱼ` are Zariski open** (Fulton, §19.1). -/
theorem isOpen_singularStratumComplement (Z : irreducibleComponents X) :
    IsOpen (singularStratumComplement X Z) := by
  haveI := (finite_irreducibleComponents_of_isAlgebraicScheme K X).to_subtype
  refine ((isClosed_singularStratum K X).union (isClosed_iUnion_of_finite fun W ↦
    isClosed_iUnion_of_finite fun _ ↦ isClosed_of_mem_irreducibleComponents _ W.2)).isOpen_compl

end MMP
