module

public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SingularStratum
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import StacksFrontier.Topology.Dimension.UnionDimension
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The dimension of the singular stratum (Fulton, §19.1)

Let `X` be an algebraic scheme of dimension `n` over a field, with irreducible components
`X₁, …, X_r`. The singular stratum `S_X = ⋃ⱼ (Xⱼ)_sing ∪ ⋃_{j ≠ l} (Xⱼ ∩ X_l)` has dimension at
most `n - 1`. Indeed `S_X` is a finite union of closed sets, each a proper closed subset of some
irreducible component `Xⱼ`: the singular locus of the integral scheme `Xⱼ` misses its generic
point, and `Xⱼ ∩ X_l ⊊ Xⱼ` for `l ≠ j` since distinct irreducible components are not contained
in one another. A proper closed subset of an irreducible space of finite dimension has strictly
smaller dimension, and on a quasi-sober space the dimension of a finite union of closed sets is
the largest of their dimensions.

## Main results

* `MMP.topologicalKrullDim_singularStratum_lt`: `dim S_X < n` whenever `dim X ≤ n`.

## Implementation notes

Fulton states the result for complex schemes; it is proved for an algebraic scheme over an
arbitrary field. The bound `dim S_X ≤ n - 1` is written `dim S_X < n` in `WithBot ℕ∞`, which for
`n = 0` says that `S_X` is empty.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped MMP.SubschemeOver

universe u

namespace MMP

variable {X : Scheme.{u}}

/-- An irreducible component of a scheme, with its reduced structure, is an integral scheme. -/
instance isIntegral_irreducibleComponentScheme (Z : irreducibleComponents X) :
    IsIntegral (irreducibleComponentScheme X Z) := by
  have : IrreducibleSpace (irreducibleComponentScheme X Z) := by
    rw [MMP.Intersection.Scheme.IdealSheafData.irreducibleSpace_subscheme_iff,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Z.2.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The image in `X` of the singular locus of an irreducible component `Xⱼ` is a proper subset
of `Xⱼ`. -/
theorem image_singularLocus_irreducibleComponentScheme_ne (Z : irreducibleComponents X) :
    (irreducibleComponentι X Z).base '' singularLocus (irreducibleComponentScheme X Z) ≠ Z.1 := by
  haveI := isIntegral_irreducibleComponentScheme Z
  intro h
  rw [← range_irreducibleComponentι X Z, ← Set.image_univ] at h
  exact singularLocus_ne_univ _
    ((irreducibleComponentι X Z).isClosedEmbedding.injective.image_injective h)

/-- The intersection of two distinct irreducible components is a proper subset of the first. -/
theorem inter_irreducibleComponents_ne {Z W : irreducibleComponents X} (hZW : Z ≠ W) :
    Z.1 ∩ W.1 ≠ Z.1 := fun h ↦
  hZW (Subtype.ext (subset_antisymm (Set.inter_eq_left.mp h)
    (Z.2.2 W.2.1 (Set.inter_eq_left.mp h))))

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]

include K

/-- **The singular stratum has smaller dimension** (Fulton, §19.1): if the algebraic scheme `X`
has dimension at most `n`, then `dim S_X ≤ n - 1`, i.e. `dim S_X < n`. -/
theorem topologicalKrullDim_singularStratum_lt {n : ℕ} (hn : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (singularStratum X) < n := by
  classical
  haveI := (finite_irreducibleComponents_of_isAlgebraicScheme K X).to_subtype
  haveI : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let ι := irreducibleComponents X ⊕ (irreducibleComponents X × irreducibleComponents X)
  let A : ι → Set X := fun i ↦ match i with
    | .inl Z => (irreducibleComponentι X Z).base '' singularLocus (irreducibleComponentScheme X Z)
    | .inr (Z, W) => if Z = W then ∅ else Z.1 ∩ W.1
  have hA : ∀ i, IsClosed (A i) := by
    rintro (Z | ⟨Z, W⟩)
    · exact (irreducibleComponentι X Z).isClosedEmbedding.isClosedMap _
        (isClosed_singularLocus_of_isAlgebraicScheme K _)
    · change IsClosed (if Z = W then ∅ else Z.1 ∩ W.1)
      split_ifs
      · exact isClosed_empty
      · exact (isClosed_of_mem_irreducibleComponents _ Z.2).inter
          (isClosed_of_mem_irreducibleComponents _ W.2)
  have hSA : singularStratum X ⊆ ⋃ i ∈ (Finset.univ : Finset ι), A i := by
    intro x hx
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    rcases mem_singularStratum_iff.mp hx with ⟨Z, hZ⟩ | ⟨Z, W, hZW, hxZ, hxW⟩
    · exact ⟨.inl Z, hZ⟩
    · refine ⟨.inr (Z, W), ?_⟩
      change x ∈ (if Z = W then ∅ else Z.1 ∩ W.1)
      rw [if_neg hZW]
      exact ⟨hxZ, hxW⟩
  -- each piece is a proper closed subset of an irreducible component
  have hlt : ∀ i, topologicalKrullDim (A i) < n := by
    have hZ : ∀ Z : irreducibleComponents X, ∀ Y : Set X, IsClosed Y → Y ⊆ Z.1 → Y ≠ Z.1 →
        topologicalKrullDim Y < n := fun Z Y hY hYZ hne ↦ by
      have hZn : topologicalKrullDim Z.1 ≤ n := (topologicalKrullDim_subspace_le X _).trans hn
      exact (MMP.topologicalKrullDim_lt_of_subset_of_ne Z.2.1 hY hYZ hne
        (ne_top_of_le_ne_top (Ne.symm (ne_of_beq_false rfl)) hZn)).trans_le hZn
    rintro (Z | ⟨Z, W⟩)
    · refine hZ Z _ (hA (.inl Z)) ?_ (image_singularLocus_irreducibleComponentScheme_ne Z)
      rw [← range_irreducibleComponentι X Z]
      exact Set.image_subset_range _ _
    · change topologicalKrullDim ↥(if Z = W then (∅ : Set X) else Z.1 ∩ W.1) < n
      by_cases hZW : Z = W
      · rw [if_pos hZW]
        exact hZ Z ∅ isClosed_empty (Set.empty_subset _) (Z.2.1.nonempty.ne_empty.symm)
      · rw [if_neg hZW]
        refine hZ Z _ ?_ Set.inter_subset_left (inter_irreducibleComponents_ne hZW)
        exact (isClosed_of_mem_irreducibleComponents _ Z.2).inter
          (isClosed_of_mem_irreducibleComponents _ W.2)
  have hle := topologicalKrullDim_le_of_subset_biUnion (Finset.univ : Finset ι)
    (isClosed_singularStratum K X) hA hSA
    (c := Finset.univ.sup fun i ↦ topologicalKrullDim (A i))
    (fun i _ ↦ (topologicalKrullDim_le_of_subset Set.inter_subset_right).trans
      (Finset.le_sup (f := fun i ↦ topologicalKrullDim (A i)) (Finset.mem_univ i)))
  exact hle.trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ ↦ hlt i)

end MMP
