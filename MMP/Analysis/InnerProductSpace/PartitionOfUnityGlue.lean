module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.PartitionOfUnity

/-!
# Gluing operator families with a partition of unity

For a partition of unity `(ρᵢ)` on `X` and families of operators `Pᵢ(x)` on a complex inner
product space `V`, continuous near the topological support of `ρᵢ`, the convex combination
`A(x) = ∑ᵢ ρᵢ(x) Pᵢ(x)` is continuous; it is self-adjoint where the `Pᵢ(x)` are, equals `P` at a
point where all the `Pᵢ(x)` with `ρᵢ(x) ≠ 0` equal `P` (a convex combination of equal projections
is that projection), and maps into a subspace `W` when the `Pᵢ(x)` do.

## Main definitions

* `MMP.glueOperators`: `x ↦ ∑ᶠ i, ρᵢ(x) • Pᵢ(x)`.

## Main results

* `MMP.continuous_glueOperators`, `MMP.isSelfAdjoint_glueOperators`,
  `MMP.glueOperators_eq`, `MMP.glueOperators_apply_mem`.
-/

@[expose] public noncomputable section

open Set Function

namespace MMP

variable {ι X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] (ρ : PartitionOfUnity ι X univ) (P : ι → X → V →L[ℂ] V)

/-- The glued family `x ↦ ∑ᶠ i, ρᵢ(x) • Pᵢ(x)`. -/
def glueOperators (x : X) : V →L[ℂ] V :=
  ∑ᶠ i, ρ i x • P i x

variable {ρ P}

/-- `glueOperators ρ P x` is the finite sum of `ρ i x • P i x` over the indices `i` with
`ρ i x ≠ 0`. -/
lemma glueOperators_eq_sum (x : X) :
    glueOperators ρ P x = ∑ i ∈ (ρ.locallyFinite.point_finite x).toFinset, ρ i x • P i x := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  rw [Finite.coe_toFinset, mem_setOf_eq, mem_support]
  intro h
  exact hi (by simp only [h, zero_smul])

/-- If each `P i` is continuous at every point of the topological support of `ρ i`, then the
glued family `glueOperators ρ P` is continuous. -/
theorem continuous_glueOperators (h : ∀ i, ∀ x ∈ tsupport (ρ i), ContinuousAt (P i) x) :
    Continuous (glueOperators ρ P) :=
  ρ.continuous_finsum_smul h

/-- If `P i x` is self-adjoint whenever `ρ i x ≠ 0`, then `glueOperators ρ P x` is self-adjoint. -/
theorem isSelfAdjoint_glueOperators {x : X} (h : ∀ i, ρ i x ≠ 0 → IsSelfAdjoint (P i x)) :
    IsSelfAdjoint (glueOperators ρ P x) := by
  rw [glueOperators_eq_sum]
  refine isSelfAdjoint_sum _ fun i hi ↦ ?_
  rw [Finite.mem_toFinset, mem_setOf_eq, mem_support] at hi
  exact IsSelfAdjoint.smul (IsSelfAdjoint.all (ρ i x)) (h i hi)

/-- If `P i x = Q` whenever `ρ i x ≠ 0`, then `glueOperators ρ P x = Q`. -/
theorem glueOperators_eq {x : X} {Q : V →L[ℂ] V} (h : ∀ i, ρ i x ≠ 0 → P i x = Q) :
    glueOperators ρ P x = Q := by
  have : ∀ i, ρ i x • P i x = ρ i x • Q := fun i ↦ by
    by_cases hi : ρ i x = 0
    · rw [hi, zero_smul, zero_smul]
    · rw [h i hi]
  rw [glueOperators]
  simp_rw [this]
  rw [← finsum_smul, ρ.sum_eq_one (mem_univ x), one_smul]

/-- If `P i x` maps `V` into the submodule `W` whenever `ρ i x ≠ 0`, then so does
`glueOperators ρ P x`. -/
theorem glueOperators_apply_mem {x : X} {W : Submodule ℂ V}
    (h : ∀ i, ρ i x ≠ 0 → ∀ v, P i x v ∈ W) (v : V) : glueOperators ρ P x v ∈ W := by
  rw [glueOperators_eq_sum, ContinuousLinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [Finite.mem_toFinset, mem_setOf_eq, mem_support] at hi
  rw [ContinuousLinearMap.smul_apply]
  exact W.restrictScalars ℝ |>.smul_mem (ρ i x) (h i hi v)

end MMP
