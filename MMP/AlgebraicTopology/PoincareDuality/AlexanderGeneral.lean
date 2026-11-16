module

public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport

/-!
# Alexander duality and dual classes (Fulton, §19.1 and Example 19.1.10)

For a closed subset `A` of a space `M` with arbitrarily small proper neighbourhood deformations
and a class `μ ∈ H_n M`, the *duality map* is `c ↦ c ∩ μ`, `H^{n-k}(M, M - A) → H_k A`
(`MMP.borelMooreHomology.dualityMap`). Alexander duality
(`thm_ext_c19_alexander_duality_general`) says that it is bijective for `μ = μ_M` the fundamental
class of an oriented real `n`-manifold; the existence and uniqueness of the dual class
(`lem_c19_topological_dual_class_well_defined`) says that every `a ∈ H_k A` has exactly one class
dual to it. The two say the same thing, degree by degree:
`existsUnique_isDualClassWithSupports_iff_bijective`.

## Main definitions

* `MMP.borelMooreHomology.dualityMap`: `c ↦ c ∩ μ`,
  `H^{n-k}(M, M - A) → H_k A`.

## Main results

* `MMP.borelMooreHomology.isDualClassWithSupports_iff_dualityMap`: `c` is dual to
  `a` iff `c ∩ μ = a`.
* `MMP.borelMooreHomology.existsUnique_isDualClassWithSupports_iff_bijective`:
  every `a ∈ H_k A` has exactly one dual class iff the duality map is bijective in degree `k`.
* `MMP.borelMooreHomology.existsUnique_isDualClassWithSupports_of_bijective`.

## Implementation notes

`thm_ext_c19_alexander_duality_general` stated "for every closed subset
`X ⊆ Y`" is false without a local hypothesis on `X`: for the Warsaw circle `W ⊆ ℝ²` (closed and
compact), `H¹(ℝ², ℝ² - W) ≅ coker(H⁰ ℝ² → H⁰(ℝ² - W)) ≅ R`, as `W` separates the plane into two
components, while `H₁ W = 0`: `W` is compact, so locally finite singular chains on `W` are finite
ones, and the singular homology of `W` is that of a point. The correction, as for the connected
theorem `thm_ext_c19_poincare_alexander_duality`, is that `X` has arbitrarily small proper
neighbourhood deformations (`MMP.HasProperNeighbourhoodDeformations`), which the
cap product `def_c19_cap_product` into `H_* X` needs anyway; for `Y` a Hausdorff, second countable
real manifold it holds for `X` closed and locally contractible
(`MMP.hasProperNeighbourhoodDeformations_of_chartedSpace`), and for Zariski closed
subsets of complex schemes (`MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver`).
Every downstream use of the dual class (`IsDualClassWithSupports`, `IsTopologicalRefinedProduct`,
`CycleGroup.IsDualCycleClass`, `Subvariety.IsCycleClassRefinedProduct`) already carries that
hypothesis, discharged for complex schemes.
-/

@[expose] public noncomputable section

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R] {M : TopCat.{u}} {A : Set M} {n : ℕ}

/-- The *duality map* `c ↦ c ∩ μ`, `H^{n-k}(M, M - A) → H_k A` (Fulton, §19.1, (3)), for a closed
subset `A` of `M` with arbitrarily small proper neighbourhood deformations and `μ ∈ H_n M`; the
cap product lands in degree `n - (n - k)`, identified with `k`. -/
def dualityMap (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) M A (n - k) →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k :=
  (congrDegree R (TopCat.of A) (by omega)).toLinearMap ∘ₗ
    (capProductSupport R M hA hAd (n - k) n).flip μ

variable {R} {hA : IsClosed A} {hAd : HasProperNeighbourhoodDeformations A}
  {μ : borelMooreHomology R (ModuleCat.of R R) M n} {k : ℤ}

/-- The duality map sends `c` to the cap product `c ∩ μ`, transported from degree
`n - (n - k)` to degree `k`. -/
lemma dualityMap_apply (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)) :
    dualityMap R hA hAd μ k c =
      congrDegree R (TopCat.of A) (by omega) (capProductSupport R M hA hAd (n - k) n c μ) :=
  rfl

/-- `c` is dual to `a` exactly when `c ∩ μ = a`. -/
lemma isDualClassWithSupports_iff_dualityMap
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k) :
    IsDualClassWithSupports R hA hAd μ c a ↔ dualityMap R hA hAd μ k c = a :=
  Iff.rfl

/-- **Dual classes and duality.** Every `a ∈ H_k A` has exactly one class
`c ∈ H^{n-k}(M, M - A)` dual to it (`c ∩ μ = a`) if and only if `c ↦ c ∩ μ` is bijective. -/
theorem existsUnique_isDualClassWithSupports_iff_bijective :
    (∀ a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k,
        ∃! c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k),
          IsDualClassWithSupports R hA hAd μ c a) ↔
      Function.Bijective (dualityMap R hA hAd μ k) := by
  simp only [isDualClassWithSupports_iff_dualityMap]
  exact (Function.bijective_iff_existsUnique _).symm

/-- If `c ↦ c ∩ μ` is bijective, every `a ∈ H_k A` has exactly one dual class. -/
theorem existsUnique_isDualClassWithSupports_of_bijective
    (h : Function.Bijective (dualityMap R hA hAd μ k))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k) :
    ∃! c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k),
      IsDualClassWithSupports R hA hAd μ c a :=
  existsUnique_isDualClassWithSupports_iff_bijective.2 h a

end borelMooreHomology

end MMP
