module

public import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct
/-!
# Refined topological intersection products (Fulton, Example 19.1.10 and §19.2)

Let `M` be an oriented real `n`-manifold with fundamental class `μ_M ∈ H_n M`, `A, B ⊆ M` closed,
`a ∈ H_k A` and `b ∈ H_l B`. With `cl^M(a) ∈ H^{n-k}(M, M - A)` and `cl^M(b) ∈ H^{n-l}(M, M - B)`
the classes dual to `a` and `b` (`c ∩ μ_M = a`), the *refined product* is
`a · b := (cl^M(a) ∪ cl^M(b)) ∩ μ_M ∈ H_{k+l-n}(A ∩ B)`.

## Main definitions

* `MMP.borelMooreHomology.IsTopologicalRefinedProduct`: `x ∈ H_{k+l-n}(A ∩ B)` is
  the refined product `a · b` with respect to `μ ∈ H_n M`, i.e.
  `x = (c ∪ d) ∩ μ` for classes `c` dual to `a` and `d` dual to `b`.

## Main results

* `MMP.borelMooreHomology.IsTopologicalRefinedProduct.of_isDualClassWithSupports`:
  for `c` dual to `a` and `d` dual to `b`, `(c ∪ d) ∩ μ` is a refined product of `a` and `b`.
* `MMP.borelMooreHomology.IsTopologicalRefinedProduct.right_unique`: the refined
  product is unique once the dual classes of `a` and of `b` are.

## Implementation notes

The dual class is the predicate `MMP.borelMooreHomology.IsDualClassWithSupports`
(the graph of `a ↦ cl^M(a)`): that there is exactly one dual class
(`lem_c19_topological_dual_class_well_defined`) is a separate statement, resting on
Poincaré–Alexander duality. Accordingly the refined product is the relation
`{(a, b, (c ∪ d) ∩ μ) : c dual to a, d dual to b}`; once dual classes exist and are unique it is
the graph of `(a, b) ↦ a · b` (`IsTopologicalRefinedProduct.right_unique`,
`IsTopologicalRefinedProduct.of_isDualClassWithSupports`).

As for the dual class, `μ` is an argument (for Fulton's notion, the fundamental class of the
oriented manifold `M`), and the cap products into `H_* A`, `H_* B` and `H_* (A ∩ B)` are those of
`MMP.borelMooreHomology.capProductSupport`, defined for closed subsets with
arbitrarily small proper neighbourhood deformations; the relation carries that hypothesis for
`A`, `B` and `A ∩ B` (all hold for Zariski closed subsets of complex schemes). The cup product
`H^{n-k}(M, M - A) ⊗ H^{n-l}(M, M - B) → H^{2n-k-l}(M, M - (A ∩ B))` is
`MMP.cohomologyWithSupports.cup`, and the cap product lands in degree
`n - ((n - k) + (n - l))`, identified with `k + l - n` by `BorelMooreCross.congrDegree`.

The case of subvarieties `V`, `W` of a non-singular complex variety (`cl(V) · cl(W)`) is
`Subvariety.IsCycleClassRefinedProduct`
(`MMP/AlgebraicGeometry/CycleMap/DualCycleClass.lean`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.10 and §19.2.
-/

@[expose] public noncomputable section

universe u

namespace MMP

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R] {M : TopCat.{u}} {A B : Set M} {n : ℕ} {k l : ℤ}

/-- The *refined product* `a · b := (cl^M(a) ∪ cl^M(b)) ∩ μ_M ∈ H_{k+l-n}(A ∩ B)` (Fulton,
Example 19.1.10 and §19.2) of `a ∈ H_k A` and `b ∈ H_l B`, for closed subsets `A`, `B` of `M` and
`μ ∈ H_n M` (for Fulton, the fundamental class of the oriented real `n`-manifold `M`): `x` is the
refined product of `a` and `b` when `x = (c ∪ d) ∩ μ` for a class `c ∈ H^{n-k}(M, M - A)` dual to
`a` and a class `d ∈ H^{n-l}(M, M - B)` dual to `b`. -/
def IsTopologicalRefinedProduct (hA : IsClosed A) (hB : IsClosed B)
    (hAd : HasProperNeighbourhoodDeformations A) (hBd : HasProperNeighbourhoodDeformations B)
    (hABd : HasProperNeighbourhoodDeformations (A ∩ B))
    (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k)
    (b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) l)
    (x : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (A ∩ B : Set M)) (k + l - n)) :
    Prop :=
  ∃ (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k))
    (d : cohomologyWithSupports R (ModuleCat.of R R) M B (n - l)),
    IsDualClassWithSupports R hA hAd μ c a ∧ IsDualClassWithSupports R hB hBd μ d b ∧
      congrDegree R (TopCat.of (A ∩ B : Set M)) (by omega)
        (capProductSupport R M (hA.inter hB) hABd ((n - k) + (n - l)) n
          (cohomologyWithSupports.cup R M hA hB (n - k) (n - l) c d) μ) = x

variable {R} {hA : IsClosed A} {hB : IsClosed B} {hAd : HasProperNeighbourhoodDeformations A}
  {hBd : HasProperNeighbourhoodDeformations B} {hABd : HasProperNeighbourhoodDeformations (A ∩ B)}
  {μ : borelMooreHomology R (ModuleCat.of R R) M n}
  {a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
  {b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) l}

/-- For `c` dual to `a` and `d` dual to `b`, the class `(c ∪ d) ∩ μ` is a refined product of `a`
and `b`. -/
lemma IsTopologicalRefinedProduct.of_isDualClassWithSupports
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {d : cohomologyWithSupports R (ModuleCat.of R R) M B (n - l)}
    (hc : IsDualClassWithSupports R hA hAd μ c a) (hd : IsDualClassWithSupports R hB hBd μ d b) :
    IsTopologicalRefinedProduct R hA hB hAd hBd hABd μ a b
      (congrDegree R (TopCat.of (A ∩ B : Set M)) (by omega)
        (capProductSupport R M (hA.inter hB) hABd ((n - k) + (n - l)) n
          (cohomologyWithSupports.cup R M hA hB (n - k) (n - l) c d) μ)) :=
  ⟨c, d, hc, hd, rfl⟩

/-- The refined product is unique when the classes dual to `a` and to `b` are. -/
lemma IsTopologicalRefinedProduct.right_unique
    (hua : ∀ c c' : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k),
      IsDualClassWithSupports R hA hAd μ c a → IsDualClassWithSupports R hA hAd μ c' a → c = c')
    (hub : ∀ d d' : cohomologyWithSupports R (ModuleCat.of R R) M B (n - l),
      IsDualClassWithSupports R hB hBd μ d b → IsDualClassWithSupports R hB hBd μ d' b → d = d')
    {x x' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (A ∩ B : Set M)) (k + l - n)}
    (hx : IsTopologicalRefinedProduct R hA hB hAd hBd hABd μ a b x)
    (hx' : IsTopologicalRefinedProduct R hA hB hAd hBd hABd μ a b x') : x = x' := by
  obtain ⟨c, d, hc, hd, rfl⟩ := hx
  obtain ⟨c', d', hc', hd', rfl⟩ := hx'
  rw [hua c c' hc hc', hub d d' hd hd']

end borelMooreHomology

end MMP
