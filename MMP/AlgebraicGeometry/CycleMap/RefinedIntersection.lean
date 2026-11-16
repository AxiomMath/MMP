module

public import MMP.AlgebraicGeometry.CycleMap.TopologicalRefinedProduct
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Commutative
public import MMP.AlgebraicTopology.CapProduct.CupSupport

/-!
# Refined products as cap products with a pulled-back class (Fulton, Corollary 19.2)

Let `P`, `Q` be closed subsets of a space `Y`, `u ∈ H^i(Y, Y - P)`, `v ∈ H^j(Y, Y - Q)` and
`m ∈ H_k Y`, with `j_P : P → Y`, `j_Q : Q → Y` the inclusions. When `(-1)^{ij} = 1` (for
instance `i` or `j` even), the cap product with a cup product (Fulton §19.1, (8)) and the graded
commutativity of the cup product give
`j_Q^* u ∩ (v ∩ m) = (u ∪ v) ∩ m = (v ∪ u) ∩ m = j_P^* v ∩ (u ∩ m)` in `H_{k-i-j}(P ∩ Q)`,
each side transported to `P ∩ Q` along `j_Q⁻¹ P ≅ P ∩ Q`, resp. `j_P⁻¹ Q ≅ P ∩ Q`.

For an oriented real `n`-manifold `M` with fundamental class `μ`, closed `A`, `B ⊆ M`,
`c ∈ H^{n-k}(M, M - A)` dual to `a ∈ H_k A` and `d ∈ H^{n-l}(M, M - B)` dual to `b ∈ H_l B`,
with `n - k` or `n - l` even, this is the step
`f^* cl^X(W) ∩ cl(V) = (cl^X(V) ∪ cl^X(W)) ∩ μ_X` of Fulton's Corollary 19.2 (a): the refined
product `a · b = (c ∪ d) ∩ μ` is `j_A^* d ∩ a ∈ H_{k+l-n}(A ∩ B)`.

## Main results

* `MMP.borelMooreHomology.capProductSupport_cup_eq_pushforward_swap`:
  `(u ∪ v) ∩ m = j_P^* v ∩ (u ∩ m)` when `(-1)^{ij} = 1`.
* `MMP.borelMooreHomology.pushforward_capProductSupportPullback_capProductSupport_comm`:
  `j_Q^* u ∩ (v ∩ m) = j_P^* v ∩ (u ∩ m)` when `(-1)^{ij} = 1`.
* `MMP.borelMooreHomology.capProductSupport_cup_of_isDualClassWithSupports`:
  `(c ∪ d) ∩ μ = j_A^* d ∩ a` for `c` dual to `a`, `(-1)^{(n-k)(n-l)} = 1`.
* `MMP.borelMooreHomology.isTopologicalRefinedProduct_capProductSupportPullback`:
  `j_A^* d ∩ a` is the refined product `a · b`.
## Implementation notes

The sign condition is stated as `(-1 : Rˣ) ^ (i * j) = 1`, the sign of
`MMP.cohomologyWithSupports.cup_comm`; it holds when `i * j` is even
(`Even.neg_one_zpow`), in particular when `i` or `j` is.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (8), and Corollary 19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u

namespace MMP

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R]

/-- For `h : i = i'`, transporting `x ∈ H_i X` to degree `i'` gives `y` if and only if `x` is
the transport of `y` back along `h.symm`. -/
lemma congrDegree_eq_iff_eq_congrDegree_symm (X : TopCat.{u}) {i i' : ℤ} (h : i = i')
    (x : borelMooreHomology R (ModuleCat.of R R) X i)
    (y : borelMooreHomology R (ModuleCat.of R R) X i') :
    congrDegree R X h x = y ↔ x = congrDegree R X h.symm y := by
  subst h
  rfl

/-- Transport of the homology class along an equality of degrees commutes with the cap product
`f^* c ∩ -`. -/
lemma capProductSupportPullback_congrDegree_apply {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {Z : Set Y}
    (hZ : IsClosed Z) (hZd : HasProperNeighbourhoodDeformations (f ⁻¹' Z)) (j : ℤ) {k k' : ℤ}
    (h : k = k') (c : cohomologyWithSupports R (ModuleCat.of R R) Y Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    capProductSupportPullback R f hZ hZd j k' c (congrDegree R _ h a) =
      congrDegree R _ (by rw [h]) (capProductSupportPullback R f hZ hZd j k c a) := by
  subst h
  rfl

/-- **The swapped cap product with a cup product.** For closed `P`, `Q` in `Y`,
`u ∈ H^i(Y, Y - P)`, `v ∈ H^j(Y, Y - Q)` with `(-1)^{ij} = 1` and `m ∈ H_k Y`,
`(u ∪ v) ∩ m = j_P^* v ∩ (u ∩ m)` in `H_{k-i-j}(P ∩ Q)`, the right side transported along
`j_P⁻¹ Q ≅ P ∩ Q`. -/
theorem capProductSupport_cup_eq_pushforward_swap (Y : TopCat.{u}) {P Q : Set Y}
    (hP : IsClosed P) (hQ : IsClosed Q) (hPd : HasProperNeighbourhoodDeformations P)
    (hPQd : HasProperNeighbourhoodDeformations (P ∩ Q))
    (hQPd : HasProperNeighbourhoodDeformations (Q ∩ P))
    (hQd' : HasProperNeighbourhoodDeformations (subsetInclusion P ⁻¹' Q)) {i j : ℤ} (k : ℤ)
    (hs : (-1 : Rˣ) ^ (i * j) = 1)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y P i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y Q j)
    (m : borelMooreHomology R (ModuleCat.of R R) Y k) :
    congrDegree R (TopCat.of (P ∩ Q : Set Y)) (by ring)
        (capProductSupport R Y (hP.inter hQ) hPQd (i + j) k
          (cohomologyWithSupports.cup R Y hP hQ i j u v) m) =
      (pushforward R (ModuleCat.of R R) (preimageInterHom P Q)
        (isProperMap_preimageInterHom hP hQ) (k - i - j)).hom
        (capProductSupportPullback R (subsetInclusion P) hQ hQd' j (k - i) v
          (capProductSupport R Y hP hPd i k u m)) := by
  have hc := cohomologyWithSupports.cup_comm R Y hP hQ i j u v
  rw [hs, Units.val_one, one_smul] at hc
  have h2 := capProductSupport_cup R Y hQ hP hPd hQPd hQd' j i k v u m
  rw [congrDegree_eq_iff_eq_congrDegree_symm] at h2
  rw [← hc, capProductSupport_congrIndex R Y (hQ.inter hP) (hP.inter hQ) hQPd hPQd
      (inter_comm Q P) (add_comm j i) k, congrDegree_congrDegree, h2, pushforward_congrDegree,
    congrDegree_congrDegree, ← pushforward_comp_apply', congrDegree_self]
  exact congrFun (congrArg (fun φ ↦ ⇑(ModuleCat.Hom.hom φ))
    (pushforward_congr (R := R) rfl _ _ _)) _

/-- **Swapping the two cap products** (Fulton §19.1, (8), with graded commutativity of the cup
product). For closed `P`, `Q` in `Y`, `u ∈ H^i(Y, Y - P)`, `v ∈ H^j(Y, Y - Q)` with
`(-1)^{ij} = 1` and `m ∈ H_k Y`, `j_Q^* u ∩ (v ∩ m) = j_P^* v ∩ (u ∩ m)` in `H_{k-i-j}(P ∩ Q)`,
the two sides transported along `j_Q⁻¹ P ≅ Q ∩ P = P ∩ Q` and `j_P⁻¹ Q ≅ P ∩ Q`. -/
theorem pushforward_capProductSupportPullback_capProductSupport_comm (Y : TopCat.{u})
    {P Q : Set Y} (hP : IsClosed P) (hQ : IsClosed Q) (hPd : HasProperNeighbourhoodDeformations P)
    (hQd : HasProperNeighbourhoodDeformations Q)
    (hPQd : HasProperNeighbourhoodDeformations (P ∩ Q))
    (hQPd : HasProperNeighbourhoodDeformations (Q ∩ P))
    (hPd' : HasProperNeighbourhoodDeformations (subsetInclusion Q ⁻¹' P))
    (hQd' : HasProperNeighbourhoodDeformations (subsetInclusion P ⁻¹' Q)) {i j : ℤ} (k : ℤ)
    (hs : (-1 : Rˣ) ^ (i * j) = 1)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y P i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y Q j)
    (m : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R)
        (preimageInterHom Q P ≫ subsetInclusionOfSubset (inter_comm Q P).le)
        ((isProperMap_subsetInclusionOfSubset (hQ.inter hP) (inter_comm Q P).le).comp
          (isProperMap_preimageInterHom hQ hP)) (k - j - i)).hom
        (capProductSupportPullback R (subsetInclusion Q) hP hPd' i (k - j) u
          (capProductSupport R Y hQ hQd j k v m)) =
      congrDegree R (TopCat.of (P ∩ Q : Set Y)) (by ring)
        ((pushforward R (ModuleCat.of R R) (preimageInterHom P Q)
          (isProperMap_preimageInterHom hP hQ) (k - i - j)).hom
          (capProductSupportPullback R (subsetInclusion P) hQ hQd' j (k - i) v
            (capProductSupport R Y hP hPd i k u m))) := by
  rw [← capProductSupport_cup R Y hP hQ hQd hPQd hPd' i j k u v m,
    ← capProductSupport_cup_eq_pushforward_swap R Y hP hQ hPd hPQd hQPd hQd' k hs u v m,
    congrDegree_congrDegree]

variable {R} {M : TopCat.{u}} {A B : Set M} {n : ℕ} {k l : ℤ}

/-- **The refined product as a cap product with a pulled-back class** (Fulton, Corollary 19.2
(a)). For closed `A`, `B ⊆ M`, `μ ∈ H_n M`, `c ∈ H^{n-k}(M, M - A)` dual to `a ∈ H_k A`,
`d ∈ H^{n-l}(M, M - B)` and `(-1)^{(n-k)(n-l)} = 1`, `(c ∪ d) ∩ μ = j_A^* d ∩ a` in
`H_{k+l-n}(A ∩ B)`, the right side transported along `j_A⁻¹ B ≅ A ∩ B`. -/
theorem capProductSupport_cup_of_isDualClassWithSupports (hA : IsClosed A) (hB : IsClosed B)
    (hAd : HasProperNeighbourhoodDeformations A)
    (hABd : HasProperNeighbourhoodDeformations (A ∩ B))
    (hBAd : HasProperNeighbourhoodDeformations (B ∩ A))
    (hA'Bd : HasProperNeighbourhoodDeformations (subsetInclusion A ⁻¹' B))
    (hs : (-1 : Rˣ) ^ (((n : ℤ) - k) * (n - l)) = 1)
    {μ : borelMooreHomology R (ModuleCat.of R R) M n}
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    (hc : IsDualClassWithSupports R hA hAd μ c a)
    (d : cohomologyWithSupports R (ModuleCat.of R R) M B (n - l)) :
    congrDegree R (TopCat.of (A ∩ B : Set M))
        (show (n : ℤ) - ((n - k) + (n - l)) = k + l - n by omega)
        (capProductSupport R M (hA.inter hB) hABd ((n - k) + (n - l)) n
          (cohomologyWithSupports.cup R M hA hB (n - k) (n - l) c d) μ) =
      congrDegree R (TopCat.of (A ∩ B : Set M)) (show k - ((n : ℤ) - l) = k + l - n by omega)
        ((pushforward R (ModuleCat.of R R) (preimageInterHom A B)
          (isProperMap_preimageInterHom hA hB) (k - (n - l))).hom
          (capProductSupportPullback R (subsetInclusion A) hB hA'Bd (n - l) k d a)) := by
  have h1 := capProductSupport_cup_eq_pushforward_swap R M hA hB hAd hABd hBAd hA'Bd n hs c d μ
  rw [congrDegree_eq_iff_eq_congrDegree_symm] at h1
  rw [h1, congrDegree_congrDegree, ← hc, capProductSupportPullback_congrDegree_apply,
    pushforward_congrDegree, congrDegree_congrDegree]

/-- **The refined product `a · b` is `j_A^* d ∩ a`** (Fulton, Corollary 19.2 (a), the step
`f^* cl^X(W) ∩ cl(V) = (cl^X(V) ∪ cl^X(W)) ∩ μ_X`). For closed `A`, `B ⊆ M`, `μ ∈ H_n M`,
`c ∈ H^{n-k}(M, M - A)` dual to `a ∈ H_k A`, `d ∈ H^{n-l}(M, M - B)` dual to `b ∈ H_l B` and
`(-1)^{(n-k)(n-l)} = 1`, the class `j_A^* d ∩ a ∈ H_{k+l-n}(A ∩ B)`, transported along
`j_A⁻¹ B ≅ A ∩ B`, is the refined product of `a` and `b`. -/
theorem isTopologicalRefinedProduct_capProductSupportPullback (hA : IsClosed A) (hB : IsClosed B)
    (hAd : HasProperNeighbourhoodDeformations A) (hBd : HasProperNeighbourhoodDeformations B)
    (hABd : HasProperNeighbourhoodDeformations (A ∩ B))
    (hBAd : HasProperNeighbourhoodDeformations (B ∩ A))
    (hA'Bd : HasProperNeighbourhoodDeformations (subsetInclusion A ⁻¹' B))
    (hs : (-1 : Rˣ) ^ (((n : ℤ) - k) * (n - l)) = 1)
    {μ : borelMooreHomology R (ModuleCat.of R R) M n}
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {d : cohomologyWithSupports R (ModuleCat.of R R) M B (n - l)}
    {a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    {b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) l}
    (hc : IsDualClassWithSupports R hA hAd μ c a) (hd : IsDualClassWithSupports R hB hBd μ d b) :
    IsTopologicalRefinedProduct R hA hB hAd hBd hABd μ a b
      (congrDegree R (TopCat.of (A ∩ B : Set M)) (show k - ((n : ℤ) - l) = k + l - n by omega)
        ((pushforward R (ModuleCat.of R R) (preimageInterHom A B)
          (isProperMap_preimageInterHom hA hB) (k - (n - l))).hom
          (capProductSupportPullback R (subsetInclusion A) hB hA'Bd (n - l) k d a))) :=
  ⟨c, d, hc, hd,
    capProductSupport_cup_of_isDualClassWithSupports hA hB hAd hABd hBAd hA'Bd hs hc d⟩

end borelMooreHomology

end MMP
