module

public import MMP.AlgebraicTopology.CapProduct.CupSupport
/-!
# Exchanging two cap products with supports (Fulton, §19.2, proof of Theorem 19.2)

Let `X`, `W` be closed subsets of a space `Y`, `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)` and
`a ∈ H_k Y`. Capping `a` first with `v` and then with (the restriction to `W` of) `u`, or first
with `u` and then with (the restriction to `X` of) `v`, gives the same class of
`H_{k-i-j}(X ∩ W)` up to the sign `(-1)^{ij}`:
`j_W^* u ∩ (v ∩ a) = (-1)^{ij} j_X^* v ∩ (u ∩ a)`.
Both sides are `(u ∪ v) ∩ a` by the cap-cup formula (`capProductSupport_cup`, Fulton §19.1 (8)),
after the graded commutativity `v ∪ u = (-1)^{ij} u ∪ v` (`cup_comm`).

This is the step `(G^*u_F)|_V ∩ (G^*u_{j_0} ∩ a) = u_{i'_0} ∩ (G^*u_F ∩ a)` of the proof of
Fulton's Theorem 19.2 (both degrees even, so the sign is `1`).

## Main results

* `MMP.borelMooreHomology.pushforward_capProductSupportPullback_swap`: the formula
  with the sign.
* `MMP.borelMooreHomology.pushforward_capProductSupportPullback_swap_of_even`:
  the formula for `i` even.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 (8), §19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R]

/-- Push-forward commutes with the transport along an equality of degrees. -/
lemma pushforward_congrDegree_comm {X X' : TopCat.{u}} (f : X ⟶ X') (hf : IsProperMap f)
    {i i' : ℤ} (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) f hf i').hom (congrDegree R X h x) =
      congrDegree R X' h ((pushforward R (ModuleCat.of R R) f hf i).hom x) := by
  subst h
  rfl

/-- Equal maps have equal push-forwards (whatever the properness proofs). -/
lemma pushforward_congr_eq {X X' : TopCat.{u}} {f g : X ⟶ X'} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (i : ℤ) :
    pushforward R (ModuleCat.of R R) f hf i = pushforward R (ModuleCat.of R R) g hg i := by
  subst hfg
  rfl

/-- **Exchanging two cap products** (Fulton, proof of Theorem 19.2). For closed `X`, `W` in a
space `Y`, `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)` and `a ∈ H_k Y`,
`j_W^* u ∩ (v ∩ a) = (-1)^{ij} j_X^* v ∩ (u ∩ a)` in `H_{k-i-j}(X ∩ W)`, for the inclusions
`j_W : W → Y`, `j_X : X → Y`, both sides carried to `X ∩ W` along `j_W⁻¹ X ≅ X ∩ W` and
`j_X⁻¹ W ≅ X ∩ W`. -/
theorem pushforward_capProductSupportPullback_swap (Y : TopCat.{u}) {X W : Set Y}
    (hX : IsClosed X) (hW : IsClosed W) (hXd : HasProperNeighbourhoodDeformations X)
    (hWd : HasProperNeighbourhoodDeformations W)
    (hXWd : HasProperNeighbourhoodDeformations (X ∩ W))
    (hXWd' : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X))
    (hWXd' : HasProperNeighbourhoodDeformations (subsetInclusion X ⁻¹' W)) (i j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R)
        (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le)
        ((isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le).comp
          (isProperMap_preimageInterHom hW hX)) (k - j - i)).hom
      (capProductSupportPullback R (subsetInclusion W) hX hXWd' i (k - j) u
        (capProductSupport R Y hW hWd j k v a)) =
      congrDegree R (TopCat.of (X ∩ W : Set Y)) (by ring)
        ((((-1 : Rˣ) ^ (i * j) : Rˣ) : R) •
          (pushforward R (ModuleCat.of R R) (preimageInterHom X W)
            (isProperMap_preimageInterHom hX hW) (k - i - j)).hom
            (capProductSupportPullback R (subsetInclusion X) hW hWXd' j (k - i) v
              (capProductSupport R Y hX hXd i k u a))) := by
  have hWXd : HasProperNeighbourhoodDeformations (W ∩ X) := inter_comm X W ▸ hXWd
  rw [capProductSupportPullback_capProductSupport R Y hX hW hWd hXWd hXWd' i j k u v a]
  have h2 := capProductSupportPullback_capProductSupport R Y hW hX hXd hWXd hWXd' j i k v u a
  have hcomp : preimageInterHom X W =
      (preimageInterHom X W ≫ subsetInclusionOfSubset (inter_comm X W).le) ≫
        subsetInclusionOfSubset (inter_comm W X).le :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have hp1 : IsProperMap (preimageInterHom X W ≫ subsetInclusionOfSubset (inter_comm X W).le) :=
    (isProperMap_subsetInclusionOfSubset (hX.inter hW) (inter_comm X W).le).comp
      (isProperMap_preimageInterHom hX hW)
  have hp2 : IsProperMap (subsetInclusionOfSubset (Y := Y) (inter_comm W X).le) :=
    isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le
  rw [pushforward_congr_eq R hcomp (isProperMap_preimageInterHom hX hW) (hp2.comp hp1),
    pushforward_comp_apply' R (preimageInterHom X W ≫ subsetInclusionOfSubset (inter_comm X W).le)
      (subsetInclusionOfSubset (inter_comm W X).le) hp1 hp2, h2,
    pushforward_congrDegree_comm]
  have h3 := capProductSupport_congrIndex R Y (hW.inter hX) (hX.inter hW) hWXd hXWd
    (inter_comm W X) (add_comm j i) k (cohomologyWithSupports.cup R Y hW hX j i v u) a
  rw [cohomologyWithSupports.cup_comm R Y hX hW i j u v, map_smul, LinearMap.smul_apply] at h3
  have h4 := congrArg (fun x ↦ (((-1 : Rˣ) ^ (i * j) : Rˣ) : R) • x) h3
  simp only [smul_smul] at h4
  have hε : (((-1 : Rˣ) ^ (i * j) : Rˣ) : R) * (((-1 : Rˣ) ^ (i * j) : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, ← mul_zpow, neg_one_mul, neg_neg, one_zpow, Units.val_one]
  rw [hε, one_smul] at h4
  rw [h4, map_smul, map_smul, congrDegree_congrDegree, congrDegree_congrDegree]

/-- **Exchanging two cap products, even degree** (Fulton, proof of Theorem 19.2): for `i` even,
`j_W^* u ∩ (v ∩ a) = j_X^* v ∩ (u ∩ a)` in `H_{k-i-j}(X ∩ W)`. -/
theorem pushforward_capProductSupportPullback_swap_of_even (Y : TopCat.{u}) {X W : Set Y}
    (hX : IsClosed X) (hW : IsClosed W) (hXd : HasProperNeighbourhoodDeformations X)
    (hWd : HasProperNeighbourhoodDeformations W)
    (hXWd : HasProperNeighbourhoodDeformations (X ∩ W))
    (hXWd' : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X))
    (hWXd' : HasProperNeighbourhoodDeformations (subsetInclusion X ⁻¹' W)) {i : ℤ} (hi : Even i)
    (j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R)
        (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le)
        ((isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le).comp
          (isProperMap_preimageInterHom hW hX)) (k - j - i)).hom
      (capProductSupportPullback R (subsetInclusion W) hX hXWd' i (k - j) u
        (capProductSupport R Y hW hWd j k v a)) =
      congrDegree R (TopCat.of (X ∩ W : Set Y)) (by ring)
        ((pushforward R (ModuleCat.of R R) (preimageInterHom X W)
            (isProperMap_preimageInterHom hX hW) (k - i - j)).hom
            (capProductSupportPullback R (subsetInclusion X) hW hWXd' j (k - i) v
              (capProductSupport R Y hX hXd i k u a))) := by
  rw [pushforward_capProductSupportPullback_swap R Y hX hW hXd hWd hXWd hXWd' hWXd' i j k u v a]
  have hs : (((-1 : Rˣ) ^ (i * j) : Rˣ) : R) = 1 := by
    rw [(hi.mul_right j).neg_one_zpow, Units.val_one]
  rw [hs, one_smul]

end borelMooreHomology

end MMP
