module

public import MMP.AlgebraicTopology.CapProduct.Cup
public import MMP.AlgebraicTopology.CapProduct.CupHomotopy
/-!
# The cap product with a cup product (Fulton, §19.1, (8))

Let `X`, `W` be closed subsets of a space `Y`, `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)` and
`a ∈ H_k Y`, with `j : W → Y` the inclusion. Then `(u ∪ v) ∩ a = j^* u ∩ (v ∩ a)` in
`H_{k-i-j}(X ∩ W)` (`MMP.borelMooreHomology.capProductSupport_cup`), for the cap product
`φ ∩ σ = φ (σ ⌊ [q, …, n]) σ ⌊ [0, …, q]` (Fulton's convention: on chains
`(φ ∪ ψ) ∩ c = φ ∩ (ψ ∩ c)`).

## Main definitions

* `MMP.borelMooreHomology.preimageInterHom`: the canonical map `ι⁻¹ W → X ∩ W` for the
  inclusion `ι : X → Y`.

## Main results

* `MMP.borelMooreHomology.capProductSupportPullback_capProductSupport`: the formula as a
  push-forward along `j⁻¹ X ≅ X ∩ W`.
* `MMP.borelMooreHomology.pushforward_capProduct_pullback`: the projection formula
  `f_* (f^* c ∩ a) = c ∩ f_* a`.
* `MMP.borelMooreHomology.capProductSupport_cup`: Fulton's (8).

## Implementation notes

Take a proper retraction `t : L → X ∩ W` of a closed neighbourhood, a smaller closed
neighbourhood `L₀ ⊆ int L` of `X ∩ W`, and a proper deformation `G : N × [0, 1] → Y` of a closed
neighbourhood `N` of `W` onto `W`, with retraction `r`, inside `int L₀ ∪ (Y - X)`. Then
* `(u ∪ v) ∩_L a = ι_N^* u ∩_{N ∩ L} (v ∩_N a)` (chain level);
* `G` moves `ι_N^* u` to `r^* j^* u`, and it maps the support `X` into `int L₀`, so the
  push-forwards along `t` agree;
* the projection formula along `r` turns `r^* j^* u ∩ (v ∩_N a)` into `j^* u ∩ r_* (v ∩_N a)`,
  and `r_* (v ∩_N a) = v ∩ a`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (8).
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u

namespace MMP

namespace borelMooreHomology

open BorelMooreCross

variable (R : Type u) [CommRing R]

/-- The canonical map `ι⁻¹ W → X ∩ W`, `y ↦ y`, for the inclusion `ι : X → Y`. -/
def preimageInterHom {Y : TopCat.{u}} (X W : Set Y) :
    TopCat.of (subsetInclusion X ⁻¹' W) ⟶ TopCat.of (X ∩ W : Set Y) :=
  TopCat.ofHom ⟨fun y ↦ ⟨y.1.1, y.1.2, y.2⟩, by fun_prop⟩

@[simp]
lemma coe_preimageInterHom_apply {Y : TopCat.{u}} (X W : Set Y)
    (y : subsetInclusion X ⁻¹' W) : (preimageInterHom X W y : Y) = y.1.1 :=
  rfl

/-- For closed `X`, `W`, the map `preimageInterHom X W : ι⁻¹ W → X ∩ W` is proper. -/
lemma isProperMap_preimageInterHom {Y : TopCat.{u}} {X W : Set Y} (hX : IsClosed X)
    (hW : IsClosed W) : IsProperMap (preimageInterHom X W) :=
  isProperMap_of_comp_of_inj (preimageInterHom X W).hom.continuous continuous_subtype_val
    ((isProperMap_subsetInclusion hX).comp
      (isProperMap_subsetInclusion (hW.preimage (subsetInclusion X).hom.continuous)))
    Subtype.val_injective

/-- The push-forward along a composite `f ≫ g` of proper maps, applied to a class `x`, is the
push-forward along `g` of the push-forward of `x` along `f`; the reverse of
`pushforward_comp_apply`, with the properness of `f ≫ g` fixed to `hg.comp hf`. -/
lemma pushforward_comp_apply' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f)
    (hg : IsProperMap g) (k : ℤ) (x : borelMooreHomology R (ModuleCat.of R R) X k) :
    (pushforward R (ModuleCat.of R R) (f ≫ g) (hg.comp hf) k).hom x =
      (pushforward R (ModuleCat.of R R) g hg k).hom
        ((pushforward R (ModuleCat.of R R) f hf k).hom x) := by
  rw [pushforward_comp]
  rfl

/-- **Projection formula**, absolute target. For a proper `f : Y' → Y`, a closed `X ⊆ Y`,
`c ∈ H^j(Y, Y - X)` and `a ∈ H_k Y'`, `f_* (f^* c ∩ a) = c ∩ f_* a` in `H_{k-j} Y`. -/
theorem pushforward_capProduct_pullback {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) (hf : IsProperMap f)
    {X : Set Y} (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations X)
    (hX'd : HasProperNeighbourhoodDeformations (f ⁻¹' X)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) f hf (k - j)).hom
        (capProduct R Y' (f ⁻¹' X) j k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f X j).hom c) a) =
      capProduct R Y X j k c ((pushforward R (ModuleCat.of R R) f hf k).hom a) := by
  rw [← pushforward_subsetInclusion_capProductSupport R Y' (hX.preimage f.hom.continuous) hX'd,
    ← pushforward_subsetInclusion_capProductSupport R Y hX hXd,
    ← pushforward_restrictPreimage_capProductSupportPullback R f hf hX hXd hX'd,
    capProductSupportPullback_apply, ← pushforward_comp_apply']
  refine Eq.trans ?_ (pushforward_comp_apply' R (TopCat.ofHom (f.hom.restrictPreimage X))
    (subsetInclusion X) (hf.restrictPreimage X) (isProperMap_subsetInclusion hX) _ _)
  rfl

/-- The push-forward along `j⁻¹ X ≅ X ∩ W` of `j^* u ∩ b`, for `j : W → Y` the inclusion, computed
through a proper retraction `t : L → X ∩ W` of a closed neighbourhood `L` of `X ∩ W`. -/
theorem pushforward_preimageInterHom_capProductSupportPullback (Y : TopCat.{u}) {X W L : Set Y}
    (hX : IsClosed X) (hW : IsClosed W) (hL : IsClosed L)
    (hXd : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X))
    (hFL : subsetInclusion W ⁻¹' X ⊆ interior (subsetInclusion W ⁻¹' L))
    (t : C(L, (X ∩ W : Set Y))) (ht : IsProperMap t)
    (htX : ∀ y : L, (y : Y) ∈ X ∩ W → (t y : Y) = y) (i k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of W) k) :
    (pushforward R (ModuleCat.of R R)
        (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le)
        ((isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le).comp
          (isProperMap_preimageInterHom hW hX)) (k - i)).hom
      (capProductSupportPullback R (subsetInclusion W) hX hXd i k u b) =
      (pushforward R (ModuleCat.of R R)
          (preimageRestrict (subsetInclusion W) (subset_refl L) ≫ TopCat.ofHom t)
          (ht.comp (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hW) hL
            (subset_refl L)))
          (k - i)).hom
        (capProductNbhd R (TopCat.of W) (hX.preimage (subsetInclusion W).hom.continuous)
          (hL.preimage (subsetInclusion W).hom.continuous) hFL i k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion W) X i).hom u)
          b) := by
  let t' : C(subsetInclusion W ⁻¹' L, subsetInclusion W ⁻¹' X) :=
    ⟨fun y ↦ ⟨⟨(t ⟨y.1.1, y.2⟩ : Y), (t ⟨y.1.1, y.2⟩).2.2⟩, (t ⟨y.1.1, y.2⟩).2.1⟩, by fun_prop⟩
  have hinj : Function.Injective
      (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le) := fun y y' hyy' ↦
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : (X ∩ W : Set Y) → Y) hyy'))
  have ht' : IsProperMap t' := isProperMap_of_comp_of_inj t'.continuous
    (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le).hom.continuous
    (ht.comp (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hW) hL
      (subset_refl L))) hinj
  have ht'X : ∀ y : subsetInclusion W ⁻¹' L, (y : TopCat.of W) ∈ subsetInclusion W ⁻¹' X →
      (t' y : TopCat.of W) = y := fun y hy ↦ Subtype.ext (htX ⟨y.1.1, y.2⟩ ⟨hy, y.1.2⟩)
  rw [capProductSupportPullback_apply, capProductSupport_eq_capProductAlong R (TopCat.of W)
    (hX.preimage (subsetInclusion W).hom.continuous) hXd
    (hL.preimage (subsetInclusion W).hom.continuous) hFL t' ht' ht'X,
    capProductAlong, LinearMap.compr₂_apply, ← pushforward_comp_apply']
  rfl

/-- **The cap product with a cup product**, as a push-forward (Fulton §19.1, (8)). For closed
`X`, `W` in `Y`, `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)`, `a ∈ H_k Y` and `j : W → Y` the
inclusion, the push-forward of `j^* u ∩ (v ∩ a) ∈ H_{k-j-i}(j⁻¹ X)` along `j⁻¹ X ≅ X ∩ W` is
`(u ∪ v) ∩ a`. The closed sets `W`, `X ∩ W ⊆ Y` and `j⁻¹ X ⊆ W` carry the setting of the cap
products. -/
theorem capProductSupportPullback_capProductSupport (Y : TopCat.{u}) {X W : Set Y}
    (hX : IsClosed X) (hW : IsClosed W) (hWd : HasProperNeighbourhoodDeformations W)
    (hXWd : HasProperNeighbourhoodDeformations (X ∩ W))
    (hXd : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X)) (i j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R)
        (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le)
        ((isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le).comp
          (isProperMap_preimageInterHom hW hX)) (k - j - i)).hom
      (capProductSupportPullback R (subsetInclusion W) hX hXd i (k - j) u
        (capProductSupport R Y hW hWd j k v a)) =
      congrDegree R (TopCat.of (X ∩ W : Set Y)) (by ring)
        (capProductSupport R Y (hX.inter hW) hXWd (i + j) k
          (cohomologyWithSupports.cup R Y hX hW i j u v) a) := by
  obtain ⟨L, hL, hXWL, -, t, ht, htX, -⟩ := hXWd univ Filter.univ_mem
  obtain ⟨L₀, hL₀, hXWL₀, hL₀L, -⟩ := hXWd (interior L) (isOpen_interior.mem_nhdsSet.2 hXWL)
  have hWM : W ⊆ interior L₀ ∪ Xᶜ := fun x hx ↦ (em (x ∈ X)).imp (fun h ↦ hXWL₀ ⟨h, hx⟩) id
  obtain ⟨N, hN, hWN, hNM, r, hr, hrW, G, hG, hG0, hG1, -, hGM⟩ :=
    hWd _ ((isOpen_interior.union hX.isOpen_compl).mem_nhdsSet.2 hWM)
  have hL₀L' : L₀ ⊆ L := hL₀L.trans interior_subset
  have hXL₀ : subsetInclusion N ⁻¹' X ⊆ interior (subsetInclusion N ⁻¹' L₀) := fun y hy ↦
    preimage_interior_subset_interior_preimage (subsetInclusion N).hom.continuous
      ((hNM y.2).resolve_right (· hy))
  have hXL : subsetInclusion N ⁻¹' X ⊆ interior (subsetInclusion N ⁻¹' L) :=
    hXL₀.trans (interior_mono (preimage_mono hL₀L'))
  have hFL : subsetInclusion W ⁻¹' X ⊆ interior (subsetInclusion W ⁻¹' L) := fun x hx ↦
    preimage_interior_subset_interior_preimage (subsetInclusion W).hom.continuous (hXWL ⟨hx, x.2⟩)
  have hFL₀ : subsetInclusion W ⁻¹' X ⊆ interior (subsetInclusion W ⁻¹' L₀) := fun x hx ↦
    preimage_interior_subset_interior_preimage (subsetInclusion W).hom.continuous (hXWL₀ ⟨hx, x.2⟩)
  have hrL₀ : (TopCat.ofHom r ≫ subsetInclusion W) ⁻¹' X ⊆
      interior ((TopCat.ofHom r ≫ subsetInclusion W) ⁻¹' L₀) := fun y hy ↦
    preimage_interior_subset_interior_preimage
      (TopCat.ofHom r ≫ subsetInclusion W).hom.continuous (hXWL₀ ⟨hy, (r y).2⟩)
  set β := capProductNbhd R Y hW hN hWN j k v a
  have hA : congrDegree R (TopCat.of (X ∩ W : Set Y)) (by ring)
      (capProductSupport R Y (hX.inter hW) hXWd (i + j) k
        (cohomologyWithSupports.cup R Y hX hW i j u v) a) =
      (pushforward R (ModuleCat.of R R) (preimageRestrict (subsetInclusion N) hL₀L' ≫
          TopCat.ofHom t) (ht.comp (isProperMap_preimageRestrict _ (isProperMap_subsetInclusion hN)
            hL₀ _)) (k - j - i)).hom
        (capProductNbhd R (TopCat.of N) (hX.preimage (subsetInclusion N).hom.continuous)
          (hL₀.preimage (subsetInclusion N).hom.continuous) hXL₀ i (k - j)
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (subsetInclusion N) X i).hom u)
          β) := by
    rw [capProductSupport_eq_capProductAlong R Y (hX.inter hW) hXWd hL hXWL t ht htX,
      capProductAlong, LinearMap.compr₂_apply, pushforward_eq_homologyMap,
      ← homologyMap_congrDegree, ← pushforward_eq_homologyMap,
      ← pushforward_preimageRestrict_capProductNbhd_capProductNbhd R Y hX hW hN hL hWN hXWL hXL,
      ← pushforward_subsetInclusionOfSubset_capProductNbhd R (TopCat.of N)
        (hX.preimage (subsetInclusion N).hom.continuous)
        (hL.preimage (subsetInclusion N).hom.continuous) hXL
        (hL₀.preimage (subsetInclusion N).hom.continuous) hXL₀ (preimage_mono hL₀L'),
      ← pushforward_comp_apply', ← pushforward_comp_apply']
    rfl
  have hB := pushforward_capProductNbhd_pullback_eq_of_homotopy R (subsetInclusion N)
    (TopCat.ofHom r ≫ subsetInclusion W) (isProperMap_subsetInclusion hN)
    ((isProperMap_subsetInclusion hW).comp hr) G hG hG0 hG1 hX hL₀ hL hL₀L
    (fun q hq ↦ (hGM q).resolve_right (· hq)) (TopCat.ofHom t) ht hXL₀ hrL₀ i (k - j) u β
  have hC := pushforward_capProductNbhd_pullback_comp R (TopCat.ofHom r) hr (subsetInclusion W)
    (isProperMap_subsetInclusion hW) hX hL₀ hL hL₀L hFL₀ (TopCat.ofHom t) ht hrL₀ hFL i (k - j) u β
  have hD : (pushforward R (ModuleCat.of R R) (TopCat.ofHom r) hr (k - j)).hom β =
      capProductSupport R Y hW hWd j k v a := by
    rw [capProductSupport_eq_capProductAlong R Y hW hWd hN hWN r hr hrW]
    rfl
  have hE := pushforward_preimageInterHom_capProductSupportPullback R Y hX hW hL hXd hFL t ht htX
    i (k - j) u (capProductSupport R Y hW hWd j k v a)
  rw [hE, ← hD, ← hC, ← hB, hA]

/-- Transporting a class along `S = S'` and `m = m'` (`cohomologyWithSupports.congrIndex`)
transports its cap product along `S ⊆ S'`, up to the degree identification `k - m = k - m'`. -/
lemma capProductSupport_congrIndex (Y : TopCat.{u}) {S S' : Set Y} (hS : IsClosed S)
    (hS' : IsClosed S') (hSd : HasProperNeighbourhoodDeformations S)
    (hS'd : HasProperNeighbourhoodDeformations S') (h : S = S') {m m' : ℤ} (hm : m = m') (k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y S m)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    capProductSupport R Y hS' hS'd m' k
        (cohomologyWithSupports.congrIndex R Y (congrArg compl h) hm c) a =
      congrDegree R (TopCat.of S') (by rw [hm])
        ((pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset h.le)
          (isProperMap_subsetInclusionOfSubset hS h.le) (k - m)).hom
            (capProductSupport R Y hS hSd m k c a)) := by
  subst h hm
  change _ = (pushforward R (ModuleCat.of R R) (𝟙 (TopCat.of S)) _ (k - m)).hom _
  rw [pushforward_id]
  rfl

/-- **The cap product with a cup product** (Fulton §19.1, (8); [BT] 2.2 (A1)). For closed `X`,
`W` in `Y`, `u ∈ H^i(Y, Y - X)`, `v ∈ H^j(Y, Y - W)`, `a ∈ H_k Y` and `j : W → Y` the inclusion,
`(u ∪ v) ∩ a = j^* u ∩ (v ∩ a)` in `H_{k-j-i}(X ∩ W)`, the right side transported along
`j⁻¹ X ≅ X ∩ W`. The closed sets `W`, `X ∩ W ⊆ Y` and `j⁻¹ X ⊆ W` carry the setting of the cap
products. -/
theorem capProductSupport_cup (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W)
    (hWd : HasProperNeighbourhoodDeformations W)
    (hXWd : HasProperNeighbourhoodDeformations (X ∩ W))
    (hXd : HasProperNeighbourhoodDeformations (subsetInclusion W ⁻¹' X)) (i j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) Y X i)
    (v : cohomologyWithSupports R (ModuleCat.of R R) Y W j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    congrDegree R (TopCat.of (X ∩ W : Set Y)) (by ring)
        (capProductSupport R Y (hX.inter hW) hXWd (i + j) k
          (cohomologyWithSupports.cup R Y hX hW i j u v) a) =
      (pushforward R (ModuleCat.of R R)
        (preimageInterHom W X ≫ subsetInclusionOfSubset (inter_comm W X).le)
        ((isProperMap_subsetInclusionOfSubset (hW.inter hX) (inter_comm W X).le).comp
          (isProperMap_preimageInterHom hW hX)) (k - j - i)).hom
        (capProductSupportPullback R (subsetInclusion W) hX hXd i (k - j) u
          (capProductSupport R Y hW hWd j k v a)) :=
  (capProductSupportPullback_capProductSupport R Y hX hW hWd hXWd hXd i j k u v a).symm

end borelMooreHomology

end MMP
