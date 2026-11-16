module

public import MMP.AlgebraicTopology.CapProduct.SupportLemmas

/-!
# The neighbourhood cap product along homotopic maps (Fulton, §19.1)

Let `f₀, f₁ : Y' → Y` be joined by a proper homotopy `G : Y' × [0, 1] → Y`, `X ⊆ Y` closed, and
`L₀ ⊆ int L` closed sets with `X ∩ G(Y' × [0, 1]) ⊆ int L₀`. Then for a proper `g : L → Z`,
`c ∈ H^j(Y, Y - X)` and `β ∈ H_k Y'`,
`(g ∘ f₀)_* (f₀^* c ∩_{f₀⁻¹ L₀} β) = (g ∘ f₁)_* (f₁^* c ∩_{f₁⁻¹ L₀} β)` in `H_{k-j} Z`.
The cohomology classes `f₀^* c`, `f₁^* c` have different supports `f₀⁻¹ X`, `f₁⁻¹ X`, so they
cannot be compared directly; instead both sides are the push-forward along `g ∘ G` of
`G^* c ∩_{G⁻¹ L} (i_t)_* β`, `i_t : y ↦ (y, t)` (the projection formula for the neighbourhood cap
product), and `(i_0)_* = (i_1)_*`.

## Main results

* `MMP.borelMooreHomology.pushforward_capProductNbhd_pullback_comp`: the
  projection formula along `f`, for a class pulled back along `f ≫ F`.
* `MMP.borelMooreHomology.pushforward_capProductNbhd_pullback_eq_of_homotopy`: for maps `f₀`, `f₁`
  joined by a proper homotopy, the push-forwards of the neighbourhood cap products with `f₀^* c`
  and `f₁^* c` agree.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology unitInterval

universe u

namespace MMP

open MMP

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- The inclusion `y ↦ (y, t)` of the slice `Y' × {t}`. -/
def sliceInclusion (Y' : TopCat.{u}) (t : I) : Y' ⟶ TopCat.of (Y' × I) :=
  TopCat.ofHom ⟨fun y ↦ (y, t), by fun_prop⟩

omit [CommRing R] in
/-- The slice inclusion `y ↦ (y, t)` is a proper map. -/
lemma isProperMap_sliceInclusion (Y' : TopCat.{u}) (t : I) :
    IsProperMap (sliceInclusion Y' t) := by
  refine Topology.IsClosedEmbedding.isProperMap ⟨isEmbedding_prodMkLeft t, ?_⟩
  have : range (fun y : Y' ↦ (y, t)) = univ ×ˢ {t} := by
    ext ⟨y, s⟩
    simp only [mem_range, Prod.mk.injEq, mem_prod, mem_univ, mem_singleton_iff, true_and]
    exact ⟨fun ⟨_, _, h⟩ ↦ h.symm, fun h ↦ ⟨y, rfl, h.symm⟩⟩
  exact this ▸ isClosed_univ.prod isClosed_singleton

/-- The slice inclusions `Y' → Y' × [0, 1]` at `0` and at `1` induce the same push-forward on
Borel–Moore homology. -/
lemma pushforward_sliceInclusion_zero_eq_one (Y' : TopCat.{u}) (k : ℤ) :
    pushforward R (ModuleCat.of R R) (sliceInclusion Y' 0) (isProperMap_sliceInclusion Y' 0) k =
      pushforward R (ModuleCat.of R R) (sliceInclusion Y' 1)
        (isProperMap_sliceInclusion Y' 1) k := by
  let H : TopCat.Homotopy (sliceInclusion Y' 0) (sliceInclusion Y' 1) :=
    { toFun := fun p ↦ (p.2, p.1)
      continuous_toFun := by fun_prop
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact pushforward_eq_of_properHomotopy R _ _ _ H (Homeomorph.prodComm I Y').isProperMap k

/-- **The projection formula for a pulled-back class.** For proper `f : Y' → P`,
`F : P → Y`, closed `X`, `L₀ ⊆ int L` with `F⁻¹ X ⊆ int F⁻¹ L₀`, and a proper `g : L → Z`,
`(g ∘ F ∘ f)_* ((F ∘ f)^* c ∩_{(F ∘ f)⁻¹ L₀} β) = (g ∘ F)_* (F^* c ∩_{F⁻¹ L} f_* β)`. -/
theorem pushforward_capProductNbhd_pullback_comp {Y' P Y : TopCat.{u}} (f : Y' ⟶ P)
    (hf : IsProperMap f) (F : P ⟶ Y) (hF : IsProperMap F) {X L₀ L : Set Y} (hX : IsClosed X)
    (hL₀ : IsClosed L₀) (hL : IsClosed L) (hL₀L : L₀ ⊆ interior L)
    (hFX : F ⁻¹' X ⊆ interior (F ⁻¹' L₀)) {Z : TopCat.{u}} (g : TopCat.of L ⟶ Z)
    (hg : IsProperMap g) (h₀ : (f ≫ F) ⁻¹' X ⊆ interior ((f ≫ F) ⁻¹' L₀))
    (hFL : F ⁻¹' X ⊆ interior (F ⁻¹' L)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (β : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) (preimageRestrict (f ≫ F) (hL₀L.trans interior_subset) ≫ g)
        (hg.comp (isProperMap_preimageRestrict _ (show IsProperMap (f ≫ F) from hF.comp hf) hL₀ _))
        (k - j)).hom
      (capProductNbhd R Y' (hX.preimage (f ≫ F).hom.continuous)
        (hL₀.preimage (f ≫ F).hom.continuous) h₀ j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (f ≫ F) X j).hom c) β) =
      (pushforward R (ModuleCat.of R R) (preimageRestrict F (subset_refl L) ≫ g)
          (hg.comp (isProperMap_preimageRestrict _ hF hL _)) (k - j)).hom
        (capProductNbhd R P (hX.preimage F.hom.continuous) (hL.preimage F.hom.continuous) hFL j k
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) F X j).hom c)
          ((pushforward R (ModuleCat.of R R) f hf k).hom β)) := by
  have hL₀L' : F ⁻¹' L₀ ⊆ interior (F ⁻¹' L) :=
    (preimage_mono hL₀L).trans (preimage_interior_subset_interior_preimage F.hom.continuous)
  have key := pushforward_preimageRestrict_capProductNbhd R f hf (hX.preimage F.hom.continuous)
    (hL₀.preimage F.hom.continuous) (hL.preimage F.hom.continuous) hFX hL₀L' j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) F X j).hom c) β
  rw [← key, cohomologyWithSupports.pullback_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (pushforward_comp R (ModuleCat.of R R)
    (preimageRestrict f (preimage_mono (s := L₀) (f := F) (hL₀L.trans interior_subset)))
    (preimageRestrict F (subset_refl L) ≫ g)
    (isProperMap_preimageRestrict _ hf (hL₀.preimage F.hom.continuous) _)
    (hg.comp (isProperMap_preimageRestrict _ hF hL _)) (k - j))) _

/-- **The neighbourhood cap product along homotopic maps.** Let `G : Y' × [0, 1] → Y` be a
proper homotopy from `f₀` to `f₁`, `X ⊆ Y` closed, `L₀ ⊆ int L` closed with
`G q ∈ X → G q ∈ int L₀`, and `g : L → Z` proper. Then
`(g ∘ f₀)_* (f₀^* c ∩_{f₀⁻¹ L₀} β) = (g ∘ f₁)_* (f₁^* c ∩_{f₁⁻¹ L₀} β)`. -/
theorem pushforward_capProductNbhd_pullback_eq_of_homotopy {Y' Y : TopCat.{u}} (f₀ f₁ : Y' ⟶ Y)
    (hf₀ : IsProperMap f₀) (hf₁ : IsProperMap f₁) (G : C(Y' × I, Y)) (hG : IsProperMap G)
    (hG₀ : ∀ y, G (y, 0) = f₀ y) (hG₁ : ∀ y, G (y, 1) = f₁ y) {X L₀ L : Set Y}
    (hX : IsClosed X) (hL₀ : IsClosed L₀) (hL : IsClosed L) (hL₀L : L₀ ⊆ interior L)
    (hGX : ∀ q, G q ∈ X → G q ∈ interior L₀) {Z : TopCat.{u}} (g : TopCat.of L ⟶ Z)
    (hg : IsProperMap g) (h₀ : f₀ ⁻¹' X ⊆ interior (f₀ ⁻¹' L₀))
    (h₁ : f₁ ⁻¹' X ⊆ interior (f₁ ⁻¹' L₀)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (β : borelMooreHomology R (ModuleCat.of R R) Y' k) :
    (pushforward R (ModuleCat.of R R) (preimageRestrict f₀ (hL₀L.trans interior_subset) ≫ g)
        (hg.comp (isProperMap_preimageRestrict _ hf₀ hL₀ _)) (k - j)).hom
      (capProductNbhd R Y' (hX.preimage f₀.hom.continuous) (hL₀.preimage f₀.hom.continuous) h₀
        j k ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f₀ X j).hom c) β) =
    (pushforward R (ModuleCat.of R R) (preimageRestrict f₁ (hL₀L.trans interior_subset) ≫ g)
        (hg.comp (isProperMap_preimageRestrict _ hf₁ hL₀ _)) (k - j)).hom
      (capProductNbhd R Y' (hX.preimage f₁.hom.continuous) (hL₀.preimage f₁.hom.continuous) h₁
        j k ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f₁ X j).hom c) β) := by
  let F : TopCat.of (Y' × I) ⟶ Y := TopCat.ofHom G
  have hF : IsProperMap F := hG
  obtain rfl : f₀ = sliceInclusion Y' 0 ≫ F := by ext y; exact (hG₀ y).symm
  obtain rfl : f₁ = sliceInclusion Y' 1 ≫ F := by ext y; exact (hG₁ y).symm
  have hFX : F ⁻¹' X ⊆ interior (F ⁻¹' L₀) := fun q hq ↦
    preimage_interior_subset_interior_preimage F.hom.continuous (hGX q hq)
  have hFL : F ⁻¹' X ⊆ interior (F ⁻¹' L) := hFX.trans (interior_mono
    ((preimage_mono (hL₀L.trans interior_subset))))
  rw [pushforward_capProductNbhd_pullback_comp R _ (isProperMap_sliceInclusion Y' 0) F hF hX hL₀
      hL hL₀L hFX g hg h₀ hFL,
    pushforward_capProductNbhd_pullback_comp R _ (isProperMap_sliceInclusion Y' 1) F hF hX hL₀
      hL hL₀L hFX g hg h₁ hFL,
    pushforward_sliceInclusion_zero_eq_one]

end borelMooreHomology

end MMP
