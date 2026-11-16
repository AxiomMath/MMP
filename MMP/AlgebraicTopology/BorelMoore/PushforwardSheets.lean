module

public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import MMP.AlgebraicTopology.BorelMoore.TopHomologyBasis

/-!
# Push-forward and restriction over a disjoint union of sheets (Fulton, §19.1)

Let `F : X → Y` be a proper map of Hausdorff spaces, `U ⊆ Y` open, and suppose that
`F⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d` is a finite disjoint union of open subsets `U_i ⊆ X`, with
`F_i : U_i → U` the restrictions of `F`. Then for every class `a ∈ H_j X`,
`(F_* a)|_U = ∑_i F_{i*}(a|_{U_i})`.
This is the topological step of the proof of Fulton's Lemma 19.1.2.

## Main definitions

* `MMP.borelMooreHomology.sheetMap`: the restriction `U_i → U` of `F`.

## Main results

* `MMP.borelMooreHomology.pushforward_eq_of_hom_eq`: the push-forward only
  depends on the map.
* `MMP.borelMooreHomology.pushforward_pushforward_eq_comp`: elementwise
  functoriality.
* `MMP.borelMooreHomology.restrict_pushforward_eq_zero_of_disjoint`: a push-forward vanishes on
  an open set missing the image.
* `MMP.borelMooreHomology.restrict_pushforward_eq_sum_sheetMap`:
  `(F_* a)|_U = ∑_i F_{i*}(a|_{U_i})` when `F⁻¹(U)` is a disjoint union of open sheets `U_i`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.2.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Function

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- The push-forward along equal maps agrees. -/
lemma pushforward_eq_of_hom_eq {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (j : ℤ) : pushforward R M f hf j = pushforward R M g hg j := by
  subst h
  rfl

/-- Elementwise form of `pushforward_eq_of_hom_eq`. -/
lemma pushforward_apply_eq_of_hom_eq {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : f = g)
    (hf : IsProperMap f) (hg : IsProperMap g) (j : ℤ) (a : borelMooreHomology R M X j) :
    pushforward R M f hf j a = pushforward R M g hg j a := by
  subst h
  rfl

/-- Elementwise functoriality of push-forward: `g_* (f_* a) = (g ∘ f)_* a`. -/
lemma pushforward_pushforward_eq_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f) (hg : IsProperMap g) (j : ℤ) (a : borelMooreHomology R M X j) :
    pushforward R M g hg j (pushforward R M f hf j a) =
      pushforward R M (f ≫ g) (hg.comp hf) j a := by
  rw [pushforward_comp]
  rfl

/-- The restriction of a push-forward to an open set missing the image vanishes. -/
theorem restrict_pushforward_eq_zero_of_disjoint {X Y : TopCat.{u}} [T2Space X] [T2Space Y]
    (f : X ⟶ Y) (hf : IsProperMap f) (U : Opens Y) (hU : Disjoint (U : Set Y) (Set.range f))
    (j : ℤ) (a : borelMooreHomology R M X j) :
    restrict R M U j (pushforward R M f hf j a) = 0 := by
  rw [restrict_pushforward_apply]
  have : IsEmpty (TopCat.of (Opens.comap f.hom U)) :=
    ⟨fun x ↦ Set.disjoint_left.mp hU x.2 ⟨x.1, rfl⟩⟩
  rw [(ModuleCat.isZero_iff_subsingleton.mp
    (isZero_borelMooreHomology_of_isEmpty R M (TopCat.of (Opens.comap f.hom U)) j)).elim
    (restrict R M (Opens.comap f.hom U) j a) 0, map_zero]

/-- Push-forward along a homeomorphism and then along its inverse is the identity. -/
lemma pushforward_homeomorph_symm_apply {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (j : ℤ)
    (a : borelMooreHomology R M (TopCat.of X) j) :
    pushforward R M (TopCat.ofHom (e.symm : C(Y, X))) e.symm.isProperMap j
      (pushforward R M (TopCat.ofHom (e : C(X, Y))) e.isProperMap j a) = a := by
  rw [pushforward_pushforward_eq_comp,
    pushforward_eq_of_hom_eq R M (g := 𝟙 (TopCat.of X)) (by ext x; exact e.symm_apply_apply x) _
      (by simpa using isProperMap_id), pushforward_id]
  rfl

section sheets

variable {X Y : TopCat.{u}} [T2Space X] [T2Space Y] (F : X ⟶ Y) (hF : IsProperMap F)
  (U : Opens Y) {ι : Type} [Fintype ι] (Ui : ι → Opens X)

/-- The pieces `U_i`, read as open subsets of `F⁻¹(U)`. -/
abbrev sheetOpens (i : ι) : Opens (TopCat.of (Opens.comap F.hom U)) :=
  subOpens (Opens.comap F.hom U) (Ui i)

variable {Ui}

include hF in
/-- If `F⁻¹(U)` is the disjoint union of the open sets `U_i`, then the inclusion of each piece
`U_i` into `F⁻¹(U)` is a proper map. -/
lemma isProperMap_clopenInclusion_sheetOpens
    (hdisj : Pairwise (Disjoint on fun i ↦ (Ui i : Set X)))
    (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (i : ι) :
    IsProperMap (clopenInclusion (sheetOpens F U Ui i)) := by
  refine isProperMap_clopenInclusion (sheetOpens F U Ui) ?_ ?_ i
  · intro i j hij
    exact Set.disjoint_left.2 fun x hx hx' ↦ Set.disjoint_left.1 (hdisj hij) hx hx'
  · intro x
    have : (x.1 : X) ∈ F ⁻¹' (U : Set Y) := x.2
    rw [hpre] at this
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
    exact ⟨i, hi⟩

/-- If `F⁻¹(U) = ⋃ i, U_i`, then each `U_i` is contained in `F⁻¹(U)`. -/
lemma le_comap_of_preimage_eq (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (i : ι) :
    Ui i ≤ Opens.comap F.hom U := fun x hx ↦ by
  change x ∈ F ⁻¹' (U : Set Y)
  rw [hpre]
  exact Set.mem_iUnion.2 ⟨i, hx⟩

/-- The restriction `F_i : U_i → U` of `F` to a sheet `U_i ⊆ F⁻¹(U)`, as the composite
`U_i ≅ U_i ∩ F⁻¹(U) ⊆ F⁻¹(U) → U`. -/
def sheetMap (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (i : ι) :
    TopCat.of (Ui i) ⟶ TopCat.of U :=
  subOpensMap (Opens.comap F.hom U) (le_comap_of_preimage_eq F U hpre i) ≫
    clopenInclusion (sheetOpens F U Ui i) ≫ restrictPreimage F U

/-- The map `F_i : U_i → U` sends `x` to `F x`. -/
@[simp]
lemma sheetMap_apply (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (i : ι) (x : Ui i) :
    ((sheetMap F U hpre i x : U) : Y) = F x.1 :=
  rfl

include hF in
/-- If `F` is proper and `F⁻¹(U)` is the disjoint union of the open sets `U_i`, then each
restriction `F_i : U_i → U` is proper. -/
lemma isProperMap_sheetMap (hdisj : Pairwise (Disjoint on fun i ↦ (Ui i : Set X)))
    (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (i : ι) :
    IsProperMap (sheetMap F U hpre i) :=
  (isProperMap_restrictPreimage F U hF).comp
    ((isProperMap_clopenInclusion_sheetOpens F hF U hdisj hpre i).comp
      (isProperMap_subOpensMap _ _))

/-- **Push-forward over a disjoint union of sheets** (Fulton, §19.1, proof of Lemma 19.1.2): if
`F⁻¹(U) = U₁ ⊔ ⋯ ⊔ U_d` with the `U_i` open, then `(F_* a)|_U = ∑_i F_{i*}(a|_{U_i})`. -/
theorem restrict_pushforward_eq_sum_sheetMap
    (hdisj : Pairwise (Disjoint on fun i ↦ (Ui i : Set X)))
    (hpre : F ⁻¹' (U : Set Y) = ⋃ i, (Ui i : Set X)) (j : ℤ)
    (a : borelMooreHomology R M X j) :
    restrict R M U j (pushforward R M F hF j a) =
      ∑ i, pushforward R M (sheetMap F U hpre i) (isProperMap_sheetMap F hF U hdisj hpre i) j
        (restrict R M (Ui i) j a) := by
  rw [restrict_pushforward_apply]
  have hsum := congrArg (fun φ ↦ φ.hom (restrict R M (Opens.comap F.hom U) j a))
    (sum_restrict_pushforward R M (Y := TopCat.of (Opens.comap F.hom U)) (sheetOpens F U Ui)
      (by
        intro i j hij
        exact Set.disjoint_left.2 fun x hx hx' ↦ Set.disjoint_left.1 (hdisj hij) hx hx')
      (fun x ↦ by
        have : (x.1 : X) ∈ F ⁻¹' (U : Set Y) := x.2
        rw [hpre] at this
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
        exact ⟨i, hi⟩)
      (isProperMap_clopenInclusion_sheetOpens F hF U hdisj hpre) j)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at hsum
  rw [← hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [restrict_restrict_apply R M (Opens.comap F.hom U) (le_comap_of_preimage_eq F U hpre i),
    pushforward_pushforward_eq_comp, pushforward_pushforward_eq_comp]
  rfl

end sheets

end borelMooreHomology

end MMP
