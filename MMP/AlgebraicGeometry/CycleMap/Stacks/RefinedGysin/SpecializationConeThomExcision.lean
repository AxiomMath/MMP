module

public import MMP.AlgebraicTopology.RefinedGysin.Cone
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicTopology.CapProduct.Restriction
/-!
# Excision for cap products with supports (Fulton, proof of Theorem 19.2)

Let `h : P → W` be continuous, `D ⊆ W` closed, `c ∈ H^j(W, W - D)` and `a ∈ H_k P`. If
`h⁻¹ D` lies in an open subset `U ⊆ P`, read on a space `O` through a homeomorphism `e : O ≃ U`
(with `m : O → P` the resulting open embedding), and `b ∈ H_k O` is `a|_U` read on `O`, then
`h^* c ∩ a = r_* ((m ≫ h)^* c ∩ b)` in `H_{k-j}(h⁻¹ D)`, for `r : (m ≫ h)⁻¹ D → h⁻¹ D` the
restriction of `m` (a homeomorphism). The cap product only sees a neighbourhood of its support.

## Main results

* `MMP.borelMooreHomology.isProperMap_restrictPreimage_of_subset_range`
* `MMP.borelMooreHomology.capProductSupportPullback_eq_pushforward_of_restrict`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, §19.2.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

namespace borelMooreHomology

/-- The restriction of an embedding `m : O → P` to the preimage of a subset `X` of its range is a
homeomorphism onto `X`, so it is proper. -/
theorem isProperMap_restrictPreimage_of_subset_range {O P : Type*} [TopologicalSpace O]
    [TopologicalSpace P] {m : O → P} (hm : IsEmbedding m) {X : Set P} (hX : X ⊆ range m) :
    IsProperMap (X.restrictPreimage m) := by
  refine IsClosedEmbedding.isProperMap ⟨hm.restrictPreimage X, ?_⟩
  rw [Set.range_restrictPreimage]
  convert isClosed_univ
  ext x
  simpa using hX x.2

/-- An open embedding `m : O → P` onto `U`, given through a homeomorphism `e : O ≃ U`, is an
embedding with range `U`. -/
theorem isEmbedding_of_homeomorph_opens {O P : TopCat.{u}} {U : TopologicalSpace.Opens P}
    (e : O ≃ₜ U) (m : O ⟶ P) (hm : ∀ x, m x = (e x : P)) : IsEmbedding m := by
  have : (m : O → P) = Subtype.val ∘ e := funext hm
  rw [this]
  exact IsEmbedding.subtypeVal.comp e.isEmbedding

/-- A subset of `U` lies in the range of the open embedding `m : O → P` onto `U`. -/
theorem subset_range_of_homeomorph_opens {O P : TopCat.{u}} {U : TopologicalSpace.Opens P}
    (e : O ≃ₜ U) (m : O ⟶ P) (hm : ∀ x, m x = (e x : P)) {X : Set P} (hXU : X ⊆ U) :
    X ⊆ range m := fun x hx ↦ ⟨e.symm ⟨x, hXU hx⟩, by rw [hm, e.apply_symm_apply]⟩

variable (R : Type u) [CommRing R]

/-- **Excision for cap products with supports.** If `h⁻¹ D ⊆ U` for an open `U ⊆ P`, identified
with `O` through `e`, and `b ∈ H_k O` is `a|_U` read on `O`, then
`h^* c ∩ a = r_* ((m ≫ h)^* c ∩ b)` for the restriction `r : (m ≫ h)⁻¹ D → h⁻¹ D` of the open
embedding `m : O → P`. -/
theorem capProductSupportPullback_eq_pushforward_of_restrict
    {P W O : TopCat.{u}} [T5Space P] (h : P ⟶ W) {D : Set W} (hD : IsClosed D)
    (hd : HasProperNeighbourhoodDeformations (h ⁻¹' D))
    (U : TopologicalSpace.Opens P) (hDU : h ⁻¹' D ⊆ U)
    (e : O ≃ₜ U) (m : O ⟶ P) (hm : ∀ x, m x = (e x : P))
    (hd' : HasProperNeighbourhoodDeformations ((m ≫ h) ⁻¹' D))
    (j k : ℤ) (c : cohomologyWithSupports R (ModuleCat.of R R) W D j)
    (a : borelMooreHomology R (ModuleCat.of R R) P k)
    (b : borelMooreHomology R (ModuleCat.of R R) O k)
    (hb : (pushforward R (ModuleCat.of R R) (TopCat.ofHom (e : C(O, U))) e.isProperMap k).hom b =
      (restrict R (ModuleCat.of R R) U k).hom a) :
    capProductSupportPullback R h hD hd j k c a =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (m.hom.restrictPreimage (h ⁻¹' D)))
        (isProperMap_restrictPreimage_of_subset_range (isEmbedding_of_homeomorph_opens e m hm)
          (subset_range_of_homeomorph_opens e m hm hDU)) (k - j)).hom
        (capProductSupportPullback R (m ≫ h) hD hd' j k c b) := by
  set X : Set P := h ⁻¹' D with hXdef
  have hX : IsClosed X := hD.preimage h.hom.continuous
  have hm' : m = TopCat.ofHom (e : C(O, U)) ≫ inclHom U := by
    ext x
    exact hm x
  subst hm'
  have hXUd : HasProperNeighbourhoodDeformations ((inclHom U).hom ⁻¹' X) := by
    have := hd'.preimage_homeomorph e.symm
    convert this using 1
    ext u
    change h u.1 ∈ D ↔ h (e (e.symm u)).1 ∈ D
    rw [e.apply_symm_apply]
  have hW : opensInter U X = ⊤ := by
    ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ hDU x.2⟩
  have hWp : IsProperMap (inclHom (opensInter U X)) := by
    rw [hW]; exact isProperMap_inclHom_top
  have key := pushforward_opensInterMap_restrict_capProductSupport R P U hX hd hXUd j k
    ((cohomologyWithSupports.pullback R _ h D j).hom c) a
  have cone := pushforward_restrictPreimage_capProductSupportPullback_comp R
    (TopCat.ofHom (e : C(O, U))) e.isProperMap (inclHom U ≫ h) hD hXUd hd' j k c b
  have step : capProductSupportPullback R (inclHom U ≫ h) hD hXUd j k c
      ((restrict R (ModuleCat.of R R) U k).hom a) =
      capProductSupportPullback R (inclHom U) hX hXUd j k
        ((cohomologyWithSupports.pullback R _ h D j).hom c)
        ((restrict R (ModuleCat.of R R) U k).hom a) := by
    rw [capProductSupportPullback_apply, capProductSupportPullback_apply,
      cohomologyWithSupports.pullback_comp]
    rfl
  rw [hb, step, ← key] at cone
  rw [capProductSupportPullback_apply R h]
  set z := capProductSupport R P hX hd j k ((cohomologyWithSupports.pullback R _ h D j).hom c) a
  have h1 := pushforward_inclHom_restrict_of_eq_top R hW hWp (k - j) z
  have h2 := pushforward_id_apply' R (opensInterMap U X ≫ opensInterInv U X)
    ((isProperMap_opensInterInv U X).comp (isProperMap_opensInterMap U X))
    (opensInterMap_opensInterInv U X) (k - j)
    ((restrict R (ModuleCat.of R R) (opensInter U X) (k - j)).hom z)
  rw [← pushforward_comp_apply R _ _ (isProperMap_opensInterMap U X)
    (isProperMap_opensInterInv U X), ← cone] at h2
  rw [← h1, ← h2]
  erw [pushforward_comp_apply R _ _ _ (isProperMap_opensInterInv U X)
      ((isProperMap_opensInterInv U X).comp (e.isProperMap.restrictPreimage _)),
    pushforward_comp_apply R _ _ _ hWp]
  · exact pushforward_apply_congr R rfl _ _ _ _
  · exact isProperMap_restrictPreimage_of_subset_range (isEmbedding_of_homeomorph_opens e _ hm)
      (subset_range_of_homeomorph_opens e _ hm hDU)

end borelMooreHomology

end MMP
