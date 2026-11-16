module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointsUnderlyingSpace
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.Properties.RegularLocus
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Complex points of a subvariety and of its image under a closed immersion

Let `f : Y → X` be a closed immersion of complex schemes and `V` a subvariety of `Y`. The
subvariety `V` is isomorphic over `X` to its image `f(V)`, and `f` is injective on points. Hence
the complex points of `Y` lying over `f(V)` are exactly those of `V`, and the regular complex
points of `V` are those whose image is a regular point of `f(V)`.

## Main results

* `MMP.mem_image_regularPart_of_regularLocus_image`: a complex point `q` of `Y`
  whose image under `f` is a regular point of `f(V)` is the image of a regular complex point
  of `V`.
* `MMP.toHom_mapFun_mem_support_image`: the image under `f` of a complex point
  of `V` lies on the support of `f(V)`.

## Implementation notes

Subvarieties are `MMP.Intersection.Scheme.Subvariety` (an ideal sheaf with integral closed
subscheme); `V.ideal.subscheme` carries the structure over `Spec ℂ` of `MMP.SubschemeOver`.
Regularity is transported along the isomorphism `V ≅ f(V)` over `X`, an isomorphism being an
open immersion: the ideal sheaf of `f(V)` is the kernel of `V ↪ Y → X`, since `V` is reduced.

## References

* [Fulton, *Intersection Theory*][fulton1998], Chapter 19
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP

open MMP.Intersection.Scheme

variable {Y X : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))]

/-- A subvariety `V` of `Y` is isomorphic over `X`, along a closed immersion `f : Y → X`, to its
image subvariety `f(V)`: the ideal sheaf of `f(V)` is the kernel of `V ↪ Y → X`, `V` being
reduced. -/
private theorem exists_isIso_image_subschemeι (f : Y ⟶ X) [IsClosedImmersion f]
    (V : Subvariety Y) :
    ∃ φ : V.ideal.subscheme ⟶ (V.image f).ideal.subscheme,
      IsIso φ ∧ φ ≫ (V.image f).ideal.subschemeι = V.ideal.subschemeι ≫ f := by
  have h : (V.ideal.subschemeι ≫ f).ker = (V.image f).ideal := by
    rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
      Subvariety.ideal_eq_vanishingIdeal, Scheme.IdealSheafData.map_vanishingIdeal]
    rfl
  rw [← h]
  exact ⟨(V.ideal.subschemeι ≫ f).toImage, inferInstance, (V.ideal.subschemeι ≫ f).toImage_imageι⟩

/-- A complex point `q` of `Y` whose image under a closed immersion `f : Y → X` is a regular point
of the image subvariety `f(V)` is (the image of) a regular complex point of `V`. -/
theorem mem_image_regularPart_of_regularLocus_image (f : Y ⟶ X) [IsClosedImmersion f]
    [f.IsOver (Spec (.of ℂ))] (V : Subvariety Y) (q : UnderlyingSpace ℂ Y)
    (h : ∃ z ∈ regularLocus (V.image f).ideal.subscheme,
      (V.image f).ideal.subschemeι z = (mapFun (K := ℂ) f q).toHom (IsLocalRing.closedPoint ℂ)) :
    q ∈ mapFun (K := ℂ) V.ideal.subschemeι '' regularPart ℂ V.ideal.subscheme := by
  obtain ⟨z, hz, hzq⟩ := h
  obtain ⟨φ, hφ, hφι⟩ := exists_isIso_image_subschemeι f V
  obtain ⟨v, rfl⟩ : ∃ v, φ v = z :=
    ⟨(inv φ) z, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  have hv : V.ideal.subschemeι v = q.toHom (IsLocalRing.closedPoint ℂ) := by
    apply f.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← hφι, Scheme.Hom.comp_apply, hzq]
    rfl
  have hq : q ∈ range (mapFun (K := ℂ) V.ideal.subschemeι) := by
    rw [range_mapFun_of_isClosedImmersion]
    exact ⟨v, hv⟩
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, ?_, rfl⟩
  have hp : p.toHom (IsLocalRing.closedPoint ℂ) = v := by
    apply V.ideal.subschemeι.isClosedEmbedding.injective
    rw [hv]
    rfl
  rw [mem_regularPart_iff, hp, ← MMP.mem_regularLocus_iff_of_isOpenImmersion φ]
  exact hz

/-- The image under `f : Y → X` of a complex point of `V ⊆ Y` lies on the support of `f(V)`. -/
theorem toHom_mapFun_mem_support_image (f : Y ⟶ X) [f.IsOver (Spec (.of ℂ))] (V : Subvariety Y)
    {q : UnderlyingSpace ℂ Y} (hq : q ∈ range (mapFun (K := ℂ) V.ideal.subschemeι)) :
    (mapFun (K := ℂ) f q).toHom (IsLocalRing.closedPoint ℂ) ∈ (V.image f).support := by
  obtain ⟨p, rfl⟩ := hq
  rw [show (V.image f).support = closure (f '' V.support) from
    Scheme.IdealSheafData.coe_support_vanishingIdeal _]
  refine subset_closure ⟨V.ideal.subschemeι (p.toHom (IsLocalRing.closedPoint ℂ)), ?_, rfl⟩
  change _ ∈ (V.ideal.support : Set Y)
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, rfl⟩

end MMP
