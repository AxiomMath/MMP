module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.AssemblyGeneric
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.FundamentalGeneric
public import MMP.AlgebraicTopology.CapProduct.CupSupport
public import MMP.AlgebraicGeometry.CycleMap.RefinedIntersection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.PushforwardInjective

/-!
# Points of the diagonal and of the self-product of a complex scheme

Topological lemmas on the diagonal `δ : X ⟶ X ×_ℂ X` of a complex scheme and on complex points
of fibre products: a closed immersion `f` induces a bijective closed embedding on complex points
of the square `IsPullback.id_vert f`, `q₂ ∘ δ = id` and `q₂(x, y) = y` on complex points, and
degree transports of the exterior product `a × b` and of cap products with pulled-back classes.

## Main results

* `MMP.Chow.isOver_pullbackDiagonal`: the diagonal is a morphism over `ℂ`.
* `MMP.isClosedEmbedding_fibreSquarePointsHom_id_vert`,
  `MMP.surjective_fibreSquarePointsHom_id_vert`: for a closed immersion `f`, the comparison map
  `fibreSquarePointsHom (IsPullback.id_vert f)` is a surjective closed embedding.
* `MMP.map_snd_map_diagonal`, `MMP.map_snd_productHomeomorph_symm`: `q₂ ∘ δ = id` and
  `q₂(x, y) = y` on complex points.
* `MMP.productClass_congrDegree`, `MMP.congrDegree_capProductSupportPullback_congrDegree`:
  compatibility of the exterior product and of the cap product with degree transport.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Corollary 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TensorProduct

/-- The diagonal `X ⟶ X ×_ℂ X` is a morphism over `ℂ`. -/
theorem MMP.Chow.isOver_pullbackDiagonal (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] :
    (pullback.diagonal (X ↘ Spec (.of ℂ)) :
      X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))).IsOver (Spec (.of ℂ)) :=
  ⟨pullback.diagonal_snd_assoc _ _⟩

namespace MMP

open UnderlyingSpace

section Points

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

attribute [local instance] MMP.Chow.isOver_pullbackDiagonal

/-- For a closed immersion `f : X ⟶ Y` of complex schemes, the comparison map
`fibreSquarePointsHom (IsPullback.id_vert f)` on complex points is a closed embedding. -/
lemma isClosedEmbedding_fibreSquarePointsHom_id_vert {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f] :
    Topology.IsClosedEmbedding (fibreSquarePointsHom (IsPullback.id_vert f)) :=
  Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f)

/-- For a closed immersion `f : X ⟶ Y` of complex schemes, the comparison map
`fibreSquarePointsHom (IsPullback.id_vert f)` on complex points is surjective. -/
lemma surjective_fibreSquarePointsHom_id_vert {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f] :
    Function.Surjective (fibreSquarePointsHom (IsPullback.id_vert f)) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ : z ∈ range (map (K := ℂ) f) := by
    rwa [range_map_eq_preimage_of_isPullback (IsPullback.id_vert f)]
  exact ⟨y, rfl⟩

/-- `q₂ ∘ δ = id` on complex points. -/
lemma map_snd_map_diagonal (x : UnderlyingSpace ℂ X) :
    map (K := ℂ) (pullback.snd (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
      (map (K := ℂ) (pullback.diagonal (X ↘ Spec (.of ℂ))) x) = x :=
  UnderlyingSpace.ext (by
    rw [toHom_map, toHom_map, Category.assoc, pullback.diagonal_snd, Category.comp_id])

/-- `q₂ (x, y) = y` through `(X × X)(ℂ) ≅ X(ℂ) × X(ℂ)`. -/
lemma map_snd_productHomeomorph_symm (x y : UnderlyingSpace ℂ X) :
    map (K := ℂ) (pullback.snd (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
      ((productHomeomorph ℂ X X).symm (x, y)) = y := by
  have := congrArg Prod.snd ((productHomeomorph ℂ X X).apply_symm_apply (x, y))
  rwa [productHomeomorph_apply] at this

end Points

section ProductClass

variable {R : Type} [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- `a × b` with `b` transported along an equality of degrees. -/
lemma productClass_congrDegree {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    {k l : ℕ} {j : ℤ} (h : j = ((2 * l : ℕ) : ℤ))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * k : ℕ))
    (c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y)) j) :
    productClass R X Y a (BorelMooreCross.congrDegree R _ h c) =
      BorelMooreCross.congrDegree R _ (by omega)
        ((borelMooreHomology.pushforward R (ModuleCat.of R R)
          (TopCat.ofHom ((productHomeomorph ℂ X Y).symm :
            C(UnderlyingSpace ℂ X × UnderlyingSpace ℂ Y,
              UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))))))
          (productHomeomorph ℂ X Y).symm.isProperMap (((2 * k : ℕ) : ℤ) + j)).hom
          (borelMooreHomology.exteriorProduct R (TopCat.of (UnderlyingSpace ℂ X))
            (TopCat.of (UnderlyingSpace ℂ Y)) (2 * k : ℕ) j (a ⊗ₜ c))) := by
  subst h
  rw [productClass, BorelMooreCross.congrDegree_self, LinearEquiv.refl_apply,
    borelMooreHomology.pushforward_congrDegree]

/-- Transport of the degree of the class capped with `g^* u`. -/
lemma congrDegree_capProductSupportPullback_congrDegree {P' P : TopCat.{0}} (g : P' ⟶ P)
    {D : Set P} (hD : IsClosed D) (hDd : HasProperNeighbourhoodDeformations (g ⁻¹' D)) (s : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) P D s) {e e' t : ℤ} (he : e = e')
    (h₁ : e - s = t) (h₂ : e' - s = t) (z : borelMooreHomology R (ModuleCat.of R R) P' e) :
    BorelMooreCross.congrDegree R _ h₂
        (borelMooreHomology.capProductSupportPullback R g hD hDd s e' u
          (BorelMooreCross.congrDegree R P' he z)) =
      BorelMooreCross.congrDegree R _ h₁
        (borelMooreHomology.capProductSupportPullback R g hD hDd s e u z) := by
  subst he
  rfl

end ProductClass

end MMP
