module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.AlgebraicGeometry.Pullbacks.Over
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The underlying space of a product of schemes over a topological field

For schemes `V`, `W` over a topological field `K`, the map `(V × W)(K) → V(K) × W(K)`,
`w ↦ (pr₁ w, pr₂ w)`, is a homeomorphism: it is an embedding
(`MMP.UnderlyingSpace.isEmbedding_prodMap_of_isPullback`), and it is onto since
`(Spec K)(K)` is a point.

## Main definitions

* `MMP.UnderlyingSpace.productHomeomorph`: `(V × W)(K) ≃ₜ V(K) × W(K)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

namespace UnderlyingSpace

variable (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]
  [T1Space K] (V W : Scheme.{u}) [V.Over (Spec (.of K))] [W.Over (Spec (.of K))]

omit [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K] in
/-- `Spec K` is over itself by the identity. -/
lemma spec_over_self : (Spec (.of K) ↘ Spec (.of K)) = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

omit [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K] in
/-- For a scheme `X` over `Spec K`, the structure morphism `X ⟶ Spec K` is a morphism over
`Spec K`. -/
instance isOver_over (X : Scheme.{u}) [X.Over (Spec (.of K))] :
    (X ↘ Spec (.of K)).IsOver (Spec (.of K)) :=
  ⟨by rw [spec_over_self, Category.comp_id]⟩

omit [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K] in
/-- `(Spec K)(K)` is a point. -/
instance subsingleton_spec : Subsingleton (UnderlyingSpace K (Spec (.of K))) :=
  ⟨fun p q ↦ UnderlyingSpace.ext (by
    have hp := p.toHom_comp_over
    have hq := q.toHom_comp_over
    rw [spec_over_self, Category.comp_id] at hp hq
    rw [hp, hq])⟩

/-- The map `(V × W)(K) → V(K) × W(K)`, `w ↦ (pr₁ w, pr₂ w)`, is surjective. -/
lemma surjective_prodMap_product :
    Function.Surjective (prodMap (K := K) (pullback.fst (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))
      (pullback.snd (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))) := by
  intro z
  have h := range_prodMap_of_isPullback (K := K)
    (IsPullback.of_hasPullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))
  have hz : z ∈ Set.range (prodMap (K := K)
      (pullback.fst (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))
      (pullback.snd (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))) := by
    rw [h]
    exact Subsingleton.elim _ _
  exact hz

/-- The homeomorphism `(V × W)(K) ≃ₜ V(K) × W(K)`, `w ↦ (pr₁ w, pr₂ w)`. -/
def productHomeomorph :
    UnderlyingSpace K (pullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) ≃ₜ
      UnderlyingSpace K V × UnderlyingSpace K W :=
  (Equiv.ofBijective _ ⟨(isEmbedding_prodMap_of_isPullback (K := K)
      (IsPullback.of_hasPullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))).injective,
    surjective_prodMap_product K V W⟩).toHomeomorphOfIsInducing
    (isEmbedding_prodMap_of_isPullback (K := K)
      (IsPullback.of_hasPullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))).isInducing

/-- `productHomeomorph K V W` sends `w` to `(pr₁ w, pr₂ w)`. -/
@[simp]
lemma productHomeomorph_apply
    (w : UnderlyingSpace K (pullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))) :
    productHomeomorph K V W w =
      (mapFun (pullback.fst (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) w,
        mapFun (pullback.snd (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) w) :=
  rfl

end UnderlyingSpace

end MMP
