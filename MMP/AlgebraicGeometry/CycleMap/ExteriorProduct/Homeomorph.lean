module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomeomorphGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointsUnderlyingSpace
public import MMP.AlgebraicGeometry.Properties.RegularLocus
public import MMP.AlgebraicGeometry.Pullbacks.Over
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering

/-!
# The underlying space of a product (Fulton, §19.1)

For schemes `V`, `W` over a topological field `K`, the map `(V × W)(K) → V(K) × W(K)`,
`w ↦ (pr₁ w, pr₂ w)`, is a homeomorphism: it is an embedding
(`MMP.UnderlyingSpace.isEmbedding_prodMap_of_isPullback`), and it is onto since
`(Spec K)(K)` is a point. This file restricts that homeomorphism,
`MMP.UnderlyingSpace.productHomeomorph`, to regular points over `ℂ`.

## Main definitions

* `MMP.UnderlyingSpace.regularProdOpens`: the open subset `V_reg(ℂ) × W_reg(ℂ)` of `(V × W)(ℂ)`.
* `MMP.UnderlyingSpace.regularProdHomeomorph`: the homeomorphism from `V_reg(ℂ) × W_reg(ℂ)` onto
  the corresponding open subset of `(V × W)_reg(ℂ)`.

## Main results

* `MMP.UnderlyingSpace.prod_regularPart_subset_image_regularPart`: over an algebraically closed
  field, every pair of regular points is the image of a regular point of `V × W`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

namespace UnderlyingSpace

section Regular

variable (V W : Scheme.{0}) [V.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
  [LocallyOfFiniteType (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]

/-- The open subset `V_reg(ℂ) × W_reg(ℂ)` of `(V × W)(ℂ)`. -/
def regularProdOpens :
    TopologicalSpace.Opens (UnderlyingSpace ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))) :=
  ⟨productHomeomorph ℂ V W ⁻¹' (regularPart ℂ V ×ˢ regularPart ℂ W),
    (isOpen_regularPart.prod isOpen_regularPart).preimage (productHomeomorph ℂ V W).continuous⟩

/-- A point `w` of `(V × W)(ℂ)` lies in `regularProdOpens V W` if and only if both of its
projections are regular points. -/
lemma mem_regularProdOpens
    {w : UnderlyingSpace ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))} :
    w ∈ regularProdOpens V W ↔ productHomeomorph ℂ V W w ∈ regularPart ℂ V ×ˢ regularPart ℂ W :=
  Iff.rfl

/-- Fulton's `V_reg × W_reg ⊆ (V × W)_reg` (Example 19.1.9) on underlying spaces: over an
algebraically closed field `K`, under the identification `(V × W)(K) = V(K) × W(K)` given by the
two projections, every pair of regular points is the image of a regular point of `V × W`. -/
theorem prod_regularPart_subset_image_regularPart (K : Type u) [Field K] [IsAlgClosed K]
    (V W : Scheme.{u}) [V.Over (Spec (.of K))] [W.Over (Spec (.of K))]
    [LocallyOfFiniteType (V ↘ Spec (.of K))] [LocallyOfFiniteType (W ↘ Spec (.of K))] :
    regularPart K V ×ˢ regularPart K W ⊆
      prodMap (K := K) (pullback.fst (V ↘ Spec (.of K)) (W ↘ Spec (.of K)))
        (pullback.snd (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) ''
          regularPart K (pullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) := by
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  have hpq : p.toHom ≫ V ↘ Spec (.of K) = q.toHom ≫ W ↘ Spec (.of K) := by simp
  let w : UnderlyingSpace K (pullback (V ↘ Spec (.of K)) (W ↘ Spec (.of K))) :=
    ⟨pullback.lift p.toHom q.toHom hpq, by
      change pullback.lift p.toHom q.toHom hpq ≫ pullback.snd _ _ ≫ W ↘ Spec (.of K) = _
      rw [pullback.lift_snd_assoc, q.toHom_comp_over]⟩
  refine ⟨w, ?_, ?_⟩
  · rw [mem_regularPart_iff]
    rw [mem_regularPart_iff] at hp hq
    refine MMP.mem_regularLocus_pullback K _ _ _ ?_ ?_
    · change (pullback.lift p.toHom q.toHom hpq ≫ pullback.fst _ _) _ ∈ _
      rwa [pullback.lift_fst]
    · change (pullback.lift p.toHom q.toHom hpq ≫ pullback.snd _ _) _ ∈ _
      rwa [pullback.lift_snd]
  · exact Prod.ext (UnderlyingSpace.ext (pullback.lift_fst _ _ _))
      (UnderlyingSpace.ext (pullback.lift_snd _ _ _))

/-- Fulton's `V_reg × W_reg ⊆ (V × W)_reg`, on underlying spaces. -/
lemma regularProdOpens_le :
    regularProdOpens V W ≤ regularOpens ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))) := by
  intro w hw
  obtain ⟨w', hw', he⟩ := prod_regularPart_subset_image_regularPart ℂ V W hw
  have : w' = w := (productHomeomorph ℂ V W).injective he
  exact this ▸ hw'

/-- The homeomorphism `V_reg(ℂ) × W_reg(ℂ) ≃ₜ (V × W)_reg(ℂ) ∩ (V_reg(ℂ) × W_reg(ℂ))`, the
inverse of `w ↦ (pr₁ w, pr₂ w)`. -/
def regularProdHomeomorph :
    regularOpens ℂ V × regularOpens ℂ W ≃ₜ regularOpensInter (regularProdOpens V W) where
  toFun z := ⟨⟨(productHomeomorph ℂ V W).symm (z.1.1, z.2.1),
      regularProdOpens_le V W (by
        rw [mem_regularProdOpens, Homeomorph.apply_symm_apply]
        exact ⟨z.1.2, z.2.2⟩)⟩, by
    change _ ∈ regularProdOpens V W
    rw [mem_regularProdOpens, Homeomorph.apply_symm_apply]
    exact ⟨z.1.2, z.2.2⟩⟩
  invFun w :=
    (⟨(productHomeomorph ℂ V W w.1.1).1, w.2.1⟩, ⟨(productHomeomorph ℂ V W w.1.1).2, w.2.2⟩)
  left_inv z := by
    ext <;> simp
  right_inv w := Subtype.ext (Subtype.ext ((productHomeomorph ℂ V W).symm_apply_apply w.1.1))
  continuous_toFun := by
    refine Continuous.subtype_mk
      (Continuous.subtype_mk ((productHomeomorph ℂ V W).symm.continuous.comp ?_) _) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have h : Continuous fun w : regularOpensInter (regularProdOpens V W) ↦
        productHomeomorph ℂ V W w.1.1 :=
      (productHomeomorph ℂ V W).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    exact (h.fst.subtype_mk _).prodMk (h.snd.subtype_mk _)

/-- The image of `regularProdHomeomorph V W z` under `productHomeomorph` is the pair of points
underlying `z`. -/
@[simp]
lemma productHomeomorph_regularProdHomeomorph (z : regularOpens ℂ V × regularOpens ℂ W) :
    productHomeomorph ℂ V W (regularProdHomeomorph V W z).1.1 = (z.1.1, z.2.1) :=
  (productHomeomorph ℂ V W).apply_symm_apply _

end Regular

end UnderlyingSpace

end MMP
