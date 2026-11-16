module

public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Orientation
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Fundamental
public import MMP.AlgebraicTopology.OrientationClass.CapProduct

/-!
# `cl(V × W) = cl(V) × cl(W)` (Fulton, Example 19.1.9)

For complex varieties `V`, `W` of dimensions `k`, `l` with `V × W` a complex variety, the
exterior product of the fundamental classes, read on `(V × W)(ℂ)`, is the fundamental class of
`V × W`.

## Main results

* `MMP.IsVarietyFundamentalClass.productClass`: `cl(V) × cl(W) = cl(V × W)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP.Intersection.Scheme (dimension)

variable {R : Type} [CommRing R] {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [W.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsComplexScheme W] [IsIntegral V] [IsIntegral W]
  [IsIntegral (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))]
  [IsComplexScheme (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))]

omit [IsIntegral (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))] in
/-- `V_reg(ℂ) × W_reg(ℂ)`, an open subset of `(V × W)_reg(ℂ)`, is connected. -/
lemma connectedSpace_regularOpensInter_regularProdOpens :
    ConnectedSpace (regularOpensInter (regularProdOpens V W)) := by
  haveI := connectedSpace_regularOpens (V := V)
  haveI := connectedSpace_regularOpens (V := W)
  exact (regularProdHomeomorph V W).surjective.connectedSpace
    (regularProdHomeomorph V W).continuous

/-- **The fundamental class of a product of varieties** (Fulton, Example 19.1.9): for complex
varieties `V`, `W` of dimensions `k`, `l`, `cl(V) × cl(W)`, read on `(V × W)(ℂ)`, is the
fundamental class of `V × W`. -/
theorem IsVarietyFundamentalClass.productClass {k l : ℕ} {hk : (k : WithBot ℕ∞) = dimension V}
    {hl : (l : WithBot ℕ∞) = dimension W}
    (hkl : ((k + l : ℕ) : WithBot ℕ∞) = dimension (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))
    {cV : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    {cW : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ W)) (2 * l : ℕ)}
    (hcV : IsVarietyFundamentalClass R hk cV) (hcW : IsVarietyFundamentalClass R hl cW) :
    IsVarietyFundamentalClass R hkl (MMP.productClass R V W cV cW) := by
  haveI := connectedSpace_regularOpensInter_regularProdOpens (V := V) (W := W)
  refine IsVarietyFundamentalClass.of_isFundamentalClass_restrict hkl (regularProdOpens V W) ?_
  rw [restrict_restrict_productClass]
  letI := regularChartedSpace (𝕜 := ℂ) hk
  letI := regularChartedSpace (𝕜 := ℂ) hl
  letI := regularChartedSpace (𝕜 := ℂ) hkl
  have h2 : 2 * k + 2 * l = 2 * (k + l) := by ring
  have hB := (IsFundamentalClass.exteriorProduct R hcV hcW).reindex_finCongr h2
  have hb : (((euclideanComplexOrientationBasis k).prod
      (euclideanComplexOrientationBasis l)).reindex finSumFinEquiv).reindex (finCongr h2) =
      ((euclideanComplexOrientationBasis k).prod (euclideanComplexOrientationBasis l)).reindex
        (finSumFinEquiv.trans (finCongr h2)) :=
    Module.Basis.eq_of_apply_eq fun _ ↦ rfl
  rw [hb] at hB
  have hC := hB.pushforward_homeomorph R (regularProdHomeomorph V W)
    (isOrientationPreserving_regularProdHomeomorph V W hk hl hkl)
  rwa [congrDegree_congrDegree_apply] at hC

end MMP
