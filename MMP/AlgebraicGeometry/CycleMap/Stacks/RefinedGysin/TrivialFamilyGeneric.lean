module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomotopyInfraGeneric
public import MMP.AlgebraicGeometry.CycleMap.RefinedGysin.Family

/-!
# The trivial family `X × T` inside a closed immersion

For a closed immersion `e : X × T → M` of complex schemes, the homeomorphism
`X(ℂ) × T(ℂ) ≃ e((X × T)(ℂ))` and its compatibility with a retraction `ρ : M → T`.

## Main definitions

* `MMP.UnderlyingSpace.trivialFamilyHomeomorph`: `X(ℂ) × T(ℂ) ≃ e((X × T)(ℂ))`.

## Main results

* `MMP.UnderlyingSpace.map_trivialFamilyHomeomorph`: `ρ ∘ e = pr₂` on `ℂ`-points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

namespace MMP

namespace UnderlyingSpace

open borelMooreHomology

variable {X T M : Scheme.{0}} [X.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
  [M.Over (Spec (.of ℂ))]
  (e : pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)) ⟶ M) [IsClosedImmersion e]
  [e.IsOver (Spec (.of ℂ))]

/-- The homeomorphism `X(ℂ) × T(ℂ) ≃ e((X × T)(ℂ))` of a closed immersion `e : X × T → M`. -/
def trivialFamilyHomeomorph :
    UnderlyingSpace ℂ X × UnderlyingSpace ℂ T ≃ₜ range (UnderlyingSpace.map (K := ℂ) e) :=
  (homeomorphProd X T).symm.trans
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isEmbedding.toHomeomorph

/-- The point `trivialFamilyHomeomorph e p` of `M(ℂ)` is the image under `e` of the point of
`(X × T)(ℂ)` corresponding to `p`. -/
lemma coe_trivialFamilyHomeomorph (p : UnderlyingSpace ℂ X × UnderlyingSpace ℂ T) :
    (trivialFamilyHomeomorph e p : UnderlyingSpace ℂ M) =
      UnderlyingSpace.map e ((homeomorphProd X T).symm p) :=
  rfl

/-- `ρ ∘ e = pr₂` on `ℂ`-points. -/
lemma map_trivialFamilyHomeomorph (ρ : M ⟶ T) [ρ.IsOver (Spec (.of ℂ))]
    (h : e ≫ ρ = pullback.snd _ _) (p : UnderlyingSpace ℂ X × UnderlyingSpace ℂ T) :
    UnderlyingSpace.map ρ (trivialFamilyHomeomorph e p : UnderlyingSpace ℂ M) = p.2 := by
  rw [coe_trivialFamilyHomeomorph, ← ContinuousMap.comp_apply, ← map_comp]
  have hm : UnderlyingSpace.map (K := ℂ) (e ≫ ρ) =
      UnderlyingSpace.map (K := ℂ) (pullback.snd (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))) := by
    ext q : 1
    exact UnderlyingSpace.ext (by rw [toHom_map, toHom_map, h])
  rw [hm]
  exact congrArg Prod.snd ((homeomorphProd X T).apply_symm_apply p)

end UnderlyingSpace

end MMP
