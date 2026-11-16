module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts

/-!
# The image of an open immersion on complex points

Let `g : W → V` be an open immersion of schemes over `ℂ`. It induces an open embedding
`W(ℂ) → V(ℂ)` (`MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion`), hence an open
subset `g(W(ℂ))` of `V(ℂ)` and a homeomorphism of `W(ℂ)` onto it.

## Main definitions

* `MMP.UnderlyingSpace.opensRangeMap`: the open subset `g(W(ℂ))` of `V(ℂ)`.
* `MMP.UnderlyingSpace.homeomorphOpensRangeMap`: `W(ℂ) ≃ₜ g(W(ℂ))`.

## Main results

* `MMP.UnderlyingSpace.mem_opensRangeMap_ι_iff`: for an open subscheme `U ⊆ X`, a point
  `p ∈ X(ℂ)` lies in `U(ℂ)` iff its closed point lies in `U`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace MMP

namespace UnderlyingSpace

section OpenImmersion

variable {W V : Scheme.{0}} [W.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))]
  (g : W ⟶ V) [IsOpenImmersion g] [g.IsOver (Spec (.of ℂ))]

/-- The open subset `g(W(ℂ))` of `V(ℂ)`, for an open immersion `g : W → V` over `ℂ`. -/
def opensRangeMap : Opens (UnderlyingSpace ℂ V) :=
  ⟨Set.range (map (K := ℂ) g), (isOpenEmbedding_map_of_isOpenImmersion g).isOpen_range⟩

/-- A point of `V(ℂ)` lies in `g(W(ℂ))` iff it is in the range of `g` on complex points. -/
@[simp]
lemma mem_opensRangeMap {p : UnderlyingSpace ℂ V} :
    p ∈ opensRangeMap g ↔ p ∈ Set.range (mapFun (K := ℂ) g) :=
  Iff.rfl

/-- An open immersion `g : W → V` over `ℂ` identifies `W(ℂ)` with the open subset `g(W(ℂ))` of
`V(ℂ)`. -/
def homeomorphOpensRangeMap : UnderlyingSpace ℂ W ≃ₜ opensRangeMap g :=
  (isOpenEmbedding_map_of_isOpenImmersion g).isEmbedding.toHomeomorph

/-- The homeomorphism `W(ℂ) ≃ₜ g(W(ℂ))`, followed by the inclusion into `V(ℂ)`, is the map
induced by `g`. -/
@[simp]
lemma coe_homeomorphOpensRangeMap_apply (z : UnderlyingSpace ℂ W) :
    (homeomorphOpensRangeMap g z : UnderlyingSpace ℂ V) = mapFun g z :=
  rfl

/-- The map induced by `g` sends the inverse image of `y ∈ g(W(ℂ))` under the homeomorphism
`W(ℂ) ≃ₜ g(W(ℂ))` back to `y`. -/
@[simp]
lemma mapFun_homeomorphOpensRangeMap_symm_apply (y : opensRangeMap g) :
    mapFun g ((homeomorphOpensRangeMap g).symm y) = y.1 :=
  congrArg Subtype.val ((homeomorphOpensRangeMap g).apply_symm_apply y)

end OpenImmersion

/-- A point `p ∈ X(ℂ)` lies in the image of `U(ℂ)` for an open subscheme `U` iff its closed point
lies in `U`. -/
lemma mem_opensRangeMap_ι_iff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (U : X.Opens)
    [U.toScheme.Over (Spec (.of ℂ))] [U.ι.IsOver (Spec (.of ℂ))] (p : UnderlyingSpace ℂ X) :
    p ∈ opensRangeMap U.ι ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ U := by
  rw [mem_opensRangeMap, range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq,
    Scheme.Opens.opensRange_ι, top_le_preimage_iff]

end UnderlyingSpace

end MMP
