module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomeomorphGeneric
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction

/-!
# The exterior product of classes of two complex schemes, on their product

For schemes `V`, `W` over `ℂ` and classes `cV ∈ H_{2k} V`, `cW ∈ H_{2l} W`, the class
`cV × cW ∈ H_{2(k+l)}(V × W)`: the Borel–Moore exterior product on `V(ℂ) × W(ℂ)`, read on
`(V × W)(ℂ)` through the homeomorphism `(V × W)(ℂ) ≃ₜ V(ℂ) × W(ℂ)` (Fulton, Example 19.1.9).

## Main definitions

* `MMP.productClass`: `cV × cW ∈ H_{2(k+l)}(V × W)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.9.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open MMP.UnderlyingSpace MMP.BorelMooreCross

namespace MMP

section ProductClass

variable {R : Type} [CommRing R] (V W : Scheme.{0}) [V.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]

/-- For natural numbers `k` and `l`, `2k + 2l = 2(k + l)` as integers. -/
lemma two_mul_add_two_mul_eq (k l : ℕ) :
    ((2 * k : ℕ) : ℤ) + ((2 * l : ℕ) : ℤ) = ((2 * (k + l) : ℕ) : ℤ) := by
  push_cast; ring

variable (R) in
/-- The class `cl(V) × cl(W) ∈ H_{2(k+l)}(V × W)`: the exterior product of classes of `V(ℂ)` and
`W(ℂ)`, read on `(V × W)(ℂ)` through `(V × W)(ℂ) ≃ₜ V(ℂ) × W(ℂ)`. -/
def productClass {k l : ℕ}
    (cV : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ))
    (cW : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ W)) (2 * l : ℕ)) :
    borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))))
      (2 * (k + l) : ℕ) :=
  (borelMooreHomology.pushforward R (ModuleCat.of R R)
    (TopCat.ofHom ((productHomeomorph ℂ V W).symm :
      C(UnderlyingSpace ℂ V × UnderlyingSpace ℂ W,
        UnderlyingSpace ℂ (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ))))))
    (productHomeomorph ℂ V W).symm.isProperMap (2 * (k + l) : ℕ)).hom
    (congrDegree R _ (two_mul_add_two_mul_eq k l)
      (borelMooreHomology.exteriorProduct R (TopCat.of (UnderlyingSpace ℂ V))
        (TopCat.of (UnderlyingSpace ℂ W)) (2 * k : ℕ) (2 * l : ℕ) (cV ⊗ₜ cW)))

end ProductClass

end MMP
