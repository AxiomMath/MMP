module

public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.Homotopy
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass

/-!
# Caps with point classes pulled back to a fibre, read in the total space

Let `g : P → T` be a continuous map to a connected Hausdorff space `T` with an oriented atlas
(for us `T(ℂ)`, `T` a connected non-singular complex curve), `μ ∈ H_m P`, and for `y ∈ T` let
`u_y ∈ H^n(T, T - y)` be the local orientation class at `y`. The cap product
`g^*(u_y) ∩ μ ∈ H_{m-n}(g⁻¹(y))`, pushed forward to `P`, does not depend on `y`
(Fulton, proof of Prop. 19.1.1): forgetting the support
(`pushforward_subsetInclusion_capProductSupport`) it is `g^*(ū_y) ∩ μ`, `ū_y` the image of `u_y`
in `H^n T`, and `ū_y` does not depend on `y` (for local orientation classes:
`cohomologyWithSupports.toCohomology_eq_of_isLocalOrientationClass`).

## Main results

* `pushforward_subsetInclusion_capProductSupportPullback_eq_of_isLocalOrientationClass`:
  `ι_{y*}(g^*(u_y) ∩ μ)` does not depend on `y`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Proposition 19.1.1.
-/

@[expose] public noncomputable section

universe u

namespace MMP

variable {R : Type u} [CommRing R]

namespace borelMooreHomology

/-- **`ι_{y*}(g^*(u_y) ∩ μ)` does not depend on `y`** (Fulton, proof of Prop. 19.1.1). For a
continuous `g : P → T` to a connected Hausdorff space with an oriented atlas, `μ ∈ H_m P`, and
local orientation classes `u_i ∈ H^n(T, T - y_i)`, the push-forwards to `P` of
`g^*(u_i) ∩ μ ∈ H_{m-n}(g⁻¹ y_i)` agree for `i = 1, 2`. -/
theorem pushforward_subsetInclusion_capProductSupportPullback_eq_of_isLocalOrientationClass
    {P T : TopCat.{u}} [T2Space T] [ConnectedSpace T] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H T]
    (hT : IsOrientedAtlas H T) {n : ℕ} (hn : 0 < n) (b : Module.Basis (Fin n) ℝ H)
    (g : P ⟶ T) (hd : ∀ y : T, HasProperNeighbourhoodDeformations (g ⁻¹' {y})) (m : ℕ)
    (μ : borelMooreHomology R (ModuleCat.of R R) P m) {y₁ y₂ : T}
    {u₁ : cohomologyWithSupports R (ModuleCat.of R R) T {y₁} n}
    {u₂ : cohomologyWithSupports R (ModuleCat.of R R) T {y₂} n}
    (hu₁ : IsLocalOrientationClass R b y₁ u₁) (hu₂ : IsLocalOrientationClass R b y₂ u₂) :
    (pushforward R (ModuleCat.of R R) (subsetInclusion (g ⁻¹' {y₁}))
        (isProperMap_subsetInclusion (isClosed_singleton.preimage g.hom.continuous)) (m - n)).hom
        (capProductSupportPullback R g isClosed_singleton (hd y₁) n m u₁ μ) =
      (pushforward R (ModuleCat.of R R) (subsetInclusion (g ⁻¹' {y₂}))
        (isProperMap_subsetInclusion (isClosed_singleton.preimage g.hom.continuous)) (m - n)).hom
        (capProductSupportPullback R g isClosed_singleton (hd y₂) n m u₂ μ) := by
  rw [capProductSupportPullback_apply, capProductSupportPullback_apply,
    pushforward_subsetInclusion_capProductSupport, pushforward_subsetInclusion_capProductSupport,
    ← capProduct_toCohomology P (g ⁻¹' {y₁}), ← capProduct_toCohomology P (g ⁻¹' {y₂})]
  rw [cohomologyWithSupports.toCohomology_pullback_eq_of_toCohomology_eq g
    (cohomologyWithSupports.toCohomology_eq_of_isLocalOrientationClass hT hn hu₁ hu₂)]

end borelMooreHomology

end MMP
