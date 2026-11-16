module

public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.CycleClassRestrict
public import MMP.AlgebraicGeometry.CycleMap.LocalizedFirstChern.CycleChartProduct

/-!
# The cycle class of a Stacks cycle in the charts of Lemma 19.1.3 (Fulton, §19.1)

The local form of the cycle class used in the proof of Fulton's Lemma 19.1.3, for
`MMP.Chow.cycleClass` on Stacks' cycles. Let `ξ` be the generic point of a `k`-dimensional
component of a complex scheme `D ⊆ X`, and `W ⊆ D(ℂ)` an open set inside the regular part of the
component, missing the other components, read in an algebraic chart of `X` as the second
component `φ : W ≅ B` of local holomorphic coordinates `(ρ, π)` with `ρ = 0` on `W`. Then `φ`
carries `cl(α)|_W` to `α(ξ) · μ_B` for every cycle `α` of delta-dimension `k` on `D`.

## Main results

* `MMP.Chow.pushforward_restrict_pointCycleClass_eq_of_chart`: the case `α = [ξ]`.
* `MMP.Chow.pushforward_restrict_cycleClass_eq_smul_of_chart`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set MMP
  MMP.UnderlyingSpace MMP.FundamentalClass borelMooreHomology Stacks.Chow

open scoped MMP.SubschemeOver

namespace MMP.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (R : Type) [CommRing R] {D X : Scheme.{0}} [D.Over (Spec (.of ℂ))] [IsComplexScheme D]
  [X.Over (Spec (.of ℂ))] (ι : D ⟶ X) [IsClosedImmersion ι] [ι.IsOver (Spec (.of ℂ))]

/-- **The cycle class of a point in a chart** (Fulton, §19.1): `φ_* (cl(ξ)|_W) = μ_B`. -/
theorem pushforward_restrict_pointCycleClass_eq_of_chart {k n : ℕ} (ξ : D)
    (hξ : relativeDimension (fieldChowSituation ℂ).dimensionFunction (D ↘ Spec (.of ℂ)) ξ = k)
    (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆
      mapFun (K := ℂ) (integralComponentAt ξ).subschemeι ''
        regularPart ℂ (integralComponentAt ξ).subscheme)
    {eX : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))}
    (heX : IsAlgebraicChart eX) (hWX : ∀ p : W, mapFun ι p.1 ∈ eX.source)
    {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB) (φ : W ≃ₜ B)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (ρ : EuclideanSpace ℂ (Fin n) → G)
    (hρ : ∀ p : W, ρ (eX (mapFun ι p.1)) = 0)
    (hρd : ∀ p : W, DifferentiableAt ℂ ρ (eX (mapFun ι p.1)))
    (hπ : ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ p : W, φ p ∈ e'.source →
      ∃ π : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin k),
        (∀ᶠ p' in 𝓝 p, e' (φ p') = π (eX (mapFun ι p'.1))) ∧
        DifferentiableAt ℂ π (eX (mapFun ι p.1)) ∧
        Function.Injective (fderiv ℂ (fun z ↦ (ρ z, π z)) (eX (mapFun ι p.1)))) :
    pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap (2 * k : ℕ)
      (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ D)) W (2 * k : ℕ)
        (pointCycleClass R ξ hξ)) = μB :=
  (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt ξ hξ)).choose_spec.1
    |>.pushforward_restrict_pushforward_eq_of_chart
      R (integralComponentAt ξ).subschemeι ι W hW heX hWX hμB φ ρ hρ hρd hπ

/-- **The cycle class of a cycle near the generic point of a component, in a chart** (Fulton,
proof of Lemma 19.1.3): `φ_* (cl(α)|_W) = α(ξ) · μ_B`. -/
theorem pushforward_restrict_cycleClass_eq_smul_of_chart {k n : ℕ} (j : irreducibleComponents D)
    (hj : relativeDimension (fieldChowSituation ℂ).dimensionFunction (D ↘ Spec (.of ℂ))
      (componentGenericPoint j) = k)
    (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆
      mapFun (K := ℂ) (integralComponentAt (componentGenericPoint j)).subschemeι ''
        regularPart ℂ (integralComponentAt (componentGenericPoint j)).subscheme)
    (hdisj : ∀ i, i ≠ j → Disjoint (W : Set (UnderlyingSpace ℂ D))
      (range (mapFun (K := ℂ) (irreducibleComponentι D i))))
    {eX : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))}
    (heX : IsAlgebraicChart eX) (hWX : ∀ p : W, mapFun ι p.1 ∈ eX.source)
    {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB) (φ : W ≃ₜ B)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (ρ : EuclideanSpace ℂ (Fin n) → G)
    (hρ : ∀ p : W, ρ (eX (mapFun ι p.1)) = 0)
    (hρd : ∀ p : W, DifferentiableAt ℂ ρ (eX (mapFun ι p.1)))
    (hπ : ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ p : W, φ p ∈ e'.source →
      ∃ π : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin k),
        (∀ᶠ p' in 𝓝 p, e' (φ p') = π (eX (mapFun ι p'.1))) ∧
        DifferentiableAt ℂ π (eX (mapFun ι p.1)) ∧
        Function.Injective (fderiv ℂ (fun z ↦ (ρ z, π z)) (eX (mapFun ι p.1))))
    (α : CycleGroup (fieldChowSituation ℂ) (D ↘ Spec (.of ℂ)) k) :
    pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap (2 * k : ℕ)
      (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ D)) W (2 * k : ℕ)
        (cycleClass R k α)) = α.1 (componentGenericPoint j) • μB := by
  rw [restrict_cycleClass_eq_smul_of_irreducibleComponent R j hj W hdisj α, map_zsmul,
    pushforward_restrict_pointCycleClass_eq_of_chart R ι _ hj W hW heX hWX hμB φ ρ hρ hρd hπ]

end MMP.Chow
