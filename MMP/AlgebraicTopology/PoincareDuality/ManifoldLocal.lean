module

public import MMP.AlgebraicTopology.PoincareDuality.CompactApprox
public import MMP.AlgebraicTopology.PoincareDuality.Localize
public import MMP.AlgebraicTopology.BorelMoore.FiniteChains
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Local homology of manifolds above the dimension, and Borel–Moore vanishing

Let `Y` be a Hausdorff space modelled on a Hausdorff real topological vector space `H` with a
basis of `n` vectors (so `H ≅ ℝⁿ`). If the local homology of `ℝⁿ` at closed boxes vanishes in
degrees `> m` (`H_{k+1}(ℝⁿ, ℝⁿ - Q) = 0` for `k ≥ m`), then so does the local homology
`H_{k+1}(Y, Y - K)` at every compact `K ⊆ Y` (Hatcher, Lemma 3.27): for `K` inside a chart, by
the case of compact sets of `ℝⁿ`, transport along `H ≅ ℝⁿ`, excision to the chart's image and
transport along the chart; for general `K`, by gluing over charts.

For `Y` moreover locally compact and σ-compact, the Borel–Moore homology `H_{k+1} Y` then
vanishes for `k ≥ m`.

## Main results

* `MMP.SingularChain.relVanishing_of_isCompact_of_chartedSpace`.
* `MMP.borelMooreHomology.isZero_of_chartedSpace_of_relVanishing_Icc`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Set Topology CategoryTheory Limits

universe u

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]

/-- A Hausdorff real topological vector space with a basis of `n` vectors is homeomorphic to
`ℝⁿ`, through the coordinates. -/
def basisHomeomorph {n : ℕ} (b : Module.Basis (Fin n) ℝ H) : H ≃ₜ (Fin n → ℝ) :=
  haveI : IsTopologicalAddGroup H :=
    { continuous_neg := by
        have : (fun x : H ↦ -x) = fun x ↦ (-1 : ℝ) • x := funext fun x ↦ by simp
        rw [this]
        exact continuous_const_smul _ }
  haveI : FiniteDimensional ℝ H := Module.Finite.of_basis b
  b.equivFun.toContinuousLinearEquiv.toHomeomorph

/-- **Hatcher, Lemma 3.27 (vanishing above the dimension), from the boxes of `ℝⁿ`.** -/
theorem relVanishing_of_isCompact_of_chartedSpace {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [ChartedSpace H Y] {n : ℕ} (b : Module.Basis (Fin n) ℝ H) {m : ℕ}
    (hbox : ∀ a c : Fin n → ℝ, ∀ k, m ≤ k → RelVanishing R (Fin n → ℝ) k (Icc a c))
    {K : Set Y} (hK : IsCompact K) : ∀ k, m ≤ k → RelVanishing R Y k K := by
  refine relVanishing_of_isCompact_of_local (𝒰 := {U | ∃ e ∈ atlas H Y, U = e.source})
    ?_ ?_ ?_ hK
  · rintro U ⟨e, -, rfl⟩
    exact e.open_source
  · intro x
    exact ⟨_, ⟨chartAt H x, chart_mem_atlas H x, rfl⟩, mem_chart_source H x⟩
  · rintro U ⟨e, -, rfl⟩ K hK hKs k hk
    have hK' : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
    set φ := basisHomeomorph b
    have hH : RelVanishing R H k (e '' K) := by
      have h := RelVanishing.of_homeomorph φ.symm
        (relVanishing_of_isCompact_euclidean (fun a c k' hk' ↦ hbox a c k' (hk.trans hk'))
          (hK'.image φ.continuous) (m := k))
      rwa [← Set.image_comp, show (φ.symm ∘ φ) = id from funext φ.symm_apply_apply,
        Set.image_id] at h
    refine RelVanishing.of_openPartialHomeomorph e hK.isClosed hKs ?_
    exact RelVanishing.subtype e.open_target hK'.isClosed
      (fun _ ⟨y, hy, hxy⟩ ↦ hxy ▸ e.map_source (hKs hy)) hH

end SingularChain

namespace borelMooreHomology

variable {R : Type u} [CommRing R] {H : Type*} [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [T2Space H]

/-- **Vanishing of Borel–Moore homology above the dimension, from the boxes of `ℝⁿ`**: for a
Hausdorff, locally compact, σ-compact space `Y` modelled on `H ≅ ℝⁿ`, if
`H_{k+1}(ℝⁿ, ℝⁿ - Q; R) = 0` for every closed box `Q` and every `k ≥ m`, then
`H_{k+1} Y = 0` for every `k ≥ m`. -/
theorem isZero_of_chartedSpace_of_relVanishing_Icc {Y : TopCat.{u}} [T2Space Y]
    [LocallyCompactSpace Y] [SigmaCompactSpace Y] [ChartedSpace H Y] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) {m : ℕ}
    (hbox : ∀ a c : Fin n → ℝ, ∀ k, m ≤ k → SingularChain.RelVanishing R (Fin n → ℝ) k (Icc a c))
    (k : ℕ) (hk : m ≤ k) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) Y ((k + 1 : ℕ) : ℤ)) :=
  isZero_of_relVanishing k
    (fun K hK ↦ SingularChain.relVanishing_of_isCompact_of_chartedSpace b hbox hK k hk)
    (fun K hK ↦ SingularChain.relVanishing_of_isCompact_of_chartedSpace b hbox hK (k + 1)
      (hk.trans k.le_succ))

end borelMooreHomology

end MMP
