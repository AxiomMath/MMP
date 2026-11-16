module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Proper metrics on locally compact, second-countable Hausdorff spaces

A locally compact, σ-compact Hausdorff space carries a continuous exhaustion function
`h : Y → ℝ`, every sublevel set of which lies in a compact set: `h = ∑ₖ fₖ` with `fₖ` an
Urysohn function, `0` on `Kₖ` and `1` off the interior of `Kₖ₊₁`, for a compact exhaustion
`(Kₖ)`. If `Y` is moreover second countable, the metric `max (d y y') |h y - h y'|`, for any
compatible metric `d`, is proper.

## Main results

* `MMP.exists_continuous_subset_isCompact_le`: the exhaustion function.
* `MMP.exists_metricSpace_properSpace`: a compatible proper metric.
-/

@[expose] public section

open Set Topology Filter Metric

namespace MMP

/-- **An exhaustion function.** A locally compact, σ-compact Hausdorff space has a continuous
real function every sublevel set of which lies in a compact set. -/
theorem exists_continuous_subset_isCompact_le (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [SigmaCompactSpace Y] :
    ∃ h : Y → ℝ, Continuous h ∧ ∀ R : ℝ, ∃ K : Set Y, IsCompact K ∧ {y | h y ≤ R} ⊆ K := by
  set K := CompactExhaustion.choice Y
  have hU : ∀ k, ∃ f : C(Y, ℝ), EqOn f 0 (K k) ∧ EqOn f 1 (interior (K (k + 1)))ᶜ ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun k ↦
    exists_continuous_zero_one_of_isCompact (K.isCompact k) isOpen_interior.isClosed_compl
      (disjoint_compl_right.mono_left (K.subset_interior_succ k))
  choose f hf0 hf1 hfI using hU
  have hzero : ∀ k j, j ≤ k → ∀ y ∈ K j, f k y = 0 := fun k j hjk y hy ↦ hf0 k (K.subset hjk hy)
  have hsupp : ∀ y, (Function.support fun k ↦ f k y) ⊆ ↑(Finset.range (K.find y)) := by
    intro y k hk
    rw [Finset.coe_range, mem_Iio]
    by_contra h
    exact hk (hzero k (K.find y) (not_lt.1 h) y (K.mem_find y))
  refine ⟨fun y ↦ ∑ᶠ k, f k y, continuous_finsum (fun k ↦ (f k).continuous) ?_, fun R ↦ ?_⟩
  · intro y
    refine ⟨interior (K (K.find y + 1)),
      isOpen_interior.mem_nhds (K.subset_interior_succ _ (K.mem_find y)), ?_⟩
    refine (finite_Iio (K.find y + 1)).subset fun k ⟨z, hzk, hz⟩ ↦ ?_
    rw [mem_Iio]
    by_contra h
    exact hzk (hzero k _ (not_lt.1 h) z (interior_subset hz))
  · set j := ⌈R⌉₊
    refine ⟨K (j + 1), K.isCompact _, fun y hy ↦ interior_subset ?_⟩
    by_contra hy'
    have hR : R < j + 1 := (Nat.le_ceil R).trans_lt (by linarith)
    have hfy : ∀ k ≤ j, f k y = 1 := fun k hk ↦
      hf1 k fun h ↦ hy' (interior_mono (K.subset (by omega)) h)
    have hfind : j < K.find y := by
      by_contra h
      exact hy' (K.subset_interior_succ j (K.subset (not_lt.1 h) (K.mem_find y)))
    have hsum : (∑ᶠ k, f k y) = ∑ k ∈ Finset.range (K.find y), f k y :=
      finsum_eq_sum_of_support_subset _ (hsupp y)
    have hge : ((j : ℝ) + 1) ≤ ∑ k ∈ Finset.range (K.find y), f k y := by
      calc ((j : ℝ) + 1) = ∑ k ∈ Finset.range (j + 1), f k y := by
            rw [Finset.sum_congr rfl fun k hk ↦ hfy k (by
              have := Finset.mem_range.1 hk; omega)]
            simp
        _ ≤ ∑ k ∈ Finset.range (K.find y), f k y :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
              fun k _ _ ↦ (hfI k y).1
    have : (∑ᶠ k, f k y) ≤ R := hy
    linarith

/-- The metric `max (d y y') |h y - h y'|` of an exhaustion function `h` is proper. -/
theorem properSpace_induced_graph {Y : Type*} [MetricSpace Y] {h : Y → ℝ} (hc : Continuous h)
    (hK : ∀ R : ℝ, ∃ K : Set Y, IsCompact K ∧ {y | h y ≤ R} ⊆ K)
    (H : (inferInstance : TopologicalSpace Y) = (MetricSpace.induced (fun y ↦ (y, h y))
      (isEmbedding_graph hc).injective inferInstance).toUniformSpace.toTopologicalSpace) :
    @ProperSpace Y ((MetricSpace.induced (fun y ↦ (y, h y)) (isEmbedding_graph hc).injective
      inferInstance).replaceTopology H).toPseudoMetricSpace := by
  have hd : ∀ a b : Y, @dist Y ((MetricSpace.induced (fun y ↦ (y, h y))
      (isEmbedding_graph hc).injective inferInstance).replaceTopology H).toDist a b =
        dist ((a, h a) : Y × ℝ) (b, h b) := fun _ _ ↦ rfl
  refine @ProperSpace.mk Y ((MetricSpace.induced (fun y ↦ (y, h y))
      (isEmbedding_graph hc).injective inferInstance).replaceTopology H).toPseudoMetricSpace
    fun x r ↦ ?_
  obtain ⟨K, hKc, hKs⟩ := hK (h x + r)
  refine hKc.of_isClosed_subset (@isClosed_closedBall Y ((MetricSpace.induced (fun y ↦ (y, h y))
      (isEmbedding_graph hc).injective inferInstance).replaceTopology H).toPseudoMetricSpace x r)
    fun y hy ↦ hKs ?_
  have hy' := (hd y x).symm.trans_le hy
  rw [Prod.dist_eq] at hy'
  have h1 := (le_max_right _ _).trans hy'
  rw [Real.dist_eq] at h1
  change h y ≤ h x + r
  linarith [le_abs_self (h y - h x)]

/-- **A compatible proper metric.** A locally compact, second-countable Hausdorff space has a
metric inducing its topology for which closed balls are compact. -/
theorem exists_metricSpace_properSpace (Y : Type*) [t : TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] :
    ∃ m : MetricSpace Y, ∃ hm : t = m.toUniformSpace.toTopologicalSpace,
      @ProperSpace Y (m.replaceTopology hm).toPseudoMetricSpace := by
  obtain ⟨h, hc, hK⟩ := exists_continuous_subset_isCompact_le Y
  let d₀ : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact ⟨MetricSpace.induced (fun y ↦ (y, h y)) (isEmbedding_graph hc).injective inferInstance,
    (isEmbedding_graph hc).eq_induced, properSpace_induced_graph hc hK _⟩

end MMP
