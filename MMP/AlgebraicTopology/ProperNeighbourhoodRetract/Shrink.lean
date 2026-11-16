module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Shrinking a neighbourhood retraction to a proper one

Let `X` be a closed subset of a proper metric space `E` and `r : U → X` a retraction of an open
neighbourhood `U` of `X`. Then `r` is proper on the closed neighbourhood
`N = {y ∈ U | d(y, r y) ≤ θ(r y)}` of `X`, where `θ = min(1, d(·, E - U)) / 10`: a point of the
closure of `N` is within `10/9` of its distance to `E - U` of `X`, hence lies in `U`; and the
preimage in `N` of a compact `K ⊆ X` is closed and lies within `1` of `K`.

## Main results

* `MMP.exists_isClosed_subset_isCompact_inter_preimage`: the closed neighbourhood.
-/

@[expose] public section

open Set Topology Metric Filter

namespace MMP

variable {E : Type*} [MetricSpace E]

/-- A continuous function, positive on an open set `U`, bounded by `1`, and with `10 θ(x)` at most
the distance from `x` to the complement of `U`. -/
theorem exists_continuous_pos_le_infDist {U : Set E} (hU : IsOpen U) :
    ∃ θ : E → ℝ, Continuous θ ∧ (∀ x ∈ U, 0 < θ x) ∧ (∀ x, θ x ≤ 1) ∧
      ∀ x, ∀ y ∉ U, 10 * θ x ≤ dist x y := by
  by_cases hne : (Uᶜ).Nonempty
  · refine ⟨fun x ↦ min 1 (infDist x Uᶜ) / 10, ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun x y hy ↦ ?_⟩
    · exact (continuous_const.min (continuous_infDist_pt _)).div_const _
    · have : 0 < infDist x Uᶜ :=
        (infDist_pos_iff_notMem_closure hne).1
          (by rwa [hU.isClosed_compl.closure_eq, notMem_compl_iff])
      positivity
    · linarith [min_le_left 1 (infDist x Uᶜ)]
    · linarith [min_le_right 1 (infDist x Uᶜ),
        infDist_le_dist_of_mem (x := x) (show y ∈ Uᶜ from hy)]
  · rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    exact ⟨fun _ ↦ 1 / 10, continuous_const, fun _ _ ↦ by norm_num, fun _ ↦ by norm_num,
      fun x y hy ↦ absurd (hne ▸ mem_univ y) hy⟩

/-- **A neighbourhood retraction is proper on a closed neighbourhood.** Let `X` be closed in a
proper metric space `E`, `U ⊇ X` open and `r` continuous on `U`, mapping `U` into `X`. Then there
is a closed `N ⊆ U` with `X ⊆ interior N` such that the preimage in `N` of every compact `K ⊆ X` is
compact; moreover every point of `N` is within `1` of its image. -/
theorem exists_isClosed_subset_isCompact_inter_preimage [ProperSpace E] {X U : Set E}
    (hX : IsClosed X) (hU : IsOpen U) (hXU : X ⊆ U) {r : E → E} (hr : ContinuousOn r U)
    (hrX : MapsTo r U X) (hrid : ∀ x ∈ X, r x = x) :
    ∃ N : Set E, IsClosed N ∧ N ⊆ U ∧ X ⊆ interior N ∧
      (∀ K : Set E, IsCompact K → K ⊆ X → IsCompact (N ∩ r ⁻¹' K)) ∧
      ∀ y ∈ N, dist y (r y) ≤ 1 := by
  obtain ⟨θ, hθc, hθpos, hθ1, hθd⟩ := exists_continuous_pos_le_infDist hU
  set f : E → ℝ := fun y ↦ dist y (r y) - θ (r y)
  have hfc : ContinuousOn f U :=
    (continuous_dist.comp_continuousOn (continuousOn_id.prodMk hr)).sub (hθc.comp_continuousOn hr)
  set N : Set E := {y ∈ U | f y ≤ 0}
  -- points of `N` are close to their image
  have hNd : ∀ z ∈ N, dist z (r z) ≤ θ (r z) := fun z hz ↦ by
    linarith [show dist z (r z) - θ (r z) ≤ 0 from hz.2]
  -- the closure of `N` lies in `U`
  have hcl : closure N ⊆ U := by
    intro y hy
    by_contra hyU
    have hyX : y ∈ X := by
      rw [← hX.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨z, hzN, hz⟩ := Metric.mem_closure_iff.1 hy (9 / 10 * ε) (by positivity)
      refine ⟨r z, hrX hzN.1, ?_⟩
      rw [dist_comm]
      linarith [hNd z hzN, hθd (r z) y hyU, dist_triangle (r z) z y, dist_comm z (r z),
        dist_comm z y]
    exact hyU (hXU hyX)
  have hNclosed : IsClosed N := by
    refine closure_subset_iff_isClosed.1 fun y hy ↦ ⟨hcl hy, ?_⟩
    have hcont : ContinuousAt f y := hfc.continuousAt (hU.mem_nhds (hcl hy))
    exact ContinuousWithinAt.closure_le (g := fun _ ↦ (0 : ℝ)) hy hcont.continuousWithinAt
      continuousWithinAt_const fun z hz ↦ hz.2
  refine ⟨N, hNclosed, fun y hy ↦ hy.1, fun x hx ↦ ?_, fun K hK hKX ↦ ?_,
    fun y hy ↦ (hNd y hy).trans (hθ1 _)⟩
  · have hxU := hXU hx
    refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset
      ((hfc.isOpen_inter_preimage hU isOpen_Iio).mem_nhds ⟨hxU, ?_⟩)
        fun z hz ↦ ⟨hz.1, le_of_lt hz.2⟩)
    change dist x (r x) - θ (r x) < 0
    rw [hrid x hx, dist_self]
    linarith [hθpos x hxU]
  · refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine closure_subset_iff_isClosed.1 fun y hy ↦ ?_
      have hyN : y ∈ N := hNclosed.closure_subset (closure_mono inter_subset_left hy)
      have hcont : ContinuousWithinAt r (N ∩ r ⁻¹' K) y :=
        (hr.continuousAt (hU.mem_nhds hyN.1)).continuousWithinAt
      exact ⟨hyN, hK.isClosed.closure_subset
        (closure_mono (image_subset_iff.2 inter_subset_right) (hcont.mem_closure_image hy))⟩
    · refine (Bornology.IsBounded.cthickening (δ := 1) hK.isBounded).subset fun z hz ↦ ?_
      exact mem_cthickening_of_dist_le z (r z) 1 K hz.2 ((hNd z hz.1).trans (hθ1 _))

end MMP
