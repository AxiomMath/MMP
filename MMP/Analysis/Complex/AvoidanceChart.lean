module

public import MMP.Attr
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Analytic avoidance charts

An *analytic avoidance chart* is an open Euclidean ball `B ⊆ ℂⁿ` together with finitely many
holomorphic functions `f₁, …, f_r` on `B`, at least one of which is not identically zero on `B`.
Its *excluded subset* is the common zero locus `A = {x ∈ B : f₁(x) = ⋯ = f_r(x) = 0}`.

## Main definitions

* `MMP.Fourfold.AnalyticAvoidanceChart n`: an analytic avoidance chart in `ℂⁿ`.
* `MMP.Fourfold.AnalyticAvoidanceChart.ball`: its ball `B`.
* `MMP.Fourfold.AnalyticAvoidanceChart.excludedSet`: its excluded subset `A`.

## Main results

* `MMP.Fourfold.AnalyticAvoidanceChart.excludedSet_subset_ball`: `A ⊆ B`.
* `MMP.Fourfold.AnalyticAvoidanceChart.isOpen_ball_diff_excludedSet`: `B \ A` is open.
* `MMP.Fourfold.AnalyticAvoidanceChart.radius_pos`: the radius of the ball is positive.

## Implementation notes

`ℂⁿ` is `EuclideanSpace ℂ (Fin n)`, whose norm is the Euclidean norm, so `Metric.ball` is a
Euclidean ball. Holomorphy on `B` is `AnalyticOnNhd ℂ (f i) B`: in several complex variables a
function on an open set is holomorphic exactly when it is complex analytic there. (Mathlib proves
the equivalence with complex differentiability only in one variable, so analyticity is the form
that is directly usable.) The functions are total functions on `ℂⁿ`, of which only the values on
`B` matter; "not identically zero on `B`" is the existence of a point of `B` where one of them does
not vanish.
-/

@[expose] public noncomputable section

namespace MMP.Fourfold

open Metric

/-- An analytic avoidance chart in `ℂⁿ`: an open Euclidean ball `ball center radius` with finitely
many functions `f 0, …, f (r - 1)`, each holomorphic (complex analytic) on the ball, at least one
of which is not identically zero on the ball. -/
@[mmp "def_mmp_analytic_avoidance_chart"]
structure AnalyticAvoidanceChart (n : ℕ) where
  /-- The centre of the ball. -/
  center : EuclideanSpace ℂ (Fin n)
  /-- The radius of the ball. -/
  radius : ℝ
  /-- The number of functions. -/
  r : ℕ
  /-- The functions `f 0, …, f (r - 1)`. -/
  f : Fin r → EuclideanSpace ℂ (Fin n) → ℂ
  /-- Each function is holomorphic on the ball. -/
  analyticOnNhd : ∀ i, AnalyticOnNhd ℂ (f i) (ball center radius)
  /-- Some function is not identically zero on the ball. -/
  exists_ne_zero : ∃ i, ∃ x ∈ ball center radius, f i x ≠ 0

namespace AnalyticAvoidanceChart

variable {n : ℕ} (C : AnalyticAvoidanceChart n)

/-- The open Euclidean ball of an analytic avoidance chart. -/
def ball : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball C.center C.radius

/-- A point lies in the ball of a chart exactly when its distance to the centre is less than the
radius. -/
@[simp] theorem mem_ball {x : EuclideanSpace ℂ (Fin n)} :
    x ∈ C.ball ↔ dist x C.center < C.radius := Iff.rfl

/-- The excluded subset of an analytic avoidance chart: the points of its ball at which all of
its functions vanish. -/
@[mmp "def_mmp_analytic_avoidance_chart"]
def excludedSet : Set (EuclideanSpace ℂ (Fin n)) := {x | x ∈ C.ball ∧ ∀ i, C.f i x = 0}

/-- A point lies in the excluded subset exactly when it lies in the ball and all the functions
vanish at it. -/
theorem mem_excludedSet {x : EuclideanSpace ℂ (Fin n)} :
    x ∈ C.excludedSet ↔ x ∈ C.ball ∧ ∀ i, C.f i x = 0 := Iff.rfl

/-- The ball of an analytic avoidance chart is open. -/
theorem isOpen_ball : IsOpen C.ball := Metric.isOpen_ball

/-- The excluded subset is contained in the ball. -/
theorem excludedSet_subset_ball : C.excludedSet ⊆ C.ball := fun _ hx => hx.1

/-- The excluded subset is the intersection of the ball with the zero sets of all the functions. -/
theorem excludedSet_eq_ball_inter_iInter :
    C.excludedSet = C.ball ∩ ⋂ i, C.f i ⁻¹' {0} := by
  ext x; simp [mem_excludedSet]

/-- Each function of the chart is analytic on its ball. -/
theorem analyticOnNhd_ball (i : Fin C.r) : AnalyticOnNhd ℂ (C.f i) C.ball := C.analyticOnNhd i

/-- The radius of the ball of an analytic avoidance chart is positive. -/
theorem radius_pos : 0 < C.radius := by
  obtain ⟨_, x, hx, _⟩ := C.exists_ne_zero
  exact pos_of_mem_ball hx

/-- The ball of an analytic avoidance chart is nonempty. -/
theorem ball_nonempty : C.ball.Nonempty := ⟨C.center, mem_ball_self C.radius_pos⟩

/-- An analytic avoidance chart has at least one function. -/
theorem r_pos : 0 < C.r := by
  obtain ⟨i, _⟩ := C.exists_ne_zero
  exact Fin.pos i

/-- Some point of the ball lies outside the excluded subset. -/
theorem exists_mem_ball_notMem_excludedSet : ∃ x ∈ C.ball, x ∉ C.excludedSet := by
  obtain ⟨i, x, hx, hfx⟩ := C.exists_ne_zero
  exact ⟨x, hx, fun h => hfx (h.2 i)⟩

/-- The complement of the excluded subset in the ball is open. -/
theorem isOpen_ball_diff_excludedSet : IsOpen (C.ball \ C.excludedSet) := by
  have : C.ball \ C.excludedSet = ⋃ i, C.ball ∩ C.f i ⁻¹' {0}ᶜ := by
    ext x
    simp only [Set.mem_sdiff, mem_excludedSet, not_and, not_forall, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨hx, h⟩ => (h hx).imp fun _ h' => ⟨hx, h'⟩,
      fun ⟨i, hx, h'⟩ => ⟨hx, fun _ => ⟨i, h'⟩⟩⟩
  rw [this]
  exact isOpen_iUnion fun i =>
    (C.analyticOnNhd i).continuousOn.isOpen_inter_preimage C.isOpen_ball isOpen_compl_singleton

end AnalyticAvoidanceChart

end MMP.Fourfold
