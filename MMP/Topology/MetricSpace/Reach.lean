module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Sets of positive reach and their nearest-point retraction

Following Federer, a closed set `A` in a metric space has *reach at least `τ`* when every point
`y` at distance less than `τ` from `A` has a unique nearest point `π y ∈ A`. We record this as
`MMP.Topology.HasUniqueNearestPoints A τ`.

In a proper metric space the nearest-point map `π` is then continuous on the open
`τ`-neighbourhood of `A`, by compactness of closed balls and uniqueness (Federer 4.8(4)).

In a proper real inner product space, more is true. The squared distance `infDist · A ^ 2` is
differentiable on the `τ`-neighbourhood, with gradient `2 (y - π y)`. From this, the nearest
point stays constant along the whole normal ray: for `y` in the neighbourhood, the points
`π y + t (y - π y)` with `t ‖y - π y‖ < τ` all have nearest point `π y` (Federer 4.8(6)).
Comparing distances along the normal ray up to length `τ` gives Federer's inequality
`2 τ ⟪y - π y, x - π y⟫ ≤ ‖x - π y‖ ^ 2 ‖y - π y‖` for `x ∈ A` (Federer 4.8(7), (12)).

A complete convex set has unique nearest points at every distance.

## Main definitions

* `MMP.Topology.HasUniqueNearestPoints A τ`: every point of the open `τ`-neighbourhood of `A`
  has a unique nearest point in `A`, that is, `A` has reach at least `τ`.

## Main results

* `MMP.Topology.HasUniqueNearestPoints.continuousOn`: the nearest-point map is continuous on
  the open `τ`-neighbourhood.
* `MMP.Topology.hasFDerivAt_infDist_sq`: the squared distance to `A` is
  differentiable there, with derivative `2 ⟪y - π y, ·⟫`.
* `MMP.Topology.HasUniqueNearestPoints.map_add_smul_sub`: the nearest point is constant along
  the normal ray up to distance `τ`.
* `MMP.Topology.HasUniqueNearestPoints.two_mul_mul_inner_le`: Federer's inequality.
* `MMP.Topology.HasUniqueNearestPoints.exists_nearestPoint`: a nearest-point retraction of
  reach `τ`, continuous and satisfying Federer's inequality.
* `MMP.Topology.hasUniqueNearestPoints_of_convex`: complete convex sets have infinite reach.

## Implementation notes

Federer extends the normal ray past its last point `w` with unchanged nearest point by a
fixed-point argument. Here the extension comes from a maximum of
`infDist z A ^ 2 - λ ‖z - w‖ ^ 2` over a small closed ball around `w`, for large `λ`: the
maximum is interior, so the gradient `2 (z - π z) - 2 λ (z - w)` vanishes there, which places
`w` on the normal segment of the maximising point `z` (see
`MMP.Topology.HasUniqueNearestPoints.exists_one_lt_map_add_smul_sub`).

The nearest-point map is an arbitrary function `π` assumed to pick a nearest point on the
`τ`-neighbourhood; `MMP.Topology.HasUniqueNearestPoints.exists_nearestPoint` chooses one.

## References

* [H. Federer, *Curvature measures*, Theorem 4.8][federer1959]
-/

open Set Filter Topology Metric

namespace MMP.Topology

@[expose] public section

section Metric

variable {α : Type*} [PseudoMetricSpace α]

/-- A set `A` *has unique nearest points in its open `τ`-neighbourhood* (Federer: `A` has reach
at least `τ`) if every point at distance less than `τ` from `A` has exactly one nearest point
in `A`. -/
def HasUniqueNearestPoints (A : Set α) (τ : ℝ) : Prop :=
  ∀ y ∈ thickening τ A, ∃! x, x ∈ A ∧ dist y x = infDist y A

/-- Having unique nearest points within distance `τ` passes to any smaller distance. -/
theorem HasUniqueNearestPoints.mono {A : Set α} {τ τ' : ℝ} (hu : HasUniqueNearestPoints A τ)
    (h : τ' ≤ τ) : HasUniqueNearestPoints A τ' :=
  fun y hy ↦ hu y (thickening_mono h A hy)

variable {A : Set α} {τ : ℝ} {π : α → α}

namespace HasUniqueNearestPoints

/-- A point of `A` that is at least as close to `y` as `A` is, is the nearest point `π y`. -/
theorem eq_of_dist_le (hu : HasUniqueNearestPoints A τ)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A) {y : α}
    (hy : y ∈ thickening τ A) {x : α} (hx : x ∈ A) (hxy : dist y x ≤ infDist y A) :
    x = π y :=
  (hu y hy).unique ⟨hx, le_antisymm hxy (infDist_le_dist_of_mem hx)⟩ (hπ y hy)

/-- In a proper space, the nearest-point map of a closed set with unique nearest points in its
open `τ`-neighbourhood is continuous on that neighbourhood. -/
theorem continuousOn [ProperSpace α] (hu : HasUniqueNearestPoints A τ) (hA : IsClosed A)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A) :
    ContinuousOn π (thickening τ A) := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hnhds : thickening τ A ∈ 𝓝 y := isOpen_thickening.mem_nhds hy
  have hdist : ∀ η > 0, ∀ᶠ y' in 𝓝 y, π y' ∈ closedBall y (infDist y A + η) := by
    intro η hη
    filter_upwards [hnhds, ball_mem_nhds y (half_pos hη)] with y' hy' hyy'
    rw [mem_ball] at hyy'
    rw [mem_closedBall]
    calc dist (π y') y ≤ dist (π y') y' + dist y' y := dist_triangle _ _ _
      _ = infDist y' A + dist y' y := by rw [dist_comm, (hπ y' hy').2]
      _ ≤ (infDist y A + dist y' y) + dist y' y := by
        gcongr; exact infDist_le_infDist_add_dist
      _ ≤ infDist y A + η := by linarith
  have hA' : ∀ᶠ y' in 𝓝 y, π y' ∈ A := by
    filter_upwards [hnhds] with y' hy' using (hπ y' hy').1
  refine isCompact_closedBall y (infDist y A + 1) |>.tendsto_nhds_of_unique_mapClusterPt
    (hdist 1 one_pos) fun x _ hx ↦ ?_
  have key : ∀ {s : Set α}, IsClosed s → (∀ᶠ y' in 𝓝 y, π y' ∈ s) → x ∈ s := fun hs h ↦
    hs.closure_subset (ClusterPt.mem_closure (ClusterPt.mono hx (le_principal_iff.2 h)))
  have hxA : x ∈ A := key hA hA'
  refine hu.eq_of_dist_le hπ hy hxA (le_of_forall_pos_le_add fun η hη ↦ ?_)
  have := key isClosed_closedBall (hdist η hη)
  rwa [mem_closedBall, dist_comm] at this

end HasUniqueNearestPoints

end Metric

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : Set E} {τ : ℝ}
  {π : E → E}

namespace HasUniqueNearestPoints

/-- For `0 ≤ s ≤ 1`, the point `π y + s • (y - π y)` of the segment from `π y` to `y` lies in the
open `τ`-neighbourhood and has nearest point `π y`. -/
theorem map_add_smul_sub_of_le_one (hu : HasUniqueNearestPoints A τ)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A) {y : E}
    (hy : y ∈ thickening τ A) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    π y + s • (y - π y) ∈ thickening τ A ∧ π (π y + s • (y - π y)) = π y := by
  obtain ⟨hpA, hpd⟩ := hπ y hy
  set p := π y
  set z := p + s • (y - p)
  have hd : ‖y - p‖ = infDist y A := by rw [← dist_eq_norm, hpd]
  have hzp : dist z p = s * infDist y A := by
    rw [dist_eq_norm, show z - p = s • (y - p) by simp [z], norm_smul, Real.norm_of_nonneg hs0,
      hd]
  have hyz : dist y z = (1 - s) * infDist y A := by
    rw [dist_eq_norm, show y - z = (1 - s) • (y - p) by simp only [z]; module, norm_smul,
      Real.norm_of_nonneg (by linarith), hd]
  have hτ : infDist y A < τ := (mem_thickening_iff_infDist_lt ⟨p, hpA⟩).1 hy
  have h0 := infDist_nonneg (x := y) (s := A)
  have hzT : z ∈ thickening τ A :=
    mem_thickening_iff.2 ⟨p, hpA, by rw [hzp]; nlinarith⟩
  refine ⟨hzT, (hu.eq_of_dist_le hπ hzT hpA ?_).symm⟩
  rw [hzp]
  refine (le_infDist ⟨p, hpA⟩).2 fun x hx ↦ ?_
  have h1 : infDist y A ≤ dist y x := infDist_le_dist_of_mem hx
  have h2 := dist_triangle y z x
  linarith

end HasUniqueNearestPoints

/-- If `π` picks a nearest point of `A` for every point of the open `τ`-neighbourhood of `A` and
is continuous there, then `infDist · A ^ 2` is differentiable on that neighbourhood, with
derivative `2 ⟪y - π y, ·⟫`. -/
theorem hasFDerivAt_infDist_sq (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A)
    (hπc : ContinuousOn π (thickening τ A)) {y : E} (hy : y ∈ thickening τ A) :
    HasFDerivAt (fun z ↦ infDist z A ^ 2) ((2 : ℝ) • innerSL ℝ (y - π y)) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_
  have hnhds : thickening τ A ∈ 𝓝 y := isOpen_thickening.mem_nhds hy
  have hadd : Tendsto (fun h : E ↦ y + h) (𝓝 0) (𝓝 y) := by
    simpa using ((continuous_const_add y).tendsto 0)
  have hcont : Tendsto (fun h : E ↦ π (y + h)) (𝓝 0) (𝓝 (π y)) :=
    (hπc.continuousAt hnhds).tendsto.comp hadd
  obtain ⟨hpA, hpd⟩ := hπ y hy
  filter_upwards [hadd hnhds, ball_mem_nhds (0 : E) (half_pos hc),
    hcont (ball_mem_nhds (π y) (by positivity : 0 < c / 4))] with h hyh hh hq
  rw [mem_preimage] at hyh
  rw [mem_ball, dist_zero_right] at hh
  rw [mem_preimage, mem_ball, dist_eq_norm] at hq
  obtain ⟨hqA, hqd⟩ := hπ (y + h) hyh
  set p := π y
  set q := π (y + h)
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Real.norm_eq_abs]
  have hfy : infDist y A ^ 2 = ‖y - p‖ ^ 2 := by rw [← hpd, dist_eq_norm]
  have hfyh : infDist (y + h) A ^ 2 = ‖y + h - q‖ ^ 2 := by rw [← hqd, dist_eq_norm]
  have hup : infDist (y + h) A ^ 2 ≤ ‖y + h - p‖ ^ 2 := by
    rw [← dist_eq_norm]
    exact pow_le_pow_left₀ infDist_nonneg (infDist_le_dist_of_mem hpA) 2
  have hlo : infDist y A ^ 2 ≤ ‖y - q‖ ^ 2 := by
    rw [← dist_eq_norm]
    exact pow_le_pow_left₀ infDist_nonneg (infDist_le_dist_of_mem hqA) 2
  have e1 : ‖y + h - p‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * inner ℝ (y - p) h + ‖h‖ ^ 2 := by
    rw [← norm_add_sq_real, add_sub_right_comm]
  have e2 : ‖y + h - q‖ ^ 2 = ‖y - q‖ ^ 2 + 2 * inner ℝ (y - q) h + ‖h‖ ^ 2 := by
    rw [← norm_add_sq_real, add_sub_right_comm]
  have e3 : inner ℝ (y - q) h = inner ℝ (y - p) h + inner ℝ (p - q) h := by
    rw [← inner_add_left]; congr 1; abel
  have hpq : |inner ℝ (p - q) h| ≤ ‖p - q‖ * ‖h‖ := abs_real_inner_le_norm _ _
  have hpq' : ‖p - q‖ * ‖h‖ ≤ c / 4 * ‖h‖ := by
    gcongr; rw [norm_sub_rev]; exact hq.le
  have hh2 : ‖h‖ ^ 2 ≤ c / 2 * ‖h‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
  rw [abs_le] at hpq ⊢
  constructor <;> nlinarith [norm_nonneg h]

namespace HasUniqueNearestPoints

/-- If `w` lies in the open `τ`-neighbourhood and `π w ≠ w`, then for some `r > 1` the point
`π w + r • (w - π w)` still lies in that neighbourhood and has nearest point `π w`. -/
theorem exists_one_lt_map_add_smul_sub [ProperSpace E] (hu : HasUniqueNearestPoints A τ)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A)
    (hπc : ContinuousOn π (thickening τ A)) {w : E} (hw : w ∈ thickening τ A) (hw0 : π w ≠ w) :
    ∃ r : ℝ, 1 < r ∧ π w + r • (w - π w) ∈ thickening τ A ∧ π (π w + r • (w - π w)) = π w := by
  obtain ⟨hpA, hpd⟩ := hπ w hw
  set d := infDist w A with hd_def
  have hd0 : 0 < d := by
    rw [← hpd]; exact dist_pos.2 (Ne.symm hw0)
  have hdτ : d < τ := (mem_thickening_iff_infDist_lt ⟨_, hpA⟩).1 hw
  set ρ := (τ - d) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set l := 1 + 4 * d / ρ with hl
  have hl1 : 1 < l := by
    have : 0 < 4 * d / ρ := by positivity
    linarith
  have hball : closedBall w ρ ⊆ thickening τ A := fun z hz ↦ by
    rw [mem_closedBall] at hz
    refine (mem_thickening_iff_infDist_lt ⟨_, hpA⟩).2 ?_
    have := infDist_le_infDist_add_dist (s := A) (x := z) (y := w)
    linarith
  set ψ : E → ℝ := fun z ↦ infDist z A ^ 2 - l * ‖z - w‖ ^ 2 with hψ
  have hψc : Continuous ψ :=
    ((continuous_infDist_pt A).pow 2).sub (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2))
  obtain ⟨z, hzK, hmax⟩ := (isCompact_closedBall w ρ).exists_isMaxOn
    (nonempty_closedBall.2 hρ0.le) hψc.continuousOn
  have hψw : ψ w = d ^ 2 := by simp [hψ, hd_def]
  have hzb : z ∈ ball w ρ := by
    rw [mem_closedBall] at hzK
    rw [mem_ball]
    refine lt_of_le_of_ne hzK fun hzρ ↦ ?_
    have h1 : ψ w ≤ ψ z := hmax (mem_closedBall_self hρ0.le)
    have h2 : infDist z A ≤ d + ρ := by
      have := infDist_le_infDist_add_dist (s := A) (x := z) (y := w); linarith
    have h3 : infDist z A ^ 2 ≤ (d + ρ) ^ 2 :=
      pow_le_pow_left₀ infDist_nonneg h2 2
    have h4 : l * ρ ^ 2 = ρ ^ 2 + 4 * d * ρ := by
      rw [hl]; field_simp
    have : ψ z = infDist z A ^ 2 - l * ρ ^ 2 := by
      simp only [hψ, ← dist_eq_norm, hzρ]
    nlinarith
  have hzT : z ∈ thickening τ A := hball hzK
  have hloc : IsLocalMax ψ z :=
    hmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hzb) ball_subset_closedBall)
  have hderiv := (hasFDerivAt_infDist_sq hπ hπc hzT).sub
      (((hasFDerivAt_id z).sub_const w).norm_sq.const_mul l)
  have h0 := DFunLike.congr_fun (hloc.hasFDerivAt_eq_zero hderiv) ((z - π z) - l • (z - w))
  simp only [sub_apply, smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    zero_apply, nsmul_eq_mul, Nat.cast_ofNat, id_eq] at h0
  have hv : z - π z = l • (z - w) := by
    have : inner ℝ ((z - π z) - l • (z - w)) ((z - π z) - l • (z - w)) = 0 := by
      rw [inner_sub_left, real_inner_smul_left]; linarith
    exact sub_eq_zero.1 (inner_self_eq_zero.1 this)
  have hl0 : l ≠ 0 := by positivity
  have hinv : l⁻¹ • (z - π z) = z - w := by
    rw [hv, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hs : 0 < 1 - l⁻¹ := by
    have : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    linarith
  have hwz : w = π z + (1 - l⁻¹) • (z - π z) := by
    linear_combination (norm := module) hinv
  have hpw : π w = π z := by
    have := (hu.map_add_smul_sub_of_le_one hπ hzT hs.le (by
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right, inv_nonneg]; positivity)).2
    rwa [← hwz] at this
  have hr1 : 1 < (1 - l⁻¹)⁻¹ :=
    (one_lt_inv₀ hs).2 (by simp only [sub_lt_self_iff, inv_pos]; positivity)
  refine ⟨(1 - l⁻¹)⁻¹, hr1, ?_⟩
  have hz : π w + (1 - l⁻¹)⁻¹ • (w - π w) = z := by
    rw [hpw]
    conv_lhs => rw [hwz]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_sub_cancel]
  rw [hz, hpw]
  exact ⟨hzT, rfl⟩

/-- The nearest point is constant along the normal ray through `y`, up to distance `τ` from
`π y` (Federer 4.8(6)). -/
theorem map_add_smul_sub [ProperSpace E] (hu : HasUniqueNearestPoints A τ)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A)
    (hπc : ContinuousOn π (thickening τ A)) {y : E} (hy : y ∈ thickening τ A) {t : ℝ}
    (ht0 : 0 ≤ t) (htτ : t * ‖y - π y‖ < τ) : π (π y + t • (y - π y)) = π y := by
  obtain ⟨hpA, -⟩ := hπ y hy
  set p := π y
  set v := y - p
  have hmem : ∀ s : ℝ, 0 ≤ s → s * ‖v‖ < τ → p + s • v ∈ thickening τ A := fun s hs0 hs ↦
    mem_thickening_iff.2 ⟨p, hpA, by
      rwa [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]⟩
  have hgood1 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → π (p + s • v) = p := fun s h0 h1 ↦
    (hu.map_add_smul_sub_of_le_one hπ hy h0 h1).2
  have hdown : ∀ s s' : ℝ, 0 ≤ s → s ≤ s' → p + s' • v ∈ thickening τ A →
      π (p + s' • v) = p → π (p + s • v) = p := by
    intro s s' hs0 hss' hz hgood
    rcases hs0.eq_or_lt with rfl | hs0'
    · exact hgood1 0 le_rfl zero_le_one
    have hs'0 : s' ≠ 0 := by linarith
    have := (hu.map_add_smul_sub_of_le_one hπ hz (s := s / s') (div_nonneg hs0 (by linarith))
      (div_le_one_of_le₀ hss' (by linarith))).2
    rw [hgood, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hs'0] at this
    exact this
  by_contra hne
  set B := {s : ℝ | 0 ≤ s ∧ s * ‖v‖ < τ ∧ π (p + s • v) ≠ p}
  have htB : t ∈ B := ⟨ht0, htτ, hne⟩
  have hBbdd : BddBelow B := ⟨0, fun s hs ↦ hs.1⟩
  set T := sInf B
  have h1T : 1 ≤ T := le_csInf ⟨t, htB⟩ fun s hs ↦ by
    by_contra h
    exact hs.2.2 (hgood1 s hs.1 (not_le.1 h).le)
  have hTt : T ≤ t := csInf_le hBbdd htB
  have hTτ : T * ‖v‖ < τ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hTt (norm_nonneg _)) htτ
  have hbelow : ∀ s : ℝ, 0 ≤ s → s < T → π (p + s • v) = p := fun s h0 hsT ↦ by
    by_contra h
    exact notMem_of_lt_csInf hsT hBbdd ⟨h0, lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (hsT.le.trans hTt) (norm_nonneg _)) htτ, h⟩
  have hwT := hmem T (by linarith) hTτ
  have hT : π (p + T • v) = p := by
    have hc : ContinuousAt (fun s : ℝ ↦ π (p + s • v)) T :=
      ContinuousAt.comp (g := π) (hπc.continuousAt (isOpen_thickening.mem_nhds hwT))
        (by fun_prop)
    have hev : (fun s : ℝ ↦ π (p + s • v)) =ᶠ[𝓝[<] T] fun _ ↦ p := by
      filter_upwards [Ioo_mem_nhdsLT (by linarith : (0 : ℝ) < T)] with s hs using
        hbelow s hs.1.le hs.2
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hv0 : v ≠ 0 := by
    intro h0
    apply hne
    rw [h0, smul_zero, add_zero]
    simpa using hgood1 0 le_rfl zero_le_one
  have hw0 : π (p + T • v) ≠ p + T • v := by
    rw [hT]
    intro h
    exact smul_ne_zero (by linarith : T ≠ 0) hv0 (by simpa using h.symm)
  obtain ⟨r, hr1, hrT, hr⟩ := hu.exists_one_lt_map_add_smul_sub hπ hπc hwT hw0
  rw [hT, add_sub_cancel_left, smul_smul] at hr hrT
  obtain ⟨b, hbB, hb⟩ := exists_lt_of_csInf_lt ⟨t, htB⟩ (show T < r * T by nlinarith)
  exact hbB.2.2 (hdown b (r * T) hbB.1 hb.le hrT hr)

/-- **Federer's inequality** (Federer 4.8(7), (12)): for a set with unique nearest points in its
open `τ`-neighbourhood, `2 τ ⟪y - π y, x - π y⟫ ≤ ‖x - π y‖ ^ 2 ‖y - π y‖` for every `y` in that
neighbourhood and every `x ∈ A`. -/
theorem two_mul_mul_inner_le [ProperSpace E] (hu : HasUniqueNearestPoints A τ)
    (hπ : ∀ y ∈ thickening τ A, π y ∈ A ∧ dist y (π y) = infDist y A)
    (hπc : ContinuousOn π (thickening τ A)) {y : E} (hy : y ∈ thickening τ A) {x : E}
    (hx : x ∈ A) : 2 * τ * inner ℝ (y - π y) (x - π y) ≤ ‖x - π y‖ ^ 2 * ‖y - π y‖ := by
  obtain ⟨hpA, -⟩ := hπ y hy
  have hτ0 : 0 < τ :=
    lt_of_le_of_lt infDist_nonneg ((mem_thickening_iff_infDist_lt ⟨_, hpA⟩).1 hy)
  have key : ∀ s ∈ Ioo 0 τ,
      2 * s * inner ℝ (y - π y) (x - π y) ≤ ‖x - π y‖ ^ 2 * ‖y - π y‖ := by
    rintro s ⟨hs0, hsτ⟩
    rcases eq_or_ne (y - π y) 0 with h0 | h0
    · rw [h0, inner_zero_left, norm_zero]; simp
    have hd : 0 < ‖y - π y‖ := norm_pos_iff.2 h0
    set p := π y
    set v := y - p
    set t := s / ‖v‖
    have ht0 : 0 ≤ t := by positivity
    have htv : t * ‖v‖ = s := div_mul_cancel₀ _ hd.ne'
    have hc := hu.map_add_smul_sub hπ hπc hy ht0 (by rw [htv]; exact hsτ)
    have hcT : p + t • v ∈ thickening τ A := mem_thickening_iff.2 ⟨p, hpA, by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0, htv]
      exact hsτ⟩
    have h1 : dist (p + t • v) p ≤ dist (p + t • v) x := by
      have := (hπ _ hcT).2
      rw [hc] at this
      rw [this]
      exact infDist_le_dist_of_mem hx
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h1
    have h2 : ‖p + t • v - x‖ ^ 2 = ‖t • v‖ ^ 2 + 2 * inner ℝ (t • v) (p - x) + ‖p - x‖ ^ 2 := by
      rw [← norm_add_sq_real, add_comm (t • v), add_sub_right_comm, add_comm]
    have h3 : ‖t • v‖ ^ 2 ≤ ‖p + t • v - x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [real_inner_smul_left, ← neg_sub x p, inner_neg_right, norm_neg] at h2
    calc 2 * s * inner ℝ v (x - p) = (2 * t * inner ℝ v (x - p)) * ‖v‖ := by
          rw [← htv]
          ring
      _ ≤ ‖x - p‖ ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_right (by linarith) hd.le
  refine le_of_tendsto (x := 𝓝[<] τ) (f := fun s ↦ 2 * s * inner ℝ (y - π y) (x - π y)) ?_ ?_
  · exact ((by fun_prop : Continuous fun s : ℝ ↦ 2 * s * inner ℝ (y - π y) (x - π y)).tendsto
      τ).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT hτ0] with s hs using key s hs

/-- A closed set of reach at least `τ` in a proper real inner product space has a nearest-point
retraction of reach `τ`: a map `π`, continuous on the open `τ`-neighbourhood of `A`, sending
each point of it to a nearest point of `A`, and satisfying Federer's inequality. -/
theorem exists_nearestPoint [ProperSpace E] (hu : HasUniqueNearestPoints A τ) (hA : IsClosed A) :
    ∃ π : E → E, ContinuousOn π (thickening τ A) ∧ (∀ y ∈ thickening τ A, π y ∈ A) ∧
      (∀ y ∈ thickening τ A, ∀ x ∈ A, ‖y - π y‖ ≤ ‖y - x‖) ∧
      (∀ y ∈ thickening τ A, ∀ x ∈ A,
        2 * τ * inner ℝ (y - π y) (x - π y) ≤ ‖x - π y‖ ^ 2 * ‖y - π y‖) := by
  choose! π hπ using fun y hy ↦ (hu y hy).exists
  have hπc := hu.continuousOn hA hπ
  refine ⟨π, hπc, fun y hy ↦ (hπ y hy).1, fun y hy x hx ↦ ?_,
    fun y hy x hx ↦ hu.two_mul_mul_inner_le hπ hπc hy hx⟩
  rw [← dist_eq_norm, ← dist_eq_norm, (hπ y hy).2]
  exact infDist_le_dist_of_mem hx

end HasUniqueNearestPoints

/-- A complete convex set in a real inner product space has unique nearest points at every
distance: it has infinite reach. -/
theorem hasUniqueNearestPoints_of_convex (hc : Convex ℝ A) (hA : IsComplete A) (τ : ℝ) :
    HasUniqueNearestPoints A τ := by
  intro y hy
  obtain ⟨z, hzA, -⟩ := mem_thickening_iff.1 hy
  obtain ⟨x, hxA, hx⟩ := exists_norm_eq_iInf_of_complete_convex ⟨z, hzA⟩ hA hc y
  replace hx : infDist y A = dist y x := by simp only [infDist_eq_iInf, dist_eq_norm, hx]
  refine ⟨x, ⟨hxA, hx.symm⟩, fun x' ⟨hx'A, hx'⟩ ↦ ?_⟩
  have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x' ∈ A :=
    hc hxA hx'A (by norm_num) (by norm_num) (by norm_num)
  have hdm : infDist y A ≤ ‖y - ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x')‖ := by
    rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hm
  have hpar := parallelogram_law_with_norm ℝ (y - x) (y - x')
  have e1 : (y - x) + (y - x') = (2 : ℝ) • (y - ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x')) := by
    module
  have e2 : (y - x) - (y - x') = x' - x := by abel
  rw [e1, e2, norm_smul, ← dist_eq_norm y x, ← dist_eq_norm y x', ← hx, hx'] at hpar
  have h0 := infDist_nonneg (x := y) (s := A)
  have hsq : ‖x' - x‖ ^ 2 ≤ 0 := by
    norm_num at hpar
    nlinarith
  have : ‖x' - x‖ = 0 := by nlinarith [norm_nonneg (x' - x)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end InnerProduct

end

end MMP.Topology
