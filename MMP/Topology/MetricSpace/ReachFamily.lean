module

public import MMP.Geometry.Manifold.Corners.ReachOfImmersion
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# Uniform positive reach for families of sets

Two refinements of the positive reach criterion of
`MMP.Topology.exists_hasUniqueNearestPoints_of_locally_inner_le`.

First, the criterion is uniform in a family: if the sets `A k` all lie in a compact set `Z`,
and near each point of `Z` one constant `K` gives the inequality
`⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` at nearest points `a` of every `A k`, then the `A k`
have a common positive lower bound for their reach. The proof is the same Lebesgue number
argument, run on `Z`.

Second, a `C²` map `g` with injective derivative at `u₀` satisfies the inequality on every
convex set `S` in a fixed ball around `u₀`, with one constant: the Lipschitz constant of the
derivative and the bi-Lipschitz constant of `g` on the ball do not depend on `S`. This is used
for sublevel sets `{ℓ ≤ δ}` of a linear form, uniformly in `δ`.

## Main results

* `MMP.Topology.exists_hasUniqueNearestPoints_of_locally_inner_le_family`
* `MMP.Topology.exists_inner_sub_le_of_contDiffAt`
-/

open Set Filter Topology Metric

namespace MMP.Topology

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A family of closed sets inside a compact set `Z`, satisfying near each point of `Z` the
inequality `⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` at nearest points with one constant for the
whole family, has a uniform positive lower bound for the reach. -/
theorem exists_hasUniqueNearestPoints_of_locally_inner_le_family [ProperSpace F] {κ : Type*}
    {Z : Set F} (hZ : IsCompact Z) {A : κ → Set F} (hAZ : ∀ k, A k ⊆ Z)
    (hA : ∀ k, IsClosed (A k))
    (hloc : ∀ z₀ ∈ Z, ∃ V ∈ 𝓝 z₀, ∃ K : ℝ, ∀ k y, ∀ a ∈ A k ∩ V, dist y a = infDist y (A k) →
      ∀ b ∈ A k ∩ V, inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2) :
    ∃ τ > 0, ∀ k, HasUniqueNearestPoints (A k) τ := by
  choose! V hV K hK using hloc
  obtain ⟨t, htZ, hcov⟩ := hZ.elim_nhds_subcover (fun x ↦ interior (V x))
    fun x hx ↦ interior_mem_nhds.2 (hV x hx)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun x : t ↦ interior (V x))
    hZ (fun _ ↦ isOpen_interior) fun z hz ↦ by
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcov hz)
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hzx⟩
  set Km : ℝ := ∑ x ∈ t, |K x| + 1 / δ
  have hsum : 0 ≤ ∑ x ∈ t, |K x| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hKm0 : 0 < Km := by positivity
  refine ⟨1 / (2 * Km), by positivity, fun k ↦ hasUniqueNearestPoints_of_inner_le (hA k)
    (K := Km) (fun y a haA ha b hbA ↦ ?_) (by field_simp; rfl)⟩
  have hP : 0 ≤ ‖y - a‖ * ‖b - a‖ ^ 2 := by positivity
  rcases lt_or_ge ‖b - a‖ δ with hba | hba
  · obtain ⟨i, hi⟩ := hleb a (hAZ k haA)
    have h := hK i (htZ i i.2) k y a ⟨haA, interior_subset (hi (mem_ball_self hδ))⟩ ha b
      ⟨hbA, interior_subset (hi (by rwa [mem_ball, dist_eq_norm]))⟩
    have hKi : K i ≤ Km := by
      linarith [le_abs_self (K i), one_div_pos.2 hδ,
        Finset.single_le_sum (f := fun x ↦ |K x|) (fun _ _ ↦ abs_nonneg _) i.2]
    calc inner ℝ (y - a) (b - a) ≤ K i * (‖y - a‖ * ‖b - a‖ ^ 2) := by rwa [← mul_assoc]
      _ ≤ Km * (‖y - a‖ * ‖b - a‖ ^ 2) := mul_le_mul_of_nonneg_right hKi hP
      _ = _ := by ring
  · have h1 : ‖y - a‖ * ‖b - a‖ ≤ 1 / δ * (‖y - a‖ * ‖b - a‖ ^ 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
      have := mul_le_mul_of_nonneg_left hba (by positivity : 0 ≤ ‖y - a‖ * ‖b - a‖)
      nlinarith
    calc inner ℝ (y - a) (b - a) ≤ 1 / δ * (‖y - a‖ * ‖b - a‖ ^ 2) :=
        (real_inner_le_norm _ _).trans h1
      _ ≤ Km * (‖y - a‖ * ‖b - a‖ ^ 2) := mul_le_mul_of_nonneg_right (by linarith) hP
      _ = _ := by ring

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- On a convex set, a map whose derivative stays within `C` of an operator `L` with
`‖h‖ ≤ K' ‖L h‖` and `K' C ≤ 1 / 2` satisfies `‖v - u‖ ≤ 2 K' ‖g v - g u‖`. -/
theorem norm_sub_le_two_mul_of_hasFDerivWithinAt {S : Set G} (hS : Convex ℝ S) {g : G → F}
    {D : G → G →L[ℝ] F} {L : G →L[ℝ] F} {C K' : ℝ}
    (hg : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w) (hD : ∀ w ∈ S, ‖D w - L‖ ≤ C)
    (hK' : 0 ≤ K') (hL : ∀ h, ‖h‖ ≤ K' * ‖L h‖) (hKC : K' * C ≤ 1 / 2) {u v : G}
    (hu : u ∈ S) (hv : v ∈ S) : ‖v - u‖ ≤ 2 * K' * ‖g v - g u‖ := by
  have h1 := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun w ↦ g w - L w)
    (fun w hw ↦ (hg w hw).sub L.hasFDerivWithinAt) hD hu hv
  have e : L (v - u) = (g v - g u) - ((g v - L v) - (g u - L u)) := by
    rw [map_sub]
    abel
  have h2 : ‖L (v - u)‖ ≤ ‖g v - g u‖ + C * ‖v - u‖ := by
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add_right h1 _)
  nlinarith [hL (v - u), mul_le_mul_of_nonneg_right hKC (norm_nonneg (v - u)),
    mul_le_mul_of_nonneg_left h2 hK']

/-- Let `g` be `C²` at `u₀` with injective derivative there. Then for some `r > 0` and `K`, on
every convex set `S` in the ball of radius `r` around `u₀`, the image satisfies
`⟪y - g u, g v - g u⟫ ≤ K ‖y - g u‖ ‖g v - g u‖²` whenever `g u` is a nearest point of `y`
among the points `g w`, `w ∈ S`. -/
theorem exists_inner_sub_le_of_contDiffAt [FiniteDimensional ℝ G] {g : G → F} {u₀ : G}
    (hg : ContDiffAt ℝ 2 g u₀) (hinj : Function.Injective (fderiv ℝ g u₀)) :
    ∃ r > 0, ∃ K : ℝ, ∀ S ⊆ ball u₀ r, Convex ℝ S → ∀ y, ∀ u ∈ S,
      IsMinOn (fun w ↦ ‖y - g w‖) S u →
      ∀ v ∈ S, inner ℝ (y - g u) (g v - g u) ≤ K * ‖y - g u‖ * ‖g v - g u‖ ^ 2 := by
  obtain ⟨U, hUo, hu₀U, hgU⟩ := hg.contDiffWithinAt (s := univ).contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem (mem_univ _), univ_inter] at hgU
  have hTu : UniqueDiffOn ℝ U := hUo.uniqueDiffOn
  obtain ⟨hdiff, -, hD1⟩ := (contDiffOn_succ_iff_fderivWithin (n := 1) hTu).1 hgU
  set D := fderivWithin ℝ g U with hD
  have hDdiff : DifferentiableOn ℝ D U := hD1.differentiableOn one_ne_zero
  set D2 := fderivWithin ℝ D U
  have hD2c : ContinuousOn D2 U := hD1.continuousOn_fderivWithin hTu le_rfl
  set B := ‖D2 u₀‖ + 1
  have hB : 0 < B := by positivity
  obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.mem_nhdsWithin_iff.1
    ((hD2c u₀ hu₀U).norm.eventually_lt tendsto_const_nhds (lt_add_one ‖D2 u₀‖))
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.isOpen_iff.1 hUo u₀ hu₀U
  have hinj' : Function.Injective (D u₀) := by
    rwa [hD, fderivWithin_of_isOpen hUo hu₀U]
  obtain ⟨K', hK'0, hK'⟩ :=
    (D u₀ : G →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj')
  have hK'0' : (0 : ℝ) < K' := by exact_mod_cast hK'0
  set r := min (min r₁ r₂) (1 / (2 * K' * B)) with hr
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) (by positivity)
  have hrK : (K' : ℝ) * (B * r) ≤ 1 / 2 := by
    have h := min_le_right (min r₁ r₂) (1 / (2 * K' * B))
    rw [← hr, le_div_iff₀ (by positivity)] at h
    linarith
  set S := ball u₀ r
  have hSconv : Convex ℝ S := convex_ball u₀ r
  have hu₀S : u₀ ∈ S := mem_ball_self hr0
  have hST : S ⊆ U := fun w hw ↦
    hr₂U (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw)
  have hSB : ∀ w ∈ S, ‖D2 w‖ ≤ B := fun w hw ↦
    (hr₁T ⟨ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw, hST hw⟩).le
  have hgS : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w := fun w hw ↦
    ((hdiff w (hST hw)).hasFDerivWithinAt).mono hST
  have hDS : ∀ w ∈ S, HasFDerivWithinAt D (D2 w) S w := fun w hw ↦
    ((hDdiff w (hST hw)).hasFDerivWithinAt).mono hST
  have hL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ B * ‖v - u‖ := fun u hu v hv ↦
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hDS hSB hSconv hu hv
  have hc : ∀ u ∈ S, ∀ v ∈ S, ‖v - u‖ ≤ (2 * K') * ‖g v - g u‖ := fun u hu v hv ↦
    norm_sub_le_two_mul_of_hasFDerivWithinAt hSconv hgS
      (fun w hw ↦ (hL u₀ hu₀S w hw).trans (mul_le_mul_of_nonneg_left
        (by rw [← dist_eq_norm]; exact (mem_ball.1 hw).le) hB.le))
      hK'0'.le (fun h ↦ (D u₀).bound_of_antilipschitz hK' h) hrK hu hv
  exact ⟨r, hr0, B * (2 * K') ^ 2, fun S' hS' hS'c y u hu hmin v hv ↦
    inner_sub_le_mul_norm_sq_of_isMinOn hS'c (fun w hw ↦ (hgS w (hS' hw)).mono hS') hB.le
      (fun u hu v hv ↦ hL u (hS' hu) v (hS' hv)) (fun u hu v hv ↦ hc u (hS' hu) v (hS' hv))
      hu hmin hv⟩

end

end MMP.Topology
