module

public import MMP.Topology.MetricSpace.Reach
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Positive reach of an embedded compact manifold with corners

Let `e : M → F` be a `C²` embedding of a compact manifold with corners into a real inner product
space whose derivative is injective at every point. Then the image `A = range e` has positive
reach: there is `τ > 0` such that every point at distance less than `τ` from `A` has a unique
nearest point in `A` (Federer, *Curvature measures*, Theorem 4.12 and Remark 4.20).

The argument is a quantitative form of the first-order condition for a nearest point. If `a`
is a nearest point of `y` in a closed set `A`, and `A` satisfies
`⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` for all `b ∈ A`, then any second nearest point `b`
satisfies `‖b - a‖² = 2 ⟪y - a, b - a⟫ ≤ 2 K ‖y - a‖ ‖b - a‖²`, so `b = a` once
`‖y - a‖ < 1 / (2 K)`. Such an inequality for pairs of nearby points globalises by compactness,
since for `‖b - a‖ ≥ δ` the Cauchy–Schwarz inequality gives it with `K = 1 / δ`.

Near a point of `M`, the image is parametrised by `g = e ∘ (extChartAt I x₀).symm` on a convex
piece `S` of the range of the model. There `g` has a Lipschitz derivative, and it is
bi-Lipschitz because its derivative at the centre is injective. If `a = g u` is a nearest point
of `y`, the function `w ↦ ‖y - g w‖²` is minimal on `S` at `u`, so its derivative is
nonnegative in the directions `v - u` of the convex set `S`: `⟪y - a, Dg(u) (v - u)⟫ ≤ 0`. A
second-order Taylor bound for `g v - g u - Dg(u) (v - u)` then gives the inequality above. No
extension of `g` beyond the corner is needed: all estimates are mean value inequalities on the
convex set `S`.

## Main results

* `MMP.Topology.hasUniqueNearestPoints_of_inner_le`: a closed set with
  `⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` at nearest points `a` has reach at least `1 / (2 K)`.
* `MMP.Topology.exists_hasUniqueNearestPoints_of_locally_inner_le`: for a compact set, it is
  enough to have this inequality locally.
* `MMP.Topology.inner_sub_le_mul_norm_sq_of_isMinOn`: the inequality for a bi-Lipschitz map
  with Lipschitz derivative on a convex set.
* `MMP.Topology.exists_hasUniqueNearestPoints_range`: the image of a compact manifold with
  corners under a `C²` embedding with injective derivative has positive reach.

## References

* [H. Federer, *Curvature measures*, Theorem 4.12, Remark 4.20][federer1959]
-/

open Set Filter Topology Metric
open scoped Manifold

namespace MMP.Topology

public section

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A closed set `A` in a proper real inner product space such that
`⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` whenever `a` is a nearest point of `y` and `b ∈ A` has
unique nearest points in its open `τ`-neighbourhood for every `τ` with `2 K τ ≤ 1`. -/
theorem hasUniqueNearestPoints_of_inner_le [ProperSpace F] {A : Set F} (hA : IsClosed A)
    {K : ℝ} (hK : ∀ y, ∀ a ∈ A, dist y a = infDist y A → ∀ b ∈ A,
      inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2)
    {τ : ℝ} (hKτ : 2 * K * τ ≤ 1) : HasUniqueNearestPoints A τ := by
  intro y hy
  obtain ⟨z, hzA, -⟩ := mem_thickening_iff.1 hy
  have hlt : infDist y A < τ := (mem_thickening_iff_infDist_lt ⟨z, hzA⟩).1 hy
  obtain ⟨a, haA, ha⟩ := hA.exists_infDist_eq_dist ⟨z, hzA⟩ y
  refine ⟨a, ⟨haA, ha.symm⟩, fun b ⟨hbA, hb⟩ ↦ ?_⟩
  have h := hK y a haA ha.symm b hbA
  have hexp : ‖y - b‖ ^ 2 = ‖y - a‖ ^ 2 - 2 * inner ℝ (y - a) (b - a) + ‖b - a‖ ^ 2 := by
    rw [show y - b = (y - a) - (b - a) by abel, norm_sub_sq_real]
  rw [← dist_eq_norm y b, ← dist_eq_norm y a, hb, ha] at hexp
  rw [ha] at hlt
  rw [← dist_eq_norm] at h
  have h1 : 2 * K * dist y a < 1 := by
    rcases le_or_gt K 0 with hK0 | hK0
    · nlinarith [dist_nonneg (x := y) (y := a)]
    · nlinarith
  have h2 : ‖b - a‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖b - a‖]
  rw [← sub_eq_zero, ← norm_eq_zero]
  nlinarith [norm_nonneg (b - a)]

/-- A compact set `A` in a proper real inner product space has positive reach if, near each of
its points, `⟪y - a, b - a⟫ ≤ K ‖y - a‖ ‖b - a‖²` whenever `a` is a nearest point of `y` and
`b ∈ A`. -/
theorem exists_hasUniqueNearestPoints_of_locally_inner_le [ProperSpace F] {A : Set F}
    (hA : IsCompact A)
    (hloc : ∀ a₀ ∈ A, ∃ V ∈ 𝓝 a₀, ∃ K : ℝ, ∀ y, ∀ a ∈ A ∩ V, dist y a = infDist y A →
      ∀ b ∈ A ∩ V, inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2) :
    ∃ τ > 0, HasUniqueNearestPoints A τ := by
  classical
  choose! V hV K hK using hloc
  obtain ⟨t, htA, hcov⟩ := hA.elim_nhds_subcover (fun x ↦ interior (V x))
    fun x hx ↦ interior_mem_nhds.2 (hV x hx)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun x : t ↦ interior (V x))
    hA (fun _ ↦ isOpen_interior) fun z hz ↦ by
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcov hz)
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hzx⟩
  set Km : ℝ := ∑ x ∈ t, |K x| + 1 / δ
  have hsum : 0 ≤ ∑ x ∈ t, |K x| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hKm0 : 0 < Km := by positivity
  refine ⟨1 / (2 * Km), by positivity, hasUniqueNearestPoints_of_inner_le hA.isClosed
    (K := Km) (fun y a haA ha b hbA ↦ ?_) (mul_one_div_cancel (by positivity)).le⟩
  have hP : 0 ≤ ‖y - a‖ * ‖b - a‖ ^ 2 := by positivity
  rcases lt_or_ge ‖b - a‖ δ with hba | hba
  · obtain ⟨i, hi⟩ := hleb a haA
    have haV : a ∈ V i := interior_subset (hi (mem_ball_self hδ))
    have hbV : b ∈ V i := interior_subset (hi (by rwa [mem_ball, dist_eq_norm]))
    have h := hK i (htA i i.2) y a ⟨haA, haV⟩ ha b ⟨hbA, hbV⟩
    have hKi : K i ≤ Km := by
      linarith [Finset.single_le_sum (f := fun x ↦ |K x|) (fun _ _ ↦ abs_nonneg _) i.2,
        le_abs_self (K i), one_div_pos.2 hδ]
    calc inner ℝ (y - a) (b - a) ≤ K i * (‖y - a‖ * ‖b - a‖ ^ 2) := by rwa [← mul_assoc]
      _ ≤ Km * (‖y - a‖ * ‖b - a‖ ^ 2) := mul_le_mul_of_nonneg_right hKi hP
      _ = _ := by ring
  · have h1 : ‖y - a‖ * ‖b - a‖ ≤ 1 / δ * (‖y - a‖ * ‖b - a‖ ^ 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
      have := mul_le_mul_of_nonneg_left hba (by positivity : 0 ≤ ‖y - a‖ * ‖b - a‖)
      nlinarith
    calc inner ℝ (y - a) (b - a) ≤ 1 / δ * (‖y - a‖ * ‖b - a‖ ^ 2) :=
        (real_inner_le_norm (y - a) (b - a)).trans h1
      _ ≤ Km * (‖y - a‖ * ‖b - a‖ ^ 2) := mul_le_mul_of_nonneg_right (by linarith) hP
      _ = _ := by ring

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Let `g` be a map on a convex set `S`, with a derivative `D` that is `L`-Lipschitz on `S`,
and with `‖v - u‖ ≤ c ‖g v - g u‖` on `S`. If `g u` is a point of `g '' S` nearest to `y`, then
`⟪y - g u, g v - g u⟫ ≤ L c² ‖y - g u‖ ‖g v - g u‖²` for `v ∈ S`. -/
theorem inner_sub_le_mul_norm_sq_of_isMinOn {g : G → F} {D : G → G →L[ℝ] F} {S : Set G}
    (hS : Convex ℝ S) (hg : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w) {L c : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ L * ‖v - u‖)
    (hc : ∀ u ∈ S, ∀ v ∈ S, ‖v - u‖ ≤ c * ‖g v - g u‖) {y : F} {u : G} (hu : u ∈ S)
    (hmin : IsMinOn (fun w ↦ ‖y - g w‖) S u) {v : G} (hv : v ∈ S) :
    inner ℝ (y - g u) (g v - g u) ≤ L * c ^ 2 * ‖y - g u‖ * ‖g v - g u‖ ^ 2 := by
  have hseg : segment ℝ u v ⊆ S := hS.segment_subset hu hv
  have hfirst : inner ℝ (y - g u) (D u (v - u)) ≤ 0 := by
    have hlm : IsLocalMinOn (fun w ↦ ‖y - g w‖ ^ 2) S u :=
      IsMinOn.isLocalMinOn fun w hw ↦
        pow_le_pow_left₀ (norm_nonneg _) (hmin hw) 2
    have hd : HasFDerivWithinAt (fun w ↦ ‖y - g w‖ ^ 2)
        (2 • (innerSL ℝ (y - g u)).comp (0 - D u)) S u :=
      ((hasFDerivWithinAt_const y u S).sub (hg u hu)).norm_sq
    have := hlm.hasFDerivWithinAt_nonneg hd
      (sub_mem_posTangentConeAt_of_segment_subset hseg)
    simp only [zero_sub, smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, neg_apply, innerSL_apply_apply, inner_neg_right,
      smul_neg, nsmul_eq_mul, Nat.cast_ofNat, Left.nonneg_neg_iff] at this
    linarith
  have htaylor : ‖g v - g u - D u (v - u)‖ ≤ L * ‖v - u‖ * ‖v - u‖ := by
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w ↦ g w - D u w) (f' := fun w ↦ D w - D u) (s := segment ℝ u v) (C := L * ‖v - u‖)
      (fun w hw ↦ ((hg w (hseg hw)).mono hseg).sub (D u).hasFDerivWithinAt)
      (fun w hw ↦ by
        refine (hL u hu w (hseg hw)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
        obtain ⟨t, ht, rfl⟩ := (segment_eq_image' ℝ u v ▸ hw : _)
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
      (convex_segment u v) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    have e : g v - D u v - (g u - D u u) = g v - g u - D u (v - u) := by rw [map_sub]; abel
    rwa [← e]
  have hsq : ‖v - u‖ ^ 2 ≤ c ^ 2 * ‖g v - g u‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc u hu v hv) 2
  have hsplit : g v - g u = D u (v - u) + (g v - g u - D u (v - u)) := by abel
  rw [hsplit, inner_add_right, ← hsplit]
  calc inner ℝ (y - g u) (D u (v - u)) + inner ℝ (y - g u) (g v - g u - D u (v - u))
      ≤ 0 + ‖y - g u‖ * (L * ‖v - u‖ * ‖v - u‖) :=
        add_le_add hfirst ((real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left htaylor (norm_nonneg _)))
    _ = L * ‖y - g u‖ * ‖v - u‖ ^ 2 := by ring
    _ ≤ L * ‖y - g u‖ * (c ^ 2 * ‖g v - g u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- Let `g` be a map on a convex set `S ⊆ ball u₀ r`, with a derivative `D` that is
`B`-Lipschitz on `S`, such that `‖h‖ ≤ K' ‖D u₀ h‖` and `K' B r ≤ 1 / 2`. Then
`‖v - u‖ ≤ 2 K' ‖g v - g u‖` on `S`. -/
theorem norm_sub_le_two_mul_norm_image_sub {g : G → F} {D : G → G →L[ℝ] F} {S : Set G}
    (hS : Convex ℝ S) (hg : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w) {u₀ : G} (hu₀ : u₀ ∈ S)
    {B r K' : ℝ} (hB : 0 ≤ B) (hK' : 0 ≤ K') (hL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ B * ‖v - u‖)
    (hSr : S ⊆ ball u₀ r) (hbd : ∀ h, ‖h‖ ≤ K' * ‖D u₀ h‖) (hrK : K' * B * r ≤ 1 / 2)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) : ‖v - u‖ ≤ 2 * K' * ‖g v - g u‖ := by
  have h1 := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun w ↦ g w - D u₀ w) (f' := fun w ↦ D w - D u₀) (C := B * r)
    (fun w hw ↦ (hg w hw).sub (D u₀).hasFDerivWithinAt)
    (fun w hw ↦ (hL u₀ hu₀ w hw).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact (mem_ball.1 (hSr hw)).le) hB)) hS hu hv
  have e : D u₀ (v - u) = (g v - g u) - ((g v - D u₀ v) - (g u - D u₀ u)) := by
    rw [map_sub]; abel
  have h2 : ‖D u₀ (v - u)‖ ≤ ‖g v - g u‖ + B * r * ‖v - u‖ := by
    rw [e]; exact (norm_sub_le _ _).trans (add_le_add_right h1 _)
  have h3 := hbd (v - u)
  have h4 : K' * (B * r * ‖v - u‖) ≤ 1 / 2 * ‖v - u‖ := by
    have := mul_le_mul_of_nonneg_right hrK (norm_nonneg (v - u))
    linarith [show K' * (B * r * ‖v - u‖) = K' * B * r * ‖v - u‖ by ring]
  have h5 := mul_le_mul_of_nonneg_left h2 hK'
  nlinarith

/-- Let `g` be `C²` within a convex set `s` on which derivatives are unique, at `u₀ ∈ s`, with
injective derivative within `s` at `u₀`. Then on `s ∩ ball u₀ r`, for some `r > 0`, the image
satisfies `⟪y - g u, g v - g u⟫ ≤ K ‖y - g u‖ ‖g v - g u‖²` whenever `g u` is a nearest point of
`y` among the points `g w`. -/
theorem exists_inner_sub_le_of_contDiffWithinAt [FiniteDimensional ℝ G] {s : Set G}
    (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) {g : G → F} {u₀ : G} (hu₀ : u₀ ∈ s)
    (hg : ContDiffWithinAt ℝ 2 g s u₀) (hinj : Function.Injective (fderivWithin ℝ g s u₀)) :
    ∃ r > 0, ∃ K : ℝ, ∀ y, ∀ u ∈ s ∩ ball u₀ r, (∀ w ∈ s ∩ ball u₀ r, ‖y - g u‖ ≤ ‖y - g w‖) →
      ∀ v ∈ s ∩ ball u₀ r, inner ℝ (y - g u) (g v - g u) ≤ K * ‖y - g u‖ * ‖g v - g u‖ ^ 2 := by
  obtain ⟨U, hUo, hu₀U, hgU⟩ := hg.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hu₀] at hgU
  set T := s ∩ U
  have hTu : UniqueDiffOn ℝ T := hsu.inter hUo
  have hT0 : u₀ ∈ T := ⟨hu₀, hu₀U⟩
  obtain ⟨hdiff, -, hD1⟩ := (contDiffOn_succ_iff_fderivWithin (n := 1) hTu).1 hgU
  set D := fderivWithin ℝ g T with hD
  have hDdiff : DifferentiableOn ℝ D T := hD1.differentiableOn one_ne_zero
  set D2 := fderivWithin ℝ D T
  have hD2c : ContinuousOn D2 T := hD1.continuousOn_fderivWithin hTu le_rfl
  set B := ‖D2 u₀‖ + 1
  have hB : 0 < B := by positivity
  obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.mem_nhdsWithin_iff.1
    ((hD2c u₀ hT0).norm.eventually_lt tendsto_const_nhds (lt_add_one ‖D2 u₀‖))
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.isOpen_iff.1 hUo u₀ hu₀U
  have hinj' : Function.Injective (D u₀) := by
    rwa [hD, fderivWithin_inter (hUo.mem_nhds hu₀U)]
  obtain ⟨K', hK'0, hK'⟩ :=
    (D u₀ : G →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj')
  have hK'0' : (0 : ℝ) < K' := by exact_mod_cast hK'0
  have hbd : ∀ h, ‖h‖ ≤ K' * ‖D u₀ h‖ := fun h ↦ (D u₀).bound_of_antilipschitz hK' h
  set r := min (min r₁ r₂) (1 / (2 * K' * B)) with hr
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) (by positivity)
  have hrK : (K' : ℝ) * B * r ≤ 1 / 2 := by
    have h := min_le_right (min r₁ r₂) (1 / (2 * K' * B))
    rw [← hr, le_div_iff₀ (by positivity)] at h
    linarith
  set S := s ∩ ball u₀ r
  have hSconv : Convex ℝ S := hs.inter (convex_ball u₀ r)
  have hu₀S : u₀ ∈ S := ⟨hu₀, mem_ball_self hr0⟩
  have hST : S ⊆ T := fun w hw ↦
    ⟨hw.1, hr₂U (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw.2)⟩
  have hSB : ∀ w ∈ S, ‖D2 w‖ ≤ B := fun w hw ↦
    (hr₁T ⟨ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw.2, hST hw⟩).le
  have hgS : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w := fun w hw ↦
    ((hdiff w (hST hw)).hasFDerivWithinAt).mono hST
  have hDS : ∀ w ∈ S, HasFDerivWithinAt D (D2 w) S w := fun w hw ↦
    ((hDdiff w (hST hw)).hasFDerivWithinAt).mono hST
  have hL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ B * ‖v - u‖ := fun u hu v hv ↦
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hDS hSB hSconv hu hv
  have hc : ∀ u ∈ S, ∀ v ∈ S, ‖v - u‖ ≤ (2 * K') * ‖g v - g u‖ := fun u hu v hv ↦
    norm_sub_le_two_mul_norm_image_sub hSconv hgS hu₀S hB.le hK'0'.le hL inter_subset_right
      hbd hrK hu hv
  exact ⟨r, hr0, B * (2 * K') ^ 2, fun y u hu hmin v hv ↦
    inner_sub_le_mul_norm_sq_of_isMinOn hSconv hgS hB.le hL hc hu hmin hv⟩

end InnerProduct

section Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Positive reach of an embedded compact manifold with corners.** The image of a compact
manifold with corners under a `C²` topological embedding into a proper real inner product space,
with injective derivative at every point, has positive reach. -/
theorem exists_hasUniqueNearestPoints_range [CompactSpace M] [ProperSpace F] {e : M → F}
    (he : ContMDiff I 𝓘(ℝ, F) 2 e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, F) e x)) :
    ∃ τ > 0, HasUniqueNearestPoints (range e) τ := by
  refine exists_hasUniqueNearestPoints_of_locally_inner_le (isCompact_range he.continuous) ?_
  rintro _ ⟨x₀, rfl⟩
  set φ := extChartAt I x₀
  have hu₀ : φ x₀ ∈ range I := extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)
  have hgc : ContDiffWithinAt ℝ 2 (e ∘ φ.symm) (range I) (φ x₀) := by
    have := (contMDiffAt_iff.1 (he x₀)).2
    rwa [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at this
  have hmd : MDifferentiableAt I 𝓘(ℝ, F) e x₀ := (he x₀).mdifferentiableAt (by norm_num)
  have hinj' : Function.Injective (fderivWithin ℝ (e ∘ φ.symm) (range I) (φ x₀)) := by
    have h := hinj x₀
    rwa [hmd.mfderiv, writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at h
  obtain ⟨r, hr, K, hK⟩ := exists_inner_sub_le_of_contDiffWithinAt I.convex_range I.uniqueDiffOn
    hu₀ hgc hinj'
  set O := φ.source ∩ φ ⁻¹' ball (φ x₀) r
  have hOn : O ∈ 𝓝 x₀ := inter_mem (extChartAt_source_mem_nhds x₀)
    ((continuousAt_extChartAt x₀).preimage_mem_nhds (ball_mem_nhds _ hr))
  rw [hemb.isInducing.nhds_eq_comap] at hOn
  obtain ⟨V, hV, hVO⟩ := mem_comap.1 hOn
  refine ⟨V, hV, K, ?_⟩
  rintro y _ ⟨⟨x, rfl⟩, hxV⟩ hd _ ⟨⟨x', rfl⟩, hx'V⟩
  have hxO : x ∈ O := hVO hxV
  have hx'O : x' ∈ O := hVO hx'V
  have mem : ∀ z ∈ O, φ z ∈ range I ∩ ball (φ x₀) r := fun z hz ↦
    ⟨extChartAt_target_subset_range x₀ (φ.map_source hz.1), hz.2⟩
  have eq : ∀ z ∈ O, (e ∘ φ.symm) (φ z) = e z := fun z hz ↦ by
    simp [φ.left_inv hz.1]
  have := hK y (φ x) (mem x hxO) (fun w _ ↦ ?_) (φ x') (mem x' hx'O)
  · rwa [eq x hxO, eq x' hx'O] at this
  · rw [eq x hxO, ← dist_eq_norm, ← dist_eq_norm, hd]
    exact infDist_le_dist_of_mem (mem_range_self _)

end Manifold

end

end MMP.Topology
