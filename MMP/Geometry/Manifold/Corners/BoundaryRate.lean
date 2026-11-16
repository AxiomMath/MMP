module

public import MMP.Geometry.Manifold.Corners.EuclideanQuadrant
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Nearest boundary points of a parametrised quadrant

Let `g` be a `C²` map on a piece `S = Q ∩ ball u₀ R` of the quadrant `Q = [0, ∞)^n`, with
Lipschitz derivative `D` bounded below, `‖D u h‖ ≥ m ‖h‖`. Let `z` be a point whose nearest
point among `g(S)` is `g u_z` with `u_z` in the open quadrant, and whose nearest point among
the images of the boundary points of `S` is `b = g u_b`. If `z` is close to `g(S)` compared
with its distance to `b`, and `S` is small, then `⟪z - b, D u 𝟙⟫ ≥ c ‖z - b‖` for every
`u ∈ S`, with `c = m² / (8 (Λ + 1))`, `Λ` a bound for `‖D‖`, and `𝟙 = (1, …, 1)`.

The first-order conditions at `u_b` on the faces `{u_i = 0}` through it give
`aₖ = ⟪z - b, D u_b eₖ⟫ = 0` for the coordinates `k` with `u_b k > 0`, and `aₖ ≤ 0` for the
others when `u_b` lies on two faces. On the other hand `Σ dₖ aₖ = ⟪z - b, D u_b d⟫` with
`d = u_z - u_b`, and since `z - g u_z` is normal to `g(S)` at `g u_z`, this is at least
`m² ‖d‖² / 2`. As `dₖ > 0` where `u_b k = 0`, the point `u_b` lies on exactly one face
`{u_{i₀} = 0}`, and `⟪z - b, D u_b 𝟙⟫ = a_{i₀} ≥ m² ‖d‖ / 2`.

## Main results

* `MMP.Topology.inner_sub_ge_of_isMinOn_boundary`
-/

open Set Filter Topology Metric

namespace MMP.Topology

public section

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The closed quadrant `[0, ∞)^n` is convex. -/
theorem convex_setOf_forall_apply_nonneg :
    Convex ℝ {u : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ u i} := by
  have : {u : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ u i} = ⋂ i, {u | 0 ≤ u i} := by
    ext
    simp
  rw [this]
  exact convex_iInter fun i ↦ convex_halfSpace_ge (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u i)
    ⟨fun x y ↦ rfl, fun c x ↦ rfl⟩ 0

/-- A piece of the quadrant is a neighbourhood of each of its points in the open quadrant. -/
theorem setOf_forall_apply_nonneg_inter_ball_mem_nhds {u₀ u : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hu : u ∈ ball u₀ R) (hpos : ∀ i, 0 < u i) :
    {v : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ v i} ∩ ball u₀ R ∈ 𝓝 u := by
  refine inter_mem ?_ (isOpen_ball.mem_nhds hu)
  have : {v : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < v i} ∈ 𝓝 u := by
    have : {v : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < v i} = ⋂ i, {v | 0 < v i} := by
      ext
      simp
    rw [this]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
      (PiLp.continuous_apply 2 _ i)).mem_nhds (by simpa using hpos)
  exact mem_of_superset this fun v hv i ↦ (hv i).le

/-- **First-order Taylor bound.** A map whose derivative is `L`-Lipschitz on a convex set is
approximated there by its linearisation up to `L ‖v - u‖²`. -/
theorem norm_sub_sub_apply_sub_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G} {D : E → E →L[ℝ] G} {S : Set E}
    {L : ℝ} (hS : Convex ℝ S) (hg : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w) (hL : 0 ≤ L)
    (hDL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ L * ‖v - u‖) {u v : E} (hu : u ∈ S) (hv : v ∈ S) :
    ‖g v - g u - D u (v - u)‖ ≤ L * ‖v - u‖ * ‖v - u‖ := by
  have hseg : segment ℝ u v ⊆ S := hS.segment_subset hu hv
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun w ↦ g w - D u w) (f' := fun w ↦ D w - D u) (s := segment ℝ u v)
    (C := L * ‖v - u‖)
    (fun w hw ↦ ((hg w (hseg hw)).mono hseg).sub (D u).hasFDerivWithinAt)
    (fun w hw ↦ by
      refine (hDL u hu w (hseg hw)).trans (mul_le_mul_of_nonneg_left ?_ hL)
      obtain ⟨t, ht, rfl⟩ := (segment_eq_image' ℝ u v ▸ hw : _)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
    (convex_segment u v) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  have e : g v - D u v - (g u - D u u) = g v - g u - D u (v - u) := by
    rw [map_sub]
    abel
  rwa [← e]

/-- **Interior first-order condition.** If `g u` is a nearest point to `z` among the values of
`g` on a neighbourhood of `u`, then `z - g u` is orthogonal to the derivative of `g` at `u`. -/
theorem inner_sub_apply_eq_zero_of_isMinOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → F} {D : E →L[ℝ] F} {S : Set E} {u : E} {z : F} (hS : S ∈ 𝓝 u)
    (hg : HasFDerivWithinAt g D S u) (hmin : ∀ w ∈ S, ‖z - g u‖ ≤ ‖z - g w‖) (v : E) :
    inner ℝ (z - g u) (D v) = 0 := by
  have hlm : IsLocalMin (fun w ↦ ‖z - g w‖ ^ 2) u :=
    mem_of_superset hS fun w hw ↦ pow_le_pow_left₀ (norm_nonneg _) (hmin w hw) 2
  have hfd : HasFDerivAt (fun w ↦ ‖z - g w‖ ^ 2)
      (2 • (innerSL ℝ (z - g u)).comp (0 - D)) u :=
    (((hasFDerivWithinAt_const z u S).sub hg).norm_sq).hasFDerivAt hS
  have h0 := congrArg (fun L ↦ L v) (hlm.hasFDerivAt_eq_zero hfd)
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply, zero_sub,
    innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at h0
  rwa [neg_apply, inner_neg_right, neg_eq_zero] at h0

/-- **One-sided first-order condition.** If `g u` is a nearest point to `z` among the values of
`g` on a convex set `T ∋ u`, then `⟪z - g u, D (w - u)⟫ ≤ 0` for `w ∈ T`. -/
theorem inner_sub_apply_sub_nonpos_of_isMinOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → F} {D : E →L[ℝ] F} {T : Set E} {u w : E} {z : F}
    (hT : Convex ℝ T) (hg : HasFDerivWithinAt g D T u) (hu : u ∈ T) (hw : w ∈ T)
    (hmin : ∀ v ∈ T, ‖z - g u‖ ≤ ‖z - g v‖) :
    inner ℝ (z - g u) (D (w - u)) ≤ 0 := by
  have hlm : IsLocalMinOn (fun v ↦ ‖z - g v‖ ^ 2) T u :=
    IsMinOn.isLocalMinOn fun v hv ↦ pow_le_pow_left₀ (norm_nonneg _) (hmin v hv) 2
  have hfd : HasFDerivWithinAt (fun v ↦ ‖z - g v‖ ^ 2)
      (2 • (innerSL ℝ (z - g u)).comp (0 - D)) T u :=
    ((hasFDerivWithinAt_const z u T).sub hg).norm_sq
  have := hlm.hasFDerivWithinAt_nonneg hfd
    (sub_mem_posTangentConeAt_of_segment_subset (hT.segment_subset hu hw))
  simp only [zero_sub, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
    innerSL_apply_apply, inner_neg_right, smul_neg, nsmul_eq_mul, Nat.cast_ofNat,
    Left.nonneg_neg_iff] at this
  linarith

/-- If `z - x` is orthogonal to `B d`, `x - y` is `A d` up to `L ‖d‖²`, `A` is `L ‖d‖`-close to
`B` and bounded below by `m`, and `L ‖d‖` and `‖z - x‖` are small, then
`m² ‖d‖² / 2 ≤ ⟪z - y, A d⟫`. -/
theorem sq_div_two_mul_sq_le_inner {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] F} {d : E} {x y z : F} {L m : ℝ} (hm : 0 ≤ m)
    (hperp : inner ℝ (z - x) (B d) = 0) (htaylor : ‖x - y - A d‖ ≤ L * ‖d‖ * ‖d‖)
    (hAB : ‖A - B‖ ≤ L * ‖d‖) (hAm : m * ‖d‖ ≤ ‖A d‖) (hLd : L * ‖d‖ ≤ m / 8)
    (hnL : 4 * ‖z - x‖ * L ≤ m ^ 2) :
    m ^ 2 / 2 * ‖d‖ ^ 2 ≤ inner ℝ (z - y) (A d) := by
  have h1 : inner ℝ (z - x) (A d) = inner ℝ (z - x) ((A - B) d) := by
    rw [sub_apply, inner_sub_right, hperp, sub_zero]
  have h2 : |inner ℝ (z - x) ((A - B) d)| ≤ ‖z - x‖ * (L * ‖d‖ * ‖d‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (((A - B).le_opNorm d).trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg _)))
      (norm_nonneg _))
  have h3 : |inner ℝ (x - y - A d) (A d)| ≤ L * ‖d‖ * ‖d‖ * ‖A d‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right htaylor (norm_nonneg _))
  have h4 : inner ℝ (z - y) (A d) =
      inner ℝ (z - x) (A d) + ‖A d‖ ^ 2 + inner ℝ (x - y - A d) (A d) := by
    rw [show z - y = z - x + (A d + (x - y - A d)) by abel, inner_add_left, inner_add_left,
      real_inner_self_eq_norm_sq]
    ring
  have hd0 := norm_nonneg d
  have hX0 := norm_nonneg (A d)
  have h5 : ‖z - x‖ * (L * ‖d‖ * ‖d‖) ≤ m ^ 2 / 4 * ‖d‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hnL (sq_nonneg ‖d‖)]
  have h6 : L * ‖d‖ * ‖d‖ * ‖A d‖ ≤ m / 8 * ‖d‖ * ‖A d‖ := by gcongr
  have h7 : m / 8 * ‖d‖ * ‖A d‖ ≤ ‖A d‖ ^ 2 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hAm hX0]
  have h8 : m ^ 2 * ‖d‖ ^ 2 ≤ ‖A d‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hm hd0) hAm 2
  rw [h4, h1]
  linarith [(abs_le.1 h2).1, (abs_le.1 h3).1, mul_nonneg (sq_nonneg m) (sq_nonneg ‖d‖)]

/-- If `z` is at least twice as far from `y` as from `x`, and `x - y` is `A d` up to
`L ‖d‖²` with `‖A‖ ≤ Λ` and `L ‖d‖ ≤ 1`, then `‖z - y‖ ≤ 2 (Λ + 1) ‖d‖`. -/
theorem norm_sub_le_of_norm_sub_sub_apply_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : E →L[ℝ] F} {d : E} {x y z : F} {L Λ : ℝ}
    (hn : ‖z - x‖ ≤ ‖z - y‖ / 2) (hA : ‖A‖ ≤ Λ) (ht : ‖x - y - A d‖ ≤ L * ‖d‖ * ‖d‖)
    (hLd : L * ‖d‖ ≤ 1) : ‖z - y‖ ≤ 2 * (Λ + 1) * ‖d‖ := by
  have h1 : ‖x - y‖ ≤ ‖A d‖ + L * ‖d‖ * ‖d‖ := by
    rw [show x - y = A d + (x - y - A d) by abel]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ht)
  have h2 : ‖A d‖ ≤ Λ * ‖d‖ := (A.le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h3 : L * ‖d‖ * ‖d‖ ≤ ‖d‖ := mul_le_of_le_one_left (norm_nonneg d) hLd
  linarith [norm_sub_le_norm_sub_add_norm_sub z x y]

/-- From `c x² ≤ y a` with `0 < y ≤ x` and `0 ≤ c`, conclude `c x ≤ a`. -/
theorem mul_le_of_mul_sq_le {c x y a : ℝ} (hc : 0 ≤ c) (hy : 0 < y) (hyx : y ≤ x)
    (h : c * x ^ 2 ≤ y * a) : c * x ≤ a := by
  have ha : 0 ≤ a := by
    by_contra! ha
    linarith [mul_neg_of_pos_of_neg hy ha, mul_nonneg hc (sq_nonneg x)]
  exact le_of_mul_le_mul_left (by nlinarith [mul_le_mul_of_nonneg_right hyx ha]) (hy.trans_le hyx)

/-- A point `ub` of a piece `S` of the quadrant can be moved along each coordinate axis by less
than some `δ > 0`, staying in `S` as long as that coordinate stays nonnegative. -/
theorem exists_add_smul_single_mem {S : Set (EuclideanSpace ℝ (Fin n))}
    {u₀ ub : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hS : S = {u | ∀ i, 0 ≤ u i} ∩ ball u₀ R)
    (hub : ub ∈ S) : ∃ δ > 0, ∀ k (t : ℝ), |t| < δ → 0 ≤ ub k + t →
      ub + t • EuclideanSpace.single k (1 : ℝ) ∈ S := by
  subst hS
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 isOpen_ball ub hub.2
  refine ⟨δ, hδ, fun k t ht hk ↦ ⟨fun i ↦ ?_, hδb ?_⟩⟩
  · rcases eq_or_ne i k with rfl | hik
    · simpa using hk
    · simpa [hik] using hub.1 i
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      show ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 by simp, mul_one, Real.norm_eq_abs]
    exact ht

/-- If `ub + t eₖ ∈ S` lies on a face `{u_i = 0}` through `ub` with `i ≠ k`, the first-order
condition on that face gives `t f eₖ ≤ 0`. -/
theorem mul_apply_single_nonpos {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {ub : EuclideanSpace ℝ (Fin n)}
    (hface : ∀ i, ub i = 0 → ∀ w ∈ S, w i = 0 → f (w - ub) ≤ 0) {k i : Fin n} {t : ℝ}
    (ht : ub + t • EuclideanSpace.single k (1 : ℝ) ∈ S) (hi : ub i = 0) (hik : i ≠ k) :
    t * f (EuclideanSpace.single k 1) ≤ 0 := by
  have := hface i hi _ ht (by simp [hi, hik])
  rwa [add_sub_cancel_left, map_smul, smul_eq_mul] at this

/-- The first-order conditions on a face `{u_i = 0}` through `ub` give `f eₖ ≤ 0` for `k ≠ i`. -/
theorem apply_single_nonpos {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {u₀ ub : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hS : S = {u | ∀ i, 0 ≤ u i} ∩ ball u₀ R) (hub : ub ∈ S)
    (hface : ∀ i, ub i = 0 → ∀ w ∈ S, w i = 0 → f (w - ub) ≤ 0) {k i : Fin n} (hi : ub i = 0)
    (hik : i ≠ k) : f (EuclideanSpace.single k 1) ≤ 0 := by
  obtain ⟨δ, hδ, hmem⟩ := exists_add_smul_single_mem hS hub
  have hk : 0 ≤ ub k := by
    rw [hS] at hub
    exact hub.1 k
  have := mul_apply_single_nonpos hface
    (hmem k (δ / 2) (by rw [abs_of_pos (half_pos hδ)]; linarith) (by linarith)) hi hik
  nlinarith

/-- The first-order conditions on a face `{u_i = 0}` through `ub` give `f eₖ = 0` when
`0 < ub k`. -/
theorem apply_single_eq_zero_of_pos {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {u₀ ub : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hS : S = {u | ∀ i, 0 ≤ u i} ∩ ball u₀ R) (hub : ub ∈ S)
    (hface : ∀ i, ub i = 0 → ∀ w ∈ S, w i = 0 → f (w - ub) ≤ 0) {i₀ k : Fin n}
    (hi₀ : ub i₀ = 0) (hk : 0 < ub k) : f (EuclideanSpace.single k 1) = 0 := by
  obtain ⟨δ, hδ, hmem⟩ := exists_add_smul_single_mem hS hub
  have hik : i₀ ≠ k := by
    rintro rfl
    linarith
  obtain ⟨t, ht0, htδ, htk⟩ : ∃ t, 0 < t ∧ t < δ ∧ t ≤ ub k / 2 :=
    ⟨min (δ / 2) (ub k / 2), lt_min (half_pos hδ) (half_pos hk),
      (min_le_left _ _).trans_lt (by linarith), min_le_right _ _⟩
  have h1 := mul_apply_single_nonpos hface
    (hmem k (-t) (by rwa [abs_neg, abs_of_pos ht0]) (by linarith)) hi₀ hik
  refine le_antisymm (apply_single_nonpos hS hub hface hi₀ hik) ?_
  nlinarith

/-- **First-order conditions in coordinates.** Let `ub` lie on the face `{u_{i₀} = 0}` of a
piece `S` of the quadrant, with `f (w - ub) ≤ 0` for every `w ∈ S` on a face through `ub`. If
`f d > 0` for some `d` with `d k > 0` whenever `ub k = 0`, then `f v = v_{i₀} f e_{i₀}`. -/
theorem apply_eq_mul_apply_single_of_isMinOn_faces {S : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {u₀ ub d : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hS : S = {u | ∀ i, 0 ≤ u i} ∩ ball u₀ R) (hub : ub ∈ S) {i₀ : Fin n} (hi₀ : ub i₀ = 0)
    (hface : ∀ i, ub i = 0 → ∀ w ∈ S, w i = 0 → f (w - ub) ≤ 0)
    (hd : ∀ k, ub k = 0 → 0 < d k) (hfd : 0 < f d) (v : EuclideanSpace ℝ (Fin n)) :
    f v = v i₀ * f (EuclideanSpace.single i₀ 1) := by
  have hsum : ∀ v : EuclideanSpace ℝ (Fin n), v = ∑ k, v k • EuclideanSpace.single k (1 : ℝ) := by
    intro v
    ext i
    simp [Pi.single_apply]
  have hnn : ∀ i, 0 ≤ ub i := by
    rw [hS] at hub
    exact hub.1
  have hsingle : ∀ j, ub j = 0 → j = i₀ := by
    by_contra! hcon
    obtain ⟨j, hj, hji⟩ := hcon
    refine hfd.not_ge ?_
    rw [hsum d, map_sum]
    refine Finset.sum_nonpos fun k _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    rcases (hnn k).lt_or_eq with hk | hk
    · rw [apply_single_eq_zero_of_pos hS hub hface hi₀ hk, mul_zero]
    · obtain ⟨i, hi, hik⟩ : ∃ i, ub i = 0 ∧ i ≠ k := by
        by_cases hki : k = i₀
        · exact ⟨j, hj, hki ▸ hji⟩
        · exact ⟨i₀, hi₀, Ne.symm hki⟩
      exact mul_nonpos_of_nonneg_of_nonpos (hd k hk.symm).le
        (apply_single_nonpos hS hub hface hi hik)
  have hother : ∀ k, k ≠ i₀ → f (EuclideanSpace.single k 1) = 0 := fun k hk ↦
    apply_single_eq_zero_of_pos hS hub hface hi₀
      ((hnn k).lt_of_ne fun h ↦ hk (hsingle k h.symm))
  conv_lhs => rw [hsum v]
  rw [map_sum, Finset.sum_eq_single i₀ (fun k _ hk ↦ by rw [map_smul, hother k hk, smul_zero])
    (by simp), map_smul, smul_eq_mul]

/-- If `2 c ‖w‖ ≤ ⟪w, A v⟫` and `‖A' - A‖ ‖v‖ ≤ c`, then `c ‖w‖ ≤ ⟪w, A' v⟫`. -/
theorem le_inner_apply_of_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A A' : E →L[ℝ] F} {w : F} {v : E} {c : ℝ} (h : 2 * c * ‖w‖ ≤ inner ℝ w (A v))
    (hAA : ‖A' - A‖ * ‖v‖ ≤ c) : c * ‖w‖ ≤ inner ℝ w (A' v) := by
  have h1 : |inner ℝ w ((A' - A) v)| ≤ ‖w‖ * (‖A' - A‖ * ‖v‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((A' - A).le_opNorm v) (norm_nonneg _))
  have h2 : inner ℝ w (A' v) = inner ℝ w (A v) + inner ℝ w ((A' - A) v) := by
    rw [sub_apply, inner_sub_right]
    ring
  linarith [(abs_le.1 h1).1, mul_le_mul_of_nonneg_left hAA (norm_nonneg w)]

/-- **Nearest boundary points move away along the diagonal.** If the nearest point to `z` in
`g(S)` is `g uz` with `uz` in the open quadrant, the nearest point among the images of boundary
points of `S` is `g ub`, and `‖z - g uz‖ ≤ ‖z - g ub‖ / 2`, then
`m² / (8 (Λ + 1)) ‖z - g ub‖ ≤ ⟪z - g ub, D u 𝟙⟫` for every `u ∈ S`. -/
theorem inner_sub_ge_of_isMinOn_boundary {g : EuclideanSpace ℝ (Fin n) → F}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] F}
    {S : Set (EuclideanSpace ℝ (Fin n))} {u₀ : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hS : S = {u | ∀ i, 0 ≤ u i} ∩ ball u₀ R)
    (hg : ∀ w ∈ S, HasFDerivWithinAt g (D w) S w) {L m Λ r : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hΛ : 0 ≤ Λ) (hDL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ L * ‖v - u‖)
    (hDm : ∀ u ∈ S, ∀ h, m * ‖h‖ ≤ ‖D u h‖) (hDΛ : ∀ u ∈ S, ‖D u‖ ≤ Λ)
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, ‖v - u‖ ≤ r) (hr1 : 8 * r * L ≤ m) (hr2 : r * L ≤ 1)
    (hr3 : 16 * (Λ + 1) * r * L * ‖quadrantDiagonal n‖ ≤ m ^ 2)
    {z : F} {uz ub : EuclideanSpace ℝ (Fin n)} (huz : uz ∈ S) (huzpos : ∀ i, 0 < uz i)
    (hmin_z : ∀ w ∈ S, ‖z - g uz‖ ≤ ‖z - g w‖) (hub : ub ∈ S) {i₀ : Fin n} (hi₀ : ub i₀ = 0)
    (hmin_b : ∀ w ∈ S, (∃ i, w i = 0) → ‖z - g ub‖ ≤ ‖z - g w‖)
    (hn : ‖z - g uz‖ ≤ ‖z - g ub‖ / 2) (hnL : 4 * ‖z - g uz‖ * L ≤ m ^ 2) :
    ∀ u ∈ S, m ^ 2 / (8 * (Λ + 1)) * ‖z - g ub‖ ≤
      inner ℝ (z - g ub) (D u (quadrantDiagonal n)) := by
  set d := uz - ub with hd
  have hSc : Convex ℝ S := hS ▸ convex_setOf_forall_apply_nonneg.inter (convex_ball _ _)
  have htaylor : ‖g uz - g ub - D ub d‖ ≤ L * ‖d‖ * ‖d‖ :=
    norm_sub_sub_apply_sub_le hSc hg hL.le hDL hub huz
  have hdle : ‖d‖ ≤ r := hdiam ub hub uz huz
  have hSn : S ∈ 𝓝 uz := by
    rw [hS] at huz ⊢
    exact setOf_forall_apply_nonneg_inter_ball_mem_nhds huz.2 huzpos
  have hlow : m ^ 2 / 2 * ‖d‖ ^ 2 ≤ inner ℝ (z - g ub) (D ub d) :=
    sq_div_two_mul_sq_le_inner hm.le (inner_sub_apply_eq_zero_of_isMinOn hSn (hg uz huz) hmin_z d)
      htaylor ((norm_sub_rev _ _).trans_le (hDL ub hub uz huz)) (hDm ub hub d)
      (by nlinarith [mul_le_mul_of_nonneg_left hdle hL.le]) hnL
  have hdpos : ∀ k, ub k = 0 → 0 < d k := fun k hk ↦ by
    simp only [hd, PiLp.sub_apply, hk, sub_zero]
    exact huzpos k
  have hdi : d i₀ ≤ ‖d‖ := (le_abs_self _).trans (PiLp.norm_apply_le d i₀)
  have hdne : 0 < ‖d‖ := (hdpos i₀ hi₀).trans_le hdi
  have hface : ∀ i, ub i = 0 → ∀ w ∈ S, w i = 0 →
      ((innerSL ℝ (z - g ub)).comp (D ub)) (w - ub) ≤ 0 := fun i hi w hw hwi ↦ by
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply] using
      inner_sub_apply_sub_nonpos_of_isMinOn (hSc.inter (convex_hyperplane
        (f := fun u : EuclideanSpace ℝ (Fin n) ↦ u i) ⟨fun x y ↦ rfl, fun c x ↦ rfl⟩ 0))
        ((hg ub hub).mono inter_subset_left) ⟨hub, hi⟩ ⟨hw, hwi⟩
        fun v hv ↦ hmin_b v hv.1 ⟨i, hv.2⟩
  have hsum : ∀ v, inner ℝ (z - g ub) (D ub v) =
      v i₀ * inner ℝ (z - g ub) (D ub (EuclideanSpace.single i₀ 1)) := fun v ↦ by
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply] using
      apply_eq_mul_apply_single_of_isMinOn_faces hS hub hi₀ hface hdpos
        (by simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
          using (by positivity : 0 < m ^ 2 / 2 * ‖d‖ ^ 2).trans_le hlow) v
  set a := inner ℝ (z - g ub) (D ub (EuclideanSpace.single i₀ 1))
  have hai : m ^ 2 / 2 * ‖d‖ ≤ a :=
    mul_le_of_mul_sq_le (by positivity) (hdpos i₀ hi₀) hdi (hlow.trans_eq (hsum d))
  have hzb : ‖z - g ub‖ ≤ 2 * (Λ + 1) * ‖d‖ := norm_sub_le_of_norm_sub_sub_apply_le hn
    (hDΛ ub hub) htaylor (by nlinarith [mul_le_mul_of_nonneg_left hdle hL.le])
  intro u hu
  have hΛ1 : 0 < Λ + 1 := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hdiam ub hub ub hub)
  refine le_inner_apply_of_norm_sub_le (A := D ub) ?_ ?_
  · have h4 : m ^ 2 / (4 * (Λ + 1)) = 2 * (m ^ 2 / (8 * (Λ + 1))) := by
      field_simp
      ring
    have h1 : inner ℝ (z - g ub) (D ub (quadrantDiagonal n)) = a := (hsum _).trans (by simp)
    rw [← h4, h1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hzb (sq_nonneg m), mul_le_mul_of_nonneg_left hai hΛ1.le]
  · rw [le_div_iff₀ (by positivity)]
    have := (hDL ub hub u hu).trans (mul_le_mul_of_nonneg_left (hdiam ub hub u hu) hL.le)
    nlinarith [mul_le_mul_of_nonneg_right this
      (by positivity : (0 : ℝ) ≤ ‖quadrantDiagonal n‖ * (8 * (Λ + 1))),
      (by positivity : 0 ≤ (Λ + 1) * r * L * ‖quadrantDiagonal n‖)]

/-- **Perturbed antilipschitz bound.** If `‖h‖ ≤ K ‖A h‖` for all `h` and `‖A' - A‖ ≤ ε` with
`K ε ≤ 1 / 2`, then `‖h‖ / (2 K) ≤ ‖A' h‖`. -/
theorem div_mul_norm_le_norm_apply_of_norm_sub_le {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {A A' : E →L[ℝ] G} {K ε : ℝ}
    (hK : 0 < K) (hA : ∀ h, ‖h‖ ≤ K * ‖A h‖) (hAA : ‖A' - A‖ ≤ ε) (hKε : K * ε ≤ 1 / 2)
    (h : E) : 1 / (2 * K) * ‖h‖ ≤ ‖A' h‖ := by
  have h2 : ‖(A' - A) h‖ ≤ ε * ‖h‖ :=
    ((A' - A).le_opNorm h).trans (mul_le_mul_of_nonneg_right hAA (norm_nonneg _))
  have h3 : ‖A h‖ ≤ ‖A' h‖ + ‖(A' - A) h‖ := by
    rw [sub_apply, ← norm_neg (A' h - A h), neg_sub]
    exact norm_le_insert' _ _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [hA h, mul_le_mul_of_nonneg_left h3 hK.le, mul_le_mul_of_nonneg_left h2 hK.le,
    mul_le_mul_of_nonneg_right hKε (norm_nonneg h)]

/-- **Uniform bounds for a `C²` map on a small convex piece.** For `g` that is `C²` within a
convex set `s` with unique derivatives at `u₀`, with injective derivative there, the derivative
`D = fderivWithin ℝ g s` is, on `s ∩ ball u₀ r₀`, a derivative of `g` within that set,
`L`-Lipschitz, bounded by `Λ`, and bounded below: `‖D u h‖ ≥ m ‖h‖`. -/
theorem exists_bounds_of_contDiffWithinAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {s : Set G} (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) {g : G → F}
    {u₀ : G} (hu₀ : u₀ ∈ s) (hg : ContDiffWithinAt ℝ 2 g s u₀)
    (hinj : Function.Injective (fderivWithin ℝ g s u₀)) :
    ∃ r₀ > 0, ∃ L > 0, ∃ m > 0, ∃ Λ ≥ 0,
      (∀ w ∈ s ∩ ball u₀ r₀, HasFDerivWithinAt g (fderivWithin ℝ g s w) (s ∩ ball u₀ r₀) w) ∧
      (∀ u ∈ s ∩ ball u₀ r₀, ∀ v ∈ s ∩ ball u₀ r₀,
        ‖fderivWithin ℝ g s v - fderivWithin ℝ g s u‖ ≤ L * ‖v - u‖) ∧
      (∀ u ∈ s ∩ ball u₀ r₀, ∀ h, m * ‖h‖ ≤ ‖fderivWithin ℝ g s u h‖) ∧
      (∀ u ∈ s ∩ ball u₀ r₀, ‖fderivWithin ℝ g s u‖ ≤ Λ) := by
  obtain ⟨U, hUo, hu₀U, hgU⟩ := hg.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem hu₀] at hgU
  set T := s ∩ U with hT
  have hTu : UniqueDiffOn ℝ T := hsu.inter hUo
  obtain ⟨hdiff, -, hD1⟩ := (contDiffOn_succ_iff_fderivWithin (n := 1) hTu).1 hgU
  set D := fderivWithin ℝ g T with hD
  have hDeq : ∀ w ∈ T, fderivWithin ℝ g s w = D w := fun w hw ↦ by
    rw [hD, hT, fderivWithin_inter (hUo.mem_nhds hw.2)]
  have hDdiff : DifferentiableOn ℝ D T := hD1.differentiableOn one_ne_zero
  set D2 := fderivWithin ℝ D T with hD2
  have hD2c : ContinuousOn D2 T := hD1.continuousOn_fderivWithin hTu le_rfl
  set B := ‖D2 u₀‖ + 1 with hBdef
  have hB : 0 < B := by positivity
  have hT0 : u₀ ∈ T := ⟨hu₀, hu₀U⟩
  obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.mem_nhdsWithin_iff.1
    ((hD2c u₀ hT0).norm.eventually_lt tendsto_const_nhds (lt_add_one ‖D2 u₀‖))
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.isOpen_iff.1 hUo u₀ hu₀U
  have hinj' : Function.Injective (D u₀) := by rw [← hDeq u₀ hT0]; exact hinj
  obtain ⟨K', hK'0, hK'⟩ :=
    (D u₀ : G →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj')
  have hK'0' : (0 : ℝ) < K' := by exact_mod_cast hK'0
  set r := min (min r₁ r₂) (1 / (2 * K' * B)) with hr
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) (by positivity)
  have hrK : (K' : ℝ) * B * r ≤ 1 / 2 := by
    have h := min_le_right (min r₁ r₂) (1 / (2 * K' * B))
    rw [← hr, le_div_iff₀ (by positivity)] at h
    linarith
  set S := s ∩ ball u₀ r with hS
  have hST : S ⊆ T := fun w hw ↦
    ⟨hw.1, hr₂U (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw.2)⟩
  have hSB : ∀ w ∈ S, ‖D2 w‖ ≤ B := fun w hw ↦
    (hr₁T ⟨ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw.2, hST hw⟩).le
  have hL : ∀ u ∈ S, ∀ v ∈ S, ‖D v - D u‖ ≤ B * ‖v - u‖ := fun u hu v hv ↦
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw ↦ ((hDdiff w (hST hw)).hasFDerivWithinAt).mono hST) hSB
      (hs.inter (convex_ball u₀ r)) hu hv
  have hDu : ∀ u ∈ S, ‖D u - D u₀‖ ≤ B * r := fun u hu ↦
    (hL u₀ ⟨hu₀, mem_ball_self hr0⟩ u hu).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact (mem_ball.1 hu.2).le) hB.le)
  refine ⟨r, hr0, B, hB, 1 / (2 * K'), by positivity, ‖D u₀‖ + B * r, by positivity,
    fun w hw ↦ ?_, fun u hu v hv ↦ ?_, fun u hu h ↦ ?_, fun u hu ↦ ?_⟩
  · rw [hDeq w (hST hw)]
    exact ((hdiff w (hST hw)).hasFDerivWithinAt).mono hST
  · rw [hDeq u (hST hu), hDeq v (hST hv)]
    exact hL u hu v hv
  · rw [hDeq u (hST hu)]
    exact div_mul_norm_le_norm_apply_of_norm_sub_le hK'0'
      (fun h ↦ (D u₀).bound_of_antilipschitz hK' h) (hDu u hu) (by linarith) h
  · rw [hDeq u (hST hu)]
    linarith [norm_le_insert' (D u) (D u₀), hDu u hu]

end

end MMP.Topology
