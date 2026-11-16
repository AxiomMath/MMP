module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The local straightening of an immersion

Let `g : E' → E` be continuously complex differentiable near `z₀`, with injective derivative
`D = g'(z₀)`, and `K : F → E` complex linear and injective with image complementary to that of
`D`. Then `G (z, w) = g z + K w` has the invertible derivative `D ⊕ K` at `(z₀, 0)`, so it is a
local homeomorphism there (inverse function theorem), and for `z` near `z₀` the image of `g'(z)`
is still complementary to that of `K`. The file also constructs a radial homeomorphism of a real
normed space onto its open unit ball which is the identity on the ball of radius `1/2`.

## Main definitions

* `MMP.radialShrink`: a continuous injection of a normed space into its open unit ball which is
  the identity on the ball of radius `1/2`.
* `MMP.radialGrow`: the inverse of `MMP.radialShrink` on the open unit ball.

## Main results

* `MMP.bijective_coprod_iff`: `D.coprod K` is bijective exactly when `D`, `K` are injective with
  complementary images.
* `MMP.eventually_isCompl_range_fderiv`: complementarity persists near `z₀`.
* `MMP.hasStrictFDerivAt_add_comp`: the strict derivative of `G` at `(z₀, w₀)` is `D ⊕ K`.
* `MMP.isOpenEmbedding_radialShrink`: `MMP.radialShrink` is an open embedding.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace MMP

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `D.coprod K` is bijective exactly when `D` and `K` are injective with complementary images. -/
theorem bijective_coprod_iff (D : E' →L[ℂ] E) (K : F →L[ℂ] E) :
    Function.Bijective (D.coprod K) ↔ Function.Injective D ∧ Function.Injective K ∧
      IsCompl (LinearMap.range (D : E' →ₗ[ℂ] E)) (LinearMap.range (K : F →ₗ[ℂ] E)) := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun a a' h ↦ ?_, fun b b' h ↦ ?_, ⟨?_, ?_⟩⟩
    · exact congrArg Prod.fst (@hi (a, 0) (a', 0) (by simp [h]))
    · exact congrArg Prod.snd (@hi (0, b) (0, b') (by simp [h]))
    · rw [Submodule.disjoint_def]
      rintro v ⟨a, rfl⟩ ⟨b, hb⟩
      have ha : a = 0 := congrArg Prod.fst (@hi (a, -b) 0 (by
        simp only [ContinuousLinearMap.coprod_apply, map_neg, map_zero]
        rw [show K b = D a from hb, add_neg_cancel]))
      simp [ha]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      obtain ⟨⟨a, b⟩, hab⟩ := hs v
      rw [← hab]
      exact Submodule.add_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩
  · rintro ⟨hD, hK, hc⟩
    refine ⟨fun p q h ↦ ?_, fun v ↦ ?_⟩
    · have h' : D (p.1 - q.1) = K (q.2 - p.2) := by
        simp only [ContinuousLinearMap.coprod_apply] at h
        rw [map_sub, map_sub]
        linear_combination (norm := abel_nf) h
      have h0 : D (p.1 - q.1) = 0 :=
        (Submodule.disjoint_def.1 hc.disjoint) _ ⟨_, rfl⟩ (h' ▸ ⟨_, rfl⟩)
      exact Prod.ext (sub_eq_zero.1 (hD (h0.trans (map_zero D).symm)))
        (sub_eq_zero.1 (hK ((h'.symm.trans h0).trans (map_zero K).symm))).symm
    · have hv : v ∈ LinearMap.range (D : E' →ₗ[ℂ] E) ⊔ LinearMap.range (K : F →ₗ[ℂ] E) :=
        hc.codisjoint.eq_top ▸ Submodule.mem_top
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.1 hv
      exact ⟨(a, b), hab⟩

/-- The strict derivative of `(z, w) ↦ g z + K w` at `(z₀, w₀)` is `g'(z₀) ⊕ K`. -/
theorem hasStrictFDerivAt_add_comp {g : E' → E} {z₀ : E'} (hg : ContDiffAt ℂ 1 g z₀)
    (K : F →L[ℂ] E) (w₀ : F) :
    HasStrictFDerivAt (fun p : E' × F ↦ g p.1 + K p.2) ((fderiv ℂ g z₀).coprod K)
      (z₀, w₀) := by
  have h1 : HasStrictFDerivAt (fun p : E' × F ↦ g p.1)
      ((fderiv ℂ g z₀).comp (ContinuousLinearMap.fst ℂ E' F)) (z₀, w₀) :=
    (hg.hasStrictFDerivAt one_ne_zero).comp (z₀, w₀) (hasStrictFDerivAt_fst)
  have h2 : HasStrictFDerivAt (fun p : E' × F ↦ K p.2)
      (K.comp (ContinuousLinearMap.snd ℂ E' F)) (z₀, w₀) :=
    K.hasStrictFDerivAt.comp (z₀, w₀) hasStrictFDerivAt_snd
  exact h1.add h2

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] [FiniteDimensional ℂ F]

/-- **Complementarity persists.** If `g` is `C¹` at `z₀` with `g'(z₀)` injective and image
complementary to that of the injective `K`, then the same holds for `g'(z)`, `z` near `z₀`. -/
theorem eventually_isCompl_range_fderiv {g : E' → E} {z₀ : E'} (hg : ContDiffAt ℂ 1 g z₀)
    (K : F →L[ℂ] E) (hD : Function.Injective (fderiv ℂ g z₀)) (hK : Function.Injective K)
    (hc : IsCompl (LinearMap.range (fderiv ℂ g z₀ : E' →ₗ[ℂ] E))
      (LinearMap.range (K : F →ₗ[ℂ] E))) :
    ∀ᶠ z in 𝓝 z₀, Function.Injective (fderiv ℂ g z) ∧
      IsCompl (LinearMap.range (fderiv ℂ g z : E' →ₗ[ℂ] E)) (LinearMap.range (K : F →ₗ[ℂ] E)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace (E' × F) := FiniteDimensional.complete ℂ (E' × F)
  have hcont : ContinuousAt (fun z ↦ (fderiv ℂ g z).coprod K) z₀ := by
    rw [show (fun z ↦ (fderiv ℂ g z).coprod K) = fun z ↦ (fderiv ℂ g z).comp
        (ContinuousLinearMap.fst ℂ E' F) + K.comp (ContinuousLinearMap.snd ℂ E' F) from
      funext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ rfl]
    exact ((hg.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_comp continuousAt_const).add
      continuousAt_const
  have hbij := (bijective_coprod_iff _ K).2 ⟨hD, hK, hc⟩
  set A₀ : (E' × F) ≃L[ℂ] E := ContinuousLinearEquiv.ofBijective ((fderiv ℂ g z₀).coprod K)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hmem : (fderiv ℂ g z₀).coprod K ∈
      range (ContinuousLinearEquiv.toContinuousLinearMap : ((E' × F) ≃L[ℂ] E) → _) :=
    ⟨A₀, ContinuousLinearMap.ext fun _ ↦ rfl⟩
  filter_upwards [hcont.preimage_mem_nhds
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℂ) (E := E' × F) (F := E)).mem_nhds hmem)]
    with z ⟨A, hA⟩
  have hb : Function.Bijective ((fderiv ℂ g z).coprod K) := by
    rw [← show (A : E' × F →L[ℂ] E) = (fderiv ℂ g z).coprod K from hA]
    exact A.bijective
  exact ((bijective_coprod_iff _ K).1 hb).imp_right And.right

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial factor of `radialShrink`: with `m = max t (1/2)`, the value `(4m - 1)/(4m²)`; it is
`1` on `[0, 1/2]`, and `t ↦ t · radialFactor t` is `t` on `[0, 1/2]` and `1 - 1/(4t)` beyond. -/
def radialFactor (t : ℝ) : ℝ := (4 * max t (1 / 2) - 1) / (4 * max t (1 / 2) ^ 2)

/-- `radialFactor` is continuous. -/
lemma continuous_radialFactor : Continuous radialFactor := by
  have hm : Continuous fun t : ℝ ↦ max t (1 / 2) := continuous_id.max continuous_const
  refine ((continuous_const.mul hm).sub continuous_const).div
    (continuous_const.mul (hm.pow 2)) fun t ↦ ?_
  have : (0 : ℝ) < max t (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  positivity

/-- `radialFactor t = 1` for `t ≤ 1/2`. -/
lemma radialFactor_of_le {t : ℝ} (ht : t ≤ 1 / 2) : radialFactor t = 1 := by
  rw [radialFactor, max_eq_right ht]
  norm_num

/-- `radialFactor` is positive. -/
lemma radialFactor_pos (t : ℝ) : 0 < radialFactor t := by
  have h : (1 / 2 : ℝ) ≤ max t (1 / 2) := le_max_right _ _
  unfold radialFactor
  apply div_pos <;> nlinarith

/-- For `1/2 ≤ t`, `t · radialFactor t = 1 - 1/(4t)`. -/
lemma mul_radialFactor_of_le {t : ℝ} (ht : 1 / 2 ≤ t) : t * radialFactor t = 1 - 1 / (4 * t) := by
  rw [radialFactor, max_eq_left ht]
  have : t ≠ 0 := by positivity
  field_simp

/-- `t · radialFactor t < 1` for every `t`. -/
lemma mul_radialFactor_lt_one (t : ℝ) : t * radialFactor t < 1 := by
  rcases le_or_gt t (1 / 2) with h | h
  · rw [radialFactor_of_le h]
    linarith
  · rw [mul_radialFactor_of_le h.le]
    have : 0 < 1 / (4 * t) := by positivity
    linarith

/-- `t ↦ t · radialFactor t` is injective on `[0, ∞)`. -/
lemma mul_radialFactor_injOn : InjOn (fun t : ℝ ↦ t * radialFactor t) (Ici 0) := by
  intro a ha b hb hab
  simp only at hab
  rcases le_or_gt a (1 / 2) with h₁ | h₁ <;> rcases le_or_gt b (1 / 2) with h₂ | h₂
  · rwa [radialFactor_of_le h₁, radialFactor_of_le h₂, mul_one, mul_one] at hab
  · rw [radialFactor_of_le h₁, mul_one, mul_radialFactor_of_le h₂.le] at hab
    have : 1 / (4 * b) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  · rw [radialFactor_of_le h₂, mul_one, mul_radialFactor_of_le h₁.le] at hab
    have : 1 / (4 * a) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  · rw [mul_radialFactor_of_le h₁.le, mul_radialFactor_of_le h₂.le] at hab
    have ha0 : a ≠ 0 := by positivity
    have hb0 : b ≠ 0 := by positivity
    field_simp at hab
    linarith

/-- A continuous injection of `V` into its open unit ball, the identity on the ball of radius
`1/2`: `w ↦ radialFactor ‖w‖ • w`. -/
def radialShrink (w : V) : V := radialFactor ‖w‖ • w

/-- `radialShrink` is continuous. -/
lemma continuous_radialShrink : Continuous (radialShrink (V := V)) :=
  (continuous_radialFactor.comp continuous_norm).smul continuous_id

/-- `radialShrink w = w` for `‖w‖ ≤ 1/2`. -/
lemma radialShrink_of_norm_le {w : V} (hw : ‖w‖ ≤ 1 / 2) : radialShrink w = w := by
  rw [radialShrink, radialFactor_of_le hw, one_smul]

/-- `radialShrink 0 = 0`. -/
@[simp]
lemma radialShrink_zero : radialShrink (0 : V) = 0 := by simp [radialShrink]

/-- `‖radialShrink w‖ = ‖w‖ · radialFactor ‖w‖`. -/
lemma norm_radialShrink (w : V) : ‖radialShrink w‖ = ‖w‖ * radialFactor ‖w‖ := by
  rw [radialShrink, norm_smul, Real.norm_eq_abs, abs_of_pos (radialFactor_pos _), mul_comm]

/-- `radialShrink` takes values in the open unit ball. -/
lemma norm_radialShrink_lt_one (w : V) : ‖radialShrink w‖ < 1 := by
  rw [norm_radialShrink]
  exact mul_radialFactor_lt_one ‖w‖

/-- `radialShrink` is injective. -/
lemma injective_radialShrink : Function.Injective (radialShrink (V := V)) := by
  intro a b hab
  have hn : ‖a‖ = ‖b‖ := mul_radialFactor_injOn (norm_nonneg a) (norm_nonneg b)
    (by simpa only [norm_radialShrink] using congrArg norm hab)
  rw [radialShrink, radialShrink, hn] at hab
  exact smul_right_injective V (radialFactor_pos ‖b‖).ne' hab

/-- `radialShrink` agrees with the identity near `0`. -/
lemma radialShrink_eventuallyEq_id : radialShrink (V := V) =ᶠ[𝓝 0] id := by
  filter_upwards [Metric.ball_mem_nhds (0 : V) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
  rw [mem_ball_zero_iff] at hw
  exact radialShrink_of_norm_le hw.le

/-- The derivative of `radialShrink` at `0` is the identity. -/
lemma hasFDerivAt_radialShrink_zero :
    HasFDerivAt (radialShrink (V := V)) (ContinuousLinearMap.id ℝ V) 0 :=
  (hasFDerivAt_id 0).congr_of_eventuallyEq radialShrink_eventuallyEq_id

/-- The radial factor of `radialGrow`, the inverse of `radialShrink` on the unit ball: with
`m = max s (1/2)`, the value `1/(4m(1 - m))`; it is `1` on `[0, 1/2]`. -/
def radialGrowFactor (s : ℝ) : ℝ := 1 / (4 * max s (1 / 2) * (1 - max s (1 / 2)))

/-- `radialGrowFactor s = 1` for `s ≤ 1/2`. -/
lemma radialGrowFactor_of_le {s : ℝ} (hs : s ≤ 1 / 2) : radialGrowFactor s = 1 := by
  rw [radialGrowFactor, max_eq_right hs]
  norm_num

/-- `radialGrowFactor` is continuous on `(-∞, 1)`. -/
lemma continuousOn_radialGrowFactor : ContinuousOn radialGrowFactor (Iio 1) := by
  have hm : Continuous fun t : ℝ ↦ max t (1 / 2) := continuous_id.max continuous_const
  refine continuousOn_const.div ((continuous_const.mul hm).mul
    (continuous_const.sub hm)).continuousOn fun s hs ↦ ?_
  have h1 : (0 : ℝ) < max s (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have h2 : max s (1 / 2) < 1 := max_lt hs (by norm_num)
  have : 0 < 1 - max s (1 / 2) := by linarith
  positivity

/-- `radialGrowFactor s` is positive for `s < 1`. -/
lemma radialGrowFactor_pos {s : ℝ} (hs : s < 1) : 0 < radialGrowFactor s := by
  have h1 : (0 : ℝ) < max s (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have h2 : max s (1 / 2) < 1 := max_lt hs (by norm_num)
  have : 0 < 1 - max s (1 / 2) := by linarith
  unfold radialGrowFactor
  positivity

/-- The inverse of `radialShrink` on the open unit ball: `v ↦ radialGrowFactor ‖v‖ • v`. -/
def radialGrow (v : V) : V := radialGrowFactor ‖v‖ • v

/-- `radialGrow` is continuous on the open unit ball. -/
lemma continuousOn_radialGrow : ContinuousOn (radialGrow (V := V)) (Metric.ball 0 1) := by
  refine ContinuousOn.smul ?_ continuousOn_id
  refine continuousOn_radialGrowFactor.comp continuous_norm.continuousOn fun v hv ↦ ?_
  simpa [mem_ball_zero_iff] using hv

/-- `radialShrink (radialGrow v) = v` for `‖v‖ < 1`. -/
lemma radialShrink_radialGrow {v : V} (hv : ‖v‖ < 1) : radialShrink (radialGrow v) = v := by
  have hp := radialGrowFactor_pos hv
  have hn : ‖radialGrow v‖ = ‖v‖ * radialGrowFactor ‖v‖ := by
    rw [radialGrow, norm_smul, Real.norm_eq_abs, abs_of_pos hp, mul_comm]
  rw [radialShrink, hn, radialGrow, smul_smul]
  rcases le_or_gt ‖v‖ (1 / 2) with h | h
  · rw [radialGrowFactor_of_le h, mul_one, mul_one, radialFactor_of_le h, one_smul]
  · set s := ‖v‖
    have hg : radialGrowFactor s = 1 / (4 * s * (1 - s)) := by
      rw [radialGrowFactor, max_eq_left h.le]
    have h1 : 0 < 1 - s := by linarith
    have ht : 1 / 2 ≤ s * radialGrowFactor s := by
      rw [hg, show s * (1 / (4 * s * (1 - s))) = 1 / (4 * (1 - s)) by field_simp,
        le_div_iff₀ (by positivity)]
      linarith
    rw [radialFactor, max_eq_left ht, hg]
    convert one_smul ℝ v using 2
    have hs0 : s ≠ 0 := by positivity
    have h10 : 1 - s ≠ 0 := h1.ne'
    field_simp
    ring

/-- `radialGrow (radialShrink w) = w`. -/
@[simp]
lemma radialGrow_radialShrink (w : V) : radialGrow (radialShrink w) = w :=
  injective_radialShrink (radialShrink_radialGrow (norm_radialShrink_lt_one w))

/-- The image of `S` under `radialShrink` is the set of points of the open unit ball whose image
under `radialGrow` lies in `S`. -/
lemma image_radialShrink (S : Set V) :
    radialShrink '' S = Metric.ball 0 1 ∩ radialGrow ⁻¹' S := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨mem_ball_zero_iff.2 (norm_radialShrink_lt_one w), by
      rwa [mem_preimage, radialGrow_radialShrink]⟩
  · rintro ⟨hv, hS⟩
    exact ⟨_, hS, radialShrink_radialGrow (mem_ball_zero_iff.1 hv)⟩

/-- The range of `radialShrink` is the open unit ball. -/
lemma range_radialShrink : range (radialShrink (V := V)) = Metric.ball 0 1 := by
  rw [← image_univ, image_radialShrink, preimage_univ, inter_univ]

/-- `radialShrink` is an open map. -/
lemma isOpenMap_radialShrink : IsOpenMap (radialShrink (V := V)) := fun S hS ↦ by
  rw [image_radialShrink]
  exact continuousOn_radialGrow.isOpen_inter_preimage Metric.isOpen_ball hS

/-- `radialShrink` is an open embedding. -/
lemma isOpenEmbedding_radialShrink : IsOpenEmbedding (radialShrink (V := V)) :=
  .of_continuous_injective_isOpenMap continuous_radialShrink injective_radialShrink
    isOpenMap_radialShrink

end Radial

end MMP
