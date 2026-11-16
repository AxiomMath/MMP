module

public import MMP.Topology.MetricSpace.ReachFamily
public import MMP.Topology.MetricSpace.ReachTube
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Sublevel sets of a regular function on an embedded manifold

Let `e : M → F` be a `C²` embedding, with injective derivative, of a compact manifold with
corners into a real inner product space, and let `ρ : M → ℝ` be `C²`. Suppose that every point
`p` with `δ₁ ≤ ρ p ≤ δ₂` is an interior point at which `ρ` has nonzero derivative. Then the
images `A_δ = e '' {ρ ≤ δ}`, `δ₁ ≤ δ ≤ δ₂`, have reach bounded below by one `τ > 0`, and the
inclusion `A_{δ₁} ⊆ A_{δ₂}` is a homotopy equivalence.

Near a point of the level set, write `ρ = ℓ ∘ Ψ` in a chart, with `ℓ` the derivative of `ρ` and
`Ψ u = u + (ρ u - ℓ u) v₀` a local diffeomorphism (`ℓ v₀ = 1`); then `A_δ` is locally the image
of the convex set `{ℓ ≤ δ}` under one `C²` map with injective derivative, for every `δ`, and
the positive reach criterion holds uniformly in `δ`. Away from the level sets, `A_δ` is locally
the image `e(M)`. For the homotopy equivalence, the inclusion `A_δ ⊆ A_{δ'}` is one when `A_{δ'}`
lies within the common reach of `A_δ`: then `A_δ` and `A_{δ'}` are deformation retracts of
their tubes in `e(M)`, and two out of six applies. The level sets have no local minima, so
`A_{δ'}` lies within any given distance of `A_δ` once `δ' - δ` is small, and finitely many steps
join `δ₁` to `δ₂`.

## Main results

* `MMP.Topology.exists_straightening_of_contDiffAt`: a `C²` function with nonzero derivative is
  a linear form in suitable local coordinates.
* `MMP.Topology.exists_hasUniqueNearestPoints_image_sublevel`: the sublevel images
  `e '' {ρ ≤ δ}`, `δ₁ ≤ δ ≤ δ₂`, have a common positive lower bound for their reach.
* `MMP.Topology.exists_homotopyEquiv_inclusion_image_sublevel`: the inclusion
  `e '' {ρ ≤ δ₁} ⊆ e '' {ρ ≤ δ₂}` is a homotopy equivalence.

## Main definitions

* `MMP.Topology.RegularBand`: every point of the band `δ₁ ≤ ρ ≤ δ₂` is an interior point at
  which `ρ` has nonzero derivative.
-/

open Set Filter Topology Metric Function
open scoped Manifold ContDiff ContinuousMap

namespace MMP.Topology

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Straightening a regular function.** A `C²` function `f` with nonzero derivative `ℓ` at
`u₀` is `ℓ ∘ Ψ` for a local `C²` diffeomorphism `Ψ` with derivative the identity at `u₀`. We
record the inverse `χ` of `Ψ` on a ball around `w₀ = Ψ u₀`. -/
theorem exists_straightening_of_contDiffAt {f : E → ℝ} {u₀ : E} (hf : ContDiffAt ℝ 2 f u₀)
    (hd : fderiv ℝ f u₀ ≠ 0) :
    ∃ (χ : E → E) (ℓ : E →L[ℝ] ℝ) (v₀ w₀ : E) (R : ℝ), 0 < R ∧ ℓ v₀ = 1 ∧
      ContDiffAt ℝ 2 χ w₀ ∧ χ w₀ = u₀ ∧ HasFDerivAt χ (ContinuousLinearMap.id ℝ E) w₀ ∧
      (∀ w ∈ ball w₀ R, f (χ w) = ℓ w) ∧
      ∀ R' > 0, ∀ᶠ u in 𝓝 u₀, ∃ w ∈ ball w₀ R', χ w = u ∧ ℓ w = f u := by
  set ℓ := fderiv ℝ f u₀
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    exact hd (ContinuousLinearMap.ext fun w ↦ by simpa using not_exists.1 h w)
  set v₀ : E := (ℓ v)⁻¹ • v with hv₀
  have hℓv₀ : ℓ v₀ = 1 := by rw [hv₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  set Ψ : E → E := fun u ↦ u + (f u - ℓ u) • v₀ with hΨ
  have hℓΨ : ∀ u, ℓ (Ψ u) = f u := fun u ↦ by
    simp only [hΨ, map_add, map_smul, smul_eq_mul, hℓv₀, mul_one]; ring
  have hfd : HasFDerivAt f ℓ u₀ := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hΨd : HasFDerivAt Ψ (ContinuousLinearMap.id ℝ E) u₀ := by
    have h := (hasFDerivAt_id u₀).add ((hfd.sub ℓ.hasFDerivAt).smul_const v₀)
    convert h using 1
    · ext w; simp [hΨ]
    · ext w; simp
  have hΨc : ContDiffAt ℝ 2 Ψ u₀ :=
    contDiffAt_id.add ((hf.sub ℓ.contDiff.contDiffAt).smul contDiffAt_const)
  have hΨs : HasStrictFDerivAt Ψ
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) u₀ := by
    have := hΨc.hasStrictFDerivAt (by norm_num)
    rwa [hΨd.fderiv] at this
  set P := hΨs.toOpenPartialHomeomorph Ψ
  have hPc : ⇑P = Ψ := hΨs.toOpenPartialHomeomorph_coe
  have hu₀ : u₀ ∈ P.source := hΨs.mem_toOpenPartialHomeomorph_source
  have hw₀ : Ψ u₀ ∈ P.target := by
    have := P.map_source hu₀; rwa [hPc] at this
  have hsymm : P.symm (Ψ u₀) = u₀ := by
    have := P.left_inv hu₀; rwa [hPc] at this
  have hΨd' : HasFDerivAt P
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (P.symm (Ψ u₀)) := by
    rw [hsymm, hPc]; exact hΨd
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.1 P.open_target _ hw₀
  refine ⟨P.symm, ℓ, v₀, Ψ u₀, R, hR, hℓv₀, ?_, hsymm, ?_, ?_, ?_⟩
  · refine P.contDiffAt_symm hw₀ hΨd' ?_
    rw [hsymm, hPc]; exact hΨc
  · simpa using P.hasFDerivAt_symm hw₀ hΨd'
  · intro w hw
    have h := P.right_inv (hRt hw)
    rw [hPc] at h
    rw [← hℓΨ, h]
  · intro R' hR'
    filter_upwards [P.open_source.mem_nhds hu₀,
      hΨd.continuousAt.preimage_mem_nhds (ball_mem_nhds (Ψ u₀) hR')] with u hu hub
    refine ⟨Ψ u, hub, ?_, hℓΨ u⟩
    have := P.left_inv hu
    rwa [hPc] at this

section Manifold

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : M → F} {ρ : M → ℝ}

/-- Near a point `p₀` where `ρ` has nonzero derivative in a chart, the pair `(ρ, e)` is
`(ℓ, G)` in suitable coordinates: `G` is `C²` with injective derivative at `w₀`, every point
`w` of a ball around `w₀` comes from a point `p` of `M` with `ρ p = ℓ w` and `e p = G w`, and
every point near `p₀` comes from a point of any given ball around `w₀`. -/
theorem exists_sublevel_param (he : ContMDiff I 𝓘(ℝ, F) 2 e) (hρ : ContMDiff I 𝓘(ℝ) 2 ρ)
    {x₀ p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source)
    (hint : extChartAt I x₀ p₀ ∈ interior (range I))
    (hd : fderivWithin ℝ (ρ ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀) ≠ 0)
    (hinj : Injective
      (fderivWithin ℝ (e ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀))) :
    ∃ (G : E → F) (ℓ : E →L[ℝ] ℝ) (v₀ w₀ : E) (R : ℝ), 0 < R ∧ ℓ v₀ = 1 ∧
      ContDiffAt ℝ 2 G w₀ ∧ Injective (fderiv ℝ G w₀) ∧ G w₀ = e p₀ ∧
      (∀ w ∈ ball w₀ R, ∃ p, ρ p = ℓ w ∧ e p = G w) ∧
      ∀ R' > 0, ∀ᶠ p in 𝓝 p₀, ∃ w ∈ ball w₀ R', ℓ w = ρ p ∧ G w = e p := by
  set φ := extChartAt I x₀ with hφ
  set u₀ := φ p₀ with hu₀
  have hnhds : range I ∈ 𝓝 u₀ := mem_interior_iff_mem_nhds.1 hint
  have hf : ContDiffAt ℝ 2 (ρ ∘ φ.symm) u₀ :=
    (contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiffAt_iff_source_of_mem_source hp₀).1 (hρ p₀))).contDiffAt hnhds
  have hg : ContDiffAt ℝ 2 (e ∘ φ.symm) u₀ :=
    (contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiffAt_iff_source_of_mem_source hp₀).1 (he p₀))).contDiffAt hnhds
  rw [fderivWithin_of_mem_nhds hnhds] at hd hinj
  obtain ⟨χ, ℓ, v₀, w₀, R, hR, hℓv₀, hχ, hχw₀, hχd, hfχ, hev⟩ :=
    exists_straightening_of_contDiffAt hf hd
  have hg' : ContDiffAt ℝ 2 (e ∘ φ.symm) (χ w₀) := by rw [hχw₀]; exact hg
  have hgd : HasFDerivAt (e ∘ φ.symm) (fderiv ℝ (e ∘ φ.symm) u₀) (χ w₀) := by
    rw [hχw₀]; exact (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hp₀s : p₀ ∈ φ.source := by rwa [hφ, extChartAt_source]
  refine ⟨(e ∘ φ.symm) ∘ χ, ℓ, v₀, w₀, R, hR, hℓv₀, hg'.comp w₀ hχ, ?_, ?_, ?_, ?_⟩
  · rw [(hgd.comp w₀ hχd).fderiv]
    exact hinj
  · simp only [comp_apply, hχw₀, hu₀, φ.left_inv hp₀s]
  · exact fun w hw ↦ ⟨φ.symm (χ w), hfχ w hw, rfl⟩
  · intro R' hR'
    have hc : ContinuousAt φ p₀ := continuousAt_extChartAt' (by rwa [extChartAt_source])
    filter_upwards [hc.preimage_mem_nhds (hev R' hR'),
      extChartAt_source_mem_nhds' (I := I) (x := x₀) (by rwa [extChartAt_source])]
      with p hp hps
    obtain ⟨w, hw, hχw, hℓw⟩ := hp
    refine ⟨w, hw, ?_, ?_⟩
    · rw [hℓw]; simp only [comp_apply, φ.left_inv hps]
    · simp only [comp_apply, hχw, φ.left_inv hps]

/-- Near a regular point `p₀` of `ρ`, every point `p` reaches any level `δ` slightly below
`ρ p` within distance `r` in `e`: some `q` with `ρ q ≤ δ` has `e q` within `r` of `e p`. -/
theorem exists_nhds_exists_sublevel_dist_lt (he : ContMDiff I 𝓘(ℝ, F) 2 e)
    (hρ : ContMDiff I 𝓘(ℝ) 2 ρ) {x₀ p₀ : M} (hx₀ : p₀ ∈ (chartAt H x₀).source)
    (hint : extChartAt I x₀ p₀ ∈ interior (range I))
    (hd : fderivWithin ℝ (ρ ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀) ≠ 0)
    (hinj₀ : Injective
      (fderivWithin ℝ (e ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀)))
    {r : ℝ} (hr : 0 < r) :
    ∃ O ∈ 𝓝 p₀, ∃ η₀ > 0, ∀ p ∈ O, ∀ δ,
      ρ p - η₀ ≤ δ → δ ≤ ρ p → ∃ q, ρ q ≤ δ ∧ dist (e q) (e p) < r := by
  obtain ⟨G, ℓ, v₀, w₀, R, hR, hℓv₀, hGc, -, -, hpar, hev⟩ :=
    exists_sublevel_param he hρ hx₀ hint hd hinj₀
  obtain ⟨R₂, hR₂, hR₂G⟩ := Metric.continuousAt_iff.1 (hGc.continuousAt) (r / 2) (half_pos hr)
  set R₃ := min R R₂
  have hR₃0 : 0 < R₃ := lt_min hR hR₂
  refine ⟨_, hev (R₃ / 2) (half_pos hR₃0), R₃ / (2 * (‖v₀‖ + 1)), by positivity, ?_⟩
  rintro p ⟨w, hw, hℓw, hGw⟩ δ hδ1 hδ2
  set t := ρ p - δ with ht
  have ht0 : 0 ≤ t := by linarith
  have htη : t ≤ R₃ / (2 * (‖v₀‖ + 1)) := by linarith
  set w' := w - t • v₀ with hw'
  have hw'b : w' ∈ ball w₀ R₃ := by
    rw [mem_ball] at hw ⊢
    have h1 : dist w' w = t * ‖v₀‖ := by
      rw [hw', dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg ht0]
    have h2 : t * ‖v₀‖ < R₃ / 2 := by
      have : t * ‖v₀‖ ≤ R₃ / (2 * (‖v₀‖ + 1)) * ‖v₀‖ :=
        mul_le_mul_of_nonneg_right htη (norm_nonneg _)
      have h3 : R₃ / (2 * (‖v₀‖ + 1)) * ‖v₀‖ < R₃ / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [norm_nonneg v₀]
      linarith
    linarith [dist_triangle w' w w₀]
  obtain ⟨q, hq, hqG⟩ := hpar w' (ball_subset_ball (min_le_left _ _) hw'b)
  refine ⟨q, ?_, ?_⟩
  · rw [hq, hw', map_sub, map_smul, hℓv₀, smul_eq_mul, mul_one, hℓw, ht]
    linarith
  · rw [hqG, ← hGw]
    calc dist (G w') (G w) ≤ dist (G w') (G w₀) + dist (G w) (G w₀) := dist_triangle_right _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hR₂G (ball_subset_ball (min_le_right _ _) hw'b))
          (hR₂G (ball_subset_ball ((half_le_self hR₃0.le).trans (min_le_right _ _)) hw))
      _ = r := by ring

end Manifold

section Reach

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e : M → F} {ρ : M → ℝ}

/-- The regularity hypothesis on the band `δ₁ ≤ ρ ≤ δ₂`: each of its points is an interior
point of some chart in which `ρ` has nonzero derivative and `e` has injective derivative. -/
@[expose] def RegularBand (I : ModelWithCorners ℝ E H) (e : M → F) (ρ : M → ℝ) (δ₁ δ₂ : ℝ) : Prop :=
  ∀ p, ρ p ∈ Icc δ₁ δ₂ → ∃ x₀, p ∈ (chartAt H x₀).source ∧
    extChartAt I x₀ p ∈ interior (range I) ∧
    fderivWithin ℝ (ρ ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p) ≠ 0 ∧
    Injective (fderivWithin ℝ (e ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p))

omit [IsManifold I 2 M] in
/-- Below the band, near a point `p₀` with `ρ p₀ < δ₁`, the sublevel images
`e '' {ρ ≤ k}`, `δ₁ ≤ k ≤ δ₂`, satisfy one local inner-product bound. -/
theorem exists_nhds_inner_le_image_sublevel_of_lt (he : ContMDiff I 𝓘(ℝ, F) 2 e)
    (hemb : IsEmbedding e) (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x))
    (hρ : ContMDiff I 𝓘(ℝ) 2 ρ) {δ₁ δ₂ : ℝ} {p₀ : M} (hlt : ρ p₀ < δ₁) :
    ∃ V ∈ 𝓝 (e p₀), ∃ K : ℝ, ∀ (k : Icc δ₁ δ₂) y,
      ∀ a ∈ e '' {p | ρ p ≤ k} ∩ V, dist y a = infDist y (e '' {p | ρ p ≤ k}) →
      ∀ b ∈ e '' {p | ρ p ≤ k} ∩ V, inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2 := by
  set φ := extChartAt I p₀
  have hu₀ : φ p₀ ∈ range I := extChartAt_target_subset_range p₀ (mem_extChartAt_target p₀)
  have hgc : ContDiffWithinAt ℝ 2 (e ∘ φ.symm) (range I) (φ p₀) := by
    have := (contMDiffAt_iff.1 (he p₀)).2
    rwa [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at this
  have hρc : ContinuousWithinAt (ρ ∘ φ.symm) (range I) (φ p₀) := by
    have := (contMDiffAt_iff.1 (hρ p₀)).2
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at this
    exact this.continuousWithinAt
  have hmd : MDifferentiableAt I 𝓘(ℝ, F) e p₀ := (he p₀).mdifferentiableAt (by norm_num)
  have hinj' : Function.Injective (fderivWithin ℝ (e ∘ φ.symm) (range I) (φ p₀)) := by
    have h := hinj p₀
    rw [hmd.mfderiv, writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at h
    intro a b hab
    exact h hab
  have hev : ∀ᶠ u in 𝓝[range I] φ p₀, u ∈ φ.target ∧ ρ (φ.symm u) < δ₁ := by
    have h1 : ∀ᶠ u in 𝓝[range I] φ p₀, u ∈ φ.target :=
      extChartAt_target_mem_nhdsWithin (I := I) p₀
    refine h1.and ?_
    have : ρ (φ.symm (φ p₀)) < δ₁ := by
      rwa [φ.left_inv (mem_extChartAt_source p₀)]
    exact hρc.eventually_lt continuousWithinAt_const this
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set s := range I ∩ ball (φ p₀) r₀ with hs
  have hsc : Convex ℝ s := I.convex_range.inter (convex_ball _ _)
  have hsu : UniqueDiffOn ℝ s := I.uniqueDiffOn.inter isOpen_ball
  have hu₀s : φ p₀ ∈ s := ⟨hu₀, mem_ball_self hr₀⟩
  have hinjs : Function.Injective (fderivWithin ℝ (e ∘ φ.symm) s (φ p₀)) := by
    rwa [hs, fderivWithin_inter (ball_mem_nhds _ hr₀)]
  obtain ⟨r, hr, K, hK⟩ := exists_inner_sub_le_of_contDiffWithinAt hsc hsu hu₀s
    (hgc.mono inter_subset_left) hinjs
  set O := φ.source ∩ φ ⁻¹' ball (φ p₀) (min r r₀)
  have hOn : O ∈ 𝓝 p₀ := inter_mem (extChartAt_source_mem_nhds p₀)
    ((continuousAt_extChartAt p₀).preimage_mem_nhds (ball_mem_nhds _ (lt_min hr hr₀)))
  rw [hemb.isInducing.nhds_eq_comap] at hOn
  obtain ⟨V, hV, hVO⟩ := mem_comap.1 hOn
  refine ⟨V, hV, K, ?_⟩
  rintro ⟨k, hk⟩ y _ ⟨⟨x, hxk, rfl⟩, hxV⟩ hd _ ⟨⟨x', hx'k, rfl⟩, hx'V⟩
  have hxO : x ∈ O := hVO hxV
  have hx'O : x' ∈ O := hVO hx'V
  have mem : ∀ z ∈ O, φ z ∈ s ∩ ball (φ p₀) r := fun z hz ↦
    ⟨⟨extChartAt_target_subset_range p₀ (φ.map_source hz.1),
      ball_subset_ball (min_le_right _ _) hz.2⟩, ball_subset_ball (min_le_left _ _) hz.2⟩
  have eq : ∀ z ∈ O, (e ∘ φ.symm) (φ z) = e z := fun z hz ↦ by
    simp [φ.left_inv hz.1]
  have := hK y (φ x) (mem x hxO) (fun w hw ↦ ?_) (φ x') (mem x' hx'O)
  · rwa [eq x hxO, eq x' hx'O] at this
  · rw [eq x hxO, ← dist_eq_norm, ← dist_eq_norm, hd]
    obtain ⟨-, hρw⟩ := hr₀s ⟨hw.1.2, hw.1.1⟩
    exact infDist_le_dist_of_mem ⟨φ.symm w, (show ρ (φ.symm w) ≤ k from hρw.le.trans hk.1),
      rfl⟩

/-- Near a regular point `p₀` of `ρ`, the sublevel images `e '' {ρ ≤ k}`, `δ₁ ≤ k ≤ δ₂`,
satisfy one local inner-product bound. -/
theorem exists_nhds_inner_le_image_sublevel_of_regular (he : ContMDiff I 𝓘(ℝ, F) 2 e)
    (hemb : IsEmbedding e) (hρ : ContMDiff I 𝓘(ℝ) 2 ρ) {δ₁ δ₂ : ℝ} {x₀ p₀ : M}
    (hx₀ : p₀ ∈ (chartAt H x₀).source) (hint : extChartAt I x₀ p₀ ∈ interior (range I))
    (hd : fderivWithin ℝ (ρ ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀) ≠ 0)
    (hinj₀ : Injective
      (fderivWithin ℝ (e ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p₀))) :
    ∃ V ∈ 𝓝 (e p₀), ∃ K : ℝ, ∀ (k : Icc δ₁ δ₂) y,
      ∀ a ∈ e '' {p | ρ p ≤ k} ∩ V, dist y a = infDist y (e '' {p | ρ p ≤ k}) →
      ∀ b ∈ e '' {p | ρ p ≤ k} ∩ V, inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2 := by
  obtain ⟨G, ℓ, v₀, w₀, R, hR, -, hGc, hGinj, -, hpar, hev⟩ :=
    exists_sublevel_param he hρ hx₀ hint hd hinj₀
  obtain ⟨r, hr, K, hK⟩ := exists_inner_sub_le_of_contDiffAt hGc hGinj
  have hOn := hev (min R r) (lt_min hR hr)
  rw [hemb.isInducing.nhds_eq_comap] at hOn
  obtain ⟨V, hV, hVO⟩ := mem_comap.1 hOn
  refine ⟨V, hV, K, ?_⟩
  rintro ⟨k, hk⟩ y _ ⟨⟨x, hxk, rfl⟩, hxV⟩ hdist _ ⟨⟨x', hx'k, rfl⟩, hx'V⟩
  obtain ⟨w, hw, hℓw, hGw⟩ := hVO hxV
  obtain ⟨w', hw', hℓw', hGw'⟩ := hVO hx'V
  set S := {w | ℓ w ≤ k} ∩ ball w₀ (min R r)
  have hSc : Convex ℝ S := (convex_halfSpace_le ℓ.isLinear k).inter (convex_ball _ _)
  have hSb : S ⊆ ball w₀ r := fun z hz ↦ ball_subset_ball (min_le_right _ _) hz.2
  have hwS : w ∈ S := ⟨hℓw.trans_le hxk, hw⟩
  have hw'S : w' ∈ S := ⟨hℓw'.trans_le hx'k, hw'⟩
  have := hK S hSb hSc y w hwS (isMinOn_iff.2 fun z hz ↦ ?_) w' hw'S
  · rwa [hGw, hGw'] at this
  · rw [hGw, ← dist_eq_norm, ← dist_eq_norm, hdist]
    obtain ⟨q, hq, hqG⟩ := hpar z (ball_subset_ball (min_le_left _ _) hz.2)
    rw [← hqG]
    exact infDist_le_dist_of_mem ⟨q, hq.trans_le hz.1, rfl⟩

/-- **Uniform reach of sublevel sets.** If every point of the band `δ₁ ≤ ρ ≤ δ₂` is regular,
the images `e '' {ρ ≤ δ}`, `δ₁ ≤ δ ≤ δ₂`, have a common positive lower bound for their reach. -/
theorem exists_hasUniqueNearestPoints_image_sublevel [CompactSpace M] [ProperSpace F]
    (he : ContMDiff I 𝓘(ℝ, F) 2 e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x)) (hρ : ContMDiff I 𝓘(ℝ) 2 ρ)
    {δ₁ δ₂ : ℝ} (hband : RegularBand I e ρ δ₁ δ₂) :
    ∃ τ > 0, ∀ δ ∈ Icc δ₁ δ₂, HasUniqueNearestPoints (e '' {p | ρ p ≤ δ}) τ := by
  have hcomp : ∀ δ, IsCompact (e '' {p | ρ p ≤ δ}) := fun δ ↦
    ((isClosed_le hρ.continuous continuous_const).isCompact).image he.continuous
  suffices hloc : ∀ z₀ ∈ e '' {p | ρ p ≤ δ₂}, ∃ V ∈ 𝓝 z₀, ∃ K : ℝ, ∀ (k : Icc δ₁ δ₂) y,
      ∀ a ∈ e '' {p | ρ p ≤ k} ∩ V, dist y a = infDist y (e '' {p | ρ p ≤ k}) →
      ∀ b ∈ e '' {p | ρ p ≤ k} ∩ V, inner ℝ (y - a) (b - a) ≤ K * ‖y - a‖ * ‖b - a‖ ^ 2 by
    obtain ⟨τ, hτ, hu⟩ := exists_hasUniqueNearestPoints_of_locally_inner_le_family (hcomp δ₂)
      (A := fun δ : Icc δ₁ δ₂ ↦ e '' {p | ρ p ≤ δ})
      (fun δ ↦ image_mono fun p hp ↦ (show ρ p ≤ δ from hp).trans δ.2.2)
      (fun δ ↦ (hcomp δ).isClosed) hloc
    exact ⟨τ, hτ, fun δ hδ ↦ hu ⟨δ, hδ⟩⟩
  rintro _ ⟨p₀, hp₀, rfl⟩
  rcases lt_or_ge (ρ p₀) δ₁ with hlt | hge
  · exact exists_nhds_inner_le_image_sublevel_of_lt he hemb hinj hρ hlt
  · obtain ⟨x₀, hx₀, hint, hd, hinj₀⟩ := hband p₀ ⟨hge, hp₀⟩
    exact exists_nhds_inner_le_image_sublevel_of_regular he hemb hρ hx₀ hint hd hinj₀

/-- On a regular band, the sublevel images vary continuously from the left: for each `r > 0`
there is `η > 0` such that `e '' {ρ ≤ δ'}` lies within `r` of `e '' {ρ ≤ δ}` whenever
`δ₁ ≤ δ ≤ δ' ≤ min δ₂ (δ + η)`. -/
theorem exists_image_sublevel_subset_thickening [CompactSpace M]
    (he : ContMDiff I 𝓘(ℝ, F) 2 e) (hρ : ContMDiff I 𝓘(ℝ) 2 ρ) {δ₁ δ₂ : ℝ}
    (hband : RegularBand I e ρ δ₁ δ₂) {r : ℝ} (hr : 0 < r) :
    ∃ η > 0, ∀ δ δ', δ₁ ≤ δ → δ ≤ δ' → δ' ≤ δ₂ → δ' ≤ δ + η →
      e '' {p | ρ p ≤ δ'} ⊆ thickening r (e '' {p | ρ p ≤ δ}) := by
  classical
  have hloc : ∀ p₀ ∈ {p | ρ p ∈ Icc δ₁ δ₂}, ∃ O ∈ 𝓝 p₀, ∃ η₀ > 0, ∀ p ∈ O, ∀ δ,
      ρ p - η₀ ≤ δ → δ ≤ ρ p → ∃ q, ρ q ≤ δ ∧ dist (e q) (e p) < r := fun p₀ hp₀ ↦ by
    obtain ⟨x₀, hx₀, hint, hd, hinj₀⟩ := hband p₀ hp₀
    exact exists_nhds_exists_sublevel_dist_lt he hρ hx₀ hint hd hinj₀ hr
  choose! O hO η₀ hη₀ hOη using hloc
  have hK : IsCompact {p | ρ p ∈ Icc δ₁ δ₂} :=
    (isClosed_Icc.preimage hρ.continuous).isCompact
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover O hO
  set η := (∑ x ∈ t, (η₀ x)⁻¹ + 1)⁻¹ with hη
  have hsum : 0 ≤ ∑ x ∈ t, (η₀ x)⁻¹ :=
    Finset.sum_nonneg fun x hx ↦ (inv_pos.2 (hη₀ x (htK x hx))).le
  have hηle : ∀ x ∈ t, η ≤ η₀ x := by
    intro x hx
    have hx0 := hη₀ x (htK x hx)
    rw [hη, inv_le_comm₀ (by positivity) hx0]
    have : (η₀ x)⁻¹ ≤ ∑ y ∈ t, (η₀ y)⁻¹ :=
      Finset.single_le_sum (f := fun y ↦ (η₀ y)⁻¹)
        (fun y hy ↦ (inv_pos.2 (hη₀ y (htK y hy))).le) hx
    linarith
  refine ⟨η, by positivity, ?_⟩
  rintro δ δ' hδ₁ hδδ' hδ'₂ hδ'η _ ⟨p, hp, rfl⟩
  have hp' : ρ p ≤ δ' := hp
  rcases le_or_gt (ρ p) δ with hle | hgt
  · exact self_subset_thickening hr _ ⟨p, hle, rfl⟩
  · have hpK : p ∈ {p | ρ p ∈ Icc δ₁ δ₂} := ⟨by linarith, by linarith⟩
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.1 (hcov hpK)
    obtain ⟨q, hq, hqp⟩ := hOη x (htK x hx) p hpx δ
      (by linarith [hηle x hx]) hgt.le
    exact mem_thickening_iff.2 ⟨e q, ⟨q, hq, rfl⟩, by rwa [dist_comm]⟩

/-- **Chaining homotopy equivalences.** If every inclusion `A δ ⊆ A δ'` with
`δ₁ ≤ δ ≤ δ' ≤ min δ₂ (δ + η)` is a homotopy equivalence, then so is `A δ₁ ⊆ A δ₂`. -/
theorem exists_homotopyEquiv_inclusion_of_forall_le_add {X : Type*} [TopologicalSpace X]
    {A : ℝ → Set X} {δ₁ δ₂ η : ℝ} (hη : 0 < η) (h₁₂ : δ₁ ≤ δ₂)
    (hstep : ∀ δ δ', δ₁ ≤ δ → δ ≤ δ' → δ' ≤ δ₂ → δ' ≤ δ + η →
      ∃ h : A δ ⊆ A δ', ∃ e : A δ ≃ₕ A δ', e.toFun = ContinuousMap.inclusion h) :
    ∃ h : A δ₁ ⊆ A δ₂, ∃ e : A δ₁ ≃ₕ A δ₂, e.toFun = ContinuousMap.inclusion h := by
  have hchain : ∀ m : ℕ, ∀ δ', δ₁ ≤ δ' → δ' ≤ δ₂ → δ' ≤ δ₁ + m * η →
      ∃ h : A δ₁ ⊆ A δ', ∃ e : A δ₁ ≃ₕ A δ', e.toFun = ContinuousMap.inclusion h := by
    intro m
    induction m with
    | zero =>
      intro δ' h1 _ h3
      obtain rfl : δ' = δ₁ := le_antisymm (by simpa using h3) h1
      exact ⟨subset_rfl, ContinuousMap.HomotopyEquiv.refl _, ContinuousMap.ext fun x ↦ rfl⟩
    | succ m ih =>
      intro δ' h1 h2 h3
      rcases le_or_gt δ' (δ₁ + m * η) with hle | hgt
      · exact ih δ' h1 h2 hle
      · have hm : 0 ≤ (m : ℝ) * η := by positivity
        obtain ⟨hs₁, e₁, he₁⟩ := ih (δ₁ + m * η) (by linarith) (by linarith) le_rfl
        obtain ⟨hs₂, e₂, he₂⟩ := hstep (δ₁ + m * η) δ' (by linarith) hgt.le h2
          (by push_cast at h3; linarith)
        exact ⟨hs₁.trans hs₂, exists_homotopyEquiv_inclusion_trans hs₁ hs₂ ⟨e₁, he₁⟩ ⟨e₂, he₂⟩⟩
  refine hchain ⌈(δ₂ - δ₁) / η⌉₊ δ₂ h₁₂ le_rfl ?_
  have h := Nat.le_ceil ((δ₂ - δ₁) / η)
  rw [div_le_iff₀ hη] at h
  linarith

/-- **Sublevel inclusions on a regular band are homotopy equivalences.** If every point of the
band `δ₁ ≤ ρ ≤ δ₂` is regular, the inclusion `e '' {ρ ≤ δ₁} ⊆ e '' {ρ ≤ δ₂}` is a homotopy
equivalence. -/
theorem exists_homotopyEquiv_inclusion_image_sublevel [CompactSpace M] [ProperSpace F]
    (he : ContMDiff I 𝓘(ℝ, F) 2 e) (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective (mfderiv I 𝓘(ℝ, F) e x)) (hρ : ContMDiff I 𝓘(ℝ) 2 ρ)
    {δ₁ δ₂ : ℝ} (hband : RegularBand I e ρ δ₁ δ₂) (h₁₂ : δ₁ ≤ δ₂) :
    ∃ e' : (e '' {p | ρ p ≤ δ₁}) ≃ₕ (e '' {p | ρ p ≤ δ₂}),
      e'.toFun = ContinuousMap.inclusion (image_mono fun p (hp : ρ p ≤ δ₁) ↦ hp.trans h₁₂) := by
  set Aδ : ℝ → Set F := fun δ ↦ e '' {p | ρ p ≤ δ}
  have hmono : ∀ {δ δ'}, δ ≤ δ' → Aδ δ ⊆ Aδ δ' := fun h ↦
    image_mono fun p (hp : ρ p ≤ _) ↦ hp.trans h
  have hcl : ∀ δ, IsClosed (Aδ δ) := fun δ ↦
    (((isClosed_le hρ.continuous continuous_const).isCompact).image he.continuous).isClosed
  obtain ⟨τ, hτ, hu⟩ := exists_hasUniqueNearestPoints_image_sublevel he hemb hinj hρ hband
  obtain ⟨τA, hτA, huA⟩ := exists_hasUniqueNearestPoints_range he hemb hinj
  have hAcl : IsClosed (range e) := (isCompact_range he.continuous).isClosed
  set r := min τ τA
  have hr0 : 0 < r := lt_min hτ hτA
  obtain ⟨η, hη, hstep⟩ := exists_image_sublevel_subset_thickening he hρ hband hr0
  have htube : ∀ δ ∈ Icc δ₁ δ₂, ∃ e' : Aδ δ ≃ₕ (range e ∩ thickening r (Aδ δ) : Set F),
      e'.toFun = ContinuousMap.inclusion (subset_inter (image_subset_range _ _)
        (self_subset_thickening hr0 _)) := by
    intro δ hδ
    exact exists_homotopyEquiv_inclusion_inter_thickening hAcl (hcl δ)
      (image_subset_range _ _) huA (hu δ hδ) hr0 (min_le_right _ _) (min_le_left _ _)
  have hone : ∀ δ δ', δ₁ ≤ δ → δ ≤ δ' → δ' ≤ δ₂ → δ' ≤ δ + η →
      ∃ h : Aδ δ ⊆ Aδ δ', ∃ e' : Aδ δ ≃ₕ Aδ δ', e'.toFun = ContinuousMap.inclusion h := by
    intro δ δ' h1 h2 h3 h4
    have hsub : Aδ δ' ⊆ range e ∩ thickening r (Aδ δ) :=
      subset_inter (image_subset_range _ _) (hstep δ δ' h1 h2 h3 h4)
    have hsub' : range e ∩ thickening r (Aδ δ) ⊆ range e ∩ thickening r (Aδ δ') :=
      inter_subset_inter_right _ (thickening_subset_of_subset r (hmono h2))
    obtain ⟨e₁, he₁⟩ := htube δ ⟨h1, h2.trans h3⟩
    obtain ⟨e₂, he₂⟩ := htube δ' ⟨h1.trans h2, h3⟩
    exact ⟨hmono h2, (exists_homotopyEquiv_inclusion_of_two_out_of_six (hmono h2) hsub hsub'
      ⟨e₁, he₁⟩ ⟨e₂, he₂⟩).1⟩
  obtain ⟨_, e', he'⟩ := exists_homotopyEquiv_inclusion_of_forall_le_add (A := Aδ) hη h₁₂ hone
  exact ⟨e', he'⟩

end Reach

end

end MMP.Topology
