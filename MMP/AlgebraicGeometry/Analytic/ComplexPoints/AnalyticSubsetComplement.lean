module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The complement of a proper analytic subset of a connected space is connected and dense

Let `M` be a preconnected topological space and `S ⊆ M` a subset which is *locally analytic*:
every point `p` has a chart `e : M → E` (an open partial homeomorphism to a complex normed space)
around it in which `S` is the common zero set of a family of functions analytic on the target of
`e`. If `S ≠ M`, then `M - S` is preconnected and dense in `M`. This is the statement on the
complement of a proper analytic subset of a connected complex manifold which, classically,
is deduced from the Riemann extension theorem.

The proof here is elementary. Locally, if `g` is analytic on a convex open `W` of a complex
normed space and `g(x) ≠ 0`, then for every `y ∈ W` the restriction of `g` to the complex line
through `x` and `y` is a one-variable analytic function on a convex open subset `D` of `ℂ`, not
identically zero; its zeros in `D` are isolated, hence countable, and a path in `D` from `0` to `1`
avoiding them is a broken line `0 → 1/2 + i s → 1` for all but countably many real `s`. So
`{g ≠ 0}` is path-connected and dense in `W`. Globally, the interior of `S` is open and, by the
identity theorem, closed, hence empty; so near every point one of the local equations of `S` does
not vanish identically, and the local result applies. A clopen partition of `M - S` then extends
to one of `M`.

## Main results

* `MMP.SmoothLocusConnected.isPathConnected_diff_preimage_zero`,
  `MMP.SmoothLocusConnected.subset_closure_diff_preimage_zero`: for `g` analytic
  on a convex open `W` and not vanishing at some point of `W`, `W - {g = 0}` is path-connected and
  dense in `W`.
* `MMP.SmoothLocusConnected.isPreconnected_compl_of_forall_isPreconnected_diff`: a
  dense subset `M - S` of a preconnected space which is locally preconnected (each point has a
  neighbourhood `W` with `W - S` preconnected) is preconnected.
* `MMP.SmoothLocusConnected.dense_compl_of_isLocallyAnalytic`,
  `MMP.SmoothLocusConnected.isPreconnected_compl_of_isLocallyAnalytic`,
  `MMP.SmoothLocusConnected.isConnected_compl_of_isLocallyAnalytic`: the
  complement of a proper locally analytic subset of a (pre)connected space is (pre)connected and
  dense.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [R. C. Gunning, H. Rossi, *Analytic functions of several complex variables*], Chapter I.C.
-/

@[expose] public section

open Set Filter Topology

namespace MMP.SmoothLocusConnected

/-! ### A broken line in a convex open subset of `ℂ` avoiding a countable set -/

/-- The corner `1/2 + i s` of the broken line `0 → 1/2 + i s → 1`. -/
private noncomputable def corner (s : ℝ) : ℂ := (1 / 2 : ℂ) + s * Complex.I

private lemma corner_re (s : ℝ) : (corner s).re = 1 / 2 := by simp [corner]

private lemma corner_im (s : ℝ) : (corner s).im = s := by simp [corner]

/-- A point `z ≠ 0` lies on the segment `[0, 1/2 + i s]` for at most one `s`. -/
private lemma subsingleton_setOf_mem_segment_zero {z : ℂ} (hz : z ≠ 0) :
    {s : ℝ | z ∈ segment ℝ 0 (corner s)}.Subsingleton := by
  have key : ∀ s, z ∈ segment ℝ 0 (corner s) → s = z.im / (2 * z.re) := by
    intro s hs
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
    have hb0 : b ≠ 0 := by rintro rfl; simp at hz
    simp only [smul_zero, zero_add, Complex.smul_re, Complex.smul_im, corner_re, corner_im,
      smul_eq_mul]
    field_simp
  intro s hs t ht
  rw [key s hs, key t ht]

/-- A point `z ≠ 1` lies on the segment `[1/2 + i s, 1]` for at most one `s`. -/
private lemma subsingleton_setOf_mem_segment_one {z : ℂ} (hz : z ≠ 1) :
    {s : ℝ | z ∈ segment ℝ (corner s) 1}.Subsingleton := by
  have key : ∀ s, z ∈ segment ℝ (corner s) 1 → s = z.im / (2 * (1 - z.re)) := by
    intro s hs
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain rfl : b = 1 := by linarith
      simp at hz
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, corner_re,
      corner_im, smul_eq_mul, Complex.one_re, Complex.one_im]
    rw [show 2 * (1 - (a * (1 / 2) + (1 - a) * 1)) = a by ring, mul_zero, add_zero,
      mul_div_cancel_left₀ _ ha0]
  intro s hs t ht
  rw [key s hs, key t ht]

/-- In a convex open subset `D` of `ℂ` containing `0` and `1`, the points `0` and `1` can be
joined by a path avoiding any countable set `Z` not containing them. -/
theorem joinedIn_zero_one_diff_of_countable {D Z : Set ℂ} (hD : IsOpen D) (hDc : Convex ℝ D)
    (h0 : (0 : ℂ) ∈ D) (h1 : (1 : ℂ) ∈ D) (hZ : Z.Countable) (h0Z : (0 : ℂ) ∉ Z)
    (h1Z : (1 : ℂ) ∉ Z) : JoinedIn (D \ Z) 0 1 := by
  have hmid : (1 / 2 : ℂ) ∈ D := by
    have := hDc.segment_subset h0 h1 (midpoint_mem_segment (𝕜 := ℝ) (0 : ℂ) 1)
    simpa [midpoint_eq_smul_add] using this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD _ hmid
  set B : Set ℝ := ⋃ z ∈ Z, ({s | z ∈ segment ℝ 0 (corner s)} ∪
    {s | z ∈ segment ℝ (corner s) 1})
  have hB : B.Countable := by
    refine hZ.biUnion fun z hz ↦ ?_
    exact ((subsingleton_setOf_mem_segment_zero (ne_of_mem_of_not_mem hz h0Z)).countable).union
      (subsingleton_setOf_mem_segment_one (ne_of_mem_of_not_mem hz h1Z)).countable
  obtain ⟨s, hsB, hs⟩ : ∃ s ∈ Bᶜ, s ∈ Metric.ball (0 : ℝ) ε :=
    (hB.dense_compl ℝ).exists_mem_open Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
  have hw : corner s ∈ D := hball (by
    rw [Metric.mem_ball, Complex.dist_eq] at *
    simpa [corner, abs_of_nonneg, Real.norm_eq_abs, dist_zero_right] using hs)
  simp only [B, mem_compl_iff, mem_iUnion, mem_union, mem_setOf_eq, not_exists, not_or] at hsB
  have hseg0 : segment ℝ 0 (corner s) ⊆ D \ Z := fun z hz ↦
    ⟨hDc.segment_subset h0 hw hz, fun hzZ ↦ (hsB z hzZ).1 hz⟩
  have hseg1 : segment ℝ (corner s) 1 ⊆ D \ Z := fun z hz ↦
    ⟨hDc.segment_subset hw h1 hz, fun hzZ ↦ (hsB z hzZ).2 hz⟩
  exact (JoinedIn.of_segment_subset hseg0).trans (JoinedIn.of_segment_subset hseg1)

/-! ### The nonvanishing locus of an analytic function on a convex open set -/

/-- The zeros in a preconnected set `D ⊆ ℂ` of a function analytic on a neighbourhood of `D`, not
vanishing at some point of `D`, form a countable set. -/
theorem countable_inter_preimage_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {D : Set ℂ} (hg : AnalyticOnNhd ℂ g D) (hD : IsPreconnected D) {t₀ : ℂ}
    (ht₀ : t₀ ∈ D) (hgt₀ : g t₀ ≠ 0) : (D ∩ g ⁻¹' {0}).Countable := by
  rcases hg.eqOn_zero_or_eventually_ne_zero_of_preconnected hD with h | h
  · exact absurd (h ht₀) hgt₀
  · have hdisc : ∀ x ∈ D ∩ g ⁻¹' {0}, 𝓝[≠] x ⊓ 𝓟 (D ∩ g ⁻¹' {0}) = ⊥ := by
      intro x hx
      have := (mem_codiscreteWithin.mp h) x hx.1
      rw [← disjoint_iff]
      refine this.mono_right (principal_mono.mpr fun y hy ↦
        (⟨hy.1, fun hy' ↦ hy' hy.2⟩ : y ∈ D \ {x | g x ≠ 0}))
    haveI : DiscreteTopology (D ∩ g ⁻¹' {0} : Set ℂ) := discreteTopology_subtype_iff.mpr hdisc
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The complex line `t ↦ x + t (y - x)` through `x` and `y`. -/
private def line (x y : E) (t : ℂ) : E := x + t • (y - x)

private lemma continuous_line (x y : E) : Continuous (line x y) := by
  unfold line; fun_prop

private lemma analyticAt_line (x y : E) (t : ℂ) : AnalyticAt ℂ (line x y) t := by
  unfold line; fun_prop

private lemma convex_preimage_line {W : Set E} (hW : Convex ℝ W) (x y : E) :
    Convex ℝ (line x y ⁻¹' W) := by
  intro a ha b hb u v hu hv huv
  have : line x y (u • a + v • b) = u • line x y a + v • line x y b := by
    simp only [line, smul_add, add_smul, smul_assoc]
    rw [show u • x + u • a • (y - x) + (v • x + v • b • (y - x)) =
      (u + v) • x + (u • a • (y - x) + v • b • (y - x)) by rw [add_smul]; abel, huv, one_smul]
  simp only [mem_preimage, this]
  exact hW ha hb hu hv huv

/-- Restriction to a line: for `g` analytic on a convex open `W` with `g(x) ≠ 0` and `y ∈ W`,
the parameters `t` of the line through `x` and `y` at which `g` does not vanish form the
complement in the convex open `D = {t | x + t (y - x) ∈ W}` of a countable set. -/
private lemma line_data {g : E → F} {W : Set E} (hWo : IsOpen W) (hWc : Convex ℝ W)
    (hg : AnalyticOnNhd ℂ g W) {x : E} (hx : x ∈ W) (hgx : g x ≠ 0) {y : E} (hy : y ∈ W) :
    IsOpen (line x y ⁻¹' W) ∧ Convex ℝ (line x y ⁻¹' W) ∧ (0 : ℂ) ∈ line x y ⁻¹' W ∧
      (1 : ℂ) ∈ line x y ⁻¹' W ∧
      (line x y ⁻¹' W ∩ (g ∘ line x y) ⁻¹' {0}).Countable := by
  have h0 : (0 : ℂ) ∈ line x y ⁻¹' W := by simpa [line] using hx
  have h1 : (1 : ℂ) ∈ line x y ⁻¹' W := by simpa [line] using hy
  refine ⟨hWo.preimage (continuous_line x y), convex_preimage_line hWc x y, h0, h1, ?_⟩
  refine countable_inter_preimage_zero (fun t ht ↦ (hg _ ht).comp (analyticAt_line x y t))
    (convex_preimage_line hWc x y).isPreconnected h0 (by simpa [line] using hgx)

/-- **The nonvanishing locus of an analytic function is path-connected.** If `g` is analytic on a
convex open subset `W` of a complex normed space and does not vanish at some point of `W`, then
`W - {g = 0}` is path-connected. -/
theorem isPathConnected_diff_preimage_zero {g : E → F} {W : Set E} (hWo : IsOpen W)
    (hWc : Convex ℝ W) (hg : AnalyticOnNhd ℂ g W) {x : E} (hx : x ∈ W) (hgx : g x ≠ 0) :
    IsPathConnected (W \ g ⁻¹' {0}) := by
  refine ⟨x, ⟨hx, hgx⟩, fun {y} hy ↦ ?_⟩
  obtain ⟨hDo, hDc, h0, h1, hZ⟩ := line_data hWo hWc hg hx hgx hy.1
  have hJ := joinedIn_zero_one_diff_of_countable hDo hDc h0 h1 hZ
    (fun h ↦ hgx (by simpa [line] using h.2))
    (fun h ↦ hy.2 (by simpa [line] using h.2))
  have := hJ.map (continuous_line x y).continuousOn
  simp only [line, zero_smul, add_zero, one_smul, add_sub_cancel] at this
  refine this.mono ?_
  rintro _ ⟨t, ⟨htW, htZ⟩, rfl⟩
  exact ⟨htW, fun h ↦ htZ ⟨htW, h⟩⟩

/-- **The nonvanishing locus of an analytic function is dense.** If `g` is analytic on a convex
open subset `W` of a complex normed space and does not vanish at some point of `W`, then
`W - {g = 0}` is dense in `W`. -/
theorem subset_closure_diff_preimage_zero {g : E → F} {W : Set E} (hWo : IsOpen W)
    (hWc : Convex ℝ W) (hg : AnalyticOnNhd ℂ g W) {x : E} (hx : x ∈ W) (hgx : g x ≠ 0) :
    W ⊆ closure (W \ g ⁻¹' {0}) := by
  intro y hy
  obtain ⟨hDo, -, -, h1, hZ⟩ := line_data hWo hWc hg hx hgx hy
  have hcl := (hZ.dense_compl ℂ).open_subset_closure_inter hDo h1
  have := (continuous_line x y).continuousWithinAt.mem_closure_image hcl
  simp only [line, one_smul, add_sub_cancel] at this
  refine closure_mono ?_ this
  rintro _ ⟨t, ⟨htW, htZ⟩, rfl⟩
  exact ⟨htW, fun h ↦ htZ ⟨htW, h⟩⟩

/-! ### A topological criterion for connectedness of a complement -/

/-- Let `M` be a preconnected space and `S ⊆ M` with dense complement. If every point has a
neighbourhood `W` with `W - S` preconnected, then `M - S` is preconnected. -/
theorem isPreconnected_compl_of_forall_isPreconnected_diff {M : Type*} [TopologicalSpace M]
    [PreconnectedSpace M] {S : Set M} (hd : Dense Sᶜ)
    (hloc : ∀ p : M, ∃ W ∈ 𝓝 p, IsPreconnected (W \ S)) : IsPreconnected Sᶜ := by
  intro u v hu hv hcov hSu hSv
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  -- the points near which `M - S` lies in `u`, resp. in `v`
  set A : Set M := {p | ∃ W ∈ 𝓝 p, W \ S ⊆ u}
  set B : Set M := {p | ∃ W ∈ 𝓝 p, W \ S ⊆ v}
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.mpr fun p ⟨W, hW, hWu⟩ ↦ ?_
    filter_upwards [eventually_eventually_nhds.mpr hW] with q hq using ⟨W, hq, hWu⟩
  have hBo : IsOpen B := by
    refine isOpen_iff_mem_nhds.mpr fun p ⟨W, hW, hWv⟩ ↦ ?_
    filter_upwards [eventually_eventually_nhds.mpr hW] with q hq using ⟨W, hq, hWv⟩
  have hcovAB : (univ : Set M) ⊆ A ∪ B := by
    intro p _
    obtain ⟨W, hW, hWc⟩ := hloc p
    have hdisj : W \ S ∩ (u ∩ v) = ∅ := by
      refine eq_empty_of_forall_notMem fun q hq ↦ ?_
      have : q ∈ Sᶜ ∩ (u ∩ v) := ⟨hq.1.2, hq.2⟩
      rw [hne] at this
      exact this
    have hcov' : W \ S ⊆ u ∪ v := (diff_subset_compl W S).trans hcov
    by_cases hWu : W \ S ⊆ u
    · exact Or.inl ⟨W, hW, hWu⟩
    · refine Or.inr ⟨W, hW, fun q hq ↦ ?_⟩
      rcases hcov' hq with h | h
      · obtain ⟨r, hr, hru⟩ := not_subset.mp hWu
        obtain ⟨z, hz⟩ := hWc u v hu hv hcov' ⟨q, hq, h⟩ ⟨r, hr, (hcov' hr).resolve_left hru⟩
        rw [hdisj] at hz
        exact hz.elim
      · exact h
  have hAB : (A ∩ B).Nonempty → False := by
    rintro ⟨p, ⟨W₁, hW₁, hW₁u⟩, ⟨W₂, hW₂, hW₂v⟩⟩
    obtain ⟨q, hq, hqS⟩ := hd.inter_open_nonempty (interior (W₁ ∩ W₂)) isOpen_interior
      ⟨p, mem_interior_iff_mem_nhds.mpr (inter_mem hW₁ hW₂)⟩
    have hq' := interior_subset hq
    have : q ∈ Sᶜ ∩ (u ∩ v) := ⟨hqS, hW₁u ⟨hq'.1, hqS⟩, hW₂v ⟨hq'.2, hqS⟩⟩
    rw [hne] at this
    exact this
  have hA : (univ ∩ A).Nonempty := by
    obtain ⟨x, hxS, hxu⟩ := hSu
    rcases hcovAB (mem_univ x) with hx | ⟨W, hW, hWv⟩
    · exact ⟨x, mem_univ x, hx⟩
    · have : x ∈ Sᶜ ∩ (u ∩ v) := ⟨hxS, hxu, hWv ⟨mem_of_mem_nhds hW, hxS⟩⟩
      rw [hne] at this
      exact this.elim
  have hB : (univ ∩ B).Nonempty := by
    obtain ⟨x, hxS, hxv⟩ := hSv
    rcases hcovAB (mem_univ x) with ⟨W, hW, hWu⟩ | hx
    · have : x ∈ Sᶜ ∩ (u ∩ v) := ⟨hxS, hWu ⟨mem_of_mem_nhds hW, hxS⟩, hxv⟩
      rw [hne] at this
      exact this.elim
    · exact ⟨x, mem_univ x, hx⟩
  obtain ⟨p, -, hp⟩ := isPreconnected_univ A B hAo hBo hcovAB hA hB
  exact hAB ⟨p, hp⟩

/-! ### Locally analytic subsets -/

/-- A subset `S` of a topological space `M` is *locally analytic* (for the complex normed space
`E`) if every point `p` lies in the source of an open partial homeomorphism `e : M → E` in which
`S` is the common zero set of a family of `F`-valued functions analytic on the target of `e`. In
particular, an analytic subset of a complex manifold modelled on `E` is locally analytic. -/
def IsLocallyAnalytic (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {M : Type*} [TopologicalSpace M] (S : Set M) :
    Prop :=
  ∀ p : M, ∃ (e : OpenPartialHomeomorph M E) (ι : Type) (g : ι → E → F), p ∈ e.source ∧
    (∀ i, AnalyticOnNhd ℂ (g i) e.target) ∧ ∀ q ∈ e.source, (q ∈ S ↔ ∀ i, g i (e q) = 0)

variable {M : Type*} [TopologicalSpace M] {S : Set M}

/-- Around each point, a ball in the target of a chart. -/
private lemma exists_ball {e : OpenPartialHomeomorph M E} {p : M} (hp : p ∈ e.source) :
    ∃ r > 0, Metric.ball (e p) r ⊆ e.target :=
  Metric.isOpen_iff.mp e.open_target _ (e.map_source hp)

/-- **A proper locally analytic subset has empty interior.** In a preconnected space, a locally
analytic subset `S ≠ M` has dense complement. -/
theorem dense_compl_of_isLocallyAnalytic [PreconnectedSpace M] (hS : IsLocallyAnalytic E F S)
    (hne : S ≠ univ) : Dense Sᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  have hclosed : IsClosed (interior S) := by
    refine closure_subset_iff_isClosed.mp fun p hp ↦ ?_
    obtain ⟨e, ι, g, hp', hg, hSe⟩ := hS p
    obtain ⟨r, hr, hball⟩ := exists_ball hp'
    set V := e.source ∩ e ⁻¹' Metric.ball (e p) r
    have hVo : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
    have hpV : p ∈ V := ⟨hp', Metric.mem_ball_self hr⟩
    obtain ⟨q, hqV, hqN⟩ := mem_closure_iff.mp hp V hVo hpV
    have hNV : IsOpen (interior S ∩ V) := isOpen_interior.inter hVo
    have himg : IsOpen (e '' (interior S ∩ V)) :=
      e.isOpen_image_of_subset_source hNV (inter_subset_right.trans inter_subset_left)
    have hzero : ∀ i, EqOn (g i) 0 (Metric.ball (e p) r) := by
      intro i
      refine ((hg i).mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected hqV.2 ?_
      filter_upwards [himg.mem_nhds ⟨q, ⟨hqN, hqV⟩, rfl⟩]
      rintro _ ⟨q', ⟨hq'N, hq'V⟩, rfl⟩
      exact (hSe q' hq'V.1).mp (interior_subset hq'N) i
    have hVS : V ⊆ S := fun q' hq' ↦ (hSe q' hq'.1).mpr fun i ↦ hzero i hq'.2
    exact interior_maximal hVS hVo hpV
  rcases isClopen_iff.mp ⟨hclosed, isOpen_interior⟩ with h | h
  · exact h
  · exact absurd (eq_univ_of_univ_subset (h ▸ interior_subset)) hne

/-- Near every point, the complement of a proper locally analytic subset of a preconnected space
is preconnected. -/
theorem exists_mem_nhds_isPreconnected_diff [PreconnectedSpace M]
    (hS : IsLocallyAnalytic E F S) (hne : S ≠ univ) (p : M) :
    ∃ W ∈ 𝓝 p, IsPreconnected (W \ S) := by
  have hd := dense_compl_of_isLocallyAnalytic hS hne
  obtain ⟨e, ι, g, hp, hg, hSe⟩ := hS p
  obtain ⟨r, hr, hball⟩ := exists_ball hp
  set V := e.source ∩ e ⁻¹' Metric.ball (e p) r
  have hVo : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
  have hpV : p ∈ V := ⟨hp, Metric.mem_ball_self hr⟩
  refine ⟨V, hVo.mem_nhds hpV, ?_⟩
  obtain ⟨q, hqV, hqS⟩ := hd.inter_open_nonempty V hVo ⟨p, hpV⟩
  obtain ⟨i, hi⟩ : ∃ i, g i (e q) ≠ 0 := by
    by_contra! h
    exact hqS ((hSe q hqV.1).mpr h)
  set P := Metric.ball (e p) r \ g i ⁻¹' {0}
  have hP := isPathConnected_diff_preimage_zero Metric.isOpen_ball (convex_ball _ _)
    ((hg i).mono hball) hqV.2 hi
  have hPt : P ⊆ e.target := diff_subset.trans hball
  have himg : IsPreconnected (e.symm '' P) :=
    hP.isConnected.isPreconnected.image _ (e.continuousOn_symm.mono hPt)
  refine himg.subset_closure ?_ ?_
  · rintro _ ⟨y, ⟨hyB, hyg⟩, rfl⟩
    have hyt := hball hyB
    refine ⟨⟨e.map_target hyt, by simpa [e.right_inv hyt] using hyB⟩, fun hS' ↦ hyg ?_⟩
    have := (hSe _ (e.map_target hyt)).mp hS' i
    rwa [e.right_inv hyt] at this
  · rintro q' ⟨hq'V, -⟩
    have hcl := subset_closure_diff_preimage_zero Metric.isOpen_ball (convex_ball _ _)
      ((hg i).mono hball) hqV.2 hi hq'V.2
    have hcont : ContinuousWithinAt e.symm P (e q') :=
      (e.continuousOn_symm.mono (insert_subset (e.map_source hq'V.1) hPt)).continuousWithinAt
        (mem_insert _ _) |>.mono (subset_insert _ _)
    simpa [e.left_inv hq'V.1] using hcont.mem_closure_image hcl

/-- **The complement of a proper analytic subset is preconnected.** In a preconnected space, the
complement of a locally analytic subset `S ≠ M` is preconnected. -/
theorem isPreconnected_compl_of_isLocallyAnalytic [PreconnectedSpace M]
    (hS : IsLocallyAnalytic E F S) (hne : S ≠ univ) : IsPreconnected Sᶜ :=
  isPreconnected_compl_of_forall_isPreconnected_diff (dense_compl_of_isLocallyAnalytic hS hne)
    (exists_mem_nhds_isPreconnected_diff hS hne)

/-- **The complement of a proper analytic subset of a connected space is connected and dense.** -/
theorem isConnected_compl_of_isLocallyAnalytic [ConnectedSpace M]
    (hS : IsLocallyAnalytic E F S) (hne : S ≠ univ) : IsConnected Sᶜ ∧ Dense Sᶜ :=
  ⟨⟨nonempty_compl.mpr hne, isPreconnected_compl_of_isLocallyAnalytic hS hne⟩,
    dense_compl_of_isLocallyAnalytic hS hne⟩

end MMP.SmoothLocusConnected
