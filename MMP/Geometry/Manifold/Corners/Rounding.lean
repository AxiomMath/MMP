module

public import MMP.Topology.Collar
public import MMP.Geometry.Manifold.Corners.SublevelReach
public import MMP.Geometry.Manifold.Corners.BoundaryDistance
public import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# The boundary of a compact manifold with corners has a model of positive reach

Let `M` be a compact manifold with corners modelled on the quadrant. We show that its boundary
`∂M` is homotopy equivalent to a compact subset of a Euclidean space of positive reach. This is
corner rounding, done by a sublevel set rather than a level set.

Embed `M` by `e` (Whitney) and smooth the distance `d_B` to `B = e(∂M)` to a function
`ρ̃` with `|ρ̃ - d_B| ≤ ε`, such that `ρ = ρ̃ ∘ e` is regular on a band `δ₁ ≤ ρ ≤ δ₂`
(`MMP.Topology.exists_regular_smoothing_infDist_boundary`). Then `S_δ = e({ρ ≤ δ})` has positive
reach for `δ` in the band, and `S_{δ₁} ⊆ S_{δ₂}` is a homotopy equivalence
(`MMP.Topology.exists_homotopyEquiv_inclusion_image_sublevel`). A collar `c : ∂M × [0, 1) → M`
gives closed collar levels `C_a = c(∂M × [0, a])`, with `C_a ⊆ C_b` a homotopy equivalence and
`∂M ≃ C_0`. The constants are chosen so that `C_a ⊆ S_{δ₁} ⊆ C_b ⊆ S_{δ₂}`; by two out of six
the inclusion `S_{δ₁} ⊆ C_b` is a homotopy equivalence, so `∂M ≃ S_{δ₁}`.

## Main results

* `MMP.Topology.exists_homotopyEquiv_inclusion_collarLevel`: `Z × [0, a] ⊆ Z × [0, b]` is a
  homotopy equivalence.
* `MMP.Topology.exists_homotopyEquiv_inclusion_image`: an embedding carries inclusions that are
  homotopy equivalences to such inclusions.
* `MMP.Topology.exists_isCompact_hasUniqueNearestPoints_homotopyEquiv_boundary`: the boundary of
  a compact manifold with corners is homotopy equivalent to a compact set of positive reach.
-/

open Set Filter Topology Metric Function
open scoped Manifold ContDiff ContinuousMap

namespace MMP.Topology

public section

section Collar

variable {Z : Type*} [TopologicalSpace Z]

/-- The closed collar levels `Z × [0, a] ⊆ Z × [0, b]`, `0 ≤ a ≤ b`, inside `Z × [0, 1)`:
the inclusion is a homotopy equivalence, `Z × [0, a]` being a deformation retract. -/
theorem exists_homotopyEquiv_inclusion_collarLevel {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ e : {q : Z × Ico (0 : ℝ) 1 | (q.2 : ℝ) ≤ a} ≃ₕ {q : Z × Ico (0 : ℝ) 1 | (q.2 : ℝ) ≤ b},
      e.toFun = ContinuousMap.inclusion (ofPred_subset_ofPred.2 fun _ hq ↦ hq.trans hab) := by
  set Pa := {q : Z × Ico (0 : ℝ) 1 | (q.2 : ℝ) ≤ a}
  set Pb := {q : Z × Ico (0 : ℝ) 1 | (q.2 : ℝ) ≤ b}
  have hsub : Pa ⊆ Pb := ofPred_subset_ofPred.2 fun _ hq ↦ hq.trans hab
  have hm : ∀ q : Pb, min (q.1.2 : ℝ) a ∈ Ico (0 : ℝ) 1 := fun q ↦
    ⟨le_min q.1.2.2.1 ha, (min_le_left _ _).trans_lt q.1.2.2.2⟩
  have hc2 : Continuous fun q : Pb ↦ (q.1.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hc1 : Continuous fun q : Pb ↦ q.1.1 := continuous_fst.comp continuous_subtype_val
  let r : C(Pb, Pa) := ⟨fun q ↦ ⟨(q.1.1, ⟨min q.1.2 a, hm q⟩),
      show min _ a ≤ a from min_le_right _ _⟩,
    (hc1.prodMk ((hc2.min continuous_const).subtype_mk _)).subtype_mk _⟩
  have hmem : ∀ (s : unitInterval) (q : Pb),
      (1 - (s : ℝ)) * min (q.1.2 : ℝ) a + s * q.1.2 ∈ Ico (0 : ℝ) 1 ∧
        (1 - (s : ℝ)) * min (q.1.2 : ℝ) a + s * q.1.2 ≤ q.1.2 := fun s q ↦ by
    have hle : (1 - (s : ℝ)) * min (q.1.2 : ℝ) a + s * q.1.2 ≤ q.1.2 := by
      nlinarith [s.2.2, min_le_left (q.1.2 : ℝ) a]
    exact ⟨⟨by nlinarith [q.1.2.2.1, s.2.1, s.2.2, le_min q.1.2.2.1 ha],
      hle.trans_lt q.1.2.2.2⟩, hle⟩
  refine ⟨⟨ContinuousMap.inclusion hsub, r, ?_, ?_⟩, rfl⟩
  · rw [show r.comp (ContinuousMap.inclusion hsub) = ContinuousMap.id Pa by
      ext q
      · rfl
      · exact min_eq_left q.2]
  · refine ⟨{ toFun := fun p ↦ ⟨(p.2.1.1, ⟨_, (hmem p.1 p.2).1⟩),
                (hmem p.1 p.2).2.trans p.2.2⟩
              continuous_toFun := ?_
              map_zero_left := fun q ↦ ?_
              map_one_left := fun q ↦ ?_ }⟩
    · have hs : Continuous fun p : unitInterval × Pb ↦ (p.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      exact ((hc1.comp continuous_snd).prodMk ((((continuous_const.sub hs).mul
        ((hc2.comp continuous_snd).min continuous_const)).add
        (hs.mul (hc2.comp continuous_snd))).subtype_mk _)).subtype_mk _
    · ext
      · rfl
      · simp [r]
    · ext
      · rfl
      · simp

/-- An embedding `g` carries an inclusion `s ⊆ t` which is a homotopy equivalence to the
inclusion `g '' s ⊆ g '' t`, again a homotopy equivalence. -/
theorem exists_homotopyEquiv_inclusion_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hg : IsEmbedding g) {s t : Set X} (hst : s ⊆ t)
    (h : ∃ e : s ≃ₕ t, e.toFun = ContinuousMap.inclusion hst) :
    ∃ e : (g '' s) ≃ₕ (g '' t), e.toFun = ContinuousMap.inclusion (image_mono hst) := by
  obtain ⟨e, he⟩ := h
  set hs := hg.homeomorphImage s
  set ht := hg.homeomorphImage t
  refine ⟨hs.symm.toHomotopyEquiv.trans (e.trans ht.toHomotopyEquiv), ?_⟩
  ext y
  change ((ht (e.toFun (hs.symm y)) : g '' t) : Y) = y
  rw [he]
  exact congrArg Subtype.val (hs.apply_symm_apply y)

/-- Small collar levels `c(Z × [0, b])` of a collar `c` of a compact `Z` lie in any open set
containing `c(Z × {0})`. -/
theorem exists_image_collarLevel_subset [CompactSpace Z] {X : Type*} [TopologicalSpace X]
    {c : Z × Ico (0 : ℝ) 1 → X} (hc : Continuous c) {U : Set X} (hU : IsOpen U)
    (hZU : ∀ x, c (x, ⟨0, by norm_num⟩) ∈ U) :
    ∃ b ∈ Ioo (0 : ℝ) 1, c '' {q | (q.2 : ℝ) ≤ b} ⊆ U := by
  have hev : ∀ᶠ t in 𝓝 (⟨0, by norm_num⟩ : Ico (0 : ℝ) 1), ∀ x ∈ (univ : Set Z),
      c (x, t) ∈ U := by
    refine (isCompact_univ : IsCompact (univ : Set Z)).eventually_forall_of_forall_eventually
      (P := fun (t : Ico (0 : ℝ) 1) (x : Z) ↦ c (x, t) ∈ U) fun x _ ↦ ?_
    refine (hc.comp continuous_swap).continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    exact hZU x
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min (ε / 2) (1 / 2), ⟨by positivity, by
    linarith [min_le_right (ε / 2) (1 / 2)]⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  refine hεU ?_ q.1 (mem_univ _)
  rw [Subtype.dist_eq]
  change dist (q.2 : ℝ) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg q.2.2.1]
  have : (q.2 : ℝ) ≤ min (ε / 2) (1 / 2) := hq
  linarith [min_le_left (ε / 2) (1 / 2)]

/-- A set `s₁` between two collar levels `g(Z × [0, a]) ⊆ s₁ ⊆ g(Z × [0, b])` of an embedded
collar `g`, whose inclusion into a set `s₃ ⊇ g(Z × [0, b])` is a homotopy equivalence, is
homotopy equivalent to `Z`. -/
theorem nonempty_homotopyEquiv_of_subset_collarLevel {Y : Type*} [TopologicalSpace Y]
    {g : Z × Ico (0 : ℝ) 1 → Y} (hg : IsEmbedding g) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {s₁ s₃ : Set Y} (h01 : g '' {q | (q.2 : ℝ) ≤ a} ⊆ s₁)
    (h12 : s₁ ⊆ g '' {q | (q.2 : ℝ) ≤ b}) (h23 : g '' {q | (q.2 : ℝ) ≤ b} ⊆ s₃)
    (h13 : ∃ e : s₁ ≃ₕ s₃, e.toFun = ContinuousMap.inclusion (h12.trans h23)) :
    Nonempty (Z ≃ₕ s₁) := by
  set P : ℝ → Set (Z × Ico (0 : ℝ) 1) := fun t ↦ {q | (q.2 : ℝ) ≤ t}
  have hPmono : ∀ {a b : ℝ}, a ≤ b → P a ⊆ P b := fun hab ↦
    ofPred_subset_ofPred.2 fun _ hq ↦ hq.trans hab
  have h02 : ∃ e' : (g '' P a) ≃ₕ (g '' P b), e'.toFun = ContinuousMap.inclusion (h01.trans h12) :=
    exists_homotopyEquiv_inclusion_image hg (hPmono hab)
      (exists_homotopyEquiv_inclusion_collarLevel ha hab)
  obtain ⟨-, e₁₂, -⟩ := exists_homotopyEquiv_inclusion_of_two_out_of_six h01 h12 h23 h02 h13
  have hP0 : ∀ q ∈ P 0, (q.2 : ℝ) = 0 := fun q hq ↦ le_antisymm hq q.2.2.1
  let ι : Z ≃ₜ P 0 :=
    { toFun := fun x ↦ ⟨(x, ⟨0, by norm_num⟩), (le_refl (0 : ℝ))⟩
      invFun := fun q ↦ q.1.1
      left_inv := fun x ↦ rfl
      right_inv := fun q ↦ by
        ext
        · rfl
        · exact (hP0 q.1 q.2).symm
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  obtain ⟨e₀₂, -⟩ := exists_homotopyEquiv_inclusion_image hg (hPmono (ha.trans hab))
    (exists_homotopyEquiv_inclusion_collarLevel le_rfl (ha.trans hab))
  exact ⟨((ι.trans (hg.homeomorphImage (P 0))).toHomotopyEquiv.trans e₀₂).trans e₁₂.symm⟩

end Collar

section Sublevel

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- If a continuous `f` on a compact space is positive off `B`, then every open neighbourhood
of `B` contains a sublevel set `{f ≤ s}` with `s > 0`. -/
theorem exists_pos_sublevel_subset {f : X → ℝ} (hf : Continuous f) {B U : Set X}
    (hpos : ∀ p ∉ B, 0 < f p) (hU : IsOpen U) (hBU : B ⊆ U) :
    ∃ s > 0, {p | f p ≤ s} ⊆ U := by
  rcases eq_empty_or_nonempty Uᶜ with hUe | hUne
  · exact ⟨1, one_pos, fun p _ ↦ by simpa using congrArg (p ∈ ·) hUe⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hUne hf.continuousOn
  have h₀ : 0 < f p₀ := hpos p₀ fun h ↦ hp₀ (hBU h)
  refine ⟨f p₀ / 2, half_pos h₀, fun p hp ↦ ?_⟩
  by_contra hpU
  have := hmin hpU
  simp only [mem_ofPred_eq] at hp this
  linarith

/-- For a collar `c` of a set `B` in a compact space and a continuous `f` vanishing exactly on
`B`, every `D > 0` admits a collar level `c(B × [0, b])` inside `{f < D / 2}` and containing a
sublevel set `{f ≤ s}`, `0 < s ≤ D`. -/
theorem exists_collarLevel_between_sublevels {B : Set X} [CompactSpace B]
    {c : B × Ico (0 : ℝ) 1 → X} (hc : IsOpenEmbedding c)
    (hc0 : ∀ x (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x) {f : X → ℝ} (hf : Continuous f)
    (hf0 : ∀ p ∈ B, f p = 0) (hfpos : ∀ p ∉ B, 0 < f p) {D : ℝ} (hD : 0 < D) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∃ s, 0 < s ∧ s ≤ D ∧ c '' {q | (q.2 : ℝ) ≤ b} ⊆ {p | f p < D / 2} ∧
      {p | f p ≤ s} ⊆ c '' {q | (q.2 : ℝ) ≤ b} := by
  obtain ⟨b, hb, hbU⟩ := exists_image_collarLevel_subset (U := {p | f p < D / 2})
    hc.continuous (isOpen_lt hf continuous_const) fun x ↦ by
      rw [hc0 x ⟨0, by norm_num⟩ rfl]
      exact show f x < D / 2 by linarith [hf0 x x.2]
  obtain ⟨s, hs, hsU⟩ := exists_pos_sublevel_subset (U := c '' {q | (q.2 : ℝ) < b}) hf hfpos
    (hc.isOpenMap _ (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const))
    fun p hp ↦ ⟨(⟨p, hp⟩, ⟨0, by norm_num⟩), (show (0 : ℝ) < b from hb.1), hc0 _ _ rfl⟩
  refine ⟨b, hb, min s D, lt_min hs hD, min_le_right _ _, hbU, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, rfl⟩ := hsU ((show f p ≤ min s D from hp).trans (min_le_left _ _))
  exact ⟨q, (show (q.2 : ℝ) < b from hq).le, rfl⟩

end Sublevel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

/-- Given an embedding `e` of a compact manifold with corners and a collar `c` of its nonempty
boundary, there is a `C²` function `ρ`, regular on a band `δ₁ ≤ ρ ≤ δ₂`, whose sublevel set
`{ρ ≤ δ₁}` lies between two collar levels `c(∂M × [0, a]) ⊆ {ρ ≤ δ₁} ⊆ c(∂M × [0, b])`, the
larger of which lies in `{ρ ≤ δ₂}`. -/
theorem exists_regularBand_sublevel_between_collarLevels
    [IsManifold (modelWithCornersEuclideanQuadrant n) 2 M] [CompactSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e)
    (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective
      (mfderiv (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e x))
    (hBne : ((modelWithCornersEuclideanQuadrant n).boundary M).Nonempty)
    {c : (modelWithCornersEuclideanQuadrant n).boundary M × Ico (0 : ℝ) 1 → M}
    (hc : IsOpenEmbedding c) (hc0 : ∀ x (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x) :
    ∃ (ρ : M → ℝ) (δ₁ δ₂ a b : ℝ), ContMDiff (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ) 2 ρ ∧
      RegularBand (modelWithCornersEuclideanQuadrant n) e ρ δ₁ δ₂ ∧ δ₁ ≤ δ₂ ∧ 0 ≤ a ∧ a ≤ b ∧
      c '' {q | (q.2 : ℝ) ≤ a} ⊆ {p | ρ p ≤ δ₁} ∧ {p | ρ p ≤ δ₁} ⊆ c '' {q | (q.2 : ℝ) ≤ b} ∧
      c '' {q | (q.2 : ℝ) ≤ b} ⊆ {p | ρ p ≤ δ₂} := by
  have hBcl : IsClosed ((modelWithCornersEuclideanQuadrant n).boundary M) :=
    ModelWithCorners.isClosed_boundary (n := 2) (by norm_num)
  have : CompactSpace ((modelWithCornersEuclideanQuadrant n).boundary M) :=
    isCompact_iff_compactSpace.1 hBcl.isCompact
  set B' := e '' (modelWithCornersEuclideanQuadrant n).boundary M with hB'
  have hB'c : IsCompact B' := hBcl.isCompact.image hemb.continuous
  set f : M → ℝ := fun p ↦ infDist (e p) B' with hf
  have hfc : Continuous f := (continuous_infDist_pt B').comp hemb.continuous
  have hf0 : ∀ p ∈ (modelWithCornersEuclideanQuadrant n).boundary M, f p = 0 :=
    fun p hp ↦ infDist_zero_of_mem ⟨p, hp, rfl⟩
  have hfpos : ∀ p, p ∉ (modelWithCornersEuclideanQuadrant n).boundary M →
      0 < f p := by
    intro p hp
    refine lt_of_le_of_ne infDist_nonneg fun h ↦ hp ?_
    obtain ⟨q, hq, hqp⟩ := (hB'c.isClosed.mem_iff_infDist_zero (hBne.image e)).2 h.symm
    rwa [← hemb.injective hqp]
  obtain ⟨D₀, hD₀, hG⟩ := exists_regular_smoothing_infDist_boundary he hemb hinj
  obtain ⟨b, hb, s', hs'0, hs'D, hbU, hsU⟩ :=
    exists_collarLevel_between_sublevels hc hc0 hfc hf0 hfpos hD₀
  obtain ⟨ε₀, hε₀, hρex⟩ := hG (s' / 4) (by positivity)
  set ε := min ε₀ (min (s' / 8) (D₀ / 4)) with hε
  have hε0 : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ s' / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ D₀ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ', hρ'c, hρ'd, hρ'reg⟩ := hρex ε hε0 (min_le_left _ _)
  set ρ : M → ℝ := ρ' ∘ e with hρ
  have hρf : ∀ p, |ρ p - f p| ≤ ε := fun p ↦ hρ'd (e p)
  set δ₁ := s' / 2 with hδ₁
  set δ₂ := D₀ / 2 + ε with hδ₂
  obtain ⟨a, ha, haU⟩ := exists_image_collarLevel_subset (U := {p | f p < δ₁ - ε})
    hc.continuous (isOpen_lt hfc continuous_const) fun x ↦ by
      rw [hc0 x ⟨0, by norm_num⟩ rfl]
      exact show f x < δ₁ - ε by linarith [hf0 x x.2]
  have hband : RegularBand (modelWithCornersEuclideanQuadrant n) e ρ δ₁ δ₂ := fun p hp ↦ by
    have h1 := abs_le.1 (hρf p)
    exact hρ'reg p ⟨by linarith [hp.1], by linarith [hp.2]⟩
  refine ⟨ρ, δ₁, δ₂, min a b, b, hρ'c.comp_contMDiff he, hband,
    by linarith, le_min ha.1.le hb.1.le, min_le_right a b, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hqa : c q ∈ {p | f p < δ₁ - ε} :=
      haU ⟨q, (show (q.2 : ℝ) ≤ min a b from hq).trans (min_le_left a b), rfl⟩
    have h1 := abs_le.1 (hρf (c q))
    exact (show ρ (c q) ≤ δ₁ by simp only [mem_ofPred_eq] at hqa; linarith)
  · intro p hp
    have h1 := abs_le.1 (hρf p)
    simp only [mem_ofPred_eq] at hp
    exact hsU (show f p ≤ s' by linarith)
  · rintro _ ⟨q, hq, rfl⟩
    have hqb : c q ∈ {p | f p < D₀ / 2} := hbU ⟨q, hq, rfl⟩
    have h1 := abs_le.1 (hρf (c q))
    exact (show ρ (c q) ≤ δ₂ by simp only [mem_ofPred_eq] at hqb; linarith)

/-- **Corner rounding, up to homotopy.** The boundary of a compact smooth manifold with corners
modelled on the quadrant is homotopy equivalent to a compact subset of a Euclidean space of
positive reach. -/
theorem exists_isCompact_hasUniqueNearestPoints_homotopyEquiv_boundary
    [IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M] [CompactSpace M] [T2Space M] :
    ∃ (N : ℕ) (A : Set (EuclideanSpace ℝ (Fin N))), IsCompact A ∧
      (∃ τ > 0, HasUniqueNearestPoints A τ) ∧
      Nonempty ((modelWithCornersEuclideanQuadrant n).boundary M ≃ₕ A) := by
  set I := modelWithCornersEuclideanQuadrant n
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by norm_cast)
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  have he2 : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e := he.of_le (by norm_cast)
  set Bd := I.boundary M
  have hBcl : IsClosed Bd :=
    ModelWithCorners.isClosed_boundary (I := I) (M := M) (n := ∞) (by simp)
  rcases eq_empty_or_nonempty Bd with hBe | hBne
  · refine ⟨0, ∅, isCompact_empty, ⟨1, one_pos, fun y hy ↦ by simp at hy⟩, ?_⟩
    have : IsEmpty Bd := isEmpty_coe_sort.2 hBe
    exact ⟨Homeomorph.empty.toHomotopyEquiv⟩
  obtain ⟨c, hc, hc0⟩ : ∃ c : Bd × Ico (0 : ℝ) 1 → M,
      IsOpenEmbedding c ∧ ∀ x (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x :=
    exists_collar_of_locallyCollared hBcl fun x hx ↦
      exists_localCollar_boundary (k := ∞) (by simp) hx
  obtain ⟨ρ, δ₁, δ₂, a, b, hρ, hband, hδ₁₂, ha, hab, h01, h12, h23⟩ :=
    exists_regularBand_sublevel_between_collarLevels he2 hemb.isEmbedding hinj hBne hc hc0
  have h01' : (e ∘ c) '' {q | (q.2 : ℝ) ≤ a} ⊆ e '' {p | ρ p ≤ δ₁} := by
    rw [image_comp]
    exact image_mono h01
  have h12' : e '' {p | ρ p ≤ δ₁} ⊆ (e ∘ c) '' {q | (q.2 : ℝ) ≤ b} := by
    rw [image_comp]
    exact image_mono h12
  have h23' : (e ∘ c) '' {q | (q.2 : ℝ) ≤ b} ⊆ e '' {p | ρ p ≤ δ₂} := by
    rw [image_comp]
    exact image_mono h23
  obtain ⟨τ, hτ, hu⟩ :=
    exists_hasUniqueNearestPoints_image_sublevel he2 hemb.isEmbedding hinj hρ hband
  exact ⟨N, _, ((isClosed_le hρ.continuous continuous_const).isCompact).image hemb.continuous,
    ⟨τ, hτ, hu δ₁ ⟨le_rfl, hδ₁₂⟩⟩, nonempty_homotopyEquiv_of_subset_collarLevel
      (hemb.isEmbedding.comp hc.isEmbedding) ha hab h01' h12' h23'
      (exists_homotopyEquiv_inclusion_image_sublevel he2 hemb.isEmbedding hinj hρ hband hδ₁₂)⟩

end

end MMP.Topology
