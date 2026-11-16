module

public import MMP.Topology.MetricSpace.Reach
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences from tubes of positive reach

Two elementary facts about homotopy equivalences, used to compare sets of positive reach.

The *two-out-of-six property*: for maps `f : A → B`, `g : B → C`, `h : C → D`, if `g ∘ f` and
`h ∘ g` are homotopy equivalences, then so is `g`. Indeed `v ∘ h` is a left homotopy inverse
of `g` and `f ∘ u` a right one, for homotopy inverses `u` of `g ∘ f` and `v` of `h ∘ g`, and a
map with a left and a right homotopy inverse is a homotopy equivalence.

The *tube lemma*: let `A₁ ⊆ A` be closed subsets of a proper real inner product space, `A` of
reach at least `τ` and `A₁` of reach at least `τ₁`. For `0 < r ≤ min τ τ₁`, the inclusion of
`A₁` into `A ∩ U_r(A₁)`, the points of `A` at distance less than `r` from `A₁`, is a homotopy
equivalence. Its homotopy inverse is the nearest-point map `π₁` of `A₁`; the homotopy moves
`y` along the segment `[π₁ y, y]` and projects back to `A` by the nearest-point map of `A`; the
triangle inequality keeps the projected point within `r` of `π₁ y`.

## Main results

* `MMP.Topology.exists_homotopyEquiv_of_comp_of_comp`: the two-out-of-six property.
* `MMP.Topology.exists_homotopyEquiv_inclusion_inter_thickening`: the tube lemma.
-/

open Set Metric ContinuousMap

namespace MMP.Topology

public section

/-- **Two out of six.** For continuous maps `f : A → B`, `g : B → C`, `h : C → D` such that
`g ∘ f` and `h ∘ g` are homotopy equivalences, `g` is a homotopy equivalence. -/
theorem exists_homotopyEquiv_of_comp_of_comp {A B C D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] (f : C(A, B)) (g : C(B, C))
    (h : C(C, D)) (e₁ : A ≃ₕ C) (he₁ : e₁.toFun = g.comp f) (e₂ : B ≃ₕ D)
    (he₂ : e₂.toFun = h.comp g) : ∃ e : B ≃ₕ C, e.toFun = g := by
  set l : C(C, B) := e₂.invFun.comp h
  set r : C(C, B) := f.comp e₁.invFun
  have hlg : (l.comp g).Homotopic (ContinuousMap.id B) := by
    have : l.comp g = e₂.invFun.comp e₂.toFun := by rw [he₂]; rfl
    rw [this]; exact e₂.left_inv
  have hgr : (g.comp r).Homotopic (ContinuousMap.id C) := by
    have : g.comp r = e₁.toFun.comp e₁.invFun := by rw [he₁]; rfl
    rw [this]; exact e₁.right_inv
  have hrl : r.Homotopic l := by
    have h1 : ((ContinuousMap.id B).comp r).Homotopic ((l.comp g).comp r) :=
      hlg.symm.comp (Homotopic.refl r)
    have h2 : (l.comp (g.comp r)).Homotopic (l.comp (ContinuousMap.id C)) :=
      (Homotopic.refl l).comp hgr
    rw [ContinuousMap.id_comp] at h1
    rw [ContinuousMap.comp_id] at h2
    exact h1.trans h2
  have hgl : (g.comp l).Homotopic (ContinuousMap.id C) :=
    ((Homotopic.refl g).comp hrl.symm).trans hgr
  exact ⟨⟨g, l, hlg, hgl⟩, rfl⟩

/-- A map homotopic to a homotopy equivalence is a homotopy equivalence. -/
theorem exists_homotopyEquiv_of_homotopic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (f : C(X, Y)) (hf : f.Homotopic e.toFun) : ∃ e' : X ≃ₕ Y, e'.toFun = f :=
  ⟨⟨f, e.invFun, ((Homotopic.refl e.invFun).comp hf).trans e.left_inv,
    (hf.comp (Homotopic.refl e.invFun)).trans e.right_inv⟩, rfl⟩

section Inclusion

variable {T : Type*} [TopologicalSpace T]

/-- Inclusions that are homotopy equivalences compose. -/
theorem exists_homotopyEquiv_inclusion_trans {s t u : Set T} (hst : s ⊆ t) (htu : t ⊆ u)
    (h₁ : ∃ e : s ≃ₕ t, e.toFun = ContinuousMap.inclusion hst)
    (h₂ : ∃ e : t ≃ₕ u, e.toFun = ContinuousMap.inclusion htu) :
    ∃ e : s ≃ₕ u, e.toFun = ContinuousMap.inclusion (hst.trans htu) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨e₁.trans e₂, ?_⟩
  change e₂.toFun.comp e₁.toFun = _
  rw [he₁, he₂]
  rfl

/-- **Two out of six for inclusions.** For `s₀ ⊆ s₁ ⊆ s₂ ⊆ s₃`, if the inclusions `s₀ ⊆ s₂` and
`s₁ ⊆ s₃` are homotopy equivalences, so are `s₀ ⊆ s₁` and `s₁ ⊆ s₂`. -/
theorem exists_homotopyEquiv_inclusion_of_two_out_of_six {s₀ s₁ s₂ s₃ : Set T} (h₀₁ : s₀ ⊆ s₁)
    (h₁₂ : s₁ ⊆ s₂) (h₂₃ : s₂ ⊆ s₃)
    (h₀₂ : ∃ e : s₀ ≃ₕ s₂, e.toFun = ContinuousMap.inclusion (h₀₁.trans h₁₂))
    (h₁₃ : ∃ e : s₁ ≃ₕ s₃, e.toFun = ContinuousMap.inclusion (h₁₂.trans h₂₃)) :
    (∃ e : s₀ ≃ₕ s₁, e.toFun = ContinuousMap.inclusion h₀₁) ∧
      ∃ e : s₁ ≃ₕ s₂, e.toFun = ContinuousMap.inclusion h₁₂ := by
  obtain ⟨e₀₂, he₀₂⟩ := h₀₂
  obtain ⟨e₁₃, he₁₃⟩ := h₁₃
  obtain ⟨e₁₂, he₁₂⟩ := exists_homotopyEquiv_of_comp_of_comp (ContinuousMap.inclusion h₀₁)
    (ContinuousMap.inclusion h₁₂) (ContinuousMap.inclusion h₂₃) e₀₂ (by rw [he₀₂]; rfl) e₁₃
    (by rw [he₁₃]; rfl)
  refine ⟨exists_homotopyEquiv_of_homotopic (e₀₂.trans e₁₂.symm) _ ?_, e₁₂, he₁₂⟩
  change (ContinuousMap.inclusion h₀₁).Homotopic (e₁₂.invFun.comp e₀₂.toFun)
  have h1 : e₁₂.invFun.comp e₀₂.toFun =
      (e₁₂.invFun.comp e₁₂.toFun).comp (ContinuousMap.inclusion h₀₁) := by
    rw [he₀₂, he₁₂]; rfl
  rw [h1]
  have := e₁₂.left_inv.symm.comp (Homotopic.refl (ContinuousMap.inclusion h₀₁))
  rwa [ContinuousMap.id_comp] at this

end Inclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- **Tube lemma.** Let `A₁ ⊆ A` be closed, `A` of reach at least `τ` and `A₁` of reach at
least `τ₁`, and `0 < r ≤ min τ τ₁`. Then the inclusion of `A₁` into the points of `A` at
distance less than `r` from `A₁` is a homotopy equivalence. -/
theorem exists_homotopyEquiv_inclusion_inter_thickening {A A₁ : Set E} (hA : IsClosed A)
    (hA₁ : IsClosed A₁) (h₁ : A₁ ⊆ A) {τ τ₁ r : ℝ} (hu : HasUniqueNearestPoints A τ)
    (hu₁ : HasUniqueNearestPoints A₁ τ₁) (hr0 : 0 < r) (hr : r ≤ τ) (hr₁ : r ≤ τ₁) :
    ∃ e : A₁ ≃ₕ (A ∩ thickening r A₁ : Set E),
      e.toFun = ContinuousMap.inclusion (subset_inter h₁ (self_subset_thickening hr0 A₁)) := by
  obtain ⟨π, hπc, hπA, hπn, -⟩ := hu.exists_nearestPoint hA
  obtain ⟨π₁, hπ₁c, hπ₁A, hπ₁n, -⟩ := hu₁.exists_nearestPoint hA₁
  set A₂ : Set E := A ∩ thickening r A₁
  have hsub : A₁ ⊆ A₂ := subset_inter h₁ (self_subset_thickening hr0 A₁)
  have hT₁ : thickening r A₁ ⊆ thickening τ₁ A₁ := thickening_mono hr₁ A₁
  have hfix₁ : ∀ x ∈ A₁, π₁ x = x := fun x hx ↦ by
    have := hπ₁n x (self_subset_thickening (hr0.trans_le hr₁) A₁ hx) x hx
    rw [sub_self, norm_zero] at this
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm
  have hfix : ∀ x ∈ A, π x = x := fun x hx ↦ by
    have := hπn x (self_subset_thickening (hr0.trans_le hr) A hx) x hx
    rw [sub_self, norm_zero] at this
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm
  -- the distance from a point of `A₂` to its nearest point in `A₁` is less than `r`
  have hlt : ∀ y ∈ A₂, ‖y - π₁ y‖ < r := fun y hy ↦ by
    obtain ⟨x, hx, hyx⟩ := mem_thickening_iff.1 hy.2
    rw [dist_eq_norm] at hyx
    exact (hπ₁n y (hT₁ hy.2) x hx).trans_lt hyx
  set z : unitInterval × E → E := fun q ↦ π₁ q.2 + (q.1 : ℝ) • (q.2 - π₁ q.2) with hz
  have hzy : ∀ (t : unitInterval) (y : E), ‖z (t, y) - y‖ = (1 - t) * ‖y - π₁ y‖ := by
    intro t y
    have : z (t, y) - y = (-(1 - (t : ℝ))) • (y - π₁ y) := by simp only [hz]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by simp [t.2.2])]
  have hzp : ∀ (t : unitInterval) (y : E), ‖z (t, y) - π₁ y‖ = t * ‖y - π₁ y‖ := by
    intro t y
    have : z (t, y) - π₁ y = (t : ℝ) • (y - π₁ y) := by simp only [hz]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  have hzT : ∀ (t : unitInterval) (y : E), y ∈ A₂ → z (t, y) ∈ thickening τ A := by
    intro t y hy
    refine mem_thickening_iff.2 ⟨y, hy.1, ?_⟩
    rw [dist_eq_norm, hzy]
    have := hlt y hy
    nlinarith [t.2.1, norm_nonneg (y - π₁ y)]
  have hmem : ∀ (t : unitInterval) (y : E), y ∈ A₂ → π (z (t, y)) ∈ A₂ := by
    intro t y hy
    refine ⟨hπA _ (hzT t y hy), mem_thickening_iff.2 ⟨π₁ y, hπ₁A y (hT₁ hy.2), ?_⟩⟩
    rw [dist_eq_norm]
    have h1 := hπn _ (hzT t y hy) y hy.1
    calc ‖π (z (t, y)) - π₁ y‖ ≤ ‖z (t, y) - π (z (t, y))‖ + ‖z (t, y) - π₁ y‖ := by
          rw [norm_sub_rev (z (t, y))]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖z (t, y) - y‖ + ‖z (t, y) - π₁ y‖ := by
          gcongr
      _ = ‖y - π₁ y‖ := by rw [hzy, hzp]; ring
      _ < r := hlt y hy
  have hπ₁c' : Continuous fun y : A₂ ↦ π₁ y :=
    (hπ₁c.mono (hT₁.trans' inter_subset_right)).restrict
  set p : C(A₂, A₁) := ⟨fun y ↦ ⟨π₁ y, hπ₁A y (hT₁ y.2.2)⟩, hπ₁c'.subtype_mk _⟩
  set i : C(A₁, A₂) := ContinuousMap.inclusion hsub
  have hzc : Continuous fun q : unitInterval × A₂ ↦ z (q.1, q.2) := by
    simp only [hz]
    exact (hπ₁c'.comp continuous_snd).add ((continuous_subtype_val.comp continuous_fst).smul
      ((continuous_subtype_val.comp continuous_snd).sub (hπ₁c'.comp continuous_snd)))
  have hHc : Continuous fun q : unitInterval × A₂ ↦ π (z (q.1, q.2)) :=
    hπc.comp_continuous hzc fun q ↦ hzT q.1 q.2 q.2.2
  refine ⟨⟨i, p, ?_, ?_⟩, rfl⟩
  · have : p.comp i = ContinuousMap.id A₁ :=
      ContinuousMap.ext fun x ↦ Subtype.ext (hfix₁ x x.2)
    rw [this]
  · refine ⟨{ toFun := fun q ↦ ⟨π (z (q.1, q.2)), hmem q.1 q.2 q.2.2⟩
              continuous_toFun := hHc.subtype_mk _
              map_zero_left := fun y ↦ Subtype.ext ?_
              map_one_left := fun y ↦ Subtype.ext ?_ }⟩
    · simp only [hz, Set.Icc.coe_zero, zero_smul, add_zero]
      exact hfix _ (h₁ (hπ₁A y (hT₁ y.2.2)))
    · simp only [hz, Set.Icc.coe_one, one_smul, add_sub_cancel]
      exact hfix _ y.2.1

end

end MMP.Topology
