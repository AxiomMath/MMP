module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Filling the boundary of a simplex through a contraction

For a finite set `s` of indices, `Δ s ⊆ (ι → ℝ)` is the standard simplex on `s` (nonnegative
weights supported in `s` with sum `1`) and `∂Δ s` its boundary (some weight in `s` vanishes). A
point `t ∈ Δ s` other than the barycentre `b` is `t = (1 - λ) b + λ p` with `p ∈ ∂Δ s`, where
`λ = 1 - |s| · min_s t`. Given `g : ∂Δ s → W` and a contraction `H` of `W` (from the identity at
time `0` to the constant `c` at time `1`), the *cone filling* `t ↦ H(1 - λ, g p)` (and `c` at `b`)
is a continuous extension of `g` to `Δ s` with values in `W`.

## Main definitions

* `MMP.ConeFill.face`: the simplex `Δ s`.
* `MMP.ConeFill.boundary`: its boundary `∂Δ s`.
* `MMP.ConeFill.fill`: the cone filling.

## Main results

* `MMP.ConeFill.continuousOn_fill`: the cone filling is continuous on `Δ s`.
* `MMP.ConeFill.fill_eq_of_mem_boundary`: it extends `g`.
* `MMP.ConeFill.mapsTo_fill`: it takes values in `W`.
-/

@[expose] public section

open Set Topology Filter

namespace MMP

namespace ConeFill

variable {ι E : Type*} [TopologicalSpace E]

open scoped Classical

/-- The standard simplex on a finite set `s` of indices. -/
def face (s : Finset ι) : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ (∀ i ∉ s, t i = 0) ∧ ∑ i ∈ s, t i = 1}

/-- The boundary of the standard simplex on `s`: the points with a vanishing weight in `s`. -/
def boundary (s : Finset ι) : Set (ι → ℝ) :=
  {t | t ∈ face s ∧ ∃ i ∈ s, t i = 0}

/-- The smallest weight in `s`. -/
noncomputable def minWeight (s : Finset ι) (t : ι → ℝ) : ℝ :=
  if hs : s.Nonempty then s.inf' hs t else 0

/-- `λ = 1 - |s| · min_s t`: `1` on the boundary, `0` at the barycentre. -/
noncomputable def radius (s : Finset ι) (t : ι → ℝ) : ℝ :=
  1 - s.card * minWeight s t

/-- The radial projection from the barycentre to the boundary. -/
noncomputable def push (s : Finset ι) (t : ι → ℝ) : ι → ℝ :=
  fun i ↦ if i ∈ s then (t i - minWeight s t) / radius s t else 0

/-- The cone filling of `g` through `H`: `t ↦ H(1 - λ, g(push t))`, and `c` at the barycentre. -/
noncomputable def fill (s : Finset ι) (g : (ι → ℝ) → E) (H : ℝ → E → E) (c : E)
    (t : ι → ℝ) : E :=
  if radius s t = 0 then c else H (1 - radius s t) (g (push s t))

/-- The boundary of the simplex is contained in the simplex. -/
theorem boundary_subset_face (s : Finset ι) : boundary s ⊆ face s := fun _ h ↦ h.1

/-- The simplex `Δ s` is closed in `ι → ℝ`. -/
theorem isClosed_face (s : Finset ι) : IsClosed (face s) := by
  simp only [face, ofPred_and, ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i))
    (IsClosed.inter (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply i) continuous_const) ?_)
  exact isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const

/-- Every weight of a point of `Δ s` lies in `[0, 1]`. -/
theorem face_subset_pi (s : Finset ι) : face s ⊆ univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
  intro t ht i _
  refine ⟨ht.1 i, ?_⟩
  by_cases hi : i ∈ s
  · rw [← ht.2.2]
    exact Finset.single_le_sum (fun j _ ↦ ht.1 j) hi
  · exact (ht.2.1 i hi).le.trans zero_le_one

/-- The simplex `Δ s` is compact. -/
theorem isCompact_face (s : Finset ι) : IsCompact (face s) :=
  (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset (isClosed_face s)
    (face_subset_pi s)

/-- The boundary `∂Δ s` is closed in `ι → ℝ`. -/
theorem isClosed_boundary (s : Finset ι) : IsClosed (boundary s) := by
  have : boundary s = face s ∩ ⋃ i ∈ s, {t : ι → ℝ | t i = 0} := by
    ext t
    simp [boundary]
  rw [this]
  exact (isClosed_face s).inter (isClosed_biUnion_finset fun i _ ↦
    isClosed_eq (continuous_apply i) continuous_const)

/-- The boundary `∂Δ s` is compact. -/
theorem isCompact_boundary (s : Finset ι) : IsCompact (boundary s) :=
  (isCompact_face s).of_isClosed_subset (isClosed_boundary s) (boundary_subset_face s)

/-- The boundary is the union of the faces opposite to the vertices. -/
theorem boundary_eq_biUnion (s : Finset ι) :
    boundary s = ⋃ i ∈ s, face (s.erase i) := by
  ext t
  simp only [boundary, mem_ofPred_eq, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨ht, i, hi, hti⟩
    refine ⟨i, hi, ht.1, fun j hj ↦ ?_, ?_⟩
    · rcases eq_or_ne j i with rfl | hji
      · exact hti
      · exact ht.2.1 j fun h ↦ hj (Finset.mem_erase.2 ⟨hji, h⟩)
    · rw [← ht.2.2, ← Finset.sum_erase_add _ _ hi, hti, add_zero]
  · rintro ⟨i, hi, ht⟩
    have hti : t i = 0 := ht.2.1 i (Finset.notMem_erase i s)
    refine ⟨⟨ht.1, fun j hj ↦ ht.2.1 j fun h ↦ hj (Finset.mem_of_mem_erase h), ?_⟩, i, hi, hti⟩
    rw [← Finset.sum_erase_add _ _ hi, hti, add_zero]
    exact ht.2.2

variable {s : Finset ι}

/-- The smallest weight in `s` is at most each weight `t i` with `i ∈ s`. -/
theorem minWeight_le {t : ι → ℝ} {i : ι} (hi : i ∈ s) : minWeight s t ≤ t i := by
  rw [minWeight, dite_cond_eq_true (eq_true ⟨i, hi⟩)]
  exact Finset.inf'_le _ hi

/-- The smallest weight of a point of `Δ s` is nonnegative. -/
theorem minWeight_nonneg {t : ι → ℝ} (ht : t ∈ face s) : 0 ≤ minWeight s t := by
  unfold minWeight
  split_ifs with hs
  · exact (Finset.le_inf'_iff hs _).2 fun i _ ↦ ht.1 i
  · exact le_rfl

/-- For nonempty `s`, the smallest weight in `s` is attained at some index of `s`. -/
theorem exists_eq_minWeight (hs : s.Nonempty) (t : ι → ℝ) : ∃ i ∈ s, t i = minWeight s t := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_inf' hs t
  exact ⟨i, hi, by simp only [minWeight, hs, ↓reduceDIte, h]⟩

/-- For a point of `Δ s`, `|s| · min_s t ≤ 1`. -/
theorem card_mul_minWeight_le {t : ι → ℝ} (ht : t ∈ face s) : s.card * minWeight s t ≤ 1 := by
  rw [← ht.2.2, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i hi ↦ minWeight_le hi

/-- The radius of a point of `Δ s` is nonnegative. -/
theorem radius_nonneg {t : ι → ℝ} (ht : t ∈ face s) : 0 ≤ radius s t :=
  sub_nonneg.2 (card_mul_minWeight_le ht)

/-- The radius of a point of `Δ s` is at most `1`. -/
theorem radius_le_one {t : ι → ℝ} (ht : t ∈ face s) : radius s t ≤ 1 :=
  sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (minWeight_nonneg ht))

/-- The smallest weight of a point of `∂Δ s` is `0`. -/
theorem minWeight_eq_zero_of_mem_boundary {t : ι → ℝ} (ht : t ∈ boundary s) :
    minWeight s t = 0 := by
  obtain ⟨i, hi, hti⟩ := ht.2
  exact le_antisymm (hti ▸ minWeight_le hi) (minWeight_nonneg ht.1)

/-- The radius of a point of `∂Δ s` is `1`. -/
theorem radius_eq_one_of_mem_boundary {t : ι → ℝ} (ht : t ∈ boundary s) : radius s t = 1 := by
  rw [radius, minWeight_eq_zero_of_mem_boundary ht, mul_zero, sub_zero]

/-- The radial projection fixes every point of `∂Δ s`. -/
theorem push_eq_self_of_mem_boundary {t : ι → ℝ} (ht : t ∈ boundary s) : push s t = t := by
  funext i
  simp only [push, radius_eq_one_of_mem_boundary ht, minWeight_eq_zero_of_mem_boundary ht,
    sub_zero, div_one]
  split_ifs with hi
  · rfl
  · exact (ht.1.2.1 i hi).symm

/-- The radial projection maps a point of `Δ s` with nonzero radius into `∂Δ s`. -/
theorem push_mem_boundary {t : ι → ℝ} (ht : t ∈ face s) (hr : radius s t ≠ 0) :
    push s t ∈ boundary s := by
  have hr' : 0 < radius s t := lt_of_le_of_ne (radius_nonneg ht) (Ne.symm hr)
  have hs : s.Nonempty := Finset.nonempty_of_sum_ne_zero (f := t) (by simp [ht.2.2])
  refine ⟨⟨fun i ↦ ?_, fun i hi ↦ by simp [push, hi], ?_⟩, ?_⟩
  · unfold push
    split_ifs with hi
    · exact div_nonneg (sub_nonneg.2 (minWeight_le hi)) hr'.le
    · exact le_rfl
  · have : ∑ i ∈ s, push s t i = ∑ i ∈ s, (t i - minWeight s t) / radius s t :=
      Finset.sum_congr rfl fun i hi ↦ by simp [push, hi]
    simp_rw [div_eq_mul_inv] at this
    rw [this, ← Finset.sum_mul, Finset.sum_sub_distrib, ht.2.2, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hr
  · obtain ⟨i, hi, h⟩ := exists_eq_minWeight hs t
    exact ⟨i, hi, by simp [push, hi, h]⟩

/-- The smallest weight in `s` depends continuously on the point. -/
theorem continuous_minWeight (s : Finset ι) : Continuous (minWeight s) := by
  by_cases hs : s.Nonempty
  · rw [show minWeight s = fun t ↦ s.inf' hs fun i ↦ t i from
      funext fun _ ↦ dite_cond_eq_true (eq_true hs)]
    exact Continuous.finset_inf'_apply hs fun i _ ↦ continuous_apply i
  · rw [show minWeight s = fun _ ↦ 0 from funext fun _ ↦ dite_cond_eq_false (eq_false hs)]
    exact continuous_const

/-- The radius depends continuously on the point. -/
theorem continuous_radius (s : Finset ι) : Continuous (radius s) :=
  continuous_const.sub (continuous_const.mul (continuous_minWeight s))

/-- The radial projection is continuous at every point of nonzero radius. -/
theorem continuousAt_push {t : ι → ℝ} (hr : radius s t ≠ 0) : ContinuousAt (push s) t := by
  refine continuousAt_pi.2 fun i ↦ ?_
  by_cases hi : i ∈ s
  · simp only [push, hi, ↓reduceIte]
    exact (((continuous_apply i).sub (continuous_minWeight s)).continuousAt).div
      (continuous_radius s).continuousAt hr
  · simp only [push, hi, ↓reduceIte]
    exact continuousAt_const

variable {g : (ι → ℝ) → E} {H : ℝ → E → E} {c : E} {W : Set E}

omit [TopologicalSpace E] in
/-- If `H 0` is the identity on `W` and `g` maps `∂Δ s` into `W`, the cone filling agrees with
`g` on `∂Δ s`. -/
theorem fill_eq_of_mem_boundary (hH0 : ∀ y ∈ W, H 0 y = y) (hgW : MapsTo g (boundary s) W)
    {t : ι → ℝ} (ht : t ∈ boundary s) : fill s g H c t = g t := by
  simp [fill, radius_eq_one_of_mem_boundary ht, push_eq_self_of_mem_boundary ht, hH0 _ (hgW ht)]

omit [TopologicalSpace E] in
/-- If `H` preserves `W` at all times in `[0, 1]`, `c ∈ W` and `g` maps `∂Δ s` into `W`, the cone
filling maps `Δ s` into `W`. -/
theorem mapsTo_fill (hHW : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ W, H τ y ∈ W) (hc : c ∈ W)
    (hgW : MapsTo g (boundary s) W) : MapsTo (fill s g H c) (face s) W := by
  intro t ht
  unfold fill
  split_ifs with hr
  · exact hc
  · exact hHW _ ⟨by linarith [radius_le_one ht], by linarith [radius_nonneg ht]⟩ _
      (hgW (push_mem_boundary ht hr))

/-- The cone filling is continuous within `Δ s` at the barycentre, where the radius vanishes. -/
theorem continuousWithinAt_fill_of_radius_eq_zero (hg : ContinuousOn g (boundary s))
    (hgW : MapsTo g (boundary s) W) (hH : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ W))
    (hH1 : ∀ y ∈ W, H 1 y = c) {t₀ : ι → ℝ} (hr : radius s t₀ = 0) :
    ContinuousWithinAt (fill s g H c) (face s) t₀ := by
  have hval : fill s g H c t₀ = c := by rw [fill, ite_cond_eq_true _ _ (eq_true hr)]
  rw [ContinuousWithinAt, hval]
  intro V hV
  have hP : ∀ y ∈ g '' boundary s, ∀ᶠ z : ℝ × E in 𝓝 ((1 : ℝ), y),
      z.1 ∈ Icc (0 : ℝ) 1 → z.2 ∈ W → H z.1 z.2 ∈ V := by
    rintro _ ⟨p, hp, rfl⟩
    have := hH (1, g p) ⟨⟨zero_le_one, le_rfl⟩, hgW hp⟩
    rw [ContinuousWithinAt, Function.uncurry_apply_pair, hH1 _ (hgW hp)] at this
    have h₂ := this hV
    rw [Filter.mem_map, mem_nhdsWithin_iff_eventually] at h₂
    exact h₂.mono fun z hz h₁ h₂ ↦ hz ⟨h₁, h₂⟩
  have hlim : Tendsto (fun t ↦ 1 - radius s t) (𝓝 t₀) (𝓝 1) := by
    have := ((continuous_radius s).tendsto t₀).const_sub 1
    rwa [hr, sub_zero] at this
  rw [Filter.mem_map]
  filter_upwards [nhdsWithin_le_nhds (hlim.eventually
    (((isCompact_boundary s).image_of_continuousOn hg).eventually_forall_of_forall_eventually
      (x₀ := (1 : ℝ)) (P := fun τ y ↦ τ ∈ Icc (0 : ℝ) 1 → y ∈ W → H τ y ∈ V) hP)),
    self_mem_nhdsWithin] with t ht hts
  change fill s g H c t ∈ V
  unfold fill
  split_ifs with hrt
  · exact mem_of_mem_nhds hV
  · exact ht _ ⟨_, push_mem_boundary hts hrt, rfl⟩
      ⟨by linarith [radius_le_one hts], by linarith [radius_nonneg hts]⟩
      (hgW (push_mem_boundary hts hrt))

/-- The cone filling is continuous within `Δ s` at every point of `Δ s` of nonzero radius. -/
theorem continuousWithinAt_fill_of_radius_ne_zero (hg : ContinuousOn g (boundary s))
    (hgW : MapsTo g (boundary s) W) (hH : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ W))
    {t₀ : ι → ℝ} (ht₀ : t₀ ∈ face s) (hr : radius s t₀ ≠ 0) :
    ContinuousWithinAt (fill s g H c) (face s) t₀ := by
  have hS : {t | radius s t ≠ 0} ∈ 𝓝[face s] t₀ :=
    mem_nhdsWithin_of_mem_nhds ((continuous_radius s).continuousAt.eventually_ne hr)
  have hev : ∀ᶠ t in 𝓝[face s] t₀, fill s g H c t = H (1 - radius s t) (g (push s t)) := by
    filter_upwards [hS] with t ht
    rw [fill, ite_cond_eq_false _ _ (eq_false ht)]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev
    (by rw [fill, ite_cond_eq_false _ _ (eq_false hr)])
  rw [← continuousWithinAt_inter' hS]
  have hmem : ∀ t ∈ face s ∩ {t | radius s t ≠ 0},
      (1 - radius s t, g (push s t)) ∈ Icc (0 : ℝ) 1 ×ˢ W := fun t ht ↦
    ⟨⟨by linarith [radius_le_one ht.1], by linarith [radius_nonneg ht.1]⟩,
      hgW (push_mem_boundary ht.1 ht.2)⟩
  exact ContinuousWithinAt.comp (g := Function.uncurry H)
    (f := fun t ↦ (1 - radius s t, g (push s t))) (hH _ (hmem t₀ ⟨ht₀, hr⟩))
    ((continuous_const.sub (continuous_radius s)).continuousWithinAt.prodMk
      ((hg _ (push_mem_boundary ht₀ hr)).comp (continuousAt_push hr).continuousWithinAt
        fun t ht ↦ push_mem_boundary ht.1 ht.2)) hmem

/-- **The cone filling is continuous.** -/
theorem continuousOn_fill (hg : ContinuousOn g (boundary s)) (hgW : MapsTo g (boundary s) W)
    (hH : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ W))
    (hH1 : ∀ y ∈ W, H 1 y = c) : ContinuousOn (fill s g H c) (face s) := fun t₀ ht₀ ↦ by
  by_cases hr : radius s t₀ = 0
  · exact continuousWithinAt_fill_of_radius_eq_zero hg hgW hH hH1 hr
  · exact continuousWithinAt_fill_of_radius_ne_zero hg hgW hH ht₀ hr

end ConeFill

end MMP
