module

public import MMP.Geometry.Manifold.Corners.EuclideanQuadrant
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.PartitionOfUnity

/-!
# Locally collared closed subsets of compact spaces are collared

Let `X` be a compact Hausdorff space and `B ⊆ X` a closed subset. Suppose `B` is *locally
collared*: every point of `B` lies in the image of an open embedding
`d : Z × [0, 1) → X` which maps `Z × {0}` into `B` and meets `B` nowhere else. Then `B` is
*collared*: there is an open embedding `c : B × [0, 1) → X` with `c (b, 0) = b`.

This is M. Brown's collaring theorem, in the compact case, with the proof of R. Connelly as
presented by A. Hatcher. Glue an external collar `B × [-3, 0]` to `X` along `B`, giving the
compact space `P` (realised inside `X × ℝ`). Cover `B` by finitely many local collars, take a
partition of unity `φ₁, …, φₖ` on `B` subordinate to it, and put `ψⱼ = φ₁ + ⋯ + φⱼ`. Each
local collar extends, through the external collar, to an open embedding
`Z × (-3, 3) → P`, and pushing along it by `φⱼ` gives a homeomorphism `hⱼ` of `P` carrying
the region `Pⱼ = {t ≥ -ψⱼ}` onto `Pⱼ₋₁`. The composite `h₁ ∘ ⋯ ∘ hₖ` carries `Pₖ` onto
`P₀ = X`, and its restriction to the external collar `B × [-1, 0)` is the collar.

## Main results

* `MMP.Topology.exists_collar_of_locallyCollared`: a locally collared closed subset of a
  compact Hausdorff space is collared.
* `MMP.Topology.exists_localCollar_boundary`: the boundary of a `C^k` manifold modelled on the
  quadrant (`k ≠ 0`) is locally collared, by the diagonal collar `quadrantCollar` in charts.

## References

* [M. Brown, *Locally flat imbeddings of topological manifolds*][brown1962]
* [R. Connelly, *A new proof of Brown's collaring theorem*][connelly1971]
-/

open Set Function Topology

namespace MMP.Topology

universe u v

noncomputable section

section Glue

variable {X : Type u} [TopologicalSpace X] {B : Set X}

/-- `X` with the external collar `B × [-3, 0]` glued along `B`, inside `X × ℝ`. -/
def collarGlue (B : Set X) : Set (X × ℝ) :=
  {p | p.2 ∈ Icc (-3 : ℝ) 0 ∧ (p.2 = 0 ∨ p.1 ∈ B)}

/-- If `B` is closed, then the glued space `collarGlue B` is closed in `X × ℝ`. -/
theorem isClosed_collarGlue (hB : IsClosed B) : IsClosed (collarGlue B) :=
  (isClosed_Icc.preimage continuous_snd).inter
    ((isClosed_eq continuous_snd continuous_const).union (hB.preimage continuous_fst))

/-- If `X` is compact and `B` is closed, then the glued space `collarGlue B` is compact. -/
theorem isCompact_collarGlue [CompactSpace X] (hB : IsClosed B) : IsCompact (collarGlue B) :=
  (isCompact_univ.prod isCompact_Icc).of_isClosed_subset (isClosed_collarGlue hB)
    fun _ hp ↦ ⟨mem_univ _, hp.1⟩

/-- The bump `β` of the push: `0` off `(-2, 2)`, `1` on `[-1, 0]`, slope at least `-1/2`. -/
def collarBump (τ : ℝ) : ℝ := max 0 (min 1 (min (τ + 2) (1 - τ / 2)))

/-- The push `τ ↦ τ + a β(τ)`. -/
def collarPush (a τ : ℝ) : ℝ := τ + a * collarBump τ

/-- The function `τ ↦ β(τ) + τ / 2` is monotone, where `β = collarBump`. -/
theorem collarBump_add_half_mono {τ τ' : ℝ} (h : τ ≤ τ') :
    collarBump τ + τ / 2 ≤ collarBump τ' + τ' / 2 := by
  unfold collarBump
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The bump `collarBump` equals `1` on `[-1, 0]`. -/
theorem collarBump_eq_one {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ ≤ 0) : collarBump τ = 1 := by
  unfold collarBump
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]

/-- The bump `collarBump` vanishes outside `[-2, 2]`. -/
theorem collarBump_eq_zero {τ : ℝ} (h : τ ∉ Icc (-2 : ℝ) 2) : collarBump τ = 0 := by
  unfold collarBump
  simp only [mem_Icc, not_and_or, not_le] at h
  apply max_eq_left
  rcases h with h | h
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

/-- The bump `collarBump` is continuous. -/
theorem continuous_collarBump : Continuous collarBump := by
  unfold collarBump
  fun_prop

/-- The push `(a, τ) ↦ collarPush a τ` is jointly continuous. -/
theorem continuous_collarPush : Continuous fun p : ℝ × ℝ ↦ collarPush p.1 p.2 := by
  unfold collarPush
  exact continuous_snd.add (continuous_fst.mul (continuous_collarBump.comp continuous_snd))

/-- For `0 ≤ a ≤ 1`, the push `collarPush a` is strictly monotone. -/
theorem collarPush_strictMono {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : StrictMono (collarPush a) := by
  intro τ τ' h
  have hm := collarBump_add_half_mono h.le
  have h2 : a * (-(τ' - τ) / 2) ≤ a * (collarBump τ' - collarBump τ) :=
    mul_le_mul_of_nonneg_left (by linarith) h0
  unfold collarPush
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h.le)]

/-- The push `collarPush a` fixes every point outside `[-2, 2]`. -/
theorem collarPush_of_notMem {a τ : ℝ} (h : τ ∉ Icc (-2 : ℝ) 2) : collarPush a τ = τ := by
  simp [collarPush, collarBump_eq_zero h]

/-- For `0 ≤ a ≤ 1`, the push `collarPush a` maps `(-3, 3)` into itself. -/
theorem collarPush_mem_Ioo {a τ : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (hτ : τ ∈ Ioo (-3 : ℝ) 3) :
    collarPush a τ ∈ Ioo (-3 : ℝ) 3 := by
  have hm := collarPush_strictMono h0 h1
  have e1 : collarPush a (-3) = -3 := collarPush_of_notMem (by norm_num)
  have e2 : collarPush a 3 = 3 := collarPush_of_notMem (by norm_num)
  exact ⟨e1 ▸ hm hτ.1, e2 ▸ hm hτ.2⟩

/-- Every `σ ∈ (-3, 3)` is `collarPush a τ` for some `τ ∈ (-3, 3)`. -/
theorem exists_collarPush_eq {a σ : ℝ} (hσ : σ ∈ Ioo (-3 : ℝ) 3) :
    ∃ τ ∈ Ioo (-3 : ℝ) 3, collarPush a τ = σ := by
  have e1 : collarPush a (-3) = -3 := collarPush_of_notMem (by norm_num)
  have e2 : collarPush a 3 = 3 := collarPush_of_notMem (by norm_num)
  have hc : Continuous (collarPush a) :=
    continuous_collarPush.comp (continuous_const.prodMk continuous_id)
  obtain ⟨τ, hτ, rfl⟩ := intermediate_value_Icc (by norm_num : (-3 : ℝ) ≤ 3) hc.continuousOn
    (show σ ∈ Icc (collarPush a (-3)) (collarPush a 3) by
      rw [e1, e2]
      exact ⟨hσ.1.le, hσ.2.le⟩)
  refine ⟨τ, ⟨lt_of_le_of_ne hτ.1 ?_, lt_of_le_of_ne hτ.2 ?_⟩, rfl⟩
  · rintro rfl
    exact hσ.1.ne' e1
  · rintro rfl
    exact hσ.2.ne e2

/-- For `0 ≤ a`, `0 ≤ b` and `a + b ≤ 1`, the push `collarPush b` carries `-(a + b)` to `-a`. -/
theorem collarPush_neg_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    collarPush b (-(a + b)) = -a := by
  unfold collarPush
  rw [collarBump_eq_one (by linarith) (by linarith)]
  ring

/-- The point `0` of `[0, 1)`. -/
def icoZero : Ico (0 : ℝ) 1 := ⟨0, left_mem_Ico.2 one_pos⟩

/-- The collar parameter `max τ 0 / 3 ∈ [0, 1)` of `τ ∈ (-3, 3)`. -/
def collarIco (τ : Ioo (-3 : ℝ) 3) : Ico (0 : ℝ) 1 :=
  ⟨max (τ : ℝ) 0 / 3, by positivity, (div_lt_one (by norm_num)).2 (max_lt τ.2.2 (by norm_num))⟩

/-- The collar parameter `collarIco τ` is `0` when `τ ≤ 0`. -/
theorem collarIco_of_nonpos {τ : Ioo (-3 : ℝ) 3} (h : (τ : ℝ) ≤ 0) : collarIco τ = icoZero :=
  Subtype.ext (by simp [collarIco, icoZero, max_eq_right h])

variable {Z : Type v} [TopologicalSpace Z] {d : Z × Ico (0 : ℝ) 1 → X}

/-- A local collar `d : Z × [0, 1) → X` of `B`, extended through the external collar to
`Z × (-3, 3) → P`. -/
def collarChart (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    (q : Z × Ioo (-3 : ℝ) 3) : collarGlue B :=
  ⟨(d (q.1, collarIco q.2), min (q.2 : ℝ) 0),
    ⟨le_min q.2.2.1.le (by norm_num), min_le_right _ _⟩, by
      rcases le_or_gt (q.2 : ℝ) 0 with h | h
      · exact Or.inr (hd0 _ _ (by rw [collarIco_of_nonpos h]; rfl))
      · exact Or.inl (min_eq_right h.le)⟩

omit [TopologicalSpace X] [TopologicalSpace Z] in
/-- For `τ ≤ 0`, `collarChart` sends `(z, τ)` to the point `(d (z, 0), τ)` of the external
collar. -/
theorem collarChart_of_nonpos (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    {q : Z × Ioo (-3 : ℝ) 3} (h : (q.2 : ℝ) ≤ 0) :
    (collarChart hd0 q).1 = (d (q.1, icoZero), (q.2 : ℝ)) := by
  simp [collarChart, collarIco_of_nonpos h, min_eq_left h]

omit [TopologicalSpace X] [TopologicalSpace Z] in
/-- For `τ > 0`, `collarChart` sends `(z, τ)` to the point `(d (z, τ / 3), 0)` of `X`. -/
theorem collarChart_of_pos (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    {q : Z × Ioo (-3 : ℝ) 3} (h : 0 < (q.2 : ℝ)) :
    (collarChart hd0 q).1 = (d (q.1, collarIco q.2), 0) := by
  simp [collarChart, min_eq_right h.le]

/-- If the local collar `d` is an embedding, then `collarChart` is an embedding. -/
theorem isEmbedding_collarChart (hd : IsEmbedding d)
    (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B) :
    IsEmbedding (collarChart hd0) := by
  have hβ : IsEmbedding fun τ : ℝ ↦ (max τ 0 / 3, min τ 0) := by
    refine Function.LeftInverse.isEmbedding (f := fun r : ℝ × ℝ ↦ 3 * r.1 + r.2) ?_ ?_ ?_
    · intro τ
      have := min_add_max τ 0
      simp only
      linarith
    · fun_prop
    · fun_prop
  have hα : IsEmbedding fun τ : Ioo (-3 : ℝ) 3 ↦ (collarIco τ, min (τ : ℝ) 0) := by
    rw [← (IsEmbedding.subtypeVal.prodMap IsEmbedding.id).of_comp_iff]
    exact hβ.comp IsEmbedding.subtypeVal
  have hA : IsEmbedding fun q : Z × Ioo (-3 : ℝ) 3 ↦ ((q.1, collarIco q.2), min (q.2 : ℝ) 0) :=
    (Homeomorph.prodAssoc Z (Ico (0 : ℝ) 1) ℝ).symm.isEmbedding.comp
      (IsEmbedding.id.prodMap hα)
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  exact (hd.prodMap IsEmbedding.id).comp hA

omit [TopologicalSpace X] [TopologicalSpace Z] in
/-- If `d` meets `B` only over `Z × {0}`, then the range of `collarChart` consists of the points
`(x, t)` of the glued space with `x` in the range of `d` and `t > -3`. -/
theorem range_collarChart (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    (hdB : ∀ p, d p ∈ B → (p.2 : ℝ) = 0) :
    range (collarChart hd0) = {p | p.1.1 ∈ range d ∧ -3 < p.1.2} := by
  ext ⟨⟨x, t⟩, ht⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact ⟨⟨_, rfl⟩, lt_min q.2.2.1 (by norm_num)⟩
  · rintro ⟨⟨⟨z, s⟩, hzs⟩, h3⟩
    simp only at hzs h3
    rcases eq_or_lt_of_le s.2.1 with hs | hs
    · refine ⟨(z, ⟨t, h3, ht.1.2.trans_lt (by norm_num)⟩), Subtype.ext ?_⟩
      rw [collarChart_of_nonpos hd0 ht.1.2]
      simp only [Prod.mk.injEq, and_true]
      rw [← hzs]
      congr 2
      exact Subtype.ext hs
    · have hxB : x ∉ B := fun hx ↦ hs.ne' (hdB _ (hzs ▸ hx))
      have ht0 : t = 0 := ht.2.resolve_right hxB
      have h3s : (3 * (s : ℝ)) ∈ Ioo (-3 : ℝ) 3 := ⟨by linarith, by linarith [s.2.2]⟩
      refine ⟨(z, ⟨_, h3s⟩), Subtype.ext ?_⟩
      rw [collarChart_of_pos hd0 (by simp only; linarith)]
      simp only [Prod.mk.injEq, ht0, and_true]
      rw [← hzs]
      congr 2
      exact Subtype.ext (by simp [collarIco, max_eq_left (by linarith : (0 : ℝ) ≤ 3 * s)])

/-- If `d` is an open embedding meeting `B` only over `Z × {0}`, then `collarChart` is an open
embedding into the glued space. -/
theorem isOpenEmbedding_collarChart (hd : IsOpenEmbedding d)
    (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    (hdB : ∀ p, d p ∈ B → (p.2 : ℝ) = 0) :
    IsOpenEmbedding (collarChart hd0) := by
  refine ⟨isEmbedding_collarChart hd.isEmbedding hd0, ?_⟩
  rw [range_collarChart hd0 hdB]
  exact (hd.isOpen_range.preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val))

omit [TopologicalSpace Z] in
/-- The push `(z, τ) ↦ (z, collarPush (a z) τ)` of `Z × (-3, 3)`, for `0 ≤ a ≤ 1`. -/
def collarPushMap (a : Z → ℝ) (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1) :
    Z × Ioo (-3 : ℝ) 3 → Z × Ioo (-3 : ℝ) 3 :=
  fun q ↦ (q.1, ⟨collarPush (a q.1) q.2, collarPush_mem_Ioo (ha0 _) (ha1 _) q.2.2⟩)

omit [TopologicalSpace Z] in
/-- The push `collarPushMap a` preserves the first coordinate. -/
@[simp]
theorem collarPushMap_fst {a : Z → ℝ} (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1)
    (q : Z × Ioo (-3 : ℝ) 3) : (collarPushMap a ha0 ha1 q).1 = q.1 :=
  rfl

/-- For continuous `a`, the push `collarPushMap a` is continuous. -/
theorem continuous_collarPushMap {a : Z → ℝ} (hac : Continuous a) (ha0 : ∀ z, 0 ≤ a z)
    (ha1 : ∀ z, a z ≤ 1) : Continuous (collarPushMap a ha0 ha1) :=
  continuous_fst.prodMk ((continuous_collarPush.comp ((hac.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

omit [TopologicalSpace Z] in
/-- The push `collarPushMap a` is bijective. -/
theorem bijective_collarPushMap {a : Z → ℝ} (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1) :
    Bijective (collarPushMap a ha0 ha1) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, τ⟩ ⟨z', τ'⟩ h
    simp only [collarPushMap, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact Prod.ext rfl (Subtype.ext ((collarPush_strictMono (ha0 z) (ha1 z)).injective h))
  · rintro ⟨z, σ⟩
    obtain ⟨τ, hτ, hτσ⟩ := exists_collarPush_eq (a := a z) σ.2
    exact ⟨(z, ⟨τ, hτ⟩), Prod.ext rfl (Subtype.ext hτσ)⟩

omit [TopologicalSpace Z] in
/-- If `a` vanishes off `S`, the push `collarPushMap a` fixes every point outside
`S × [-2, 2]`. -/
theorem collarPushMap_of_notMem {a : Z → ℝ} (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1)
    {S : Set Z} {q : Z × Ioo (-3 : ℝ) 3}
    (hq : q ∉ S ×ˢ {τ : Ioo (-3 : ℝ) 3 | (τ : ℝ) ∈ Icc (-2 : ℝ) 2})
    (haS : ∀ z ∉ S, a z = 0) : collarPushMap a ha0 ha1 q = q := by
  obtain ⟨z, τ⟩ := q
  simp only [mem_prod, not_and_or] at hq
  refine Prod.ext rfl (Subtype.ext ?_)
  rcases hq with hz | hτ
  · simp [collarPushMap, collarPush, haS z hz]
  · exact collarPush_of_notMem hτ

/-- If `φ` is supported in the range of the local collar `d`, then the set
`{z | d (z, 0) ∈ tsupport φ} × [-2, 2]` is compact. -/
theorem isCompact_collarPushSupport [CompactSpace X] (hB : IsClosed B) (hd : IsOpenEmbedding d)
    (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    (hdB : ∀ p, d p ∈ B → (p.2 : ℝ) = 0) {φ : X → ℝ} (hsupp : tsupport φ ⊆ range d) :
    IsCompact ({z | d (z, icoZero) ∈ tsupport φ} ×ˢ
      {τ : Ioo (-3 : ℝ) 3 | (τ : ℝ) ∈ Icc (-2 : ℝ) 2}) := by
  refine IsCompact.prod ?_ ?_
  · have hemb : IsEmbedding fun z : Z ↦ d (z, icoZero) :=
      hd.isEmbedding.comp (isEmbedding_prodMkLeft icoZero)
    rw [hemb.isInducing.isCompact_iff]
    have : (fun z ↦ d (z, icoZero)) '' {z | d (z, icoZero) ∈ tsupport φ} = tsupport φ ∩ B := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, hd0 _ _ rfl⟩
      · rintro ⟨hx, hxB⟩
        obtain ⟨⟨z, s⟩, rfl⟩ := hsupp hx
        have hs : s = icoZero := Subtype.ext (hdB _ hxB)
        subst hs
        exact ⟨z, hx, rfl⟩
    rw [this]
    exact ((isClosed_tsupport φ).inter hB).isCompact
  · rw [IsEmbedding.subtypeVal.isInducing.isCompact_iff]
    have : (Subtype.val : Ioo (-3 : ℝ) 3 → ℝ) '' {τ | (τ : ℝ) ∈ Icc (-2 : ℝ) 2} =
        Icc (-2) 2 := by
      ext x
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact hτ
      · intro hx
        exact ⟨⟨x, by linarith [hx.1], by linarith [hx.2]⟩, hx, rfl⟩
    rw [this]
    exact isCompact_Icc

/-- A bijective continuous self-map `g` of `Y`, the identity off a compact set, extends through
an open embedding `D : Y → P` into a compact Hausdorff space, by the identity off the range of
`D`, to a homeomorphism of `P`. -/
theorem exists_homeomorph_extend_of_isOpenEmbedding {P Y : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P] [TopologicalSpace Y] {D : Y → P} (hD : IsOpenEmbedding D)
    {g : Y → Y} (hg : Continuous g) (hgb : Bijective g) {C : Set Y} (hC : IsCompact C)
    (hgC : ∀ q ∉ C, g q = q) :
    ∃ h : P ≃ₜ P, (∀ q, h (D q) = D (g q)) ∧ ∀ p ∉ range D, h p = p := by
  classical
  let Dh := hD.isEmbedding.toHomeomorph
  let f : P → P := fun p ↦ if hp : p ∈ range D then D (g (Dh.symm ⟨p, hp⟩)) else p
  have hfD : ∀ q, f (D q) = D (g q) := by
    intro q
    simp only [f, dite_eq_left (mem_range_self q)]
    exact congrArg (D ∘ g) (hD.isEmbedding.toHomeomorph_symm_apply q)
  have hfout : ∀ p, p ∉ range D → f p = p := fun p hp ↦ dite_eq_right hp
  have hF : IsClosed (D '' C) := (hC.image hD.continuous).isClosed
  have hfix : ∀ p ∉ D '' C, f p = p := by
    intro p hp
    by_cases hr : p ∈ range D
    · obtain ⟨q, rfl⟩ := hr
      rw [hfD, hgC q (fun hq ↦ hp ⟨q, hq, rfl⟩)]
    · exact hfout p hr
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    by_cases hp : p ∈ D '' C
    · have hon : ContinuousOn f (range D) := by
        refine continuousOn_iff_continuous_domRestrict.2 ?_
        convert hD.continuous.comp (hg.comp Dh.symm.continuous) using 1
        funext ⟨p, hp⟩
        exact dite_eq_left hp
      exact hon.continuousAt (hD.isOpen_range.mem_nhds (image_subset_range _ _ hp))
    · exact continuousAt_id.congr (Filter.eventuallyEq_of_mem (hF.isOpen_compl.mem_nhds hp)
        fun p' hp' ↦ (hfix p' hp').symm)
  have hinj : Injective f := by
    intro p p' h
    by_cases hp : p ∈ range D <;> by_cases hp' : p' ∈ range D
    · obtain ⟨q, rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hp'
      rw [hfD, hfD] at h
      rw [hgb.1 (hD.injective h)]
    · obtain ⟨q, rfl⟩ := hp
      rw [hfD, hfout _ hp'] at h
      exact absurd ⟨_, h⟩ hp'
    · obtain ⟨q', rfl⟩ := hp'
      rw [hfD, hfout _ hp] at h
      exact absurd ⟨_, h.symm⟩ hp
    · rwa [hfout _ hp, hfout _ hp'] at h
  have hsurj : Surjective f := by
    intro p
    by_cases hp : p ∈ range D
    · obtain ⟨q, rfl⟩ := hp
      obtain ⟨q₀, rfl⟩ := hgb.2 q
      exact ⟨D q₀, hfD q₀⟩
    · exact ⟨p, hfout p hp⟩
  exact ⟨hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩), hfD, hfout⟩

omit [TopologicalSpace X] [TopologicalSpace Z] in
/-- Through a map `D` agreeing with a local collar chart, the region `{t ≥ -χ}` of the glued
space pulls back to `{τ ≥ -χ (d (z, 0))}`, for `χ ≥ 0`. -/
theorem neg_le_chart_iff {D : Z × Ioo (-3 : ℝ) 3 → collarGlue B}
    (hDneg : ∀ q : Z × Ioo (-3 : ℝ) 3, (q.2 : ℝ) ≤ 0 → (D q).1 = (d (q.1, icoZero), (q.2 : ℝ)))
    (hDpos : ∀ q : Z × Ioo (-3 : ℝ) 3, 0 < (q.2 : ℝ) → (D q).1 = (d (q.1, collarIco q.2), 0))
    {χ : X → ℝ} (hχ : ∀ x, 0 ≤ χ x) (q : Z × Ioo (-3 : ℝ) 3) :
    -χ (D q).1.1 ≤ (D q).1.2 ↔ -χ (d (q.1, icoZero)) ≤ q.2 := by
  rcases le_or_gt (q.2 : ℝ) 0 with h0 | h0
  · rw [hDneg q h0]
  · rw [hDpos q h0]
    constructor <;> intro <;> linarith [hχ (d (q.1, collarIco q.2)), hχ (d (q.1, icoZero))]

omit [TopologicalSpace Z] in
/-- A point of the glued space off the range of a local collar chart either lies at level `-3`
or lies over a zero of any `φ` supported in the range of `d`. -/
theorem eq_zero_or_eq_neg_three_of_notMem_range {D : Z × Ioo (-3 : ℝ) 3 → collarGlue B}
    (hrange : range D = {p | p.1.1 ∈ range d ∧ -3 < p.1.2}) {φ : X → ℝ}
    (hsupp : tsupport φ ⊆ range d) {p : collarGlue B} (hp : p ∉ range D) :
    φ p.1.1 = 0 ∨ p.1.2 = -3 := by
  rw [hrange] at hp
  simp only [mem_ofPred_eq, not_and, not_lt] at hp
  by_cases hx : p.1.1 ∈ range d
  · exact .inr (le_antisymm (hp hx) p.2.1.1)
  · exact .inl (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h))

/-- Pushing along one local collar by a function `φ` supported in it: a homeomorphism of the
glued space carrying `{t ≥ -(ψ + φ)}` onto `{t ≥ -ψ}`, and the graph of `-(ψ + φ)` over `B`
onto the graph of `-ψ`. -/
theorem exists_collarPush_homeomorph [CompactSpace X] [T2Space X] (hB : IsClosed B)
    (hd : IsOpenEmbedding d) (hd0 : ∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B)
    (hdB : ∀ p, d p ∈ B → (p.2 : ℝ) = 0) {ψ φ : X → ℝ} (hφ : Continuous φ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hφ0 : ∀ x, 0 ≤ φ x) (hle : ∀ x, ψ x + φ x ≤ 1)
    (hsupp : tsupport φ ⊆ range d) :
    ∃ h : collarGlue B ≃ₜ collarGlue B,
      (∀ p, -ψ (h p).1.1 ≤ (h p).1.2 ↔ -(ψ p.1.1 + φ p.1.1) ≤ p.1.2) ∧
      ∀ p : collarGlue B, p.1.1 ∈ B → p.1.2 = -(ψ p.1.1 + φ p.1.1) →
        (h p).1 = (p.1.1, -ψ p.1.1) := by
  have : CompactSpace (collarGlue B) := isCompact_iff_compactSpace.1 (isCompact_collarGlue hB)
  have hD : IsOpenEmbedding (collarChart hd0) := isOpenEmbedding_collarChart hd hd0 hdB
  have hrange := range_collarChart hd0 hdB
  have hDneg := fun (q : Z × Ioo (-3 : ℝ) 3) (h : (q.2 : ℝ) ≤ 0) ↦ collarChart_of_nonpos hd0 h
  have hDpos := fun (q : Z × Ioo (-3 : ℝ) 3) (h : 0 < (q.2 : ℝ)) ↦ collarChart_of_pos hd0 h
  generalize collarChart hd0 = D at hD hrange hDneg hDpos
  let a : Z → ℝ := fun z ↦ φ (d (z, icoZero))
  have ha0 : ∀ z, 0 ≤ a z := fun z ↦ hφ0 _
  have ha1 : ∀ z, a z ≤ 1 := fun z ↦ (le_add_of_nonneg_left (hψ0 _)).trans (hle _)
  have hac : Continuous a := hφ.comp (hd.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨h, hfD, hfout⟩ := exists_homeomorph_extend_of_isOpenEmbedding hD
    (continuous_collarPushMap hac ha0 ha1) (bijective_collarPushMap ha0 ha1)
    (isCompact_collarPushSupport hB hd hd0 hdB hsupp) fun q hq ↦
      collarPushMap_of_notMem ha0 ha1 hq fun z hz ↦ image_eq_zero_of_notMem_tsupport (f := φ) hz
  have hkey : ∀ x, collarPush (φ x) (-(ψ x + φ x)) = -ψ x :=
    fun x ↦ collarPush_neg_add (hψ0 x) (hφ0 x) (hle x)
  refine ⟨h, fun p ↦ ?_, fun p hpB hpt ↦ ?_⟩
  · by_cases hr : p ∈ range D
    · obtain ⟨q, rfl⟩ := hr
      have h2 := neg_le_chart_iff hDneg hDpos (fun x ↦ add_nonneg (hψ0 x) (hφ0 x)) q
      rw [hfD, neg_le_chart_iff hDneg hDpos hψ0, h2]
      change -ψ (d (q.1, icoZero)) ≤ collarPush (a q.1) q.2 ↔ _
      rw [← hkey, (collarPush_strictMono (ha0 _) (ha1 _)).le_iff_le]
    · rw [hfout p hr]
      rcases eq_zero_or_eq_neg_three_of_notMem_range hrange hsupp hr with h0 | h3
      · rw [h0, add_zero]
      · constructor <;> intro <;> linarith [hle p.1.1, hψ0 p.1.1, hφ0 p.1.1]
  · by_cases hr : p ∈ range D
    · obtain ⟨q, rfl⟩ := hr
      rcases le_or_gt (q.2 : ℝ) 0 with h0 | h0
      · have e := hDneg q h0
        rw [e] at hpt
        simp only at hpt
        rw [hfD, e]
        have hpq : ((collarPushMap a ha0 ha1 q).2 : ℝ) = -ψ (d (q.1, icoZero)) := by
          change collarPush (a q.1) q.2 = _
          rw [hpt]
          exact hkey _
        rw [hDneg (collarPushMap a ha0 ha1 q) (by rw [hpq]; linarith [hψ0 (d (q.1, icoZero))]),
          hpq, collarPushMap_fst]
      · rw [hDpos q h0] at hpB
        have := hdB _ hpB
        simp only [collarIco] at this
        linarith [le_max_left (q.2 : ℝ) 0]
    · rw [hfout p hr]
      rcases eq_zero_or_eq_neg_three_of_notMem_range hrange hsupp hr with h0 | h3
      · rw [h0, add_zero] at hpt
        exact Prod.ext rfl hpt
      · linarith [hle p.1.1, hψ0 p.1.1, hφ0 p.1.1]

/-- Given local collars `d i` and nonnegative functions `φ i` supported in them with
`∑ i ∈ s, φ i ≤ 1`, there is a homeomorphism `H` of the glued space carrying
`{t ≥ -∑ i ∈ s, φ i}` onto `{t ≥ 0}`, and the graph of `-∑ i ∈ s, φ i` over `B` onto
`B × {0}`. -/
theorem exists_collarGlue_homeomorph [CompactSpace X] [T2Space X] (hB : IsClosed B)
    {ι : Type*} (Zf : ι → Type v) [tZ : ∀ i, TopologicalSpace (Zf i)]
    (d : ∀ i, Zf i × Ico (0 : ℝ) 1 → X) (hd : ∀ i, IsOpenEmbedding (d i))
    (hd0 : ∀ i z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d i (z, t) ∈ B)
    (hdB : ∀ i p, d i p ∈ B → (p.2 : ℝ) = 0) (φ : ι → X → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hφ0 : ∀ i x, 0 ≤ φ i x) (hsupp : ∀ i, tsupport (φ i) ⊆ range (d i)) (s : Finset ι)
    (hs : ∀ x, ∑ i ∈ s, φ i x ≤ 1) :
    ∃ H : collarGlue B ≃ₜ collarGlue B,
      (∀ p, 0 ≤ (H p).1.2 ↔ -(∑ i ∈ s, φ i p.1.1) ≤ p.1.2) ∧
      ∀ p : collarGlue B, p.1.1 ∈ B → p.1.2 = -(∑ i ∈ s, φ i p.1.1) → (H p).1 = (p.1.1, 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Homeomorph.refl _, fun p ↦ by simp, fun p _ hp ↦ ?_⟩
    simp only [Finset.sum_empty, neg_zero] at hp
    exact Prod.ext rfl hp
  | insert a s ha ih =>
    have hs' : ∀ x, ∑ i ∈ s, φ i x ≤ 1 := fun x ↦
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert a s)
        (fun i _ _ ↦ hφ0 i x)).trans (hs x)
    obtain ⟨H, hH1, hH2⟩ := ih hs'
    obtain ⟨h, hh1, hh2⟩ := exists_collarPush_homeomorph hB (hd a) (hd0 a) (hdB a)
      (ψ := fun x ↦ ∑ i ∈ s, φ i x) (hφ a) (fun x ↦ Finset.sum_nonneg fun i _ ↦ hφ0 i x)
      (hφ0 a) (fun x ↦ by have := hs x; rw [Finset.sum_insert ha] at this; linarith) (hsupp a)
    refine ⟨h.trans H, fun p ↦ ?_, fun p hpB hp ↦ ?_⟩
    · rw [Homeomorph.trans_apply, hH1, hh1, Finset.sum_insert ha, add_comm (φ a p.1.1)]
    · rw [Finset.sum_insert ha, add_comm] at hp
      have e := hh2 p hpB hp
      rw [Homeomorph.trans_apply, hH2 (h p) (by rw [e]; exact hpB) (by rw [e]), e]

/-- A homeomorphism `H` of the glued space carrying `{t ≥ -ψ}` onto `X` and the graph of `-ψ`
over `B` onto `B × {0}`, where `ψ = 1` on `B`, restricts on `B × [-1, 0)` to a collar of `B`. -/
theorem exists_collar_of_collarGlue_homeomorph [CompactSpace X] [T2Space X] (hB : IsClosed B)
    {ψ : X → ℝ} (hψB : ∀ x ∈ B, ψ x = 1) (H : collarGlue B ≃ₜ collarGlue B)
    (hH1 : ∀ p, 0 ≤ (H p).1.2 ↔ -ψ p.1.1 ≤ p.1.2)
    (hH2 : ∀ p : collarGlue B, p.1.1 ∈ B → p.1.2 = -ψ p.1.1 → (H p).1 = (p.1.1, 0)) :
    ∃ c : B × Ico (0 : ℝ) 1 → X,
      IsOpenEmbedding c ∧ ∀ x (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x := by
  have : CompactSpace (collarGlue B) := isCompact_iff_compactSpace.1 (isCompact_collarGlue hB)
  let ι0 : B × Ico (0 : ℝ) 1 → collarGlue B := fun q ↦
    ⟨(q.1.1, (q.2 : ℝ) - 1), ⟨by linarith [q.2.2.1], by linarith [q.2.2.2]⟩, Or.inr q.1.2⟩
  let j : X → collarGlue B := fun x ↦ ⟨(x, 0), ⟨by norm_num, le_rfl⟩, Or.inl rfl⟩
  let c : B × Ico (0 : ℝ) 1 → X := fun q ↦ (H (ι0 q)).1.1
  have hHι : ∀ q, (H (ι0 q)).1.2 = 0 := fun q ↦ le_antisymm (H (ι0 q)).2.1.2 <|
    (hH1 (ι0 q)).2 <| by
      change -ψ q.1.1 ≤ (q.2 : ℝ) - 1
      linarith [q.2.2.1, hψB _ q.1.2]
  have hjc : ∀ q, H (ι0 q) = j (c q) := fun q ↦ Subtype.ext (Prod.ext rfl (hHι q))
  have hι0 : IsEmbedding ι0 := by
    rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact IsEmbedding.subtypeVal.prodMap
      ((Homeomorph.subRight (1 : ℝ)).isEmbedding.comp IsEmbedding.subtypeVal)
  have hj : IsEmbedding j := by
    rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact isEmbedding_prodMkLeft (0 : ℝ)
  have hc : IsEmbedding c := by
    rw [← hj.of_comp_iff, show j ∘ c = H ∘ ι0 from funext fun q ↦ (hjc q).symm]
    exact H.isEmbedding.comp hι0
  have hX0 : IsClosed (H '' {p : collarGlue B | p.1.2 = 0}) :=
    ((isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const).isCompact.image
      H.continuous).isClosed
  have hrange : range c = j ⁻¹' (H '' {p : collarGlue B | p.1.2 = 0})ᶜ := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩ ⟨p, hp, hpq⟩
      rw [← hjc] at hpq
      have := congrArg (fun r : collarGlue B ↦ r.1.2) (H.injective hpq)
      simp only [mem_ofPred_eq] at hp
      simp only [hp, ι0] at this
      linarith [q.2.2.2]
    · intro hx
      obtain ⟨p, hp⟩ := H.surjective (j x)
      have h1 := (hH1 p).1 (congrArg (fun r : collarGlue B ↦ r.1.2) hp).ge
      have hne : p.1.2 ≠ 0 := fun h0 ↦ hx ⟨p, h0, hp⟩
      have hlt : p.1.2 < 0 := lt_of_le_of_ne p.2.1.2 hne
      have hpB : p.1.1 ∈ B := p.2.2.resolve_left hne
      rw [hψB _ hpB] at h1
      refine ⟨(⟨p.1.1, hpB⟩, ⟨p.1.2 + 1, by linarith, by linarith⟩), ?_⟩
      have hιp : ι0 (⟨p.1.1, hpB⟩, ⟨p.1.2 + 1, by linarith, by linarith⟩) = p :=
        Subtype.ext (Prod.ext rfl (by simp [ι0]))
      change (H (ι0 _)).1.1 = x
      rw [hιp, hp]
  refine ⟨c, ⟨hc, ?_⟩, fun x t ht ↦ ?_⟩
  · rw [hrange]
    exact hX0.isOpen_compl.preimage hj.continuous
  · exact congrArg Prod.fst (hH2 (ι0 (x, t)) x.2 (by
      change (t : ℝ) - 1 = -ψ x.1
      linarith [hψB _ x.2]))

end Glue

/-- **Brown's collaring theorem** (compact case). A closed subset `B` of a compact Hausdorff
space which is locally collared — every point of `B` lies in the image of an open embedding
`d : Z × [0, 1) → X` mapping `Z × {0}` into `B` and nothing else into `B` — has a collar: an
open embedding `c : B × [0, 1) → X` with `c (b, 0) = b`. -/
public theorem exists_collar_of_locallyCollared {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {B : Set X} (hB : IsClosed B)
    (hloc : ∀ x ∈ B, ∃ (Z : Type v) (_ : TopologicalSpace Z) (d : Z × Ico (0 : ℝ) 1 → X),
      IsOpenEmbedding d ∧ (∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → d (z, t) ∈ B) ∧
      (∀ p, d p ∈ B → (p.2 : ℝ) = 0) ∧ x ∈ range d) :
    ∃ c : B × Ico (0 : ℝ) 1 → X,
      IsOpenEmbedding c ∧ ∀ x (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x := by
  classical
  choose Z tZ d hd hd0 hdB hxd using hloc
  obtain ⟨t, ht⟩ := hB.isCompact.elim_finite_subcover (fun b : B ↦ range (d b.1 b.2))
    (fun b ↦ (hd b.1 b.2).isOpen_range) (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxd x hx⟩)
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hB
    (fun i : t ↦ range (d i.1.1 i.1.2)) (fun i ↦ (hd _ _).isOpen_range) (by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
  have hsum1 : ∀ x, ∑ i, f i x ≤ 1 := fun x ↦ by
    rw [← finsum_eq_sum_of_fintype]; exact f.sum_le_one x
  have hsumB : ∀ x ∈ B, ∑ i, f i x = 1 := fun x hx ↦ by
    rw [← finsum_eq_sum_of_fintype]; exact f.sum_eq_one hx
  obtain ⟨H, hH1, hH2⟩ := exists_collarGlue_homeomorph hB (fun i : t ↦ Z i.1.1 i.1.2)
    (tZ := fun i ↦ tZ i.1.1 i.1.2) (fun i ↦ d i.1.1 i.1.2) (fun i ↦ hd _ _)
    (fun i ↦ hd0 _ _) (fun i ↦ hdB _ _) (fun i ↦ f i) (fun i ↦ (f i).continuous)
    (fun i x ↦ f.nonneg i x) hf Finset.univ hsum1
  exact exists_collar_of_collarGlue_homeomorph hB (ψ := fun x ↦ ∑ i, f i x) hsumB H hH1 hH2

/-! ### Local collars of the boundary of a manifold modelled on the quadrant -/

section Quadrant

open scoped Manifold

/-- The scaling `t ↦ ε t` of `[0, 1)` into `[0, ∞)`, for `0 ≤ ε`. -/
def icoScale {ε : ℝ} (hε : 0 ≤ ε) (t : Ico (0 : ℝ) 1) : Ici (0 : ℝ) :=
  ⟨ε * t, mem_Ici.2 (mul_nonneg hε t.2.1)⟩

/-- The value of the scaling `icoScale` at `t` is `ε * t`. -/
@[simp]
theorem coe_icoScale {ε : ℝ} (hε : 0 ≤ ε) (t : Ico (0 : ℝ) 1) :
    (icoScale hε t : ℝ) = ε * t :=
  rfl

/-- For `0 < ε`, the scaling `icoScale` is an open embedding. -/
theorem isOpenEmbedding_icoScale {ε : ℝ} (hε : 0 < ε) : IsOpenEmbedding (icoScale hε.le) := by
  refine ⟨?_, ?_⟩
  · rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact (Homeomorph.mulLeft₀ ε hε.ne').isEmbedding.comp IsEmbedding.subtypeVal
  · have : range (icoScale hε.le) = {s : Ici (0 : ℝ) | (s : ℝ) < ε} := by
      ext s
      constructor
      · rintro ⟨t, rfl⟩
        change ε * t < ε
        nlinarith [t.2.1, t.2.2]
      · intro hs
        refine ⟨⟨s / ε, div_nonneg s.2 hε.le, (div_lt_one hε).2 hs⟩, Subtype.ext ?_⟩
        change ε * (s / ε) = s
        field_simp
    rw [this]
    exact isOpen_lt continuous_subtype_val continuous_const

/-- The scaling `icoScale` takes values in the ball of radius `ε` about `0`. -/
theorem dist_icoScale_lt {ε : ℝ} (hε : 0 < ε) (t : Ico (0 : ℝ) 1) :
    dist (icoScale hε.le t) ⟨0, mem_Ici.2 le_rfl⟩ < ε := by
  rw [Subtype.dist_eq]
  change dist (ε * t) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hε.le t.2.1)]
  nlinarith [t.2.1, t.2.2]

/-- A point of the diagonal collar `quadrantCollar` has a vanishing coordinate exactly at
height `0`. -/
theorem exists_quadrantCollar_eq_zero_iff {n : ℕ} [NeZero n]
    (y : {x : EuclideanQuadrant n | ∃ i, x.1 i = 0}) (s : Ici (0 : ℝ)) :
    (∃ i, (quadrantCollar n (y, s)).1 i = 0) ↔ (s : ℝ) = 0 := by
  obtain ⟨z, j, hj⟩ := y
  change (∃ i, (z.1 + (s : ℝ) • quadrantDiagonal n) i = 0) ↔ (s : ℝ) = 0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨i, hi⟩
    linarith [z.2 i, mem_Ici.1 s.2]
  · intro hs
    refine ⟨j, ?_⟩
    rw [hs, add_zero]
    exact hj

/-- The inverse of an open partial homeomorphism, after an open embedding into its target, is
an open embedding. -/
theorem isOpenEmbedding_symm_comp {Y : Type*} {W : Type*} {T : Type*} [TopologicalSpace Y]
    [TopologicalSpace W] [TopologicalSpace T] (e : OpenPartialHomeomorph Y W) {g : T → W}
    (hg : IsOpenEmbedding g) (hgt : range g ⊆ e.target) : IsOpenEmbedding (e.symm ∘ g) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (e.continuousOn_symm.comp_continuous hg.continuous fun p ↦ hgt ⟨p, rfl⟩) ?_ ?_
  · intro p p' h
    exact hg.injective
      (e.symm.injOn (e.symm_source ▸ hgt ⟨p, rfl⟩) (e.symm_source ▸ hgt ⟨p', rfl⟩) h)
  · intro V hV
    rw [image_comp]
    exact e.isOpen_image_symm_of_subset_target (hg.isOpenMap V hV)
      ((image_subset_range _ _).trans hgt)

/-- Every boundary point of a `C^k` manifold modelled on the quadrant (`k ≠ 0`) has a local
collar: an open embedding `d : Z × [0, 1) → M` through it, carrying exactly `Z × {0}` into the
boundary. -/
public theorem exists_localCollar_boundary {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanQuadrant n) M] {k : WithTop ℕ∞}
    [IsManifold (modelWithCornersEuclideanQuadrant n) k M] (hk : k ≠ 0) {x : M}
    (hx : x ∈ (modelWithCornersEuclideanQuadrant n).boundary M) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (d : Z × Ico (0 : ℝ) 1 → M),
      IsOpenEmbedding d ∧
      (∀ z (t : Ico (0 : ℝ) 1), (t : ℝ) = 0 →
        d (z, t) ∈ (modelWithCornersEuclideanQuadrant n).boundary M) ∧
      (∀ p, d p ∈ (modelWithCornersEuclideanQuadrant n).boundary M → (p.2 : ℝ) = 0) ∧
      x ∈ range d := by
  set e := chartAt (EuclideanQuadrant n) x
  have he : e ∈ atlas (EuclideanQuadrant n) M := chart_mem_atlas _ x
  have hxs : x ∈ e.source := mem_chart_source _ x
  have hbd : ∀ m ∈ e.source, m ∈ (modelWithCornersEuclideanQuadrant n).boundary M ↔
      ∃ i, (e m).1 i = 0 :=
    fun m hm ↦ isBoundaryPoint_iff_exists_extend_eq_zero_of_mem_atlas hk he hm
  obtain ⟨i₀, hi₀⟩ := (hbd x hxs).1 hx
  have : NeZero n := ⟨by rintro rfl; exact i₀.elim0⟩
  set Φ := quadrantCollar n
  let y : {x : EuclideanQuadrant n | ∃ i, x.1 i = 0} := ⟨e x, i₀, hi₀⟩
  let o : Ici (0 : ℝ) := ⟨0, mem_Ici.2 le_rfl⟩
  have hW : IsOpen (Φ ⁻¹' e.target) := e.open_target.preimage Φ.continuous
  have hyW : (y, o) ∈ Φ ⁻¹' e.target := by
    rw [mem_preimage, quadrantCollar_apply_zero]
    exact e.map_source hxs
  obtain ⟨u, v, hu, hv, hyu, hov, huv⟩ := isOpen_prod_iff.1 hW y o hyW
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.1 hv o hov
  let g : u × Ico (0 : ℝ) 1 → EuclideanQuadrant n := fun p ↦ Φ (p.1.1, icoScale hε.le p.2)
  have hg : IsOpenEmbedding g :=
    Φ.isOpenEmbedding.comp (hu.isOpenEmbedding_subtypeVal.prodMap (isOpenEmbedding_icoScale hε))
  have hgt : range g ⊆ e.target := by
    rintro _ ⟨p, rfl⟩
    exact huv ⟨p.1.2, hεv (Metric.mem_ball.2 (dist_icoScale_lt hε p.2))⟩
  have hgcoord : ∀ p : u × Ico (0 : ℝ) 1, (∃ i, (g p).1 i = 0) ↔ (p.2 : ℝ) = 0 := fun p ↦
    (exists_quadrantCollar_eq_zero_iff p.1.1 (icoScale hε.le p.2)).trans <| by
      rw [coe_icoScale, mul_eq_zero, or_iff_right hε.ne']
  refine ⟨u, inferInstance, e.symm ∘ g, isOpenEmbedding_symm_comp e hg hgt,
    fun z t ht ↦ ?_, fun p hp ↦ ?_, ⟨(⟨y, hyu⟩, icoZero), ?_⟩⟩
  · have hm := e.map_target (hgt ⟨(z, t), rfl⟩)
    rw [comp_apply, hbd _ hm, e.right_inv (hgt ⟨(z, t), rfl⟩)]
    exact (hgcoord (z, t)).2 ht
  · have hm := e.map_target (hgt ⟨p, rfl⟩)
    rw [comp_apply, hbd _ hm, e.right_inv (hgt ⟨p, rfl⟩)] at hp
    exact (hgcoord p).1 hp
  · have : icoScale hε.le icoZero = o := Subtype.ext (mul_zero ε)
    simp only [comp_apply, g, this]
    rw [quadrantCollar_apply_zero]
    exact e.left_inv hxs

end Quadrant

end

end MMP.Topology
