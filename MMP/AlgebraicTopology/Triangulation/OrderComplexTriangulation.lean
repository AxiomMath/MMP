module

public import MMP.AlgebraicTopology.Triangulation.StdTriangulation
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Analysis.Normed.Module.Basic
public import MMP.AlgebraicGeometry.Semialgebraic.CylindricalDecomposition

/-!
# Regular cell complexes with radial structures are triangulable

Let `X` be a Hausdorff space and `e a`, `a ∈ κ`, finitely many pairwise disjoint subsets of `X`
(the *cells*), such that the closure of each cell is a union of cells. Write `b ≺ a` when
`e b` lies in the boundary `∂ e a = cl(e a) \ e a`. A *radial structure* on a cell `A` is a
centre `c ∈ A` and a continuous map `ray : ∂A × [0, 1] → cl A` with `ray(q, 0) = c`,
`ray(q, 1) = q`, mapping `∂A × (0, 1)` bijectively onto `A \ {c}`: it presents `cl A` as the
cone over the compact set `∂A`.

If every cell has a radial structure, the *order complex* of `≺` (its simplices are the nonempty
chains of cells) triangulates the union of the cells. The homeomorphism is the iterated cone
map: a point `y` of the simplex of a chain with top cell `a` and weight `y a < 1` on it is sent
to `ray_a(Φ(y'), 1 - y a)`, where `y'` is the renormalised rest of `y`, a point of the simplex
of the chain without `a`, and the vertex of `a` is sent to the centre of `a`. Each open simplex
is mapped into its top cell, so the triangulation is compatible with every union of cells.

## Main definitions

* `MMP.IsRadialCell`: a radial structure on a set.
* `MMP.IsRadialCellComplex`: a finite cell complex with radial structures.
* `MMP.orderComplex`: the chains of cells.
* `MMP.coneMap`: the iterated cone map.

## Main results

* `MMP.IsRadialCellComplex.isStdTriangulation`: the iterated cone map is a
  standard triangulation of the union of the cells by the order complex, mapping each open
  simplex into its top cell.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §9.2.
-/

@[expose] public section

open Set Filter Topology

namespace MMP

section RadialCell

variable {X : Type*} [TopologicalSpace X]

/-- A **radial structure** on `A ⊆ X`: a centre `c ∈ A` and rays `ray q : [0, 1] → cl A` from
`c` to the points `q` of the compact boundary `cl A \ A`, continuous in `(q, s)`, which sweep
out `A \ {c}` bijectively for `0 < s < 1`. -/
structure IsRadialCell (A : Set X) (c : X) (ray : X → ℝ → X) : Prop where
  center_mem : c ∈ A
  isCompact_boundary : IsCompact (closure A \ A)
  continuousOn : ContinuousOn (fun p : X × ℝ ↦ ray p.1 p.2) ((closure A \ A) ×ˢ Icc 0 1)
  ray_zero : ∀ q ∈ closure A \ A, ray q 0 = c
  ray_one : ∀ q ∈ closure A \ A, ray q 1 = q
  ray_mem : ∀ q ∈ closure A \ A, ∀ s ∈ Ico (0 : ℝ) 1, ray q s ∈ A
  ray_ne_center : ∀ q ∈ closure A \ A, ∀ s ∈ Ioo (0 : ℝ) 1, ray q s ≠ c
  ray_injOn : ∀ q ∈ closure A \ A, ∀ q' ∈ closure A \ A, ∀ s ∈ Ioo (0 : ℝ) 1,
    ∀ s' ∈ Ioo (0 : ℝ) 1, ray q s = ray q' s' → q = q' ∧ s = s'
  exists_ray_eq : ∀ z ∈ A, z ≠ c → ∃ q ∈ closure A \ A, ∃ s ∈ Ioo (0 : ℝ) 1, ray q s = z

/-- Near the centre, all rays are uniformly close to it. -/
theorem IsRadialCell.eventually_ray_mem {A : Set X} {c : X} {ray : X → ℝ → X}
    (h : IsRadialCell A c ray) {W : Set X} (hW : W ∈ 𝓝 c) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q ∈ closure A \ A, s ∈ Icc (0 : ℝ) 1 → ray q s ∈ W := by
  have key := h.isCompact_boundary.eventually_forall_of_forall_eventually
    (P := fun (s : ℝ) (q : X) ↦ q ∈ closure A \ A → s ∈ Icc (0 : ℝ) 1 → ray q s ∈ W)
    (x₀ := (0 : ℝ)) fun q hq ↦ ?_
  · filter_upwards [key] with s hs q hq hsI using hs q hq hq hsI
  have hc : ContinuousWithinAt (fun p : X × ℝ ↦ ray p.1 p.2) ((closure A \ A) ×ˢ Icc 0 1)
      (q, 0) := h.continuousOn _ ⟨hq, left_mem_Icc.2 zero_le_one⟩
  have h1 : ∀ᶠ p in 𝓝[(closure A \ A) ×ˢ Icc 0 1] (q, (0 : ℝ)), ray p.1 p.2 ∈ W := by
    refine hc.eventually_mem ?_
    simpa [h.ray_zero q hq] using hW
  rw [eventually_nhdsWithin_iff] at h1
  have h2 : Tendsto (fun z : ℝ × X ↦ (z.2, z.1)) (𝓝 ((0 : ℝ), q)) (𝓝 (q, (0 : ℝ))) :=
    (continuous_snd.prodMk continuous_fst).tendsto' _ _ rfl
  filter_upwards [h2.eventually h1] with z hz hzq hzI
  exact hz ⟨hzq, hzI⟩

end RadialCell

section CellComplex

variable {X : Type*} [TopologicalSpace X] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The face relation of a family of cells: `e a` lies in the boundary of `e b`. -/
def CellLT (e : κ → Set X) (a b : κ) : Prop := e a ⊆ closure (e b) \ e b

/-- A **finite cell complex with radial structures**: pairwise disjoint cells, the closure of
each a union of cells, each with a radial structure. -/
structure IsRadialCellComplex (e : κ → Set X) (center : κ → X) (ray : κ → X → ℝ → X) :
    Prop where
  /-- The cells are pairwise disjoint. -/
  pairwise_disjoint : Pairwise fun a b ↦ Disjoint (e a) (e b)
  /-- Each cell carries a radial structure. -/
  isRadialCell : ∀ a, IsRadialCell (e a) (center a) (ray a)
  /-- The closure of each cell lies in the union of the cells. -/
  closure_subset : ∀ a, closure (e a) ⊆ ⋃ b, e b
  /-- A cell meeting the closure of another cell lies in that closure. -/
  subset_closure : ∀ a b, (e b ∩ closure (e a)).Nonempty → e b ⊆ closure (e a)

/-- The **order complex** of the face relation: the nonempty chains of cells. -/
def orderComplex (e : κ → Set X) : Set (Finset κ) :=
  {c | c.Nonempty ∧ IsChain (CellLT e) (c : Set κ)}

/-- A point of the polyhedron of the order complex: nonnegative weights with sum one, supported
on a chain. -/
def IsChainPoint (e : κ → Set X) (y : κ → ℝ) : Prop :=
  (∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1 ∧ IsChain (CellLT e) {a | y a ≠ 0}

/-- `a` is the top cell of the support of `y`. -/
def IsChainTop (e : κ → Set X) (y : κ → ℝ) (a : κ) : Prop :=
  y a ≠ 0 ∧ ∀ b, y b ≠ 0 → b = a ∨ CellLT e b a

open scoped Classical in
/-- The number of cells below `a`; it increases along the face relation. -/
noncomputable def cellRank (e : κ → Set X) (a : κ) : ℕ :=
  (Finset.univ.filter (CellLT e · a)).card

/-- The top cell of the support of `y` (a junk value if there is none). -/
noncomputable def chainTop [Nonempty κ] (e : κ → Set X) (y : κ → ℝ) : κ :=
  Classical.epsilon (IsChainTop e y)

/-- The renormalised rest of `y` after removing the weight on `a`. -/
noncomputable def coneRest (a : κ) (y : κ → ℝ) : κ → ℝ :=
  (1 - y a)⁻¹ • (y - Pi.single a (y a))

/-- The iterated cone map, by recursion on the size of the support. -/
noncomputable def coneMapAux [Nonempty κ] (e : κ → Set X) (center : κ → X)
    (ray : κ → X → ℝ → X) : ℕ → (κ → ℝ) → X
  | 0, y => center (chainTop e y)
  | n + 1, y => if y (chainTop e y) = 1 then center (chainTop e y) else
      ray (chainTop e y) (coneMapAux e center ray n (coneRest (chainTop e y) y))
        (1 - y (chainTop e y))

/-- The **iterated cone map** of a cell complex with radial structures. -/
noncomputable def coneMap [Nonempty κ] (e : κ → Set X) (center : κ → X)
    (ray : κ → X → ℝ → X) (y : κ → ℝ) : X :=
  coneMapAux e center ray (Finset.univ.filter (y · ≠ 0)).card y

omit [Fintype κ] in
/-- The value of `coneRest a y` at `b`: zero at `a`, and `y b / (1 - y a)` elsewhere. -/
theorem coneRest_apply (a : κ) (y : κ → ℝ) (b : κ) :
    coneRest a y b = if b = a then 0 else (1 - y a)⁻¹ * y b := by
  by_cases hb : b = a
  · subst hb
    simp [coneRest]
  · simp [coneRest, hb]

/-- Chain points are exactly the points of the polyhedron of the order complex. -/
theorem isChainPoint_iff_mem_stdSpace {e : κ → Set X} {y : κ → ℝ} :
    IsChainPoint e y ↔ y ∈ stdSpace (orderComplex e) := by
  simp only [stdSpace, mem_iUnion, exists_prop, mem_convexHull_stdVertex_iff]
  constructor
  · rintro ⟨h0, h1, hc⟩
    refine ⟨Finset.univ.filter (y · ≠ 0), ⟨?_, ?_⟩, h0, h1, fun v hv ↦ ?_⟩
    · obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
        by_contra! h
        simp [h] at h1
      exact ⟨a, by simp [ha]⟩
    · exact hc.mono fun a ha ↦ by simpa using ha
    · simpa using hv
  · rintro ⟨c, ⟨-, hc⟩, h0, h1, hoff⟩
    exact ⟨h0, h1, hc.mono fun a ha ↦ of_not_not fun h ↦ ha (hoff a h)⟩

omit [DecidableEq κ] in
/-- A chain point has a nonzero weight. -/
theorem IsChainPoint.exists_ne_zero {e : κ → Set X} {y : κ → ℝ} (hy : IsChainPoint e y) :
    ∃ a, y a ≠ 0 := by
  by_contra! h
  simpa [h] using hy.2.1

omit [DecidableEq κ] in
/-- Each weight of a chain point is at most one. -/
theorem IsChainPoint.le_one {e : κ → Set X} {y : κ → ℝ} (hy : IsChainPoint e y) (a : κ) :
    y a ≤ 1 := by
  rw [← hy.2.1]
  exact Finset.single_le_sum (fun b _ ↦ hy.1 b) (Finset.mem_univ a)

omit [Fintype κ] in
/-- If `y a ≠ 1`, then `y` is the combination `(1 - y a) • coneRest a y + y a • δ_a`. -/
theorem coneRest_reconstruct (a : κ) (y : κ → ℝ) (ha1 : y a ≠ 1) :
    y = (1 - y a) • coneRest a y + y a • Pi.single a 1 := by
  have hpos : 1 - y a ≠ 0 := sub_ne_zero.2 (Ne.symm ha1)
  funext b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coneRest_apply, Pi.single_apply]
  split_ifs with hb
  · subst hb
    ring
  · field_simp; ring

/-- Removing the top cell of a chain point. -/
theorem isChainPoint_coneRest {e : κ → Set X} {y : κ → ℝ} (hy : IsChainPoint e y) {a : κ}
    (ha : IsChainTop e y a) (ha1 : y a ≠ 1) :
    IsChainPoint e (coneRest a y) ∧ (∀ b, coneRest a y b ≠ 0 → CellLT e b a) ∧
      (Finset.univ.filter (coneRest a y · ≠ 0)).card + 1 =
        (Finset.univ.filter (y · ≠ 0)).card := by
  have hlt : y a < 1 := lt_of_le_of_ne (hy.le_one a) ha1
  have hpos : 0 < 1 - y a := sub_pos.2 hlt
  have hsupp : ∀ b, coneRest a y b ≠ 0 ↔ b ≠ a ∧ y b ≠ 0 := fun b ↦ by
    rw [coneRest_apply]
    split_ifs with hb
    · simp [hb]
    · simp [hb, hpos.ne']
  refine ⟨⟨fun b ↦ ?_, ?_, ?_⟩, fun b hb ↦ ?_, ?_⟩
  · rw [coneRest_apply]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (inv_nonneg.2 hpos.le) (hy.1 b)
  · simp only [coneRest_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
    have : ∑ b ∈ Finset.univ.filter (fun b ↦ ¬ b = a), y b = 1 - y a := by
      have hfe : Finset.univ.filter (fun b ↦ ¬ b = a) = Finset.univ.erase a := by ext b; simp
      rw [hfe]
      have := Finset.add_sum_erase Finset.univ y (Finset.mem_univ a)
      linarith [hy.2.1]
    rw [this, inv_mul_cancel₀ hpos.ne']
  · exact hy.2.2.mono fun b hb ↦ ((hsupp b).1 hb).2
  · obtain ⟨hba, hb⟩ := (hsupp b).1 hb
    rcases ha.2 b hb with h | h
    · exact absurd h hba
    · exact h
  · classical
    have : Finset.univ.filter (y · ≠ 0) = insert a (Finset.univ.filter (coneRest a y · ≠ 0)) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hsupp]
      by_cases hb : b = a
      · subst hb; simp [ha.1]
      · simp [hb]
    rw [this, Finset.card_insert_of_notMem (by simp [hsupp])]

namespace IsRadialCellComplex

variable [T2Space X] {e : κ → Set X} {center : κ → X} {ray : κ → X → ℝ → X}
  (H : IsRadialCellComplex e center ray)

include H

omit [Fintype κ] [DecidableEq κ] [T2Space X] in
/-- The face relation is irreflexive. -/
theorem cellLT_irrefl (a : κ) : ¬ CellLT e a a := fun h ↦
  (h (H.isRadialCell a).center_mem).2 (H.isRadialCell a).center_mem

omit [Fintype κ] [DecidableEq κ] in
/-- The face relation is transitive. -/
theorem cellLT_trans {a b c : κ} (hab : CellLT e a b) (hbc : CellLT e b c) : CellLT e a c :=
  hab.trans <| sdiff_subset.trans <|
    closure_minimal hbc (H.isRadialCell c).isCompact_boundary.isClosed

omit [Fintype κ] [DecidableEq κ] [T2Space X] in
/-- A cell containing a boundary point of `e a` is a face of `e a`. -/
theorem cellLT_of_mem {a b : κ} {q : X} (hq : q ∈ closure (e a) \ e a) (hqb : q ∈ e b) :
    CellLT e b a := by
  have hba : b ≠ a := by rintro rfl; exact hq.2 hqb
  exact fun z hz ↦ ⟨H.subset_closure a b ⟨q, hqb, hq.1⟩ hz,
    fun hza ↦ Set.disjoint_left.1 (H.pairwise_disjoint hba) hz hza⟩

omit [Fintype κ] [DecidableEq κ] [T2Space X] in
/-- Every boundary point of `e a` lies in a face of `e a`. -/
theorem exists_cellLT_of_mem {a : κ} {q : X} (hq : q ∈ closure (e a) \ e a) :
    ∃ b, CellLT e b a ∧ q ∈ e b := by
  obtain ⟨b, hb⟩ := mem_iUnion.1 (H.closure_subset a hq.1)
  exact ⟨b, H.cellLT_of_mem hq hb, hb⟩

omit [Fintype κ] [DecidableEq κ] [T2Space X] in
/-- A point lies in at most one cell. -/
theorem eq_of_mem {a b : κ} {z : X} (ha : z ∈ e a) (hb : z ∈ e b) : a = b := by
  by_contra h
  exact Set.disjoint_left.1 (H.pairwise_disjoint h) ha hb

omit [DecidableEq κ] in
/-- The rank strictly increases along the face relation. -/
theorem cellRank_lt {a b : κ} (h : CellLT e a b) : cellRank e a < cellRank e b := by
  classical
  unfold cellRank
  apply Finset.card_lt_card
  refine ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact H.cellLT_trans hx h
  · have : a ∈ Finset.univ.filter (CellLT e · b) := by simp [h]
    have := hsub this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact H.cellLT_irrefl a this

omit [Fintype κ] [DecidableEq κ] in
/-- The top cell of the support of `y` is unique. -/
theorem isChainTop_unique {y : κ → ℝ} {a a' : κ} (ha : IsChainTop e y a)
    (ha' : IsChainTop e y a') : a = a' := by
  rcases ha.2 a' ha'.1 with h | h
  · exact h.symm
  rcases ha'.2 a ha.1 with h' | h'
  · exact h'
  exact absurd (H.cellLT_trans h h') (H.cellLT_irrefl a')

omit [DecidableEq κ] in
/-- A chain with a nonzero weight has a top cell. -/
theorem exists_isChainTop {y : κ → ℝ} (hy : IsChain (CellLT e) {a | y a ≠ 0})
    (hne : ∃ a, y a ≠ 0) : ∃ a, IsChainTop e y a := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (y · ≠ 0)) (cellRank e)
    ⟨a₀, by simp [ha₀]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
  refine ⟨a, ha, fun b hb ↦ ?_⟩
  by_cases hba : b = a
  · exact Or.inl hba
  rcases hy hb ha hba with h | h
  · exact Or.inr h
  · exact absurd (H.cellRank_lt h) (not_lt.2 (hmax b hb))

variable [Nonempty κ]

omit [DecidableEq κ] in
/-- `chainTop e y` is the top cell of the support of a chain point `y`. -/
theorem isChainTop_chainTop {y : κ → ℝ} (hy : IsChainPoint e y) :
    IsChainTop e y (chainTop e y) :=
  Classical.epsilon_spec (H.exists_isChainTop hy.2.2 hy.exists_ne_zero)

omit [DecidableEq κ] in
/-- `chainTop e y` equals any top cell of the support of a chain point `y`. -/
theorem chainTop_eq {y : κ → ℝ} (hy : IsChainPoint e y) {a : κ} (ha : IsChainTop e y a) :
    chainTop e y = a :=
  H.isChainTop_unique (H.isChainTop_chainTop hy) ha

/-- The defining equation of the iterated cone map at a chain point. -/
theorem coneMap_eq {y : κ → ℝ} (hy : IsChainPoint e y) :
    coneMap e center ray y = if y (chainTop e y) = 1 then center (chainTop e y) else
      ray (chainTop e y) (coneMap e center ray (coneRest (chainTop e y) y))
        (1 - y (chainTop e y)) := by
  have ht := H.isChainTop_chainTop hy
  obtain ⟨n, hn⟩ : ∃ n, (Finset.univ.filter (y · ≠ 0)).card = n + 1 :=
    Nat.exists_eq_add_one.2 (Finset.card_pos.2 ⟨chainTop e y, by simp [ht.1]⟩)
  unfold coneMap
  rw [hn, coneMapAux]
  split_ifs with h1
  · rfl
  · have := (isChainPoint_coneRest hy ht h1).2.2
    rw [hn] at this
    rw [show (Finset.univ.filter (coneRest (chainTop e y) y · ≠ 0)).card = n by omega]

/-- The iterated cone map sends a chain point into its top cell. -/
theorem coneMap_mem {y : κ → ℝ} (hy : IsChainPoint e y) :
    coneMap e center ray y ∈ e (chainTop e y) := by
  induction hn : (Finset.univ.filter (y · ≠ 0)).card using Nat.strong_induction_on generalizing y
    with
  | _ n ih =>
  have ht := H.isChainTop_chainTop hy
  set a := chainTop e y
  rw [H.coneMap_eq hy]
  split_ifs with h1
  · exact (H.isRadialCell a).center_mem
  · obtain ⟨hy', hlt', hcard⟩ := isChainPoint_coneRest hy ht h1
    have hq := ih _ (by omega) hy' rfl
    have hb := hlt' _ (H.isChainTop_chainTop hy').1
    refine (H.isRadialCell a).ray_mem _ (hb hq) _ ⟨sub_nonneg.2 (hy.le_one a), ?_⟩
    have := ht.1
    have h0 := hy.1 a
    exact sub_lt_self 1 (lt_of_le_of_ne h0 (Ne.symm this))

/-- If the support of a chain point `y` lies below `a`, the iterated cone map sends `y` into the
boundary of `e a`. -/
theorem coneMap_mem_boundary {y : κ → ℝ} (hy : IsChainPoint e y) {a : κ}
    (ha : ∀ b, y b ≠ 0 → CellLT e b a) :
    coneMap e center ray y ∈ closure (e a) \ e a :=
  ha _ (H.isChainTop_chainTop hy).1 (H.coneMap_mem hy)

/-- **The iterated cone map is injective** on the polyhedron of the order complex. -/
theorem coneMap_injOn {y y' : κ → ℝ} (hy : IsChainPoint e y) (hy' : IsChainPoint e y')
    (h : coneMap e center ray y = coneMap e center ray y') : y = y' := by
  induction hn : (Finset.univ.filter (y · ≠ 0)).card using Nat.strong_induction_on
    generalizing y y' with
  | _ n ih =>
  have ht := H.isChainTop_chainTop hy
  have ht' := H.isChainTop_chainTop hy'
  have haa : chainTop e y = chainTop e y' :=
    H.eq_of_mem (H.coneMap_mem hy) (h ▸ H.coneMap_mem hy')
  set a := chainTop e y with ha_def
  have hsingle : ∀ z : κ → ℝ, IsChainPoint e z → z a = 1 → z = Pi.single a 1 := by
    intro z hz hza
    funext b
    by_cases hb : b = a
    · subst hb; simp [hza]
    · rw [Pi.single_apply, ite_eq_right hb]
      have hsum : ∑ c ∈ Finset.univ.erase a, z c = 0 := by
        have := Finset.add_sum_erase Finset.univ z (Finset.mem_univ a)
        rw [hz.2.1, hza] at this; linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ hz.1 c).1 hsum b (by simp [hb])
  have hint : ∀ z : κ → ℝ, IsChainPoint e z → IsChainTop e z a → z a ≠ 1 →
      1 - z a ∈ Ioo (0 : ℝ) 1 := fun z hz hza h1 ↦
    ⟨sub_pos.2 (lt_of_le_of_ne (hz.le_one a) h1),
      sub_lt_self 1 (lt_of_le_of_ne (hz.1 a) (Ne.symm hza.1))⟩
  have ht'a : IsChainTop e y' a := haa ▸ ht'
  rw [H.coneMap_eq hy, H.coneMap_eq hy', ← haa] at h
  by_cases h1 : y a = 1 <;> by_cases h1' : y' a = 1
  · rw [hsingle y hy h1, hsingle y' hy' h1']
  · rw [ite_eq_left h1, ite_eq_right h1'] at h
    obtain ⟨hz', hlt', -⟩ := isChainPoint_coneRest hy' ht'a h1'
    exact absurd h.symm ((H.isRadialCell a).ray_ne_center _
      (H.coneMap_mem_boundary hz' hlt') _ (hint y' hy' ht'a h1'))
  · rw [ite_eq_right h1, ite_eq_left h1'] at h
    obtain ⟨hz, hlt, -⟩ := isChainPoint_coneRest hy ht h1
    exact absurd h ((H.isRadialCell a).ray_ne_center _
      (H.coneMap_mem_boundary hz hlt) _ (hint y hy ht h1))
  · rw [ite_eq_right h1, ite_eq_right h1'] at h
    obtain ⟨hz, hlt, hcard⟩ := isChainPoint_coneRest hy ht h1
    obtain ⟨hz', hlt', -⟩ := isChainPoint_coneRest hy' ht'a h1'
    obtain ⟨hq, hs⟩ := (H.isRadialCell a).ray_injOn _ (H.coneMap_mem_boundary hz hlt) _
      (H.coneMap_mem_boundary hz' hlt') _ (hint y hy ht h1) _ (hint y' hy' ht'a h1') h
    have hya : y a = y' a := by linarith
    have hrest := ih _ (by omega) hz hz' hq rfl
    rw [coneRest_reconstruct a y h1, coneRest_reconstruct a y' h1', hrest, hya]

/-- **The iterated cone map is onto the union of the cells**: every point of `e a` is the image
of a chain point with top cell `a`. -/
theorem exists_coneMap_eq (a : κ) {z : X} (hz : z ∈ e a) :
    ∃ y, IsChainPoint e y ∧ chainTop e y = a ∧ coneMap e center ray y = z := by
  induction hn : cellRank e a using Nat.strong_induction_on generalizing a z with
  | _ n ih =>
  have hsa : IsChainPoint e (Pi.single a 1) := by
    refine ⟨fun b ↦ ?_, by simp, ?_⟩
    · rw [Pi.single_apply]; split_ifs <;> norm_num
    · refine Set.Subsingleton.isChain fun b hb b' hb' ↦ ?_
      have h1 : b = a := by by_contra h; simp [Pi.single_apply, h] at hb
      have h2 : b' = a := by by_contra h; simp [Pi.single_apply, h] at hb'
      rw [h1, h2]
  have hta : IsChainTop e (Pi.single a 1) a := ⟨by simp, fun b hb ↦ by
    by_cases h : b = a
    · exact Or.inl h
    · simp [h] at hb⟩
  by_cases hzc : z = center a
  · refine ⟨_, hsa, H.chainTop_eq hsa hta, ?_⟩
    rw [H.coneMap_eq hsa, H.chainTop_eq hsa hta, ite_eq_left (by simp), hzc]
  obtain ⟨q, hq, s, hs, rfl⟩ := (H.isRadialCell a).exists_ray_eq z hz hzc
  obtain ⟨b, hba, hqb⟩ := H.exists_cellLT_of_mem hq
  obtain ⟨y'', hy'', htb, hq''⟩ := ih _ (hn ▸ H.cellRank_lt hba) b hqb rfl
  have htb' := htb ▸ H.isChainTop_chainTop hy''
  have hbelow : ∀ c, y'' c ≠ 0 → CellLT e c a := fun c hc ↦ by
    rcases htb'.2 c hc with h | h
    · exact h ▸ hba
    · exact H.cellLT_trans h hba
  have hya : y'' a = 0 := of_not_not fun h ↦ H.cellLT_irrefl a (hbelow a h)
  set y := s • y'' + (1 - s) • Pi.single a (1 : ℝ) with hy_def
  have hyb : ∀ c, y c = if c = a then 1 - s else s * y'' c := fun c ↦ by
    simp only [hy_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h
    · subst h; rw [hya]; ring
    · ring
  have hyc : IsChainPoint e y := by
    refine ⟨fun c ↦ ?_, ?_, ?_⟩
    · rw [hyb]; split_ifs
      · linarith [hs.2]
      · exact mul_nonneg hs.1.le (hy''.1 c)
    · simp only [hy_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hy''.2.1, Finset.sum_pi_single', Finset.mem_univ, ite_true]
      ring
    · intro c hc c' hc' hcc'
      simp only [mem_ofPred_eq, hyb] at hc hc'
      by_cases h : c = a <;> by_cases h' : c' = a
      · exact absurd (h.trans h'.symm) hcc'
      · rw [ite_eq_right h', mul_ne_zero_iff] at hc'; subst h; exact Or.inr (hbelow c' hc'.2)
      · rw [ite_eq_right h, mul_ne_zero_iff] at hc; subst h'; exact Or.inl (hbelow c hc.2)
      · rw [ite_eq_right h, mul_ne_zero_iff] at hc
        rw [ite_eq_right h', mul_ne_zero_iff] at hc'
        exact hy''.2.2 hc.2 hc'.2 hcc'
  have hya' : y a = 1 - s := by rw [hyb, ite_eq_left rfl]
  have hyt : IsChainTop e y a := by
    refine ⟨by rw [hya']; linarith [hs.2], fun c hc ↦ ?_⟩
    rw [hyb] at hc
    split_ifs at hc with h
    · exact Or.inl h
    · exact Or.inr (hbelow c (right_ne_zero_of_mul hc))
  have hct := H.chainTop_eq hyc hyt
  refine ⟨y, hyc, hct, ?_⟩
  have h1 : y a ≠ 1 := by rw [hya']; linarith [hs.1]
  have hrest : coneRest a y = y'' := by
    funext c
    rw [coneRest_apply, hya', hyb]
    split_ifs with h
    · rw [h, hya]
    · rw [sub_sub_cancel, ← mul_assoc, inv_mul_cancel₀ hs.1.ne', one_mul]
  rw [H.coneMap_eq hyc, hct, ite_eq_right h1, hrest, hq'', hya', sub_sub_cancel]

/-- The iterated cone map is continuous on the closed simplex of each nonempty chain of cells. -/
theorem continuousOn_coneMap_simplex :
    ∀ (c : Finset κ), c.Nonempty → IsChain (CellLT e) (c : Set κ) →
      ContinuousOn (coneMap e center ray)
        {y | (∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1 ∧ ∀ a ∉ c, y a = 0} := by
  intro c
  induction hn : c.card using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  intro hne hc
  set T := {y : κ → ℝ | (∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1 ∧ ∀ a ∉ c, y a = 0} with hT
  have hTc : ∀ y ∈ T, IsChainPoint e y := fun y hy ↦
    ⟨hy.1, hy.2.1, hc.mono fun a ha ↦ of_not_not fun h ↦ ha (hy.2.2 a h)⟩
  obtain ⟨a, hat⟩ := H.exists_isChainTop (y := fun b ↦ if b ∈ c then 1 else 0)
    (hc.mono fun b hb ↦ by simpa using hb) (hne.imp fun b hb ↦ by simp [hb])
  have hac : a ∈ c := by simpa using hat.1
  have habove : ∀ b ∈ c, b ≠ a → CellLT e b a := fun b hb hba ↦ by
    rcases hat.2 b (by simp [hb]) with h | h
    · exact absurd h hba
    · exact h
  by_cases hca : c = {a}
  · refine Set.Subsingleton.continuousOn (fun y hy y' hy' ↦ ?_) _
    have hval : ∀ z ∈ T, z = Pi.single a 1 := fun z hz ↦ by
      funext b
      by_cases hb : b = a
      · subst hb
        have := hz.2.1
        rw [← Finset.add_sum_erase Finset.univ z (Finset.mem_univ b),
          Finset.sum_eq_zero fun d hd ↦ hz.2.2 d (by
            rw [hca, Finset.mem_singleton]; exact (Finset.mem_erase.1 hd).1)] at this
        simpa using this
      · rw [Pi.single_apply, ite_eq_right hb]
        exact hz.2.2 b (by rw [hca, Finset.mem_singleton]; exact hb)
    rw [hval y hy, hval y' hy']
  set c' := c.erase a
  have hc'ne : c'.Nonempty := by
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ c, b ≠ a := by
      by_contra h
      push Not at h
      exact hca (Finset.eq_singleton_iff_unique_mem.2 ⟨hac, h⟩)
    exact ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩⟩
  have ih' := ih c'.card (by rw [← hn]; exact Finset.card_erase_lt_of_mem hac) c' rfl hc'ne
    (hc.mono (by simp [c', Finset.coe_erase]))
  set T' := {y : κ → ℝ | (∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1 ∧ ∀ b ∉ c', y b = 0}
  set F : (κ → ℝ) → X := fun y ↦ if y a = 1 then center a else
    ray a (coneMap e center ray (coneRest a y)) (1 - y a) with hF
  have hrestT : ∀ y ∈ T, y a ≠ 1 → coneRest a y ∈ T' := by
    intro y hy h1
    by_cases h0 : y a = 0
    · have : coneRest a y = y := by
        funext b; rw [coneRest_apply, h0]; split_ifs with h
        · rw [h, h0]
        · simp
      rw [this]
      refine ⟨hy.1, hy.2.1, fun b hb ↦ ?_⟩
      by_cases hba : b = a
      · rw [hba, h0]
      · exact hy.2.2 b fun h ↦ hb (Finset.mem_erase.2 ⟨hba, h⟩)
    · have hta : IsChainTop e y a := ⟨h0, fun b hb ↦ by
        by_cases hba : b = a
        · exact Or.inl hba
        · exact Or.inr (habove b (of_not_not fun h ↦ hb (hy.2.2 b h)) hba)⟩
      obtain ⟨hp, -, -⟩ := isChainPoint_coneRest (hTc y hy) hta h1
      refine ⟨hp.1, hp.2.1, fun b hb ↦ ?_⟩
      rw [coneRest_apply]
      split_ifs with hba
      · rfl
      · rw [hy.2.2 b fun h ↦ hb (Finset.mem_erase.2 ⟨hba, h⟩), mul_zero]
  have hT'bd : ∀ y ∈ T', coneMap e center ray y ∈ closure (e a) \ e a := by
    intro y hy
    refine H.coneMap_mem_boundary ⟨hy.1, hy.2.1, hc.mono (s := {b | y b ≠ 0}) fun b hb ↦ ?_⟩
      fun b hb ↦ ?_
    · have hb' : b ∈ c' := of_not_not fun h ↦ hb (hy.2.2 b h)
      exact Finset.mem_of_mem_erase hb'
    · have hb' : b ∈ c' := of_not_not fun h ↦ hb (hy.2.2 b h)
      exact habove b (Finset.mem_of_mem_erase hb') (Finset.ne_of_mem_erase hb')
  have hEq : EqOn (coneMap e center ray) F T := by
    intro y hy
    by_cases h0 : y a = 0
    · have h1 : y a ≠ 1 := by rw [h0]; norm_num
      have hrest : coneRest a y = y := by
        funext b; rw [coneRest_apply, h0]; split_ifs with h
        · rw [h, h0]
        · simp
      simp only [hF, ite_eq_right h1, hrest, h0, sub_zero]
      refine ((H.isRadialCell a).ray_one _ (hT'bd y ?_)).symm
      rw [← hrest]; exact hrestT y hy h1
    · have hta : IsChainTop e y a := ⟨h0, fun b hb ↦ by
        by_cases hba : b = a
        · exact Or.inl hba
        · exact Or.inr (habove b (of_not_not fun h ↦ hb (hy.2.2 b h)) hba)⟩
      rw [H.coneMap_eq (hTc y hy), H.chainTop_eq (hTc y hy) hta]
  refine ContinuousOn.congr ?_ hEq
  intro y hy
  by_cases h1 : y a = 1
  · have hFy : F y = center a := by simp only [hF, ite_eq_left h1]
    rw [ContinuousWithinAt, hFy]
    intro W hW
    have hev := (H.isRadialCell a).eventually_ray_mem hW
    have hcont : Tendsto (fun z : κ → ℝ ↦ 1 - z a) (𝓝 y) (𝓝 0) := by
      have : Continuous fun z : κ → ℝ ↦ 1 - z a := continuous_const.sub (continuous_apply a)
      simpa [h1] using this.tendsto y
    have h2 := hcont.eventually hev
    rw [Filter.mem_map]
    filter_upwards [nhdsWithin_le_nhds h2, self_mem_nhdsWithin] with z hz hzT
    change F z ∈ W
    by_cases hz1 : z a = 1
    · simp only [hF, ite_eq_left hz1]; exact mem_of_mem_nhds hW
    · simp only [hF, ite_eq_right hz1]
      exact hz _ (hT'bd _ (hrestT z hzT hz1))
        ⟨sub_nonneg.2 ((hTc z hzT).le_one a), by linarith [hzT.1 a]⟩
  · have hU : {z : κ → ℝ | z a ≠ 1} ∈ 𝓝 y :=
      (isOpen_ne_fun (continuous_apply a) continuous_const).mem_nhds h1
    have hG : ContinuousOn (fun z ↦ ray a (coneMap e center ray (coneRest a z)) (1 - z a))
        (T ∩ {z | z a ≠ 1}) := by
      have hrc : ContinuousOn (coneRest a) {z : κ → ℝ | z a ≠ 1} := by
        intro z hz
        refine (ContinuousAt.continuousWithinAt ?_)
        refine continuousAt_pi.2 fun b ↦ ?_
        simp only [coneRest_apply]
        split_ifs
        · exact continuousAt_const
        · refine ContinuousAt.mul ?_ (continuous_apply b).continuousAt
          exact ((continuous_const.sub (continuous_apply a)).continuousAt).inv₀
            (sub_ne_zero.2 (Ne.symm hz))
      have h3 : ContinuousOn (fun z ↦ coneMap e center ray (coneRest a z))
          (T ∩ {z | z a ≠ 1}) :=
        ih'.comp (hrc.mono inter_subset_right) fun z hz ↦ hrestT z hz.1 hz.2
      refine (H.isRadialCell a).continuousOn.comp (h3.prodMk
        ((continuous_const.sub (continuous_apply a)).continuousOn)) fun z hz ↦ ?_
      exact ⟨hT'bd _ (hrestT z hz.1 hz.2),
        show (0 : ℝ) ≤ 1 - z a from sub_nonneg.2 ((hTc z hz.1).le_one a),
        show 1 - z a ≤ (1 : ℝ) by linarith [hz.1.1 a]⟩
    have hmem : T ∩ {z | z a ≠ 1} ∈ 𝓝[T] y := inter_mem_nhdsWithin T hU
    refine ((hG y ⟨hy, h1⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with z hz
      simp only [hF, ite_eq_right hz]
    · simp only [hF, ite_eq_right h1]

end IsRadialCellComplex

namespace IsRadialCellComplex

variable {σ : Type*} {e : κ → Set (σ → ℝ)} {center : κ → σ → ℝ}
  {ray : κ → (σ → ℝ) → ℝ → σ → ℝ} [Nonempty κ] (H : IsRadialCellComplex e center ray)

include H

/-- **Regular cell complexes with radial structures are triangulated by their order
complexes.** The iterated cone map is a standard triangulation of the union of the cells by the
order complex, and it maps the open simplex of each chain into its top cell. -/
theorem isStdTriangulation :
    IsStdTriangulation (orderComplex e) (coneMap e center ray) (⋃ a, e a) ∧
      ∀ c ∈ orderComplex e, ∃ a ∈ c,
        coneMap e center ray '' openSimplex (c.map (stdVertex κ)) ⊆ e a := by
  refine ⟨⟨fun c hc ↦ hc.1, fun c hc d hdc hdne ↦ ⟨hdne, hc.2.mono (Finset.coe_subset.2 hdc)⟩,
    ?_, fun y hy y' hy' h ↦ ?_, ?_⟩, fun c hc ↦ ?_⟩
  · have : stdSpace (orderComplex e) = ⋃ c : orderComplex e,
        convexHull ℝ ((c : Finset κ).map (stdVertex κ) : Set (κ → ℝ)) := by
      rw [stdSpace, biUnion_eq_iUnion]
    rw [this]
    refine (locallyFinite_of_finite _).continuousOn_iUnion
      (fun c ↦ (Finset.finite_toSet _).isClosed_convexHull ℝ) fun c ↦ ?_
    exact (H.continuousOn_coneMap_simplex c c.2.1 c.2.2).mono fun y hy ↦
      (mem_convexHull_stdVertex_iff _ _).1 hy
  · exact H.coneMap_injOn (isChainPoint_iff_mem_stdSpace.2 hy)
      (isChainPoint_iff_mem_stdSpace.2 hy') h
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_iUnion.2 ⟨_, H.coneMap_mem (isChainPoint_iff_mem_stdSpace.2 hy)⟩
    · intro hz
      obtain ⟨a, ha⟩ := mem_iUnion.1 hz
      obtain ⟨y, hy, -, rfl⟩ := H.exists_coneMap_eq a ha
      exact ⟨y, isChainPoint_iff_mem_stdSpace.1 hy, rfl⟩
  · obtain ⟨a, hat⟩ := H.exists_isChainTop (y := fun b ↦ if b ∈ c then 1 else 0)
      (hc.2.mono fun b hb ↦ by simpa using hb)
      (hc.1.imp fun b hb ↦ by simp [hb])
    have hac : a ∈ c := by simpa using hat.1
    refine ⟨a, hac, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨h0, h1, hoff⟩ := (mem_openSimplex_stdVertex_iff c y).1 hy
    have hyc : IsChainPoint e y :=
      ⟨fun b ↦ if hb : b ∈ c then (h0 b hb).le else (hoff b hb).ge, h1,
        hc.2.mono fun b hb ↦ of_not_not fun h ↦ hb (hoff b h)⟩
    have hta : IsChainTop e y a := ⟨(h0 a hac).ne', fun b hb ↦ by
      have hbc : b ∈ c := of_not_not fun h ↦ hb (hoff b h)
      simpa [hbc] using hat.2 b (by simp [hbc])⟩
    simpa only [H.chainTop_eq hyc hta] using H.coneMap_mem hyc

end IsRadialCellComplex

end CellComplex

section RadialModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **radial model**: a set `Q` with a centre `c` and a gauge `μ : Q → [0, 1]` vanishing only
at `c`, linear along the segments from `c` to the points of gauge one, and every point of
positive gauge on such a segment. -/
structure IsRadialModel (Q : Set E) (c : E) (μ : E → ℝ) : Prop where
  center_mem : c ∈ Q
  gauge_center : μ c = 0
  nonneg : ∀ z ∈ Q, 0 ≤ μ z
  le_one : ∀ z ∈ Q, μ z ≤ 1
  eq_center : ∀ z ∈ Q, μ z = 0 → z = c
  segment_mem : ∀ p ∈ Q, μ p = 1 → ∀ s ∈ Icc (0 : ℝ) 1,
    c + s • (p - c) ∈ Q ∧ μ (c + s • (p - c)) = s
  proj_mem : ∀ z ∈ Q, μ z ≠ 0 → c + (μ z)⁻¹ • (z - c) ∈ Q ∧ μ (c + (μ z)⁻¹ • (z - c)) = 1

/-- **Positively homogeneous gauges give radial models.** If `G` is positively homogeneous
about `c`, nonnegative on a set `L` stable under the homotheties of centre `c` and vanishing on
`L` only at `c`, then `L ∩ {G ≤ 1}` is a radial model with gauge `G`. -/
theorem isRadialModel_of_gauge {L : Set E} {c : E} (hc : c ∈ L)
    (hL : ∀ z ∈ L, ∀ t : ℝ, 0 ≤ t → c + t • (z - c) ∈ L) {G : E → ℝ}
    (hG : ∀ z, ∀ t : ℝ, 0 ≤ t → G (c + t • (z - c)) = t * G z)
    (hG0 : ∀ z ∈ L, 0 ≤ G z) (hGc : ∀ z ∈ L, G z = 0 → z = c) :
    IsRadialModel (L ∩ {z | G z ≤ 1}) c G := by
  have hGc0 : G c = 0 := by simpa using hG c 0 le_rfl
  refine ⟨⟨hc, by simp [hGc0]⟩, hGc0, fun z hz ↦ hG0 z hz.1, fun z hz ↦ hz.2,
    fun z hz ↦ hGc z hz.1, fun p hp hp1 s hs ↦ ?_, fun z hz hz0 ↦ ?_⟩
  · have := hG p s hs.1
    rw [hp1, mul_one] at this
    exact ⟨⟨hL p hp.1 s hs.1, this.trans_le hs.2⟩, this⟩
  · have hpos : 0 < G z := lt_of_le_of_ne (hG0 z hz.1) (Ne.symm hz0)
    have := hG z (G z)⁻¹ (inv_nonneg.2 hpos.le)
    rw [inv_mul_cancel₀ hz0] at this
    exact ⟨⟨hL z hz.1 _ (inv_nonneg.2 hpos.le), this.le⟩, this⟩

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [NormedSpace ℝ E] in
/-- The inverse of a continuous injective map on a compact set is continuous on the image. -/
theorem continuousOn_invFunOn_of_isCompact {Q : Set E} (hQ : IsCompact Q) {θ : E → X}
    (hθ : ContinuousOn θ Q) (hinj : InjOn θ Q) :
    ContinuousOn (Function.invFunOn θ Q) (θ '' Q) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨θ '' (Q ∩ C), ((hQ.inter_right hC).image_of_continuousOn
    (hθ.mono inter_subset_left)).isClosed, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨hxC, ⟨q, hq, rfl⟩⟩
    exact ⟨⟨_, ⟨Function.invFunOn_mem (f := θ) ⟨q, hq, rfl⟩, hxC⟩,
      Function.invFunOn_eq (f := θ) ⟨q, hq, rfl⟩⟩, q, hq, rfl⟩
  · rintro ⟨⟨p, ⟨hp, hpC⟩, rfl⟩, -⟩
    rw [hinj.leftInvOn_invFunOn hp]
    exact ⟨hpC, p, hp, rfl⟩

/-- The image of the points of gauge less than one of a compact radial model is dense in the
image of the model. -/
theorem IsRadialModel.closure_image_lt_one {Q : Set E} {c : E} {μ : E → ℝ}
    (hm : IsRadialModel Q c μ) (hQ : IsCompact Q) {θ : E → X} (hθ : ContinuousOn θ Q) :
    closure (θ '' (Q ∩ {z | μ z < 1})) = θ '' Q := by
  refine le_antisymm (closure_minimal (image_mono inter_subset_left)
    (hQ.image_of_continuousOn hθ).isClosed) ?_
  rintro _ ⟨p, hp, rfl⟩
  by_cases hp1 : μ p < 1
  · exact subset_closure ⟨p, ⟨hp, hp1⟩, rfl⟩
  have hp1' : μ p = 1 := le_antisymm (hm.le_one p hp) (not_lt.1 hp1)
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), c + s • (p - c) ∈ Q ∩ {z | μ z < 1} := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    obtain ⟨h1, h2⟩ := hm.segment_mem p hp hp1' s ⟨hs.1.le, hs.2.le⟩
    exact ⟨h1, h2.trans_lt hs.2⟩
  have hseg : Tendsto (fun s : ℝ ↦ c + s • (p - c)) (𝓝[<] 1) (𝓝 p) := by
    have : Continuous fun s : ℝ ↦ c + s • (p - c) := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ ↦ θ (c + s • (p - c))) (𝓝[<] 1) (𝓝 (θ p)) :=
    (hθ p hp).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hseg, hev.mono fun _ h ↦ h.1⟩)
  exact mem_closure_of_tendsto hlim (hev.mono fun s hs ↦ ⟨_, hs, rfl⟩)

/-- The boundary of the image of the points of gauge less than one of a compact radial model is
the image of the points of gauge one. -/
theorem IsRadialModel.closure_diff_image_lt_one {Q : Set E} {c : E} {μ : E → ℝ}
    (hm : IsRadialModel Q c μ) (hQ : IsCompact Q) {θ : E → X} (hθ : ContinuousOn θ Q)
    (hinj : InjOn θ Q) :
    closure (θ '' (Q ∩ {z | μ z < 1})) \ θ '' (Q ∩ {z | μ z < 1}) =
      θ '' (Q ∩ {z | μ z = 1}) := by
  rw [hm.closure_image_lt_one hQ hθ]
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hpA⟩
    exact ⟨p, ⟨hp, le_antisymm (hm.le_one p hp) (not_lt.1 fun h ↦ hpA ⟨p, ⟨hp, h⟩, rfl⟩)⟩,
      rfl⟩
  · rintro ⟨p, ⟨hp, hp1⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro ⟨q, ⟨hq, hq1⟩, hqp⟩
    rw [hinj hq hp hqp] at hq1
    simp only [mem_ofPred_eq] at hq1 hp1
    linarith

omit [TopologicalSpace X] [T2Space X] in
/-- In a radial model, the images of the segments from the centre to two points of gauge one
meet away from the centre only at equal parameters on equal segments. -/
theorem IsRadialModel.eq_of_image_segment_eq {Q : Set E} {c : E} {μ : E → ℝ}
    (hm : IsRadialModel Q c μ) {θ : E → X} (hinj : InjOn θ Q) {p p' : E} (hp : p ∈ Q)
    (hp1 : μ p = 1) (hp' : p' ∈ Q) (hp1' : μ p' = 1) {s s' : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hs' : s' ∈ Ioo (0 : ℝ) 1) (h : θ (c + s • (p - c)) = θ (c + s' • (p' - c))) :
    p = p' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := hm.segment_mem p hp hp1 s ⟨hs.1.le, hs.2.le⟩
  obtain ⟨h1', h2'⟩ := hm.segment_mem p' hp' hp1' s' ⟨hs'.1.le, hs'.2.le⟩
  have heq := hinj h1 h1' h
  obtain rfl : s = s' := by rw [← h2, ← h2', heq]
  exact ⟨by simpa using smul_right_injective E hs.1.ne' (add_left_cancel heq), rfl⟩

/-- **A radial model gives a radial structure on its image.** Let `Q` be a compact radial model
with continuous gauge `μ`, and `θ` continuous and injective on `Q`. The image of the points of
gauge less than one has closure `θ(Q)`, boundary the image of the points of gauge one, and the
images of the segments from the centre form a radial structure. -/
theorem IsRadialModel.isRadialCell {Q : Set E} {c : E} {μ : E → ℝ} (hm : IsRadialModel Q c μ)
    (hQ : IsCompact Q) (hμ : ContinuousOn μ Q) {θ : E → X} (hθ : ContinuousOn θ Q)
    (hinj : InjOn θ Q) :
    closure (θ '' (Q ∩ {z | μ z < 1})) = θ '' Q ∧
      closure (θ '' (Q ∩ {z | μ z < 1})) \ θ '' (Q ∩ {z | μ z < 1}) =
        θ '' (Q ∩ {z | μ z = 1}) ∧
      IsRadialCell (θ '' (Q ∩ {z | μ z < 1})) (θ c)
        (fun q s ↦ θ (c + s • (Function.invFunOn θ Q q - c))) := by
  set A := θ '' (Q ∩ {z | μ z < 1})
  have hcl : closure A = θ '' Q := hm.closure_image_lt_one hQ hθ
  have hbd : closure A \ A = θ '' (Q ∩ {z | μ z = 1}) :=
    hm.closure_diff_image_lt_one hQ hθ hinj
  set g := Function.invFunOn θ Q
  have hg : ∀ q ∈ closure A \ A, g q ∈ Q ∩ {z | μ z = 1} ∧ θ (g q) = q := by
    intro q hq
    rw [hbd] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [show g (θ p) = p from hinj.leftInvOn_invFunOn hp.1]
    exact ⟨hp, rfl⟩
  refine ⟨hcl, hbd, ⟨⟨c, ⟨hm.center_mem, by simp [hm.gauge_center]⟩, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · rw [hbd]
    have hcl1 : IsClosed (Q ∩ μ ⁻¹' {1}) :=
      hμ.preimage_isClosed_of_isClosed hQ.isClosed isClosed_singleton
    exact (hQ.of_isClosed_subset hcl1 inter_subset_left).image_of_continuousOn
      (hθ.mono inter_subset_left)
  · have hgc : ContinuousOn g (closure A \ A) :=
      (continuousOn_invFunOn_of_isCompact hQ hθ hinj).mono (hcl ▸ sdiff_subset)
    refine hθ.comp (continuousOn_const.add ((continuousOn_snd).smul
      ((hgc.comp continuousOn_fst fun p hp ↦ hp.1).sub continuousOn_const))) ?_
    intro p hp
    exact (hm.segment_mem _ (hg p.1 hp.1).1.1 (hg p.1 hp.1).1.2 p.2 hp.2).1
  · exact fun q _ ↦ by simp
  · exact fun q hq ↦ by simp [(hg q hq).2]
  · intro q hq s hs
    obtain ⟨h1, h2⟩ := hm.segment_mem _ (hg q hq).1.1 (hg q hq).1.2 s ⟨hs.1, hs.2.le⟩
    exact ⟨_, ⟨h1, h2.trans_lt hs.2⟩, rfl⟩
  · intro q hq s hs h
    obtain ⟨h1, h2⟩ := hm.segment_mem _ (hg q hq).1.1 (hg q hq).1.2 s ⟨hs.1.le, hs.2.le⟩
    rw [hinj h1 hm.center_mem h, hm.gauge_center] at h2
    exact hs.1.ne' h2.symm
  · intro q hq q' hq' s hs s' hs' h
    obtain ⟨hgq, hss⟩ := hm.eq_of_image_segment_eq hinj (hg q hq).1.1 (hg q hq).1.2
      (hg q' hq').1.1 (hg q' hq').1.2 hs hs' h
    exact ⟨(hg q hq).2.symm.trans ((congrArg θ hgq).trans (hg q' hq').2), hss⟩
  · rintro _ ⟨w, ⟨hw, hw1⟩, rfl⟩ hwc
    have hw0 : μ w ≠ 0 := fun h ↦ hwc (by rw [hm.eq_center w hw h])
    obtain ⟨hp, hp1⟩ := hm.proj_mem w hw hw0
    set p := c + (μ w)⁻¹ • (w - c)
    have hqb : θ p ∈ closure A \ A := hbd ▸ ⟨p, ⟨hp, hp1⟩, rfl⟩
    refine ⟨θ p, hqb, μ w, ⟨lt_of_le_of_ne (hm.nonneg w hw) (Ne.symm hw0), hw1⟩, ?_⟩
    have hgp : g (θ p) = p := hinj.leftInvOn_invFunOn hp
    simp only [hgp, p, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hw0, one_smul,
      add_sub_cancel]

end RadialModel

section StdModels

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The closed standard simplex of `s`: weight vectors supported on `s`. -/
def closedStd (s : Finset ν) : Set (ν → ℝ) :=
  {y | (∀ u, 0 ≤ y u) ∧ ∑ u, y u = 1 ∧ ∀ u ∉ s, y u = 0}

/-- The open standard simplex of `s`: weight vectors with support `s`. -/
def openStd (s : Finset ν) : Set (ν → ℝ) :=
  {y | (∀ u ∈ s, 0 < y u) ∧ ∑ u, y u = 1 ∧ ∀ u ∉ s, y u = 0}

/-- The affine span of the standard simplex of `s`. -/
def affineStd (s : Finset ν) : Set (ν → ℝ) := {y | ∑ u, y u = 1 ∧ ∀ u ∉ s, y u = 0}

/-- The barycentre of the standard simplex of `s`. -/
noncomputable def baryStd (s : Finset ν) : ν → ℝ := fun u ↦ if u ∈ s then ((s.card : ℝ))⁻¹ else 0

/-- The gauge of the standard simplex of `s` about its barycentre. -/
noncomputable def stdGauge (s : Finset ν) (hs : s.Nonempty) (y : ν → ℝ) : ℝ :=
  s.sup' hs fun u ↦ 1 - s.card * y u

/-- The closed standard simplex of `s` is the convex hull of its vertices. -/
theorem closedStd_eq_convexHull (s : Finset ν) :
    closedStd s = convexHull ℝ (s.map (stdVertex ν) : Set (ν → ℝ)) := by
  ext y
  rw [mem_convexHull_stdVertex_iff]
  rfl

/-- The open standard simplex of `s` is the open simplex on its vertices. -/
theorem openStd_eq_openSimplex (s : Finset ν) :
    openStd s = openSimplex (s.map (stdVertex ν)) := by
  ext y
  rw [mem_openSimplex_stdVertex_iff]
  rfl

omit [DecidableEq ν] in
/-- The closed standard simplex is compact. -/
theorem isCompact_closedStd (s : Finset ν) : IsCompact (closedStd s) := by
  classical
  rw [closedStd_eq_convexHull]
  exact (Finset.finite_toSet _).isCompact_convexHull ℝ

omit [DecidableEq ν] in
/-- The open standard simplex lies in the closed standard simplex. -/
theorem openStd_subset_closedStd (s : Finset ν) : openStd s ⊆ closedStd s := by
  rintro y ⟨h0, h1, hoff⟩
  refine ⟨fun u ↦ ?_, h1, hoff⟩
  by_cases hu : u ∈ s
  · exact (h0 u hu).le
  · exact (hoff u hu).ge

omit [DecidableEq ν] in
/-- The weights on `s` of a point of the affine span of the simplex of `s` sum to one. -/
theorem sum_mem_eq_one {s : Finset ν} {y : ν → ℝ} (hy : y ∈ affineStd s) : ∑ u ∈ s, y u = 1 := by
  rw [← hy.1, ← Finset.sum_subset (Finset.subset_univ s) fun u _ hu ↦ hy.2 u hu]

/-- The barycentre lies in the affine span of the standard simplex. -/
theorem baryStd_mem (s : Finset ν) (hs : s.Nonempty) : baryStd s ∈ affineStd s := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  refine ⟨?_, fun u hu ↦ by simp [baryStd, hu]⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun u _ hu ↦ by simp [baryStd, hu],
    Finset.sum_congr rfl (g := fun _ ↦ ((s.card : ℝ))⁻¹) fun u hu ↦ by simp [baryStd, hu],
    Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc]

/-- The affine span of the standard simplex is stable under homotheties about the barycentre. -/
theorem affineStd_homothety {s : Finset ν} (hs : s.Nonempty) {z : ν → ℝ} (hz : z ∈ affineStd s)
    (t : ℝ) : baryStd s + t • (z - baryStd s) ∈ affineStd s := by
  have hb := baryStd_mem s hs
  refine ⟨?_, fun u hu ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hb.1, hz.1, sub_self, mul_zero, add_zero]
  · simp [hb.2 u hu, hz.2 u hu]

omit [Fintype ν] in
/-- The gauge is positively homogeneous under homotheties about the barycentre. -/
theorem stdGauge_homothety {s : Finset ν} (hs : s.Nonempty) (z : ν → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stdGauge s hs (baryStd s + t • (z - baryStd s)) = t * stdGauge s hs z := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  unfold stdGauge
  rw [Finset.apply_sup'_eq_sup'_comp hs (fun x ↦ t * x) fun x y ↦ mul_max_of_nonneg x y ht]
  refine Finset.sup'_congr hs rfl fun u hu ↦ ?_
  simp only [Function.comp, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, baryStd,
    ite_eq_left hu]
  field_simp
  ring

omit [DecidableEq ν] in
/-- The gauge is nonnegative on the affine span of the standard simplex. -/
theorem stdGauge_nonneg {s : Finset ν} (hs : s.Nonempty) {y : ν → ℝ} (hy : y ∈ affineStd s) :
    0 ≤ stdGauge s hs y := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  obtain ⟨u, hu, hyu⟩ : ∃ u ∈ s, y u ≤ (s.card : ℝ)⁻¹ := by
    by_contra! h
    have := Finset.sum_lt_sum_of_nonempty hs h
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne', sum_mem_eq_one hy] at this
    exact lt_irrefl _ this
  refine le_trans ?_ (Finset.le_sup' (fun u ↦ 1 - s.card * y u) hu)
  have := mul_le_mul_of_nonneg_left hyu hc.le
  rw [mul_inv_cancel₀ hc.ne'] at this
  linarith

/-- On the affine span, the gauge vanishes only at the barycentre. -/
theorem eq_baryStd_of_stdGauge_eq_zero {s : Finset ν} (hs : s.Nonempty) {y : ν → ℝ}
    (hy : y ∈ affineStd s) (h : stdGauge s hs y = 0) : y = baryStd s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hge : ∀ u ∈ s, (s.card : ℝ)⁻¹ ≤ y u := fun u hu ↦ by
    have := (Finset.sup'_le_iff hs _).1 h.le u hu
    rw [inv_le_iff_one_le_mul₀' hc]
    linarith
  have hsum : ∑ u ∈ s, (y u - (s.card : ℝ)⁻¹) = 0 := by
    rw [Finset.sum_sub_distrib, sum_mem_eq_one hy, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ hc.ne', sub_self]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun u hu ↦ sub_nonneg.2 (hge u hu)).1 hsum
  funext u
  by_cases hu : u ∈ s
  · simp only [baryStd, ite_eq_left hu]
    linarith [h0 u hu]
  · simp [baryStd, hu, hy.2 u hu]

omit [Fintype ν] [DecidableEq ν] in
/-- The gauge of the standard simplex is continuous. -/
theorem continuous_stdGauge {s : Finset ν} (hs : s.Nonempty) : Continuous (stdGauge s hs) :=
  Continuous.finset_sup'_apply hs fun u _ ↦ continuous_const.sub
    (continuous_const.mul (continuous_apply u))

omit [DecidableEq ν] in
/-- On the affine span, the gauge is at most one exactly on the closed standard simplex. -/
theorem stdGauge_le_one_iff {s : Finset ν} (hs : s.Nonempty) {y : ν → ℝ} :
    y ∈ affineStd s ∩ {y | stdGauge s hs y ≤ 1} ↔ y ∈ closedStd s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  simp only [mem_inter_iff, mem_ofPred_eq, stdGauge, Finset.sup'_le_iff, affineStd, closedStd]
  constructor
  · rintro ⟨⟨h1, hoff⟩, hle⟩
    refine ⟨fun u ↦ ?_, h1, hoff⟩
    by_cases hu : u ∈ s
    · nlinarith [hle u hu]
    · exact (hoff u hu).ge
  · rintro ⟨h0, h1, hoff⟩
    exact ⟨⟨h1, hoff⟩, fun u _ ↦ by nlinarith [h0 u]⟩

omit [DecidableEq ν] in
/-- On the affine span, the gauge is less than one exactly on the open standard simplex. -/
theorem stdGauge_lt_one_iff {s : Finset ν} (hs : s.Nonempty) {y : ν → ℝ} :
    y ∈ affineStd s ∧ stdGauge s hs y < 1 ↔ y ∈ openStd s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  simp only [stdGauge, Finset.sup'_lt_iff, affineStd, openStd, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, hoff⟩, hlt⟩
    exact ⟨fun u hu ↦ by nlinarith [hlt u hu], h1, hoff⟩
  · rintro ⟨h0, h1, hoff⟩
    exact ⟨⟨h1, hoff⟩, fun u hu ↦ by nlinarith [h0 u hu]⟩

/-- The standard simplex is a radial model about its barycentre. -/
theorem isRadialModel_closedStd {s : Finset ν} (hs : s.Nonempty) :
    IsRadialModel (closedStd s) (baryStd s) (stdGauge s hs) := by
  have h := isRadialModel_of_gauge (L := affineStd s) (baryStd_mem s hs)
    (fun z hz t _ ↦ affineStd_homothety hs hz t) (fun z t ht ↦ stdGauge_homothety hs z ht)
    (fun z hz ↦ stdGauge_nonneg hs hz) (fun _ hz ↦ eq_baryStd_of_stdGauge_eq_zero hs hz)
  have : affineStd s ∩ {z | stdGauge s hs z ≤ 1} = closedStd s :=
    Set.ext fun _ ↦ stdGauge_le_one_iff hs
  rwa [this] at h

omit [DecidableEq ν] in
/-- The points of the closed standard simplex of gauge less than one form the open simplex. -/
theorem closedStd_inter_lt_one {s : Finset ν} (hs : s.Nonempty) :
    closedStd s ∩ {z | stdGauge s hs z < 1} = openStd s := by
  ext y
  rw [← stdGauge_lt_one_iff hs]
  constructor
  · rintro ⟨hy, hlt⟩
    exact ⟨⟨hy.2.1, hy.2.2⟩, hlt⟩
  · rintro ⟨hy, hlt⟩
    exact ⟨(stdGauge_le_one_iff hs).1 ⟨hy, hlt.le⟩, hlt⟩

/-! ### The band model -/

/-- The total weight off a face `F` of `s`. -/
def faceDist (s F : Finset ν) (y : ν → ℝ) : ℝ := ∑ u ∈ s \ F, y u

/-- The smallest total weight off the faces of a family `𝓕`. -/
noncomputable def faceMin (s : Finset ν) (𝓕 : Finset (Finset ν)) (h𝓕 : 𝓕.Nonempty)
    (y : ν → ℝ) : ℝ :=
  𝓕.inf' h𝓕 fun F ↦ faceDist s F y

/-- The gauge of the region `|v| ≤ faceMin y` over the standard simplex. -/
noncomputable def bandGauge (s : Finset ν) (hs : s.Nonempty) (𝓕 : Finset (Finset ν))
    (h𝓕 : 𝓕.Nonempty) (z : (ν → ℝ) × ℝ) : ℝ :=
  max (stdGauge s hs z.1)
    (𝓕.sup' h𝓕 fun F ↦ 1 + (|z.2| - faceDist s F z.1) / faceDist s F (baryStd s))

/-- The region `|v| ≤ faceMin y` over the closed standard simplex. -/
def bandModel (s : Finset ν) (𝓕 : Finset (Finset ν)) (h𝓕 : 𝓕.Nonempty) :
    Set ((ν → ℝ) × ℝ) :=
  {z | z.1 ∈ closedStd s ∧ |z.2| ≤ faceMin s 𝓕 h𝓕 z.1}

omit [Fintype ν] in
/-- The barycentre has positive weight off a face `F` not containing `s`. -/
theorem faceDist_baryStd {s F : Finset ν} (hsF : ¬ s ⊆ F) : 0 < faceDist s F (baryStd s) := by
  obtain ⟨u, hus, huF⟩ := Finset.not_subset.1 hsF
  have hs : s.Nonempty := ⟨u, hus⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  unfold faceDist
  refine Finset.sum_pos (fun v hv ↦ ?_) ⟨u, Finset.mem_sdiff.2 ⟨hus, huF⟩⟩
  simp only [baryStd, ite_eq_left (Finset.mem_sdiff.1 hv).1]
  positivity

/-- The weight off a face is nonnegative on the closed standard simplex. -/
theorem faceDist_nonneg {s F : Finset ν} {y : ν → ℝ} (hy : y ∈ closedStd s) :
    0 ≤ faceDist s F y := Finset.sum_nonneg fun u _ ↦ hy.1 u

/-- The weight off the empty face is one on the affine span. -/
theorem faceDist_empty {s : Finset ν} {y : ν → ℝ} (hy : y ∈ affineStd s) :
    faceDist s ∅ y = 1 := by
  rw [faceDist, Finset.sdiff_empty, sum_mem_eq_one hy]

/-- A point of the open simplex has positive weight off a face `F` not containing `s`. -/
theorem faceDist_pos {s F : Finset ν} (hsF : ¬ s ⊆ F) {y : ν → ℝ} (hy : y ∈ openStd s) :
    0 < faceDist s F y := by
  obtain ⟨u, hus, huF⟩ := Finset.not_subset.1 hsF
  exact Finset.sum_pos' (fun v hv ↦ (hy.1 v (Finset.mem_sdiff.1 hv).1).le)
    ⟨u, Finset.mem_sdiff.2 ⟨hus, huF⟩, hy.1 u hus⟩

omit [Fintype ν] in
/-- The weight off a face is affine along homotheties about the barycentre. -/
theorem faceDist_homothety (s F : Finset ν) (y : ν → ℝ) (t : ℝ) :
    faceDist s F (baryStd s + t • (y - baryStd s)) =
      faceDist s F (baryStd s) + t * (faceDist s F y - faceDist s F (baryStd s)) := by
  simp only [faceDist, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

variable {s : Finset ν} (hs : s.Nonempty) {𝓕 : Finset (Finset ν)} (h𝓕 : 𝓕.Nonempty)
  (h𝓕e : ∅ ∈ 𝓕) (h𝓕s : ∀ F ∈ 𝓕, ¬ s ⊆ F)

include h𝓕s in
/-- Over the affine span, the band gauge is at most one exactly on the band region. -/
theorem mem_bandModel_iff {z : (ν → ℝ) × ℝ} :
    z ∈ {z : (ν → ℝ) × ℝ | z.1 ∈ affineStd s} ∩ {z | bandGauge s hs 𝓕 h𝓕 z ≤ 1} ↔
      z ∈ bandModel s 𝓕 h𝓕 := by
  simp only [mem_inter_iff, mem_ofPred_eq, bandGauge, max_le_iff, Finset.sup'_le_iff, bandModel,
    faceMin, Finset.le_inf'_iff]
  constructor
  · rintro ⟨hz, h1, h2⟩
    refine ⟨(stdGauge_le_one_iff hs).1 ⟨hz, h1⟩, fun F hF ↦ ?_⟩
    have hβ := faceDist_baryStd (h𝓕s F hF)
    have := h2 F hF
    rw [add_le_iff_nonpos_right, div_nonpos_iff] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (not_le.2 hβ)
    · linarith
  · rintro ⟨hz, h⟩
    refine ⟨⟨hz.2.1, hz.2.2⟩, ((stdGauge_le_one_iff hs).2 hz).2, fun F hF ↦ ?_⟩
    have hβ := faceDist_baryStd (h𝓕s F hF)
    rw [add_le_iff_nonpos_right]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [h F hF]) hβ.le

include h𝓕s in
/-- The points of the band region of band gauge less than one are those over the open simplex with
`|v| < faceMin y`. -/
theorem bandModel_inter_lt_iff {z : (ν → ℝ) × ℝ} :
    z ∈ bandModel s 𝓕 h𝓕 ∩ {z | bandGauge s hs 𝓕 h𝓕 z < 1} ↔
      z.1 ∈ openStd s ∧ |z.2| < faceMin s 𝓕 h𝓕 z.1 := by
  simp only [mem_inter_iff, mem_ofPred_eq, bandGauge, max_lt_iff, Finset.sup'_lt_iff, bandModel,
    faceMin, Finset.lt_inf'_iff]
  constructor
  · rintro ⟨⟨hz, -⟩, h1, h2⟩
    refine ⟨(stdGauge_lt_one_iff hs).1 ⟨⟨hz.2.1, hz.2.2⟩, h1⟩, fun F hF ↦ ?_⟩
    have hβ := faceDist_baryStd (h𝓕s F hF)
    have := h2 F hF
    rw [add_lt_iff_neg_left, div_neg_iff] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (not_lt.2 hβ.le)
    · linarith
  · rintro ⟨hz, h⟩
    refine ⟨⟨openStd_subset_closedStd s hz, (Finset.le_inf'_iff h𝓕 _).2 fun F hF ↦ (h F hF).le⟩,
      ((stdGauge_lt_one_iff hs).2 hz).2, fun F hF ↦ ?_⟩
    have hβ := faceDist_baryStd (h𝓕s F hF)
    rw [add_lt_iff_neg_left]
    exact div_neg_of_neg_of_pos (by linarith [h F hF]) hβ

include h𝓕e h𝓕s in
/-- The band region is a radial model about `(barycentre, 0)`. -/
theorem isRadialModel_bandModel :
    IsRadialModel (bandModel s 𝓕 h𝓕) (baryStd s, 0) (bandGauge s hs 𝓕 h𝓕) := by
  have h := isRadialModel_of_gauge (L := {z : (ν → ℝ) × ℝ | z.1 ∈ affineStd s})
    (c := (baryStd s, 0)) (baryStd_mem s hs)
    (fun z hz t _ ↦ by simpa using affineStd_homothety hs hz t) (G := bandGauge s hs 𝓕 h𝓕)
    (fun z t ht ↦ ?_) (fun z hz ↦ le_trans (stdGauge_nonneg hs hz) (le_max_left _ _))
    (fun z hz h0 ↦ ?_)
  · have : {z : (ν → ℝ) × ℝ | z.1 ∈ affineStd s} ∩ {z | bandGauge s hs 𝓕 h𝓕 z ≤ 1} =
        bandModel s 𝓕 h𝓕 :=
      Set.ext fun _ ↦ mem_bandModel_iff hs h𝓕 h𝓕s
    rwa [this] at h
  · simp only [bandGauge, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, sub_zero, zero_add]
    have h2 : (𝓕.sup' h𝓕 fun F ↦ 1 + (|t • z.2| - faceDist s F (baryStd s + t • (z.1 - baryStd s)))
        / faceDist s F (baryStd s)) = t * 𝓕.sup' h𝓕 (fun F ↦ 1 + (|z.2| - faceDist s F z.1) /
          faceDist s F (baryStd s)) := by
      rw [Finset.apply_sup'_eq_sup'_comp h𝓕 (fun x ↦ t * x) fun x y ↦ mul_max_of_nonneg x y ht]
      refine Finset.sup'_congr h𝓕 rfl fun F hF ↦ ?_
      have hβ := (faceDist_baryStd (h𝓕s F hF)).ne'
      simp only [Function.comp, faceDist_homothety, smul_eq_mul, abs_mul, abs_of_nonneg ht]
      field_simp
      ring
    rw [stdGauge_homothety hs _ ht, h2, mul_max_of_nonneg _ _ ht]
  · unfold bandGauge at h0
    have hz1 : stdGauge s hs z.1 = 0 :=
      le_antisymm (max_le_iff.1 h0.le).1 (stdGauge_nonneg hs hz)
    have hzb := eq_baryStd_of_stdGauge_eq_zero hs hz hz1
    have h2 := (Finset.sup'_le_iff h𝓕 _).1 (max_le_iff.1 h0.le).2 ∅ h𝓕e
    rw [hzb, faceDist_empty (baryStd_mem s hs)] at h2
    exact Prod.ext hzb (abs_nonpos_iff.1 (by linarith))

include h𝓕e in
/-- The band region is compact. -/
theorem isCompact_bandModel : IsCompact (bandModel s 𝓕 h𝓕) := by
  refine ((isCompact_closedStd s).prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
    ?_ fun z hz ↦ ⟨hz.1, ?_⟩
  · have hcont : Continuous fun z : (ν → ℝ) × ℝ ↦ faceMin s 𝓕 h𝓕 z.1 :=
      (Continuous.finset_inf'_apply h𝓕 fun F _ ↦
        continuous_finsetSum (s \ F) fun u _ ↦ continuous_apply u).comp continuous_fst
    exact ((isCompact_closedStd s).isClosed.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp continuous_snd) hcont)
  · have hle : faceMin s 𝓕 h𝓕 z.1 ≤ faceDist s ∅ z.1 := Finset.inf'_le _ h𝓕e
    rw [faceDist_empty ⟨hz.1.2.1, hz.1.2.2⟩] at hle
    exact abs_le.1 (hz.2.trans hle)

omit [Fintype ν] in
/-- The band gauge is continuous. -/
theorem continuous_bandGauge : Continuous (bandGauge s hs 𝓕 h𝓕) := by
  refine ((continuous_stdGauge hs).comp continuous_fst).max
    (Continuous.finset_sup'_apply h𝓕 fun F _ ↦ ?_)
  refine continuous_const.add (Continuous.div_const ?_ _)
  exact (continuous_abs.comp continuous_snd).sub
    ((continuous_finsetSum _ fun u _ ↦ continuous_apply u).comp continuous_fst)

include h𝓕s in
/-- The smallest weight off the faces of `𝓕` is positive on the open simplex. -/
theorem faceMin_pos {y : ν → ℝ} (hy : y ∈ openStd s) : 0 < faceMin s 𝓕 h𝓕 y :=
  (Finset.lt_inf'_iff h𝓕).2 fun F hF ↦ faceDist_pos (h𝓕s F hF) hy

/-- The smallest weight off the faces of `𝓕` is nonnegative on the closed simplex. -/
theorem faceMin_nonneg {y : ν → ℝ} (hy : y ∈ closedStd s) : 0 ≤ faceMin s 𝓕 h𝓕 y :=
  (Finset.le_inf'_iff h𝓕 _).2 fun _ _ ↦ faceDist_nonneg hy

end StdModels

end MMP
