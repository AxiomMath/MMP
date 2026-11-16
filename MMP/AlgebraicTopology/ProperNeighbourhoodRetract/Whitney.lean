module

public import MMP.AlgebraicTopology.ProperNeighbourhoodRetract.Core
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Whitney boxes and neighbourhood retractions in `ℝᴺ`

Let `X` be a nonempty closed subset of `ℝᴺ` (with the sup metric). For `k ∈ ℤ` let `L_k` be the
layer `2^{-k}/2 < d(·, X) < 2 · 2^{-k}` and, for `m ∈ ℤᴺ`, `B_{k,m}` the intersection of `L_k`
with the open box of half-side `h_k = 2^{-k}/8` about `h_k m`. These boxes cover `ℝᴺ - X`, each
point lies in at most `2 · 2ᴺ` of them, and a box meeting a small ball about `x ∈ X` is small and
close to `x`. With the nearest point of `X` to a point of the box, they form the cover that
Borsuk's construction needs: a closed, locally contractible subset of `ℝᴺ` is a neighbourhood
retract.

## Main results

* `MMP.NbhdRetract.exists_retraction_pi`: the neighbourhood retraction in `ℝᴺ`.
-/

@[expose] public section

open Set Topology Filter Metric

namespace MMP

namespace NbhdRetract

variable {N : ℕ}

/-- The half-side `2^{-k}/8` of the Whitney boxes of level `k`. -/
noncomputable def whitneyScale (k : ℤ) : ℝ := (2 : ℝ) ^ (-k) / 8

/-- The Whitney box of index `(k, m)`: the box of half-side `h_k` about `h_k m`, intersected with
the layer `2^{-k}/2 < d(·, X) < 2 · 2^{-k}`. -/
def whitneyBox (X : Set (Fin N → ℝ)) (p : ℤ × (Fin N → ℤ)) : Set (Fin N → ℝ) :=
  ball (fun j ↦ (p.2 j : ℝ) * whitneyScale p.1) (whitneyScale p.1) ∩
    {y | (2 : ℝ) ^ (-p.1) / 2 < infDist y X ∧ infDist y X < 2 * (2 : ℝ) ^ (-p.1)}

open scoped Classical in
/-- A nearest point of `X` to a point of the box (or `e₀` if the box is empty). -/
noncomputable def whitneyPoint (X : Set (Fin N → ℝ)) (e₀ : Fin N → ℝ) (p : ℤ × (Fin N → ℤ)) :
    Fin N → ℝ :=
  if h : ∃ y ∈ whitneyBox X p, ∃ x ∈ X, infDist y X = dist y x then h.choose_spec.2.choose
  else e₀

/-- The half-side `whitneyScale k` is positive. -/
theorem whitneyScale_pos (k : ℤ) : 0 < whitneyScale k := by
  unfold whitneyScale
  positivity

/-- Every Whitney box is open. -/
theorem isOpen_whitneyBox (X : Set (Fin N → ℝ)) (p : ℤ × (Fin N → ℤ)) :
    IsOpen (whitneyBox X p) :=
  isOpen_ball.inter ((isOpen_lt continuous_const (continuous_infDist_pt X)).inter
    (isOpen_lt (continuous_infDist_pt X) continuous_const))

/-- If `e₀ ∈ X`, then `whitneyPoint X e₀ p` lies in `X`. -/
theorem whitneyPoint_mem {X : Set (Fin N → ℝ)} {e₀ : Fin N → ℝ} (he₀ : e₀ ∈ X)
    (p : ℤ × (Fin N → ℤ)) : whitneyPoint X e₀ p ∈ X := by
  unfold whitneyPoint
  split_ifs with h
  · exact h.choose_spec.2.choose_spec.1
  · exact he₀

/-- `2 ^ (k - 1) = 2 ^ k / 2` for integer exponents. -/
theorem two_zpow_sub_one (k : ℤ) : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
  rw [zpow_sub_one₀ two_ne_zero, div_eq_mul_inv]

/-- `2 ^ (k + 1) = 2 * 2 ^ k` for integer exponents. -/
theorem two_zpow_add_one (k : ℤ) : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
  rw [zpow_add_one₀ two_ne_zero, mul_comm]

/-- The Whitney boxes cover the complement of `X`. -/
theorem exists_mem_whitneyBox {X : Set (Fin N → ℝ)} (hX : IsClosed X) (hne : X.Nonempty)
    {y : Fin N → ℝ} (hy : y ∉ X) : ∃ p, y ∈ whitneyBox X p := by
  have hD : 0 < infDist y X := (hX.notMem_iff_infDist_pos hne).1 hy
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hD (one_lt_two : (1 : ℝ) < 2)
  set h := whitneyScale (-n)
  have hh : 0 < h := whitneyScale_pos _
  refine ⟨(-n, fun j ↦ round (y j / h)), ?_, ?_, ?_⟩
  · rw [mem_ball, dist_pi_lt_iff hh]
    intro j
    rw [Real.dist_eq]
    have h1 := abs_sub_round (y j / h)
    have h2 : y j - (round (y j / h) : ℝ) * h = (y j / h - round (y j / h)) * h := by
      field_simp
    rw [h2, abs_mul, abs_of_pos hh]
    nlinarith
  · change (2 : ℝ) ^ (-(-n)) / 2 < infDist y X
    rw [neg_neg]
    linarith [zpow_pos (two_pos : (0 : ℝ) < 2) n]
  · change infDist y X < 2 * (2 : ℝ) ^ (-(-n))
    rwa [neg_neg, ← two_zpow_add_one]

/-- A Whitney box meeting a small ball about a point `x ∈ X` has its point of `X` close to `x`
and a small level. -/
theorem whitney_small {X : Set (Fin N → ℝ)} (hX : IsClosed X) (e₀ : Fin N → ℝ) {x : Fin N → ℝ}
    (hx : x ∈ X) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ p, (whitneyBox X p ∩ ball x δ).Nonempty →
      dist (whitneyPoint X e₀ p) x < ε ∧ (2 : ℝ) ^ (-p.1) < ε := by
  refine ⟨ε / 8, by positivity, fun p ⟨z, hzB, hzx⟩ ↦ ?_⟩
  set q := (2 : ℝ) ^ (-p.1)
  have hq : 0 < q := by positivity
  have hDz : infDist z X < ε / 8 := (infDist_le_dist_of_mem hx).trans_lt hzx
  have hq' : q < ε / 4 := by linarith [hzB.2.1]
  refine ⟨?_, by linarith⟩
  have h : ∃ y ∈ whitneyBox X p, ∃ x ∈ X, infDist y X = dist y x :=
    ⟨z, hzB, hX.exists_infDist_eq_dist ⟨x, hx⟩ z⟩
  rw [whitneyPoint, dite_cond_eq_true (eq_true h)]
  have hyB : h.choose ∈ whitneyBox X p := h.choose_spec.1
  have hya := h.choose_spec.2.choose_spec.2
  set y := h.choose
  set a := h.choose_spec.2.choose
  have h1 : dist y a < 2 * q := hya ▸ hyB.2.2
  have h2 : dist y z < 2 * whitneyScale p.1 :=
    (dist_triangle_right y z (fun j ↦ (p.2 j : ℝ) * whitneyScale p.1)).trans_lt
      (by linarith [mem_ball.1 hyB.1, mem_ball.1 hzB.1])
  have h3 : whitneyScale p.1 = q / 8 := rfl
  rw [mem_ball] at hzx
  linarith [dist_triangle4 a y z x, dist_comm a y]

/-- Each point of the complement of `X` lies in at most `2 · 2ᴺ` Whitney boxes. -/
theorem whitney_order {X : Set (Fin N → ℝ)} (hX : IsClosed X) (hne : X.Nonempty)
    {y : Fin N → ℝ} (hy : y ∉ X) :
    {p | y ∈ whitneyBox X p}.Finite ∧ {p | y ∈ whitneyBox X p}.ncard ≤ 2 * 2 ^ N := by
  have hD : 0 < infDist y X := (hX.notMem_iff_infDist_pos hne).1 hy
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hD (one_lt_two : (1 : ℝ) < 2)
  set T : Finset (ℤ × (Fin N → ℤ)) := ({-n - 1, -n} : Finset ℤ).biUnion fun k ↦
    (Fintype.piFinset fun j ↦ ({⌊y j / whitneyScale k⌋, ⌊y j / whitneyScale k⌋ + 1} :
      Finset ℤ)).image fun m ↦ (k, m)
  have hsub : {p | y ∈ whitneyBox X p} ⊆ T := by
    rintro ⟨k, m⟩ ⟨hball, hl1, hl2⟩
    have hk1 : -k - 1 < n + 1 := by
      rw [← zpow_lt_zpow_iff_right₀ (one_lt_two : (1 : ℝ) < 2), two_zpow_sub_one]
      exact hl1.trans hn2
    have hk2 : n < -k + 1 := by
      rw [← zpow_lt_zpow_iff_right₀ (one_lt_two : (1 : ℝ) < 2), two_zpow_add_one]
      exact hn1.trans_lt hl2
    simp only [T, Finset.coe_biUnion, Finset.coe_image, mem_iUnion, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, mem_image, Prod.mk.injEq]
    refine ⟨k, by omega, m, Fintype.mem_piFinset.2 fun j ↦ ?_, rfl, rfl⟩
    have hh := whitneyScale_pos k
    have hj := (dist_pi_lt_iff hh).1 (mem_ball.1 hball) j
    rw [Real.dist_eq, abs_lt] at hj
    set t := y j / whitneyScale k
    have ht1 : (m j : ℝ) - 1 < t := by rw [lt_div_iff₀ hh]; linarith
    have ht2 : t < m j + 1 := by rw [div_lt_iff₀ hh]; linarith
    have hm1 : m j - 1 ≤ ⌊t⌋ := Int.le_floor.2 (by push_cast; linarith)
    have hm2 : ⌊t⌋ < m j + 1 := Int.floor_lt.2 (by push_cast; linarith)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hk : ∀ k ∈ ({-n - 1, -n} : Finset ℤ), ((Fintype.piFinset fun j ↦
      ({⌊y j / whitneyScale k⌋, ⌊y j / whitneyScale k⌋ + 1} : Finset ℤ)).image
        fun m ↦ (k, m)).card ≤ 2 ^ N := fun k _ ↦ by
    refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset]
    calc ∏ j, ({⌊y j / whitneyScale k⌋, ⌊y j / whitneyScale k⌋ + 1} : Finset ℤ).card
        ≤ ∏ _j : Fin N, 2 := Finset.prod_le_prod' fun j _ ↦ Finset.card_le_two
      _ = 2 ^ N := by simp
  have hcard : T.card ≤ 2 * 2 ^ N := by
    calc T.card ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ ({-n - 1, -n} : Finset ℤ), 2 ^ N := Finset.sum_le_sum hk
      _ ≤ 2 * 2 ^ N := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ Finset.card_le_two
  exact ⟨T.finite_toSet.subset hsub,
    (Set.ncard_le_ncard hsub T.finite_toSet).trans ((Set.ncard_coe_finset T).trans_le hcard)⟩

/-- **A closed, locally contractible subset of `ℝᴺ` is a neighbourhood retract** (Borsuk). -/
theorem exists_retraction_pi {X : Set (Fin N → ℝ)} (hX : IsClosed X)
    (hloc : ∀ x ∈ X, ∀ ε > 0, ∃ W ⊆ X, W ⊆ ball x ε ∧ ContractibleSpace W ∧
      ∃ ρ > 0, ball x ρ ∩ X ⊆ W) :
    ∃ U : Set (Fin N → ℝ), IsOpen U ∧ X ⊆ U ∧ ∃ r : (Fin N → ℝ) → Fin N → ℝ,
      ContinuousOn r U ∧ MapsTo r U X ∧ ∀ x ∈ X, r x = x := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · exact ⟨∅, isOpen_empty, subset_rfl, id, continuousOn_empty _, mapsTo_empty _ _, by simp⟩
  exact exists_retraction hX hloc (whitneyBox X) (whitneyPoint X e₀) (fun p ↦ (2 : ℝ) ^ (-p.1))
    (isOpen_whitneyBox X) (whitneyPoint_mem he₀) (fun p ↦ by positivity)
    (fun y hy ↦ exists_mem_whitneyBox hX ⟨e₀, he₀⟩ hy)
    (fun x hx ε hε ↦ whitney_small hX e₀ hx hε)
    (fun x _ ↦ ⟨1, one_pos, 2 * 2 ^ N, fun y _ hy ↦ whitney_order hX ⟨e₀, he₀⟩ hy⟩)

end NbhdRetract

end MMP
