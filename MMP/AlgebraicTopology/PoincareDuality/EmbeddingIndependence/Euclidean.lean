module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Exhaustion
public import MMP.AlgebraicTopology.PoincareDuality.Homotopy
public import MMP.AlgebraicTopology.PoincareDuality.PuncturedLow
public import MMP.AlgebraicTopology.PoincareDuality.LocalInjective
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction

/-!
# The Borel–Moore homology of `ℝⁿ` vanishes below degree `n`

For `n ≥ 1` and `q < n`, the Borel–Moore homology `H_q(ℝⁿ; R)` of locally finite singular
chains vanishes. With `borelMooreHomology.isZero_of_dim_lt` (degrees `> n`) and the top-degree
computation `H_n ℝⁿ ≅ R`, this is the case `X = Y = ℝⁿ` of Poincaré–Alexander duality, and the
convex case of the induction on open sets proving it.

The proof runs along the exhaustion of `ℝⁿ` by the closed (sup-norm) balls `B_j = B̄(0, j + 1)`
(`borelMooreHomology.isZero_of_exhaustion`):

* `H_{k+1}(ℝⁿ, ℝⁿ - B_j) = 0` for `k + 1 < n`: the local homology at `0` vanishes there
  (`relVanishing_singleton_zero_low`), and the box step (`isRelBoundary_of_convex`) passes from
  `0` to the ball.
* The Mittag-Leffler condition `H_{m+1}(E, E - B̄(0, r')) ↠ H_{m+1}(E, E - B̄(0, r))` holds in
  every degree and every normed space, for `0 < r ≤ r'`: the scaling `x ↦ (r' / r) x` maps
  `E - B̄(0, r)` into `E - B̄(0, r')`, and the straight-line homotopy from the identity keeps
  `E - B̄(0, r)` inside itself, so for a relative cycle `c` the prism `P` gives
  `c - (r'/r)_# c + ∂ P c = -P ∂ c` in `E - B̄(0, r)` (`relSurj_closedBall`).
* In degree `0`, `H_0(E, E - K) = 0` for every compact `K` of a nonzero normed space: a
  translation moves the finitely many vertices of a `0`-chain off `K`
  (`isRelBoundary_zero_of_isCompact`).

## Main results

* `MMP.SingularChain.relSurj_closedBall`: the Mittag-Leffler condition for balls.
* `MMP.SingularChain.relVanishing_closedBall_low`:
  `H_{k+1}(ℝⁿ, ℝⁿ - B̄(0, r)) = 0` for `k + 1 < n`.
* `MMP.SingularChain.isRelBoundary_zero_of_isCompact`: `H_0(E, E - K) = 0`.
* `MMP.borelMooreHomology.isZero_euclidean_of_lt`: `H_q ℝⁿ = 0` for `q < n`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial Finsupp

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R]

section scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scaling `x ↦ a • x`. -/
def scaleMap (a : ℝ) : C(E, E) := ⟨fun x ↦ a • x, by fun_prop⟩

/-- The straight-line homotopy `(x, t) ↦ (1 + t (a - 1)) • x` from the identity to `scaleMap a`. -/
def scaleHomotopy (a : ℝ) : C(E × unitInterval, E) :=
  ⟨fun p ↦ (1 + (p.2 : ℝ) * (a - 1)) • p.1, by fun_prop⟩

/-- For `1 ≤ a`, the homotopy `scaleHomotopy a` does not decrease norms: `‖x‖ ≤ ‖F (x, t)‖`. -/
lemma norm_scaleHomotopy (a : ℝ) (ha : 1 ≤ a) (p : E × unitInterval) :
    ‖p.1‖ ≤ ‖scaleHomotopy a p‖ := by
  change ‖p.1‖ ≤ ‖(1 + (p.2 : ℝ) * (a - 1)) • p.1‖
  have h0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
  have h1 : 1 ≤ 1 + (p.2 : ℝ) * (a - 1) := by nlinarith
  rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  nlinarith [norm_nonneg p.1]

/-- **The Mittag-Leffler condition for concentric closed balls**: for `0 < r ≤ r'`, the map
`H_{m+1}(E, E - B̄(0, r')) → H_{m+1}(E, E - B̄(0, r))` is surjective, in every degree. -/
theorem relSurj_closedBall (m : ℕ) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    RelSurj R E m (Metric.closedBall 0 r) (Metric.closedBall 0 r') := by
  intro c hc
  set a := r' / r with ha_def
  have ha : 1 ≤ a := by rw [ha_def, le_div_iff₀ hr]; linarith
  have hF0 : ∀ x : E, scaleHomotopy a (x, 0) = ContinuousMap.id E x := fun x ↦ by
    simp [scaleHomotopy]
  have hF1 : ∀ x : E, scaleHomotopy a (x, 1) = scaleMap a x := fun x ↦ by
    simp [scaleHomotopy, scaleMap]
  have key := bd_prism_add_prism_bd (R := R) (scaleHomotopy a) hF0 hF1 m c
  rw [postcomp_id] at key
  refine ⟨postcomp R (scaleMap a) (m + 1) c, -prism R (scaleHomotopy a) (m + 1) c, ?_, ?_⟩
  · rw [← postcomp_bd]
    refine postcomp_mem_inside _ (fun x hx ↦ ?_) hc
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx ⊢
    change r' < ‖a • x‖
    rw [norm_smul, Real.norm_of_nonneg (by linarith), ha_def, div_mul_eq_mul_div,
      lt_div_iff₀ hr]
    nlinarith
  · have : c - postcomp R (scaleMap a) (m + 1) c - bd R (m + 1)
        (-prism R (scaleHomotopy a) (m + 1) c) = -prism R (scaleHomotopy a) m (bd R m c) := by
      rw [map_neg, sub_neg_eq_add, ← sub_eq_zero]
      rw [eq_sub_of_add_eq key]
      abel
    rw [this]
    refine Submodule.neg_mem _ (prism_mem_inside _ (fun p hp ↦ ?_) hc)
    have hp1 : p.1 ∈ (Metric.closedBall (0 : E) r)ᶜ := hp.1
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hp1 ⊢
    exact hp1.trans_le (norm_scaleHomotopy a ha p)

end scaling

section translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`H_0(E, E - K) = 0`** for a compact `K` of a nonzero normed space: every `0`-chain is a
boundary plus a chain off `K`, by translating its vertices off `K`. -/
theorem isRelBoundary_zero_of_isCompact [Nontrivial E] {K : Set E} (hK : IsCompact K)
    (c : Chain R E 0) : IsRelBoundary R 0 K c := by
  set S := ⋃ ν ∈ c.support, range ν
  have hS : IsCompact S := isCompact_biUnion_range c
  obtain ⟨A, hA⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨B, hB⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  set v : E := ((|A| + |B| + 1) / ‖v₀‖) • v₀
  have hv : ‖v‖ = |A| + |B| + 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv₀)]
  let F : C(E × unitInterval, E) := ⟨fun p ↦ p.1 + (p.2 : ℝ) • v, by fun_prop⟩
  let τ : C(E, E) := ⟨fun x ↦ x + v, by fun_prop⟩
  have key := bd_prism_zero (R := R) F (f := ContinuousMap.id E) (g := τ)
    (fun x ↦ by simp [F]) (fun x ↦ by simp [F, τ]) c
  rw [postcomp_id] at key
  refine ⟨-prism R F 0 c, ?_⟩
  rw [map_neg, sub_neg_eq_add, key, add_sub_cancel]
  refine postcomp_mem_inside _ (fun x hx ↦ ?_) (mem_inside_biUnion_range c)
  intro hxK
  have h1 := hB hx
  have h2 := hA hxK
  simp only [Metric.mem_closedBall, dist_zero_right] at h1 h2
  change ‖x + v‖ ≤ A at h2
  have h3 : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
    calc ‖v‖ = ‖(x + v) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + v‖ + ‖x‖ := norm_sub_le _ _
  rw [hv] at h3
  linarith [le_abs_self A, le_abs_self B]

end translation

section euclidean

/-- **`H_{k+1}(ℝⁿ, ℝⁿ - B̄(0, r)) = 0` for `k + 1 < n`** (sup norm, `r ≥ 0`). -/
theorem relVanishing_closedBall_low {n k : ℕ} (hk : k + 1 < n) {r : ℝ} (hr : 0 ≤ r) :
    RelVanishing R (Fin n → ℝ) k (Metric.closedBall 0 r) := by
  intro c hc
  refine isRelBoundary_of_convex (convex_closedBall 0 r) Metric.isBounded_closedBall
    (Metric.mem_closedBall_self hr) hc ?_
  refine relVanishing_singleton_zero_low n k hk c (inside_mono k ?_ hc)
  rw [compl_subset_compl, singleton_subset_iff]
  exact Metric.mem_closedBall_self hr

end euclidean

end SingularChain

namespace borelMooreHomology

open LocallyFiniteChain SingularChain

variable (R : Type) [CommRing R]

/-- The exhaustion of `ℝⁿ` by the closed balls `B̄(0, j + 1)`. -/
abbrev euclideanBall (n : ℕ) (j : ℕ) : Set (TopCat.of (Fin n → ℝ)) :=
  Metric.closedBall (0 : Fin n → ℝ) (j + 1)

/-- Each ball `euclideanBall n j` is compact. -/
lemma isCompact_euclideanBall (n j : ℕ) : IsCompact (euclideanBall n j) :=
  isCompact_closedBall _ _

/-- The balls `euclideanBall n j` increase with `j`. -/
lemma monotone_euclideanBall (n : ℕ) : Monotone (euclideanBall n) := fun i j hij ↦
  Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hij 1)

/-- Every point of `ℝⁿ` has some ball `euclideanBall n j` as a neighbourhood. -/
lemma exists_euclideanBall_mem_nhds (n : ℕ) (x : TopCat.of (Fin n → ℝ)) :
    ∃ j, euclideanBall n j ∈ 𝓝 x := by
  obtain ⟨j, hj⟩ := exists_nat_gt ‖(x : Fin n → ℝ)‖
  refine ⟨j, Metric.closedBall_mem_nhds_of_mem ?_⟩
  rw [mem_ball_zero_iff]
  linarith

/-- The Mittag-Leffler condition for the exhaustion by `euclideanBall n`: the map
`H_{m+1}(ℝⁿ, ℝⁿ - B_{j+1}) → H_{m+1}(ℝⁿ, ℝⁿ - B_j)` is surjective. -/
lemma relSurjBM_euclideanBall (n m j : ℕ) :
    RelSurjBM (TopCat.of (Fin n → ℝ)) R (ModuleCat.of R R) m (euclideanBall n j)
      (euclideanBall n (j + 1)) :=
  relSurjBM_of_relSurj (relSurj_closedBall m (by positivity) (by push_cast; linarith))

/-- **The Borel–Moore homology of `ℝⁿ` vanishes in positive degrees below `n`**:
`H_{k+1}(ℝⁿ; R) = 0` for `k + 1 < n`. -/
theorem isZero_euclidean_succ_of_lt {n k : ℕ} (hk : k + 1 < n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) ((k + 1 : ℕ) : ℤ)) :=
  isZero_of_exhaustion (euclideanBall n) (isCompact_euclideanBall n) (monotone_euclideanBall n)
    (exists_euclideanBall_mem_nhds n) k
    (fun j ↦ relVanishingBM_of_relVanishing (relVanishing_closedBall_low hk (by positivity)))
    (fun j ↦ relSurjBM_euclideanBall R n (k + 1) j)

/-- **The Borel–Moore homology of `ℝⁿ` vanishes in degree `0`** for `n ≥ 1`. -/
theorem isZero_euclidean_zero {n : ℕ} (hn : 1 ≤ n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) ((0 : ℕ) : ℤ)) := by
  haveI : Nontrivial (Fin n → ℝ) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  set X := TopCat.of (Fin n → ℝ)
  refine IsZero.of_iso ?_ (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) X 0)
  refine HomologicalComplex.ExactAt.isZero_homology (K := borelMooreChainComplex R _ X)
    (i := 0) ?_
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  suffices H : ∀ z : (borelMooreChainComplex R (ModuleCat.of R R) X).X 0,
      ∃ w : (borelMooreChainComplex R (ModuleCat.of R R) X).X 1,
        ((borelMooreChainComplex R (ModuleCat.of R R) X).d 1 0).hom w = z from
    fun z _ ↦ H z
  intro z
  have hz : ∀ j, ∃ w : (borelMooreChainComplex R (ModuleCat.of R R) X).X 1,
      IsOffChain (euclideanBall n j)
        (z - ((borelMooreChainComplex R (ModuleCat.of R R) X).d 1 0).hom w) := by
    intro j
    set K := euclideanBall n j
    have hK : IsCompact K := isCompact_euclideanBall n j
    set t := truncChain K z
    have ht := finite_support_truncChain hK z
    obtain ⟨w, hw⟩ := isRelBoundary_zero_of_isCompact (R := R) hK (toFinsupp t ht)
    refine ⟨ofFinsupp w, ?_⟩
    have h1 : IsOffChain K (t - ((borelMooreChainComplex R _ X).d 1 0).hom (ofFinsupp w)) := by
      rw [d_ofFinsupp, ← ofFinsupp_toFinsupp t ht, ← ofFinsupp_sub, isOffChain_ofFinsupp_iff]
      exact hw
    have := (isOffChain_sub_truncChain K z).add h1
    convert this using 1
    abel
  obtain ⟨w, hw⟩ := exists_d_eq_of_exhaustion (euclideanBall n) (isCompact_euclideanBall n)
    (monotone_euclideanBall n) (exists_euclideanBall_mem_nhds n) (m := 0) z hz
    (fun j ↦ relSurjBM_euclideanBall R n 0 j)
  exact ⟨w, hw⟩

/-- **`H_q(ℝⁿ; R) = 0` for `q < n`.** -/
theorem isZero_euclidean_of_lt {n q : ℕ} (hq : q < n) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) (q : ℤ)) := by
  rcases q with _ | k
  · exact isZero_euclidean_zero R (by omega)
  · exact isZero_euclidean_succ_of_lt R hq

end borelMooreHomology

end MMP
