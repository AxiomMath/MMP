module

public import MMP.AlgebraicTopology.SingularHomology.Excision.VertexChains
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Barycentric subdivision of affine simplices in the standard simplex

Points of the standard simplex `Δⁿ = stdSimplex ℝ (Fin (n + 1))` have barycentres, and an
`(m + 1)`-tuple `w` of points of `Δⁿ` spans the affine simplex `affine w : Δᵐ → Δⁿ`,
`t ↦ ∑ i, t i • w i`. Affine maps preserve barycentres, so push-forward of vertex chains along
an affine map commutes with the barycentric subdivision.

The subdivision shrinks simplices: if the vertices of `v` (a `(k + 1)`-tuple) are pairwise at
distance at most `D`, the vertices of every tuple occurring in `S [v]` lie in the convex hull of
`v` and are pairwise at distance at most `k / (k + 1) * D` (Hatcher, §2.1). With the Lebesgue
number lemma, for every open cover of `Δⁿ` some iterated subdivision of the identity simplex
consists of affine simplices each of which lies in a member of the cover.

## Main definitions

* `MMP.VertexChain.tupleBary`: the barycentre of finitely many points of `Δⁿ`.
* `MMP.VertexChain.affine`: the affine simplex spanned by a tuple of points.

## Main results

* `MMP.VertexChain.subdiv_single_mem`: the diameter estimate.
* `MMP.VertexChain.exists_iterate_subdiv_small`: iterated subdivision is
  subordinate to a given open cover.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, proof of Prop. 2.21.
-/

@[expose] public noncomputable section

open Finsupp Set Metric

namespace MMP

namespace VertexChain

section support

variable {R : Type*} [CommRing R] {α : Type*}

/-- A linear map sends the chains supported on `s` into `N` if it sends every generator of `s`
into `N`. -/
lemma mem_of_mem_supported {M : Type*} [AddCommGroup M] [Module R M]
    (F : (α →₀ R) →ₗ[R] M) (N : Submodule R M) {s : Set α}
    (h : ∀ a ∈ s, F (single a 1) ∈ N) {c : α →₀ R} (hc : c ∈ supported R R s) : F c ∈ N := by
  rw [supported_eq_span_single] at hc
  have : Submodule.span R ((fun i ↦ single i (1 : R)) '' s) ≤ N.comap F :=
    Submodule.span_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)
  exact this hc

/-- The cone with apex `b` on a chain supported on `s` is supported on the tuples `Fin.cons b w`,
`w ∈ s`. -/
lemma cone_mem_supported {P : Type*} (b : P) (k : ℕ) {s : Set (Fin k → P)}
    {c : Chain R P k} (hc : c ∈ supported R R s) :
    cone R b k c ∈ supported R R ((fun w ↦ (Fin.cons b w : Fin (k + 1) → P)) '' s) :=
  mem_of_mem_supported _ _ (fun w hw ↦ by
    rw [cone_single]; exact single_mem_supported R _ ⟨w, hw, rfl⟩) hc

end support

variable {n m : ℕ}

/-- The barycentre of `k + 1` points of the standard simplex `Δⁿ`. -/
def tupleBary (n : ℕ) : Bary (stdSimplex ℝ (Fin (n + 1))) := fun k v ↦
  ⟨∑ i, ((k : ℝ) + 1)⁻¹ • (v i : Fin (n + 1) → ℝ),
    (convex_stdSimplex ℝ _).sum_mem (fun _ _ ↦ by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
          field_simp)
      (fun i _ ↦ (v i).2)⟩

/-- The barycentre of `k + 1` points is `∑ i, (k + 1)⁻¹ • v i`. -/
lemma tupleBary_coe (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (tupleBary n k v : Fin (n + 1) → ℝ) = ∑ i, ((k : ℝ) + 1)⁻¹ • (v i : Fin (n + 1) → ℝ) :=
  rfl

/-- The affine simplex `Δᵐ → Δⁿ`, `t ↦ ∑ i, t i • w i`, spanned by `m + 1` points `w` of
`Δⁿ`. -/
def affine (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1))) where
  toFun t := ⟨∑ i, t i • (w i : Fin (n + 1) → ℝ),
    (convex_stdSimplex ℝ _).sum_mem (fun i _ ↦ stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t)
      (fun i _ ↦ (w i).2)⟩
  continuous_toFun := Continuous.subtype_mk (continuous_finset_sum _ fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const) _

/-- The affine simplex sends `t` to the linear combination of the points `w i` with coefficients
`t i`. -/
lemma affine_coe (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1)))
    (t : stdSimplex ℝ (Fin (m + 1))) :
    (affine w t : Fin (n + 1) → ℝ) =
      Fintype.linearCombination ℝ (fun i ↦ (w i : Fin (n + 1) → ℝ)) (t : Fin (m + 1) → ℝ) := by
  rw [Fintype.linearCombination_apply]; rfl

/-- The affine simplex spanned by `w` sends the `i`-th vertex of `Δᵐ` to `w i`. -/
lemma affine_vertex (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) (i : Fin (m + 1)) :
    affine w (stdSimplex.vertex i) = w i := by
  ext1
  rw [affine_coe]
  exact (Fintype.linearCombination_apply_single ℝ _ i 1).trans (one_smul _ _)

/-- The affine simplex spanned by the vertices of `Δⁿ` is the identity. -/
lemma affine_vertices (t : stdSimplex ℝ (Fin (n + 1))) :
    affine (fun i ↦ stdSimplex.vertex i) t = t := by
  ext1
  rw [affine_coe]
  have : Fintype.linearCombination ℝ (fun i : Fin (n + 1) ↦
      ((stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ)) =
      LinearMap.id := by
    refine LinearMap.pi_ext fun i x ↦ ?_
    rw [Fintype.linearCombination_apply_single]
    ext j
    rw [Pi.smul_apply, stdSimplex.vertex_coe, LinearMap.id_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  rw [this]; rfl

/-- Precomposing the affine simplex spanned by `w` with `stdSimplex.map f` gives the affine simplex
spanned by `w ∘ f`. -/
lemma affine_map {p : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) (f : Fin (p + 1) → Fin (m + 1))
    (t : stdSimplex ℝ (Fin (p + 1))) :
    affine w (stdSimplex.map f t) = affine (w ∘ f) t := by
  ext1
  rw [affine_coe, affine_coe, stdSimplex.map_coe]
  have : (Fintype.linearCombination ℝ (fun i ↦ (w i : Fin (n + 1) → ℝ))).comp
      (FunOnFinite.linearMap ℝ ℝ f) =
      Fintype.linearCombination ℝ (fun i ↦ ((w ∘ f) i : Fin (n + 1) → ℝ)) := by
    refine LinearMap.pi_ext fun i x ↦ ?_
    simp [Fintype.linearCombination_apply_single]
  exact congr($this (t : Fin (p + 1) → ℝ))

/-- A composite of affine simplices is the affine simplex spanned by the images of the vertices. -/
lemma affine_affine {p : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1)))
    (v : Fin (p + 1) → stdSimplex ℝ (Fin (m + 1))) (t : stdSimplex ℝ (Fin (p + 1))) :
    affine w (affine v t) = affine (affine w ∘ v) t := by
  ext1
  rw [affine_coe, affine_coe, affine_coe]
  have : (Fintype.linearCombination ℝ (fun i ↦ (w i : Fin (n + 1) → ℝ))).comp
      (Fintype.linearCombination ℝ (fun i ↦ (v i : Fin (m + 1) → ℝ))) =
      Fintype.linearCombination ℝ (fun i ↦ ((affine w ∘ v) i : Fin (n + 1) → ℝ)) := by
    refine LinearMap.pi_ext fun i x ↦ ?_
    simp only [LinearMap.comp_apply, Fintype.linearCombination_apply_single, map_smul,
      Function.comp_apply, affine_coe]
  exact congr($this (t : Fin (p + 1) → ℝ))

/-- Affine simplices preserve barycentres. -/
lemma affine_tupleBary (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) (k : ℕ)
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (m + 1))) :
    affine w (tupleBary m k v) = tupleBary n k (affine w ∘ v) := by
  ext1
  rw [affine_coe, tupleBary_coe, tupleBary_coe, map_sum]
  simp only [map_smul, Function.comp_apply, affine_coe]

section geometry

/-- The barycentre of `k + 1` points lies in their convex hull. -/
lemma tupleBary_mem_convexHull (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (tupleBary n k v : Fin (n + 1) → ℝ) ∈
      convexHull ℝ (range fun i ↦ (v i : Fin (n + 1) → ℝ)) := by
  rw [tupleBary_coe]
  exact (convex_convexHull ℝ _).sum_mem (fun _ _ ↦ by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
        field_simp)
    (fun i _ ↦ subset_convexHull ℝ _ ⟨i, rfl⟩)

/-- The barycentre of `k + 1` points at pairwise distance at most `D` is at distance at most
`k / (k + 1) * D` from every point of their convex hull. -/
lemma dist_tupleBary_le (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) {D : ℝ}
    (hD : ∀ i j, dist (v i) (v j) ≤ D) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ convexHull ℝ (range fun i ↦ (v i : Fin (n + 1) → ℝ))) :
    dist (tupleBary n k v : Fin (n + 1) → ℝ) x ≤ k / (k + 1) * D := by
  rw [dist_comm, ← mem_closedBall]
  refine convexHull_min ?_ (convex_closedBall _ _) hx
  rintro _ ⟨i, rfl⟩
  rw [mem_closedBall, dist_eq_norm, tupleBary_coe]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hv : (v i : Fin (n + 1) → ℝ) = ∑ j : Fin (k + 1), ((k : ℝ) + 1)⁻¹ • (v i : Fin (n + 1) → ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hk, one_smul]
  have h1 : ‖(v i : Fin (n + 1) → ℝ) - ∑ j, ((k : ℝ) + 1)⁻¹ • (v j : Fin (n + 1) → ℝ)‖ ≤
      ∑ j, ((k : ℝ) + 1)⁻¹ * dist (v i) (v j) := by
    conv_lhs => rw [hv, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_))
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), Subtype.dist_eq, dist_eq_norm]
    rfl
  have h2 : ∑ j, dist (v i) (v j) ≤ k * D := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), dist_self, add_zero]
    have := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j ↦ dist (v i) (v j)) D
      (fun j _ ↦ hD i j)
    simpa [Finset.card_erase_of_mem] using this
  rw [← Finset.mul_sum] at h1
  calc _ ≤ _ := h1
    _ ≤ ((k : ℝ) + 1)⁻¹ * (k * D) := by gcongr
    _ = k / (k + 1) * D := by field_simp

variable (R : Type*) [CommRing R]

private lemma ratio_le (k : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (k : ℝ) / (k + 1) * D ≤ ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1) * D := by
  refine mul_le_mul_of_nonneg_right ?_ hD
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

/-- The diameter estimate for the barycentric subdivision: if the `k + 1` vertices of `v` are
pairwise at distance at most `D`, every tuple occurring in `S [v]` has its vertices in the convex
hull of `v`, pairwise at distance at most `k / (k + 1) * D`. -/
lemma subdiv_single_mem (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) {D : ℝ}
    (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    subdiv R (tupleBary n) (k + 1) (single v 1) ∈ supported R R
      {w | (∀ i, (w i : Fin (n + 1) → ℝ) ∈ convexHull ℝ (range fun j ↦ (v j : Fin (n + 1) → ℝ)))
        ∧ ∀ i j, dist (w i) (w j) ≤ k / (k + 1) * D} := by
  induction k generalizing D with
  | zero =>
    rw [subdiv_single]
    refine supported_mono ?_ (cone_mem_supported (R := R) _ 0 (s := univ) (by simp))
    rintro _ ⟨w, -, rfl⟩
    refine ⟨fun i ↦ ?_, fun i j ↦ ?_⟩
    · rw [Fin.fin_one_eq_zero i]
      show ((tupleBary n 0 v : stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) ∈ _
      exact tupleBary_mem_convexHull 0 v
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, dist_self]
      simp
  | succ k ih =>
    have hD0 : 0 ≤ D := dist_self (v 0) ▸ hD 0 0
    rw [subdiv_single]
    have hsub : subdiv R (tupleBary n) (k + 1) (bd R (k + 1) (single v 1)) ∈ supported R R
        {w | (∀ i, (w i : Fin (n + 1) → ℝ) ∈ convexHull ℝ (range fun j ↦ (v j : Fin (n + 1) → ℝ)))
          ∧ ∀ i j, dist (w i) (w j) ≤ k / (k + 1) * D} := by
      rw [bd_single, map_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [map_smul]
      refine Submodule.smul_mem _ _ (supported_mono ?_ (ih (v ∘ i.succAbove) (fun a b ↦ hD _ _)))
      rintro w ⟨hw, hw'⟩
      refine ⟨fun a ↦ convexHull_mono ?_ (hw a), hw'⟩
      rintro _ ⟨j, rfl⟩
      exact ⟨_, rfl⟩
    refine supported_mono ?_ (cone_mem_supported (R := R) _ _ hsub)
    rintro _ ⟨w, ⟨hw, hw'⟩, rfl⟩
    have hb := fun {x : Fin (n + 1) → ℝ} (hx) ↦ dist_tupleBary_le (k + 1) v hD (x := x) hx
    refine ⟨fun i ↦ ?_, fun i j ↦ ?_⟩
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact tupleBary_mem_convexHull _ v
      · exact hw i
    · refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
      · rw [dist_self]; positivity
      · have := hb (hw j)
        simp only [Fin.cons_zero, Fin.cons_succ, Subtype.dist_eq]
        push_cast at this ⊢
        exact this
      · have := hb (hw i)
        simp only [Fin.cons_zero, Fin.cons_succ, Subtype.dist_eq]
        push_cast at this ⊢
        rw [dist_comm]
        exact this
      · simpa using (hw' i j).trans (ratio_le k hD0)

/-- One subdivision step multiplies the bound on the pairwise distances of vertices by
`k / (k + 1)`. -/
lemma subdiv_mem_supported (k : ℕ) {D : ℝ} {c : Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1)}
    (hc : c ∈ supported R R {w | ∀ i j, dist (w i) (w j) ≤ D}) :
    subdiv R (tupleBary n) (k + 1) c ∈
      supported R R {w | ∀ i j, dist (w i) (w j) ≤ k / (k + 1) * D} :=
  mem_of_mem_supported _ _ (fun w hw ↦
    supported_mono (fun _ h ↦ h.2) (subdiv_single_mem R k w hw)) hc

/-- Any two vertices of `Δⁿ` are at distance at most `1`. -/
lemma dist_vertex_le (i j : Fin (n + 1)) :
    dist (stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ (Fin (n + 1))) (stdSimplex.vertex j) ≤ 1 :=
  (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (n + 1))) (stdSimplex.vertex (S := ℝ) i).2
    (stdSimplex.vertex (S := ℝ) j).2).trans diam_stdSimplex_le

/-- The tuples occurring in the `m`-th iterated subdivision of the identity simplex of `Δⁿ` have
vertices pairwise at distance at most `(n / (n + 1)) ^ m`. -/
lemma iterate_subdiv_mem_supported (m : ℕ) :
    (subdiv R (tupleBary n) (n + 1))^[m] (single (fun i ↦ stdSimplex.vertex i) 1) ∈
      supported R R {w | ∀ i j, dist (w i) (w j) ≤ ((n : ℝ) / (n + 1)) ^ m} := by
  induction m with
  | zero => exact single_mem_supported R _ (by simpa using dist_vertex_le)
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact subdiv_mem_supported R n ih

/-- If the points `w i` are pairwise at distance at most `ε`, every point of the affine simplex
spanned by `w` is at distance at most `ε` from `w 0`. -/
lemma dist_affine_le (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) {ε : ℝ}
    (h : ∀ i j, dist (w i) (w j) ≤ ε) (t : stdSimplex ℝ (Fin (m + 1))) :
    dist (affine w t) (w 0) ≤ ε := by
  have hd : ∀ i, dist (w i) (w 0) = ‖(w i : Fin (n + 1) → ℝ) - w 0‖ := fun i ↦ by
    rw [Subtype.dist_eq, dist_eq_norm]; rfl
  rw [show dist (affine w t) (w 0) = ‖(affine w t : Fin (n + 1) → ℝ) - w 0‖ by
    rw [Subtype.dist_eq, dist_eq_norm]; rfl, affine_coe, Fintype.linearCombination_apply]
  have ht : (w 0 : Fin (n + 1) → ℝ) = ∑ i, t i • (w 0 : Fin (n + 1) → ℝ) := by
    rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]
  rw [ht, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i, ‖t i • ((w i : Fin (n + 1) → ℝ) - w 0)‖ := by
        simp_rw [smul_sub]; exact norm_sum_le _ _
    _ ≤ ∑ i, t i * ε := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_smul, Real.norm_of_nonneg (stdSimplex.zero_le t i), ← hd]
        exact mul_le_mul_of_nonneg_left (h i 0) (stdSimplex.zero_le t i)
    _ = ε := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one t, one_mul]

/-- For every open cover of `Δⁿ`, some iterated barycentric subdivision of the identity simplex
consists of affine simplices each contained in a member of the cover. -/
lemma exists_iterate_subdiv_small {ι : Type*} (U : ι → Set (stdSimplex ℝ (Fin (n + 1))))
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    ∃ m, (subdiv R (tupleBary n) (n + 1))^[m] (single (fun i ↦ stdSimplex.vertex i) 1) ∈
      supported R R {w | ∃ i, range (affine w) ⊆ U i} := by
  have : CompactSpace (stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (n + 1)))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcov.symm.subset
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ
    (show (n : ℝ) / (n + 1) < 1 by rw [div_lt_one (by positivity)]; linarith)
  refine ⟨m, supported_mono ?_ (iterate_subdiv_mem_supported R m)⟩
  intro w hw
  obtain ⟨i, hi⟩ := hball (w 0) (mem_univ _)
  refine ⟨i, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hi (mem_ball.2 ((dist_affine_le w hw t).trans_lt hm))

end geometry

end VertexChain

end MMP
