module
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ConeDatumClosure
public import MMP.Analysis.Convex.FiniteDimensional

/-!
# Exact finite-sum decomposition of the cone of a cone datum

For a cone datum `(N_ℤ, NE̅, K, a)`, every point of `NE̅` is a finite sum `c + r₁ + ⋯ + r_s` with
`c ∈ NE̅`, `K(c) ≥ 0`, and `rᵢ` in pairwise distinct rays `Rᵢ ∈ 𝓡(NE̅, K)`; conversely every
such sum lies in `NE̅`. Unlike `MMP.Positivity.ConeDatum.cone_eq_closure_nonneg_add_sum_rays`,
no closure is taken.

The proof fixes an integral form `G` positive on `NE̅ ∖ {0}`. The slice
`{z ∈ NE̅ : G(z) = 1}` is compact and convex, hence the convex hull of its extreme points
(Minkowski). An extreme point `s` spans an extremal ray of `NE̅`; when `K(s) < 0`, the
decomposition `NE̅ = NE̅_{K+εG≥0} + ∑ R` with `ε = -K(s)/2` forces `s` onto a ray of
`𝓡(NE̅, K)`. So the slice, and by rescaling all of `NE̅`, lies in the convex cone of finite sums.

## Main results

* `MMP.Positivity.ConeDatum.cone_eq_nonneg_add_sum_negativeRationalRays`
-/

@[expose] public noncomputable section

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

namespace ConeDatum

/-- Minkowski's theorem in a finite-dimensional real topological vector space. -/
private theorem subset_convexHull_extremePoints {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {S : Set V} (hS : IsCompact S) (hSc : Convex ℝ S) :
    S ⊆ convexHull ℝ (S.extremePoints ℝ) := by
  intro x hx
  let e := toEuclidean (E := V)
  have hex : e x ∈ convexHull ℝ ((e '' S).extremePoints ℝ) := by
    rw [MMP.Resolution.Bridges.convexHull_extremePoints_eq (hS.image e.continuous)
      (hSc.linear_image e.toLinearMap)]
    exact ⟨x, hx, rfl⟩
  rw [← image_extremePoints e S, show e '' S.extremePoints ℝ =
    e.toLinearMap '' S.extremePoints ℝ from rfl, ← LinearMap.image_convexHull] at hex
  obtain ⟨y, hy, hyx⟩ := hex
  exact e.injective hyx ▸ hy

/-- An extreme point `s` of the slice `{z ∈ C : G(z) = 1}` of a convex cone `C` spans an
extremal ray: every `u ∈ C` with `s - u ∈ C` is the multiple `G(u) • s`. -/
private theorem eq_smul_of_mem_extremePoints_slice {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : PointedCone ℝ V} {G : Module.Dual ℝ V} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) {s : V}
    (hs : s ∈ ({z | z ∈ C ∧ G z = 1} : Set V).extremePoints ℝ) {u : V} (hu : u ∈ C)
    (hsu : s - u ∈ C) : u = G u • s := by
  obtain ⟨⟨-, hGs⟩, hext⟩ := hs
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  rcases eq_or_ne (s - u) 0 with hv0 | hv0
  · rw [← sub_eq_zero.1 hv0, hGs, one_smul]
  have hGu := hG u hu hu0
  have hGv := hG _ hsu hv0
  have mem {w} (hw : w ∈ C) (hGw : 0 < G w) : (G w)⁻¹ • w ∈ {z | z ∈ C ∧ G z = 1} :=
    ⟨C.smul_mem (inv_nonneg.2 hGw.le) hw, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGw.ne']⟩
  have h1 := hext (mem hu hGu) (mem hsu hGv) ⟨G u, G (s - u), hGu, hGv,
    by rw [map_sub, hGs]; ring, by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ hGu.ne', mul_inv_cancel₀ hGv.ne', one_smul,
        one_smul, add_sub_cancel]⟩
  rw [← h1, smul_smul, mul_inv_cancel₀ hGu.ne', one_smul]

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- An extreme point `s` of the slice `{z ∈ NE̅ : G(z) = 1}` with `K(s) < 0` lies on a ray of
`𝓡(NE̅, K)`: decompose `s` with `ε = -K(s)/2`; extremality makes every summand a multiple of `s`,
which kills the `NE̅_{K+εG≥0}` part and puts `s` on the ray of a nonzero summand. -/
private theorem exists_mem_negativeRationalRays_of_mem_extremePoints (D : ConeDatum N)
    {G : Module.Dual ℝ (ℝ ⊗[ℤ] N)} (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < G z) {s : ℝ ⊗[ℤ] N}
    (hs : s ∈ ({z | z ∈ D.cone ∧ G z = 1} : Set _).extremePoints ℝ)
    (hK : realOfRatForm N D.form s < 0) : ∃ R ∈ D.negativeRationalRays, s ∈ R := by
  classical
  obtain ⟨hsC, hGs⟩ := hs.1
  obtain ⟨S, hS, hCeq⟩ := cone_eq_nonneg_add_sum_rays D hG (ε := -realOfRatForm N D.form s / 2)
    (by linarith)
  obtain ⟨c, hc, hKc, r, hr, hseq⟩ := hCeq.subset hsC
  have hSr : ∀ R ∈ S, R ∈ D.negativeRationalRays := fun R hR =>
    (hS.subset (Finset.mem_coe.2 hR)).1
  have hRP := fun R (hR : R ∈ S) =>
    zero_mem_add_mem_smul_mem_subset_of_mem_negativeRationalRays D (hSr R hR)
  have hrC : ∀ R ∈ S, r R ∈ D.cone := fun R hR => (hRP R hR).2.2.2 (hr R hR)
  have hcs := eq_smul_of_mem_extremePoints_slice hG hs hc
    (by rw [hseq, add_sub_cancel_left]; exact D.cone.sum_mem hrC)
  have hGc : G c = 0 := by
    have : 0 ≤ G c := (eq_or_ne c 0).elim (fun h => h ▸ (map_zero G).ge) fun h => (hG c hc h).le
    rw [hcs, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hGs] at hKc
    nlinarith
  rw [hcs, hGc, zero_smul, zero_add] at hseq
  obtain ⟨R, hR, hrR⟩ : ∃ R ∈ S, r R ≠ 0 := by
    by_contra! hne
    rw [Finset.sum_eq_zero hne] at hseq
    simp [hseq] at hGs
  have hrs := eq_smul_of_mem_extremePoints_slice hG hs (hrC R hR) (by
    rw [hseq, ← Finset.add_sum_erase S r hR, add_sub_cancel_left]
    exact D.cone.sum_mem fun R' hR' => hrC R' (Finset.mem_of_mem_erase hR'))
  have hGr := hG _ (hrC R hR) hrR
  refine ⟨R, hSr R hR, ?_⟩
  rw [show s = (G (r R))⁻¹ • r R by rw [eq_inv_smul_iff₀ hGr.ne', ← hrs]]
  exact (hRP R hR).2.2.1 _ (hr R hR) _ (inv_nonneg.2 hGr.le)

/-- **Exact cone decomposition.** For a cone datum `(N_ℤ, NE̅, K, a)`,
`NE̅ = NE̅_{K≥0} + ∑_{R ∈ 𝓡(NE̅, K)} R`, the set of finite sums `c + ∑_{R ∈ S} r_R` with
`c ∈ NE̅`, `K(c) ≥ 0`, `S` a finite set of rays in `MMP.Mori.ConeDatum.negativeRationalRays` and
`r_R ∈ R`. No closure is taken. -/
@[mmp "lem_mmp_foundation_formal_cone_decomposition"]
public theorem cone_eq_nonneg_add_sum_negativeRationalRays (D : ConeDatum N) :
    (D.cone : Set (ℝ ⊗[ℤ] N)) =
      {x | ∃ c ∈ D.cone, 0 ≤ realOfRatForm N D.form c ∧
        ∃ (S : Finset (Set (ℝ ⊗[ℤ] N))) (r : Set (ℝ ⊗[ℤ] N) → ℝ ⊗[ℤ] N),
          (∀ R ∈ S, R ∈ D.negativeRationalRays ∧ r R ∈ R) ∧ x = c + ∑ R ∈ S, r R} := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  let T := nonnegAddSumRays D
  refine Set.Subset.antisymm (fun x hx => ?_) (nonnegAddSumRays_le D)
  obtain ⟨H₀, hH₀, -⟩ := exists_intForm_pos_and_add_coord_pos D (Module.Free.chooseBasis ℤ N)
  set G := realOfIntForm N H₀
  set S : Set (ℝ ⊗[ℤ] N) := {z | z ∈ D.cone ∧ G z = 1}
  have hScpt : IsCompact S :=
    (isCompact_slice (isCone_coe D.cone) D.isClosed_cone hH₀ 1).of_isClosed_subset
      (D.isClosed_cone.inter (isClosed_eq (LinearMap.continuous_of_finiteDimensional G)
        continuous_const)) fun z hz => ⟨hz.1, hz.2.le⟩
  have hext : S.extremePoints ℝ ⊆ T := fun s hs =>
    (le_or_gt 0 (realOfRatForm N D.form s)).elim
      (fun hK => ⟨s, hs.1.1, hK, ∅, fun _ => 0, by simp, by simp⟩) fun hK => by
      obtain ⟨R, hR, hsR⟩ := exists_mem_negativeRationalRays_of_mem_extremePoints D hH₀ hs hK
      exact ⟨0, D.cone.zero_mem, by simp, {R}, fun _ => s, by simpa using ⟨hR, hsR⟩, by simp⟩
  have hST : S ⊆ T := (subset_convexHull_extremePoints hScpt
    (D.cone.convex.inter (convex_hyperplane G.isLinear 1))).trans (convexHull_min hext T.convex)
  rcases eq_or_ne x 0 with rfl | hx0
  · exact T.zero_mem
  have hGx := hH₀ x hx hx0
  have := T.smul_mem hGx.le (hST ⟨D.cone.smul_mem (inv_nonneg.2 hGx.le) hx,
    by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGx.ne']⟩)
  rwa [smul_smul, mul_inv_cancel₀ hGx.ne', one_smul] at this

end ConeDatum

end MMP.Positivity
