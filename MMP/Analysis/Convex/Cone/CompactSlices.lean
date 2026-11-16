module

public import MMP.Analysis.Convex.Cone.ExtremalRays

/-!
# Compact slices, closed sums and strictly positive combinations of cones (KM 3.3)

Let `V` be a finite-dimensional real vector space.

* For a closed cone `C` and `G ∈ V^*` positive on `C ∖ {0}`, every slice `{z ∈ C : G(z) ≤ t}`
  is compact.
* For a closed convex cone `C` with `C ∩ (-C) = {0}`, a sum `C₁ + ⋯ + C_k` of closed convex cones
  `Cᵢ ⊆ C` is closed.
* If `λ ≥ 0` on such a `C` cuts out the closed cone `F = {λ = 0} ∩ C` and `K < 0` on `F ∖ {0}`,
  then `mλ - K > 0` on `C ∖ {0}` for all `m ≫ 0`.

## Main results

* `MMP.Positivity.isCompact_slice`
* `MMP.Positivity.isClosed_sum_cones`
* `MMP.Positivity.exists_forall_ge_pos_smul_sub`
-/

@[expose] public noncomputable section

namespace MMP.Positivity

open MMP.Mori

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

/-- The preimage of a cone under a linear map is a cone. -/
theorem isCone_preimage {U W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W]
    {C : Set W} (hC : IsCone ℝ C) (f : U →ₗ[ℝ] W) : IsCone ℝ (f ⁻¹' C) :=
  ⟨by simpa using hC.1, fun v hv c hc => by simpa [map_smul] using hC.2 _ hv c hc⟩

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a closed cone in a finite-dimensional normed space, a linear form positive off `0` is
bounded below by a positive multiple of the norm. -/
theorem exists_pos_mul_norm_le_of_forall_pos {C : Set E} (hC : IsCone ℝ C) (hCcl : IsClosed C)
    {G : E →ₗ[ℝ] ℝ} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) :
    ∃ δ > 0, ∀ z ∈ C, δ * ‖z‖ ≤ G z := by
  have hS : IsCompact (C ∩ Metric.sphere (0 : E) 1) :=
    (isCompact_sphere 0 1).inter_left hCcl
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hscale : ∀ z ∈ C, z ≠ 0 → ‖z‖⁻¹ • z ∈ C ∩ Metric.sphere (0 : E) 1 := by
    intro z hz hz0
    refine ⟨smul_mem_of_isCone hC hz (inv_nonneg.2 (norm_nonneg z)), ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
  have hhom : ∀ z : E, G z = ‖z‖ * G (‖z‖⁻¹ • z) := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz0), one_mul]
  rcases (C ∩ Metric.sphere (0 : E) 1).eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · exact absurd (hscale z hz hz0) (by rw [hSe]; exact Set.notMem_empty _)
  · obtain ⟨s, hs, hmin⟩ := hS.exists_isMinOn hSne hGc.continuousOn
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    refine ⟨G s, hG s hs.1 hs0, fun z hz => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · rw [hhom z, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hscale z hz hz0)) (norm_nonneg z)

/-- Compact slices of a closed cone in a finite-dimensional normed space. -/
theorem isCompact_slice_of_normed {C : Set E} (hC : IsCone ℝ C) (hCcl : IsClosed C)
    {G : E →ₗ[ℝ] ℝ} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) (t : ℝ) :
    IsCompact {z | z ∈ C ∧ G z ≤ t} := by
  obtain ⟨δ, hδ, hδG⟩ := exists_pos_mul_norm_le_of_forall_pos hC hCcl hG
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  refine Metric.isCompact_of_isClosed_isBounded
    (hCcl.inter (isClosed_le hGc continuous_const)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := t / δ)).subset fun z hz => ?_
  rw [mem_closedBall_zero_iff, le_div_iff₀ hδ, mul_comm]
  exact (hδG z hz.1).trans hz.2

/-- A closed salient convex cone in a finite-dimensional normed space admits a continuous linear
form positive on its nonzero elements. -/
theorem exists_dual_pos_of_salient_of_normed {C : Set E} (hC : IsCone ℝ C) (hCc : Convex ℝ C)
    (hCcl : IsClosed C) (hCs : ∀ z ∈ C, -z ∈ C → z = 0) :
    ∃ G : E →L[ℝ] ℝ, ∀ z ∈ C, z ≠ 0 → 0 < G z := by
  have key : ∀ s ∈ C, s ≠ 0 → ∃ f : E →L[ℝ] ℝ, (∀ b ∈ C, 0 ≤ f b) ∧ 0 < f s := by
    intro s hs hs0
    have hns : -s ∉ C := fun h => hs0 (hCs s hs h)
    obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed hCc hCcl hns
    have hu : u < 0 := by simpa using hfC 0 hC.1
    refine ⟨f, fun b hb => ?_, ?_⟩
    · by_contra hneg
      push Not at hneg
      have hc : 0 < u / f b := div_pos_of_neg_of_neg hu hneg
      have := hfC _ (hC.2 b hb _ hc)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hneg.ne] at this
      exact lt_irrefl _ this
    · rw [map_neg] at hfu
      linarith
  have hS : IsCompact (C ∩ Metric.sphere (0 : E) 1) := (isCompact_sphere 0 1).inter_left hCcl
  have hS0 : ∀ s ∈ C ∩ Metric.sphere (0 : E) 1, s ≠ 0 := by
    rintro s hs rfl
    simp at hs
  choose! f hfC hfs using key
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : (C ∩ Metric.sphere (0 : E) 1 : Set E) => {z | 0 < f s z})
    (fun s => isOpen_lt continuous_const (f s).continuous)
    (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hfs s hs.1 (hS0 s hs)⟩)
  refine ⟨∑ i ∈ t, f i, fun z hz hz0 => ?_⟩
  have hzS : ‖z‖⁻¹ • z ∈ C ∩ Metric.sphere (0 : E) 1 := by
    refine ⟨smul_mem_of_isCone hC hz (inv_nonneg.2 (norm_nonneg z)), ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
  obtain ⟨i, hi, hiz⟩ := Set.mem_iUnion₂.1 (ht hzS)
  have hpos : 0 < f i z := by
    have hinv : 0 < ‖z‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hz0)
    rw [Set.mem_ofPred_eq, map_smul, smul_eq_mul] at hiz
    exact pos_of_mul_pos_right hiz hinv.le
  rw [sum_apply]
  exact Finset.sum_pos' (fun j _ => hfC j j.2.1 (hS0 j j.2) z hz) ⟨i, hi, hpos⟩

end Normed

/-- **Positive forms on pointed cones.** A closed convex cone `C` with `C ∩ (-C) = {0}` in a
finite-dimensional real vector space admits a linear form positive on `C ∖ {0}`. -/
theorem exists_dual_pos_of_salient {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C)
    (hCcl : IsClosed C) (hCs : C ∩ -C = {0}) :
    ∃ G : Module.Dual ℝ V, ∀ z ∈ C, z ≠ 0 → 0 < G z := by
  let e := toEuclidean (E := V)
  have hs : ∀ z ∈ e.symm ⁻¹' C, -z ∈ e.symm ⁻¹' C → z = 0 := by
    intro z hz hnz
    have : e.symm z ∈ C ∩ -C := ⟨hz, by simpa using hnz⟩
    rw [hCs] at this
    simpa using this
  obtain ⟨g, hg⟩ := exists_dual_pos_of_salient_of_normed (isCone_preimage hC e.symm.toLinearMap)
    (hCc.linear_preimage e.symm.toLinearMap) (hCcl.preimage e.symm.continuous) hs
  exact ⟨(g : _ →ₗ[ℝ] ℝ).comp e.toLinearMap, fun z hz hz0 =>
    hg (e z) (by simpa using hz) (by simpa using hz0)⟩

/-- **Compact slices** (KM 3.3 Steps 3, 4, 6). Let `C ⊆ V` be a closed cone, `G ∈ V^*` with
`G(z) > 0` for all `z ∈ C ∖ {0}`, and `t ≥ 0`. Then `{z ∈ C : G(z) ≤ t}` is compact (for every real
`t`). -/
@[mmp "lem_km3b_cone_slice_compact"]
theorem isCompact_slice {C : Set V} (hC : IsCone ℝ C) (hCcl : IsClosed C) {G : Module.Dual ℝ V}
    (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) (t : ℝ) :
    IsCompact {z | z ∈ C ∧ G z ≤ t} := by
  let e := toEuclidean (E := V)
  have heq : {z | z ∈ C ∧ G z ≤ t} =
      e.symm '' {z | z ∈ e.symm ⁻¹' C ∧ (G.comp e.symm.toLinearMap) z ≤ t} := by
    ext z
    constructor
    · intro hz
      exact ⟨e z, by simpa using hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [heq]
  exact (isCompact_slice_of_normed (isCone_preimage hC e.symm.toLinearMap)
    (hCcl.preimage e.symm.continuous) (G := G.comp e.symm.toLinearMap)
    (fun z hz hz0 => hG _ hz (by simpa using hz0)) t).image e.symm.continuous

/-- **KM 3.3 Steps 4, 6.** Let `C ⊆ V` be a closed convex cone with `C ∩ (-C) = {0}` and
`C₁, …, C_k ⊆ C` closed convex cones. Then `C₁ + ⋯ + C_k` is closed. Convexity of the `Cᵢ` is not
used. -/
@[mmp "lem_km3b_cone_sum_closed"]
theorem isClosed_sum_cones {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    (hCs : C ∩ -C = {0}) {k : ℕ} (D : Fin k → Set V) (hD : ∀ i, IsCone ℝ (D i))
    (hDcl : ∀ i, IsClosed (D i)) (hDC : ∀ i, D i ⊆ C) :
    IsClosed {x | ∃ c : Fin k → V, (∀ i, c i ∈ D i) ∧ x = ∑ i, c i} := by
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient hC hCc hCcl hCs
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hG0 : ∀ z ∈ C, 0 ≤ G z := fun z hz => by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · exact (hG z hz hz0).le
  set X := {x | ∃ c : Fin k → V, (∀ i, c i ∈ D i) ∧ x = ∑ i, c i}
  have hXtcl : ∀ t, IsClosed (X ∩ {x | G x ≤ t}) := by
    intro t
    have hXt : X ∩ {x | G x ≤ t} = (fun c : Fin k → V => ∑ i, c i) ''
        (Set.univ.pi fun i => {z | z ∈ D i ∧ G z ≤ t}) ∩ {x | G x ≤ t} := by
      ext x
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, hx⟩
        refine ⟨⟨c, fun i _ => ⟨hc i, le_trans ?_ hx⟩, rfl⟩, hx⟩
        rw [map_sum]
        exact Finset.single_le_sum (fun j _ => hG0 _ (hDC j (hc j))) (Finset.mem_univ i)
      · rintro ⟨⟨c, hc, rfl⟩, hx⟩
        exact ⟨⟨c, fun i => (hc i (Set.mem_univ i)).1, rfl⟩, hx⟩
    rw [hXt]
    exact ((isCompact_univ_pi fun i => isCompact_slice (hD i) (hDcl i)
      (fun z hz hz0 => hG z (hDC i hz) hz0) t).image
      (continuous_finsetSum _ fun i _ => continuous_apply i)).isClosed.inter
      (isClosed_le hGc continuous_const)
  refine isClosed_of_closure_subset fun x hx => ?_
  have h1 := (isOpen_lt hGc continuous_const).inter_closure
    ⟨show G x < G x + 1 from lt_add_one _, hx⟩
  exact (closure_minimal (t := X ∩ {y | G y ≤ G x + 1})
    (fun y hy => ⟨hy.2, show G y ≤ _ from le_of_lt hy.1⟩) (hXtcl _) h1).1

/-- **KM 3.3 Step 7, "`mD - (K_X + Δ)` is strictly positive on `NE(X) ∖ {0}` for `m ≫ 1`".**
Let `C ⊆ V` be a closed convex cone with `C ∩ (-C) = {0}`, `F ⊆ C` a closed cone, `λ ∈ V^*` with
`λ ≥ 0` on `C` and `{z ∈ C : λ(z) = 0} = F`, and `K ∈ V^*` with `K < 0` on `F ∖ {0}`. Then there
is `m₀` with `mλ - K > 0` on `C ∖ {0}` for every real `m ≥ m₀`. That `F` is a closed cone follows
from its description and is not assumed. -/
@[mmp "lem_km3b_cone_supporting_minus_negative_positive"]
theorem exists_forall_ge_pos_smul_sub {C F : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C)
    (hCcl : IsClosed C) (hCs : C ∩ -C = {0})
    {l K : Module.Dual ℝ V} (hl : ∀ z ∈ C, 0 ≤ l z) (hlF : {z | z ∈ C ∧ l z = 0} = F)
    (hK : ∀ z ∈ F, z ≠ 0 → K z < 0) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ z ∈ C, z ≠ 0 → 0 < m * l z - K z := by
  obtain ⟨G, hG⟩ := exists_dual_pos_of_salient hC hCc hCcl hCs
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hlc : Continuous l := LinearMap.continuous_of_finiteDimensional l
  have hKc : Continuous K := LinearMap.continuous_of_finiteDimensional K
  have hslice := isCompact_slice hC hCcl hG 1
  let A : ℕ → Set V := fun m =>
    {z | z ∈ C ∧ G z ≤ 1} ∩ {z | 1 ≤ G z ∧ (m : ℝ) * l z - K z ≤ 0}
  have hBcl : ∀ m : ℕ, IsClosed {z | 1 ≤ G z ∧ (m : ℝ) * l z - K z ≤ 0} := fun m =>
    (isClosed_le continuous_const hGc).inter
      (isClosed_le ((continuous_const.mul hlc).sub hKc) continuous_const)
  have hA0 : IsCompact (A 0) := hslice.inter_right (hBcl 0)
  have hAcl : ∀ m, IsClosed (A m) := fun m => hslice.isClosed.inter (hBcl m)
  have hAmono : ∀ m, A (m + 1) ⊆ A m := by
    rintro m z ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have := hl z h1.1
    push_cast at h3
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, A N = ∅ := by
    by_contra hne
    push Not at hne
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hAmono
      hne hA0 hAcl
    rw [Set.mem_iInter] at hz
    have hzC := (hz 0).1.1
    have hG1 : G z = 1 := le_antisymm (hz 0).1.2 (hz 0).2.1
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hG1
    have hlz : l z = 0 := by
      by_contra hne'
      have hpos : 0 < l z := lt_of_le_of_ne (hl z hzC) (Ne.symm hne')
      obtain ⟨m, hm⟩ := exists_nat_gt (K z / l z)
      have := (hz m).2.2
      rw [div_lt_iff₀ hpos] at hm
      linarith
    have hzF : z ∈ F := by
      rw [← hlF]
      exact ⟨hzC, hlz⟩
    have h0 := (hz 0).2.2
    simp only [Nat.cast_zero, zero_mul, zero_sub] at h0
    linarith [hK z hzF hz0]
  refine ⟨N, fun m hm z hz hz0 => ?_⟩
  have hGz := hG z hz hz0
  have hsC : (G z)⁻¹ • z ∈ C := smul_mem_of_isCone hC hz (inv_nonneg.2 hGz.le)
  have hGs : G ((G z)⁻¹ • z) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGz.ne']
  have hsN : (G z)⁻¹ • z ∉ A N := hN ▸ Set.notMem_empty _
  have hpos : 0 < (N : ℝ) * l ((G z)⁻¹ • z) - K ((G z)⁻¹ • z) := by
    by_contra h
    push Not at h
    exact hsN ⟨⟨hsC, hGs.le⟩, hGs.ge, h⟩
  have hls := hl _ hsC
  have hpos' : 0 < m * l ((G z)⁻¹ • z) - K ((G z)⁻¹ • z) := by nlinarith
  have heq : m * l z - K z = G z * (m * l ((G z)⁻¹ • z) - K ((G z)⁻¹ • z)) := by
    simp only [map_smul, smul_eq_mul]
    field_simp
  rw [heq]
  exact mul_pos hGz hpos'

end MMP.Positivity
