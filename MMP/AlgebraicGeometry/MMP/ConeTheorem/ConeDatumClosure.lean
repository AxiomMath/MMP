module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AbstractConeTheorem

/-!
# The cone as the closure of its `K`-nonnegative part and its negative rational rays

For a cone datum `(N_ℤ, NE̅, K, a)`, `NE̅` is the closure of `NE̅_{K≥0} + ∑_{R ∈ 𝓡(NE̅, K)} R`
(finite sums of elements of the rays).

## Main results

* `MMP.Positivity.ConeDatum.cone_eq_closure_nonneg_add_sum_rays`
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

namespace ConeDatum

variable {N : Type u} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- A ray `R ∈ 𝓡(NE̅, K)` contains `0`, is closed under addition and nonnegative scaling, and
lies in `NE̅`. -/
theorem zero_mem_add_mem_smul_mem_subset_of_mem_negativeRationalRays (D : ConeDatum N)
    {R : Set (ℝ ⊗[ℤ] N)} (hR : R ∈ D.negativeRationalRays) :
    (0 : ℝ ⊗[ℤ] N) ∈ R ∧ (∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) ∧
      (∀ a ∈ R, ∀ t : ℝ, 0 ≤ t → t • a ∈ R) ∧ R ⊆ D.cone := by
  obtain ⟨ξ, -, -, L, -, rfl⟩ := hR
  refine ⟨⟨D.cone.zero_mem, map_zero _⟩, fun a ha b hb => ⟨D.cone.add_mem ha.1 hb.1, ?_⟩,
    fun a ha t ht => ⟨D.cone.smul_mem ht ha.1, ?_⟩, fun z hz => hz.1⟩
  · rw [map_add, ha.2, hb.2, add_zero]
  · rw [map_smul, ha.2, smul_zero]

/-- The convex cone `NE̅_{K≥0} + ∑_{R ∈ 𝓡} R` of finite sums `c + ∑ r_R` with `c ∈ NE̅`,
`K(c) ≥ 0` and `r_R ∈ R` for finitely many rays `R ∈ 𝓡(NE̅, K)`. -/
def nonnegAddSumRays (D : ConeDatum N) : PointedCone ℝ (ℝ ⊗[ℤ] N) where
  carrier := {x | ∃ c ∈ D.cone, 0 ≤ realOfRatForm N D.form c ∧
    ∃ (S : Finset (Set (ℝ ⊗[ℤ] N))) (r : Set (ℝ ⊗[ℤ] N) → ℝ ⊗[ℤ] N),
      (∀ R ∈ S, R ∈ D.negativeRationalRays ∧ r R ∈ R) ∧ x = c + ∑ R ∈ S, r R}
  zero_mem' := ⟨0, D.cone.zero_mem, by simp, ∅, fun _ => 0, by simp, by simp⟩
  add_mem' := by
    classical
    rintro _ _ ⟨c, hc, hKc, S, r, hr, rfl⟩ ⟨c', hc', hKc', S', r', hr', rfl⟩
    refine ⟨c + c', D.cone.add_mem hc hc', by rw [map_add]; positivity, S ∪ S',
      fun R => (if R ∈ S then r R else 0) + (if R ∈ S' then r' R else 0), fun R hR => ?_, ?_⟩
    · have hRr : R ∈ D.negativeRationalRays :=
        (Finset.mem_union.1 hR).elim (fun h => (hr R h).1) fun h => (hr' R h).1
      have hRP := zero_mem_add_mem_smul_mem_subset_of_mem_negativeRationalRays D hRr
      refine ⟨hRr, hRP.2.1 _ ?_ _ ?_⟩ <;> split_ifs with h
      exacts [(hr R h).2, hRP.1, (hr' R h).2, hRP.1]
    · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
      abel
  smul_mem' := by
    rintro ⟨t, ht⟩ _ ⟨c, hc, hKc, S, r, hr, rfl⟩
    refine ⟨t • c, D.cone.smul_mem ht hc, by rw [map_smul, smul_eq_mul]; positivity, S,
      fun R => t • r R, fun R hR => ⟨(hr R hR).1,
        (zero_mem_add_mem_smul_mem_subset_of_mem_negativeRationalRays D (hr R hR).1).2.2.1 _
          (hr R hR).2 t ht⟩, ?_⟩
    change t • (c + _) = _
    rw [smul_add, Finset.smul_sum]

theorem mem_nonnegAddSumRays_iff (D : ConeDatum N) {x : ℝ ⊗[ℤ] N} :
    x ∈ nonnegAddSumRays D ↔ ∃ c ∈ D.cone, 0 ≤ realOfRatForm N D.form c ∧
      ∃ (S : Finset (Set (ℝ ⊗[ℤ] N))) (r : Set (ℝ ⊗[ℤ] N) → ℝ ⊗[ℤ] N),
        (∀ R ∈ S, R ∈ D.negativeRationalRays ∧ r R ∈ R) ∧ x = c + ∑ R ∈ S, r R :=
  Iff.rfl

/-- The cone `NE̅_{K≥0} + ∑_{R ∈ 𝓡} R` lies in `NE̅`. -/
theorem nonnegAddSumRays_le (D : ConeDatum N) : nonnegAddSumRays D ≤ D.cone := by
  rintro _ ⟨c, hc, -, S, r, hr, rfl⟩
  exact D.cone.add_mem hc (D.cone.sum_mem fun R hR =>
    (zero_mem_add_mem_smul_mem_subset_of_mem_negativeRationalRays D (hr R hR).1).2.2.2
      (hr R hR).2)

/-- **KM 3.3 Step 3.** Let `(N_ℤ, NE̅, K, a)` be a cone datum. Then `NE̅` is the closure (for the
canonical topology of `N_ℝ`) of `NE̅_{K≥0} + ∑_{R ∈ 𝓡(NE̅, K)} R`, the set of finite sums
`c + r₁ + ⋯ + r_s` with `c ∈ NE̅`, `K(c) ≥ 0` and `rᵢ ∈ Rᵢ ∈ 𝓡(NE̅, K)`. -/
@[mmp "lem_km3b_cone_closure"]
theorem cone_eq_closure_nonneg_add_sum_rays (D : ConeDatum N) :
    (D.cone : Set (ℝ ⊗[ℤ] N)) =
      @closure _ (moduleTopology ℝ (ℝ ⊗[ℤ] N))
        {x | ∃ c ∈ D.cone, 0 ≤ realOfRatForm N D.form c ∧
          ∃ (S : Finset (Set (ℝ ⊗[ℤ] N))) (r : Set (ℝ ⊗[ℤ] N) → ℝ ⊗[ℤ] N),
            (∀ R ∈ S, R ∈ D.negativeRationalRays ∧ r R ∈ R) ∧ x = c + ∑ R ∈ S, r R} := by
  classical
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set K := realOfRatForm N D.form
  let T := nonnegAddSumRays D
  have hTC : (T : Set (ℝ ⊗[ℤ] N)) ⊆ C := nonnegAddSumRays_le D
  have hWcone : IsCone ℝ (closure (T : Set (ℝ ⊗[ℤ] N))) :=
    ⟨subset_closure T.zero_mem, fun v hv t ht =>
      map_mem_closure (continuous_const_smul t) hv fun y hy => T.smul_mem ht.le hy⟩
  refine Set.Subset.antisymm (fun x hx => ?_) (closure_minimal hTC D.isClosed_cone)
  change x ∈ closure (T : Set (ℝ ⊗[ℤ] N))
  by_contra hxW
  obtain ⟨ℓ₀, hℓ₀W, hℓ₀x⟩ :=
    exists_dual_nonneg_neg_of_notMem hWcone T.convex.closure isClosed_closure hxW
  have hℓ₀T : ∀ w ∈ (T : Set (ℝ ⊗[ℤ] N)), 0 ≤ ℓ₀ w := fun w hw => hℓ₀W w (subset_closure hw)
  obtain ⟨H₀, hH₀, -⟩ := exists_intForm_pos_and_add_coord_pos D (Module.Free.chooseBasis ℤ N)
  set G := realOfIntForm N H₀
  have hG0 : ∀ z ∈ C, 0 ≤ G z := fun z hz => by
    rcases eq_or_ne z 0 with rfl | h0
    · simp
    · exact (hH₀ z hz h0).le
  have hKc : Continuous K := LinearMap.continuous_of_finiteDimensional K
  have hℓc : Continuous ℓ₀ := LinearMap.continuous_of_finiteDimensional ℓ₀
  set Q : Set (ℝ ⊗[ℤ] N) := {z | z ∈ C ∧ G z ≤ G x} ∩ {z | ℓ₀ z ≤ ℓ₀ x}
  have hQc : IsCompact Q :=
    (isCompact_slice (isCone_coe D.cone) D.isClosed_cone hH₀ (G x)).inter_right
      (isClosed_le hℓc continuous_const)
  obtain ⟨c₀, hc₀Q, hc₀⟩ :=
    hQc.exists_isMaxOn ⟨x, ⟨hx, le_rfl⟩, (le_rfl : ℓ₀ x ≤ ℓ₀ x)⟩ hKc.continuousOn
  rcases le_or_gt 0 (K c₀) with hK0 | hK0
  · have := hℓ₀T c₀ ⟨c₀, hc₀Q.1.1, hK0, ∅, fun _ => 0, by simp, by simp⟩
    linarith [show ℓ₀ c₀ ≤ ℓ₀ x from hc₀Q.2]
  have hGx := hG0 x hx
  set ε := -K c₀ / (2 * (G x + 1)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨S, hS, hCeq⟩ := cone_eq_nonneg_add_sum_rays D hH₀ hε0
  have hx' : x ∈ C := hx
  rw [hCdef, hCeq] at hx'
  obtain ⟨c, hc, hKc', r, hr, hxeq⟩ := hx'
  have hSr : ∀ R ∈ S, R ∈ D.negativeRationalRays := fun R hR => by
    have : R ∈ (↑S : Set (Set (ℝ ⊗[ℤ] N))) := hR
    rw [hS] at this
    exact this.1
  have hsumT : ∑ R ∈ S, r R ∈ (T : Set (ℝ ⊗[ℤ] N)) :=
    ⟨0, D.cone.zero_mem, by simp, S, r, fun R hR => ⟨hSr R hR, hr R hR⟩, by simp⟩
  have hℓs := hℓ₀T _ hsumT
  have hGs := hG0 _ (hTC hsumT)
  have hcQ : c ∈ Q := by
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · rw [hxeq, map_add]
      linarith
    · change ℓ₀ c ≤ ℓ₀ x
      rw [hxeq, map_add]
      linarith
  have hKle : K c ≤ K c₀ := hc₀ hcQ
  have hGc : G c ≤ G x := hcQ.1.2
  have h1 : ε * G c ≤ ε * G x := mul_le_mul_of_nonneg_left hGc hε0.le
  have h2 : ε * G x < -K c₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

end ConeDatum

end MMP.Positivity
