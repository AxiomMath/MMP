module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ConeDatumBasis

/-!
# Faces of nef classes in a cone datum (KM 3.3 Steps 1, 2)

Let `(N_ℤ, NE̅, K, a)` be a cone datum and `L ∈ N_ℚ^*` with `L ≥ 0` on `NE̅` and
`F_L ⊄ NE̅_{K≥0}`.

* (Step 1) For `H ∈ N_ℚ^*` positive on `NE̅ ∖ {0}` there are `n₀ > 0` and `t ∈ ℚ_{≥0}` such that
  for every `n ≥ n₀` the form `nL + H + tK` is `≥ 0` on `NE̅`, its face is
  `F_L ∩ (H + tK)^⊥ ≠ {0}`, and `K < 0` on it away from `0`; for integral `L, H`, `at ∈ ℤ`.
* (Step 2) There is `L' ∈ N_ℚ^*` with `L' ≥ 0` on `NE̅`, `F_{L'} ⊆ F_L` and
  `F_{L'} ∈ 𝓡(NE̅, K)`.

## Main results

* `MMP.Positivity.ConeDatum.exists_faceOfNefForm_subface_negative`
* `MMP.Positivity.ConeDatum.exists_faceOfNefForm_mem_negativeRationalRays`
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

section Forms

variable {N : Type*} [AddCommGroup N]

/-- The real extension of a rational form is additive in the form. -/
theorem realOfRatForm_add_apply (L L' : N →ₗ[ℤ] ℚ) (z : ℝ ⊗[ℤ] N) :
    realOfRatForm N (L + L') z = realOfRatForm N L z + realOfRatForm N L' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfRatForm_tmul, LinearMap.add_apply]
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- The real extension of `q • L` is `q` times the real extension of `L`. -/
theorem realOfRatForm_smul_apply (q : ℚ) (L : N →ₗ[ℤ] ℚ) (z : ℝ ⊗[ℤ] N) :
    realOfRatForm N (q • L) z = q * realOfRatForm N L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfRatForm_tmul, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- The real extension of `k • L`, for `k ∈ ℤ`, is `k` times the real extension of `L`. -/
theorem realOfRatForm_zsmul_apply (k : ℤ) (L : N →ₗ[ℤ] ℚ) (z : ℝ ⊗[ℤ] N) :
    realOfRatForm N (k • L) z = k * realOfRatForm N L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfRatForm_tmul, LinearMap.smul_apply, zsmul_eq_mul]
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- A rational form agreeing with an integral form on `N` has the same real extension. -/
theorem realOfRatForm_eq_realOfIntForm {L : N →ₗ[ℤ] ℚ} {H : Module.Dual ℤ N}
    (h : ∀ x, L x = H x) (z : ℝ ⊗[ℤ] N) : realOfRatForm N L z = realOfIntForm N H z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    rw [realOfRatForm_tmul, realOfIntForm_tmul, h n]
    push_cast
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A rational form with integral values is an integral form. -/
theorem exists_intForm_eq_of_forall_intCast {L : N →ₗ[ℤ] ℚ} (hL : ∀ x, ∃ m : ℤ, L x = m) :
    ∃ H : Module.Dual ℤ N, ∀ x, L x = H x := by
  choose f hf using hL
  refine ⟨{ toFun := f, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, hf⟩
  · apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, ← hf, ← hf, ← hf, map_add]
  · apply Int.cast_injective (α := ℚ)
    simp only [RingHom.id_apply, smul_eq_mul, Int.cast_mul, ← hf, map_zsmul, zsmul_eq_mul]

/-- Two rational forms on a finite free `ℤ`-module have integral multiples by a common positive
integer `d`, and `d = 1` can be taken when both are integral. -/
theorem exists_intForm_pair_eq_mul [Module.Free ℤ N] [Module.Finite ℤ N] (L H : N →ₗ[ℤ] ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ L₀ H₀ : Module.Dual ℤ N,
      (∀ z, realOfIntForm N L₀ z = d * realOfRatForm N L z) ∧
      (∀ z, realOfIntForm N H₀ z = d * realOfRatForm N H z) ∧
      ((∀ x, ∃ m : ℤ, L x = m) → (∀ x, ∃ m : ℤ, H x = m) → d = 1) := by
  by_cases hint : (∀ x, ∃ m : ℤ, L x = m) ∧ (∀ x, ∃ m : ℤ, H x = m)
  · obtain ⟨L₀, hL₀⟩ := exists_intForm_eq_of_forall_intCast hint.1
    obtain ⟨H₀, hH₀⟩ := exists_intForm_eq_of_forall_intCast hint.2
    refine ⟨1, one_pos, L₀, H₀, fun z => ?_, fun z => ?_, fun _ _ => rfl⟩
    · rw [realOfRatForm_eq_realOfIntForm hL₀]
      simp
    · rw [realOfRatForm_eq_realOfIntForm hH₀]
      simp
  · obtain ⟨d₁, hd₁, L₀, hL₀⟩ := exists_intForm_eq_mul_ratForm L
    obtain ⟨d₂, hd₂, H₀, hH₀⟩ := exists_intForm_eq_mul_ratForm H
    refine ⟨d₁ * d₂, mul_pos hd₁ hd₂, d₂ • L₀, d₁ • H₀, fun z => ?_, fun z => ?_,
      fun h₁ h₂ => absurd ⟨h₁, h₂⟩ hint⟩
    · rw [realOfIntForm_zsmul_apply, hL₀]
      push_cast
      ring
    · rw [realOfIntForm_zsmul_apply, hH₀]
      push_cast
      ring

end Forms

/-- If `t` is the `K`-threshold of `G` on `C` and `G' = cG` with `c > 0`, then `ct` is the
`K`-threshold of `G'` on `C`. -/
theorem isConeThreshold_of_eq_mul {V : Type*} [AddCommGroup V] [Module ℝ V] {C : Set V}
    {G G' K : Module.Dual ℝ V} {t c : ℝ} (hc : 0 < c) (hG : ∀ z, G' z = c * G z)
    (h : IsConeThreshold C G K t) : IsConeThreshold C G' K (c * t) := by
  refine ⟨fun z hz => ?_, fun t' ht' hall => h.2 (t' / c) ?_ fun z hz => ?_⟩
  · rw [hG, show c * G z + c * t * K z = c * (G z + t * K z) by ring]
    exact mul_nonneg hc.le (h.1 z hz)
  · rwa [lt_div_iff₀ hc, mul_comm]
  · have := hall z hz
    rw [hG] at this
    rw [show G z + t' / c * K z = (c * G z + t' * K z) / c by field_simp]
    exact div_nonneg this hc.le

/-- **KM 3.3 Step 1, "`0 ≠ F_{D(nL,H)}`".** If `t` is the `K`-threshold of `G` on a closed
convex cone `C` with `C ∩ (-C) = {0}`, then `G + tK` vanishes at a nonzero point of `C`. -/
theorem exists_ne_zero_add_mul_eq_zero_of_isConeThreshold {V : Type*} [AddCommGroup V]
    [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    (hCs : C ∩ -C = {0}) {G K : Module.Dual ℝ V} {t : ℝ} (ht : IsConeThreshold C G K t) :
    ∃ z ∈ C, z ≠ 0 ∧ G z + t * K z = 0 := by
  by_contra hcon
  push Not at hcon
  set l : Module.Dual ℝ V := G + t • K with hldef
  have hlapp : ∀ z, l z = G z + t * K z := fun z => by simp [hldef]
  have hl : ∀ z ∈ C, 0 ≤ l z := fun z hz => by simpa only [hlapp] using ht.1 z hz
  obtain ⟨m₀, hm₀⟩ := exists_forall_ge_pos_smul_sub hC hCc hCcl hCs (l := l) (K := -K) hl
    (F := {0}) (by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      refine ⟨fun ⟨hz, hz0⟩ => by_contra fun hne => hcon z hz hne (by rwa [← hlapp]), ?_⟩
      rintro rfl
      exact ⟨hC.1, map_zero l⟩) (fun z hz hz0 => absurd hz hz0)
  set m := max m₀ 1 with hm
  have hm1 : 0 < m := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hm1' : 0 < 1 / m := by positivity
  refine ht.2 (t + 1 / m) (by linarith) fun z hz => ?_
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have := hm₀ m (le_max_left _ _) z hz hz0
    rw [hlapp, LinearMap.neg_apply] at this
    have e : G z + (t + 1 / m) * K z = (m * (G z + t * K z) - -K z) / m := by
      field_simp
      ring
    rw [e]
    exact div_nonneg this.le hm1.le

/-- A nondecreasing sequence of integers which is bounded above is eventually constant. -/
theorem exists_forall_ge_eq_of_monotone_of_bddAbove {s : ℕ → ℤ} (hs : Monotone s)
    (hb : BddAbove (Set.range s)) : ∃ n₁, ∀ n, n₁ ≤ n → s n = s n₁ := by
  obtain ⟨n₁, hn₁⟩ := Int.csSup_mem (Set.range_nonempty s) hb
  exact ⟨n₁, fun n hn => le_antisymm (hn₁ ▸ le_csSup hb ⟨n, rfl⟩) (hs hn)⟩

/-- **KM 3.3 Step 1, "non-ample nef divisors … `0 ≠ F_{D(nL,H)}`".** Let `C ⊆ V` be a closed
convex cone, `G ∈ V^*` positive on `C ∖ {0}`, `K ∈ V^*` with `K(z₀) < 0` for some `z₀ ∈ C`, and
`t` the `K`-threshold of `G` on `C`. Then the face `F_{G+tK}` of `C` is not `{0}`. The hypothesis
on `K` only ensures the threshold exists, and is not needed once `t` is given. -/
@[mmp "lem_km3b_cone_threshold_face_nonzero"]
theorem faceOfNefForm_add_smul_ne_bot {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    {G K : Module.Dual ℝ V} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) {t : ℝ}
    (ht : IsConeThreshold C G K t) :
    faceOfNefForm C (G + t • K) ≠ {0} := by
  have hCs : C ∩ -C = {0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_neg, Set.mem_singleton_iff]
    refine ⟨fun ⟨hz, hnz⟩ => by_contra fun h0 => ?_, fun h => h ▸ ⟨hC.1, by simpa using hC.1⟩⟩
    have h1 := hG z hz h0
    have h2 := hG (-z) hnz (neg_ne_zero.mpr h0)
    rw [map_neg] at h2
    linarith
  obtain ⟨z, hz, hz0, hzG⟩ := exists_ne_zero_add_mul_eq_zero_of_isConeThreshold hC hCc hCcl hCs ht
  intro h
  have : z ∈ faceOfNefForm C (G + t • K) := ⟨hz, by simpa [smul_eq_mul] using hzG⟩
  rw [h] at this
  exact hz0 this

/-- The `K`-threshold of `G` on `C` is at most `G(ξ) / -K(ξ)` for any `ξ ∈ C` with `K(ξ) < 0`. -/
theorem le_div_neg_of_isConeThreshold {V : Type*} [AddCommGroup V] [Module ℝ V] {C : Set V}
    {G K : Module.Dual ℝ V} {t : ℝ} (ht : IsConeThreshold C G K t) {ξ : V} (hξ : ξ ∈ C)
    (hKξ : K ξ < 0) : t ≤ G ξ / -K ξ := by
  have := ht.1 ξ hξ
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- If `l ≥ 0` on `C`, the `K`-thresholds of the forms `n • l + h` are monotone in `n`. -/
theorem monotone_of_isConeThreshold_smul_add {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} {l h k : Module.Dual ℝ V} (hl : ∀ z ∈ C, 0 ≤ l z) {τ : ℕ → ℝ}
    (hτ : ∀ n : ℕ, IsConeThreshold C ((n : ℝ) • l + h) k (τ n)) : Monotone τ := by
  intro n n' hnn'
  refine ((isConeThreshold_iff_isGreatest _ _ _ _).mp (hτ n')).2 fun z hz => ?_
  have h1 := (hτ n).1 z hz
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1 ⊢
  have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
  have := hl z hz
  nlinarith

/-- If `f = n l + g` with `l ≥ 0` and `(n - 1) l + g ≥ 0` on `C`, then `F_f = F_l ∩ g^⊥`. -/
theorem faceOfNefForm_eq_inter_of_eq_mul_add {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} {f l g : Module.Dual ℝ V} {n : ℝ} (hf : ∀ z, f z = n * l z + g z)
    (hl : ∀ z ∈ C, 0 ≤ l z) (hg : ∀ z ∈ C, 0 ≤ (n - 1) * l z + g z) :
    faceOfNefForm C f = faceOfNefForm C l ∩ {z | g z = 0} := by
  ext z
  simp only [faceOfNefForm, Set.mem_inter_iff, Set.mem_ofPred_eq, hf]
  constructor
  · rintro ⟨hz, hz0⟩
    have := hg z hz
    have := hl z hz
    have hl0 : l z = 0 := by nlinarith
    refine ⟨⟨hz, hl0⟩, ?_⟩
    rw [hl0] at hz0
    linarith
  · rintro ⟨⟨hz, hl0⟩, hg0⟩
    exact ⟨hz, by rw [hl0, hg0, mul_zero, add_zero]⟩

/-- If every point `z` of the face `F_l` of a cone `C` with `C ∩ (-C) = {0}` equals `k(z) • w`
for a fixed `w`, and `ξ ∈ F_l` has `k(ξ) < 0`, then `F_l` is the ray `ℝ_{≥0} ξ`. -/
theorem faceOfNefForm_eq_ray_of_forall_eq_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} (hC : IsCone ℝ C) (hCs : C ∩ -C = {0}) {l k : Module.Dual ℝ V} {w ξ : V}
    (hzw : ∀ z ∈ faceOfNefForm C l, z = k z • w) (hξF : ξ ∈ faceOfNefForm C l)
    (hξk : k ξ < 0) : faceOfNefForm C l = {z | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = z} := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    simp at hξk
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hz
    refine ⟨k z / k ξ, ?_, ?_⟩
    · rw [div_nonneg_iff]
      right
      refine ⟨not_lt.mp fun hkz => hξ0 ?_, hξk.le⟩
      have hu : k z • ξ ∈ C := smul_mem_of_isCone hC hξF.1 hkz.le
      have hv : (-k ξ) • z ∈ C := smul_mem_of_isCone hC hz.1 (by linarith)
      have hsum : k z • ξ = -((-k ξ) • z) := by
        rw [(congrArg (k z • ·) (hzw ξ hξF)).trans (smul_smul _ _ _),
          (congrArg ((-k ξ) • ·) (hzw z hz)).trans (smul_smul _ _ _), ← neg_smul]
        congr 1
        ring
      have h0 : k z • ξ ∈ C ∩ -C := ⟨hu, by rwa [hsum, Set.neg_mem_neg]⟩
      rw [hCs, Set.mem_singleton_iff, smul_eq_zero] at h0
      exact h0.resolve_left hkz.ne'
    · calc (k z / k ξ) • ξ = (k z / k ξ * k ξ) • w :=
            (congrArg ((k z / k ξ) • ·) (hzw ξ hξF)).trans (smul_smul _ _ _)
        _ = z := by rw [div_mul_cancel₀ _ hξk.ne, ← hzw z hz]
  · rintro ⟨c, hc, rfl⟩
    exact ⟨smul_mem_of_isCone hC hξF.1 hc, by rw [map_smul, hξF.2, smul_zero]⟩

/-- Cutting a face `F_l` by the kernel of a form `g` which does not vanish on it lowers the
dimension of its span. -/
theorem finrank_span_faceOfNefForm_lt {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {C : Set V} {l l₁ g : Module.Dual ℝ V}
    (hfeq : faceOfNefForm C l₁ = faceOfNefForm C l ∩ {z | g z = 0}) {z : V}
    (hz : z ∈ faceOfNefForm C l) (hgz : g z ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (faceOfNefForm C l₁)) <
      Module.finrank ℝ (Submodule.span ℝ (faceOfNefForm C l)) := by
  have hsub : faceOfNefForm C l₁ ⊆ faceOfNefForm C l := by
    rw [hfeq]
    exact Set.inter_subset_left
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (Submodule.span_mono hsub) fun heq => hgz ?_
  have hker : Submodule.span ℝ (faceOfNefForm C l₁) ≤ LinearMap.ker g := by
    refine Submodule.span_le.mpr fun y hy => ?_
    rw [hfeq] at hy
    exact LinearMap.mem_ker.mpr hy.2
  exact LinearMap.mem_ker.mp (hker (heq ▸ Submodule.subset_span hz))

namespace ConeDatum

variable {N : Type u} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- If `G₀ = d G` is integral for an integer `d > 0` and `G > 0` on `NE̅ ∖ {0}`, then the
`K`-threshold of `G` lies in `(ad)⁻¹ ℤ`. -/
theorem exists_eq_intCast_div_of_isConeThreshold (D : ConeDatum N)
    {G : Module.Dual ℝ (ℝ ⊗[ℤ] N)} (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < G z) {d : ℤ} (hd : 0 < d)
    {G₀ : Module.Dual ℤ N} (hG₀ : ∀ z, realOfIntForm N G₀ z = d * G z) {τ : ℝ}
    (hτ : IsConeThreshold (D.cone : Set (ℝ ⊗[ℤ] N)) G (realOfRatForm N D.form) τ) :
    ∃ s : ℤ, τ = s / ((D.index : ℝ) * d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : (0 : ℝ) < D.index := by exact_mod_cast D.index_pos
  obtain ⟨m, hm⟩ := D.threshold_mem G₀
    (fun z hz hz0 => by simpa only [hG₀] using mul_pos hdR (hG z hz hz0)) _
    (isConeThreshold_of_eq_mul hdR hG₀ hτ)
  refine ⟨m, ?_⟩
  rw [eq_div_iff (by positivity)]
  rw [eq_div_iff ha.ne'] at hm
  linarith

/-- **KM 3.3 Step 1, stabilisation.** Let `L ∈ N_ℚ^*` with `L ≥ 0` on `NE̅` and
`F_L ⊄ NE̅_{K≥0}`, and `H ∈ N_ℚ^*` positive on `NE̅ ∖ {0}`. Then the `K`-threshold of `nL + H` is
a constant `t ∈ ℚ_{≥0}` for all large `n`; if moreover `L, H ∈ N_ℤ^*`, then `at ∈ ℤ`. -/
theorem exists_forall_ge_isConeThreshold (D : ConeDatum N) {L H : N →ₗ[ℤ] ℚ}
    (hL : ∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z)
    (hLK : ¬ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ⊆
      {z | 0 ≤ realOfRatForm N D.form z})
    (hH : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfRatForm N H z) :
    ∃ n₁ : ℕ, ∃ t : ℚ, 0 ≤ t ∧
      (∀ n : ℕ, n₁ ≤ n → IsConeThreshold (D.cone : Set (ℝ ⊗[ℤ] N))
        ((n : ℝ) • realOfRatForm N L + realOfRatForm N H) (realOfRatForm N D.form) t) ∧
      ((∀ x, ∃ m : ℤ, L x = m) → (∀ x, ∃ m : ℤ, H x = m) → ∃ m : ℤ, (D.index : ℚ) * t = m) := by
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set l := realOfRatForm N L with hldef
  set h := realOfRatForm N H with hhdef
  set k := realOfRatForm N D.form with hkdef
  obtain ⟨ξ, hξF, hξk⟩ := Set.not_subset.mp hLK
  replace hξk : k ξ < 0 := not_le.mp hξk
  obtain ⟨d, hd, L₀, H₀, hL₀, hH₀, hd1⟩ := exists_intForm_pair_eq_mul L H
  have hpos : (0 : ℝ) < D.index * d :=
    mul_pos (by exact_mod_cast D.index_pos) (by exact_mod_cast hd)
  let G : ℕ → Module.Dual ℝ (ℝ ⊗[ℤ] N) := fun n => (n : ℝ) • l + h
  have hGapp : ∀ (n : ℕ) z, G n z = n * l z + h z := fun n z => by simp [G]
  have hGpos : ∀ n, ∀ z ∈ C, z ≠ 0 → 0 < G n z := fun n z hz hz0 => by
    simpa only [hGapp] using
      add_pos_of_nonneg_of_pos (mul_nonneg n.cast_nonneg (hL z hz)) (hH z hz hz0)
  choose τ hτ using fun n => (existsUnique_isConeThreshold (hGpos n) D.exists_form_neg).1.exists
  have hint : ∀ n, ∃ s : ℤ, τ n = s / ((D.index : ℝ) * d) := fun n =>
    exists_eq_intCast_div_of_isConeThreshold D (hGpos n) hd (G₀ := (n : ℤ) • L₀ + H₀)
      (fun z => by
        rw [realOfIntForm_add_apply, realOfIntForm_zsmul_apply, hL₀, hH₀, hGapp]
        push_cast
        ring) (hτ n)
  choose s hs using hint
  have hsmono : Monotone s := by
    intro n n' hnn'
    have := monotone_of_isConeThreshold_smul_add hL hτ hnn'
    rw [hs, hs, div_le_div_iff_of_pos_right hpos] at this
    exact_mod_cast this
  have hsbd : BddAbove (Set.range s) := by
    refine ⟨⌈h ξ / -k ξ * ((D.index : ℝ) * d)⌉, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := le_div_neg_of_isConeThreshold (hτ n) hξF.1 hξk
    rw [hGapp, hξF.2, mul_zero, zero_add, hs, div_le_iff₀ hpos] at this
    exact_mod_cast this.trans (Int.le_ceil _)
  obtain ⟨n₁, hn₁⟩ := exists_forall_ge_eq_of_monotone_of_bddAbove hsmono hsbd
  set tq : ℚ := (s n₁ : ℚ) / ((D.index : ℚ) * d) with htq
  have htq' : (tq : ℝ) = τ n₁ := by
    rw [hs, htq]
    push_cast
    rfl
  have ht0 : (0 : ℝ) ≤ tq :=
    htq' ▸ (existsUnique_isConeThreshold (hGpos n₁) D.exists_form_neg).2 _ (hτ n₁)
  refine ⟨n₁, tq, by exact_mod_cast ht0, fun n hn => ?_, fun hLi hHi => ?_⟩
  · rw [show (tq : ℝ) = τ n by rw [htq', hs, hs, hn₁ n hn]]
    exact hτ n
  · obtain rfl := hd1 hLi hHi
    have ha' : (D.index : ℚ) ≠ 0 := by exact_mod_cast D.index_pos.ne'
    refine ⟨s n₁, ?_⟩
    rw [htq, Int.cast_one, mul_one, mul_div_cancel₀ _ ha']

/-- **KM 3.3 Step 1.** Let `(N_ℤ, NE̅, K, a)` be a cone datum, `L ∈ N_ℚ^*` with `L ≥ 0` on `NE̅`
and `F_L ⊄ NE̅_{K≥0}`, and `H ∈ N_ℚ^*` positive on `NE̅ ∖ {0}`. Then there are `n₀ ∈ ℤ_{>0}` and
`t ∈ ℚ_{≥0}` such that for every integer `n ≥ n₀` the form `nL + H + tK` is `≥ 0` on `NE̅`, its
face satisfies `F_{nL+H+tK} ≠ {0}` and `F_{nL+H+tK} = F_L ∩ (H + tK)^⊥`, and `K < 0` on
`F_{nL+H+tK} ∖ {0}`; if moreover `L, H ∈ N_ℤ^*`, then `at ∈ ℤ`. -/
@[mmp "lem_km3b_cone_subface_negative"]
theorem exists_faceOfNefForm_subface_negative (D : ConeDatum N) {L H : N →ₗ[ℤ] ℚ}
    (hL : ∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z)
    (hLK : ¬ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ⊆
      {z | 0 ≤ realOfRatForm N D.form z})
    (hH : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfRatForm N H z) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ t : ℚ, 0 ≤ t ∧
      (∀ n : ℕ, n₀ ≤ n →
        (∀ z ∈ D.cone, 0 ≤ realOfRatForm N ((n : ℤ) • L + H + t • D.form) z) ∧
        faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N ((n : ℤ) • L + H + t • D.form))
          ≠ {0} ∧
        faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N ((n : ℤ) • L + H + t • D.form)) =
          faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ∩
            {z | realOfRatForm N (H + t • D.form) z = 0} ∧
        ∀ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N))
            (realOfRatForm N ((n : ℤ) • L + H + t • D.form)),
          z ≠ 0 → realOfRatForm N D.form z < 0) ∧
      ((∀ x, ∃ m : ℤ, L x = m) → (∀ x, ∃ m : ℤ, H x = m) → ∃ m : ℤ, (D.index : ℚ) * t = m) := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set l := realOfRatForm N L with hldef
  set h := realOfRatForm N H with hhdef
  set k := realOfRatForm N D.form with hkdef
  obtain ⟨n₁, tq, ht0, hthr, hint⟩ := exists_forall_ge_isConeThreshold D hL hLK hH
  have ht0' : (0 : ℝ) ≤ tq := by exact_mod_cast ht0
  have happ : ∀ (n : ℕ) z,
      realOfRatForm N ((n : ℤ) • L + H + tq • D.form) z = ((n : ℝ) • l + h) z + tq * k z := by
    intro n z
    rw [realOfRatForm_add_apply, realOfRatForm_add_apply, realOfRatForm_zsmul_apply,
      realOfRatForm_smul_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  have happ' : ∀ z, realOfRatForm N (H + tq • D.form) z = h z + tq * k z := by
    intro z
    rw [realOfRatForm_add_apply, realOfRatForm_smul_apply]
  refine ⟨n₁ + 1, Nat.succ_pos _, tq, ht0, fun n hn => ?_, hint⟩
  have hthr' := hthr n (by omega)
  have hface : faceOfNefForm C (realOfRatForm N ((n : ℤ) • L + H + tq • D.form)) =
      faceOfNefForm C l ∩ {z | realOfRatForm N (H + tq • D.form) z = 0} := by
    refine faceOfNefForm_eq_inter_of_eq_mul_add (n := n) (fun z => ?_) hL fun z hz => ?_
    · rw [happ, happ', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · have h1 := (hthr (n - 1) (by omega)).1 z hz
      rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Nat.cast_sub (by omega),
        Nat.cast_one] at h1
      rw [happ']
      linarith
  refine ⟨fun z hz => ?_, ?_, hface, fun z hz hz0 => ?_⟩
  · rw [happ]
    exact hthr'.1 z hz
  · obtain ⟨z, hz, hz0, hz'⟩ := exists_ne_zero_add_mul_eq_zero_of_isConeThreshold
      (isCone_coe D.cone) D.cone.convex D.isClosed_cone D.inter_neg_eq hthr'
    intro heq
    have hmem : z ∈ faceOfNefForm C (realOfRatForm N ((n : ℤ) • L + H + tq • D.form)) :=
      ⟨hz, by rwa [happ]⟩
    rw [heq] at hmem
    exact hz0 hmem
  · rw [hface] at hz
    obtain ⟨⟨hzC, -⟩, hht⟩ := hz
    rw [Set.mem_ofPred_eq, happ'] at hht
    have := hH z hzC hz0
    by_contra hk
    push Not at hk
    nlinarith

/-- If the face `F_L` lies in the kernels of `H₀ + t₀ K` and of `H₀ + x_j + t_j K` for every
coordinate `x_j` of a basis of `N`, and `F_L ⊄ NE̅_{K≥0}`, then `F_L ∈ 𝓡(NE̅, K)`. -/
theorem faceOfNefForm_mem_negativeRationalRays_of_forall_eq_zero (D : ConeDatum N)
    {L : N →ₗ[ℤ] ℚ} (hL : ∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z)
    (hLK : ¬ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ⊆
      {z | 0 ≤ realOfRatForm N D.form z})
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℤ N) {H₀ : Module.Dual ℤ N} {t₀ : ℚ}
    {t : ι → ℚ}
    (h₀ : ∀ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L),
      realOfIntForm N H₀ z + t₀ * realOfRatForm N D.form z = 0)
    (hj : ∀ j, ∀ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L),
      realOfIntForm N (H₀ + b.coord j) z + t j * realOfRatForm N D.form z = 0) :
    faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ∈ D.negativeRationalRays := by
  have := Fintype.ofFinite ι
  set k := realOfRatForm N D.form with hkdef
  let bB := Algebra.TensorProduct.basis ℝ b
  obtain ⟨ξ, hξF, hξk⟩ := Set.not_subset.mp hLK
  replace hξk : k ξ < 0 := not_le.mp hξk
  have hzw : ∀ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L),
      z = k z • ∑ j, ((t₀ - t j : ℚ) : ℝ) • bB j := by
    intro z hz
    have hxj : ∀ j, realOfIntForm N (b.coord j) z = ((t₀ - t j : ℚ) : ℝ) * k z := fun j => by
      have ej := hj j z hz
      have e0 := h₀ z hz
      rw [realOfIntForm_add_apply] at ej
      push_cast
      linarith
    conv_lhs => rw [← bB.sum_repr z]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← realOfIntForm_coord_apply, hxj, smul_smul, mul_comm]
  exact ⟨ξ, hξk, faceOfNefForm_eq_ray_of_forall_eq_smul (isCone_coe D.cone) D.inter_neg_eq hzw
    hξF hξk, L, hL, rfl⟩

/-- **KM 3.3 Step 2.** Let `(N_ℤ, NE̅, K, a)` be a cone datum and `L ∈ N_ℚ^*` with `L ≥ 0` on
`NE̅` and `F_L ⊄ NE̅_{K≥0}`. Then there is `L' ∈ N_ℚ^*` with `L' ≥ 0` on `NE̅`, `F_{L'} ⊆ F_L` and
`F_{L'} ∈ 𝓡(NE̅, K)`. -/
@[mmp "lem_km3b_cone_one_dim_subface"]
theorem exists_faceOfNefForm_mem_negativeRationalRays (D : ConeDatum N) {L : N →ₗ[ℤ] ℚ}
    (hL : ∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z)
    (hLK : ¬ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ⊆
      {z | 0 ≤ realOfRatForm N D.form z}) :
    ∃ L' : N →ₗ[ℤ] ℚ, (∀ z ∈ D.cone, 0 ≤ realOfRatForm N L' z) ∧
      faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L') ⊆
        faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ∧
      faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L') ∈ D.negativeRationalRays := by
  classical
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set k := realOfRatForm N D.form with hkdef
  let b := Module.Free.chooseBasis ℤ N
  obtain ⟨H₀, hH₀pos, hHjpos⟩ := exists_intForm_pos_and_add_coord_pos D b
  let Hs : Option (Module.Free.ChooseBasisIndex ℤ N) → Module.Dual ℤ N :=
    fun o => o.elim H₀ fun j => H₀ + b.coord j
  have hHspos : ∀ o, ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N (Hs o) z := by
    rintro (_ | j)
    exacts [hH₀pos, hHjpos j]
  let Hq : Option (Module.Free.ChooseBasisIndex ℤ N) → N →ₗ[ℤ] ℚ :=
    fun o => (Int.castAddHom ℚ).toIntLinearMap ∘ₗ Hs o
  have hHq : ∀ o z, realOfRatForm N (Hq o) z = realOfIntForm N (Hs o) z := fun o z =>
    realOfRatForm_eq_realOfIntForm (fun _ => rfl) z
  suffices key : ∀ n : ℕ, ∀ L : N →ₗ[ℤ] ℚ,
      Module.finrank ℝ (Submodule.span ℝ (faceOfNefForm C (realOfRatForm N L))) = n →
      (∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z) →
      ¬ faceOfNefForm C (realOfRatForm N L) ⊆ {z | 0 ≤ k z} →
      ∃ L' : N →ₗ[ℤ] ℚ, (∀ z ∈ D.cone, 0 ≤ realOfRatForm N L' z) ∧
        faceOfNefForm C (realOfRatForm N L') ⊆ faceOfNefForm C (realOfRatForm N L) ∧
        faceOfNefForm C (realOfRatForm N L') ∈ D.negativeRationalRays from
    key _ L rfl hL hLK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL hLK
  choose n₀ hn₀ t ht0 hprop _ using fun o => exists_faceOfNefForm_subface_negative D hL hLK
    (H := Hq o) fun z hz hz0 => by simpa only [hHq] using hHspos o z hz hz0
  have happ : ∀ o z, realOfRatForm N (Hq o + t o • D.form) z =
      realOfIntForm N (Hs o) z + t o * k z := fun o z => by
    rw [realOfRatForm_add_apply, realOfRatForm_smul_apply, hHq]
  by_cases hvan : ∀ o, ∀ z ∈ faceOfNefForm C (realOfRatForm N L),
      realOfRatForm N (Hq o + t o • D.form) z = 0
  · exact ⟨L, hL, subset_rfl, faceOfNefForm_mem_negativeRationalRays_of_forall_eq_zero D hL hLK b
      (t₀ := t none) (fun z hz => (happ none z).symm.trans (hvan none z hz))
      fun j z hz => (happ (some j) z).symm.trans (hvan (some j) z hz)⟩
  · push Not at hvan
    obtain ⟨o, z, hzF, hz⟩ := hvan
    obtain ⟨hnn, hne, hfeq, hneg⟩ := hprop o (n₀ o) le_rfl
    set L₁ : N →ₗ[ℤ] ℚ := ((n₀ o : ℕ) : ℤ) • L + Hq o + t o • D.form with hL₁
    have hsub : faceOfNefForm C (realOfRatForm N L₁) ⊆ faceOfNefForm C (realOfRatForm N L) :=
      hfeq ▸ Set.inter_subset_left
    have hlt : Module.finrank ℝ (Submodule.span ℝ (faceOfNefForm C (realOfRatForm N L₁))) < n :=
      hn ▸ finrank_span_faceOfNefForm_lt hfeq hzF hz
    have hL₁K : ¬ faceOfNefForm C (realOfRatForm N L₁) ⊆ {z | 0 ≤ k z} := fun hsub' =>
      hne (Set.eq_singleton_iff_unique_mem.mpr ⟨⟨D.cone.zero_mem, map_zero _⟩,
        fun y hy => by_contra fun hy0 => not_le.mpr (hneg y hy hy0) (hsub' hy)⟩)
    obtain ⟨L', h1, h2, h3⟩ := ih _ hlt L₁ rfl hnn hL₁K
    exact ⟨L', h1, h2.trans hsub, h3⟩

end ConeDatum

end MMP.Positivity
