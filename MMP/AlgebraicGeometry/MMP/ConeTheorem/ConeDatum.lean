module

public import MMP.Analysis.Convex.Cone.CompactSlices

/-!
# Thresholds and negative rational rays of a cone datum (KM 3.3, 3.15)

* For a closed convex cone `C`, `G` positive on `C ∖ {0}` and `K` negative somewhere on `C`, the
  `K`-threshold of `G` on `C` exists, is unique and is `≥ 0`.
* For a cone datum `(N_ℤ, NE̅, K, a)`, `H ∈ N_ℤ^*` positive on `NE̅ ∖ {0}` and a ray
  `R ∈ 𝓡(NE̅, K)`, `H(ξ)/K(ξ) ∈ (1/a)ℤ` for `ξ ∈ R ∖ {0}`.
* For `G` positive on `NE̅ ∖ {0}` and `ε > 0`, only finitely many `R ∈ 𝓡(NE̅, K)` have
  `K + εG < 0` on `R ∖ {0}`.

## Main results

* `MMP.Positivity.existsUnique_isConeThreshold`
* `MMP.Positivity.ConeDatum.exists_div_eq_intCast_div_index`
* `MMP.Positivity.ConeDatum.finite_negativeRationalRays_add_smul_neg`
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

/-- The module topology on a finite-dimensional real vector space makes it a Hausdorff
topological vector space. -/
theorem moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (V : Type*) [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] :
    letI := moduleTopology ℝ V
    IsTopologicalAddGroup V ∧ ContinuousSMul ℝ V ∧ T2Space V := by
  let := moduleTopology ℝ V
  have := IsModuleTopology.toContinuousAdd ℝ V
  refine ⟨IsModuleTopology.isTopologicalAddGroup ℝ V, inferInstance, ?_⟩
  let b := Module.Basis.ofVectorSpace ℝ V
  let h : V ≃ₜ (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun :=
        IsModuleTopology.continuous_of_linearMap (R := ℝ) b.equivFun.symm.toLinearMap }
  exact h.isEmbedding.t2Space

/-- **KM Thm. 3.15, the threshold exists.** Let `C ⊆ V` be a closed convex cone, `G ∈ V^*`
positive on `C ∖ {0}` and `K ∈ V^*` with `K(z₀) < 0` for some `z₀ ∈ C`. Then `G` has exactly one
`K`-threshold on `C`, and it is `≥ 0`. That `C` is a closed convex cone is not used. -/
@[mmp "lem_km3b_cone_threshold_exists"]
theorem existsUnique_isConeThreshold {V : Type*} [AddCommGroup V] [Module ℝ V] {C : Set V}
    {G K : Module.Dual ℝ V} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) (hK : ∃ z₀ ∈ C, K z₀ < 0) :
    (∃! t : ℝ, IsConeThreshold C G K t) ∧ ∀ t : ℝ, IsConeThreshold C G K t → 0 ≤ t := by
  set S : Set ℝ := {s | ∀ z ∈ C, 0 ≤ G z + s * K z} with hS
  have h0 : (0 : ℝ) ∈ S := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · simpa using (hG z hz hz0).le
  obtain ⟨z₀, hz₀, hKz₀⟩ := hK
  have hbdd : BddAbove S := by
    refine ⟨G z₀ / -K z₀, fun s hs => ?_⟩
    rw [le_div_iff₀ (by linarith)]
    linarith [hs z₀ hz₀]
  have hcl : IsClosed S := by
    have : S = ⋂ z ∈ C, {s : ℝ | 0 ≤ G z + s * K z} := by
      ext s
      simp [hS]
    rw [this]
    exact isClosed_biInter fun z _ =>
      isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const))
  have hth : IsConeThreshold C G K (sSup S) :=
    (isConeThreshold_iff_isGreatest C G K _).mpr
      ⟨hcl.csSup_mem ⟨0, h0⟩ hbdd, fun s hs => le_csSup hbdd hs⟩
  exact ⟨⟨sSup S, hth, fun t ht => ht.unique hth⟩,
    fun t ht => ((isConeThreshold_iff_isGreatest C G K t).mp ht).2 h0⟩

section Forms

variable {N : Type*} [AddCommGroup N]

/-- The real extension of an integral form sends `r ⊗ₜ n` to `r * H n`. -/
theorem realOfIntForm_tmul (H : Module.Dual ℤ N) (r : ℝ) (n : N) :
    realOfIntForm N H (r ⊗ₜ n) = r * H n := by
  simp [realOfIntForm]

/-- The real extension of a rational form sends `r ⊗ₜ n` to `r * L n`. -/
theorem realOfRatForm_tmul (L : N →ₗ[ℤ] ℚ) (r : ℝ) (n : N) :
    realOfRatForm N L (r ⊗ₜ n) = r * L n := by
  simp [realOfRatForm]

/-- The real extension of integral forms is additive in the form. -/
theorem realOfIntForm_add_apply (H H' : Module.Dual ℤ N) (z : ℝ ⊗[ℤ] N) :
    realOfIntForm N (H + H') z = realOfIntForm N H z + realOfIntForm N H' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfIntForm_tmul, LinearMap.add_apply]
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- The real extension of `k • H` is `k` times the real extension of `H`. -/
theorem realOfIntForm_zsmul_apply (k : ℤ) (H : Module.Dual ℤ N) (z : ℝ ⊗[ℤ] N) :
    realOfIntForm N (k • H) z = k * realOfIntForm N H z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfIntForm_tmul, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- A rational form on a finite free `ℤ`-module has a positive integral multiple. -/
theorem exists_intForm_eq_mul_ratForm [Module.Free ℤ N] [Module.Finite ℤ N] (L : N →ₗ[ℤ] ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ L₀ : Module.Dual ℤ N, ∀ z : ℝ ⊗[ℤ] N,
      realOfIntForm N L₀ z = d * realOfRatForm N L z := by
  let b := Module.Free.chooseBasis ℤ N
  let d : ℕ := ∏ i, (L (b i)).den
  have hd : 0 < d := Finset.prod_pos fun i _ => (L (b i)).den_pos
  have hk : ∀ i, ∃ k : ℤ, (k : ℚ) = d * L (b i) := by
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun j => (L (b j)).den) (Finset.mem_univ i)
    refine ⟨(L (b i)).num * e, ?_⟩
    change (_ : ℚ) = ((∏ j, (L (b j)).den : ℕ) : ℚ) * _
    rw [he]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose k hk using hk
  let L₀ : Module.Dual ℤ N := b.constr ℤ k
  have hL₀ : (Int.castAddHom ℚ).toIntLinearMap ∘ₗ L₀ = (d : ℤ) • L := by
    refine b.ext fun i => ?_
    simp [L₀, hk i]
  refine ⟨d, by exact_mod_cast hd, L₀, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    rw [realOfIntForm_tmul, realOfRatForm_tmul]
    have := LinearMap.congr_fun hL₀ n
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    have h'' : ((L₀ n : ℤ) : ℚ) = d * L n := by simpa [zsmul_eq_mul] using this
    have h' : ((L₀ n : ℤ) : ℝ) = (d : ℝ) * ((L n : ℚ) : ℝ) := by
      exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) h''
    rw [h']
    push_cast
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ring

/-- The real extension of the `i`-th coordinate form of a basis `b` is the `i`-th coordinate in
the base-changed basis of `ℝ ⊗[ℤ] N`. -/
theorem realOfIntForm_coord_apply {ι : Type*} (b : Module.Basis ι ℤ N) (i : ι) (z : ℝ ⊗[ℤ] N) :
    realOfIntForm N (b.coord i) z = (Algebra.TensorProduct.basis ℝ b).repr z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    rw [realOfIntForm_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply]

/-- The real extension of `∑ i ∈ s, v i • H i` is the corresponding `ℤ`-linear combination of the
real extensions of the `H i`. -/
theorem realOfIntForm_sum_zsmul_apply {ι : Type*} (s : Finset ι) (v : ι → ℤ)
    (H : ι → Module.Dual ℤ N) (z : ℝ ⊗[ℤ] N) :
    realOfIntForm N (∑ i ∈ s, v i • H i) z = ∑ i ∈ s, v i * realOfIntForm N (H i) z := by
  induction s using Finset.cons_induction with
  | empty => simpa using realOfIntForm_zsmul_apply (0 : ℤ) (0 : Module.Dual ℤ N) z
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, realOfIntForm_add_apply, realOfIntForm_zsmul_apply, ih]

/-- For a basis `b` of `N`, a real form `G` and `M : ℝ`, rounding the coefficients of `M • G` gives
an integral form `H₀` with `M * G - ∑ |xᵢ| ≤ H₀`, where `xᵢ` are the coordinates of `b`. -/
theorem exists_mul_sub_sum_abs_coord_le_realOfIntForm {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ N) (G : Module.Dual ℝ (ℝ ⊗[ℤ] N)) (M : ℝ) :
    ∃ H₀ : Module.Dual ℤ N, ∀ z,
      M * G z - ∑ i, |realOfIntForm N (b.coord i) z| ≤ realOfIntForm N H₀ z := by
  let bB := Algebra.TensorProduct.basis ℝ b
  let v₀ : ι → ℤ := fun i => round (M * G (bB i))
  refine ⟨∑ i, v₀ i • b.coord i, fun z => ?_⟩
  have hGx : G z = ∑ i, G (bB i) * realOfIntForm N (b.coord i) z := by
    conv_lhs => rw [← bB.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, realOfIntForm_coord_apply, mul_comm]
  rw [realOfIntForm_sum_zsmul_apply, hGx, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : |(M * G (bB i) - v₀ i) * realOfIntForm N (b.coord i) z| ≤
      |realOfIntForm N (b.coord i) z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [abs_sub_round (M * G (bB i))])
  rw [show M * (G (bB i) * realOfIntForm N (b.coord i) z) =
    (M * G (bB i) - v₀ i) * realOfIntForm N (b.coord i) z +
      v₀ i * realOfIntForm N (b.coord i) z by ring]
  linarith [le_abs_self ((M * G (bB i) - v₀ i) * realOfIntForm N (b.coord i) z)]

end Forms

/-- The ray `ℝ_{≥0} (t x)` is the ray `ℝ_{≥0} x` for `t > 0`. -/
theorem setOf_exists_smul_smul_eq_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V] {t : ℝ}
    (ht : 0 < t) (x : V) :
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • (t • x) = w} = {w | ∃ c : ℝ, 0 ≤ c ∧ c • x = w} := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * t, mul_nonneg hc ht.le, by rw [smul_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / t, div_nonneg hc ht.le, by rw [smul_smul, div_mul_cancel₀ c ht.ne']⟩

/-- On a closed cone `C` of a finite-dimensional Hausdorff real vector space, a form `G` positive
on `C ∖ {0}` dominates `∑ |fᵢ|` for finitely many linear forms `fᵢ`, up to a constant. -/
theorem exists_sum_abs_le_mul_of_forall_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C : Set V} (hC : IsCone ℝ C) (hCcl : IsClosed C)
    {G : Module.Dual ℝ V} (hG : ∀ z ∈ C, z ≠ 0 → 0 < G z) {ι : Type*} (s : Finset ι)
    (f : ι → Module.Dual ℝ V) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ C, ∑ i ∈ s, |f i z| ≤ c * G z := by
  have hcont : Continuous fun z => ∑ i ∈ s, |f i z| :=
    continuous_finsetSum _ fun i _ => (LinearMap.continuous_of_finiteDimensional (f i)).abs
  obtain ⟨c, hc⟩ := (isCompact_slice hC hCcl hG 1).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max c 0, le_max_right _ _, fun z hz => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hGz := hG z hz hz0
  have hmem : (G z)⁻¹ • z ∈ {z | z ∈ C ∧ G z ≤ 1} :=
    ⟨smul_mem_of_isCone hC hz (inv_nonneg.2 hGz.le), by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hGz.ne']⟩
  have h1 := hc _ hmem
  simp only [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hGz, ← Finset.mul_sum,
    Real.norm_eq_abs] at h1
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _), inv_mul_le_iff₀ hGz] at h1
  exact h1.trans (by nlinarith [le_max_left c 0])

/-- If every `s < r` lies below some `m / a ≤ r` with `m ∈ ℤ` and `a > 0`, then `r ∈ (1/a)ℤ`,
namely `r = ⌊r a⌋ / a`. -/
theorem eq_floor_mul_div_of_forall_lt {r a : ℝ} (ha : 0 < a)
    (h : ∀ s < r, ∃ m : ℤ, s ≤ m / a ∧ (m : ℝ) / a ≤ r) : r = (⌊r * a⌋ : ℝ) / a := by
  refine le_antisymm (le_of_forall_lt fun s hs => ?_) ?_
  · obtain ⟨m, hsm, hmr⟩ := h ((s + r) / 2) (by linarith)
    refine lt_of_lt_of_le (by linarith) (hsm.trans ?_)
    rw [div_le_div_iff_of_pos_right ha]
    rw [div_le_iff₀ ha] at hmr
    exact_mod_cast Int.le_floor.mpr hmr
  · rw [div_le_iff₀ ha]
    exact Int.floor_le _

namespace ConeDatum

variable {N : Type u} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- Let `(N_ℤ, NE̅, K, a)` be a cone datum, `H ∈ N_ℤ^*` positive on `NE̅ ∖ {0}`, `L₀ ∈ N_ℤ^*`
nonnegative on `NE̅` with face `R`, and `ξ ∈ NE̅` with `L₀(ξ) = 0`, `K(ξ) < 0` and every nonzero
point of `R` a positive multiple of `ξ`. Then every `s < -H(ξ)/K(ξ)` lies below some
`m / a ≤ -H(ξ)/K(ξ)` with `m ∈ ℤ`. -/
theorem exists_le_intCast_div_index_le (D : ConeDatum N) {H L₀ : Module.Dual ℤ N}
    (hH : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H z)
    (hL₀ : ∀ z ∈ D.cone, 0 ≤ realOfIntForm N L₀ z) {R : Set (ℝ ⊗[ℤ] N)}
    (hR : {z | z ∈ (D.cone : Set (ℝ ⊗[ℤ] N)) ∧ realOfIntForm N L₀ z = 0} = R)
    {ξ : ℝ ⊗[ℤ] N} (hξC : ξ ∈ D.cone) (hL₀ξ : realOfIntForm N L₀ ξ = 0)
    (hKξ : realOfRatForm N D.form ξ < 0) (hRξ : ∀ z ∈ R, z ≠ 0 → ∃ c : ℝ, 0 < c ∧ z = c • ξ)
    {s : ℝ} (hs : s < -(realOfIntForm N H ξ / realOfRatForm N D.form ξ)) :
    ∃ m : ℤ, s ≤ m / D.index ∧
      (m : ℝ) / D.index ≤ -(realOfIntForm N H ξ / realOfRatForm N D.form ξ) := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set K := realOfRatForm N D.form
  set r := -(realOfIntForm N H ξ / K ξ) with hr
  have hHξ : realOfIntForm N H ξ = -r * K ξ := by
    rw [hr, neg_neg, div_mul_cancel₀ _ hKξ.ne]
  obtain ⟨m₀, hm₀⟩ := exists_forall_ge_pos_smul_sub (isCone_coe D.cone) D.cone.convex
    D.isClosed_cone D.inter_neg_eq hL₀ hR (K := -(realOfIntForm N H + s • K)) (by
      intro z hz hz0
      obtain ⟨c, hc, rfl⟩ := hRξ z hz hz0
      simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
        smul_eq_mul, hHξ]
      nlinarith [mul_pos hc (mul_pos_of_neg_of_neg (sub_neg.mpr hs) hKξ)])
  obtain ⟨n, hn⟩ := exists_nat_ge m₀
  set Hn : Module.Dual ℤ N := H + (n : ℤ) • L₀ with hHn
  have hHnapp : ∀ z, realOfIntForm N Hn z = realOfIntForm N H z + n * realOfIntForm N L₀ z := by
    intro z
    rw [hHn, realOfIntForm_add_apply, realOfIntForm_zsmul_apply]
    push_cast
    rfl
  have hHnpos : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N Hn z := fun z hz hz0 => by
    rw [hHnapp]
    exact add_pos_of_pos_of_nonneg (hH z hz hz0) (mul_nonneg n.cast_nonneg (hL₀ z hz))
  obtain ⟨⟨t, ht, -⟩, -⟩ := existsUnique_isConeThreshold hHnpos D.exists_form_neg
  obtain ⟨m, hm⟩ := D.threshold_mem Hn hHnpos t ht
  refine ⟨m, ?_, ?_⟩
  · rw [← hm]
    refine ((isConeThreshold_iff_isGreatest _ _ _ t).mp ht).2 fun z hz => ?_
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have := hm₀ n hn z hz hz0
      simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      rw [hHnapp]
      linarith
  · rw [← hm]
    by_contra! hlt
    have := ht.1 ξ hξC
    rw [hHnapp, hL₀ξ, hHξ] at this
    nlinarith

/-- **KM 3.3 Step 4, displayed equation.** Let `(N_ℤ, NE̅, K, a)` be a cone datum, `H ∈ N_ℤ^*`
positive on `NE̅ ∖ {0}`, `R ∈ 𝓡(NE̅, K)` and `ξ ∈ R ∖ {0}`. Then `H(ξ)/K(ξ) ∈ (1/a)ℤ`. -/
@[mmp "lem_km3b_cone_integral_ratios"]
theorem exists_div_eq_intCast_div_index (D : ConeDatum N) {H : Module.Dual ℤ N}
    (hH : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H z) {R : Set (ℝ ⊗[ℤ] N)}
    (hR : R ∈ D.negativeRationalRays) {ξ : ℝ ⊗[ℤ] N} (hξ : ξ ∈ R) (hξ0 : ξ ≠ 0) :
    ∃ m : ℤ, realOfIntForm N H ξ / realOfRatForm N D.form ξ = m / D.index := by
  set K := realOfRatForm N D.form
  obtain ⟨ξ', hKξ', hRξ', L, hL, hRL⟩ := hR
  have hξC : ξ ∈ D.cone := (hRL ▸ hξ).1
  have hLξ : realOfRatForm N L ξ = 0 := (hRL ▸ hξ).2
  -- `ξ` is a positive multiple of `ξ'`, and every nonzero point of `R` a positive multiple of `ξ`
  obtain ⟨c₁, hc₁, rfl⟩ : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ • ξ' = ξ := by
    obtain ⟨c, hc, hcξ⟩ := hRξ' ▸ hξ
    refine ⟨c, lt_of_le_of_ne hc ?_, hcξ⟩
    rintro rfl
    exact hξ0 (by rw [← hcξ, zero_smul])
  have hKξ : K (c₁ • ξ') < 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc₁ hKξ'
  have hRpos : ∀ z ∈ R, z ≠ 0 → ∃ c : ℝ, 0 < c ∧ z = c • (c₁ • ξ') := by
    intro z hz hz0
    obtain ⟨c, hc, rfl⟩ := hRξ' ▸ hz
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hz0 (zero_smul _ _)
    refine ⟨c / c₁, div_pos (lt_of_le_of_ne hc (Ne.symm hc0)) hc₁, ?_⟩
    rw [smul_smul, div_mul_cancel₀ c hc₁.ne']
  set ξ := c₁ • ξ'
  set r := -(realOfIntForm N H ξ / K ξ) with hr
  obtain ⟨d, hd, L₀, hL₀⟩ := exists_intForm_eq_mul_ratForm L
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL₀C : ∀ z ∈ D.cone, 0 ≤ realOfIntForm N L₀ z := fun z hz => by
    rw [hL₀]
    exact mul_nonneg hdR.le (hL z hz)
  have hL₀ξ : realOfIntForm N L₀ ξ = 0 := by rw [hL₀, hLξ, mul_zero]
  have hface : {z | z ∈ (D.cone : Set (ℝ ⊗[ℤ] N)) ∧ realOfIntForm N L₀ z = 0} = R := by
    rw [hRL]
    ext z
    simp only [faceOfNefForm, Set.mem_ofPred_eq, hL₀, mul_eq_zero, hdR.ne', false_or]
  have ha : (0 : ℝ) < D.index := by exact_mod_cast D.index_pos
  have : r = (⌊r * D.index⌋ : ℝ) / D.index := eq_floor_mul_div_of_forall_lt ha fun s hs =>
    exists_le_intCast_div_index_le D hH hL₀C hface hξC hL₀ξ hKξ hRpos hs
  refine ⟨-⌊r * D.index⌋, ?_⟩
  rw [show realOfIntForm N H ξ / K ξ = -r by rw [hr, neg_neg]]
  generalize ⌊r * D.index⌋ = m at this ⊢
  rw [this]
  push_cast
  ring

/-- Every `R ∈ 𝓡(NE̅, K)` is the ray `ℝ_{≥0} ξ` spanned by some `ξ ∈ R ∩ NE̅` with `K(ξ) = -1`. -/
theorem exists_eq_ray_of_mem_negativeRationalRays (D : ConeDatum N) {R : Set (ℝ ⊗[ℤ] N)}
    (hR : R ∈ D.negativeRationalRays) :
    ∃ ξ ∈ R, ξ ∈ D.cone ∧ realOfRatForm N D.form ξ = -1 ∧
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w} := by
  set K := realOfRatForm N D.form
  obtain ⟨ξ', hKξ', hRξ', L, -, hRL⟩ := hR
  set ξ := (-K ξ')⁻¹ • ξ' with hξdef
  have hξR : ξ ∈ R := hRξ' ▸ ⟨_, inv_nonneg.2 (by linarith), rfl⟩
  refine ⟨ξ, hξR, (hRL ▸ hξR).1, ?_, ?_⟩
  · rw [hξdef, map_smul, smul_eq_mul, inv_mul_eq_div, div_neg, div_self hKξ'.ne]
  · rw [hRξ', ← setOf_exists_smul_smul_eq_of_pos (t := -K ξ') (by linarith) ξ, hξdef,
      smul_smul, mul_inv_cancel₀ (by linarith : -K ξ' ≠ 0), one_smul]

/-- Let `(N_ℤ, NE̅, K, a)` be a cone datum, `H₀, H₁ ∈ N_ℤ^*` with `H₀` and `H₀ + H₁` positive on
`NE̅ ∖ {0}`, `R ∈ 𝓡(NE̅, K)` and `ξ ∈ R` with `K(ξ) = -1`. Then `H₁(ξ) ∈ (1/a)ℤ`. -/
theorem exists_realOfIntForm_eq_intCast_div_index (D : ConeDatum N) {H₀ H₁ : Module.Dual ℤ N}
    (h₀ : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H₀ z)
    (h₁ : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N (H₀ + H₁) z) {R : Set (ℝ ⊗[ℤ] N)}
    (hR : R ∈ D.negativeRationalRays) {ξ : ℝ ⊗[ℤ] N} (hξ : ξ ∈ R) (hξ0 : ξ ≠ 0)
    (hKξ : realOfRatForm N D.form ξ = -1) :
    ∃ k : ℤ, realOfIntForm N H₁ ξ = k / D.index := by
  obtain ⟨m₀, hm₀⟩ := exists_div_eq_intCast_div_index D h₀ hR hξ hξ0
  obtain ⟨m₁, hm₁⟩ := exists_div_eq_intCast_div_index D h₁ hR hξ hξ0
  rw [hKξ, div_neg, div_one] at hm₀ hm₁
  rw [realOfIntForm_add_apply] at hm₁
  refine ⟨m₀ - m₁, ?_⟩
  push_cast
  rw [sub_div]
  linarith

/-- Let `(N_ℤ, NE̅, K, a)` be a cone datum, `b` a basis of `N_ℤ` with coordinates `xᵢ`, and `G`
positive on `NE̅ ∖ {0}` with `∑ |xᵢ| ≤ c G` on `NE̅`. Then there is `H₀ ∈ N_ℤ^*` such that `H₀`
and every `H₀ + xⱼ` are positive on `NE̅ ∖ {0}`. -/
theorem exists_intForm_pos_and_add_coord_pos_of_sum_abs_le (D : ConeDatum N)
    {G : Module.Dual ℝ (ℝ ⊗[ℤ] N)} (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < G z) {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℤ N) {c : ℝ}
    (hc : ∀ z ∈ D.cone, ∑ i, |realOfIntForm N (b.coord i) z| ≤ c * G z) :
    ∃ H₀ : Module.Dual ℤ N, (∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N H₀ z) ∧
      ∀ j, ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N (H₀ + b.coord j) z := by
  obtain ⟨M, hM⟩ := exists_gt (2 * c)
  obtain ⟨H₀, hH₀⟩ := exists_mul_sub_sum_abs_coord_le_realOfIntForm b G M
  have hpos : ∀ z ∈ D.cone, z ≠ 0 → 2 * ∑ i, |realOfIntForm N (b.coord i) z| < M * G z := by
    intro z hz hz0
    nlinarith [hc z hz, hG z hz hz0]
  refine ⟨H₀, fun z hz hz0 => ?_, fun j z hz hz0 => ?_⟩
  · have : 0 ≤ ∑ i, |realOfIntForm N (b.coord i) z| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [hH₀ z, hpos z hz hz0]
  · have : |realOfIntForm N (b.coord j) z| ≤ ∑ i, |realOfIntForm N (b.coord i) z| :=
      Finset.single_le_sum (f := fun i => |realOfIntForm N (b.coord i) z|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    rw [realOfIntForm_add_apply]
    linarith [hH₀ z, hpos z hz hz0, neg_abs_le (realOfIntForm N (b.coord j) z)]

/-- **KM 3.3 Step 4, "only finitely many `F_L` such that `F_L · (K + εH) < 0`".** Let
`(N_ℤ, NE̅, K, a)` be a cone datum, `G ∈ N_ℝ^*` positive on `NE̅ ∖ {0}` and `ε > 0`. Then only
finitely many `R ∈ 𝓡(NE̅, K)` satisfy `K + εG < 0` on `R ∖ {0}`. -/
@[mmp "lem_km3b_cone_rays_finitely_many_below"]
theorem finite_negativeRationalRays_add_smul_neg (D : ConeDatum N)
    {G : Module.Dual ℝ (ℝ ⊗[ℤ] N)} (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < G z) {ε : ℝ} (hε : 0 < ε) :
    {R | R ∈ D.negativeRationalRays ∧
      ∀ z ∈ R, z ≠ 0 → realOfRatForm N D.form z + ε * G z < 0}.Finite := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  let b := Module.Free.chooseBasis ℤ N
  let bB := Algebra.TensorProduct.basis ℝ b
  -- the coordinates `xᵢ` of `N_ℝ` in the basis `bB` are integral forms
  let x : Module.Free.ChooseBasisIndex ℤ N → Module.Dual ℝ (ℝ ⊗[ℤ] N) :=
    fun i => realOfIntForm N (b.coord i)
  have hx : ∀ z, ∑ i, x i z • bB i = z := fun z => by
    simpa only [x, realOfIntForm_coord_apply] using bB.sum_repr z
  obtain ⟨c, hc0, hc⟩ := exists_sum_abs_le_mul_of_forall_pos (isCone_coe D.cone)
    D.isClosed_cone hG Finset.univ x
  obtain ⟨H₀, hH₀pos, hHjpos⟩ := exists_intForm_pos_and_add_coord_pos_of_sum_abs_le D hG b hc
  -- every ray in question is spanned by `∑ (kᵢ / a) bBᵢ` with `|kᵢ| ≤ B`
  set B : ℕ := ⌈(D.index : ℝ) * c / ε⌉₊
  let T : Set (Module.Free.ChooseBasisIndex ℤ N → ℤ) :=
    Set.univ.pi fun _ => Set.Icc (-(B : ℤ)) B
  have hT : T.Finite := Set.Finite.pi fun _ => Set.finite_Icc _ _
  let f : (Module.Free.ChooseBasisIndex ℤ N → ℤ) → Set (ℝ ⊗[ℤ] N) := fun k =>
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • (∑ i, ((k i : ℝ) / D.index) • bB i) = w}
  refine (hT.image f).subset ?_
  rintro R ⟨hR, hRneg⟩
  obtain ⟨ξ, hξR, hξC, hKξ, hRξ⟩ := exists_eq_ray_of_mem_negativeRationalRays D hR
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hKξ
  have hGξ : ε * G ξ < 1 := by linarith [hRneg ξ hξR hξ0]
  have ha : (0 : ℝ) < D.index := by exact_mod_cast D.index_pos
  have hcoord : ∀ j, ∃ k : ℤ, x j ξ = k / D.index ∧ k ∈ Set.Icc (-(B : ℤ)) B := by
    intro j
    obtain ⟨k, hxj⟩ : ∃ k : ℤ, x j ξ = k / D.index :=
      exists_realOfIntForm_eq_intCast_div_index D hH₀pos (hHjpos j) hR hξR hξ0 hKξ
    refine ⟨k, hxj, ?_⟩
    have hbd : |x j ξ| ≤ c / ε :=
      calc |x j ξ| ≤ ∑ i, |x i ξ| :=
            Finset.single_le_sum (f := fun i => |x i ξ|) (fun i _ => abs_nonneg _)
              (Finset.mem_univ j)
        _ ≤ c * G ξ := hc ξ hξC
        _ ≤ c / ε := by
          rw [le_div_iff₀ hε]
          nlinarith
    rw [hxj, abs_div, abs_of_pos ha, div_le_iff₀ ha] at hbd
    have hk : |(k : ℝ)| ≤ B :=
      hbd.trans ((by ring : c / ε * (D.index : ℝ) = D.index * c / ε).trans_le (Nat.le_ceil _))
    rw [← Int.cast_abs] at hk
    exact abs_le.mp (by exact_mod_cast hk)
  choose k hk using hcoord
  refine ⟨k, fun j _ => (hk j).2, ?_⟩
  have hsum : ∑ i, ((k i : ℝ) / D.index) • bB i = ξ := by
    conv_rhs => rw [← hx ξ]
    exact Finset.sum_congr rfl fun i _ => by rw [(hk i).1]
  rw [hRξ, ← hsum]

end ConeDatum

end MMP.Positivity
