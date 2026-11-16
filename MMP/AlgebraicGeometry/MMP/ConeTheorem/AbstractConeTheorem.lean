module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ConeDatumFaces

/-!
# The abstract cone theorem, finite part (KM 3.3 Step 4, 3.14)

* For a closed convex cone `C` and `L ≥ 0` on `C`, `F_L = C ∩ L^⊥` is a closed convex extremal
  face of `C`.
* For a cone datum `(N_ℤ, NE̅, K, a)`, `G` positive on `NE̅ ∖ {0}` and `ε > 0`,
  `NE̅ = NE̅_{K+εG≥0} + ∑ R`, the sum over the finitely many `R ∈ 𝓡(NE̅, K)` with `K + εG < 0` on
  `R ∖ {0}`.

## Main results

* `MMP.Positivity.isClosed_convex_isExtremalFace_faceOfNefForm`
* `MMP.Positivity.ConeDatum.cone_eq_nonneg_add_sum_rays`
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace MMP.Positivity

open MMP.Mori

/-- **KM 3.14, "thus `NE(X) ∩ (H + r(K_X + Δ))^⊥` is a face".** Let `C ⊆ V` be a closed convex
cone and `L ∈ V^*` with `L ≥ 0` on `C`. Then `F_L` is a closed convex extremal face of `C`. -/
@[mmp "lem_km3b_face_of_nef_class_extremal"]
theorem isClosed_convex_isExtremalFace_faceOfNefForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    {L : Module.Dual ℝ V} (hL : ∀ z ∈ C, 0 ≤ L z) :
    IsClosed (faceOfNefForm C L) ∧ Convex ℝ (faceOfNefForm C L) ∧
      IsExtremalFace ℝ C (faceOfNefForm C L) := by
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hCadd : ∀ u ∈ C, ∀ v ∈ C, u + v ∈ C := fun u hu v hv => by
    have hm := hCc hu hv (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    have h2 := hC.2 _ hm 2 (by norm_num)
    rwa [smul_add, smul_smul, smul_smul, mul_inv_cancel₀ (two_ne_zero), one_smul, one_smul] at h2
  exact ⟨hCcl.inter (isClosed_eq hLc continuous_const),
    hCc.inter (convex_hyperplane L.isLinear 0), isExtremalFace_faceOfNefForm hC hCadd hL⟩

/-- **Separation of a point from a closed convex cone.** If `W ⊆ V` is a closed convex cone and
`x ∉ W`, there is `ℓ ∈ V^*` with `ℓ ≥ 0` on `W` and `ℓ(x) < 0`. -/
theorem exists_dual_nonneg_neg_of_notMem {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {W : Set V} (hW : IsCone ℝ W) (hWc : Convex ℝ W) (hWcl : IsClosed W)
    {x : V} (hx : x ∉ W) : ∃ ℓ : Module.Dual ℝ V, (∀ w ∈ W, 0 ≤ ℓ w) ∧ ℓ x < 0 := by
  let e := toEuclidean (E := V)
  have hx' : e x ∉ e.symm ⁻¹' W := by simpa using hx
  obtain ⟨f, u, hfu, hfW⟩ := geometric_hahn_banach_point_closed
    (hWc.linear_preimage e.symm.toLinearMap) (hWcl.preimage e.symm.continuous) hx'
  have hu : u < 0 := by simpa using hfW 0 (by simpa using hW.1)
  refine ⟨(f : _ →ₗ[ℝ] ℝ).comp e.toLinearMap, fun w hw => ?_, ?_⟩
  · by_contra hneg
    push Not at hneg
    change f (e w) < 0 at hneg
    have hc : 0 < u / f (e w) := div_pos_of_neg_of_neg hu hneg
    have := hfW (e ((u / f (e w)) • w)) (by simpa using hW.2 w hw _ hc)
    rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ u hneg.ne] at this
    exact lt_irrefl _ this
  · exact hfu.trans hu

/-- A linear form positive on `C ∖ {0}` is nonnegative on `C`. -/
theorem forall_mem_nonneg_of_forall_ne_zero_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : Set V} {P : Module.Dual ℝ V} (hP : ∀ z ∈ C, z ≠ 0 → 0 < P z) : ∀ z ∈ C, 0 ≤ P z :=
  fun z hz => by
    rcases eq_or_ne z 0 with rfl | h0
    · simp
    · exact (hP z hz h0).le

/-- If `C` is a closed convex cone and `φ ∈ V^*`, then `C_{φ≥0}` is a closed convex cone. -/
theorem isCone_isClosed_convex_setOf_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [FiniteDimensional ℝ V] {C : Set V} (hC : IsCone ℝ C) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    (φ : Module.Dual ℝ V) :
    IsCone ℝ {c | c ∈ C ∧ 0 ≤ φ c} ∧ IsClosed {c | c ∈ C ∧ 0 ≤ φ c} ∧
      Convex ℝ {c | c ∈ C ∧ 0 ≤ φ c} := by
  refine ⟨⟨⟨hC.1, by simp⟩, fun v hv c hc => ⟨hC.2 v hv.1 c hc, ?_⟩⟩,
    hCcl.inter (isClosed_le continuous_const (LinearMap.continuous_of_finiteDimensional φ)),
    hCc.inter (convex_halfSpace_ge φ.isLinear 0)⟩
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg hc.le hv.2

/-- The sum `∑ Dᵢ` of finitely many convex cones is a convex cone containing each `Dᵢ`. -/
theorem isCone_convex_sum_cones {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (D : Fin k → Set V) (hD : ∀ i, IsCone ℝ (D i)) (hDc : ∀ i, Convex ℝ (D i)) :
    IsCone ℝ {x | ∃ c : Fin k → V, (∀ i, c i ∈ D i) ∧ x = ∑ i, c i} ∧
      Convex ℝ {x | ∃ c : Fin k → V, (∀ i, c i ∈ D i) ∧ x = ∑ i, c i} ∧
      ∀ i, D i ⊆ {x | ∃ c : Fin k → V, (∀ i, c i ∈ D i) ∧ x = ∑ i, c i} := by
  classical
  refine ⟨⟨⟨0, fun i => (hD i).1, by simp⟩, ?_⟩, ?_,
    fun i w hw => ⟨Pi.single i w, fun j => ?_, by simp⟩⟩
  · rintro _ ⟨c, hc, rfl⟩ t ht
    exact ⟨fun i => t • c i, fun i => (hD i).2 _ (hc i) t ht, by rw [Finset.smul_sum]⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ a b ha hb hab
    exact ⟨fun i => a • c i + b • d i, fun i => hDc i (hc i) (hd i) ha hb hab,
      by simp [Finset.smul_sum, Finset.sum_add_distrib]⟩
  · rcases eq_or_ne j i with rfl | hji
    · simpa using hw
    · simpa [Pi.single_apply, hji] using (hD j).1

/-- A sum over `Fin (#S + 1)` whose `i.succ` term lies in the `i`-th member of `S` is
`c₀ + ∑_{R ∈ S} r_R` with `r_R ∈ R`. -/
theorem exists_sum_eq_add_sum_of_mem {V : Type*} [AddCommGroup V] (S : Finset (Set V))
    (c : Fin (S.card + 1) → V) (hc : ∀ i : Fin S.card, c i.succ ∈ (S.equivFin.symm i : Set V)) :
    ∃ r : Set V → V, (∀ R ∈ S, r R ∈ R) ∧ ∑ i, c i = c 0 + ∑ R ∈ S, r R := by
  classical
  refine ⟨fun R => if h : R ∈ S then c (S.equivFin ⟨R, h⟩).succ else 0, fun R hR => ?_, ?_⟩
  · simpa [hR] using hc (S.equivFin ⟨R, hR⟩)
  · rw [Fin.sum_univ_succ, ← Finset.sum_coe_sort S, ← S.equivFin.symm.sum_comp]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp

/-- The real extension of `∑ i, qᵢ bᵢ^*` is `z ↦ ∑ i, qᵢ bᵢ^*(z)`. -/
theorem realOfRatForm_sum_smul_coord_apply {N : Type u} [AddCommGroup N] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℤ N) (q : ι → ℚ) (z : ℝ ⊗[ℤ] N) :
    realOfRatForm N (∑ i, q i • ((Int.castAddHom ℚ).toIntLinearMap ∘ₗ b.coord i)) z =
      ∑ i, (q i : ℝ) * realOfIntForm N (b.coord i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    simp only [realOfRatForm_tmul, realOfIntForm_tmul, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom, smul_eq_mul]
    push_cast
    ring
  | add y w hy hw => simp only [map_add, hy, hw, ← Finset.sum_add_distrib, mul_add]

namespace ConeDatum

variable {N : Type u} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- **Rational approximation of a real form on a cone datum.** Let `(N_ℤ, NE̅, K, a)` be a cone
datum, `P ∈ N_ℝ^*` positive on `NE̅ ∖ {0}`, `ℓ₀ ∈ N_ℝ^*` and `δ > 0`. Then there is `L ∈ N_ℚ^*`
with `|L(z) - ℓ₀(z)| ≤ δ P(z)` for every `z ∈ NE̅`. -/
theorem exists_ratForm_abs_sub_le (D : ConeDatum N) {P : Module.Dual ℝ (ℝ ⊗[ℤ] N)}
    (hP : ∀ z ∈ D.cone, z ≠ 0 → 0 < P z) (ℓ₀ : Module.Dual ℝ (ℝ ⊗[ℤ] N)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ L : N →ₗ[ℤ] ℚ, ∀ z ∈ D.cone, |realOfRatForm N L z - ℓ₀ z| ≤ δ * P z := by
  classical
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  let b := Module.Free.chooseBasis ℤ N
  let bB := Algebra.TensorProduct.basis ℝ b
  let x : Module.Free.ChooseBasisIndex ℤ N → Module.Dual ℝ (ℝ ⊗[ℤ] N) :=
    fun i => realOfIntForm N (b.coord i)
  have hx : ∀ z, ∑ i, x i z • bB i = z := fun z => by
    simpa only [x, realOfIntForm_coord_apply] using bB.sum_repr z
  have hℓx : ∀ z, ℓ₀ z = ∑ i, ℓ₀ (bB i) * x i z := fun z => by
    conv_lhs => rw [← hx z]
    simp [map_sum, mul_comm]
  obtain ⟨c, hc0, hc⟩ := exists_sum_abs_le_mul_of_forall_pos (isCone_coe D.cone)
    D.isClosed_cone hP Finset.univ x
  set η := δ / (c + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hq : ∀ i, ∃ q : ℚ, |(q : ℝ) - ℓ₀ (bB i)| ≤ η := fun i => by
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ℓ₀ (bB i) - η < ℓ₀ (bB i) by linarith)
    exact ⟨q, abs_le.2 ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  refine ⟨∑ i, q i • ((Int.castAddHom ℚ).toIntLinearMap ∘ₗ b.coord i), fun z hz => ?_⟩
  rw [realOfRatForm_sum_smul_coord_apply, hℓx, ← Finset.sum_sub_distrib]
  calc |∑ i, ((q i : ℝ) * x i z - ℓ₀ (bB i) * x i z)|
      ≤ ∑ i, |(q i : ℝ) * x i z - ℓ₀ (bB i) * x i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, η * |x i z| := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _)
    _ = η * ∑ i, |x i z| := (Finset.mul_sum _ _ _).symm
    _ ≤ η * (c * P z) := mul_le_mul_of_nonneg_left (hc z hz) hη0.le
    _ ≤ δ * P z := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (forall_mem_nonneg_of_forall_ne_zero_pos hP z hz)
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- Every `R ∈ 𝓡(NE̅, K)` is a closed convex cone in `NE̅` with a nonzero point. -/
theorem isCone_isClosed_convex_of_mem_negativeRationalRays (D : ConeDatum N)
    {R : Set (ℝ ⊗[ℤ] N)} (hR : R ∈ D.negativeRationalRays) :
    IsCone ℝ R ∧ @IsClosed _ (moduleTopology ℝ (ℝ ⊗[ℤ] N)) R ∧ Convex ℝ R ∧
      R ⊆ (D.cone : Set (ℝ ⊗[ℤ] N)) ∧ ∃ ξ ∈ R, ξ ≠ 0 := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨ξ, hKξ, hRξ, L, hL, hRL⟩ := hR
  obtain ⟨hcl, hcv, hext⟩ := isClosed_convex_isExtremalFace_faceOfNefForm (isCone_coe D.cone)
    D.cone.convex D.isClosed_cone hL
  refine ⟨hRL ▸ hext.2.1, hRL ▸ hcl, hRL ▸ hcv, hRL ▸ hext.1, ξ, ?_, ?_⟩
  · rw [hRξ]
    exact ⟨1, zero_le_one, one_smul _ _⟩
  · rintro rfl
    simp at hKξ

/-- **Rational separation from a closed convex subcone.** If `W ⊆ NE̅` is a closed convex cone
and `x ∈ NE̅ ∖ W`, there is `ℓ ∈ N_ℚ^*` with `ℓ ≥ 0` on `W` and `ℓ(x) < 0`. -/
theorem exists_ratForm_nonneg_neg_of_notMem (D : ConeDatum N) {W : Set (ℝ ⊗[ℤ] N)}
    (hW : IsCone ℝ W) (hWc : Convex ℝ W) (hWcl : @IsClosed _ (moduleTopology ℝ (ℝ ⊗[ℤ] N)) W)
    (hWC : W ⊆ D.cone) {x : ℝ ⊗[ℤ] N} (hx : x ∈ D.cone) (hxW : x ∉ W) :
    ∃ ℓ : N →ₗ[ℤ] ℚ, (∀ w ∈ W, 0 ≤ realOfRatForm N ℓ w) ∧ realOfRatForm N ℓ x < 0 := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨ℓ₀, hℓ₀W, hℓ₀x⟩ := exists_dual_nonneg_neg_of_notMem hW hWc hWcl hxW
  obtain ⟨H₀, hH₀, -⟩ := exists_intForm_pos_and_add_coord_pos D (Module.Free.chooseBasis ℤ N)
  set h := realOfIntForm N H₀ with hhdef
  have hhx := hH₀ x hx fun h0 => hxW (h0 ▸ hW.1)
  set δ := -ℓ₀ x / (4 * h x) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by linarith)
  obtain ⟨ℓq, hℓq⟩ := exists_ratForm_abs_sub_le D hH₀ (ℓ₀ + δ • h) hδ0
  refine ⟨ℓq, fun w hw => ?_, ?_⟩
  · have := hℓq w (hWC hw)
    rw [abs_le] at this
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
    linarith [hℓ₀W w hw]
  · have h1 := hℓq x hx
    rw [abs_le] at h1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : δ * h x = -ℓ₀ x / 4 := by
      rw [hδ]
      field_simp
    linarith

/-- Let `H ∈ N_ℚ^*` be positive on `NE̅ ∖ {0}`, `ℓ ∈ N_ℚ^*` negative somewhere on `NE̅`, with
`K < 0` wherever `ℓ < 0` on `NE̅`, and `κ ≥ 0`. Then for some rational `s > 0`, `H + sℓ` is
positive on `NE̅ ∖ {0}` and every `t ≥ 0` with `H + sℓ + tK ≥ 0` on `NE̅` satisfies `tκ < 1`. -/
theorem exists_rat_pos_add_smul_threshold_mul_lt (D : ConeDatum N) {H ℓq : N →ₗ[ℤ] ℚ}
    (hH : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfRatForm N H z) {x : ℝ ⊗[ℤ] N} (hx : x ∈ D.cone)
    (hℓx : realOfRatForm N ℓq x < 0)
    (hK : ∀ z ∈ D.cone, realOfRatForm N ℓq z < 0 → realOfRatForm N D.form z < 0) {κ : ℝ}
    (hκ0 : 0 ≤ κ) :
    ∃ s : ℚ, (0 : ℝ) < s ∧ (∀ z ∈ D.cone, z ≠ 0 → 0 < realOfRatForm N (H + s • ℓq) z) ∧
      ∀ t : ℝ, 0 ≤ t → (∀ z ∈ D.cone,
        0 ≤ realOfRatForm N (H + s • ℓq) z + t * realOfRatForm N D.form z) → t * κ < 1 := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set h := realOfRatForm N H with hhdef
  set ℓ := realOfRatForm N ℓq with hℓdef
  set K := realOfRatForm N D.form with hKdef
  have hGs : ∀ (s : ℚ) z, realOfRatForm N (H + s • ℓq) z = h z + s * ℓ z := fun s z => by
    rw [realOfRatForm_add_apply, realOfRatForm_smul_apply]
  obtain ⟨⟨μ, hμ, -⟩, hμ0⟩ := existsUnique_isConeThreshold hH ⟨x, hx, hℓx⟩
  obtain ⟨z₁, hz₁C, hz₁0, hz₁⟩ := exists_ne_zero_add_mul_eq_zero_of_isConeThreshold
    (isCone_coe D.cone) D.cone.convex D.isClosed_cone D.inter_neg_eq hμ
  have hhz₁ := hH z₁ hz₁C hz₁0
  have hμpos : 0 < μ := by
    rcases (hμ0 μ hμ).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul, add_zero] at hz₁
      linarith
  have hKz₁ := hK z₁ hz₁C (by nlinarith)
  have hY : 0 < h z₁ * κ + 1 := by nlinarith [mul_nonneg hhz₁.le hκ0]
  have hX : 0 < -K z₁ * μ / (h z₁ * κ + 1) := div_pos (by nlinarith) hY
  have hlo_lt : max 0 (μ - -K z₁ * μ / (h z₁ * κ + 1)) < μ := max_lt hμpos (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hlo_lt
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (le_max_left _ _) hs1
  have hs3 : μ - -K z₁ * μ / (h z₁ * κ + 1) < s := lt_of_le_of_lt (le_max_right _ _) hs1
  refine ⟨s, hs0, fun z hz hz0 => ?_, fun t ht0 ht => ?_⟩
  · rw [hGs]
    have e1 : μ * (h z + s * ℓ z) = (μ - s) * h z + s * (h z + μ * ℓ z) := by ring
    have : 0 < μ * (h z + s * ℓ z) := by
      rw [e1]
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) (hH z hz hz0))
        (mul_nonneg hs0.le (hμ.1 z hz))
    exact pos_of_mul_pos_right this hμpos.le
  have h1 := ht z₁ hz₁C
  rw [hGs] at h1
  have h2 : t * -K z₁ * μ ≤ (μ - s) * h z₁ := by
    have h3 := mul_nonneg hμpos.le h1
    have e1 : μ * (h z₁ + s * ℓ z₁ + t * K z₁) =
        (μ - s) * h z₁ + t * K z₁ * μ + s * (h z₁ + μ * ℓ z₁) := by ring
    rw [e1, hz₁] at h3
    linarith
  have h3 : (μ - s) * (h z₁ * κ + 1) < -K z₁ * μ := (lt_div_iff₀ hY).1 (by linarith)
  have hA : 0 < -K z₁ * μ := mul_pos (by linarith) hμpos
  have h4 : t * κ * (-K z₁ * μ) < 1 * (-K z₁ * μ) := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hκ0]
  exact lt_of_mul_lt_mul_right h4 hA.le

/-- **KM 3.5, rationality of the threshold.** If `G ∈ N_ℚ^*` is positive on `NE̅ ∖ {0}`, its
`K`-threshold `t ≥ 0` is rational: `G + tK = L` for some `L ∈ N_ℚ^*`, and `F_L ≠ {0}`. -/
theorem exists_isConeThreshold_ratForm_faceOfNefForm_ne_bot (D : ConeDatum N) {G : N →ₗ[ℤ] ℚ}
    (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfRatForm N G z) :
    ∃ t : ℝ, IsConeThreshold (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N G)
      (realOfRatForm N D.form) t ∧ 0 ≤ t ∧ ∃ L : N →ₗ[ℤ] ℚ,
      (∀ z, realOfRatForm N L z = realOfRatForm N G z + t * realOfRatForm N D.form z) ∧
        faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ≠ {0} := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨⟨t, ht, -⟩, ht0⟩ := existsUnique_isConeThreshold hG D.exists_form_neg
  obtain ⟨d, hd, L₀, hL₀⟩ := exists_intForm_eq_mul_ratForm G
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL₀pos : ∀ z ∈ D.cone, z ≠ 0 → 0 < realOfIntForm N L₀ z := fun z hz hz0 => by
    rw [hL₀]
    exact mul_pos hdR (hG z hz hz0)
  obtain ⟨m, hm⟩ := D.threshold_mem L₀ hL₀pos (d * t) (isConeThreshold_of_eq_mul hdR hL₀ ht)
  have ha : (0 : ℝ) < D.index := by exact_mod_cast D.index_pos
  set tq : ℚ := m / (D.index * d) with htq
  have htq' : (tq : ℝ) = t := by
    rw [eq_div_iff ha.ne'] at hm
    rw [htq]
    push_cast
    rw [div_eq_iff (by positivity), ← hm]
    ring
  have hL : ∀ z, realOfRatForm N (G + tq • D.form) z =
      realOfRatForm N G z + t * realOfRatForm N D.form z := fun z => by
    rw [realOfRatForm_add_apply, realOfRatForm_smul_apply, htq']
  refine ⟨t, ht, ht0 t ht, G + tq • D.form, hL, ?_⟩
  have heq : realOfRatForm N (G + tq • D.form) = realOfRatForm N G + t • realOfRatForm N D.form :=
    LinearMap.ext fun z => by rw [hL, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [heq]
  exact faceOfNefForm_add_smul_ne_bot (isCone_coe D.cone) D.cone.convex D.isClosed_cone hG ht

/-- **KM 3.3 Step 3, the nef form.** If `ℓ ∈ N_ℚ^*` is negative somewhere on `NE̅` and `K < 0`
wherever `ℓ < 0` on `NE̅`, there is `L ∈ N_ℚ^*` with `L ≥ 0` on `NE̅`, `F_L ≠ {0}` and `ℓ < 0` on
`F_L ∖ {0}`. -/
theorem exists_ratForm_nonneg_faceOfNefForm_ne_bot_neg (D : ConeDatum N) {ℓq : N →ₗ[ℤ] ℚ}
    {x : ℝ ⊗[ℤ] N} (hx : x ∈ D.cone) (hℓx : realOfRatForm N ℓq x < 0)
    (hK : ∀ z ∈ D.cone, realOfRatForm N ℓq z < 0 → realOfRatForm N D.form z < 0) :
    ∃ L : N →ₗ[ℤ] ℚ, (∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z) ∧
      faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ≠ {0} ∧
      ∀ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L), z ≠ 0 →
        realOfRatForm N ℓq z < 0 := by
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  obtain ⟨H₀, hH₀, -⟩ := exists_intForm_pos_and_add_coord_pos D (Module.Free.chooseBasis ℤ N)
  let Hq : N →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap ∘ₗ H₀
  set h := realOfRatForm N Hq with hhdef
  have hh : ∀ z ∈ D.cone, z ≠ 0 → 0 < h z := fun z hz h0 => by
    rw [hhdef, realOfRatForm_eq_realOfIntForm (H := H₀) (fun n => rfl)]
    exact hH₀ z hz h0
  set K := realOfRatForm N D.form with hKdef
  obtain ⟨κ, hκ0, hκ⟩ := exists_sum_abs_le_mul_of_forall_pos (isCone_coe D.cone) D.isClosed_cone
    hh (Finset.univ : Finset Unit) (fun _ => K)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hκ
  obtain ⟨s, hs0, hGspos, htκ⟩ := exists_rat_pos_add_smul_threshold_mul_lt D hh hx hℓx hK hκ0
  obtain ⟨t, ht, ht0, L, hL, hFne⟩ := exists_isConeThreshold_ratForm_faceOfNefForm_ne_bot D hGspos
  have htκ' := htκ t ht0 ht.1
  refine ⟨L, fun z hz => by rw [hL]; exact ht.1 z hz, hFne, ?_⟩
  rintro z ⟨hzC, hz⟩ hz0
  rw [hL, realOfRatForm_add_apply, realOfRatForm_smul_apply] at hz
  have h3 : -K z ≤ κ * h z := le_trans (neg_le_abs _) (hκ z hzC)
  have : s * realOfRatForm N ℓq z < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 ht0, mul_pos (sub_pos.2 htκ') (hh z hzC hz0)]
  by_contra hℓz
  push Not at hℓz
  nlinarith [mul_nonneg hs0.le hℓz]

/-- **KM 3.3 Step 3.** A closed convex cone `W ⊆ NE̅` containing `NE̅_{K≥0}` and meeting every
`R ∈ 𝓡(NE̅, K)` in a nonzero point is all of `NE̅`. -/
theorem cone_subset_of_forall_mem_negativeRationalRays (D : ConeDatum N) {W : Set (ℝ ⊗[ℤ] N)}
    (hW : IsCone ℝ W) (hWc : Convex ℝ W) (hWcl : @IsClosed _ (moduleTopology ℝ (ℝ ⊗[ℤ] N)) W)
    (hWC : W ⊆ D.cone) (hWK : ∀ z ∈ D.cone, 0 ≤ realOfRatForm N D.form z → z ∈ W)
    (hWR : ∀ R ∈ D.negativeRationalRays, ∃ z ∈ R, z ≠ 0 ∧ z ∈ W) :
    (D.cone : Set (ℝ ⊗[ℤ] N)) ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨ℓq, hℓW, hℓx⟩ := exists_ratForm_nonneg_neg_of_notMem D hW hWc hWcl hWC hx hxW
  have hK : ∀ z ∈ D.cone, realOfRatForm N ℓq z < 0 → realOfRatForm N D.form z < 0 :=
    fun z hzC hz => not_le.1 fun hKz => absurd (hℓW z (hWK z hzC hKz)) (not_le.2 hz)
  obtain ⟨L, hLC, hFne, hFneg⟩ := exists_ratForm_nonneg_faceOfNefForm_ne_bot_neg D hx hℓx hK
  have hLK : ¬ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L) ⊆
      {z | 0 ≤ realOfRatForm N D.form z} := by
    intro hsub
    obtain ⟨z, hzF, hz0⟩ :
        ∃ z ∈ faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L), z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hFne (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.cone.zero_mem, map_zero _⟩, hcon⟩)
    exact absurd (hsub hzF) (not_le.2 (hK z hzF.1 (hFneg z hzF hz0)))
  obtain ⟨L', -, hL'sub, hL'R⟩ := exists_faceOfNefForm_mem_negativeRationalRays D hLC hLK
  obtain ⟨z, hzR, hz0, hzW⟩ := hWR _ hL'R
  exact absurd (hℓW z hzW) (not_le.2 (hFneg z (hL'sub hzR) hz0))

/-- **KM 3.3 Step 4, end: abstract form of (3.7.2).** Let `(N_ℤ, NE̅, K, a)` be a cone datum,
`G ∈ N_ℝ^*` positive on `NE̅ ∖ {0}` and `ε > 0`. Then `NE̅` is the sum of `NE̅_{K+εG≥0}` and the
finitely many `R ∈ 𝓡(NE̅, K)` with `K + εG < 0` on `R ∖ {0}`. -/
@[mmp "thm_km3b_abstract_cone_finite"]
theorem cone_eq_nonneg_add_sum_rays (D : ConeDatum N) {G : Module.Dual ℝ (ℝ ⊗[ℤ] N)}
    (hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < G z) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (Set (ℝ ⊗[ℤ] N)),
      (↑S : Set (Set (ℝ ⊗[ℤ] N))) = {R | R ∈ D.negativeRationalRays ∧
        ∀ z ∈ R, z ≠ 0 → realOfRatForm N D.form z + ε * G z < 0} ∧
      (D.cone : Set (ℝ ⊗[ℤ] N)) =
        {x | ∃ c ∈ D.cone, 0 ≤ realOfRatForm N D.form c + ε * G c ∧
          ∃ r : Set (ℝ ⊗[ℤ] N) → ℝ ⊗[ℤ] N, (∀ R ∈ S, r R ∈ R) ∧ x = c + ∑ R ∈ S, r R} := by
  classical
  let := moduleTopology ℝ (ℝ ⊗[ℤ] N)
  obtain ⟨h₁, h₂, h₃⟩ := moduleTopology_isTopologicalAddGroup_continuousSMul_t2Space (ℝ ⊗[ℤ] N)
  set C : Set (ℝ ⊗[ℤ] N) := (D.cone : Set (ℝ ⊗[ℤ] N)) with hCdef
  set K := realOfRatForm N D.form with hKdef
  set T := {R | R ∈ D.negativeRationalRays ∧ ∀ z ∈ R, z ≠ 0 → K z + ε * G z < 0} with hT
  have hTfin : T.Finite := finite_negativeRationalRays_add_smul_neg D hG hε
  set S := hTfin.toFinset with hS
  refine ⟨S, hTfin.coe_toFinset, ?_⟩
  have hSmem : ∀ R, R ∈ S ↔ R ∈ T := fun R => hTfin.mem_toFinset
  set Cge : Set (ℝ ⊗[ℤ] N) := {c | c ∈ C ∧ 0 ≤ K c + ε * G c} with hCge
  let e : Fin S.card ≃ S := S.equivFin.symm
  let Df : Fin (S.card + 1) → Set (ℝ ⊗[ℤ] N) := Fin.cons Cge fun i => (e i : Set (ℝ ⊗[ℤ] N))
  have hDf : ∀ i, IsCone ℝ (Df i) ∧ IsClosed (Df i) ∧ Convex ℝ (Df i) ∧ Df i ⊆ C := by
    refine Fin.cases ?_ fun j => ?_
    · simp only [Df, Fin.cons_zero]
      obtain ⟨h1, h2, h3⟩ := isCone_isClosed_convex_setOf_nonneg (isCone_coe D.cone) D.cone.convex
        D.isClosed_cone (K + ε • G)
      exact ⟨h1, h2, h3, fun z hz => hz.1⟩
    · simp only [Df, Fin.cons_succ]
      obtain ⟨h1, h2, h3, h4, -⟩ :=
        isCone_isClosed_convex_of_mem_negativeRationalRays D ((hSmem _).1 (e j).2).1
      exact ⟨h1, h2, h3, h4⟩
  set W : Set (ℝ ⊗[ℤ] N) :=
    {x | ∃ c : Fin (S.card + 1) → ℝ ⊗[ℤ] N, (∀ i, c i ∈ Df i) ∧ x = ∑ i, c i} with hW
  have hWcl : IsClosed W := isClosed_sum_cones (isCone_coe D.cone) D.cone.convex D.isClosed_cone
    D.inter_neg_eq Df
    (fun i => (hDf i).1) (fun i => (hDf i).2.1) (fun i => (hDf i).2.2.2)
  obtain ⟨hWcone, hWcv, hsingle⟩ :=
    isCone_convex_sum_cones Df (fun i => (hDf i).1) (fun i => (hDf i).2.2.1)
  have hWC : W ⊆ C := fun _ ⟨c, hc, h⟩ => h ▸ D.cone.sum_mem fun i _ => (hDf i).2.2.2 (hc i)
  have hCgeW : Cge ⊆ W := fun w hw => hsingle 0 (by simpa [Df] using hw)
  have key : C ⊆ W := cone_subset_of_forall_mem_negativeRationalRays D hWcone hWcv hWcl hWC
    (fun z hzC hK => hCgeW ⟨hzC, add_nonneg hK
      (mul_nonneg hε.le (forall_mem_nonneg_of_forall_ne_zero_pos hG z hzC))⟩) fun R hR => by
      obtain ⟨-, -, -, hRC, ξ, hξR, hξ0⟩ := isCone_isClosed_convex_of_mem_negativeRationalRays D hR
      by_cases hT' : ∀ z ∈ R, z ≠ 0 → K z + ε * G z < 0
      · have hRS := (hSmem _).2 ⟨hR, hT'⟩
        exact ⟨ξ, hξR, hξ0, hsingle (e.symm ⟨R, hRS⟩).succ (by simpa [Df] using hξR)⟩
      · push Not at hT'
        obtain ⟨z, hzR, hz0, hz⟩ := hT'
        exact ⟨z, hzR, hz0, hCgeW ⟨hRC hzR, hz⟩⟩
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨c, hc, rfl⟩ := key hx
    have hc0 : c 0 ∈ Cge := by simpa [Df] using hc 0
    obtain ⟨r, hr, hsum⟩ := exists_sum_eq_add_sum_of_mem S c fun i => by simpa [Df] using hc i.succ
    exact ⟨c 0, hc0.1, hc0.2, r, hr, hsum⟩
  rintro _ ⟨c, hc, -, r, hr, rfl⟩
  exact D.cone.add_mem hc (D.cone.sum_mem fun R hR =>
    (isCone_isClosed_convex_of_mem_negativeRationalRays D ((hSmem R).1 hR).1).2.2.2.1 (hr R hR))

end ConeDatum

end MMP.Positivity
