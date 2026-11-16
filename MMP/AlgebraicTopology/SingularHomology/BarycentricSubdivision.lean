module

public import MMP.AlgebraicTopology.Triangulation.StdSimplicialComplex
public import Mathlib.Data.Fintype.Powerset

/-!
# Barycentric subdivision of a standard simplex

The *barycentric subdivision* of an abstract simplicial complex `Δ` on a finite type `ν` has as
vertices the faces of `Δ` and as simplices the nonempty chains of faces. Its realization in
`ℝ^{Finset ν}` maps to the realization of `Δ` in `ℝ^ν` by the linear map `baryMap`, sending the
vertex `τ` to the barycentre `|τ|⁻¹ ∑_{v ∈ τ} eᵥ` of `τ`.

The main result is that this map is a bijection from the weight vectors on `Finset ν` supported
on a chain of nonempty sets onto the weight vectors on `ν`: every nonnegative `x : ν → ℝ` is
`baryMap y` for a unique nonnegative `y` supported on a chain of nonempty sets
(`MMP.exists_baryMap_eq`, `MMP.baryMap_injOn`). The largest member
of the chain is the support of `x` (`MMP.support_baryMap`): a point of the open
simplex of a chain is mapped into the open simplex of its largest member.

## Main definitions

* `MMP.baryMap`: the linear map `ℝ^{Finset ν} → ℝ^ν`, `δ_τ ↦ |τ|⁻¹ 1_τ`.
* `MMP.IsChainSupported`: `y` is nonnegative and supported on a chain of nonempty
  sets.

## Main results

* `MMP.exists_baryMap_eq`: surjectivity onto nonnegative vectors.
* `MMP.baryMap_injOn`: injectivity on chain-supported vectors.
* `MMP.support_baryMap`: the support of the image is the top of the chain.
-/

@[expose] public section

open Set

namespace MMP

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The realization of the barycentric subdivision: `δ_τ ↦ |τ|⁻¹ 1_τ`, the barycentre of `τ`. -/
noncomputable def baryMap : (Finset ν → ℝ) →ₗ[ℝ] (ν → ℝ) where
  toFun y v := ∑ τ, y τ * if v ∈ τ then ((τ.card : ℝ))⁻¹ else 0
  map_add' y z := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, RingHom.id_apply]

/-- The coordinate `v` of `baryMap y` is `∑_τ y τ · |τ|⁻¹ 1_τ(v)`. -/
theorem baryMap_apply (y : Finset ν → ℝ) (v : ν) :
    baryMap y v = ∑ τ, y τ * if v ∈ τ then ((τ.card : ℝ))⁻¹ else 0 := rfl

/-- The image of `c δ_T` under `baryMap` is `c |T|⁻¹ 1_T`. -/
theorem baryMap_single (T : Finset ν) (c : ℝ) (v : ν) :
    baryMap (Pi.single T c) v = if v ∈ T then c * ((T.card : ℝ))⁻¹ else 0 := by
  rw [baryMap_apply, Finset.sum_eq_single T (fun τ _ hτ ↦ by simp [hτ])
    (fun h ↦ absurd (Finset.mem_univ T) h)]
  simp only [Pi.single_eq_same, mul_ite, mul_zero]

/-- `y` is nonnegative and supported on a chain of nonempty sets. -/
def IsChainSupported (y : Finset ν → ℝ) : Prop :=
  (∀ τ, 0 ≤ y τ) ∧ (∀ τ, y τ ≠ 0 → τ.Nonempty) ∧ IsChain (· ⊆ ·) {τ | y τ ≠ 0}

/-- `baryMap` maps nonnegative vectors to nonnegative vectors. -/
theorem baryMap_nonneg {y : Finset ν → ℝ} (hy : ∀ τ, 0 ≤ y τ) (v : ν) : 0 ≤ baryMap y v :=
  Finset.sum_nonneg fun τ _ ↦ mul_nonneg (hy τ) (by split_ifs <;> positivity)

/-- The total mass is preserved on vectors supported on nonempty sets. -/
theorem sum_baryMap {y : Finset ν → ℝ} (hy : ∀ τ, y τ ≠ 0 → τ.Nonempty) :
    ∑ v, baryMap y v = ∑ τ, y τ := by
  simp only [baryMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  by_cases h : y τ = 0
  · simp [h]
  · have hc : (0 : ℝ) < τ.card := by exact_mod_cast (hy τ h).card_pos
    rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_inv_cancel₀ hc.ne', mul_one]

omit [Fintype ν] [DecidableEq ν] in
/-- A finite nonempty chain of finite sets has a greatest element. -/
theorem exists_greatest_of_isChain {c : Finset (Finset ν)}
    (hc : IsChain (· ⊆ ·) (↑c : Set (Finset ν))) (hne : c.Nonempty) :
    ∃ M ∈ c, ∀ τ ∈ c, τ ⊆ M := by
  obtain ⟨M, hM, hmax⟩ := c.exists_max_image Finset.card hne
  refine ⟨M, hM, fun τ hτ ↦ ?_⟩
  rcases eq_or_ne τ M with rfl | hne'
  · exact subset_rfl
  rcases hc hτ hM hne' with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h (hmax τ hτ)) ▸ subset_rfl

/-- **The top of the chain.** For `y` chain-supported and nonzero, the support of `baryMap y` is
the largest member `M` of the chain, and the minimum of `baryMap y` on `M` is `y M / |M|`,
attained at a point of `M` lying in no other member of the chain. -/
theorem exists_top_of_isChainSupported {y : Finset ν → ℝ} (hy : IsChainSupported y)
    (h0 : ∃ τ, y τ ≠ 0) :
    ∃ M, y M ≠ 0 ∧ (∀ τ, y τ ≠ 0 → τ ⊆ M) ∧ (∀ v, baryMap y v ≠ 0 ↔ v ∈ M) ∧
      (∀ v ∈ M, y M * ((M.card : ℝ))⁻¹ ≤ baryMap y v) ∧
      ∃ v ∈ M, baryMap y v = y M * ((M.card : ℝ))⁻¹ := by
  classical
  obtain ⟨hy0, hyne, hyc⟩ := hy
  set c : Finset (Finset ν) := Finset.univ.filter (y · ≠ 0)
  have hcc : IsChain (· ⊆ ·) (c : Set (Finset ν)) := by
    convert hyc using 1
    ext τ
    simp [c]
  obtain ⟨τ₀, hτ₀⟩ := h0
  obtain ⟨M, hMc, hMmax⟩ := exists_greatest_of_isChain hcc ⟨τ₀, by simp [c, hτ₀]⟩
  have hMy : y M ≠ 0 := by simpa [c] using hMc
  have hmax : ∀ τ, y τ ≠ 0 → τ ⊆ M := fun τ hτ ↦ hMmax τ (by simp [c, hτ])
  have hMne := hyne M hMy
  have hMpos : 0 < y M := lt_of_le_of_ne (hy0 M) (Ne.symm hMy)
  have hterm : ∀ v τ, 0 ≤ y τ * if v ∈ τ then ((τ.card : ℝ))⁻¹ else 0 := fun v τ ↦
    mul_nonneg (hy0 τ) (by split_ifs <;> positivity)
  have hlow : ∀ v ∈ M, y M * ((M.card : ℝ))⁻¹ ≤ baryMap y v := fun v hv ↦ by
    rw [baryMap_apply]
    simpa [hv] using Finset.single_le_sum (fun τ _ ↦ hterm v τ) (Finset.mem_univ M)
  refine ⟨M, hMy, hmax, fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩, hlow, ?_⟩
  · by_contra hvM
    refine hv (Finset.sum_eq_zero fun τ _ ↦ ?_)
    by_cases hτ : y τ = 0
    · simp [hτ]
    · simp [show v ∉ τ from fun h ↦ hvM (hmax τ hτ h)]
  · have hc : (0 : ℝ) < M.card := by exact_mod_cast hMne.card_pos
    exact (lt_of_lt_of_le (by positivity) (hlow v hv)).ne'
  · obtain ⟨v, hvM, hv⟩ : ∃ v ∈ M, ∀ τ, y τ ≠ 0 → τ ≠ M → v ∉ τ := by
      by_contra hcon
      push Not at hcon
      rcases (c.erase M).eq_empty_or_nonempty with he | hne'
      · obtain ⟨v, hv⟩ := hMne
        obtain ⟨τ, hτ, hτM, -⟩ := hcon v hv
        simpa [he] using Finset.mem_erase.2 ⟨hτM, show τ ∈ c by simp [c, hτ]⟩
      · obtain ⟨M₁, hM₁, hM₁max⟩ := exists_greatest_of_isChain
          (hcc.mono (Finset.coe_subset.2 (Finset.erase_subset _ _))) hne'
        refine Finset.ne_of_mem_erase hM₁ ((hMmax M₁ (Finset.mem_of_mem_erase hM₁)).antisymm
          fun v hv ↦ ?_)
        obtain ⟨τ, hτ, hτM, hvτ⟩ := hcon v hv
        exact hM₁max τ (Finset.mem_erase.2 ⟨hτM, by simp [c, hτ]⟩) hvτ
    refine ⟨v, hvM, ?_⟩
    rw [baryMap_apply, Finset.sum_eq_single M (fun τ _ hτM ↦ ?_) (fun h ↦ absurd
      (Finset.mem_univ M) h), ite_eq_left_of_eq_true _ _ (eq_true hvM)]
    by_cases hτ : y τ = 0
    · simp [hτ]
    · simp [hv τ hτ hτM]

omit [Fintype ν] in
/-- Adding a nonnegative multiple of `δ_T`, for a nonempty `T` containing every member of the
chain, keeps a vector chain-supported. -/
theorem IsChainSupported.add_single {y : Finset ν → ℝ} (hy : IsChainSupported y) {T : Finset ν}
    (hT : T.Nonempty) {c : ℝ} (hc : 0 ≤ c) (hsub : ∀ τ, y τ ≠ 0 → τ ⊆ T) :
    IsChainSupported (y + Pi.single T c) := by
  have hTy : ∀ τ, (y + Pi.single T c : Finset ν → ℝ) τ ≠ 0 → τ = T ∨ y τ ≠ 0 := fun τ h ↦ by
    by_cases hτ : τ = T
    · exact Or.inl hτ
    · exact Or.inr (by simpa [Pi.single_apply, hτ] using h)
  refine ⟨fun τ ↦ ?_, fun τ hτ ↦ ?_, ?_⟩
  · rw [Pi.add_apply, Pi.single_apply]
    exact add_nonneg (hy.1 τ) (by split_ifs; exacts [hc, le_rfl])
  · rcases hTy τ hτ with rfl | h
    exacts [hT, hy.2.1 τ h]
  · refine (hy.2.2.insert fun b hb _ ↦ Or.inr (hsub b hb)).mono fun τ hτ ↦ ?_
    rcases hTy τ hτ with rfl | h
    exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ h]

/-- **Barycentric coordinates exist.** Every nonnegative `x : ν → ℝ` is `baryMap y` for a
chain-supported `y` whose members lie in the support of `x`. -/
theorem exists_baryMap_eq (x : ν → ℝ) (hx : ∀ v, 0 ≤ x v) :
    ∃ y, IsChainSupported y ∧ (∀ τ, y τ ≠ 0 → ∀ v ∈ τ, x v ≠ 0) ∧ baryMap y = x := by
  classical
  induction hn : (Finset.univ.filter (x · ≠ 0)).card using Nat.strong_induction_on generalizing x
    with
  | _ n IH =>
  set T := Finset.univ.filter (x · ≠ 0)
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · have hx0 : x = 0 := by
      funext v
      by_contra h
      have h' : x v ≠ 0 := h
      have : v ∈ T := by simp [T, h']
      simp [hTe] at this
    refine ⟨0, ⟨fun _ ↦ le_rfl, fun τ h ↦ absurd rfl h, ?_⟩, fun τ h ↦ absurd rfl h, ?_⟩
    · simp only [Pi.zero_apply, ne_eq, not_true_eq_false, Set.ofPred_false]
      intro a ha
      simp at ha
    · rw [hx0, map_zero]
  set m := T.inf' hTne x with hm
  have hmT : ∀ v ∈ T, m ≤ x v := fun v hv ↦ Finset.inf'_le _ hv
  obtain ⟨v₀, hv₀T, hv₀⟩ := Finset.exists_mem_eq_inf' hTne x
  have hxT : ∀ v, v ∈ T ↔ x v ≠ 0 := fun v ↦ by simp [T]
  have hmpos : 0 < m := by
    rw [hm, hv₀]
    exact lt_of_le_of_ne (hx v₀) (Ne.symm ((hxT v₀).1 hv₀T))
  set x' : ν → ℝ := fun v ↦ if v ∈ T then x v - m else 0
  have hx'0 : ∀ v, 0 ≤ x' v := fun v ↦ by
    simp only [x']
    split_ifs with h
    exacts [sub_nonneg.2 (hmT v h), le_rfl]
  have hx'T : ∀ v, x' v ≠ 0 → v ∈ T := fun v h ↦ by
    by_contra hv
    simp [x', hv] at h
  have hx'v₀ : x' v₀ = 0 := by
    simp only [x', hv₀T, ite_true]
    rw [hm, hv₀, sub_self]
  have hcard : (Finset.univ.filter (x' · ≠ 0)).card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨fun v hv ↦ hx'T v (Finset.mem_filter.1 hv).2,
      fun hsub ↦ (Finset.mem_filter.1 (hsub hv₀T)).2 hx'v₀⟩
  obtain ⟨y', hy', hy'x, hy'eq⟩ := IH _ hcard x' hx'0 rfl
  have hy'T : ∀ τ, y' τ ≠ 0 → τ ⊆ T := fun τ hτ v hv ↦ hx'T v (hy'x τ hτ v hv)
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  refine ⟨y' + Pi.single T (m * T.card), hy'.add_single hTne (mul_pos hmpos hc).le hy'T,
    fun τ hτ v hv ↦ (hxT v).1 ?_, ?_⟩
  · by_cases hτT : τ = T
    · exact hτT ▸ hv
    · exact hy'T τ (by simpa [Pi.single_apply, hτT] using hτ) hv
  · funext v
    rw [map_add, Pi.add_apply, hy'eq, baryMap_single]
    simp only [x']
    split_ifs with h
    · rw [mul_assoc, mul_inv_cancel₀ hc.ne', mul_one, sub_add_cancel]
    · rw [add_zero]
      by_contra h'
      exact h ((hxT v).2 (Ne.symm h'))

/-- A chain-supported vector with zero image under `baryMap` is zero. -/
theorem eq_zero_of_baryMap_eq_zero {w : Finset ν → ℝ} (hw : IsChainSupported w)
    (h : baryMap w = 0) : w = 0 := by
  by_contra hne
  obtain ⟨M, hMy, -, hMs, -⟩ := exists_top_of_isChainSupported hw (Function.ne_iff.1 hne)
  obtain ⟨v, hv⟩ := hw.2.1 M hMy
  exact (hMs v).2 hv (by rw [h, Pi.zero_apply])

omit [Fintype ν] in
/-- Zeroing the coordinate `M` keeps a vector chain-supported. -/
theorem IsChainSupported.ite_eq_zero {w : Finset ν → ℝ} (hw : IsChainSupported w)
    (M : Finset ν) : IsChainSupported (fun τ ↦ if τ = M then 0 else w τ) := by
  refine ⟨fun τ ↦ ?_, fun τ hτ ↦ ?_, hw.2.2.mono fun τ hτ ↦ ?_⟩
  · dsimp only
    split_ifs
    exacts [le_rfl, hw.1 τ]
  · dsimp only at hτ
    split_ifs at hτ
    exacts [absurd rfl hτ, hw.2.1 τ hτ]
  · simp only [Set.mem_ofPred_eq] at hτ ⊢
    split_ifs at hτ
    exacts [absurd rfl hτ, hτ]

/-- **Barycentric coordinates are unique.** `baryMap` is injective on chain-supported vectors. -/
theorem baryMap_injOn {y y' : Finset ν → ℝ} (hy : IsChainSupported y) (hy' : IsChainSupported y')
    (h : baryMap y = baryMap y') : y = y' := by
  classical
  induction hn : (Finset.univ.filter (baryMap y · ≠ 0)).card using Nat.strong_induction_on
    generalizing y y' with
  | _ n IH =>
  by_cases h0 : ∃ τ, y τ ≠ 0
  · have h0' : ∃ τ, y' τ ≠ 0 := Function.ne_iff.1 fun (hy'0 : y' = 0) ↦ h0.elim fun τ hτ ↦
      hτ <| congrFun (eq_zero_of_baryMap_eq_zero hy (by rw [h, hy'0, map_zero])) τ
    obtain ⟨M, hMy, -, hMs, hMlow, v₀, hv₀M, hv₀⟩ := exists_top_of_isChainSupported hy h0
    obtain ⟨M', -, -, hM's, hM'low, v₁, hv₁M, hv₁⟩ := exists_top_of_isChainSupported hy' h0'
    have hMM : M = M' := by
      ext v
      rw [← hMs, ← hM's, h]
    subst hMM
    have hc : (0 : ℝ) < M.card := by exact_mod_cast (hy.2.1 M hMy).card_pos
    have hyM : y M = y' M := mul_right_cancel₀ (inv_ne_zero hc.ne') <| le_antisymm
      (by rw [← hv₁, ← h]; exact hMlow v₁ hv₁M) (by rw [← hv₀, h]; exact hM'low v₀ hv₀M)
    have hz : ∀ w : Finset ν → ℝ, w - Pi.single M (w M) = fun τ ↦ if τ = M then 0 else w τ :=
      fun w ↦ funext fun τ ↦ by by_cases hτ : τ = M <;> simp [hτ]
    have hbz : baryMap (y - Pi.single M (y M)) = baryMap (y' - Pi.single M (y' M)) := by
      rw [map_sub, map_sub, h, hyM]
    have hcard : (Finset.univ.filter (baryMap (y - Pi.single M (y M)) · ≠ 0)).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun v hv ↦ ?_, fun hsub ↦ ?_⟩
      · have hv' := (Finset.mem_filter.1 hv).2
        rw [map_sub, Pi.sub_apply, baryMap_single] at hv'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hMs]
        by_contra hvM
        rw [ite_eq_right_of_eq_false _ _ (eq_false hvM), sub_zero, ne_eq, ← ne_eq, hMs] at hv'
        exact hvM hv'
      · have := (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨Finset.mem_univ v₀,
          (hMs v₀).2 hv₀M⟩))).2
        rw [map_sub, Pi.sub_apply, baryMap_single, ite_eq_left_of_eq_true _ _ (eq_true hv₀M), hv₀,
          sub_self] at this
        exact this rfl
    have := IH _ hcard (by rw [hz]; exact hy.ite_eq_zero M) (by rw [hz]; exact hy'.ite_eq_zero M)
      hbz rfl
    calc y = y - Pi.single M (y M) + Pi.single M (y M) := (sub_add_cancel _ _).symm
      _ = y' - Pi.single M (y' M) + Pi.single M (y' M) := by rw [this, hyM]
      _ = y' := sub_add_cancel _ _
  · push Not at h0
    have hy0 : y = 0 := funext h0
    exact hy0.trans (eq_zero_of_baryMap_eq_zero hy' (by rw [← h, hy0, map_zero])).symm

/-- The support of `baryMap y`, for `y` chain-supported, is the top of the chain. -/
theorem support_baryMap {y : Finset ν → ℝ} (hy : IsChainSupported y) {M : Finset ν}
    (hM : y M ≠ 0) (hmax : ∀ τ, y τ ≠ 0 → τ ⊆ M) (v : ν) : baryMap y v ≠ 0 ↔ v ∈ M := by
  obtain ⟨M', hM'y, hM'max, hM's, -⟩ := exists_top_of_isChainSupported hy ⟨M, hM⟩
  have : M = M' := (hM'max M hM).antisymm (hmax M' hM'y)
  rw [this, hM's]

end MMP
