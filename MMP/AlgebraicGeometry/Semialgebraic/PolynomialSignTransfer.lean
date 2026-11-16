module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Sign patterns of real polynomials up to order automorphisms of `ℝ`

Two families `f, g : ι → ℝ[X]` have the same *sign pattern* if some order automorphism `ψ` of
`ℝ` satisfies `sign (f i (x)) = sign (g i (ψ x))` for all `i` and `x`. This is the invariant
behind Hörmander's proof of the Tarski–Seidenberg theorem: the sign pattern of a family
containing a non-constant `p` is determined by the sign pattern of the family obtained by
replacing `p` with its derivative `p'` and with polynomials agreeing in sign with `p` on the
zeros of the other members and of `p'` (in practice, pseudo-remainders of `p`).

## Main definitions

* `MMP.SameSignPattern`: the relation above.

## Main results

* `MMP.exists_orderIso_eqOn_of_strictMonoOn`: a strictly monotone map on a finite
  subset of `ℝ` extends to an order automorphism of `ℝ`.
* `MMP.sameSignPattern_of_derivative`: Hörmander's transfer lemma.
* `MMP.SameSignPattern.exists_iff`: families with the same sign pattern realise
  the same sign conditions.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §1.4.
* [L. Hörmander, *The analysis of linear partial differential operators II*][hormander1983],
  Appendix A.2.
-/

@[expose] public section

open Polynomial Set Filter

namespace MMP

/-! ### Extending finite order embeddings of `ℝ` -/

/-- An order automorphism of `ℝ` fixing `(-∞, c]` and sending `u > c` to `v > c`. -/
theorem exists_orderIso_fix_le_of_lt {c u v : ℝ} (hu : c < u) (hv : c < v) :
    ∃ θ : ℝ ≃o ℝ, (∀ x ≤ c, θ x = x) ∧ θ u = v := by
  set k := (v - c) / (u - c) with hk
  have hk0 : 0 < k := div_pos (sub_pos.2 hv) (sub_pos.2 hu)
  let F : ℝ → ℝ := fun x ↦ if x ≤ c then x else c + k * (x - c)
  have hF : StrictMono F := by
    intro x y hxy
    simp only [F]
    split_ifs with h1 h2 h2
    · exact hxy
    · nlinarith
    · exact absurd (h2.trans' hxy.le) h1
    · nlinarith
  have hFs : Function.Surjective F := by
    intro y
    by_cases hy : y ≤ c
    · exact ⟨y, by simp [F, hy]⟩
    · refine ⟨c + (y - c) / k, ?_⟩
      have : ¬ c + (y - c) / k ≤ c := by
        have : 0 < (y - c) / k := div_pos (by linarith) hk0
        linarith
      simp only [F, this, ↓reduceIte]
      field_simp
      ring
  refine ⟨hF.orderIsoOfSurjective F hFs, fun x hx ↦ by simp [F, hx], ?_⟩
  simp only [StrictMono.coe_orderIsoOfSurjective, F, not_le.2 hu, ↓reduceIte, hk]
  field_simp [(sub_pos.2 hu).ne']
  ring

/-- **Finite order embeddings of `ℝ` extend.** A strictly monotone map on a finite subset of
`ℝ` agrees there with an order automorphism of `ℝ`. -/
theorem exists_orderIso_eqOn_of_strictMonoOn {A : Finset ℝ} {χ : ℝ → ℝ}
    (hχ : StrictMonoOn χ A) : ∃ ψ : ℝ ≃o ℝ, ∀ x ∈ A, ψ x = χ x := by
  classical
  induction A using Finset.induction_on_max with
  | empty => exact ⟨OrderIso.refl ℝ, by simp⟩
  | insert a s hlt ih =>
    obtain ⟨ψ', hψ'⟩ := ih (hχ.mono (by simp))
    rcases s.eq_empty_or_nonempty with rfl | hs
    · refine ⟨ψ'.trans (OrderIso.addRight (χ a - ψ' a)), ?_⟩
      simp
    · set m := s.max' hs
      have hm : m ∈ s := s.max'_mem hs
      have hma : m < a := hlt m hm
      obtain ⟨θ, hθc, hθu⟩ := exists_orderIso_fix_le_of_lt (c := χ m) (u := ψ' a) (v := χ a)
        (by rw [← hψ' m hm]; exact ψ'.strictMono hma)
        (hχ (by simp [hm]) (by simp) hma)
      refine ⟨ψ'.trans θ, fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simpa using hθu
      · have hxm : x ≤ m := s.le_max' x hx
        simp only [OrderIso.trans_apply, hψ' x hx]
        apply hθc
        rcases hxm.lt_or_eq with h | h
        · exact (hχ (by simp [hx]) (by simp [hm]) h).le
        · rw [h]

/-! ### Elementary facts on real polynomials -/

/-- A real polynomial without zeros on `[[a, b]]` has the same sign at `a` and `b`. -/
theorem sign_eval_eq_of_forall_ne_zero (p : ℝ[X]) {a b : ℝ}
    (h : ∀ x ∈ uIcc a b, p.eval x ≠ 0) : SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  have hab := intermediate_value_uIcc (a := a) (b := b) p.continuous.continuousOn
  have ha := h a left_mem_uIcc
  have hb := h b right_mem_uIcc
  by_contra hne
  have h0 : (0 : ℝ) ∈ uIcc (p.eval a) (p.eval b) := by
    rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
    · exact absurd (by rw [sign_neg ha', sign_neg hb']) hne
    · exact mem_uIcc.2 (Or.inl ⟨ha'.le, hb'.le⟩)
    · exact mem_uIcc.2 (Or.inr ⟨hb'.le, ha'.le⟩)
    · exact absurd (by rw [sign_pos ha', sign_pos hb']) hne
  obtain ⟨x, hx, hx0⟩ := hab h0
  exact h x hx hx0

/-- If a real polynomial takes different signs at `a` and `b`, it has a zero on `[[a, b]]`. -/
theorem exists_mem_uIcc_eval_eq_zero (p : ℝ[X]) {a b : ℝ}
    (h : SignType.sign (p.eval a) ≠ SignType.sign (p.eval b)) :
    ∃ x ∈ uIcc a b, p.eval x = 0 := by
  by_contra! h'
  exact h (sign_eval_eq_of_forall_ne_zero p h')

/-- Mean value theorem for real polynomials. -/
theorem exists_eval_sub_eq_derivative_mul (p : ℝ[X]) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_slope (fun x ↦ p.eval x)
    (fun x ↦ p.derivative.eval x) hab p.continuous.continuousOn
    (fun x _ ↦ p.hasDerivAt x)
  refine ⟨c, hc, ?_⟩
  rw [h]
  field_simp [(sub_pos.2 hab).ne']

/-- For large `x`, a real polynomial has the sign of its leading coefficient. -/
theorem eventually_sign_eval_eq_sign_leadingCoeff (p : ℝ[X]) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · rw [p.eq_C_of_natDegree_eq_zero h]
    simp
  · have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.1 h
    have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt h)
    rcases hlc.lt_or_gt with hlc | hlc
    · filter_upwards [(p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc.le).eventually_lt_atBot 0]
        with x hx
      rw [sign_neg hx, sign_neg hlc]
    · filter_upwards [(p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le).eventually_gt_atTop 0]
        with x hx
      rw [sign_pos hx, sign_pos hlc]

/-- For large `x`, a non-constant real polynomial and its derivative have the same sign. -/
theorem eventually_sign_eval_eq_sign_eval_derivative {p : ℝ[X]} (hp : 0 < p.natDegree) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign (p.derivative.eval x) := by
  filter_upwards [eventually_sign_eval_eq_sign_leadingCoeff p,
    eventually_sign_eval_eq_sign_leadingCoeff p.derivative] with x h1 h2
  rw [h1, h2, leadingCoeff_derivative, sign_mul,
    sign_pos (by exact_mod_cast hp : (0 : ℝ) < p.natDegree), mul_one]

/-- For `x → -∞`, a non-constant real polynomial and its derivative have opposite signs. -/
theorem eventually_sign_eval_eq_neg_sign_eval_derivative {p : ℝ[X]} (hp : 0 < p.natDegree) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) = -SignType.sign (p.derivative.eval x) := by
  have hdeg : 0 < (p.comp (-X)).natDegree := by
    rwa [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  filter_upwards [tendsto_neg_atBot_atTop.eventually
    (eventually_sign_eval_eq_sign_eval_derivative hdeg)] with x hx
  simp only [eval_comp, eval_neg, eval_X, neg_neg, derivative_comp, derivative_neg,
    derivative_X, neg_one_mul] at hx
  rw [hx, Left.sign_neg]

/-! ### Gaps of a finite subset of `ℝ` -/

/-- If no point of the finite set `W` separates `a` and `b`, none lies between them. -/
theorem notMem_uIcc_of_forall_lt_iff {W : Finset ℝ} {a b : ℝ} (ha : a ∉ W) (hb : b ∉ W)
    (h : ∀ w ∈ W, w < a ↔ w < b) : ∀ w ∈ W, w ∉ uIcc a b := by
  intro w hw hwab
  have hwa : w ≠ a := fun e ↦ ha (e ▸ hw)
  have hwb : w ≠ b := fun e ↦ hb (e ▸ hw)
  rcases mem_uIcc.1 hwab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd ((h w hw).2 (lt_of_le_of_ne h2 hwb)) (not_lt.2 h1)
  · exact absurd ((h w hw).1 (lt_of_le_of_ne h2 hwa)) (not_lt.2 h1)

/-- A real polynomial whose zeros lie in `W` has constant sign between points not separated
by `W`. -/
theorem sign_eval_eq_of_zeros_subset (h : ℝ[X]) {W : Finset ℝ} {a b : ℝ}
    (hW : ∀ x, h.eval x = 0 → x ∈ W) (hab : ∀ w ∈ W, w ∉ uIcc a b) :
    SignType.sign (h.eval a) = SignType.sign (h.eval b) :=
  sign_eval_eq_of_forall_ne_zero h fun x hx h0 ↦ hab x (hW x h0) hx

/-- **Rolle.** Between two zeros of a real polynomial lies a zero of its derivative. -/
theorem exists_mem_Ioo_of_eval_eq_zero (p : ℝ[X]) {W : Finset ℝ}
    (hW : ∀ x, p.derivative.eval x = 0 → x ∈ W) {a b : ℝ} (hab : a < b) (ha : p.eval a = 0)
    (hb : p.eval b = 0) : ∃ w ∈ W, w ∈ Ioo a b := by
  obtain ⟨c, hc, h⟩ := exists_eval_sub_eq_derivative_mul p hab
  rw [ha, hb, sub_zero, eq_comm, mul_eq_zero] at h
  exact ⟨c, hW c (h.resolve_right (sub_pos.2 hab).ne'), hc⟩

/-- Two zeros of a real polynomial not separated by a finite set containing the zeros of its
derivative coincide. -/
theorem eq_of_eval_eq_zero_of_forall_lt_iff (q : ℝ[X]) {W : Finset ℝ}
    (hW : ∀ y, q.derivative.eval y = 0 → y ∈ W) {a b : ℝ} (ha : q.eval a = 0) (hb : q.eval b = 0)
    (h : ∀ w ∈ W, w < a ↔ w < b) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hab
  · obtain ⟨w, hw, hw1, hw2⟩ := exists_mem_Ioo_of_eval_eq_zero q hW hab ha hb
    exact absurd ((h w hw).2 hw2) (not_lt.2 hw1.le)
  · obtain ⟨w, hw, hw1, hw2⟩ := exists_mem_Ioo_of_eval_eq_zero q hW hab hb ha
    exact absurd ((h w hw).1 hw2) (not_lt.2 hw1.le)

/-- A finite set with a point above `x` has a least point above `x`. -/
theorem exists_min_of_exists_gt {W : Finset ℝ} {x : ℝ} (h : ∃ z ∈ W, x < z) :
    ∃ zR ∈ W, x < zR ∧ ∀ z ∈ W, x < z → zR ≤ z := by
  classical
  obtain ⟨z, hz, hxz⟩ := h
  have hS : (W.filter (x < ·)).Nonempty := ⟨z, Finset.mem_filter.2 ⟨hz, hxz⟩⟩
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 ((W.filter (x < ·)).min'_mem hS)
  exact ⟨_, h₁, h₂, fun z hz hxz ↦
    (W.filter (x < ·)).min'_le z (Finset.mem_filter.2 ⟨hz, hxz⟩)⟩

/-- A finite set with a point below `x` has a greatest point below `x`. -/
theorem exists_max_of_exists_lt {W : Finset ℝ} {x : ℝ} (h : ∃ z ∈ W, z < x) :
    ∃ zL ∈ W, zL < x ∧ ∀ z ∈ W, z < x → z ≤ zL := by
  classical
  obtain ⟨z, hz, hzx⟩ := h
  have hS : (W.filter (· < x)).Nonempty := ⟨z, Finset.mem_filter.2 ⟨hz, hzx⟩⟩
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 ((W.filter (· < x)).max'_mem hS)
  exact ⟨_, h₁, h₂, fun z hz hzx ↦
    (W.filter (· < x)).le_max' z (Finset.mem_filter.2 ⟨hz, hzx⟩)⟩

/-- A real polynomial with no zero off `W` in the gap of `x ∉ W` has the same sign at `x` and at
the least point `b` of `W` above `x`, provided it vanishes at neither. -/
theorem sign_eval_eq_of_minimal_gt (r : ℝ[X]) {W : Finset ℝ} {x b : ℝ} (hxW : x ∉ W)
    (hxb : x < b) (hb : ∀ w ∈ W, x < w → b ≤ w) (hrx : r.eval x ≠ 0) (hrb : r.eval b ≠ 0)
    (hno : ∀ w, r.eval w = 0 → w ∉ W → ¬ ∀ z ∈ W, (z < w ↔ z < x)) :
    SignType.sign (r.eval x) = SignType.sign (r.eval b) :=
  sign_eval_eq_of_forall_ne_zero r fun w hw hw0 ↦ by
    have hw' : x ≤ w ∧ w ≤ b := by
      rcases mem_uIcc.1 hw with h | h
      · exact h
      · exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
    have hwx : w ≠ x := fun e ↦ hrx (e ▸ hw0)
    have hwb : w ≠ b := fun e ↦ hrb (e ▸ hw0)
    by_cases hwW : w ∈ W
    · exact hwb (le_antisymm hw'.2 (hb w hwW (lt_of_le_of_ne hw'.1 hwx.symm)))
    · refine hno w hw0 hwW fun z hz ↦ ⟨fun h ↦ ?_, fun h ↦ h.trans_le hw'.1⟩
      have hzx : z ≠ x := fun e ↦ hxW (e ▸ hz)
      rcases hzx.lt_or_gt with h' | h'
      · exact h'
      · exact absurd (h.trans_le (hw'.2.trans (hb z hz h'))) (lt_irrefl _)

/-! ### Hörmander's transfer lemma -/

/-- The hypotheses of the root-transfer step: `φ` matches the finite sets `Z ⊇ {p' = 0}` and
`φ(Z) ⊇ {q' = 0}`, the signs of `p, q` on them, and the signs of `p', q'` everywhere. -/
structure SignTransferData (Z : Finset ℝ) (φ : ℝ ≃o ℝ) (p q : ℝ[X]) : Prop where
  natDegree_left : 0 < p.natDegree
  natDegree_right : 0 < q.natDegree
  mem_of_derivative_left : ∀ x, p.derivative.eval x = 0 → x ∈ Z
  mem_of_derivative_right : ∀ y, q.derivative.eval y = 0 → φ.symm y ∈ Z
  sign_eval : ∀ z ∈ Z, SignType.sign (p.eval z) = SignType.sign (q.eval (φ z))
  sign_derivative : ∀ x, SignType.sign (p.derivative.eval x) =
    SignType.sign (q.derivative.eval (φ x))

namespace SignTransferData

variable {Z : Finset ℝ} {φ : ℝ ≃o ℝ} {p q : ℝ[X]}

/-- The data are symmetric: `φ⁻¹` transfers `q` on `φ(Z)` back to `p`. -/
theorem symm (D : SignTransferData Z φ p q) : SignTransferData (Z.image φ) φ.symm q p where
  natDegree_left := D.natDegree_right
  natDegree_right := D.natDegree_left
  mem_of_derivative_left y hy := Finset.mem_image.2 ⟨φ.symm y, D.mem_of_derivative_right y hy,
    by simp⟩
  mem_of_derivative_right x hx := by simpa using D.mem_of_derivative_left x hx
  sign_eval w hw := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    simp [D.sign_eval z hz]
  sign_derivative y := by simpa using (D.sign_derivative (φ.symm y)).symm

/-- A point lies in `φ(Z)` if and only if its preimage under `φ` lies in `Z`. -/
theorem mem_image_iff (y : ℝ) : y ∈ Z.image φ ↔ φ.symm y ∈ Z := by
  constructor
  · rintro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 h
    simpa using hz
  · intro h
    exact Finset.mem_image.2 ⟨_, h, by simp⟩

/-- To the right of a zero `x ∉ Z` of `p`, the sign of `p'` at `x` is taken by `q` at a point
above the image of the gap of `x`. -/
theorem exists_sign_eval_right (D : SignTransferData Z φ p q) {x : ℝ} (hxZ : x ∉ Z)
    (hx : p.eval x = 0) :
    ∃ yR, SignType.sign (q.eval yR) = SignType.sign (p.derivative.eval x) ∧
      (∀ z ∈ Z, z < x → φ z < yR) ∧ ∀ z ∈ Z, x < z → yR ≤ φ z := by
  have hne : ∀ z ∈ Z, z ≠ x := fun z hz e ↦ hxZ (e ▸ hz)
  by_cases hR : ∃ z ∈ Z, x < z
  · obtain ⟨zR, hzR, hxzR, hzRmin⟩ := exists_min_of_exists_gt hR
    obtain ⟨c, ⟨hc₁, hc₂⟩, hmvt⟩ := exists_eval_sub_eq_derivative_mul p hxzR
    have hsc : SignType.sign (p.derivative.eval c) = SignType.sign (p.derivative.eval x) :=
      sign_eval_eq_of_zeros_subset _ D.mem_of_derivative_left fun z hz hzc ↦ by
        rcases mem_uIcc.1 hzc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases (hne z hz).lt_or_gt with h | h <;>
          first | linarith | linarith [hzRmin z hz h]
    refine ⟨φ zR, ?_, fun z hz hzx ↦ φ.strictMono (hzx.trans hxzR),
      fun z hz hxz ↦ φ.monotone (hzRmin z hz hxz)⟩
    rw [hx, sub_zero] at hmvt
    rw [← D.sign_eval zR hzR, hmvt, sign_mul, hsc, sign_pos (sub_pos.2 hxzR), mul_one]
  · push Not at hR
    obtain ⟨M, hM⟩ :=
      (eventually_sign_eval_eq_sign_eval_derivative D.natDegree_right).exists_forall_of_atTop
    set yR := max M (φ x) + 1
    have hyR : φ x < yR := by simp only [yR]; linarith [le_max_right M (φ x)]
    refine ⟨yR, ?_, fun z hz hzx ↦ (φ.strictMono hzx).trans hyR,
      fun z hz hxz ↦ absurd (hR z hz) (not_le.2 hxz)⟩
    rw [hM yR (by simp only [yR]; linarith [le_max_left M (φ x)]), D.sign_derivative x]
    symm
    refine sign_eval_eq_of_zeros_subset _ (W := Z.image φ) D.symm.mem_of_derivative_left ?_
    rw [Finset.forall_mem_image]
    intro z hz hzy
    have : φ z < φ x := φ.strictMono (lt_of_le_of_ne (hR z hz) (hne z hz))
    rcases mem_uIcc.1 hzy with ⟨h1, -⟩ | ⟨h1, h2⟩ <;> linarith

/-- To the left of a zero `x ∉ Z` of `p`, the opposite of the sign of `p'` at `x` is taken by
`q` at a point below the image of the gap of `x`. -/
theorem exists_sign_eval_left (D : SignTransferData Z φ p q) {x : ℝ} (hxZ : x ∉ Z)
    (hx : p.eval x = 0) :
    ∃ yL, SignType.sign (q.eval yL) = -SignType.sign (p.derivative.eval x) ∧
      (∀ z ∈ Z, z < x → φ z ≤ yL) ∧ ∀ z ∈ Z, x < z → yL < φ z := by
  have hne : ∀ z ∈ Z, z ≠ x := fun z hz e ↦ hxZ (e ▸ hz)
  by_cases hL : ∃ z ∈ Z, z < x
  · obtain ⟨zL, hzL, hzLx, hzLmax⟩ := exists_max_of_exists_lt hL
    obtain ⟨c, ⟨hc₁, hc₂⟩, hmvt⟩ := exists_eval_sub_eq_derivative_mul p hzLx
    have hsc : SignType.sign (p.derivative.eval c) = SignType.sign (p.derivative.eval x) := by
      symm
      refine sign_eval_eq_of_zeros_subset _ D.mem_of_derivative_left fun z hz hzc ↦ ?_
      rcases mem_uIcc.1 hzc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases (hne z hz).lt_or_gt with h | h <;>
        first | linarith | linarith [hzLmax z hz h]
    refine ⟨φ zL, ?_, fun z hz hzx ↦ φ.monotone (hzLmax z hz hzx),
      fun z hz hxz ↦ φ.strictMono (hzLx.trans hxz)⟩
    rw [hx, zero_sub, neg_eq_iff_eq_neg] at hmvt
    rw [← D.sign_eval zL hzL, hmvt, Left.sign_neg, sign_mul, hsc, sign_pos (sub_pos.2 hzLx),
      mul_one]
  · push Not at hL
    obtain ⟨M, hM⟩ :=
      (eventually_sign_eval_eq_neg_sign_eval_derivative D.natDegree_right).exists_forall_of_atBot
    set yL := min M (φ x) - 1
    have hyL : yL < φ x := by simp only [yL]; linarith [min_le_right M (φ x)]
    refine ⟨yL, ?_, fun z hz hzx ↦ absurd (hL z hz) (not_le.2 hzx),
      fun z hz hxz ↦ hyL.trans (φ.strictMono hxz)⟩
    rw [hM yL (by simp only [yL]; linarith [min_le_left M (φ x)]), D.sign_derivative x]
    congr 1
    refine sign_eval_eq_of_zeros_subset _ (W := Z.image φ) D.symm.mem_of_derivative_left ?_
    rw [Finset.forall_mem_image]
    intro z hz hzy
    have : φ x < φ z := φ.strictMono (lt_of_le_of_ne (hL z hz) (hne z hz).symm)
    rcases mem_uIcc.1 hzy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- **Roots transfer.** A zero of `p` off `Z` has a zero of `q` off `φ(Z)` in the corresponding
gap of `φ(Z)`. -/
theorem exists_root (D : SignTransferData Z φ p q) {x : ℝ} (hxZ : x ∉ Z) (hx : p.eval x = 0) :
    ∃ y, q.eval y = 0 ∧ φ.symm y ∉ Z ∧ ∀ z ∈ Z, (z < x ↔ φ z < y) := by
  have hne : ∀ z ∈ Z, z ≠ x := fun z hz e ↦ hxZ (e ▸ hz)
  obtain ⟨yR, hsR, hR1, hR2⟩ := D.exists_sign_eval_right hxZ hx
  obtain ⟨yL, hsL, hL1, hL2⟩ := D.exists_sign_eval_left hxZ hx
  set ε := SignType.sign (p.derivative.eval x) with hε
  have hε0 : ε ≠ 0 := sign_ne_zero.2 fun h ↦ hxZ (D.mem_of_derivative_left x h)
  have hsne : SignType.sign (q.eval yL) ≠ SignType.sign (q.eval yR) := by
    rw [hsL, hsR]
    intro h
    rcases SignType.trichotomy ε with h' | h' | h' <;> simp_all
  obtain ⟨y, hy, hy0⟩ := exists_mem_uIcc_eval_eq_zero q hsne
  have hyL : y ≠ yL := by
    rintro rfl
    rw [hy0, sign_zero] at hsL
    exact hε0 (by simpa using hsL.symm)
  have hyR : y ≠ yR := by
    rintro rfl
    rw [hy0, sign_zero] at hsR
    exact hε0 hsR.symm
  have hlo : min yL yR < y := by
    rw [min_lt_iff]
    rcases mem_uIcc.1 hy with h | h
    · exact Or.inl (h.1.lt_of_ne hyL.symm)
    · exact Or.inr (h.1.lt_of_ne hyR.symm)
  have hhi : y < max yL yR := by
    rw [lt_max_iff]
    rcases mem_uIcc.1 hy with h | h
    · exact Or.inr (h.2.lt_of_ne hyR)
    · exact Or.inl (h.2.lt_of_ne hyL)
  have hlt : ∀ z ∈ Z, z < x → φ z < y := fun z hz hzx ↦
    (le_min (hL1 z hz hzx) (hR1 z hz hzx).le).trans_lt hlo
  have hgt : ∀ z ∈ Z, x < z → y < φ z := fun z hz hxz ↦
    hhi.trans_le (max_le (hL2 z hz hxz).le (hR2 z hz hxz))
  refine ⟨y, hy0, fun hyZ ↦ ?_, fun z hz ↦ ⟨hlt z hz, fun h ↦ ?_⟩⟩
  · rcases (hne _ hyZ).lt_or_gt with h | h
    · exact lt_irrefl y (by simpa using hlt _ hyZ h)
    · exact lt_irrefl y (by simpa using hgt _ hyZ h)
  · rcases (hne z hz).lt_or_gt with h' | h'
    · exact h'
    · exact absurd h (not_lt.2 (hgt z hz h').le)

/-- Two zeros of `q` in the same gap of `φ(Z)` coincide. -/
theorem eq_of_eval_eq_zero (D : SignTransferData Z φ p q) {y y' : ℝ} (hy : q.eval y = 0)
    (hy' : q.eval y' = 0) (h : ∀ z ∈ Z, (φ z < y ↔ φ z < y')) : y = y' :=
  eq_of_eval_eq_zero_of_forall_lt_iff q D.symm.mem_of_derivative_left hy hy' (by
    rw [Finset.forall_mem_image]
    exact h)

/-- The derivatives `p'` and `q'` have the same sign at points of corresponding gaps. -/
theorem sign_eval_derivative_eq (D : SignTransferData Z φ p q) {x y : ℝ} (hxZ : x ∉ Z)
    (hyZ : φ.symm y ∉ Z) (hG : ∀ z ∈ Z, (z < x ↔ φ z < y)) :
    SignType.sign (q.derivative.eval y) = SignType.sign (p.derivative.eval x) := by
  rw [D.sign_derivative x]
  refine sign_eval_eq_of_zeros_subset _ D.symm.mem_of_derivative_left
    (notMem_uIcc_of_forall_lt_iff (by rwa [mem_image_iff])
      (by rw [mem_image_iff, φ.symm_apply_apply]; exact hxZ) ?_)
  rw [Finset.forall_mem_image]
  intro z hz
  rw [← hG z hz, φ.lt_iff_lt]

/-- If `p` has no zero off `Z` in the gap of `x`, then `q` has no zero off `φ(Z)` in the
corresponding gap of `y`. -/
theorem no_root_of_no_root (D : SignTransferData Z φ p q) {x y : ℝ}
    (hG : ∀ z ∈ Z, (z < x ↔ φ z < y))
    (hno : ∀ w, p.eval w = 0 → w ∉ Z → ¬ ∀ z ∈ Z, (z < w ↔ z < x)) :
    ∀ w, q.eval w = 0 → φ.symm w ∉ Z → ¬ ∀ z ∈ Z, (φ z < w ↔ φ z < y) := by
  intro w hw hwZ hgw
  obtain ⟨x₀, hx₀, hx₀Z, hG₀⟩ := D.symm.exists_root (x := w) (by rwa [mem_image_iff]) hw
  refine hno x₀ hx₀ (fun h ↦ hx₀Z (by simpa using h)) fun z hz ↦ ?_
  have := hG₀ (φ z) (Finset.mem_image_of_mem φ hz)
  simp only [OrderIso.symm_apply_apply] at this
  rw [← this, hgw z hz, ← hG z hz]

/-- `sign_eval_eq` when `p` has a zero `x₀ ∉ Z` in the gap of `x`. -/
theorem sign_eval_eq_of_root (D : SignTransferData Z φ p q) {x y x₀ : ℝ} (hxZ : x ∉ Z)
    (hyZ : φ.symm y ∉ Z) (hpx : p.eval x ≠ 0) (hqy : q.eval y ≠ 0)
    (hG : ∀ z ∈ Z, (z < x ↔ φ z < y))
    (hcmp : ∀ x₁ y₁, p.eval x₁ = 0 → x₁ ∉ Z → q.eval y₁ = 0 → φ.symm y₁ ∉ Z →
      (∀ z ∈ Z, (z < x₁ ↔ φ z < y₁)) → (x₁ < x ↔ y₁ < y))
    (hx₀ : p.eval x₀ = 0) (hx₀Z : x₀ ∉ Z) (hgap : ∀ z ∈ Z, (z < x₀ ↔ z < x)) :
    SignType.sign (p.eval x) = SignType.sign (q.eval y) := by
  have hyW : y ∉ Z.image φ := by rwa [mem_image_iff]
  have hd := D.sign_eval_derivative_eq hxZ hyZ hG
  obtain ⟨y₀, hy₀, hy₀Z, hG₀⟩ := D.exists_root hx₀Z hx₀
  have hc := hcmp x₀ y₀ hx₀ hx₀Z hy₀ hy₀Z hG₀
  have hxx₀ : x₀ ≠ x := fun e ↦ hpx (e ▸ hx₀)
  have hyy₀ : y₀ ≠ y := fun e ↦ hqy (e ▸ hy₀)
  have hy₀W : y₀ ∉ Z.image φ := by rwa [mem_image_iff]
  have hZx : ∀ z ∈ Z, z ∉ uIcc x₀ x := notMem_uIcc_of_forall_lt_iff hx₀Z hxZ hgap
  have hZy : ∀ w ∈ Z.image φ, w ∉ uIcc y₀ y := notMem_uIcc_of_forall_lt_iff hy₀W hyW (by
    rw [Finset.forall_mem_image]
    intro z hz
    rw [← hG₀ z hz, ← hG z hz]
    exact hgap z hz)
  have e1 : ∀ c ∈ uIcc x₀ x, SignType.sign (p.derivative.eval c) =
      SignType.sign (p.derivative.eval x) := fun c hc ↦
    sign_eval_eq_of_zeros_subset _ D.mem_of_derivative_left fun z hz hzc ↦
      hZx z hz (uIcc_subset_uIcc hc right_mem_uIcc hzc)
  have e2 : ∀ c ∈ uIcc y₀ y, SignType.sign (q.derivative.eval c) =
      SignType.sign (q.derivative.eval y) := fun c hc ↦
    sign_eval_eq_of_zeros_subset _ D.symm.mem_of_derivative_left fun w hw hwc ↦
      hZy w hw (uIcc_subset_uIcc hc right_mem_uIcc hwc)
  rcases hxx₀.lt_or_gt with h | h
  · have hy : y₀ < y := hc.1 h
    obtain ⟨c, hc', hm⟩ := exists_eval_sub_eq_derivative_mul p h
    obtain ⟨c₂, hc₂, hm₂⟩ := exists_eval_sub_eq_derivative_mul q hy
    rw [hx₀, sub_zero] at hm
    rw [hy₀, sub_zero] at hm₂
    rw [hm, hm₂, sign_mul, sign_mul, e1 c (Icc_subset_uIcc (Ioo_subset_Icc_self hc')),
      e2 c₂ (Icc_subset_uIcc (Ioo_subset_Icc_self hc₂)), hd, sign_pos (sub_pos.2 h),
      sign_pos (sub_pos.2 hy)]
  · have hy : y < y₀ := lt_of_le_of_ne (not_lt.1 fun h' ↦ (lt_asymm h) (hc.2 h')) hyy₀.symm
    obtain ⟨c, hc', hm⟩ := exists_eval_sub_eq_derivative_mul p h
    obtain ⟨c₂, hc₂, hm₂⟩ := exists_eval_sub_eq_derivative_mul q hy
    rw [hx₀, zero_sub, neg_eq_iff_eq_neg] at hm
    rw [hy₀, zero_sub, neg_eq_iff_eq_neg] at hm₂
    rw [hm, hm₂, Left.sign_neg, Left.sign_neg, sign_mul, sign_mul,
      e1 c (Icc_subset_uIcc' (Ioo_subset_Icc_self hc')),
      e2 c₂ (Icc_subset_uIcc' (Ioo_subset_Icc_self hc₂)), hd, sign_pos (sub_pos.2 h),
      sign_pos (sub_pos.2 hy)]

/-- `sign_eval_eq` when `p` has no zero off `Z` in the gap of `x` and `Z` has a point
above `x`. -/
theorem sign_eval_eq_of_no_root_of_exists_gt (D : SignTransferData Z φ p q) {x y : ℝ}
    (hxZ : x ∉ Z) (hyZ : φ.symm y ∉ Z) (hpx : p.eval x ≠ 0) (hqy : q.eval y ≠ 0)
    (hG : ∀ z ∈ Z, (z < x ↔ φ z < y))
    (hno : ∀ w, p.eval w = 0 → w ∉ Z → ¬ ∀ z ∈ Z, (z < w ↔ z < x)) (hR : ∃ z ∈ Z, x < z) :
    SignType.sign (p.eval x) = SignType.sign (q.eval y) := by
  have hne : ∀ z ∈ Z, z ≠ x := fun z hz e ↦ hxZ (e ▸ hz)
  have hφy : ∀ z ∈ Z, φ z ≠ y := fun z hz e ↦ hyZ (by rw [← e]; simpa using hz)
  have hd := D.sign_eval_derivative_eq hxZ hyZ hG
  obtain ⟨zR, hzR, hxzR, hzRmin⟩ := exists_min_of_exists_gt hR
  have hyzR : y < φ zR := lt_of_le_of_ne
    (not_lt.1 fun h ↦ (lt_asymm hxzR) ((hG zR hzR).2 h)) (hφy zR hzR).symm
  have hab : ∀ z ∈ Z, y < φ z → φ zR ≤ φ z := fun z hz h ↦ by
    refine φ.monotone (hzRmin z hz ?_)
    rcases (hne z hz).lt_or_gt with h' | h'
    · exact absurd ((hG z hz).1 h') (not_lt.2 h.le)
    · exact h'
  by_cases hpz : p.eval zR = 0
  · have hqz : q.eval (φ zR) = 0 :=
      sign_eq_zero_iff.1 (by rw [← D.sign_eval zR hzR, hpz, sign_zero])
    obtain ⟨c, ⟨hc₁, hc₂⟩, hm⟩ := exists_eval_sub_eq_derivative_mul p hxzR
    obtain ⟨c₂, ⟨hc₃, hc₄⟩, hm₂⟩ := exists_eval_sub_eq_derivative_mul q hyzR
    rw [hpz, zero_sub, neg_eq_iff_eq_neg] at hm
    rw [hqz, zero_sub, neg_eq_iff_eq_neg] at hm₂
    have e1 : SignType.sign (p.derivative.eval c) = SignType.sign (p.derivative.eval x) :=
      sign_eval_eq_of_zeros_subset _ D.mem_of_derivative_left fun z hz hzc ↦ by
        rcases mem_uIcc.1 hzc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases (hne z hz).lt_or_gt with h | h <;>
          first | linarith | linarith [hzRmin z hz h]
    have e2 : SignType.sign (q.derivative.eval c₂) = SignType.sign (q.derivative.eval y) :=
      sign_eval_eq_of_zeros_subset _ D.symm.mem_of_derivative_left fun w hw hwc ↦ by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
        rcases mem_uIcc.1 hwc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases (hφy z hz).lt_or_gt with h | h <;>
          first | linarith | linarith [hab z hz h]
    rw [hm, hm₂, Left.sign_neg, Left.sign_neg, sign_mul, sign_mul, e1, e2, hd,
      sign_pos (sub_pos.2 hxzR), sign_pos (sub_pos.2 hyzR)]
  · have hqz : q.eval (φ zR) ≠ 0 := fun h ↦
      hpz (sign_eq_zero_iff.1 (by rw [D.sign_eval zR hzR, h, sign_zero]))
    have sp := sign_eval_eq_of_minimal_gt p hxZ hxzR hzRmin hpx hpz hno
    have sq : SignType.sign (q.eval y) = SignType.sign (q.eval (φ zR)) :=
      sign_eval_eq_of_minimal_gt q (W := Z.image φ) (by rwa [mem_image_iff]) hyzR
        (by rw [Finset.forall_mem_image]; exact hab) hqy hqz fun w hw hwW hg ↦
        D.no_root_of_no_root hG hno w hw (fun h ↦ hwW ((mem_image_iff w).2 h))
          (by rw [Finset.forall_mem_image] at hg; exact hg)
    rw [sp, sq, D.sign_eval zR hzR]

/-- `sign_eval_eq` when `p` has no zero off `Z` in the gap of `x` and `Z` lies below `x`. -/
theorem sign_eval_eq_of_no_root_of_forall_le (D : SignTransferData Z φ p q) {x y : ℝ}
    (hxZ : x ∉ Z) (hyZ : φ.symm y ∉ Z) (hG : ∀ z ∈ Z, (z < x ↔ φ z < y))
    (hno : ∀ w, p.eval w = 0 → w ∉ Z → ¬ ∀ z ∈ Z, (z < w ↔ z < x)) (hR : ∀ z ∈ Z, z ≤ x) :
    SignType.sign (p.eval x) = SignType.sign (q.eval y) := by
  have hlt : ∀ z ∈ Z, z < x := fun z hz ↦ lt_of_le_of_ne (hR z hz) fun e ↦ hxZ (e ▸ hz)
  have hnoQ := D.no_root_of_no_root hG hno
  obtain ⟨M, hM⟩ :=
    (eventually_sign_eval_eq_sign_eval_derivative D.natDegree_left).exists_forall_of_atTop
  obtain ⟨M₂, hM₂⟩ :=
    (eventually_sign_eval_eq_sign_eval_derivative D.natDegree_right).exists_forall_of_atTop
  set t := max M x + 1
  set t₂ := max M₂ y + 1
  have ht : x < t := by simp only [t]; linarith [le_max_right M x]
  have ht₂ : y < t₂ := by simp only [t₂]; linarith [le_max_right M₂ y]
  have hZt : ∀ z ∈ Z, z ∉ uIcc x t := fun z hz hzt ↦ by
    rw [uIcc_of_le ht.le] at hzt; linarith [hzt.1, hlt z hz]
  have hZt₂ : ∀ w ∈ Z.image φ, w ∉ uIcc y t₂ := by
    rw [Finset.forall_mem_image]
    intro z hz hzt
    rw [uIcc_of_le ht₂.le] at hzt
    linarith [hzt.1, (hG z hz).1 (hlt z hz)]
  have s1 : SignType.sign (p.eval x) = SignType.sign (p.eval t) :=
    sign_eval_eq_of_forall_ne_zero p fun w hw hw0 ↦ by
      rw [uIcc_of_le ht.le] at hw
      refine hno w hw0 (fun h ↦ hZt w h (by rw [uIcc_of_le ht.le]; exact hw)) fun z hz ↦
        ⟨fun _ ↦ hlt z hz, fun h ↦ h.trans_le hw.1⟩
  have s2 : SignType.sign (q.eval y) = SignType.sign (q.eval t₂) :=
    sign_eval_eq_of_forall_ne_zero q fun w hw hw0 ↦ by
      rw [uIcc_of_le ht₂.le] at hw
      refine hnoQ w hw0 (fun h ↦ hZt₂ w ((mem_image_iff w).2 h)
        (by rw [uIcc_of_le ht₂.le]; exact hw)) fun z hz ↦
        ⟨fun _ ↦ (hG z hz).1 (hlt z hz), fun h ↦ h.trans_le hw.1⟩
  rw [s1, s2, hM t (by simp only [t]; linarith [le_max_left M x]),
    hM₂ t₂ (by simp only [t₂]; linarith [le_max_left M₂ y]),
    ← sign_eval_eq_of_zeros_subset _ D.mem_of_derivative_left hZt,
    ← sign_eval_eq_of_zeros_subset _ D.symm.mem_of_derivative_left hZt₂,
    D.sign_eval_derivative_eq hxZ hyZ hG]

/-- **Signs transfer off the zeros.** Let `x ∉ Z` and `y ∉ φ(Z)` lie in corresponding gaps, with
`p x ≠ 0 ≠ q y`, and suppose the zeros of `p` and `q` in corresponding gaps lie on the same side
of `x` and `y`. Then `p x` and `q y` have the same sign. -/
theorem sign_eval_eq (D : SignTransferData Z φ p q) {x y : ℝ} (hxZ : x ∉ Z) (hyZ : φ.symm y ∉ Z)
    (hpx : p.eval x ≠ 0) (hqy : q.eval y ≠ 0) (hG : ∀ z ∈ Z, (z < x ↔ φ z < y))
    (hcmp : ∀ x₀ y₀, p.eval x₀ = 0 → x₀ ∉ Z → q.eval y₀ = 0 → φ.symm y₀ ∉ Z →
      (∀ z ∈ Z, (z < x₀ ↔ φ z < y₀)) → (x₀ < x ↔ y₀ < y)) :
    SignType.sign (p.eval x) = SignType.sign (q.eval y) := by
  by_cases h1 : ∃ x₀, p.eval x₀ = 0 ∧ x₀ ∉ Z ∧ ∀ z ∈ Z, (z < x₀ ↔ z < x)
  · obtain ⟨x₀, hx₀, hx₀Z, hgap⟩ := h1
    exact D.sign_eval_eq_of_root hxZ hyZ hpx hqy hG hcmp hx₀ hx₀Z hgap
  have hno : ∀ w, p.eval w = 0 → w ∉ Z → ¬ ∀ z ∈ Z, (z < w ↔ z < x) :=
    fun w a b c ↦ h1 ⟨w, a, b, c⟩
  by_cases hR : ∃ z ∈ Z, x < z
  · exact D.sign_eval_eq_of_no_root_of_exists_gt hxZ hyZ hpx hqy hG hno hR
  push Not at hR
  exact D.sign_eval_eq_of_no_root_of_forall_le hxZ hyZ hG hno hR

/-- An order automorphism agreeing with `φ` on `Z` maps points off `Z` to points off `φ(Z)`. -/
theorem symm_apply_notMem {ψ : ℝ ≃o ℝ} (hψZ : ∀ z ∈ Z, ψ z = φ z) {x : ℝ} (hx : x ∉ Z) :
    φ.symm (ψ x) ∉ Z := fun h ↦ by
  have := hψZ _ h
  rw [OrderIso.apply_symm_apply] at this
  exact hx (ψ.injective this ▸ h)

/-- Some order automorphism of `ℝ` agrees with `φ` on `Z` and sends the zeros of `p` off `Z` to
zeros of `q`. -/
theorem exists_orderIso (D : SignTransferData Z φ p q) :
    ∃ ψ : ℝ ≃o ℝ, (∀ z ∈ Z, ψ z = φ z) ∧ ∀ x, x ∉ Z → p.eval x = 0 → q.eval (ψ x) = 0 := by
  classical
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt D.natDegree_left
  set R := p.roots.toFinset
  have hmemR : ∀ x, x ∈ R ↔ p.eval x = 0 := fun x ↦ by
    simp [R, mem_roots hp0]
  set A := Z ∪ R
  let spec : ℝ → ℝ → Prop := fun x y ↦
    q.eval y = 0 ∧ φ.symm y ∉ Z ∧ ∀ z ∈ Z, (z < x ↔ φ z < y)
  let χ : ℝ → ℝ := fun x ↦ if x ∈ Z then φ x else if h : ∃ y, spec x y then h.choose else 0
  have hχZ : ∀ x ∈ Z, χ x = φ x := fun x hx ↦ by simp [χ, hx]
  have hχR : ∀ x, x ∉ Z → p.eval x = 0 → spec x (χ x) := fun x hx h0 ↦ by
    have h : ∃ y, spec x y := D.exists_root hx h0
    simp only [χ, hx, h, ↓reduceIte, ↓reduceDIte]
    exact h.choose_spec
  have hA : ∀ x ∈ A, x ∈ Z ∨ (x ∉ Z ∧ p.eval x = 0) := fun x hx ↦
    (em (x ∈ Z)).imp_right fun hz ↦ ⟨hz, (hmemR x).1 ((Finset.mem_union.1 hx).resolve_left hz)⟩
  have hmono : StrictMonoOn χ A := by
    intro x hx x' hx' hxx'
    rcases hA x hx with hx | ⟨hxZ, hx0⟩ <;> rcases hA x' hx' with hx' | ⟨hxZ', hx0'⟩
    · rw [hχZ x hx, hχZ x' hx']
      exact φ.strictMono hxx'
    · rw [hχZ x hx]
      exact ((hχR x' hxZ' hx0').2.2 x hx).1 hxx'
    · rw [hχZ x' hx']
      have h := hχR x hxZ hx0
      refine lt_of_le_of_ne (not_lt.1 fun h' ↦ (lt_asymm hxx') ((h.2.2 x' hx').2 h')) ?_
      intro e
      exact h.2.1 (by rw [e]; simpa using hx')
    · obtain ⟨z, hz, hz1, hz2⟩ :=
        exists_mem_Ioo_of_eval_eq_zero p D.mem_of_derivative_left hxx' hx0 hx0'
      have h := hχR x hxZ hx0
      have h' := hχR x' hxZ' hx0'
      have e1 : χ x < φ z :=
        lt_of_le_of_ne (not_lt.1 fun h'' ↦ (lt_asymm hz1) ((h.2.2 z hz).2 h''))
          (fun e ↦ h.2.1 (by rw [e]; simpa using hz))
      exact e1.trans ((h'.2.2 z hz).1 hz2)
  obtain ⟨ψ, hψ⟩ := exists_orderIso_eqOn_of_strictMonoOn hmono
  refine ⟨ψ, fun z hz ↦ (hψ z (Finset.mem_union_left _ hz)).trans (hχZ z hz),
    fun x hxZ hx0 ↦ ?_⟩
  rw [hψ x (Finset.mem_union_right _ ((hmemR x).2 hx0))]
  exact (hχR x hxZ hx0).1

/-- An order automorphism agreeing with `φ` on `Z` and sending the zeros of `p` off `Z` to zeros
of `q` carries the signs of `p` to those of `q`. -/
theorem sign_eval_eq_of_orderIso (D : SignTransferData Z φ p q) {ψ : ℝ ≃o ℝ}
    (hψZ : ∀ z ∈ Z, ψ z = φ z) (hψ : ∀ x, x ∉ Z → p.eval x = 0 → q.eval (ψ x) = 0) (x : ℝ) :
    SignType.sign (p.eval x) = SignType.sign (q.eval (ψ x)) := by
  have hG : ∀ x, ∀ z ∈ Z, (z < x ↔ φ z < ψ x) := fun x z hz ↦ by
    rw [← hψZ z hz, ψ.lt_iff_lt]
  by_cases hxZ : x ∈ Z
  · rw [hψZ x hxZ]
    exact D.sign_eval x hxZ
  by_cases hx0 : p.eval x = 0
  · rw [hψ x hxZ hx0, hx0]
  have hqy : q.eval (ψ x) ≠ 0 := by
    intro hq0
    obtain ⟨x₀, hx₀, hx₀Z, hG₀⟩ := D.symm.exists_root (x := ψ x)
      (by rw [mem_image_iff]; exact symm_apply_notMem hψZ hxZ) hq0
    have hx₀Z' : x₀ ∉ Z := fun h ↦ hx₀Z (by simpa using h)
    have e := D.eq_of_eval_eq_zero (hψ x₀ hx₀Z' hx₀) hq0 fun z hz ↦ by
      have := hG₀ (φ z) (Finset.mem_image_of_mem φ hz)
      simp only [OrderIso.symm_apply_apply] at this
      rw [← hG x₀ z hz, this]
    exact hx0 (ψ.injective e ▸ hx₀)
  refine D.sign_eval_eq hxZ (symm_apply_notMem hψZ hxZ) hx0 hqy (hG x)
    fun x₀ y₀ hx₀ hx₀Z hy₀ hy₀Z hG₀ ↦ ?_
  rw [← D.eq_of_eval_eq_zero (hψ x₀ hx₀Z hx₀) hy₀ fun z hz ↦ (hG x₀ z hz).symm.trans (hG₀ z hz),
    ψ.lt_iff_lt]

end SignTransferData

/-! ### Sign patterns -/

/-- Two families of real polynomials have the *same sign pattern* if an order automorphism `ψ`
of `ℝ` carries the signs of the first family to those of the second:
`sign (f i (x)) = sign (g i (ψ x))`. -/
def SameSignPattern {ι : Type*} (f g : ι → ℝ[X]) : Prop :=
  ∃ ψ : ℝ ≃o ℝ, ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))

namespace SameSignPattern

variable {ι κ : Type*} {f g h : ι → ℝ[X]}

/-- Every family has the same sign pattern as itself. -/
@[refl]
theorem refl (f : ι → ℝ[X]) : SameSignPattern f f := ⟨OrderIso.refl ℝ, fun _ _ ↦ rfl⟩

/-- Having the same sign pattern is symmetric. -/
@[symm]
theorem symm (H : SameSignPattern f g) : SameSignPattern g f := by
  obtain ⟨ψ, hψ⟩ := H
  exact ⟨ψ.symm, fun i x ↦ by simpa using (hψ i (ψ.symm x)).symm⟩

/-- Having the same sign pattern is transitive. -/
@[trans]
theorem trans (H₁ : SameSignPattern f g) (H₂ : SameSignPattern g h) : SameSignPattern f h := by
  obtain ⟨ψ₁, h₁⟩ := H₁
  obtain ⟨ψ₂, h₂⟩ := H₂
  exact ⟨ψ₁.trans ψ₂, fun i x ↦ (h₁ i x).trans (h₂ i (ψ₁ x))⟩

/-- Reindexing both families along `e` preserves having the same sign pattern. -/
theorem comp (H : SameSignPattern f g) (e : κ → ι) : SameSignPattern (f ∘ e) (g ∘ e) := by
  obtain ⟨ψ, hψ⟩ := H
  exact ⟨ψ, fun i x ↦ hψ (e i) x⟩

/-- Reindexing both families along an equivalence `e` does not change whether they have the same
sign pattern. -/
theorem comp_equiv_iff (e : κ ≃ ι) : SameSignPattern (f ∘ e) (g ∘ e) ↔ SameSignPattern f g :=
  ⟨fun H ↦ by simpa [Function.comp_def] using H.comp e.symm, fun H ↦ H.comp e⟩

/-- A sign condition realised by one family is realised by any family with the same sign
pattern. -/
theorem exists_iff (H : SameSignPattern f g) (ε : ι → SignType) :
    (∃ x, ∀ i, SignType.sign ((f i).eval x) = ε i) ↔
      ∃ y, ∀ i, SignType.sign ((g i).eval y) = ε i := by
  obtain ⟨ψ, hψ⟩ := H
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ψ x, fun i ↦ (hψ i x).symm.trans (hx i)⟩
  · rintro ⟨y, hy⟩
    exact ⟨ψ.symm y, fun i ↦ (hψ i (ψ.symm y)).trans (by simpa using hy i)⟩

end SameSignPattern

/-- **Hörmander's transfer lemma.** Let `p, q` be non-constant real polynomials and `f, g`
families of real polynomials. Let `rᵢ` agree in sign with `p` on the zeros of `fᵢ` and `r₀` with
`p` on the zeros of `p'` (`rᵢ` is unconstrained when `fᵢ = 0`), and likewise `sᵢ, s₀` for
`q, g`. If one order automorphism of `ℝ`
carries the signs of `fᵢ, p', rᵢ, r₀` to those of `gᵢ, q', sᵢ, s₀`, then the families
`(p, f)` and `(q, g)` have the same sign pattern. -/
theorem sameSignPattern_of_derivative {ι : Type*} [Finite ι] {f g r s : ι → ℝ[X]}
    {p q r₀ s₀ : ℝ[X]} (hp : 0 < p.natDegree) (hq : 0 < q.natDegree)
    (hr : ∀ i x, f i ≠ 0 → (f i).eval x = 0 →
      SignType.sign (p.eval x) = SignType.sign ((r i).eval x))
    (hs : ∀ i y, g i ≠ 0 → (g i).eval y = 0 →
      SignType.sign (q.eval y) = SignType.sign ((s i).eval y))
    (hr₀ : ∀ x, p.derivative.eval x = 0 → SignType.sign (p.eval x) = SignType.sign (r₀.eval x))
    (hs₀ : ∀ y, q.derivative.eval y = 0 → SignType.sign (q.eval y) = SignType.sign (s₀.eval y))
    (φ : ℝ ≃o ℝ)
    (hφf : ∀ i x, SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (φ x)))
    (hφd : ∀ x, SignType.sign (p.derivative.eval x) = SignType.sign (q.derivative.eval (φ x)))
    (hφr : ∀ i x, SignType.sign ((r i).eval x) = SignType.sign ((s i).eval (φ x)))
    (hφr₀ : ∀ x, SignType.sign (r₀.eval x) = SignType.sign (s₀.eval (φ x))) :
    SameSignPattern (fun o : Option ι ↦ o.elim p f) (fun o : Option ι ↦ o.elim q g) := by
  classical
  have := Fintype.ofFinite ι
  have hzero : ∀ i x, (f i).eval x = 0 ↔ (g i).eval (φ x) = 0 := fun i x ↦ by
    rw [← sign_eq_zero_iff, hφf i x, sign_eq_zero_iff]
  have hfg : ∀ i, f i ≠ 0 → g i ≠ 0 := fun i hi hgi ↦ hi (Polynomial.funext fun x ↦ by
    simpa [hgi] using (hzero i x))
  have hd0 : p.derivative ≠ 0 := fun h ↦ hp.ne' (Polynomial.derivative_eq_zero.1 h)
  set N := Finset.univ.filter fun i ↦ f i ≠ 0
  set P := (∏ i ∈ N, f i) * p.derivative
  have hP : P ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi ↦ (Finset.mem_filter.1 hi).2) hd0
  set Z := P.roots.toFinset
  have hmemZ : ∀ x, x ∈ Z ↔ (∃ i, f i ≠ 0 ∧ (f i).eval x = 0) ∨ p.derivative.eval x = 0 := by
    intro x
    simp only [Z, Multiset.mem_toFinset, mem_roots hP, IsRoot.def, P, eval_mul, eval_prod,
      mul_eq_zero, Finset.prod_eq_zero_iff, N, Finset.mem_filter, Finset.mem_univ, true_and]
  have D : SignTransferData Z φ p q := by
    refine ⟨hp, hq, fun x hx ↦ (hmemZ x).2 (Or.inr hx),
      fun y hy ↦ (hmemZ _).2 (Or.inr ?_), ?_, hφd⟩
    · rwa [← sign_eq_zero_iff, hφd, OrderIso.apply_symm_apply, sign_eq_zero_iff]
    · intro z hz
      rcases (hmemZ z).1 hz with ⟨i, hfi, hi⟩ | hz'
      · rw [hr i z hfi hi, hφr i z, hs i (φ z) (hfg i hfi) ((hzero i z).1 hi)]
      · rw [hr₀ z hz', hφr₀ z,
          hs₀ (φ z) (by rwa [← sign_eq_zero_iff, ← hφd, sign_eq_zero_iff])]
  obtain ⟨ψ, hψZ, hψ⟩ := D.exists_orderIso
  refine ⟨ψ, ?_⟩
  rintro (_ | i) x
  · exact D.sign_eval_eq_of_orderIso hψZ hψ x
  change SignType.sign ((f i).eval x) = SignType.sign ((g i).eval (ψ x))
  by_cases hfi : f i = 0
  · have hgi : g i = 0 := Polynomial.funext fun y ↦ by
      simpa using (hzero i (φ.symm y)).1 (by simp [hfi])
    simp [hfi, hgi]
  by_cases hxZ : x ∈ Z
  · rw [hψZ x hxZ]
    exact hφf i x
  rw [hφf i x]
  refine sign_eval_eq_of_zeros_subset _ (W := Z.image φ) (fun w hw ↦
    (SignTransferData.mem_image_iff w).2 ((hmemZ _).2 (Or.inl ⟨i, hfi, by
      rw [hzero, OrderIso.apply_symm_apply]; exact hw⟩)))
    (notMem_uIcc_of_forall_lt_iff (by rw [SignTransferData.mem_image_iff]; simpa using hxZ)
      (by rw [SignTransferData.mem_image_iff]; exact SignTransferData.symm_apply_notMem hψZ hxZ)
      ?_)
  rw [Finset.forall_mem_image]
  intro z hz
  rw [φ.lt_iff_lt, ← hψZ z hz, ψ.lt_iff_lt]

end MMP
