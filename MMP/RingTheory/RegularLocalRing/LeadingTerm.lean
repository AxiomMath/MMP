module

public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorReesKernel
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Existence and uniqueness of leading terms (Kollár 1.38)

Let `(A, 𝔪, κ)` be a regular local ring of dimension `2` with regular system of parameters
`x, y`, and `f ∈ A` with `mult f = m < ∞`. A form `F ∈ κ[X, Y]_m` is a leading term of `f`
(`MMP.Resolution.IsLeadingTerm`) if it maps to the class of `f` in `𝔪^m / 𝔪^{m+1}`. Then `f` has
exactly one leading term, and it is a non-zero form.

## Main statements

* `MMP.Resolution.Kollar.existsUnique_isLeadingTerm`: Kollár 1.38.
-/

@[expose] public section

open IsLocalRing

namespace MMP.Resolution.Kollar

open MvPolynomial in
private theorem exists_eq_eval_add_of_mem_pow_succ {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A}
    (hxy : maximalIdeal A = Ideal.span {x, y}) {k : ℕ}
    (hk : ∀ a ∈ maximalIdeal A ^ k, ∃ G : MvPolynomial (Fin 2) A, G.IsHomogeneous k ∧
      eval ![x, y] G = a) {a : A} (ha : a ∈ maximalIdeal A ^ (k + 1)) :
    ∃ H₀ H₁ : MvPolynomial (Fin 2) A, H₀.IsHomogeneous k ∧ H₁.IsHomogeneous k ∧
      a = x * eval ![x, y] H₀ + y * eval ![x, y] H₁ := by
  rw [pow_succ] at ha
  refine Submodule.mul_induction_on ha (fun s hs r hr => ?_) (fun a b ha hb => ?_)
  · obtain ⟨G, hG, rfl⟩ := hk s hs
    rw [hxy, Ideal.mem_span_pair] at hr
    obtain ⟨u, v, rfl⟩ := hr
    refine ⟨C u * G, C v * G, hG.C_mul u, hG.C_mul v, ?_⟩
    simp only [map_mul, eval_C]
    ring
  · obtain ⟨H₀, H₁, h₀, h₁, rfl⟩ := ha
    obtain ⟨K₀, K₁, k₀, k₁, rfl⟩ := hb
    refine ⟨H₀ + K₀, H₁ + K₁, h₀.add k₀, h₁.add k₁, ?_⟩
    simp only [map_add]
    ring

open MvPolynomial in
private theorem exists_isHomogeneous_eval_eq_of_mem_pow {A : Type*} [CommRing A]
    [IsLocalRing A] {x y : A}
    (hxy : maximalIdeal A = Ideal.span {x, y}) (k : ℕ) :
    ∀ a ∈ maximalIdeal A ^ k, ∃ G : MvPolynomial (Fin 2) A, G.IsHomogeneous k ∧
      eval ![x, y] G = a := by
  induction k with
  | zero =>
    intro a _
    exact ⟨C a, isHomogeneous_C _ _, by simp⟩
  | succ k ih =>
    intro a ha
    obtain ⟨H₀, H₁, h₀, h₁, rfl⟩ := exists_eq_eval_add_of_mem_pow_succ hxy ih ha
    refine ⟨X 0 * H₀ + X 1 * H₁, ?_, ?_⟩
    · have := (isHomogeneous_X A (0 : Fin 2)).mul h₀
      have h2 := (isHomogeneous_X A (1 : Fin 2)).mul h₁
      rw [add_comm 1 k] at this h2
      exact this.add h2
    · simp

open MvPolynomial in
private theorem eval_mem_pow_succ_of_map_eq_zero {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A} (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) {m : ℕ}
    {G : MvPolynomial (Fin 2) A} (hG : G.IsHomogeneous m) (h0 : map (residue A) G = 0) :
    eval ![x, y] G ∈ maximalIdeal A ^ (m + 1) := by
  rw [eval_eq']
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : d 0 + d 1 = m := by
    have := hG (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
    simpa using this
  have hc : G.coeff d ∈ maximalIdeal A := by
    have : (map (residue A) G).coeff d = (0 : MvPolynomial (Fin 2) (ResidueField A)).coeff d := by
      rw [h0]
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact (residue_eq_zero_iff _).mp this
  have hp : (∏ i, (![x, y] : Fin 2 → A) i ^ d i) ∈ maximalIdeal A ^ m := by
    rw [Fin.prod_univ_two, ← hdeg, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)
  rw [pow_succ']
  exact Ideal.mul_mem_mul hc hp

open MvPolynomial Pointwise in
private theorem map_eq_zero_of_eval_mem_pow_succ {A : Type*} [CommRing A] [IsRegularLocalRing A]
    (hA : ringKrullDim A = 2) {x y : A} (hxy : maximalIdeal A = Ideal.span {x, y}) {m : ℕ}
    {G : MvPolynomial (Fin 2) A} (hG : G.IsHomogeneous m)
    (h : eval ![x, y] G ∈ maximalIdeal A ^ (m + 1)) : map (residue A) G = 0 := by
  have hx : x ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
  have hy : y ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
  have hfr : (maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hA] at h
    exact_mod_cast h
  have hlist : Ideal.ofList [x, y] = maximalIdeal A := by
    have h : {r : A | r ∈ [x, y]} = {x, y} := by ext r; simp
    rw [Ideal.ofList, h, hxy]
  have hcm :=
    IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay A
  have hreg := ((hcm.1 [x, y] hlist (by simp [hfr])).1).toIsWeaklyRegular
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hreg
  obtain ⟨h1, h2⟩ := hreg
  have hspan : x • (⊤ : Submodule A A) = Ideal.span ({x} : Set A) := by
    ext c
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hf₁ : ∀ a : A, x * a = 0 → a = 0 :=
    fun a ha => h1 (show x • a = x • 0 by simpa using ha)
  have hf₂ : ∀ a : A, y * a ∈ Ideal.span ({x} : Set A) → a ∈ Ideal.span ({x} : Set A) := by
    intro a ha
    have h2' : IsSMulRegular (A ⧸ (x • ⊤ : Submodule A A)) y := h2
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at h2'
    have h3 := h2' a (by rw [hspan]; simpa using ha)
    rwa [hspan] at h3
  obtain ⟨H₀, H₁, h₀, h₁, hH⟩ := exists_eq_eval_add_of_mem_pow_succ hxy
    (exists_isHomogeneous_eval_eq_of_mem_pow hxy m) h
  have hP : (G - C x * H₀ - C y * H₁).IsHomogeneous m := by
    have := ((hG.sub (h₀.C_mul x)).sub (h₁.C_mul y))
    exact this
  have hev : eval (Stacks.AlmostBlowUp.centerGens A x y) (G - C x * H₀ - C y * H₁) = 0 := by
    have : Stacks.AlmostBlowUp.centerGens A x y = ![x, y] := rfl
    rw [this]
    simp only [map_sub, map_mul, eval_C]
    rw [hH]
    ring
  have hmem := Stacks.AlmostBlowUp.mem_relationIdeal_of_isHomogeneous_of_eval_eq_zero A x y hf₁
    hf₂ hP hev
  rw [Stacks.AlmostBlowUp.relationIdeal, Ideal.mem_span_singleton] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  have hxr : residue A x = 0 := (residue_eq_zero_iff _).mpr hx
  have hyr : residue A y = 0 := (residue_eq_zero_iff _).mpr hy
  have := congrArg (map (residue A)) hQ
  simp only [map_sub, map_mul, map_C, hxr, hyr, map_zero] at this
  simpa using this

/-- **Kollár 1.38.** Let `(A, 𝔪, κ)` be a regular local ring of dimension `2` with regular system
of parameters `x, y` (`𝔪 = (x, y)`), and `f ∈ A` with `mult f < ∞`. Then `f` has exactly one
leading term with respect to `x, y`, and it is a non-zero form. -/
@[mmp "lem_kr1b_leading_term_exists"]
theorem existsUnique_isLeadingTerm {A : Type*} [CommRing A] [IsRegularLocalRing A]
    (hA : ringKrullDim A = 2) {x y : A} (hxy : maximalIdeal A = Ideal.span {x, y}) {f : A}
    (hf : MMP.Resolution.mult f ≠ ⊤) :
    (∃! F : MvPolynomial (Fin 2) (ResidueField A), MMP.Resolution.IsLeadingTerm x y f F) ∧
      ∀ F, MMP.Resolution.IsLeadingTerm x y f F → F ≠ 0 := by
  have hx : x ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
  have hy : y ∈ maximalIdeal A := hxy ▸ Ideal.subset_span (by simp)
  obtain ⟨m, hm0⟩ := ENat.ne_top_iff_exists.mp hf
  have hm : MMP.Resolution.mult f = m := hm0.symm
  have hm' : (m : ℕ∞) = MMP.Resolution.idealOrder (Ideal.span {f}) := hm0
  have hfm : f ∈ maximalIdeal A ^ m :=
    Ideal.span_singleton_le_iff_mem _ |>.mp
      (MMP.Resolution.le_pow_of_le_idealOrder hm'.le)
  have hfm1 : f ∉ maximalIdeal A ^ (m + 1) := by
    intro h
    have hle : Ideal.span {f} ≤ maximalIdeal A ^ (m + 1) :=
      (Ideal.span_singleton_le_iff_mem _).mpr h
    have : ((m + 1 : ℕ) : ℕ∞) ≤ MMP.Resolution.idealOrder (Ideal.span {f}) :=
      le_iSup₂_of_le (m + 1) hle le_rfl
    rw [← hm'] at this
    exact absurd (by exact_mod_cast this : m + 1 ≤ m) (by omega)
  have key : ∀ F, MMP.Resolution.IsLeadingTerm x y f F → ∃ G : MvPolynomial (Fin 2) A,
      G.IsHomogeneous m ∧ MvPolynomial.map (residue A) G = F ∧
        f - MvPolynomial.eval ![x, y] G ∈ maximalIdeal A ^ (m + 1) := by
    rintro F ⟨m', hm2, -, G, hG, hGF, hfG⟩
    have : m' = m := by
      have := hm.symm.trans hm2
      exact_mod_cast this.symm
    subst this
    exact ⟨G, hG, hGF, hfG⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hG, hGf⟩ := exists_isHomogeneous_eval_eq_of_mem_pow hxy m f hfm
    refine ⟨MvPolynomial.map (residue A) G, ⟨m, hm, hG.map _, G, hG, rfl, ?_⟩, ?_⟩
    · rw [hGf, sub_self]
      exact Submodule.zero_mem _
    · intro F hF
      obtain ⟨G', hG', rfl, h'⟩ := key F hF
      have hsub : MvPolynomial.eval ![x, y] (G' - G) ∈ maximalIdeal A ^ (m + 1) := by
        have := Ideal.sub_mem _ (Ideal.zero_mem _) h'
        rw [← hGf] at this
        simpa [sub_eq_add_neg, add_comm] using this
      have := map_eq_zero_of_eval_mem_pow_succ hA hxy (hG'.sub hG) hsub
      rw [map_sub, sub_eq_zero] at this
      exact this
  · intro F hF h0
    obtain ⟨G, hG, hGF, hfG⟩ := key F hF
    rw [h0] at hGF
    have := eval_mem_pow_succ_of_map_eq_zero hx hy hG hGF
    exact hfm1 (by simpa using Ideal.add_mem _ hfG this)

end MMP.Resolution.Kollar
