module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Span

/-!
# Linear algebra of the normal fibre of a regular sequence

This file collects the commutative algebra behind the local analysis of the orientation class
of a regular imbedding (Fulton, §19.2; Baum–Fulton–MacPherson IV.4). Let `A` be a ring with a
character `ev : A → k` (in the application, evaluation at a complex point `x` of the zero locus),
`s₁, …, sₑ ∈ A` the coordinates of a section, and `f₁, …, f_d` a weakly regular sequence with
`(s) = (f)`, so that `s = M f` and `f = G s` for matrices `M`, `G` over `A`, and `ev(f) = 0`.

## Main results

* `MMP.WeaklyRegular.mem_span_of_sum_mul_eq_zero`: the coefficients of a linear relation
  `∑ hᵢ fᵢ = 0` among the members of a weakly regular sequence lie in the ideal `(f)` (vanishing
  of the first Koszul homology in degree one).
* `MMP.RegularSequenceFibre.sum_ev_mul_ev_eq_zero`: the value at `x` of every relation
  `∑ gₐ sₐ = 0` annihilates the columns of `M(x)`.
* `MMP.RegularSequenceFibre.ev_mul_ev_eq_one`: `G(x) M(x) = 1`, so `M(x)` is injective.
* `MMP.RegularSequenceFibre.eq_mulVec_of_forall_relation`: a vector annihilating the values at
  `x` of the relations `sₐ - ∑_b M_{ab} ∑_c G_{bc} s_c = 0` lies in the range of `M(x)`.

Together these identify the fibre `N_x` of the normal bundle in the coordinates of `E`
(`MMP.Modules.normalFibre`) with the range of `M(x)`.
-/

@[expose] public section

open RingTheory.Sequence

namespace MMP.WeaklyRegular

open _root_.RingTheory.Sequence.IsWeaklyRegular

/-- **Relations among a weakly regular sequence are Koszul.** If `f₁, …, fₙ` is a weakly regular
sequence in `R` and `∑ hᵢ fᵢ = 0`, then every `hᵢ` lies in the ideal `(f₁, …, fₙ)`. -/
theorem mem_span_of_sum_mul_eq_zero {R : Type*} [CommRing R] :
    ∀ {n : ℕ} (f : Fin n → R), IsWeaklyRegular R (List.ofFn f) → ∀ (h : Fin n → R),
      ∑ i, h i * f i = 0 → ∀ i, h i ∈ Ideal.span (Set.range f)
  | 0, _, _, _, _, i => i.elim0
  | n + 1, f, hf, h, hs, i => by
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff] at hf
    obtain ⟨hf', hr⟩ := hf
    rw [isWeaklyRegular_cons_iff] at hr
    have hr := hr.1
    rw [Ideal.ofList_ofFn] at hr
    set f' := f ∘ Fin.castSucc
    rw [Fin.sum_univ_castSucc] at hs
    have hlast : h (Fin.last n) ∈ Ideal.span (Set.range f') := by
      have hmem : f (Fin.last n) • h (Fin.last n) ∈
          Ideal.span (Set.range f') • (⊤ : Submodule R R) := by
        rw [smul_eq_mul, smul_eq_mul, Ideal.mul_top, mul_comm, eq_neg_of_add_eq_zero_right hs]
        exact neg_mem (Submodule.sum_mem _ fun j _ ↦
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
      have : f (Fin.last n) • (Submodule.Quotient.mk (h (Fin.last n)) :
          R ⧸ Ideal.span (Set.range f') • (⊤ : Submodule R R)) = f (Fin.last n) • 0 := by
        rw [← Submodule.Quotient.mk_smul, smul_zero, Submodule.Quotient.mk_eq_zero]
        exact hmem
      have h0 := (Submodule.Quotient.mk_eq_zero _).1 (hr this)
      rwa [smul_eq_mul, Ideal.mul_top] at h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hlast
    have hs' : ∑ j, (h (Fin.castSucc j) + c j * f (Fin.last n)) * f' j = 0 := by
      rw [← hs, ← hc, Finset.sum_mul]
      simp only [add_mul, Finset.sum_add_distrib, f', Function.comp_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hmono : Ideal.span (Set.range f') ≤ Ideal.span (Set.range f) :=
      Ideal.span_mono (Set.range_comp_subset_range _ _)
    have hfl : f (Fin.last n) ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨_, rfl⟩
    refine Fin.lastCases (hmono hlast) (fun j ↦ ?_) i
    have := hmono (mem_span_of_sum_mul_eq_zero f' hf' _ hs' j)
    have h2 := sub_mem this (Ideal.mul_mem_left _ (c j) hfl)
    rwa [add_sub_cancel_right] at h2

end MMP.WeaklyRegular

namespace MMP

namespace RegularSequenceFibre

variable {A k : Type*} [CommRing A] [Field k] {e d : ℕ} (ev : A →+* k) {f : Fin d → A}
  {s : Fin e → A}

/-- If `ev` vanishes on each `f b`, then it vanishes on every element of the ideal
`(f₁, …, f_d)`. -/
lemma ev_eq_zero_of_mem_span (hev : ∀ b, ev (f b) = 0) {y : A}
    (hy : y ∈ Ideal.span (Set.range f)) : ev y = 0 :=
  (Ideal.span_le.2 (by rintro _ ⟨b, rfl⟩; exact hev b) : Ideal.span (Set.range f) ≤ RingHom.ker ev)
    hy

/-- If `f` is a weakly regular sequence vanishing under `ev` and `s = M f`, the value under `ev` of
every relation `∑ gₐ sₐ = 0` annihilates each column of `ev(M)`. -/
theorem sum_ev_mul_ev_eq_zero (hf : IsWeaklyRegular A (List.ofFn f)) (hev : ∀ b, ev (f b) = 0)
    (M : Fin e → Fin d → A) (hM : ∀ a, s a = ∑ b, M a b * f b) {g : Fin e → A}
    (hg : ∑ a, g a * s a = 0) (b : Fin d) :
    ∑ a, ev (g a) * ev (M a b) = 0 := by
  have h1 : ∑ b, (∑ a, g a * M a b) * f b = 0 := by
    rw [← hg]
    simp_rw [hM, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have := ev_eq_zero_of_mem_span ev hev (WeaklyRegular.mem_span_of_sum_mul_eq_zero f hf _ h1 b)
  simpa [map_sum, map_mul] using this

/-- If `f` is a weakly regular sequence vanishing under `ev`, `s = M f` and `f = G s`, then
`ev(G) ev(M) = 1`. -/
theorem ev_mul_ev_eq_one (hf : IsWeaklyRegular A (List.ofFn f)) (hev : ∀ b, ev (f b) = 0)
    (M : Fin e → Fin d → A) (hM : ∀ a, s a = ∑ b, M a b * f b) (G : Fin d → Fin e → A)
    (hG : ∀ b, f b = ∑ a, G b a * s a) (b c : Fin d) :
    ∑ a, ev (G b a) * ev (M a c) = if b = c then 1 else 0 := by
  have h1 : ∑ c, ((∑ a, G b a * M a c) - if b = c then 1 else 0) * f c = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_mul]
    rw [Finset.sum_comm, hG b, sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hM a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have := ev_eq_zero_of_mem_span ev hev (WeaklyRegular.mem_span_of_sum_mul_eq_zero f hf _ h1 c)
  rw [map_sub, sub_eq_zero] at this
  simpa [map_sum, map_mul, apply_ite ev] using this

/-- The relation `sₐ - ∑_b M_{ab} ∑_c G_{bc} s_c = 0` attached to an index `a`, when `s = M f`
and `f = G s`. -/
def relation (M : Fin e → Fin d → A) (G : Fin d → Fin e → A) (a : Fin e) : Fin e → A :=
  fun c ↦ (if a = c then 1 else 0) - ∑ b, M a b * G b c

/-- If `s = M f` and `f = G s`, then `∑_c (relation M G a)_c s_c = 0` for every index `a`. -/
theorem sum_relation_mul_eq_zero (M : Fin e → Fin d → A) (hM : ∀ a, s a = ∑ b, M a b * f b)
    (G : Fin d → Fin e → A) (hG : ∀ b, f b = ∑ a, G b a * s a) (a : Fin e) :
    ∑ c, relation M G a c * s c = 0 := by
  simp_rw [relation, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm, hM a, sub_eq_zero]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [hG b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A vector `w ∈ kᵉ` annihilating the values under `ev` of the relations `relation M G a` is
`ev(M)` applied to `ev(G) w`; in particular it lies in the range of `ev(M)`. -/
theorem eq_mulVec_of_forall_relation (M : Fin e → Fin d → A) (G : Fin d → Fin e → A)
    {w : Fin e → k} (hw : ∀ a, ∑ c, w c * ev (relation M G a c) = 0) (a : Fin e) :
    w a = ∑ b, ev (M a b) * ∑ c, ev (G b c) * w c := by
  have := hw a
  simp only [relation, map_sub, map_sum, map_mul, apply_ite ev, map_one, map_zero, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, sub_eq_zero] at this
  rw [this]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

end RegularSequenceFibre

end MMP
