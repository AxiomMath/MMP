module

public import Mathlib.Order.KrullDimension
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

/-!
# Height plus coheight in a finite type domain over a field

For a finite type domain `A` over a field `k` and a prime `p` of `A`,
`dim A ≤ height p + coheight p`. Splicing a longest chain of primes ending at `p` with a longest
chain starting at `p` gives a maximal chain of primes, and every maximal chain has length `dim A`
(Stacks 00OS, `Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim`).
The reverse inequality, which holds in any preorder, is `Order.height_add_coheight_le_krullDim`.

## Main results

* `MMP.exists_covBy_series_length_eq_height_add_coheight`: through an element of finite height
  and coheight there is a maximal chain of covering relations of length `height a + coheight a`.
* `MMP.ringKrullDim_le_height_add_coheight`: `dim A ≤ height p + coheight p`.

## References

* [StacksProject 00OS](https://stacks.math.columbia.edu/tag/00OS)
-/

@[expose] public section

open Order

namespace MMP

/-- If `a` has finite height and coheight, there is a maximal chain through `a` of length
`height a + coheight a`: a chain starting at a minimal element, ending at a maximal element, all of
whose steps are covering relations. It is a longest chain ending at `a` followed by a longest chain
starting at `a`. -/
theorem exists_covBy_series_length_eq_height_add_coheight {α : Type*} [PartialOrder α] (a : α)
    (hh : height a ≠ ⊤) (hc : coheight a ≠ ⊤) :
    ∃ s : LTSeries α, IsMin s.head ∧ IsMax s.last ∧
      (∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) ∧
      (s.length : ℕ∞) = height a + coheight a := by
  obtain ⟨h, hh'⟩ := ENat.ne_top_iff_exists.mp hh
  obtain ⟨c, hc'⟩ := ENat.ne_top_iff_exists.mp hc
  obtain ⟨s₁, hs₁, hl₁⟩ := exists_series_of_le_height a (n := h) hh'.le
  obtain ⟨s₂, hs₂, hl₂⟩ := exists_series_of_le_coheight a (n := c) hc'.le
  have e₁ : (s₁.length : ℕ∞) = height s₁.last := by rw [hs₁, hl₁, hh']
  have e₂ : (s₂.length : ℕ∞) = coheight s₂.head := by rw [hs₂, hl₂, hc']
  have H₁ := height_eq_index_of_length_eq_height_last e₁
  have H₂ := coheight_eq_index_of_length_eq_head_coheight e₂
  have hS : s₁.last = s₂.head := hs₁.trans hs₂.symm
  refine ⟨s₁.smash s₂ hS, ?_, ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash]
    have := H₁ 0
    simp only [Fin.val_zero, Nat.cast_zero] at this
    exact height_eq_zero.mp this
  · rw [RelSeries.last_smash]
    have := H₂ (Fin.last _)
    simp only [Fin.rev_last, Fin.val_zero, Nat.cast_zero] at this
    exact coheight_eq_zero.mp this
  · have key : ∀ i : Fin (s₁.length + s₂.length),
        (s₁.smash s₂ hS).toFun i.castSucc ⋖ (s₁.smash s₂ hS).toFun i.succ := by
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_)
      · erw [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd]
        refine ⟨s₁.step j, fun b hb₁ hb₂ ↦ ?_⟩
        have k₁ := height_add_one_le hb₁
        have k₂ := height_add_one_le hb₂
        rw [H₁] at k₁ k₂
        have k : ((j.castSucc : ℕ) : ℕ∞) + 1 + 1 ≤ ((j.succ : ℕ) : ℕ∞) :=
          (by gcongr : ((j.castSucc : ℕ) : ℕ∞) + 1 + 1 ≤ height b + 1).trans k₂
        simp only [Fin.val_castSucc, Fin.val_succ] at k
        norm_cast at k
        omega
      · erw [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]
        refine ⟨s₂.step j, fun b hb₁ hb₂ ↦ ?_⟩
        have k₁ := coheight_add_one_le hb₁
        have k₂ := coheight_add_one_le hb₂
        rw [H₂] at k₁ k₂
        have k : ((j.succ.rev : ℕ) : ℕ∞) + 1 + 1 ≤ ((j.castSucc.rev : ℕ) : ℕ∞) :=
          (by gcongr : ((j.succ.rev : ℕ) : ℕ∞) + 1 + 1 ≤ coheight b + 1).trans k₁
        simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ] at k
        norm_cast at k
        omega
    exact key
  · simp [RelSeries.smash, hl₁, hl₂, hh', hc']

/-- For a finite type domain `A` over a field and a prime `p` of `A`,
`dim A ≤ height p + coheight p`: a maximal chain of primes through `p` has length `dim A`
(Stacks 00OS). Together with `Order.height_add_coheight_le_krullDim` this is an equality. -/
theorem ringKrullDim_le_height_add_coheight (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    ringKrullDim A ≤ ((height p + coheight p : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨h₁, h₂⟩ :=
    Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim k A
  have := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have hfin : ringKrullDim A ≠ ⊤ := by
    rw [h₁ m]
    exact_mod_cast Ideal.height_ne_top hm.ne_top
  have hh : height p ≠ ⊤ := by
    simpa using ne_top_of_le_ne_top hfin (height_le_krullDim p)
  have hc : coheight p ≠ ⊤ := by
    simpa using ne_top_of_le_ne_top hfin (coheight_le_krullDim p)
  obtain ⟨s, hmin, hmax, hcov, hlen⟩ := exists_covBy_series_length_eq_height_add_coheight p hh hc
  rw [← hlen, ← h₂ ⟨s.length, s.toFun, hcov⟩ hmin hmax]
  rfl

end MMP
