module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Positivity.AmplePerturbation

/-!
# Adapted resolutions of a basepoint-free datum admit a tie-breaker

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)`, with `m ≥ 1` and `|mD|` not basepoint free. Then some `r_j` is positive (else
`f^*|mD|` would be free and, `f` being surjective, so would `|mD|`). Let `j'` minimise
`(1 + a_j - p_j) / r_j` over `{j : r_j > 0}`. Enlarging `p_{j'}` by a small `η > 0` (which keeps
`f^*(aD - K_X - Δ) - ∑_j p_j F_j` ample and `p_{j'} < 1 + a_{j'}`) gives rationals `p'_j` for
which the tuple is again an `m`-adapted resolution and `j'` is the unique minimiser; with `c` the
minimum, `(j', c)` is a tie-breaker.

## Main results

* `MMP.Mori.IsBasepointFreeAdaptedResolution.exists_isBasepointFreeTieBreaker`: after changing
  only the `p_j`, an `m`-adapted resolution admits a tie-breaker.

## Implementation notes

A tie-breaker `MMP.Mori.IsBasepointFreeTieBreaker` extends
`MMP.Mori.IsBasepointFreeAdaptedResolution`, so the single conclusion
`IsBasepointFreeTieBreaker … p' rj j' c` says both that the tuple with `p'` is an `m`-adapted
resolution and that `(j', c)` is a tie-breaker for it. The condition `H⁰(X, mD) ≠ 0` is part of
`MMP.Mori.IsBasepointFreeAdaptedResolution`, and `Bs|mD| ≠ ∅` is
`¬ (m • D).IsBasepointFree`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 4
-/

@[expose] public section

section

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

namespace MMP.FourfoldProofs.Km3aBpfThresholdProof

open MMP.Mori

/-- Raising one `p` breaks the tie: if `j'` minimises `(1 + b_j - p_j) / r_j` over the indices with
`r_j > 0`, `p_j < 1 + b_j` and `r_j ≥ 0` for all `j`, and `η > 0`, then with
`c = (1 + b_{j'} - p_{j'} - η) / r_{j'}` every index has `c r_j < 1 + b_j - p_j`. -/
private theorem div_mul_lt_one_add_sub {ι : Type*} {b p r : ι → ℚ} (hpb : ∀ j, p j < 1 + b j)
    (hr : ∀ j, 0 ≤ r j) {j' : ι} (hrj' : 0 < r j')
    (hmin : ∀ j, 0 < r j → (1 + b j' - p j') / r j' ≤ (1 + b j - p j) / r j)
    {η : ℚ} (hη : 0 < η) (j : ι) :
    (1 + b j' - p j' - η) / r j' * r j < 1 + b j - p j := by
  rcases (hr j).lt_or_eq with hj | hj
  · have := hmin j hj
    rw [div_le_div_iff₀ hrj' hj] at this
    rw [div_mul_eq_mul_div, div_lt_iff₀ hrj']
    nlinarith
  · rw [← hj, mul_zero]
    linarith [hpb j]

/-- Raising the coefficient of `F_{j'}` in `∑_j p_j F_j` by `η` adds `η F_{j'}`. -/
private theorem sum_single_add_piSingle {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Scheme.{0}}
    (F : ι → PrimeDivisor Y) (p : ι → ℚ) (j' : ι) (η : ℚ) :
    ∑ j, Finsupp.single (F j) ((p + Pi.single j' η : ι → ℚ) j) =
      ∑ j, Finsupp.single (F j) (p j) + η • Divisor.toQDivisor (Finsupp.single (F j') 1) := by
  simp only [Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j' (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same]
  ext E
  by_cases hE : F j' = E
  · subst hE; simp [DivisorWithCoeffs.coeff_single_self]
  · simp [DivisorWithCoeffs.coeff_single_of_ne hE]

/-- If an `m`-adapted resolution exists and `|mD|` is not basepoint free, some `r_j` is
positive. -/
private theorem exists_pos_of_not_isBasepointFree {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : Divisor X} {a : ℚ} {m : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ}
    {rj : Fin s → ℕ} (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj)
    (hBs : ¬ (m • D).IsBasepointFree) : ∃ j, 0 < rj j := by
  by_contra! hall
  have hr0 : ∀ j, rj j = 0 := fun j => Nat.le_zero.mp (hall j)
  haveI : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  haveI : IsProper f := h.isLogResolution.isProper
  refine hBs (eq_bot_iff.mpr fun x hx => ?_)
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨σ, hσ, _, Z', hpb, hy⟩ := h.exists_notMem_supp y
  simp only [hr0, Nat.cast_zero, Finsupp.single_zero, Finset.sum_const_zero, sub_zero] at hy
  exact hy (MMP.Flips.preimage_supp_subset_supp_of_isPullback
    ((Divisor.isCartier_principalDivisor _).add (h.isCartier.nsmul m))
    (Divisor.zeroDivisor_nonneg _ σ hσ) hpb (Divisor.baseLocus_le_supp _ σ hσ hx))

end MMP.FourfoldProofs.Km3aBpfThresholdProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aBpfThresholdProof in
/-- **Tie-breakers exist** (Kollár–Mori 3.2, Step 4). Let `(f; F_•; a_•; p_•; r_•)` be an
`m`-adapted resolution of a basepoint-free datum `(X, Δ, D, a)`, with `m ≥ 1` and `|mD|` not
basepoint free. Then there are rationals `p'_j` such that `(f; F_•; a_•; p'_•; r_•)` is an
`m`-adapted resolution with a tie-breaker `(j', c)`. -/
@[mmp "lem_km3a_bpf_threshold"]
public theorem IsBasepointFreeAdaptedResolution.exists_isBasepointFreeTieBreaker
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj) (hm : 1 ≤ m)
    (hBs : ¬ (m • D).IsBasepointFree) :
    ∃ (p' : Fin s → ℚ) (j' : Fin s) (c : ℚ),
      IsBasepointFreeTieBreaker sX n K Δ D a m f F aj p' rj j' c := by
  haveI := h.isProjectiveVariety
  obtain ⟨j', hj', hmin⟩ := (Finset.univ.filter fun j => 0 < (rj j : ℚ)).exists_min_image
    (fun j => (1 + aj j - pj j) / rj j)
    (let ⟨j, hj⟩ := exists_pos_of_not_isBasepointFree h hBs; ⟨j, by simpa using hj⟩)
  have hrj' : (0 : ℚ) < rj j' := (Finset.mem_filter.1 hj').2
  obtain ⟨hB, B', hB', hA⟩ := h.isAmple
  have hFc : Divisor.IsCartier (Finsupp.single (F j') 1 : Divisor Y) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme
      h.isLogResolution.isSmoothScheme (F j')
  obtain ⟨ε, hε, hamp⟩ := QDivisor.exists_pos_forall_isAmple_add_sum_smul (f ≫ sX) (ι := Unit)
    (fun _ => Divisor.toQDivisor (Finsupp.single (F j') 1)) hA
    (fun _ => QDivisor.isQCartier_toQDivisor hFc)
  -- a rational `η` with `0 < η < ε` and `η < 1 + a_{j'} - p_{j'}`
  obtain ⟨η, hη, hηε⟩ := exists_rat_btwn (show (0 : ℝ) < min ε (1 + aj j' - pj j' : ℚ) from
    lt_min hε (by exact_mod_cast sub_pos.2 (h.lt_one_add j')))
  have hη0 : (0 : ℚ) < η := by exact_mod_cast hη
  have hηa : η < 1 + aj j' - pj j' := by exact_mod_cast hηε.trans_le (min_le_right _ _)
  have hamp' := hamp (fun _ => -η) fun _ => by
    rw [Rat.cast_neg, abs_neg, abs_of_pos hη]; exact hηε.trans_le (min_le_left _ _)
  have hlt := div_mul_lt_one_add_sub (b := aj) (r := fun j => (rj j : ℚ)) h.lt_one_add
    (fun j => Nat.cast_nonneg _) hrj' (fun j hj => hmin j (by simpa using hj)) hη0
  refine ⟨pj + Pi.single j' η, j', (1 + aj j' - pj j' - η) / rj j',
    { h with
      pos_p := fun j => by
        rw [Pi.add_apply, Pi.single_apply]; split_ifs <;> linarith [h.pos_p j]
      lt_one_add := fun j => ?_
      isAmple := ⟨hB, B', hB', ?_⟩ },
    div_pos (by linarith) hrj', by exact_mod_cast hrj', ?_, fun j hj => ?_⟩
  · rcases eq_or_ne j j' with rfl | hj
    · simp only [Pi.add_apply, Pi.single_eq_same]; linarith
    · simpa [Pi.single_eq_of_ne hj] using h.lt_one_add j
  · rw [sum_single_add_piSingle, ← sub_sub]
    simpa [neg_smul, ← sub_eq_add_neg] using hamp'
  · rw [Pi.add_apply, Pi.single_eq_same, neg_mul, div_mul_cancel₀ _ hrj'.ne']; ring
  · rw [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; linarith [hlt j]

end MMP.Mori

end

end
