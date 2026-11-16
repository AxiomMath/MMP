module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.TieBreakerNotInBaseLocus
public import MMP.AlgebraicGeometry.MMP.BasepointFree.SectionsExist
public import MMP.AlgebraicGeometry.MMP.BasepointFree.TieBreaker

@[expose] public section

section

/-! ## The image of the tie-breaker divisor lies in `Bs|mD|` -/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aBpfStableBaseLocusEmptyProof

/-- The coefficient of `F i` in `∑ j, r_j F_j` is `r_i`, for an injective family `F`. -/
private theorem coeff_sum_single {Y : Scheme.{0}} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    (hF : Function.Injective F) (r : Fin s → ℤ) (i : Fin s) :
    DivisorWithCoeffs.coeff (∑ j, Finsupp.single (F j) (r j) : Divisor Y) (F i) = r i := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
    Finset.sum_eq_single i (fun j _ hj => Finsupp.single_eq_of_ne' (hF.ne hj)) (by simp)]
  simp

/-- For a tie-breaker `(j', c)` of an `m`-adapted resolution, `f(F_{j'}) ⊆ Bs|mD|`. -/
private theorem image_subset_baseLocus {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c) :
    f.base '' (F j').support ⊆ ((m • D).baseLocus : Set X) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Divisor.mem_baseLocus_iff]
  intro σ hσ
  obtain ⟨hB, Z', hpb, hle⟩ := h.le_zeroDivisor σ hσ
  have hcoeff := hle (F j')
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
    coeff_sum_single h.injective] at hcoeff
  have hpos := h.pos_r
  have hyZ : y ∈ (Z'.supp : Set Y) :=
    DivisorWithCoeffs.mem_supp_iff.mpr ⟨F j', by omega, hy⟩
  rwa [MMP.Flips.supp_eq_preimage_supp_of_isPullback
    ((Divisor.isCartier_principalDivisor _).add (h.isCartier.nsmul m))
    (Divisor.zeroDivisor_nonneg _ σ hσ) hpb] at hyZ

end MMP.FourfoldProofs.Km3aBpfStableBaseLocusEmptyProof

end

section

/-!
# The stable base loci of a basepoint-free datum are empty

Let `(X, Δ, D, a)` be a basepoint-free datum over an algebraically closed field of
characteristic zero. For every integer `s ≥ 2`, the stable base locus
`B_s = ⋂_{u ≥ 1} Bs|sᵘ D|` is empty. If it were not, then for `m = sᵘ` large, `H⁰(X, mD) ≠ 0`
and `Bs|mD| = B_s`; an `m`-adapted resolution with a tie-breaker `(j', c)` would give a prime
divisor `F = F_{j'}` with `f(F) ⊆ Bs|mD| = B_s`, whereas `f(F) ⊄ Bs|bD|` for all large `b`, in
particular for `b = sᵘ`.

## Main results

* `MMP.Mori.IsBasepointFreeDatum.stableBaseLocusOfPowers_eq_bot`: `B_s = ∅` for every `s ≥ 2`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Steps 2–5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **The stable base loci of a basepoint-free datum are empty** (Kollár–Mori 3.2, Steps 2–5).
Let `(X, Δ, D, a)` be a basepoint-free datum over an algebraically closed field `k` of
characteristic zero. Then for every `s ≥ 2` the stable base locus
`D.stableBaseLocusOfPowers s = ⋂_{u ≥ 1} Bs|sᵘ D|` is empty. -/
@[mmp "lem_km3a_bpf_stable_base_locus_empty"]
public theorem IsBasepointFreeDatum.stableBaseLocusOfPowers_eq_bot
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ}
    (h : IsBasepointFreeDatum sX n K Δ D a) {s : ℕ} (hs : 2 ≤ s) :
    D.stableBaseLocusOfPowers s = ⊥ := by
  by_contra hne
  obtain ⟨u₀, -, hu₀⟩ := Divisor.exists_baseLocusOfMultiple_pow_eq_stableBaseLocusOfPowers D s
  obtain ⟨m₀, hm₀⟩ := h.exists_section_ne_zero_nsmul
  have hpow : ∀ u, u < s ^ u := fun u => Nat.lt_pow_self (by omega)
  set u₁ := max u₀ m₀
  have hBm : ((s ^ u₁) • D).baseLocus = D.stableBaseLocusOfPowers s := hu₀ u₁ (le_max_left _ _)
  obtain ⟨Y, _, _, _, f, t, F, aj, pj, rj, hres⟩ :=
    h.exists_isBasepointFreeAdaptedResolution (hm₀ _ ((le_max_right _ _).trans (hpow u₁).le))
  obtain ⟨p', j', c, ht⟩ := hres.exists_isBasepointFreeTieBreaker
    (Nat.one_le_pow _ _ (by omega)) (fun hbf => hne (hBm ▸ hbf))
  obtain ⟨b₂, hb₂⟩ := ht.exists_forall_not_image_subset_baseLocus
  set u := max u₁ b₂.toNat
  refine hb₂ (s ^ u : ℕ) (by have := hpow u; have := le_max_right u₁ b₂.toNat; omega) ?_
  rw [natCast_zsmul]
  change _ ⊆ ((D.baseLocusOfMultiple (s ^ u) : _) : Set X)
  rw [hu₀ u ((le_max_left _ _).trans (le_max_left _ _)), ← hBm]
  exact MMP.FourfoldProofs.Km3aBpfStableBaseLocusEmptyProof.image_subset_baseLocus ht

end MMP.Mori

end
