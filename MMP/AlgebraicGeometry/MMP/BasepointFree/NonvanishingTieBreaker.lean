module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity

@[expose] public section

section

/-!
# Adapted resolutions of a non-vanishing datum admit a tie-breaker

For an adapted resolution `(x, q, e, M; f; F_•; b_•; p_•; r_•)` of a smooth non-vanishing datum
`(X, D, G, a)` of dimension `d`, let `J = {j : r_j > 0}` and `γ_j = (1 + b_j - p_j) / r_j`. Choose
`j' ∈ J` minimising `γ`, and enlarge `p_{j'}` by a small rational `η > 0` keeping
`½ f^*(aD + G - K_X) - ∑_j p_j F_j - η F_{j'}` ample. Then `j'` is the unique minimiser of the new
ratios, and with `c` the new minimum, `(j', c)` is a tie-breaker.

The ampleness of the perturbation comes from the fact that on an integral, locally Noetherian,
normal, quasi-compact scheme, for Cartier divisors `D` (with `𝒪(D)` ample) and `E`, the sheaf
`𝒪(ND + E)` is ample for all large `N`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5 Step 5
-/

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

namespace MMP.FourfoldProofs.Km3aNonvanishingThresholdProof

open MMP.Mori

section AmpleTwist

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- If `𝒪_Y(D) ≅ 𝒪(L)` and `𝒪_Y(E) ≅ 𝒪(E')` for Cartier divisors `L`, `E'`, then
`𝒪_Y(ND + E) ≅ 𝒪(NL + E')`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {D E : Divisor Y} (hD : D.IsCartier)
    (hE : E.IsCartier) {L E' : Y.CartierDivisor}
    (a : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf L)
    (b : E.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E') (N : ℕ) :
    Nonempty ((N • D + E).divisorialSheaf ≅
      MMP.CartierDivisor.sheaf (N • L + E')) := by
  induction N with
  | zero => exact ⟨eqToIso (by simp) ≪≫ b ≪≫ eqToIso (by simp)⟩
  | succ N ih =>
    obtain ⟨c⟩ := ih
    have h₁ : (N + 1 : ℕ) • D + E = (N • D + E) + D := by rw [succ_nsmul]; abel
    have h₂ : (N • L + E') + L = (N + 1 : ℕ) • L + E' := by rw [succ_nsmul]; abel
    exact ⟨eqToIso (by rw [h₁]) ≪≫ (((hD.nsmul N).add hE).divisorialSheafTensorIso hD).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso c).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso a ≪≫
      MMP.CartierDivisorSheaf.sheafMulIso _ _ ≪≫ eqToIso (by rw [h₂])⟩

/-- **Ample twists.** On an integral, locally Noetherian, normal, quasi-compact scheme, if `D`
and `E` are Cartier divisors with `𝒪(D)` ample, then `𝒪(ND + E)` is ample for all large `N`. -/
private theorem eventually_isAmple_nsmul_add [IsIntegral Y] {D E : Divisor Y} (hD : D.IsCartier)
    (hE : E.IsCartier) (hA : D.IsAmple hD) :
    ∀ᶠ N : ℕ in Filter.atTop, (N • D + E).IsAmple ((hD.nsmul N).add hE) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨L, ⟨a⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨E', ⟨b⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf E.divisorialSheaf
  have hL : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf L) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ a).1 hA
  filter_upwards [MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add L E' hL] with N hN
  obtain ⟨c⟩ := nonempty_divisorialSheaf_nsmul_add_iso hD hE a b N
  haveI := ((hD.nsmul N).add hE).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ c).2 hN

/-- **Perturbing an ample `ℚ`-divisor.** If `A` is an ample `ℚ`-divisor and `P` a Cartier
divisor on an integral, locally Noetherian, normal, quasi-compact scheme, then `A - ηP` is ample
for some arbitrarily small rational `η > 0`. -/
private theorem exists_isAmple_sub_smul [IsIntegral Y] {A : QDivisor Y} (hA : A.IsAmple)
    {P : Divisor Y} (hP : P.IsCartier) {ε : ℚ} (hε : 0 < ε) :
    ∃ η : ℚ, 0 < η ∧ η < ε ∧ (A - η • Divisor.toQDivisor P).IsAmple := by
  obtain ⟨m, hm, D, hDe, hDc, hDa⟩ := hA
  obtain ⟨N, hN, hNε⟩ := ((eventually_isAmple_nsmul_add hDc hP.neg hDa).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop ((1 : ℚ) / (m * ε)))).exists
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hmε : 0 < (m : ℚ) * ε := mul_pos hm' hε
  have hN0 : (0 : ℚ) < N := lt_trans (by positivity) hNε
  refine ⟨1 / (m * N), by positivity, ?_, m * N, Nat.mul_pos hm (by exact_mod_cast hN0),
    N • D + -P, ?_, _, hN⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hmε] at hNε
    nlinarith
  · rw [map_add, map_nsmul, map_neg, hDe, smul_sub, smul_smul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, sub_eq_add_neg]
    congr 1
    · rw [Nat.cast_mul, mul_comm]
    · rw [Nat.cast_mul, mul_one_div_cancel (by positivity), one_smul]

end AmpleTwist

/-- **Raising one `p` breaks the tie.** Let `j'` minimise `(1 + b_j - p_j) / r_j` over the
indices with `r_j > 0`, and suppose `p_j < 1 + b_j` and `r_j ≥ 0` for all `j`. For `η > 0` and
`c = (1 + b_{j'} - p_{j'} - η) / r_{j'}`, every index (including `j'`) has
`c r_j < 1 + b_j - p_j`. -/
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

end MMP.FourfoldProofs.Km3aNonvanishingThresholdProof

end

section

/-!
# Adapted resolutions of a non-vanishing datum admit a tie-breaker

Let `(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)` be an adapted resolution of a smooth
non-vanishing datum `(X, D, G, a)` of dimension `d`. Replacing the rationals `p_j` by suitable
`p'_j` (in the proof, enlarging a single `p_{j'}` by a small `η > 0`, which keeps
`½ f^*(aD + G - K_X) - ∑_j p'_j F_j` ample), one obtains again an adapted resolution, and the
function `j ↦ (1 + b_j - p'_j) / r_j` on `{j : r_j > 0}` has a unique minimiser `j'`. Its minimum
`c` then satisfies `0 < c < ½`, and `(j', c)` is a tie-breaker.

## Main results

* `MMP.Mori.IsNonvanishingAdaptedResolution.exists_isNonvanishingTieBreaker`: every adapted
  resolution becomes, after changing only the `p_j`, an adapted resolution with a tie-breaker.

## Implementation notes

A tie-breaker `MMP.Mori.IsNonvanishingTieBreaker` extends
`MMP.Mori.IsNonvanishingAdaptedResolution`, so the single conclusion
`IsNonvanishingTieBreaker … p' r j' c` says both that the tuple with `p'` is an adapted
resolution and that `(j', c)` is a tie-breaker for it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **Tie-breakers exist** (Kollár–Mori 3.5, Step 5). For an adapted resolution
`(x, q, e, M; f; F_•; b_•; p_•; r_•)` of a smooth non-vanishing datum `(X, D, G, a)` there are
rationals `p'_0, …, p'_s` such that `(x, q, e, M; f; F_•; b_•; p'_•; r_•)` is again an adapted
resolution and has a tie-breaker `(j', c)`. -/
@[mmp "lem_km3a_nonvanishing_threshold"]
public theorem IsNonvanishingAdaptedResolution.exists_isNonvanishingTieBreaker
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ} {M : QDivisor X}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin (s + 1) → PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    (h : IsNonvanishingAdaptedResolution sX n K D G a x q e M f F b p r) :
    ∃ (p' : Fin (s + 1) → ℚ) (j' : Fin (s + 1)) (c : ℚ),
      IsNonvanishingTieBreaker sX n K D G a x q e M f F b p' r j' c := by
  haveI : IsIntegral Y := h.isProjectiveVariety_source.toIsIntegral
  have hr0 : (2 * n : ℚ) < r 0 := h.multiplicityAt_gt.trans_le h.multiplicityAt_le
  obtain ⟨j', hj', hmin⟩ := (Finset.univ.filter fun j => 0 < r j).exists_min_image
    (fun j => (1 + b j - p j) / r j)
    ⟨0, by simpa using (by positivity : (0 : ℚ) ≤ 2 * n).trans_lt hr0⟩
  have hrj' : 0 < r j' := (Finset.mem_filter.1 hj').2
  obtain ⟨hB, B', hB', hA⟩ := h.isAmple_half
  obtain ⟨η, hη, hηε, hamp⟩ :=
    MMP.FourfoldProofs.Km3aNonvanishingThresholdProof.exists_isAmple_sub_smul hA
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme
        h.isLogResolution.isSmoothScheme (F j')) (sub_pos.2 (h.lt_one_add j'))
  have hlt := MMP.FourfoldProofs.Km3aNonvanishingThresholdProof.div_mul_lt_one_add_sub h.lt_one_add
    h.nonneg_r hrj' (fun j hj => hmin j (by simpa using hj)) hη
  refine ⟨p + Pi.single j' η, j', (1 + b j' - p j' - η) / r j',
    { h with
      pos_p := fun j => by
        rw [Pi.add_apply, Pi.single_apply]; split_ifs <;> linarith [h.pos_p j]
      lt_one_add := fun j => ?_
      isAmple_half := ⟨hB, B', hB', by
        rwa [MMP.FourfoldProofs.Km3aNonvanishingThresholdProof.sum_single_add_piSingle, ← sub_sub]⟩ },
    div_pos (by linarith) hrj', ?_, hrj', ?_, fun j hj => ?_⟩
  · rcases eq_or_ne j j' with rfl | hj
    · simp only [Pi.add_apply, Pi.single_eq_same]; linarith
    · simpa [Pi.single_eq_of_ne hj] using h.lt_one_add j
  · nlinarith [hlt 0, h.pos_p 0, h.b_zero_le, (by exact_mod_cast h.one_le_dim : (1 : ℚ) ≤ n)]
  · rw [Pi.add_apply, Pi.single_eq_same, neg_mul, div_mul_cancel₀ _ hrj'.ne']; ring
  · rw [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]; linarith [hlt j]

end MMP.Mori

end

end
