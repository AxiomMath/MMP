module

public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous

section

/-!
## Auxiliary lemmas for the ample perturbation theorem

Let `A` be an ample `ℚ`-divisor and `E j` finitely many `ℚ`-Cartier `ℚ`-divisors on a normal
projective variety `Y`. For each `j` there is `c j > 0` with `A ± c j • E j` ample: write
`mA = D` with `𝒪(D)` ample and `n E j = F` Cartier, and take `N` so large that `N D ± F` is ample.
Then `A · C ≥ c j |E j · C|` for every curve `C`, since `A ± c j • E j` is nef. With
`c₀ = min_j c j`, `n = |ι| + 1` and `|t j| < c₀ / n`, each `A / n + t j • E j` is nef, and
`A + ∑ t j • E j = A / n + ∑ (A / n + t j • E j)` is ample plus nef, hence ample.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.1
-/

namespace MMP.FourfoldProofs.Km3aAmplePerturbationProof

open CategoryTheory AlgebraicGeometry MMP.Mori

section AmpleTwist

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- If `𝒪_Y(D) ≅ 𝒪(L)` and `𝒪_Y(E) ≅ 𝒪(E')` for Cartier divisors `L`, `E'`, then
`𝒪_Y(N • D + E) ≅ 𝒪(N • L + E')` for every `N : ℕ`. -/
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

/-- **Ample twists.** On an integral, locally Noetherian, normal scheme with compact underlying
space, if `D` and `E` are Cartier divisors with `𝒪(D)` ample, then `𝒪(ND + E)` is ample for all
large `N`. -/
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

/-- `(1 / b) A` is ample when `A` is, for `b > 0`. -/
private theorem isAmple_inv_natCast_smul {A : QDivisor Y} (hA : A.IsAmple) {b : ℕ}
    (hb : 0 < b) : (((b : ℚ)⁻¹) • A).IsAmple := by
  obtain ⟨m, hm, D, hDe, hDc, hDa⟩ := hA
  refine ⟨b * m, Nat.mul_pos hb hm, D, ?_, hDc, hDa⟩
  have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hDe, smul_smul, Nat.cast_mul, mul_assoc, mul_comm (m : ℚ), ← mul_assoc,
    mul_inv_cancel₀ this, one_mul]

/-- For an ample `A` and a `ℚ`-Cartier `E`, both `A + c E` and `A - c E` are ample for some
rational `c > 0`. -/
private theorem exists_pos_isAmple_add_smul [IsIntegral Y] {A E : QDivisor Y} (hA : A.IsAmple)
    (hE : E.IsQCartier) :
    ∃ c : ℚ, 0 < c ∧ (A + c • E).IsAmple ∧ (A + (-c) • E).IsAmple := by
  obtain ⟨m, hm, D, hDe, hDc, hDa⟩ := hA
  obtain ⟨n, hn, F, hF, hFc⟩ := hE.exists_pos
  obtain ⟨N, h₁, h₂, hN⟩ := ((eventually_isAmple_nsmul_add hDc hFc hDa).and
    ((eventually_isAmple_nsmul_add hDc hFc.neg hDa).and (Filter.eventually_gt_atTop 0))).exists
  have hNm : ((N * m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hm).ne'
  have key : ∀ σ : ℚ, ((N * m : ℕ) : ℚ) • (A + (σ * (n / (N * m : ℕ))) • E) =
      Divisor.toQDivisor (N • D) + σ • Divisor.toQDivisor F := by
    intro σ
    rw [map_nsmul, hDe, hF, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_add,
      smul_smul, smul_smul, smul_smul, Int.cast_natCast, Nat.cast_mul]
    congr 2
    field_simp
  refine ⟨n / (N * m : ℕ), by positivity, ⟨N * m, Nat.mul_pos hN hm, N • D + F, ?_, _, h₁⟩,
    ⟨N * m, Nat.mul_pos hN hm, N • D + -F, ?_, _, h₂⟩⟩
  · rw [← one_mul ((n : ℚ) / _), key, one_smul, map_add]
  · rw [neg_eq_neg_one_mul, key, neg_one_smul, map_add, map_neg]

end AmpleTwist

section Nef

variable {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-- If `A ± c E` are nef, `c > 0` and `|t| ≤ q c`, then `q A + t E` is nef. -/
private theorem isNef_smul_add_smul {A E : QDivisor Y} (hA : A.IsQCartier) (hE : E.IsQCartier)
    {c q t : ℚ} (hc : 0 < c) (hp : (A + c • E).IsNef k sY) (hm : (A + (-c) • E).IsNef k sY)
    (ht : |t| ≤ q * c) : (q • A + t • E).IsNef k sY := by
  have hq : ∀ r : ℚ, (r • E).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hE
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hm⟩ := hm
  refine ⟨(MMP.Flips.QDivisor.IsQCartier.qsmul hA q).add (hq t), fun C i _ _ _ hC => ?_⟩
  have ep := hp C i hC
  have em := hm C i hC
  rw [QDivisor.intersectionNumber_add' k sY i hC.le _ _ hA (hq _),
    MMP.Fourfold.intersectionNumber_smul sY i hC.le E hE] at ep em
  rw [QDivisor.intersectionNumber_add' k sY i hC.le _ _
      (MMP.Flips.QDivisor.IsQCartier.qsmul hA q) (hq _),
    MMP.Fourfold.intersectionNumber_smul sY i hC.le E hE,
    MMP.Fourfold.intersectionNumber_smul sY i hC.le A hA]
  set a := A.intersectionNumber k sY i hC.le hA
  set e := E.intersectionNumber k sY i hC.le hE
  obtain ⟨ht₁, ht₂⟩ := abs_le.1 ht
  have : 0 ≤ c * (q * a + t * e) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ q * c + t) ep,
      mul_nonneg (by linarith : 0 ≤ q * c - t) em]
  exact (mul_nonneg_iff_of_pos_left hc).1 this

end Nef

/-- With `n = |ι| + 1`, `A + ∑ v j = A / n + ∑ (A / n + v j)`. -/
private theorem add_sum_eq_inv_smul_add_sum {M : Type*} [AddCommGroup M] [Module ℚ M]
    {ι : Type*} [Fintype ι] (A : M) (v : ι → M) :
    A + ∑ j, v j = ((Fintype.card ι + 1 : ℕ) : ℚ)⁻¹ • A +
      ∑ j, (((Fintype.card ι + 1 : ℕ) : ℚ)⁻¹ • A + v j) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, ← add_assoc, ← add_smul]
  congr 1
  convert (one_smul ℚ A).symm using 2
  push_cast
  field_simp
  ring

end MMP.FourfoldProofs.Km3aAmplePerturbationProof

end

section

/-!
# Small perturbations of an ample `ℚ`-divisor are ample

Let `Y` be a normal projective variety over a field `k`, `A` an ample `ℚ`-divisor and
`E j` (`j : ι`, a finite index type) `ℚ`-Cartier `ℚ`-divisors on `Y`. Then there is a real
`η > 0` such that `A + ∑ j, t j • E j` is ample for every family of rationals `t` with
`|t j| < η` for all `j`. Ampleness is open in the space of `ℚ`-Cartier `ℚ`-divisors.

## Main results

* `MMP.Mori.QDivisor.exists_pos_forall_isAmple_add_sum_smul`

## Implementation notes

The divisors `E₁, …, E_s` are a family `E : ι → QDivisor Y` over a `Fintype` `ι`; `ι = Fin s`
is the source's form and `ι` empty is the case `s = 0`. Ampleness `QDivisor.IsAmple` already
contains `ℚ`-Cartierness of `A`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

namespace QDivisor

open MMP.FourfoldProofs.Km3aAmplePerturbationProof in
/-- **Ample perturbation.** On a normal projective variety `Y` over a field `k`, let `A` be an
ample `ℚ`-divisor and `E j` (`j : ι`, finite) `ℚ`-Cartier `ℚ`-divisors. Then there is a real
`η > 0` such that `A + ∑ j, t j • E j` is ample whenever `|t j| < η` for all `j`. -/
@[mmp "lem_km3a_ample_perturbation"]
public theorem exists_pos_forall_isAmple_add_sum_smul {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] [IsNormal Y]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    {ι : Type*} [Fintype ι] {A : QDivisor Y} (E : ι → QDivisor Y) (hA : A.IsAmple)
    (hE : ∀ j, (E j).IsQCartier) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ι → ℚ, (∀ j, |(t j : ℝ)| < η) →
      (A + ∑ j, t j • E j).IsAmple := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun t _ => by simpa using hA⟩
  choose c hc hcp hcm using fun j => exists_pos_isAmple_add_smul hA (hE j)
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min c
  set n := Fintype.card ι + 1 with hn
  have hAn := isAmple_inv_natCast_smul hA (Nat.succ_pos _ : 0 < n)
  refine ⟨((c j₀ / n : ℚ) : ℝ), by have := hc j₀; positivity, fun t ht => ?_⟩
  have hnef (j : ι) : ((n : ℚ)⁻¹ • A + t j • E j).IsNef k sY := by
    refine isNef_smul_add_smul sY (QDivisor.isNef_and_isBig_of_isAmple sY hA).1.isQCartier (hE j)
      (hc j)
      (QDivisor.isNef_and_isBig_of_isAmple sY (hcp j)).1
      (QDivisor.isNef_and_isBig_of_isAmple sY (hcm j)).1 ?_
    have h := ht j
    rw [← Rat.cast_abs, Rat.cast_lt] at h
    rw [inv_mul_eq_div]
    exact h.le.trans (div_le_div_of_nonneg_right (hj₀ j) (by positivity))
  rw [add_sum_eq_inv_smul_add_sum, ← hn]
  exact QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sY Finset.univ _ hAn
    (fun j _ => hnef j) (QDivisor.NumericallyEquivalent.refl
      ((QDivisor.isNef_and_isBig_of_isAmple sY hAn).1.isQCartier.add
        (MMP.Flips.QDivisor.isQCartier_sum _ _ fun j _ => (hnef j).isQCartier)))

end QDivisor

end MMP.Mori

end
