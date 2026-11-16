module

public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Positivity.NefThresholdConvexity
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum

@[expose] public section

section

/-!
# Adapted resolutions of a rationality datum admit a tie-breaker

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `p, q > 0` integers with
`0 < aq - rp < 1`, and `(f; F_•; a_•; p_•; r_•)` a `(p, q)`-adapted resolution with
`L(p, q) ≠ ∅`. Put `B = pH + (qa - 1)(K_X + Δ)`; it is nef because `0 ≤ qa - 1 < rp`, and so is
its pull-back `f^*B`. Since `L(p, q) = f(⋃_{r_j > 0} F_j)`, some `r_j` is positive.

*Shrinking.* For `N ≥ 1` the divisor `N (f^*B - ∑_j (p_j / N) F_j)` is the ample divisor
`f^*B - ∑_j p_j F_j` plus `N - 1` copies of the nef divisor `f^*B`, hence ample; for `N` large,
`p_j / N < 1 + a_j` for every `j`.

*Tie-breaking.* With `j₀` minimising `(1 + a_j - p_j / N) / r_j` over `{j : r_j > 0}`, raising the
coefficient `p_{j₀} / N` by a small rational `η > 0` keeps the divisor ample and makes `j₀` the
unique minimiser.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 8
-/

open CategoryTheory TopologicalSpace
open AlgebraicGeometry hiding PrimeDivisor

namespace MMP.FourfoldProofs.Km3bStripTieBreakingProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

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
  have := hD.isInvertibleModule_divisorialSheaf
  have := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨L, ⟨a⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨E', ⟨b⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf E.divisorialSheaf
  have hL : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf L) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ a).1 hA
  filter_upwards [MMP.Mori.eventually_isAmple_cartierSheaf_nsmul_add L E' hL] with N hN
  obtain ⟨c⟩ := nonempty_divisorialSheaf_nsmul_add_iso hD hE a b N
  have := ((hD.nsmul N).add hE).isInvertibleModule_divisorialSheaf
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

/-- An ample `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_of_isAmple {A : QDivisor Y} (hA : A.IsAmple) : A.IsQCartier := by
  obtain ⟨m, hm, D, hD, hc, -⟩ := hA
  exact ⟨m, by exact_mod_cast hm.ne', D, by rw [hD, natCast_zsmul, Nat.cast_smul_eq_nsmul], hc⟩

/-- If a positive integral multiple `N A` of a `ℚ`-divisor is ample, so is `A`. -/
private theorem isAmple_of_isAmple_natCast_smul {A : QDivisor Y} {N : ℕ} (hN : 0 < N)
    (h : ((N : ℚ) • A).IsAmple) : A.IsAmple := by
  obtain ⟨m, hm, D, hD, hc, ha⟩ := h
  exact ⟨m * N, Nat.mul_pos hm hN, D, by rw [hD, smul_smul, Nat.cast_mul], hc, ha⟩

end AmpleTwist

section Nef

variable {k : Type} [Field k]

/-- If `H + tK` is nef in the sense of `QDivisor.IsNefCombination` for a rational `t`, then the
`ℚ`-divisor `H + tK` is nef. -/
private theorem isNef_add_smul_of_isNefCombination {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {H K : QDivisor X} {t : ℚ}
    (h : QDivisor.IsNefCombination k sX H K t) : (H + t • K).IsNef k sX := by
  obtain ⟨hH, hK, hC⟩ := h
  have htK : (t • K).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hK t
  have hq : (H + t • K).IsQCartier := hH.add htK
  refine ⟨hq, fun C i _ _ _ hC' => ?_⟩
  have := hC C i hC'
  rw [QDivisor.intersectionNumber_add' k sX i hC'.le H (t • K) hH htK hq,
    MMP.Fourfold.intersectionNumber_smul sX i hC'.le K hK t htK]
  exact_mod_cast this

/-- **The pull-back of a nef `ℚ`-divisor is nef.** For a morphism `u : V ⟶ W` of normal varieties
over `k` and a curve `C ⊆ V`, `(u^*L · C)` is `0` if `u(C)` is a point and a nonnegative multiple
of `(L · u(C))` otherwise. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
    have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
    have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
    have : IsProper ((i ≫ u).imageι ≫ sW) := isProper_imageι_comp (i ≫ u) sW
    have hcurve : AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) :=
      isCurve_imageι_comp sW (i ≫ u) hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- **The strip divisor below the threshold is nef.** For a rationality datum `(X, Δ, a, H)` with
nef threshold `r` and integers `p, q > 0` with `aq - rp < 1`, the `ℚ`-divisor
`pH + (qa - 1)(K_X + Δ)` is nef, because `0 ≤ qa - 1 < rp`. -/
private theorem isNef_smul_add_sub_one_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} (hD : IsRationalityDatum sX n K Δ a H)
    {r : ℝ} (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    {p q : ℤ} (hp : 0 < p) (hq : 0 < q) (hpq : (a * q : ℝ) - r * p < 1) :
    (p • Divisor.toQDivisor H + (q * a - 1) • (Divisor.toQDivisor K + Δ)).IsNef k sX := by
  have hq1 : (1 : ℝ) ≤ q * a := by exact_mod_cast one_le_mul_of_one_le_of_one_le hq hD.pos
  have := isNef_add_smul_of_isNefCombination <|
    MMP.Positivity.IsRationalityDatum.isNefCombination_of_le hD hr (x := p) (by exact_mod_cast hp)
      (t := (((q * a - 1 : ℤ) : ℚ) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
  rwa [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul] at this

end Nef

section Shrinking

variable {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
  [MMP.Mori.IsProjectiveVariety k sY] [IsNormal Y] [IsLocallyNoetherian Y] [CompactSpace Y]
  [QuasiCompact sY]

/-- **Shrinking the coefficients.** If `B` is nef and `B - ∑_j p_j F_j` is ample, then so is
`B - ∑_j (p_j / N) F_j` for every integer `N ≥ 1`: `N` times it is the ample divisor
`B - ∑_j p_j F_j` plus `N - 1` copies of `B`. -/
private theorem isAmple_sub_sum_single_div {ι : Type*} [Fintype ι] (F : ι → PrimeDivisor Y)
    (p : ι → ℚ) {B : QDivisor Y} (hB : B.IsNef k sY)
    (hA : (B - ∑ j, Finsupp.single (F j) (p j)).IsAmple) {N : ℕ} (hN : 0 < N) :
    (B - ∑ j, Finsupp.single (F j) (p j / N)).IsAmple := by
  refine isAmple_of_isAmple_natCast_smul hN ?_
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN.ne'
  have heq : ((M + 1 : ℕ) : ℚ) • (B - ∑ j, Finsupp.single (F j) (p j / (M + 1 : ℕ))) =
      (B - ∑ j, Finsupp.single (F j) (p j)) + ∑ _i ∈ Finset.range M, B := by
    rw [Finset.sum_const, Finset.card_range, smul_sub, Finset.smul_sum]
    have hM : (M + 1 : ℚ) ≠ 0 := by positivity
    simp only [Finsupp.smul_single, smul_eq_mul, Nat.cast_succ, mul_div_cancel₀ _ hM]
    rw [← Nat.cast_smul_eq_nsmul ℚ, add_smul, one_smul]
    abel
  rw [heq]
  exact QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sY _ (fun _ => B) hA
    (fun _ _ => hB) (.refl ((isQCartier_of_isAmple hA).add
      (MMP.Flips.QDivisor.isQCartier_sum _ _ fun _ _ => hB.1)))

end Shrinking

/-- Finitely many rationals `p_j` become smaller than given positive bounds `c_j` after division
by a suitable integer `N ≥ 1`. -/
private theorem exists_div_lt {ι : Type*} [Finite ι] (p : ι → ℚ) {c : ι → ℚ}
    (hc : ∀ j, 0 < c j) : ∃ N : ℕ, 0 < N ∧ ∀ j, p j / N < c j :=
  ((Filter.eventually_gt_atTop 0).and <| Filter.eventually_all.2 fun j =>
    (tendsto_const_div_atTop_nhds_zero_nat (p j)).eventually (gt_mem_nhds (hc j))).exists

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

end MMP.FourfoldProofs.Km3bStripTieBreakingProof

end

section

/-!
# Adapted resolutions of a rationality datum admit a tie-breaker

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, let `p, q > 0` be integers with `0 < aq - rp < 1`, and let
`(f; F_1, …, F_s; a_•; p_•; r_•)` be a `(p, q)`-adapted resolution whose strip base locus
`L(p, q)` is nonempty. Replacing the rationals `p_j` by suitable `p'_j` (in the proof: first
scaling them by a small `λ ∈ (0, 1]`, which keeps `f^*(pH + (qa - 1)(K_X + Δ)) - ∑_j p_j F_j`
ample because `f^*(pH + (qa - 1)(K_X + Δ))` is nef, then enlarging a single `p_{j₀}` by a small
amount), one obtains again a `(p, q)`-adapted resolution, now with `p'_j < 1 + a_j` for all `j`
and such that `j ↦ (1 + a_j - p'_j) / r_j` has a unique minimiser `j₀` on `{j : r_j > 0}`; with
`c` its minimum, `(j₀, c)` is a tie-breaker.

## Main results

* `MMP.Mori.IsStripAdaptedResolution.exists_isStripTieBreaker`: every `(p, q)`-adapted
  resolution with `0 < aq - rp < 1` and `L(p, q) ≠ ∅` becomes, after changing only the `p_j`, a
  `(p, q)`-adapted resolution with a tie-breaker.

## Implementation notes

A tie-breaker `MMP.Mori.IsStripTieBreaker` extends `MMP.Mori.IsStripAdaptedResolution`, so the
single conclusion `IsStripTieBreaker … p' r j₀ c` says both that the tuple with `p'` is a
`(p, q)`-adapted resolution and that `(j₀, c)` is a tie-breaker for it. The strip base locus is
a closed subset of `X`, and `L(p, q) ≠ ∅` is `stripBaseLocus K Δ a H p q ≠ ⊥`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 8
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripTieBreakingProof in
/-- **Tie-breakers exist for the rationality theorem** (Kollár–Mori 3.4, Step 8). Let
`(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to `K_X + Δ`,
`p, q > 0` integers with `0 < aq - rp < 1`, and `(f; F_•; a_•; p_•; r_•)` a `(p, q)`-adapted
resolution with `L(p, q) ≠ ∅`. Then there are rationals `p'_1, …, p'_s` such that
`(f; F_•; a_•; p'_•; r_•)` is a `(p, q)`-adapted resolution which admits a tie-breaker
`(j₀, c)`. -/
@[mmp "lem_km3b_strip_tie_breaking"]
public theorem IsStripAdaptedResolution.exists_isStripTieBreaker
    {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (_hpq₀ : 0 < (a * q : ℝ) - r * p) (hpq₁ : (a * q : ℝ) - r * p < 1)
    (hL : stripBaseLocus K Δ a H p q ≠ ⊥) :
    ∃ (pj' : Fin s → ℚ) (j₀ : Fin s) (c : ℚ),
      IsStripTieBreaker sX n K Δ a H p q f F aj pj' rj j₀ c := by
  have : IsIntegral Y := h.isProjectiveVariety.toIsIntegral
  have := h.isProperVariety.toIsVariety
  have := h.isProjectiveVariety.toIsVariety
  have := h.isProjectiveVariety
  -- some `r_j` is positive, since `L(p, q) = f(⋃_{r_j > 0} F_j)` is nonempty
  obtain ⟨j₁, hj₁⟩ : ∃ j, 0 < rj j := by
    by_contra hne
    push Not at hne
    apply hL
    ext1
    rw [h.stripBaseLocus_eq_image]
    simp [fun j => Nat.le_zero.1 (hne j)]
  -- shrinking: `p''_j = p_j / N` with `p''_j < 1 + a_j`, and `f^*B - ∑ p''_j F_j` still ample
  obtain ⟨hB, B', hpb, hamp⟩ := h.isAmple
  obtain ⟨N, hN, hM'⟩ := exists_div_lt pj fun j => (by linarith [h.neg_one_lt j] : 0 < 1 + aj j)
  set p'' : Fin s → ℚ := fun j => pj j / N
  have hamp'' := isAmple_sub_sum_single_div F pj (isNef_of_isPullback rfl
    (isNef_smul_add_sub_one_smul h.toIsRationalityDatum hr h.pos_p h.pos_q hpq₁) hpb) hamp hN
  -- the minimiser `j₀` of `(1 + a_j - p''_j) / r_j` over `{j : r_j > 0}`
  obtain ⟨j₀, hj₀, hmin⟩ := (Finset.univ.filter fun j => 0 < rj j).exists_min_image
    (fun j => (1 + aj j - p'' j) / rj j) ⟨j₁, by simpa using hj₁⟩
  have hrj₀ : (0 : ℚ) < rj j₀ := by exact_mod_cast (Finset.mem_filter.1 hj₀).2
  -- tie-breaking: raise `p''_{j₀}` by a small `η`
  obtain ⟨η, hη, hηε, hamp'⟩ := exists_isAmple_sub_smul hamp''
    (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme
      h.isLogResolution.isSmoothScheme (F j₀)) (sub_pos.2 (hM' j₀))
  have hlt := div_mul_lt_one_add_sub (b := aj) (p := p'') (r := fun j => (rj j : ℚ)) hM'
    (fun j => by positivity) hrj₀ (fun j hj => hmin j (by simpa using hj)) hη
  refine ⟨p'' + Pi.single j₀ η, j₀, (1 + aj j₀ - p'' j₀ - η) / rj j₀,
    { h with
      pos_p' := fun j => ?_
      isAmple := ⟨hB, B', hpb, by rwa [sum_single_add_piSingle, ← sub_sub]⟩
      lt_one_add := fun j => ?_
      pos_r := by exact_mod_cast hrj₀
      eq_div := ?_
      lt_div := fun j hj hrj => ?_ }⟩
  · have := h.pos_p' j
    rw [Pi.add_apply, Pi.single_apply]
    split_ifs <;> positivity
  · rcases eq_or_ne j j₀ with rfl | hj
    · simp only [Pi.add_apply, Pi.single_eq_same]; linarith
    · simpa [Pi.single_eq_of_ne hj] using hM' j
  · rw [Pi.add_apply, Pi.single_eq_same]; ring
  · rw [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, lt_div_iff₀ (by exact_mod_cast hrj)]
    exact hlt j

end MMP.Mori

end
