module
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.CommonRayCurveBound

/-!
# A uniform positive gap for intersection numbers of a weighted adjoint

Let `X` be a normal `ℚ`-factorial projective complex threefold with canonical divisor `K_X`, let
`B₁, …, B_s` be effective `ℚ`-divisors with every `(X, Bᵢ)` klt, let `rᵢ > 0` be real weights with
`∑ rᵢ = 1`, and let `m > 0` be an integer with every `m(K_X + Bᵢ)` an integral Cartier divisor.
Put `Dᵢ = K_X + Bᵢ` and `D = ∑ rᵢ Dᵢ`. There is a `τ > 0`, depending only on `m` and the
weights `rᵢ` (and not on `X` or the `Bᵢ`), such that every extremal ray `R` of `NE̅(X)` that is
negative for some real klt adjoint contains the class of a rational curve `C` with
`Dᵢ · C ≥ -6` for every `i` and with either `D · C ≤ 0` or `D · C ≥ τ`.

Writing `Dᵢ · C = nᵢ / m` with `nᵢ ∈ ℤ`, the bounds `nᵢ ≥ -6m` and `∑ rᵢ nᵢ ≤ m` confine every
`nᵢ` to a finite set, so the positive values of `D · C` that are at most one form a finite set,
and `τ` is its minimum (or `1` when it is empty).

## Main results

* `MMP.Fourfold.exists_pos_forall_exists_isRationalCurve_neg_six_le_and_le_zero_or_le`.

## Implementation notes

The weights are indexed by an arbitrary finite type `ι`, and `τ` is produced before the
threefold: the statement quantifies over every threefold `X` (in `Scheme.{0}`), every family of
rational klt boundaries `B : ι → ℚ`-divisors and every ray, which is the uniformity of the source.
The Cartier index is witnessed by Cartier divisors `Lᵢ` with `Lᵢ = m (K + Bᵢ)` coefficientwise,
and `Dᵢ · C` is `(𝒪_X(Lᵢ) · C) / m`, computed with `MMP.Mori.NumericalCurveClasses.degree`; this
is `MMP.Fourfold.QDivisor.curveForm` of `K + Bᵢ`. The real klt adjoint `K + B'` making `R`
negative is paired with `R` through a Cartier presentation `K + B' = ∑ cⱼ Mⱼ`, as in
`MMP.Fourfold.exists_isRationalCurve_numericalClass_mem_and_neg_six_le`. The dimension of `X` is
the `3` of `MMP.Mori.Divisor.IsCanonicalDivisor`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The arithmetic gap: for positive weights `rᵢ` summing to one and `m > 0`, the positive values
of `∑ rᵢ nᵢ / m` over integer vectors with `nᵢ / m ≥ -6` are bounded below by some `τ > 0`. -/
private theorem exists_pos_le_sum {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hr1 : ∑ i, r i = 1) (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ n : ι → ℤ, (∀ i, -6 ≤ (n i : ℝ) / m) →
      0 < ∑ i, r i * ((n i : ℝ) / m) → τ ≤ ∑ i, r i * ((n i : ℝ) / m) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set f : (ι → ℤ) → ℝ := fun n => ∑ i, r i * ((n i : ℝ) / m) with hf
  set S : Finset ℝ := ((Fintype.piFinset fun i =>
    Finset.Icc (-6 * (m : ℤ)) ⌊7 * (m : ℝ) / r i⌋).image f).filter (0 < ·)
  have hne : (insert 1 S).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 S).min' hne, ?_, fun n hn hpos => ?_⟩
  · rcases Finset.mem_insert.mp (Finset.min'_mem _ hne) with h | h
    · rw [h]
      exact one_pos
    · exact (Finset.mem_filter.mp h).2
  have hn' : ∀ j, (0 : ℝ) ≤ n j + 6 * m := fun j => by
    linarith [(le_div_iff₀ hmR).mp (hn j)]
  by_cases h1 : f n ≤ 1
  · refine Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨n, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr
        ⟨by exact_mod_cast (by push_cast; linarith [hn' i] : ((-6 * (m : ℤ) : ℤ) : ℝ) ≤ n i),
          Int.le_floor.mpr ?_⟩, rfl⟩, hpos⟩))
    have hsum : ∑ j, r j * ((n j : ℝ) + 6 * m) = m * f n + 6 * m := by
      simp only [hf, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hr1, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by field_simp
      · ring
    have hle : r i * ((n i : ℝ) + 6 * m) ≤ ∑ j, r j * ((n j : ℝ) + 6 * m) :=
      Finset.single_le_sum (f := fun j => r j * ((n j : ℝ) + 6 * m))
        (fun j _ => mul_nonneg (hr j).le (hn' j)) (Finset.mem_univ i)
    rw [le_div_iff₀ (hr i)]
    nlinarith [hr i, hn' i]
  · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (not_le.mp h1).le

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltPair sY Θ) (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y)
    infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- If `m (K + B) = L` coefficientwise, then `K + B = (1 / m) L` as real divisors. -/
private theorem toRDivisor_add_eq_smul {Y : Scheme.{0}} {K : Divisor Y} {B : QDivisor Y}
    {m : ℕ} (hm : 0 < m) {L : Divisor Y}
    (hBL : ∀ P, (m : ℚ) * ((K.coeff P : ℚ) + B.coeff P) = L.coeff P) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B = (1 / m : ℝ) • Divisor.toRDivisor L := by
  ext P
  have h : (m : ℝ) * ((K.coeff P : ℝ) + (B.coeff P : ℝ)) = L.coeff P := by exact_mod_cast hBL P
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change (K.coeff P : ℝ) + (B.coeff P : ℝ) = 1 / m * (L.coeff P : ℝ)
  rw [← h]
  field_simp

/-- A rational klt boundary `B` with `m (K + B)` integral Cartier is klt as a real boundary. -/
private theorem isRealKltPair_toRDivisor {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {B : QDivisor Y} (hB : IsKltPair sY B) {m : ℕ} (hm : 0 < m)
    {L : Divisor Y} (hL : L.IsCartier)
    (hBL : ∀ P, (m : ℚ) * ((K.coeff P : ℚ) + B.coeff P) = L.coeff P) :
    IsRealKltPair sY (QDivisor.toRDivisor B) :=
  ⟨hB.1.isPair.1, fun P => by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast coeff_lt_one_of_isKltPair hB P,
    ⟨n, K, hK, 1, fun _ => 1 / m, fun _ => L, fun _ => hL, fun P => by
      have h := congrArg (·.coeff P) (toRDivisor_add_eq_smul hm hBL)
      simp only [Fin.sum_univ_one]
      exact h⟩, hB.2⟩

/-- **A uniform positive intersection gap.** Let `rᵢ > 0` (`i ∈ ι`, finite) be real weights with
`∑ rᵢ = 1` and let `m > 0`. There is `τ > 0` with the following property. Let `X` be a normal
`ℚ`-factorial projective complex threefold with canonical divisor `K`, let `Bᵢ` be effective
`ℚ`-divisors with every `(X, Bᵢ)` klt, and let `Lᵢ` be Cartier divisors with
`Lᵢ = m (K + Bᵢ)`. Let `R` be an extremal ray of `NE̅(X)` on which `K + B'` is negative for some
effective real boundary `B'` with `(X, B')` klt. Then `R` contains the nonzero class of a
rational curve `C` with `(K + Bᵢ) · C = (Lᵢ · C) / m ≥ -6` for every `i`, and such that
`D · C = ∑ rᵢ (K + Bᵢ) · C` satisfies `D · C ≤ 0` or `τ ≤ D · C`. -/
@[mmp "lem_fourfold_positive_intersection_gap"]
public theorem exists_pos_forall_exists_isRationalCurve_neg_six_le_and_le_zero_or_le
    {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∑ i, r i = 1)
    (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
        [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X],
        IsQFactorial sX → ∀ {K : Divisor X}, K.IsCanonicalDivisor sX 3 →
        ∀ (B : ι → QDivisor X), (∀ i P, 0 ≤ (B i).coeff P) → (∀ i, IsKltPair sX (B i)) →
        ∀ (L : ι → Divisor X) (hL : ∀ i, (L i).IsCartier),
        (∀ i P, (m : ℚ) * ((K.coeff P : ℚ) + (B i).coeff P) = (L i).coeff P) →
        ∀ {R : Set (NumericalCurveClasses sX)},
        IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R →
        (∃ (B' : RDivisor X), (∀ P, 0 ≤ B'.coeff P) ∧ IsRealKltPair sX B' ∧
          ∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ j, (M j).IsCartier),
            Divisor.toRDivisor K + B' = ∑ j, c j • Divisor.toRDivisor (M j) ∧
            ∀ u ∈ R, u ≠ 0 →
              ∑ j, c j * (haveI := (hM j).isInvertibleModule_divisorialSheaf
                NumericalCurveClasses.degree sX (M j).divisorialSheaf u) < 0) →
        ∃ C : ProperCurve sX,
          IsRationalCurve sX
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
          OneCycle.numericalClass sX (C.cycle ℝ) ∈ R ∧
          OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 ∧
          (∀ i, -6 ≤ (haveI := (hL i).isInvertibleModule_divisorialSheaf
              NumericalCurveClasses.degree sX (L i).divisorialSheaf
                (OneCycle.numericalClass sX (C.cycle ℝ))) / m) ∧
          (∑ i, r i * ((haveI := (hL i).isInvertibleModule_divisorialSheaf
              NumericalCurveClasses.degree sX (L i).divisorialSheaf
                (OneCycle.numericalClass sX (C.cycle ℝ))) / m) ≤ 0 ∨
            τ ≤ ∑ i, r i * ((haveI := (hL i).isInvertibleModule_divisorialSheaf
              NumericalCurveClasses.degree sX (L i).divisorialSheaf
                (OneCycle.numericalClass sX (C.cycle ℝ))) / m)) := by
  obtain ⟨τ, hτ, hgap⟩ := exists_pos_le_sum r hr hr1 m hm
  refine ⟨τ, hτ, ?_⟩
  rintro X sX _ _ _ _ _ hXq K hK B hB0 hB L hL hBL R hR
    ⟨B', hB'0, hB'klt, n, c, M, hM, hKB', hcneg⟩
  let Bf : Option ι → RDivisor X := fun o => o.elim B' fun i => QDivisor.toRDivisor (B i)
  have hBf0 : ∀ j P, 0 ≤ (Bf j).coeff P := by
    rintro (_ | i) P
    · exact hB'0 P
    · change (0 : ℝ) ≤ ((B i).coeff P : ℝ)
      exact_mod_cast hB0 i P
  have hBf : ∀ j, IsRealKltPair sX (Bf j) := by
    rintro (_ | i)
    · exact hB'klt
    · exact isRealKltPair_toRDivisor hK (hB i) hm (hL i) (hBL i)
  obtain ⟨C, hrat, hmem, hne, hbd⟩ :=
    exists_isRationalCurve_numericalClass_mem_and_neg_six_le hXq hK hBf0 hBf hR
      ⟨none, n, c, M, hM, hKB', hcneg⟩
  -- the integral degrees `nᵢ = deg_C (Lᵢ)`
  let N : ι → ℤ := fun i => haveI := (hL i).isInvertibleModule_divisorialSheaf
    C.degree ℂ (L i).divisorialSheaf
  have hN : ∀ i, (haveI := (hL i).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX (L i).divisorialSheaf
        (OneCycle.numericalClass sX (C.cycle ℝ))) = (N i : ℝ) := fun i =>
    haveI := (hL i).isInvertibleModule_divisorialSheaf
    OneCycle.degree_cycle ℝ _ C
  have hsix : ∀ i, -6 ≤ (N i : ℝ) / m := fun i => by
    simpa [hN i, div_eq_inv_mul] using hbd (some i) 1 (fun _ => 1 / m) (fun _ => L i)
      (fun _ => hL i) (by simpa [Bf] using toRDivisor_add_eq_smul hm (hBL i))
  refine ⟨C, hrat, hmem, hne, fun i => hN i ▸ hsix i, ?_⟩
  simp only [hN]
  exact (le_or_gt _ 0).imp id (hgap N hsix)

end MMP.Fourfold

end
