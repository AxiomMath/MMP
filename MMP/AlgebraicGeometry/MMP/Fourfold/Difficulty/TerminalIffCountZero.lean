module

public import MMP.AlgebraicGeometry.Singularities.KltLogDiscrepancyDiscrete
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform

/-!
# A klt pair is terminal exactly when `e(X, B) = 0`

Let `(X, B)` be a Kawamata log terminal pair with `B` a `ℚ`-divisor. Then `(X, B)` is terminal,
meaning `discrep(X, B) > 0`, if and only if no exceptional divisor `E` of `k(X)` with center on `X`
has `a(E, X, B) ≤ 0`. Equivalently, the count `e(X, B)` of `MMP.Flips.eCount` vanishes.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.isTerminalPair_iff_eCount_eq_zero`: the statement above.

## Implementation notes

Terminality (`MMP.Flips.IsTerminalPair`) is defined for a `ℚ`-divisor, while Kawamata log
terminality and `e(X, B)` are defined for `ℝ`-divisors. So the boundary is a `ℚ`-divisor `B`, and
it enters the latter two through `MMP.Mori.QDivisor.toRDivisor`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.9, 6.6
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori
open scoped WithZero

/-- Every divisor over `X` has a discrepancy `a_ω(E, X, B)` with respect to a pair `(X, B)` with
`K_X + B` `ℚ`-Cartier. -/
private theorem exists_isQDiscrepancyWith {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hX : IsNormalVariety k sX)
    (hK : K.IsCanonicalDivisor sX n) (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    (E : ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), IsQDiscrepancyWith sX n B ω E a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' E.f
    (Divisor.toQDivisor (divisorOfForm ω) + B)
  obtain ⟨G, hG, -⟩ := hKB.existsUnique_isPullback hB
  exact ⟨ω, _, hX, hK.1, hω0, hKB, hB, G, hG, rfl⟩

/-- Values `m + ∑ⱼ lⱼ cⱼ` (`m, lⱼ ∈ ℕ`, `cⱼ > 0`) larger than `1` are at least `1 + ε` for some
fixed `ε > 0`. -/
private theorem exists_pos_forall_one_add_le {s : ℕ} (c : Fin s → ℝ) (hc : ∀ j, 0 < c j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : ℕ) (l : Fin s → ℕ),
      1 < (m : ℝ) + ∑ j, (l j : ℝ) * c j → 1 + ε ≤ (m : ℝ) + ∑ j, (l j : ℝ) * c j := by
  classical
  set N : ℕ := ⌈2 + ∑ j, 2 / c j⌉₊
  let val : ℕ × (Fin s → ℕ) → ℝ := fun p => (p.1 : ℝ) + ∑ j, (p.2 j : ℝ) * c j
  let T : Finset ℝ := insert 2 ((((Finset.range (N + 1)) ×ˢ
    Fintype.piFinset fun _ => Finset.range (N + 1)).image val).filter (1 < ·))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hT1 : ∀ t ∈ T, 1 < t := by
    simp only [T, Finset.mem_insert, Finset.mem_filter]
    rintro t (rfl | ⟨-, ht⟩) <;> [norm_num; exact ht]
  refine ⟨T.min' hT - 1, by linarith [hT1 _ (T.min'_mem hT)], fun m l hx => ?_⟩
  rw [add_sub_cancel]
  by_cases h2 : 2 ≤ (m : ℝ) + ∑ j, (l j : ℝ) * c j
  · exact (T.min'_le 2 (Finset.mem_insert_self _ _)).trans h2
  push Not at h2
  have hnn : ∀ j, 0 ≤ (l j : ℝ) * c j := fun j => mul_nonneg (Nat.cast_nonneg _) (hc j).le
  have hdiv : ∀ j, 0 ≤ 2 / c j := fun j => div_nonneg zero_le_two (hc j).le
  have hN : 2 + ∑ j, 2 / c j ≤ N := Nat.le_ceil _
  have hsd : 0 ≤ ∑ j, 2 / c j := Finset.sum_nonneg fun j _ => hdiv j
  have hsum : 0 ≤ ∑ j, (l j : ℝ) * c j := Finset.sum_nonneg fun j _ => hnn j
  refine T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, hx⟩))
  refine Finset.mem_image.mpr ⟨(m, l), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Finset.mem_range.mpr (by exact_mod_cast (by linarith : (m : ℝ) < N + 1))
  · refine Fintype.mem_piFinset.mpr fun j => Finset.mem_range.mpr ?_
    have hj : (l j : ℝ) * c j < 2 := by
      linarith [Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j),
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hlj : (l j : ℝ) < 2 / c j := (lt_div_iff₀ (hc j)).mpr hj
    have := Finset.single_le_sum (fun i _ => hdiv i) (Finset.mem_univ j)
    exact_mod_cast (by linarith : (l j : ℝ) < N + 1)

/-- The positive discrepancies of a klt pair are bounded away from `0`. -/
private theorem exists_pos_forall_le_discrepancy {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : RDivisor X} (h : IsKawamataLogTerminal sX n K B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Valuation X.functionField ℤᵐ⁰) (a : ℝ),
      IsDiscrepancy sX n K B F a → 0 < a → ε ≤ a := by
  obtain ⟨s, c, hc, hdisc⟩ := h.exists_logDiscrepancy_eq_add_sum sX
  obtain ⟨ε, hε, hgap⟩ := exists_pos_forall_one_add_le c hc
  refine ⟨ε, hε, fun F a hd ha => ?_⟩
  obtain ⟨m, l, -, hb⟩ := hdisc F hd.2.2.1 (1 + a) ⟨a, hd, rfl⟩
  linarith [hgap m l (by linarith)]

/-- **FA 6.6.** Let `(X, B)` be a Kawamata log terminal pair, with `X` of dimension `n`, canonical
divisor `K` and `B` a `ℚ`-divisor. Then `(X, B)` is terminal if and only if `e(X, B) = 0`. -/
@[mmp "lem_fa6_terminal_iff_e_zero"]
public theorem IsKawamataLogTerminal.isTerminalPair_iff_eCount_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (h : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor B)) :
    IsTerminalPair sX n K B ↔ eCount sX n K (QDivisor.toRDivisor B) h = 0 := by
  rw [eCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro ⟨hX, hK, -, hKB, hd⟩ _ ⟨⟨E, hEx, rfl⟩, a, ha, ha0⟩
    obtain ⟨ω, a', h'⟩ := exists_isQDiscrepancyWith hX hK hKB E
    obtain rfl := ha.eq (h'.isDiscrepancy hK hKB hEx)
    have : discrep sX n B ≤ ((a' : ℝ) : EReal) := sInf_le ⟨E, ω, a', hEx, h', rfl⟩
    exact ha0.not_gt (EReal.coe_pos.mp (hd.trans_le this))
  · intro he
    obtain ⟨hlv, hK, hKBc, -⟩ := id h
    have hKB : (Divisor.toQDivisor K + B).IsQCartier := by
      refine QDivisor.isQCartier_of_isCartierCombination ?_
      rwa [map_add, QDivisor.toRDivisor_toQDivisor]
    obtain ⟨ε, hε, hgap⟩ := exists_pos_forall_le_discrepancy h
    refine ⟨hlv.isNormalVariety, hK, fun P => ?_, hKB,
      (EReal.coe_pos.mpr hε).trans_le (le_sInf ?_)⟩
    · exact_mod_cast QDivisor.coeff_toRDivisor B P ▸ (hlv.isBoundary P).1
    rintro _ ⟨E, ω, a, hEx, hq, rfl⟩
    have hd := hq.isDiscrepancy hK hKB hEx
    exact EReal.coe_le_coe_iff.mpr <| hgap _ _ hd <|
      not_le.mp fun ha => he _ ⟨⟨E, hEx, rfl⟩, _, hd, ha⟩

end MMP.Flips
