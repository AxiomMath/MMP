module

public import MMP.Attr
public import Mathlib.Order.CompletePartialOrder
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.ArithmeticPoints

/-!
# Algebraic inputs of the fourfold source

Two elementary algebraic facts used by the fourfold source: a field which is a finitely generated
`ℤ`-algebra is a finite field of positive characteristic, and the factorial-base limit of the
normalized minimal orders of a graded series.

## Main results

* `MMP.Fourfold.finite_and_charPos_of_finiteType_int`: a field of finite type over `ℤ` is finite of
  positive characteristic.
* `MMP.Fourfold.tendsto_normalized_factorial_of_subadditive`: the factorial limit for a subadditive
  family `a : ℕ → ℕ∞`.
* `MMP.Fourfold.gradedSeriesOrder`, `MMP.Fourfold.factorial_base_limit`: the minimal order of a
  graded series (with `gradedSeriesOrder_le`, `gradedSeriesOrder_ne_top_iff` and
  `gradedSeriesOrder_add_le`) and the factorial-base limit
  `inf_{m} v(V_m)/m = lim_j v(V_{b j!})/(b j!)`.
* `MMP.Fourfold.valuationSectionOrder`, `MMP.Fourfold.factorial_base_limit_valuation`: the same
  for a (divisorial) valuation.

## Implementation notes

For a graded series `V_•` of sections, `v(V_m)` is the minimum, over the nonzero `s ∈ V_m`, of the
order of `s` along `v` as a section of `𝒪(m D)`, that is of `ord_v(s) + m·coeff_v(D)`; this order
is nonnegative for sections. The limit statement uses only that this order is subadditive for
products, so it is stated for an abstract order function (covering divisorial valuations and
multiplicity at the generic point of a subvariety of a smooth variety, the order function of a
regular local ring being additive on products). The index `b` is a positive integer.
-/

@[expose] public noncomputable section

open Filter ENNReal

namespace MMP.Fourfold

/-- A field that is a finitely generated `ℤ`-algebra is a finite field of positive
characteristic. -/
@[mmp "lem_fourfold_finite_type_integer_field_finite"]
theorem finite_and_charPos_of_finiteType_int (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K ∧ 0 < ringChar K := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  have : Finite K := AlgebraicGeometry.HodgeSpreadingOut.finite_of_moduleFinite_int K
  exact ⟨this, Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite K)⟩

/-! ### The factorial-base limit -/

/-- A subadditive family satisfies `a (k m) ≤ k a m` for `0 < k`. -/
theorem mul_le_of_subadditive {a : ℕ → ℕ∞} (h : ∀ m n, a (m + n) ≤ a m + a n) (k m : ℕ)
    (hk : 0 < k) : a (k * m) ≤ k * a m := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    calc a ((k+1) * m) = a (k * m + m) := by ring_nf
      _ ≤ a (k*m) + a m := h _ _
      _ ≤ k * a m + a m := by gcongr
      _ = (k+1) * a m := by ring

/-- The normalized values of a subadditive family satisfy `a (k m) / (k m) ≤ a m / m`. -/
theorem normalized_mul_le {a : ℕ → ℕ∞} (h : ∀ m n, a (m + n) ≤ a m + a n) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    ((a (k * m) : ℕ∞) : ℝ≥0∞) / ((k * m : ℕ) : ℝ≥0∞) ≤ ((a m : ℕ∞) : ℝ≥0∞) / (m : ℝ≥0∞) := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Nat.cast_mul, ENNReal.div_le_iff (by simp [hk.ne', hm0])
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))]
  calc _ ≤ (k : ℝ≥0∞) * a m := by
        simpa using ENat.toENNReal_le.2 (mul_le_of_subadditive h k m hk)
    _ = (a m / m) * (k * m) := by
      rw [mul_comm (k : ℝ≥0∞) m, ← mul_assoc, ENNReal.div_mul_cancel hm0 (by simp), mul_comm]

/-- **Factorial limit for a subadditive family.** If `a : ℕ → ℕ∞` is subadditive (with `a m = ⊤`
standing for `V_m = 0`) and `b > 0` with `a b ≠ ⊤`, then `a (b j!) / (b j!)` converges, as
`j → ∞`, to the infimum of `a m / m` over the `m > 0` with `a m ≠ ⊤`. -/
theorem tendsto_normalized_factorial_of_subadditive {a : ℕ → ℕ∞}
    (h : ∀ m n, a (m + n) ≤ a m + a n) {b : ℕ} (hb : 0 < b) (hab : a b ≠ ⊤) :
    Tendsto (fun j : ℕ => ((a (b * j.factorial) : ℕ∞) : ℝ≥0∞) / ((b * j.factorial : ℕ) : ℝ≥0∞))
      atTop (nhds (⨅ (m : ℕ) (_ : 0 < m ∧ a m ≠ ⊤), ((a m : ℕ∞) : ℝ≥0∞) / (m : ℝ≥0∞))) := by
  set f : ℕ → ℝ≥0∞ := fun j => ((a (b * j.factorial) : ℕ∞) : ℝ≥0∞) / ((b * j.factorial : ℕ) : ℝ≥0∞)
  have hpos : ∀ j : ℕ, 0 < b * j.factorial := fun j => Nat.mul_pos hb (Nat.factorial_pos j)
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le fun j => ?_
    have := normalized_mul_le h (j + 1) (b * j.factorial) (Nat.succ_pos j) (hpos j)
    have e : (j + 1) * (b * j.factorial) = b * (j + 1).factorial := by
      rw [Nat.factorial_succ]; ring
    rwa [e] at this
  suffices heq : (⨅ j, f j) = ⨅ (m : ℕ) (_ : 0 < m ∧ a m ≠ ⊤), ((a m : ℕ∞) : ℝ≥0∞) / (m : ℝ≥0∞) by
    rw [← heq]
    exact tendsto_atTop_iInf hanti
  apply le_antisymm
  · refine le_iInf₂ fun m hm => iInf_le_of_le m ?_
    replace hm := hm.1
    obtain ⟨c, hc⟩ : m ∣ b * m.factorial := Dvd.dvd.mul_left (Nat.dvd_factorial hm le_rfl) b
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simpa [hc] using hpos m)
    have := normalized_mul_le h c m hc0 hm
    rwa [mul_comm c m, ← hc] at this
  · refine le_iInf fun j => iInf_le_of_le (b * j.factorial) (iInf_le_of_le ⟨hpos j, ?_⟩ le_rfl)
    rw [mul_comm]
    exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top _) hab)
      (mul_le_of_subadditive h j.factorial b j.factorial_pos)

section GradedSeries

variable {K : Type*} [MulZeroClass K]

/-- The minimal order `v(V_m)` of a graded series: the infimum, over the nonzero `s ∈ V_m`, of the
order `ord m s` of `s` as a section of degree `m` (`⊤` if `V_m = 0`). -/
def gradedSeriesOrder (V : ℕ → Set K) (ord : ℕ → K → ℕ∞) (m : ℕ) : ℕ∞ :=
  ⨅ s : {s : K // s ∈ V m ∧ s ≠ 0}, ord m s.1

/-- The minimal order of a graded series is at most the order of any nonzero section. -/
theorem gradedSeriesOrder_le {V : ℕ → Set K} {ord : ℕ → K → ℕ∞} {m : ℕ} {s : K}
    (hs : s ∈ V m) (hs0 : s ≠ 0) : gradedSeriesOrder V ord m ≤ ord m s :=
  iInf_le (fun s : {s : K // s ∈ V m ∧ s ≠ 0} => ord m s.1) ⟨s, hs, hs0⟩

/-- The minimal order of a graded series with no nonzero section in degree `m` is `⊤`. -/
theorem gradedSeriesOrder_eq_top_of_forall {V : ℕ → Set K} {ord : ℕ → K → ℕ∞} {m : ℕ}
    (h : ∀ s ∈ V m, s = 0) : gradedSeriesOrder V ord m = ⊤ := by
  have : IsEmpty {s : K // s ∈ V m ∧ s ≠ 0} := ⟨fun s => s.2.2 (h s.1 s.2.1)⟩
  simp [gradedSeriesOrder]

/-- For an order finite on nonzero sections, the minimal order of `V_m` is finite iff
`V_m ≠ 0`. -/
theorem gradedSeriesOrder_ne_top_iff {V : ℕ → Set K} {ord : ℕ → K → ℕ∞}
    (hfin : ∀ m s, s ≠ 0 → ord m s ≠ ⊤) (m : ℕ) :
    gradedSeriesOrder V ord m ≠ ⊤ ↔ ∃ s ∈ V m, s ≠ 0 := by
  refine ⟨fun h => ?_, fun ⟨s, hs, hs0⟩ => ne_top_of_le_ne_top (hfin m s hs0)
    (gradedSeriesOrder_le hs hs0)⟩
  by_contra! hcon
  exact h (gradedSeriesOrder_eq_top_of_forall hcon)

/-- The minimal order of a graded series is subadditive when the order is subadditive on
products. -/
theorem gradedSeriesOrder_add_le [NoZeroDivisors K] {V : ℕ → Set K} {ord : ℕ → K → ℕ∞}
    (hV : ∀ m n s t, s ∈ V m → t ∈ V n → s * t ∈ V (m + n))
    (hord : ∀ m n s t, s ∈ V m → t ∈ V n → s ≠ 0 → t ≠ 0 →
      ord (m + n) (s * t) ≤ ord m s + ord n t) (m n : ℕ) :
    gradedSeriesOrder V ord (m + n) ≤ gradedSeriesOrder V ord m + gradedSeriesOrder V ord n :=
  ENat.le_iInf_add_iInf fun s t => iInf_le_of_le
    (⟨s.1 * t.1, hV m n _ _ s.2.1 t.2.1, mul_ne_zero s.2.2 t.2.2⟩ :
      {s : K // s ∈ V (m + n) ∧ s ≠ 0}) (hord m n _ _ s.2.1 t.2.1 s.2.2 t.2.2)

/-- **Factorial limits of base multiplicities.** Let `V_•` be a graded series (`V_m V_n ⊆ V_{m+n}`)
in a `K` without zero divisors (e.g. the function field), and let `ord m s` be the order of a
nonzero section `s` of degree `m` along a divisorial valuation, or the multiplicity at the generic
point of a subvariety of a smooth variety. If this order is subadditive on products and finite on
nonzero sections, then for any `b > 0` with `V_b ≠ 0` the normalized orders `v(V_{b j!}) / (b j!)`
converge, as `j → ∞`, to `inf_{m : V_m ≠ 0} v(V_m) / m`. -/
@[mmp "lem_fourfold_factorial_base_limit"]
theorem factorial_base_limit [NoZeroDivisors K] (V : ℕ → Set K)
    (hV : ∀ m n s t, s ∈ V m → t ∈ V n → s * t ∈ V (m + n)) (ord : ℕ → K → ℕ∞)
    (hord : ∀ m n s t, s ∈ V m → t ∈ V n → s ≠ 0 → t ≠ 0 →
      ord (m + n) (s * t) ≤ ord m s + ord n t)
    (hfin : ∀ m s, s ≠ 0 → ord m s ≠ ⊤) {b : ℕ} (hb : 0 < b) (hVb : ∃ s ∈ V b, s ≠ 0) :
    Tendsto (fun j : ℕ => ((gradedSeriesOrder V ord (b * j.factorial) : ℕ∞) : ℝ≥0∞) /
        ((b * j.factorial : ℕ) : ℝ≥0∞))
      atTop (nhds (⨅ (m : ℕ) (_ : 0 < m ∧ ∃ s ∈ V m, s ≠ 0),
        ((gradedSeriesOrder V ord m : ℕ∞) : ℝ≥0∞) / (m : ℝ≥0∞))) := by
  have hne := fun m => gradedSeriesOrder_ne_top_iff (V := V) hfin m
  simpa only [hne] using tendsto_normalized_factorial_of_subadditive
    (gradedSeriesOrder_add_le hV hord) hb ((hne b).2 hVb)

end GradedSeries

section Valuation

variable {K : Type*} [Field K]

open Classical in
/-- The order of a nonzero section `s` along a valuation `v` of `K`, for a section of a line
bundle whose divisor has coefficient `d` along `v`: `ord_v(s) + d` (`⊤` for `s = 0`). It is the
coefficient of `v` in `div s + D`, and is nonnegative for a section `s` of `𝒪(D)`; for a rational
function that is not a section the value is truncated at `0`. -/
def valuationSectionOrder (v : Valuation K (WithZero (Multiplicative ℤ))) (d : ℤ) (s : K) : ℕ∞ :=
  if s = 0 then ⊤ else (((d - WithZero.log (v s)).toNat : ℕ) : ℕ∞)

/-- The order of the zero section is `⊤`. -/
@[simp]
theorem valuationSectionOrder_zero (v : Valuation K (WithZero (Multiplicative ℤ))) (d : ℤ) :
    valuationSectionOrder v d 0 = ⊤ := by
  simp [valuationSectionOrder]

/-- For `s ≠ 0`, `valuationSectionOrder v d s` is `(d - log (v s)).toNat`. -/
theorem valuationSectionOrder_of_ne_zero (v : Valuation K (WithZero (Multiplicative ℤ))) (d : ℤ)
    {s : K} (hs : s ≠ 0) :
    valuationSectionOrder v d s = (((d - WithZero.log (v s)).toNat : ℕ) : ℕ∞) := by
  rw [valuationSectionOrder, if_neg hs]

/-- **Factorial limits of base multiplicities along a divisorial valuation.** Let `V_•` be a graded
series in a field `K` and `v` a `ℤₘ₀`-valued valuation of `K` (for instance a divisorial valuation
of the function field of a normal variety, `MMP.Mori.DivisorOver.valuation`). The twist `e m` is the
coefficient along `v` of the divisor `m D` the sections of `V_m` live on (additive in `m` on the
indices with `V_m ≠ 0`), and `v(V_m)` is the minimal order `ord_v(s) + e m` (truncated at `0`) of
the nonzero `s ∈ V_m`. Then for any `b > 0` with `V_b ≠ 0`,
`inf_{m : V_m ≠ 0} v(V_m) / m = lim_{j → ∞} v(V_{b j!}) / (b j!)`. -/
@[mmp "lem_fourfold_factorial_base_limit"]
theorem factorial_base_limit_valuation (v : Valuation K (WithZero (Multiplicative ℤ)))
    (e : ℕ → ℤ) (V : ℕ → Set K)
    (hV : ∀ m n s t, s ∈ V m → t ∈ V n → s * t ∈ V (m + n))
    (he : ∀ m n, (∃ s ∈ V m, s ≠ 0) → (∃ t ∈ V n, t ≠ 0) → e (m + n) = e m + e n)
    {b : ℕ} (hb : 0 < b) (hVb : ∃ s ∈ V b, s ≠ 0) :
    Tendsto (fun j : ℕ => ((gradedSeriesOrder V (fun m => valuationSectionOrder v (e m))
        (b * j.factorial) : ℕ∞) : ℝ≥0∞) / ((b * j.factorial : ℕ) : ℝ≥0∞))
      atTop (nhds (⨅ (m : ℕ) (_ : 0 < m ∧ ∃ s ∈ V m, s ≠ 0),
        ((gradedSeriesOrder V (fun m => valuationSectionOrder v (e m)) m : ℕ∞) : ℝ≥0∞) /
          (m : ℝ≥0∞))) := by
  refine factorial_base_limit V hV _ ?_ ?_ hb hVb
  · intro m n s t hs ht hs0 ht0
    rw [valuationSectionOrder_of_ne_zero _ _ hs0, valuationSectionOrder_of_ne_zero _ _ ht0,
      valuationSectionOrder_of_ne_zero _ _ (mul_ne_zero hs0 ht0)]
    rw [map_mul, WithZero.log_mul (v.ne_zero_iff.2 hs0) (v.ne_zero_iff.2 ht0),
      he m n ⟨s, hs, hs0⟩ ⟨t, ht, ht0⟩, ← Nat.cast_add, Nat.cast_le]
    omega
  · intro m s hs0
    simp [valuationSectionOrder_of_ne_zero _ _ hs0]

end Valuation

end MMP.Fourfold

