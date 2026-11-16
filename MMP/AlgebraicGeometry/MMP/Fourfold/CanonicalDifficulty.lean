module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program

/-!
# The canonical difficulty of a real canonical pair and rational null-decomposition data

For a real canonical pair `(X, B = ∑ⱼ bⱼ Bⱼ)` with no coefficient one, let
`d = max ({0} ∪ {bⱼ})` and let `S(B)` be the set of the sums `∑ⱼ nⱼ bⱼ`, `nⱼ ∈ ℕ`, lying in
`[d, 1]` (so `S(0) = {0}`). For `u ∈ ℝ`, `𝓔_u(X, B)` is the set of exceptional divisorial
valuations with center on `X` and log discrepancy `a(E, X, B) < u`. The *canonical difficulty* is
`𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)`.

For a real klt boundary `B` on a normal `ℚ`-factorial projective complex variety `X`, *rational
null-decomposition data* consist of rational klt boundaries `B₁, …, B_s` in the smallest rational
affine hull of `B`, positive real weights `rᵢ` with `∑ rᵢ = 1` and `B = ∑ rᵢ Bᵢ`, and an integer
`m > 0` such that every `m(K_X + Bᵢ)` is an integral Cartier divisor.

## Main definitions

* `MMP.Fourfold.realThresholdMax`: `d = max ({0} ∪ {bⱼ})`.
* `MMP.Fourfold.realThresholdSet`: `S(B)`.
* `MMP.Fourfold.logDiscrepancyLtSet`: `𝓔_u(X, B)`.
* `MMP.Fourfold.realCanonicalDifficulty`: `𝔡(X, B) ∈ ℕ ∪ {∞}`.
* `MMP.Fourfold.RationalNullData`: rational null-decomposition data.

## Main results

* `MMP.Fourfold.realThresholdSet_zero`: `S(0) = {0}`.
* `MMP.Fourfold.realThresholdSet_finite`: `S(B)` is finite when every coefficient of `B` is
  positive or zero.
* `MMP.Fourfold.realCanonicalDifficulty_eq_finsum`: for finite `S(B)`,
  `𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)`.

## Implementation notes

* The coefficients `bⱼ` are the nonzero coefficients of `B`, indexed by its support. The case
  `s = 0` of an empty boundary needs no separate clause: for `B = 0` the defining condition gives
  `S(0) = {0}` (`MMP.Fourfold.realThresholdSet_zero`).
* An exceptional divisorial valuation with center on `X` is the valuation of an exceptional
  divisor `(Y, f, E)` over `X` with `f` proper, and its log discrepancy is
  `MMP.Intersection.IsLogDiscrepancy` (which requires `f` proper), as in
  `MMP.Fourfold.IsRealCanonicalPair`. The set `𝓔_u(X, B)` is a set of valuations of `k(X)`, so
  different models of the same valuation are counted once.
* `#𝓔_u(X, B)` is the cardinality `Set.encard` in `ℕ ∪ {∞}`. The sum over `S(B)` is the
  cardinality of the disjoint union `⨆_{s ∈ S(B)} 𝓔_{2 - s}(X, B)`, which is the sum of the
  cardinalities whenever `S(B)` is finite (`MMP.Fourfold.realCanonicalDifficulty_eq_finsum`), in
  particular for a real canonical pair.
* The canonical difficulty is defined for every `ℝ`-divisor `B`; the source considers it for real
  canonical pairs (`MMP.Fourfold.IsRealCanonicalPair`).
* In rational null-decomposition data, the hypotheses on `X` and `B` are fields of the structure,
  the smallest rational affine hull is `MMP.Fourfold.IsInSmallestRationalAffineHull` (whose
  coefficient space has one coordinate for each prime divisor in the support of `B`), the
  rational klt boundaries are effective `ℚ`-divisors `Bᵢ` with `(X, Bᵢ)` klt
  (`MMP.Fourfold.IsKltPair`), and `m(K_X + Bᵢ)` is computed with a fixed canonical divisor `K` of
  `X`. A real klt boundary is an effective `ℝ`-divisor `B` with `(X, B)` klt in the sense of
  `MMP.Fourfold.IsRealKltPair`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### The canonical difficulty -/

section Difficulty

variable {X : Scheme.{u}}

/-- `d = max ({0} ∪ {bⱼ})`, the maximum of `0` and the coefficients `bⱼ` of `B = ∑ⱼ bⱼ Bⱼ`. -/
@[mmp "def_fourfold_real_canonical_difficulty"]
def realThresholdMax (B : RDivisor X) : ℝ :=
  (insert 0 (B.support.image B.coeff)).max' (Finset.insert_nonempty _ _)

/-- `S(B) = {∑ⱼ nⱼ bⱼ : nⱼ ∈ ℕ, d ≤ ∑ⱼ nⱼ bⱼ ≤ 1}` for `B = ∑ⱼ bⱼ Bⱼ` and
`d = max ({0} ∪ {bⱼ})`. -/
@[mmp "def_fourfold_real_canonical_difficulty"]
def realThresholdSet (B : RDivisor X) : Set ℝ :=
  {t | (∃ n : MMP.Mori.PrimeDivisor X → ℕ, t = ∑ P ∈ B.support, (n P : ℝ) * B.coeff P) ∧
    realThresholdMax B ≤ t ∧ t ≤ 1}

/-- Membership in `S(B)`. -/
theorem mem_realThresholdSet {B : RDivisor X} {t : ℝ} :
    t ∈ realThresholdSet B ↔
      (∃ n : MMP.Mori.PrimeDivisor X → ℕ, t = ∑ P ∈ B.support, (n P : ℝ) * B.coeff P) ∧
        realThresholdMax B ≤ t ∧ t ≤ 1 :=
  Iff.rfl

/-- For the empty boundary, `realThresholdMax 0 = 0`. -/
@[simp]
theorem realThresholdMax_zero : realThresholdMax (0 : RDivisor X) = 0 := by
  simp [realThresholdMax]

/-- Every coefficient of `B` at a prime divisor in its support is at most `realThresholdMax B`. -/
theorem le_realThresholdMax_of_mem_support (B : RDivisor X) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∈ B.support) : B.coeff P ≤ realThresholdMax B :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hP))

/-- `realThresholdMax B` is nonnegative. -/
theorem zero_le_realThresholdMax (B : RDivisor X) : 0 ≤ realThresholdMax B :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

/-- For the empty boundary, `S(0) = {0}`. -/
@[simp]
theorem realThresholdSet_zero : realThresholdSet (0 : RDivisor X) = {0} := by
  ext t
  simp only [realThresholdSet, realThresholdMax_zero, Finsupp.support_zero, Finset.sum_empty,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, rfl⟩, -, -⟩
    rfl
  · rintro rfl
    exact ⟨⟨fun _ => 0, rfl⟩, le_rfl, zero_le_one⟩

/-- `S(B)` is finite when the coefficients of `B` are nonnegative. -/
theorem realThresholdSet_finite (B : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) :
    (realThresholdSet B).Finite := by
  classical
  let N : MMP.Mori.PrimeDivisor X → ℕ := fun P => ⌊1 / B.coeff P⌋₊
  let F : Finset (MMP.Mori.PrimeDivisor X → ℕ) :=
    Fintype.piFinset (fun P : B.support => Finset.range (N P + 1)) |>.image
      fun n P => if h : P ∈ B.support then n ⟨P, h⟩ else 0
  refine (F.finite_toSet.image fun n => ∑ P ∈ B.support, (n P : ℝ) * B.coeff P).subset ?_
  rintro t ⟨⟨n, rfl⟩, -, ht1⟩
  refine ⟨fun P => if P ∈ B.support then min (n P) (N P) else 0, ?_, ?_⟩
  · refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨fun P => min (n P) (N P), ?_, ?_⟩)
    · exact Fintype.mem_piFinset.mpr fun P =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
    · funext P
      by_cases h : P ∈ B.support <;> simp [h]
  · refine Finset.sum_congr rfl fun P hP => ?_
    simp only [hP, ↓reduceIte]
    congr 2
    refine min_eq_left (Nat.le_floor ?_)
    rw [le_div_iff₀ ((hB P).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp hP)))]
    exact (Finset.single_le_sum (f := fun P => (n P : ℝ) * B.coeff P)
      (fun Q _ => mul_nonneg (Nat.cast_nonneg _) (hB Q)) hP).trans ht1

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- `𝓔_u(X, B)`: the exceptional divisorial valuations of `k(X)` with center on `X` and log
discrepancy `a(E, X, B) < u`, realized by exceptional divisors `(Y, f, E)` over `X` with `f`
proper. -/
@[mmp "def_fourfold_real_canonical_difficulty"]
def logDiscrepancyLtSet (B : RDivisor X) (u : ℝ) : Set (Valuation X.functionField ℤᵐ⁰) :=
  {v | ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ), E.IsExceptional ∧ E.valuation = v ∧
    MMP.Intersection.IsLogDiscrepancy sX n B E a ∧ a < u}

/-- Membership in `𝓔_u(X, B)`. -/
theorem mem_logDiscrepancyLtSet {B : RDivisor X} {u : ℝ} {v : Valuation X.functionField ℤᵐ⁰} :
    v ∈ logDiscrepancyLtSet sX B u ↔ ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
      E.IsExceptional ∧ E.valuation = v ∧ MMP.Intersection.IsLogDiscrepancy sX n B E a ∧ a < u :=
  Iff.rfl

/-- **The finite real-threshold canonical difficulty** `𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)`,
the cardinality in `ℕ ∪ {∞}` of the disjoint union of the sets `𝓔_{2 - s}(X, B)`, `s ∈ S(B)`. -/
@[mmp "def_fourfold_real_canonical_difficulty"]
def realCanonicalDifficulty (B : RDivisor X) : ℕ∞ :=
  (⋃ s ∈ realThresholdSet B, ({s} ×ˢ logDiscrepancyLtSet sX B (2 - s))).encard

/-- When `S(B)` is finite, `𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)`. -/
theorem realCanonicalDifficulty_eq_finsum (B : RDivisor X) (hS : (realThresholdSet B).Finite) :
    realCanonicalDifficulty sX B =
      ∑ᶠ s ∈ realThresholdSet B, (logDiscrepancyLtSet sX B (2 - s)).encard := by
  rw [realCanonicalDifficulty, hS.encard_biUnion]
  · refine finsum_mem_congr rfl fun s _ => ?_
    rw [Set.singleton_prod, (Prod.mk_right_injective s).encard_image]
  · intro s _ t _ hst
    refine Set.disjoint_left.mpr fun x hx hx' => hst ?_
    rw [← (Set.mem_singleton_iff.mp (Set.mem_prod.mp hx).1),
      ← (Set.mem_singleton_iff.mp (Set.mem_prod.mp hx').1)]

/-- For a boundary with nonnegative coefficients (for instance that of a real canonical pair),
`𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)`, a finite sum. -/
theorem realCanonicalDifficulty_eq_finsum_of_nonneg (B : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) :
    realCanonicalDifficulty sX B =
      ∑ᶠ s ∈ realThresholdSet B, (logDiscrepancyLtSet sX B (2 - s)).encard :=
  realCanonicalDifficulty_eq_finsum sX B (realThresholdSet_finite B hB)

end Difficulty

/-! ### Rational null-decomposition data -/

section NullData

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ))

/-- **Rational null-decomposition data** for a real klt boundary `B` (an effective `ℝ`-divisor
with `(X, B)` klt) on a normal `ℚ`-factorial projective complex variety `X` with canonical
divisor `K`: rational klt boundaries `B₁, …, B_s` (effective `ℚ`-divisors with `(X, Bᵢ)` klt) in
the smallest rational affine hull of `B`, positive real weights `rᵢ` with `∑ᵢ rᵢ = 1` and
`B = ∑ᵢ rᵢ Bᵢ`, and an integer `m > 0` such that every `m(K + Bᵢ)` is an integral Cartier
divisor. -/
@[mmp "def_fourfold_rational_null_data"]
structure RationalNullData (K : Divisor X) (B : RDivisor X) where
  /-- `X` is `ℚ`-factorial (in particular a normal variety). -/
  isQFactorial : IsQFactorial sX
  /-- `X` is projective. -/
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sX
  /-- `K` is a canonical divisor of `X`. -/
  isCanonicalDivisor : ∃ n : ℕ, K.IsCanonicalDivisor sX n
  /-- `B` is effective. -/
  nonneg : ∀ P, 0 ≤ B.coeff P
  /-- `(X, B)` is klt. -/
  isRealKltPair : IsRealKltPair sX B
  /-- The number `s` of rational boundaries. -/
  s : ℕ
  /-- The rational boundaries `B₁, …, B_s`. -/
  boundary : Fin s → QDivisor X
  /-- Each `Bᵢ` is effective. -/
  boundary_nonneg : ∀ i P, 0 ≤ (boundary i).coeff P
  /-- Each `(X, Bᵢ)` is klt. -/
  isKltPair_boundary : ∀ i, IsKltPair sX (boundary i)
  /-- Each `Bᵢ` lies in the smallest rational affine hull of `B`. -/
  mem_hull : ∀ i, IsInSmallestRationalAffineHull B (QDivisor.toRDivisor (boundary i))
  /-- The weights `r₁, …, r_s`. -/
  weight : Fin s → ℝ
  /-- Each weight `rᵢ` is positive. -/
  weight_pos : ∀ i, 0 < weight i
  /-- The weights sum to one: `∑ᵢ rᵢ = 1`. -/
  sum_weight : ∑ i, weight i = 1
  /-- `B = ∑ᵢ rᵢ Bᵢ`. -/
  eq_sum : B = ∑ i, weight i • QDivisor.toRDivisor (boundary i)
  /-- The integer `m`. -/
  m : ℕ
  /-- The integer `m` is positive. -/
  m_pos : 0 < m
  /-- Every `m(K + Bᵢ)` is an integral Cartier divisor. -/
  isCartier : ∀ i, ∃ D : Divisor X, D.IsCartier ∧
    ∀ P, (m : ℚ) * ((K.coeff P : ℚ) + (boundary i).coeff P) = D.coeff P

end NullData

end MMP.Fourfold
