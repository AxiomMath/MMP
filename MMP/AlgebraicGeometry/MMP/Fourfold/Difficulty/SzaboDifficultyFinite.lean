module
public import MMP.AlgebraicGeometry.Singularities.KltSmallDiscrepancyCenters

/-!
# Finiteness of small log discrepancies and of Szabó's difficulty

Let `(X, D)` be a Kawamata log terminal pair, with `D = ∑ⱼ dⱼ Dⱼ` an effective `ℚ`-divisor. Then
only finitely many exceptional divisors `ν` of `k(X)` with nonempty center on `X` satisfy
`a_ℓ(ν, X, D) < 1 + logdiscrep(X, D)`, `a_ℓ(ν, X, D) < 2` and `a_ℓ(ν, X, D) < 2 - dⱼ` for every
`j`. Here `logdiscrep(X, D) = 1 + discrep(X, D)`.

Let `(X, D)` be a canonical pair with `⌊D⌋ = 0`, let `N ≥ 1` be an integer with `N dⱼ ∈ ℤ` for
all `j`, `c ≥ 0` rational, and `B ⊆ X` a closed subset containing every `Dⱼ` with `dⱼ > c`. Then
Szabó's modified difficulty `d_{N,c}(X, D; B)` is finite. Indeed `(X, D)` is klt and every
exceptional divisor with nonempty center has log discrepancy `≥ 1`, so `𝒮_t(X, D; B)` is empty
for `t ≤ 1` and only the terms `Nc ≤ i < N` of the difficulty can be nonzero. Each of these is
finite: a divisor of `𝒮_t(X, D; B)`, `t ≤ 2 - c`, outside the finite set of
`MMP.Flips.IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min_of_charZero` would
have its center of codimension `2` inside a component `Dⱼ` with `dⱼ > c`, hence inside `B`.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.finite_setOf_logDiscrepancy_lt`: over a klt pair, only
  finitely many exceptional divisors have small log discrepancy.
* `MMP.Flips.IsCanonicalPair.szaboDifficulty_ne_top_of_charZero`: Szabó's modified difficulty
  of a canonical pair with `⌊D⌋ = 0` over a field of characteristic zero is finite.
* `MMP.Flips.IsCanonicalPair.szaboDifficulty_ne_top`: its specialization to an algebraically
  closed field.

## Implementation notes

* An exceptional divisor of `k(X)` with nonempty center on `X` is a valuation `ν` of `k(X)` with
  `MMP.Flips.HasNonemptyCenter` that is the valuation of an exceptional divisor `(Y, f, E)` over
  `X`, as in `MMP.Flips.smallLogDiscrepancySet`; the set counts valuations, not models.
* The components `Dⱼ` of `D` are the prime divisors `P` with `D.coeff P ≠ 0`, and
  `dⱼ = D.coeff P`; the integrality condition `N dⱼ ∈ ℤ` is imposed on every prime divisor,
  which is the same since it holds trivially where the coefficient vanishes.
* The bound `1 + logdiscrep(X, D)` is taken in `EReal`, where `MMP.Flips.discrep` lives.
* `d_{N,c}(X, D; B)` is `MMP.Flips.szaboDifficulty`, valued in `ℕ∞`; finiteness is `≠ ⊤`.
  Its normality, canonical-divisor and `ℚ`-Cartier arguments are read off the canonical pair.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2.2,
  4.14
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori hiding IsCanonicalPair

/-- **FA 4.12.2.2.** Let `(X, D)` be a Kawamata log terminal pair, `X` of dimension `n` with
canonical divisor `K`, and `D` an effective `ℚ`-divisor. Only finitely many exceptional divisors
`ν` of `k(X)` with nonempty center on `X` have a log discrepancy `b = a_ℓ(ν, X, D)` with
`b < 1 + logdiscrep(X, D) = 2 + discrep(X, D)`, `b < 2`, and `b < 2 - D.coeff P` for every
component `P` of `D`. -/
@[mmp "lem_fa4_klt_finitely_many_small_log_discrepancy"]
public theorem IsKawamataLogTerminal.finite_setOf_logDiscrepancy_lt {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (h : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D)) (hD : D.IsEffective) :
    {ν : Valuation X.functionField ℤᵐ⁰ | HasNonemptyCenter k sX ν ∧
      (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) ∧
      ∃ b : ℝ, IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) ν b ∧
        (b : EReal) < 1 + (1 + discrep sX n D) ∧ b < 2 ∧
        ∀ P : Mori.PrimeDivisor X, D.coeff P ≠ 0 → b < 2 - (D.coeff P : ℝ)}.Finite := by
  obtain ⟨𝒩, h𝒩, -, hmem⟩ := h.exists_finite_forall_logDiscrepancy_lt_min sX hD
  refine h𝒩.subset fun ν ⟨hc, hE, b, hb, h1, h2, h3⟩ => by_contra fun hν => ?_
  obtain ⟨P, hP, hle, -⟩ := hmem ν hν hc hE b hb (lt_min (EReal.coe_lt_coe_iff.mpr h2) h1)
  exact (h3 P hP.ne').not_ge hle

/-- Every divisor over `X` has a discrepancy `a_ω(E, X, D)` with respect to a pair `(X, D)` with
`K_X + D` `ℚ`-Cartier. -/
private theorem exists_isQDiscrepancyWith {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} (hX : IsNormalVariety k sX)
    (hK : K.IsCanonicalDivisor sX n) (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (E : ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), IsQDiscrepancyWith sX n D ω E a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hKD' : (Divisor.toQDivisor (divisorOfForm ω) + D).IsQCartier := hdiv ▸ hKD
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' E.f
    (Divisor.toQDivisor (divisorOfForm ω) + D)
  obtain ⟨G, hG, -⟩ := hKD'.existsUnique_isPullback hB
  exact ⟨ω, _, hX, hK.1, hω0, hKD', hB, G, hG, rfl⟩

/-- A `ℚ`-Cartier combination `K + D` is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_of_isQCartier {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {K : Divisor X} {D : QDivisor X}
    (hKD : (Divisor.toQDivisor K + D).IsQCartier) :
    IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hKD.exists_pos
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  simp only [← Flips.toRDivisor_eq_mapCoeffs]
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have := congrArg (fun G : QDivisor X => ((G.coeff Γ : ℚ) : ℝ)) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    zsmul_eq_mul, Int.cast_natCast] at this
  push_cast at this
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, this]
  field_simp

section CanonicalPair

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D : QDivisor X}

/-- Over a canonical pair, every exceptional divisor with nonempty center has log
discrepancy `≥ 1`. -/
private theorem IsCanonicalPair.one_le_of_isLogDiscrepancy (h : IsCanonicalPair sX n K D)
    {E : ProperDivisorOver k sX} (hE : E.IsExceptional) {b : ℝ}
    (hb : IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation b) : 1 ≤ b := by
  obtain ⟨hX, hK, -, hKD, hd⟩ := h
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨ω, a', h'⟩ := exists_isQDiscrepancyWith hX hK hKD E
  have haa : a = a' := ha.eq (h'.isDiscrepancy hK hKD hE)
  have hle : discrep sX n D ≤ ((a' : ℝ) : EReal) := sInf_le ⟨E, ω, a', hE, h', rfl⟩
  have : (0 : ℝ) ≤ a' := EReal.coe_nonneg.mp (hd.trans hle)
  linarith

/-- A canonical pair `(X, D)` with `⌊D⌋ = 0` is Kawamata log terminal. -/
private theorem IsCanonicalPair.isKawamataLogTerminal_of_roundDown_eq_zero
    (h : IsCanonicalPair sX n K D) (hD0 : DivisorWithCoeffs.roundDown D = 0) :
    IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D) := by
  have ⟨hX, hK, hDe, hKD, _⟩ := h
  have hlt : ∀ P : Mori.PrimeDivisor X, D.coeff P < 1 :=
    roundDown_nonpos_iff.mp (le_of_eq hD0)
  refine ⟨⟨hX, fun P => ?_⟩, hK, isCartierCombination_of_isQCartier hKD, ?_⟩
  · rw [QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hDe P, by exact_mod_cast (hlt P).le⟩
  · rintro F ⟨-, E, rfl⟩ b hb
    by_cases hE : E.IsExceptional
    · linarith [h.one_le_of_isLogDiscrepancy hE hb]
    · obtain ⟨P, -, -, -, hP⟩ := E.exists_primeDivisor_of_not_isExceptional hX hE
      obtain ⟨a, ha, rfl⟩ := hb
      rw [hP] at ha
      have := ha.eq_neg_coeff
      rw [QDivisor.coeff_toRDivisor] at this
      have : ((D.coeff P : ℚ) : ℝ) < 1 := by exact_mod_cast hlt P
      linarith

/-- Over a canonical pair, `𝒮_t(X, D; B)` is empty for `t ≤ 1`. -/
private theorem IsCanonicalPair.smallLogDiscrepancySetOff_eq_empty_of_le_one
    (h : IsCanonicalPair sX n K D) (B : Closeds X) {t : ℚ} (ht : t ≤ 1) :
    smallLogDiscrepancySetOff sX n K D h.1 h.2.1 h.2.2.2.1 B t = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro _ ⟨⟨-, ⟨E, hE, rfl⟩, b, hb, hbt⟩, -⟩
  have : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  linarith [h.one_le_of_isLogDiscrepancy hE hb]

/-- Over a canonical pair `(X, D)` with `⌊D⌋ = 0`, `𝒮_t(X, D; B)` is finite for `t ≤ 2 - c`,
provided `B` contains every component `Dⱼ` with `dⱼ > c ≥ 0`. -/
private theorem IsCanonicalPair.finite_smallLogDiscrepancySetOff (h : IsCanonicalPair sX n K D)
    (hD0 : DivisorWithCoeffs.roundDown D = 0) {c : ℚ} (hc : 0 ≤ c) {B : Closeds X}
    (hB : ∀ P : Mori.PrimeDivisor X, c < D.coeff P → P.support ⊆ B) {t : ℚ} (ht : t ≤ 2 - c) :
    (smallLogDiscrepancySetOff sX n K D h.1 h.2.1 h.2.2.2.1 B t).Finite := by
  have hklt := h.isKawamataLogTerminal_of_roundDown_eq_zero hD0
  obtain ⟨𝒩, h𝒩, -, hmem⟩ := hklt.exists_finite_forall_logDiscrepancy_lt_min_of_charZero sX h.2.2.1
  refine h𝒩.subset fun ν ⟨⟨hcen, hEx, b, hb, hbt⟩, hoff⟩ => by_contra fun hν𝒩 => ?_
  have hbc : b < 2 - c := by
    have : (t : ℝ) ≤ 2 - c := by exact_mod_cast ht
    linarith
  have hb2 : (b : EReal) < 2 := by
    have : (0 : ℝ) ≤ c := by exact_mod_cast hc
    exact EReal.coe_lt_coe_iff.mpr (by linarith : b < 2)
  have h2 : (2 : EReal) ≤ 1 + (1 + discrep sX n D) := by
    calc (2 : EReal) = 1 + (1 + 0) := by rw [add_zero, one_add_one_eq_two]
      _ ≤ 1 + (1 + discrep sX n D) := by gcongr; exact h.2.2.2.2
  obtain ⟨P, -, hle, hall⟩ := hmem ν hν𝒩 hcen hEx b hb (lt_min hb2 (hb2.trans_le h2))
  obtain ⟨E, -, hEν⟩ := hEx
  obtain ⟨hcod, hsub, -⟩ := hall E hEν
  have hcP : c < D.coeff P := by exact_mod_cast (by linarith : (c : ℝ) < D.coeff P)
  exact hoff E hEν ⟨hcod, hsub.trans (hB P hcP)⟩

/-- Over a canonical pair, only the indices `Nc ≤ i < N` contribute to `d_{N,c}(X, D; B)`: for
`i ≥ N` the term `𝒮_{2 - i/N}(X, D; B)` is empty. -/
private theorem support_encard_smallLogDiscrepancySetOff_subset (h : IsCanonicalPair sX n K D)
    (B : Closeds X) {N : ℕ} (hN : 1 ≤ N) {c : ℚ} (hc : 0 ≤ c) :
    Function.support (fun i : {i : ℤ // (N : ℚ) * c ≤ i} =>
      (smallLogDiscrepancySetOff sX n K D h.1 h.2.1 h.2.2.2.1 B (2 - (i : ℚ) / N)).encard) ⊆
      (Finset.Ico 0 (N : ℤ)).subtype fun i : ℤ => (N : ℚ) * c ≤ i := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  refine Function.support_subset_iff'.mpr fun i hi => ?_
  simp only [Finset.mem_coe, Finset.mem_subtype, Finset.mem_Ico, not_and, not_lt] at hi
  have hNi : (N : ℚ) ≤ i :=
    by exact_mod_cast hi (by exact_mod_cast (mul_nonneg hN0.le hc).trans i.2)
  rw [h.smallLogDiscrepancySetOff_eq_empty_of_le_one B, Set.encard_empty]
  linarith [(one_le_div hN0).mpr hNi]

/-- FA 4.14 over any field of characteristic zero: Szabó's modified difficulty
`d_{N,c}(X, D; B)` of a canonical pair with `⌊D⌋ = 0` is finite. -/
public theorem IsCanonicalPair.szaboDifficulty_ne_top_of_charZero (h : IsCanonicalPair sX n K D)
    (hD0 : DivisorWithCoeffs.roundDown D = 0) {N : ℕ} (hN : 1 ≤ N) {c : ℚ} (hc : 0 ≤ c)
    {B : Closeds X} (hB : ∀ P : Mori.PrimeDivisor X, c < D.coeff P → P.support ⊆ B) :
    szaboDifficulty sX n K D h.1 h.2.1 h.2.2.2.1 B N hN c ≠ ⊤ := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  rw [szaboDifficulty, tsum_eq_sum' (support_encard_smallLogDiscrepancySetOff_subset h B hN hc)]
  refine (ENat.sum_lt_top.mpr fun i _ => (Set.encard_ne_top_iff.mpr
    (h.finite_smallLogDiscrepancySetOff hD0 hc hB ?_)).lt_top).ne
  linarith [(le_div_iff₀ hN0).mpr (by linarith [i.2] : c * N ≤ i)]

end CanonicalPair

/-- **FA 4.14.** Let `(X, D)` be a canonical pair, `X` of dimension `n` with canonical divisor
`K`, with `⌊D⌋ = 0`. Let `N ≥ 1` be an integer with `N · D.coeff P ∈ ℤ` for every prime divisor
`P`, `c ≥ 0` rational, and `B ⊆ X` a closed subset containing every prime divisor `P` with
`D.coeff P > c`. Then Szabó's modified difficulty `d_{N,c}(X, D; B)` is finite; this is
`IsCanonicalPair.szaboDifficulty_ne_top_of_charZero` over an algebraically closed field. -/
@[mmp "lem_fa4_szabo_difficulty_finite"]
public theorem IsCanonicalPair.szaboDifficulty_ne_top {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} (h : IsCanonicalPair sX n K D)
    (hD0 : DivisorWithCoeffs.roundDown D = 0) {N : ℕ} (hN : 1 ≤ N)
    (_hDN : ∀ P : Mori.PrimeDivisor X, ∃ m : ℤ, (N : ℚ) * D.coeff P = m)
    {c : ℚ} (hc : 0 ≤ c) {B : Closeds X}
    (hB : ∀ P : Mori.PrimeDivisor X, c < D.coeff P → P.support ⊆ B) :
    szaboDifficulty sX n K D h.1 h.2.1 h.2.2.2.1 B N hN c ≠ ⊤ :=
  h.szaboDifficulty_ne_top_of_charZero hD0 hN hc hB

end MMP.Flips
