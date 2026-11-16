module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics

/-!
# A klt pair has finitely many exceptional divisors of log discrepancy at most one

Let `(X, B)` be a Kawamata log terminal pair. Only finitely many exceptional divisors `E` of
`k(X)` with center on `X` have log discrepancy `a_ℓ(E, X, B) ≤ 1`. Equivalently, the set
`𝓔(X, B)` of `MMP.Flips.smallDiscrepancySet` is finite, so the count `e(X, B)` of
`MMP.Flips.eCount` is a natural number.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.finite_smallDiscrepancySet`: the statement above.

## Implementation notes

An exceptional divisor of `k(X)` with center on `X` is the valuation `ord_E` of an exceptional
divisor `(Y, f, E)` over `X` with `f` proper. The set counts valuations, not models. The condition
`a(E, X, B) ≤ 0` that defines `MMP.Flips.smallDiscrepancySet` is the same as `a_ℓ(E, X, B) ≤ 1`, by
`MMP.Flips.mem_smallDiscrepancySet_iff_logDiscrepancy`.

The proof reduces to `MMP.Fourfold.IsRealKltPair.finite_setOf_isLogDiscrepancy_le_one`, the same
finiteness for real klt pairs (FA 4.12.2). A klt pair in the sense of FA is a real klt pair: a
prime divisor `P` of `X` has log discrepancy `1 - b_P > 0`, and a log discrepancy computed on a
proper model `(Y, f, E)` is `1` plus the discrepancy of `ord_E`. Two notions of log discrepancy
meet here: `MMP.Flips.IsLogDiscrepancy` (computed with a fixed canonical divisor) and
`MMP.Intersection.IsLogDiscrepancy` (computed on a proper model with any rational top form and
any Cartier presentation); they agree by `MMP.Flips.IsDiscrepancyWith.eq`. Likewise both notions
of exceptional divisor over `X` say that `f(η_E)` has coheight at least two.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2, 6.6
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Fourfold
open MMP.Mori hiding IsLogResolution exceptionalSet

/-- If `d + c = n`, then `d + 2 ≤ n` exactly when `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

section Dictionary

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- A divisor over `X` is exceptional exactly when its center has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) :
    E.IsExceptional ↔ 2 ≤ Order.coheight (E.f E.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (E.f E.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor over a normal variety is exceptional (in the sense of Kollár–Mori) if and only if
its center has codimension at least two. -/
private theorem divisorOver_isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

variable [CompactSpace X] [LocallyOfFiniteType sX]

/-- A presentation of `div(ω) + B`, coefficientwise, is a presentation as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum_of_coeff {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) :
    Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
  ext Γ
  change (Divisor.toRDivisor (divisorOfForm ω) + B).coeff Γ =
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
  rw [coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    coeff_divisorOfForm]
  exact h Γ

/-- A datum computing the discrepancy `a_ω(E, B)`, with `div(ω)` a canonical divisor, computes
the log discrepancy `1 + a_ω(E, B)`. -/
private theorem isLogDiscrepancy_one_add_of_isDiscrepancyWith {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {a : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n B ω r L E a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hLc,
    fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

/-- Every presentation of `div(ω) + B` by Cartier divisors computes a discrepancy on every
proper model. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ a, IsDiscrepancyWith sX n B ω r L E a := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨(E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E.E : ℝ), hX, hn, hω0,
    hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- A discrepancy computed with a fixed canonical divisor `K` gives the log discrepancy of any
proper model of the valuation. -/
private theorem isLogDiscrepancy_of_isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X}
    {B : RDivisor X} {E : ProperDivisorOver k sX} {a : ℝ}
    (h : IsDiscrepancy sX n K B E.valuation a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E', ω, m, r, L, hv, rfl, hw⟩ := h
  obtain ⟨hX, hn, hω0, hLc, hsum, -⟩ := id hw
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum E
  obtain rfl := hc.eq hw hv.symm
  exact isLogDiscrepancy_one_add_of_isDiscrepancyWith hK hc

/-- A log discrepancy `a` of a proper model `E` gives the discrepancy `a - 1` of its valuation,
computed with any canonical divisor `K` for which `K + B` is `ℝ`-Cartier. -/
private theorem isDiscrepancy_of_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    {n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) {E : ProperDivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n' B E.toDivisorOver a) :
    IsDiscrepancy sX n K B E.valuation (a - 1) := by
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨-, -, ω', hω0', ⟨K', hK', hK'ω⟩, m', r', C, C', hCc, hsum', hpb, ha⟩ := h
  obtain rfl : n = n' := by
    have h' := hK'.topologicalKrullDim_eq
    rw [hn] at h'
    exact_mod_cast h'
  have hw' : IsDiscrepancyWith sX n B ω' r' C E (a - 1) :=
    ⟨hX, hn, hω0', hCc, toRDivisor_add_eq_sum_of_coeff hsum', C', hpb, by linarith⟩
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum₁ : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum₁ E
  rw [← hc.eq hw' rfl]
  exact ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation E, E, ω, m, r, L, rfl, rfl, hc⟩

end Dictionary

section Klt

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX]

/-- A klt pair in the sense of *Flips and abundance* is a real klt pair. -/
private theorem isRealKltPair_of_isKawamataLogTerminal {n : ℕ} {K : Divisor X} {B : RDivisor X}
    (h : IsKawamataLogTerminal sX n K B) : IsRealKltPair sX B := by
  obtain ⟨hlv, hK, hKB, hpos⟩ := h
  have hX : IsNormalVariety k sX := hlv.isNormalVariety
  refine ⟨hX, fun P => ?_, ⟨n, K, hK, ?_⟩, fun n' E a ha => ?_⟩
  · obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
    obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
    have hP := isDiscrepancy_divisorialValuation hX ω hω0 hK hKB P
    have := hpos _ hP.2.2.1 _ ⟨_, hP, rfl⟩
    linarith
  · obtain ⟨m, r, L, hLc, hsum⟩ := hKB
    refine ⟨m, r, L, hLc, fun Γ => ?_⟩
    have hsum' : Divisor.toRDivisor K + B = ∑ j, r j • Divisor.toRDivisor (L j) := by
      simpa only [toRDivisor_eq_mapCoeffs] using hsum
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum'
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      coeff_sum_smul_toRDivisor] at this
    rw [← this]
    rfl
  · let E₀ : ProperDivisorOver k sX := ⟨E, ha.2.1⟩
    have hd := isDiscrepancy_of_isLogDiscrepancy hX hK hKB (E := E₀) ha
    have := hpos _ (hasNonemptyCenter_valuation E₀) _ ⟨_, hd, rfl⟩
    linarith

end Klt

/-- **FA 6.6.** Let `(X, B)` be a Kawamata log terminal pair, with `X` of dimension `n` and
canonical divisor `K`. Only finitely many exceptional divisors `E` of `k(X)` with center on `X`
satisfy `a_ℓ(E, X, B) ≤ 1`, that is, `𝓔(X, B)` is finite. -/
@[mmp "lem_fa6_klt_finitely_many_small_log_discrepancy"]
public theorem IsKawamataLogTerminal.finite_smallDiscrepancySet {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : RDivisor X} (h : IsKawamataLogTerminal sX n K B) :
    (smallDiscrepancySet sX n K B).Finite := by
  refine (isRealKltPair_of_isKawamataLogTerminal h).finite_setOf_isLogDiscrepancy_le_one.subset ?_
  rintro v ⟨⟨E, hEex, rfl⟩, a, ha, ha0⟩
  refine ⟨n, E.toDivisorOver, 1 + a, ?_, rfl, isLogDiscrepancy_of_isDiscrepancy ha, by linarith⟩
  exact (divisorOver_isExceptional_iff_two_le_coheight h.1.isNormalVariety _).mpr
    ((isExceptional_iff_two_le_coheight h.2.1.topologicalKrullDim_eq E).mp hEex)

end MMP.Flips
