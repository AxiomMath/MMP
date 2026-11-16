module

public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.PairClasses
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.TerminalIffCountZero

/-!
# Terminal pairs are terminal in the sense of *Flips and abundance*

Let `(X, D)` be a pair with an effective `ℚ`-boundary `D` which is terminal in Kollár–Mori's
convention: it is klt and every exceptional divisorial valuation `v` of `k(X)` has log discrepancy
`a(v; X, D) > 1`. Then `(X, D)` is terminal in the convention of *Flips and abundance*:
for every canonical divisor `K` of `X`, `K + D` is `ℚ`-Cartier and `discrep(X, D) > 0`.

## Main results

* `MMP.Fourfold.IsKltTerminalPair.isTerminalPair`: the statement above.

## Implementation notes

The ground field is an algebraically closed field of characteristic zero rather than `ℂ`.
Terminality in the sense of *Flips and abundance* (`MMP.Flips.IsTerminalPair`) is relative to a
chosen canonical divisor `K` of dimension `n`; the conclusion holds for every such `K`, since
canonical divisors are linearly equivalent and `discrep(X, D)` does not depend on `K`.

The proof compares the two conventions. The data computing a discrepancy `a(F, D)` of *Flips and
abundance* are a divisor `(Y, f, E)` over `X` with `f` proper, and the same data compute the
Kollár–Mori log discrepancy `1 + a(F, D)`. So `(X, D)` is Kawamata log terminal in the sense of
*Flips and abundance*, and no exceptional divisor has `a(E, D) ≤ 0`. That gives `e(X, D) = 0`,
and FA 6.6 (`MMP.Flips.IsKawamataLogTerminal.isTerminalPair_iff_eCount_eq_zero`) makes the pair
terminal.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 1.16, 6.6
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The data computing a discrepancy `a(F, B)` of *Flips and abundance* compute the log
discrepancy `1 + a(F, B)` of a divisor over `X` with valuation `F`. -/
private theorem exists_isLogDiscrepancy_of_isDiscrepancy {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {B : RDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ} (h : MMP.Flips.IsDiscrepancy sX n K B F a) :
    ∃ E : MMP.Flips.ProperDivisorOver k sX, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, hω, hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨K, hK, fun Γ => by rw [← hω]; rfl⟩, m, r, L, L',
    hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Flips.coeff_sum_smul_toRDivisor] using this

/-- A `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-combination of Cartier divisors: if `mD = M` with `M`
Cartier, then `D = m⁻¹ M`. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := h
  refine ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => M, fun _ => hMc, DivisorWithCoeffs.ext' fun Γ => ?_⟩
  have hΓ := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hΓ
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs, Fin.sum_univ_one, QDivisor.coeff_toRDivisor,
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
  rw [← Rat.cast_intCast (M.coeff Γ), hΓ]
  push_cast
  field_simp

/-- If `d + c = n` and `d + 2 ≤ n` in `WithBot ℕ∞`, then `2 ≤ c`. -/
private theorem two_le_of_add_eq {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n)
    (h2 : d + 2 ≤ n) : 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => exact le_top
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have h2' : d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le] at h2
          exact h2
        exact_mod_cast (show 2 ≤ c by omega)

/-- A divisor over `X` whose valuation is that of an exceptional divisor over `X` (in the sense of
*Flips and abundance*) is exceptional: its centre has codimension at least two, so its valuation is
not that of a prime divisor of `X`. -/
private theorem isExceptional_of_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {E E' : MMP.Flips.ProperDivisorOver k sX}
    (hE : E.IsExceptional) (hv : E'.valuation = E.valuation) :
    E'.toDivisorOver.IsExceptional := by
  by_contra hne
  obtain ⟨P, hPv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hne
  unfold MMP.Flips.ProperDivisorOver.IsExceptional at hE
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn] at hE
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (E.f E.E.genericPoint)
  rw [hn] at h
  have h2 : 2 ≤ codimension E.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact two_le_of_add_eq h hE
  exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX _).mp h2 P (hv.symm.trans hPv)

/-- An effective `ℚ`-boundary pair `(X, D)` that is terminal in Kollár–Mori's sense
(`MMP.Fourfold.IsKltTerminalPair`) is terminal in the sense of *Flips and abundance*
(`MMP.Flips.IsTerminalPair`) with respect to every canonical divisor `K` of `X`. -/
@[mmp "lem_mmp_indexc_terminal_is_fa_terminal"]
public theorem IsKltTerminalPair.isTerminalPair {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {D : QDivisor X}
    (h : IsKltTerminalPair sX D) (hD : D.IsEffective) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : MMP.Flips.IsTerminalPair sX n K D := by
  obtain ⟨⟨hP, hpos⟩, hterm⟩ := h
  obtain ⟨hX, n', K', hK', hQ'⟩ := hP.isPair
  have hKBc : MMP.Flips.IsCartierCombination
      (Divisor.toRDivisor K + QDivisor.toRDivisor D) := by
    simpa [QDivisor.toRDivisor_toQDivisor] using isCartierCombination_toRDivisor
      (hQ'.add_of_linearlyEquivalent
        (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK))
  have hlog : ∀ F a, MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor D) F a → 0 < 1 + a :=
    fun _ _ ha => (exists_isLogDiscrepancy_of_isDiscrepancy ha).elim fun _ hE => hpos n _ _ hE.2
  have hklt : MMP.Flips.IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D) := by
    refine ⟨⟨hX, fun P => ⟨by simpa using hD P, ?_⟩⟩, hK, hKBc, ?_⟩
    · obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
      obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
      linarith [hlog _ _ (MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω0 hK hKBc P)]
    · rintro F - b ⟨a, ha, rfl⟩
      exact hlog F a ha
  rw [MMP.Flips.IsKawamataLogTerminal.isTerminalPair_iff_eCount_eq_zero sX hklt,
    MMP.Flips.eCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨E, hEx, rfl⟩, a, ha, ha0⟩
  obtain ⟨E', hE'v, hE'⟩ := exists_isLogDiscrepancy_of_isDiscrepancy ha
  linarith [hterm n _ _ (isExceptional_of_valuation_eq hX hK.topologicalKrullDim_eq hEx hE'v) hE']

end MMP.Fourfold
