module
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties

/-!
# Log discrepancy conventions

Let `(X, B)` be a pair with rational boundary: a normal variety `X` of dimension `n`, a
`ℚ`-divisor `B` and a canonical divisor `K_X` with `K_X + B` `ℚ`-Cartier. For a prime divisor
`E` on a model `p : W ⟶ X` (a proper birational morphism from a smooth variety), Kollár–Mori's
log discrepancy `a(E; X, B) = 1 + coeff_E(K_W - p^*(K_X + B))` and the log discrepancy
`a_ℓ(E, B) = 1 + a(E, B)` of *Flips and abundance* coincide: both are one plus the coefficient of
`E` in `K_W - p^*(K_X + B)`, with `K_X = div(ω)` and `K_W = div(p^*ω)` for the same rational top
form `ω`. Any datum computing the discrepancy of *Flips and abundance* computes Kollár–Mori's
log discrepancy, and the latter is unique.

## Main results

* `MMP.Flips.ProperDivisorOver.isLogDiscrepancy_iff`: the two log discrepancies agree.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.5, 2.7
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A datum computing the discrepancy `a_ω(E, D_X)` of *Flips and abundance*, with `div(ω)` a
canonical divisor, computes Kollár–Mori's log discrepancy `1 + a_ω(E, D_X)`. -/
private theorem isLogDiscrepancy_one_add_of_isDiscrepancyWith {n : ℕ} {D_X : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {a : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D_X ω r L E a) :
    MMP.Intersection.IsLogDiscrepancy sX n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hLc,
    fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

/-- Every presentation of `div(ω) + D_X` by Cartier divisors computes a discrepancy on every
proper model. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D_X : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D_X = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ a, IsDiscrepancyWith sX n D_X ω r L E a := by
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

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- The valuation of a proper model is a divisor of `k(X)` with nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have hbij := E.isBirationalMorphism.functionFieldMap_bijective
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (E.f ≫ sX)
  let := functionFieldMapAlgebra E.f
  have := isScalarTower_functionFieldMap sX E.f
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E, AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k X.functionField E.Y.functionField) hbij, rfl⟩, E, rfl⟩

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] in
/-- If `M = m • (K + B)` with `m > 0`, then `K + B = (1 / m) • M` as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_one_div_smul {K M : Divisor X} {B : QDivisor X} {m : ℕ}
    (hm : 0 < m) (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
  ext Γ
  have hMΓ : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    simpa [mul_add] using congrArg (fun G : QDivisor X => G.coeff Γ) hM
  replace hMΓ : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast hMΓ
  rw [coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    QDivisor.coeff_toRDivisor, Fin.sum_univ_one, hMΓ]
  field_simp

/-- **The two conventions for log discrepancies agree.** Let `(X, B)` be a pair with canonical
divisor `K` of dimension `n` and rational boundary `B`, and let `E` be a prime divisor on a
smooth variety `W` with a proper birational morphism `W ⟶ X`. Then a real number `a` is
Kollár–Mori's log discrepancy `a(E; X, B)` (`MMP.Intersection.IsLogDiscrepancy`) if and only if
it is the log discrepancy `a_ℓ(ord_E, B)` of *Flips and abundance*
(`MMP.Flips.IsLogDiscrepancy`) computed with `K`.

Writing `K = div(ω)` and `K + B = (1/m) • M` with `M` Cartier, the data `(ω, M)` compute a
discrepancy `c` of *Flips and abundance* on `E`, which is a datum for Kollár–Mori's log
discrepancy `1 + c`; conversely any datum for the *Flips and abundance* side is recomputed on `E`
itself, where its value is independent of the model. -/
@[mmp "lem_mmp_discrepancy_dictionary"]
public theorem ProperDivisorOver.isLogDiscrepancy_iff [PerfectField k] {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hB : IsPairWith sX n K B) (E : ProperDivisorOver k sX)
    (hW : IsSmoothScheme (E.f ≫ sX)) (a : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E.toDivisorOver a ↔
      IsLogDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation a := by
  obtain ⟨hX, hK, hQ⟩ := hB
  have hn := hK.topologicalKrullDim_eq
  constructor
  · intro h
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
    obtain rfl : divisorOfForm ω = K := Finsupp.ext hω
    obtain ⟨m, hm, M, hM, hMc⟩ := hQ.exists_pos
    have hsum := toRDivisor_add_eq_one_div_smul hm hM
    obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 (fun _ => hMc) hsum E
    exact ⟨c, ⟨hK, ⟨1, _, _, fun _ => hMc, hsum⟩, hasNonemptyCenter_valuation E, E, ω, 1, _, _,
      rfl, rfl, hc⟩, MMP.Threefold.Bridges.IsLogDiscrepancy.unique h
        (isLogDiscrepancy_one_add_of_isDiscrepancyWith hK hc)⟩
  · rintro ⟨c, ⟨hK', -, -, E', ω, m, r, L, hv, rfl, hw⟩, rfl⟩
    obtain ⟨-, -, hω0, hLc, hsum, -⟩ := id hw
    obtain ⟨d, hd⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum E
    obtain rfl := hd.eq hw hv.symm
    exact isLogDiscrepancy_one_add_of_isDiscrepancyWith hK' hd

end MMP.Flips

end
