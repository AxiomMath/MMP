module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Discrepancies, klt and dlt pairs

Results of Kollár–Mori, Sections 2.3, on the discrepancies `a(E, X, Δ)` of divisors over a
pair `(X, Δ)` and on klt and dlt pairs. Throughout, `X` is a normal variety over an algebraically
closed field `k` of characteristic zero (Kollár–Mori's standing field), `K` a canonical divisor of
`X` of dimension `n` and `Δ` a `ℚ`-divisor; the discrepancy is the relation
`MMP.Mori.IsDiscrepancy`, the discrepancy of the pair is `MMP.Mori.discrep`.

## Main results

* `MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback`: a `ℚ`-divisor `Δ'` on `Y` with
  `K_Y + Δ' = f^*(K_X + Δ)` and `f_* K_Y = K_X` is the crepant boundary.
* `MMP.Threefold.Mori.exists_isDiscrepancyNoBoundary`,
  `MMP.Threefold.Mori.isDiscrepancyNoBoundary_iff_isDiscrepancy_zero`: `a(E, X)` exists and
  equals `a(E, X, 0)`; it is independent of the choices by `MMP.Mori.IsDiscrepancyNoBoundary.eq`.
* `MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq`: `a(E, X, Δ)` depends only on the
  valuation of `E`.
* `MMP.Threefold.Mori.discrepancy_antitone_of_add`: adding an effective `ℚ`-Cartier divisor
  lowers discrepancies.
* `MMP.Threefold.Mori.discrep_eq_bot_of_totalDiscrep_lt`,
  `MMP.Threefold.Mori.discrep_eq_bot_or_bounds`: `totaldiscrep < -1` forces `discrep = -∞`.
* `MMP.Threefold.Mori.discrep_add_smul_eq_inf'_of_small`: near `ε = 0`, `discrep(X, Δ + εΔ')` is
  a minimum of finitely many affine functions of `ε`.
* `MMP.Threefold.Mori.discrep_eq_of_isSNC`: the discrepancy of an snc pair on a smooth variety.
* `MMP.Threefold.Mori.IsKltPair.of_add`, `MMP.Threefold.Mori.IsKltPair.exists_add_smul`:
  klt is preserved by removing, and by adding a small multiple of, an effective `ℚ`-Cartier
  divisor.
* `MMP.Threefold.Mori.IsKltPair.isDltPair`, `MMP.Threefold.Mori.IsDltPair.of_add`,
  `MMP.Threefold.Mori.IsDltPair.isKltPair_iff_roundDown_eq_zero`: klt and dlt pairs.
* `MMP.Threefold.Mori.IsDltPair.exists_open_nonempty`: the closed set of a dlt pair may be taken
  proper.
* `MMP.Threefold.Mori.exists_isLogResolution_isSNCSubset_preimage`,
  `MMP.Threefold.Mori.exists_isLogResolution_inverseTransform_smooth`: existence of log
  resolutions.
* `MMP.Threefold.Mori.exists_pos_le_isDiscrepancy_of_isLogResolution`,
  `MMP.Threefold.Mori.isDltPair_iff_exists_isLogResolution`: the dlt criterion on a log
  resolution.
* `MMP.Threefold.Mori.IsDltPair.exists_perturbation_isDltPair`,
  `MMP.Threefold.Mori.IsDltPair.exists_perturbation_isKltPair`: perturbations of dlt pairs.

## Implementation notes

The closed subset `Z` of a dlt pair is the complement of an open `U`; `Z ≠ X` is `U` nonempty.
"`a(E, X, Δ) > -1`" is encoded as in `MMP.Mori.IsDltPair`: every number that is the discrepancy
is `> -1`. A divisor `F` of a model `f : Y ⟶ X` is regarded as the divisor `(Y, f, F)` over `X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.22–2.43
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-! ### Discrepancies -/

omit [IsAlgClosed k] [CharZero k] in
/-- **`a(E, X) = a(E, X, 0)`** (KM Definition 2.22). For an exceptional divisor `(Y, f, E)` over
`X`, a number is computed as in `MMP.Mori.IsDiscrepancyNoBoundary` exactly when it is the
discrepancy `a(E, X, 0)` of the pair `(X, 0)`. -/
theorem isDiscrepancyNoBoundary_iff_isDiscrepancy_zero {D : DivisorOver k sX}
    (hD : D.IsExceptional) (a : ℚ) :
    IsDiscrepancyNoBoundary sX n K D a ↔ IsDiscrepancy sX n K 0 D a :=
  isDiscrepancyNoBoundary_iff.trans (and_iff_right hD)

/-- **Discrepancies decrease when an effective divisor is added** (Kollár–Mori 2.27, first
assertion). For a pair `(X, Δ)` and an effective `ℚ`-Cartier `ℚ`-divisor `Δ'`,
`a(E, X, Δ) ≥ a(E, X, Δ + Δ')` for every divisor `E` over `X`. -/
@[mmp "lem_km2b_discrepancy_monotone"]
theorem discrepancy_antitone_of_add (hΔ : IsPairWith sX n K Δ) {Δ' : QDivisor X}
    (hΔ'e : Δ'.IsEffective) (hΔ'q : Δ'.IsQCartier) (D : DivisorOver k sX) {a a' : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (ha' : IsDiscrepancy sX n K (Δ + Δ') D a') : a' ≤ a :=
  Helpers.isDiscrepancy_le_of_effective hΔ'e ha ha'

/-! ### Klt pairs -/

/-- **Klt is preserved by removing an effective divisor** (Kollár–Mori 2.35(1), klt case). For a
pair `(X, Δ)` and an effective `ℚ`-Cartier `ℚ`-divisor `Δ'`, if `(X, Δ + Δ')` is klt then so is
`(X, Δ)`. -/
@[mmp "lem_km2b_klt_of_klt_add"]
theorem IsKltPair.of_add (hΔ : IsPairWith sX n K Δ) {Δ' : QDivisor X} (hΔ'e : Δ'.IsEffective)
    (hΔ'q : Δ'.IsQCartier) (h : IsKltPair sX n K (Δ + Δ')) : IsKltPair sX n K Δ := by
  obtain ⟨-, hd, hr⟩ := h
  refine ⟨hΔ, lt_of_lt_of_le hd (Helpers.discrep_add_le hΔ'e hΔ'q), ?_⟩
  rw [roundDown_nonpos_iff] at hr ⊢
  intro P
  have := hr P
  rw [DivisorWithCoeffs.coeff_add] at this
  linarith [hΔ'e P]

/-! ### Dlt pairs -/

/-- **Dlt is preserved by removing an effective divisor** (Kollár–Mori 2.39(1)). For a pair
`(X, Δ)` with `Δ` effective and an effective `ℚ`-Cartier `ℚ`-divisor `Δ'`, if `(X, Δ + Δ')` is
dlt then so is `(X, Δ)`. -/
@[mmp "lem_km2b_dlt_add_effective"]
theorem IsDltPair.of_add (hΔ : IsPairWith sX n K Δ) (hΔe : Δ.IsEffective) {Δ' : QDivisor X}
    (hΔ'e : Δ'.IsEffective) (hΔ'q : Δ'.IsQCartier) (h : IsDltPair sX n K (Δ + Δ')) :
    IsDltPair sX n K Δ := by
  obtain ⟨-, hc, U, hUs, hsnc, hdisc⟩ := h
  refine ⟨hΔ, fun P => ⟨hΔe P, ?_⟩, U, hUs, ?_, ?_⟩
  · have := (hc P).2
    rw [DivisorWithCoeffs.coeff_add] at this
    linarith [hΔ'e P]
  · refine hsnc.of_support_subset fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW ⊢
    change Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) ≠ 0 at hW
    change (Δ + Δ').coeff (OpenWeilRestriction.primeDivisorMap U.ι W) ≠ 0
    have h1 := hΔe (OpenWeilRestriction.primeDivisorMap U.ι W)
    have h2 := hΔ'e (OpenWeilRestriction.primeDivisorMap U.ι W)
    rw [DivisorWithCoeffs.coeff_add]
    have : 0 < Δ.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) := lt_of_le_of_ne h1 (Ne.symm hW)
    linarith
  · intro D a hcen ha
    obtain ⟨a', hle, ha'⟩ := Helpers.exists_isDiscrepancy_add_le hΔ'e hΔ'q ha
    exact lt_of_lt_of_le (hdisc D a' hcen ha') hle

/-! ### Log resolutions -/

/-! ### Perturbations of dlt pairs -/

section Perturbation

variable [CompactSpace X]

end Perturbation

end MMP.Threefold.Mori
