module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.OpenRestriction

/-!
# Singularities of pairs

Let `(X, Δ)` be a pair: a normal variety `X` of dimension `n` over a field `k` with canonical
divisor `K_X`, and a `ℚ`-divisor `Δ` with `K_X + Δ` `ℚ`-Cartier. The discrepancies
`a(E, X, Δ)` of the divisors `E` over `X` measure the singularities of the pair. With
`discrep(X, Δ)` the infimum over the exceptional divisors, the pair is *terminal* if
`discrep(X, Δ) > 0`, *canonical* if `discrep(X, Δ) ≥ 0`, *klt* if
`discrep(X, Δ) > -1` and `⌊Δ⌋ ≤ 0`, *plt* if `discrep(X, Δ) > -1` and *lc*
if `discrep(X, Δ) ≥ -1`. It is *dlt* if the coefficients of `Δ` lie in `[0, 1]` and there is a
closed `Z ⊆ X` with `X \ Z` smooth, `Δ|_{X \ Z}` snc, and `a(E, X, Δ) > -1` whenever
`center_X E ⊆ Z`. The *total discrepancy* `totaldiscrep(X, Δ)` is the infimum over the
exceptional divisors and the prime divisors of `X`, and `discrep(center ⊆ Z, X, Δ)`,
`totaldiscrep(center ⊆ Z, X, Δ)` restrict both infima to the divisors with center in a closed
subset `Z`.

A property `𝒫` of pairs holds *near* `W ⊆ X` if it holds for `(U, Δ|_U)` on an open `U ⊇ W`, and
*at* `x` if it holds near `{x}`. On a reduced divisor `S` with pairwise disjoint normal components
`Sⱼ`, a pair `(S, Θ)` is the family of pairs `(Sⱼ, Θ|_{Sⱼ})`; it is `𝒫` when every
`(Sⱼ, Θ|_{Sⱼ})` is, and its discrepancies are the minima over `j`.

For a birational morphism `f : Y ⟶ X` from a normal variety, the negative and positive parts of
the discrepancy are `A_f = ∑_E max {-a(E, X, Δ), 0} E` and `B_f = ∑_E max {a(E, X, Δ), 0} E`, so
that `K_Y ≡ f^*(K_X + Δ) - A_f + B_f`. A valuation of `k(X)` is *algebraic* if it is the valuation
of a divisor over `X`. Finally, a rational top form `σ ∈ Ω^n_{k(X)}` has a divisor `div(σ)`, and
`ω_X(D)` is the sheaf of rational top forms with `div(σ) + D ≥ 0`.

## Main definitions

* `MMP.Mori.DivisorWithCoeffs.restrictOpen`: the restriction `D|_U` to an open subscheme.
* `MMP.Mori.totalDiscrep`, `MMP.Mori.discrepCenterIn`, `MMP.Mori.totalDiscrepCenterIn`:
  `totaldiscrep(X, Δ)`, `discrep(center ⊆ Z, X, Δ)` and `totaldiscrep(center ⊆ Z, X, Δ)`.
* `MMP.Mori.IsTerminalPair`, `MMP.Mori.IsCanonicalPair`, `MMP.Mori.IsKltPair`,
  `MMP.Mori.IsPltPair`, `MMP.Mori.IsLcPair`, `MMP.Mori.IsDltPair`: terminal, canonical, klt, plt,
  lc and dlt pairs.
* `MMP.Mori.PairProperty`, `MMP.Mori.IsNear`, `MMP.Mori.IsAt`: properties of pairs near a subset
  and at a point.
* `MMP.Mori.PairOnNormalDivisor`, with `Satisfies`, `DivisorOver`, `IsDiscrepancy`, `discrep`,
  `totalDiscrep` and `totalDiscrepCenterIn`: pairs on a divisor with disjoint normal components.
* `MMP.Mori.IsDiscrepancyNegativePart`, `MMP.Mori.IsDiscrepancyPositivePart`: `A_f` and `B_f`.
* `MMP.Mori.IsAlgebraicValuation`: algebraic valuations.
* `MMP.Mori.RationalTopForms`, `MMP.Mori.topFormDivisor`: rational top forms and their divisors.
* `MMP.Mori.twistedCanonicalSheaf`, `MMP.Mori.omega`: the sheaves `ω_X(D)` and `ω_X`.

## Main results

* `MMP.Mori.totalDiscrep_le_discrep`, `MMP.Mori.totalDiscrep_le_neg_coeff`:
  `totaldiscrep(X, Δ) ≤ discrep(X, Δ)` and `totaldiscrep(X, Δ) ≤ -coeff_P(Δ)`.
* `MMP.Mori.discrepCenterIn_univ`, `MMP.Mori.totalDiscrepCenterIn_univ`: for `Z = X` the
  infima over `Z` are `discrep` and `totaldiscrep`.
* `MMP.Mori.IsTerminalPair.isCanonicalPair`, `MMP.Mori.IsCanonicalPair.isPltPair`,
  `MMP.Mori.IsPltPair.isLcPair`, `MMP.Mori.IsKltPair.isPltPair`: terminal ⇒ canonical ⇒ plt ⇒ lc,
  and klt ⇒ plt.
* `MMP.Mori.roundDown_nonpos_iff`: `⌊Δ⌋ ≤ 0` exactly when every coefficient of `Δ` is `< 1`.
* `MMP.Mori.IsCrepantBoundary.isDiscrepancyNegativePart`,
  `MMP.Mori.IsCrepantBoundary.isDiscrepancyPositivePart`, `MMP.Mori.IsDiscrepancyNegativePart.eq`,
  `MMP.Mori.IsDiscrepancyNegativePart.sub_eq`: `A_f` and `B_f` exist when the crepant boundary
  `Δ_Y` does, are unique over a perfect field, and `A_f - B_f = Δ_Y`.

## Implementation notes

As for `MMP.Mori.IsDiscrepancy` and `MMP.Mori.discrep`, the canonical divisor `K` and its
dimension `n` are explicit arguments. Each property of pairs asserts `MMP.Mori.IsPairWith`: `X` is
a normal variety, `K` is a canonical divisor of dimension `n`, and `K + Δ` is `ℚ`-Cartier; so it
is false for any `K` that is not a canonical divisor, and for a canonical `K` the pair condition
is the source's.

The infima are taken in `EReal`, as `MMP.Mori.discrep` is. The total discrepancy runs over the
divisors over `X` that are exceptional or of the form `(X, 𝟙_X, P)` for a prime divisor `P`
(`MMP.Mori.DivisorOver.IsExceptionalOrPrimeDivisor`); over a perfect field the discrepancy of
`(X, 𝟙_X, P)` is `-coeff_P(Δ)` (`MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor`).

In the definition of dlt pairs the closed subset `Z` is the complement of the open `U`, and
"`X \ Z` is smooth" is `U ≤ X_sm`. The restriction of a divisor to an open `U` keeps the
coefficients of the prime divisors meeting `U`, a prime divisor of `U` being identified with its
closure in `X` (`AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap`). A property "near `W`"
takes the restricted canonical divisor `K|_U` as the canonical divisor of `U`, and asks `U` to
be nonempty, so that it is integral.

A pair `(S, Θ)` on `S = S₁ + ⋯ + S_s` is recorded by its components, as prime divisors of `X`,
the restrictions `Θ|_{Sⱼ}` and canonical divisors `K_{Sⱼ}`: since the `Sⱼ` are disjoint, `S` is
their disjoint union and a `ℚ`-divisor on `S` is the same as the family of its restrictions. Each
`Sⱼ` is the integral closed subscheme cut out by the prime divisor.

The negative and positive parts of the discrepancy are predicates on a `ℚ`-divisor of `Y`, in the
style of `MMP.Mori.IsCrepantBoundary`; the morphism `f` is only assumed birational (the source
takes it proper). When the crepant boundary `Δ_Y` exists, `A_f` and `B_f` are its parts with
positive and with negative coefficients.

Rational `n`-forms `σ ∈ Ω^n_{k(X)}` are regarded as rational `1`-canonical forms
`σ ∈ (Ω^n_{k(X)})^{⊗1}` (`MMP.Mori.RationalTopForms.toPluriForms`), so `div(σ)` is
`MMP.Mori.divisorOfForm` and `ω_X(D)` is `𝒪_X(K_X + D)`, `MMP.Mori.pluricanonicalSheaf` for
`m = 1`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Remark 2.23,
  Definitions 2.28, 2.34, 2.37 and 5.45, Notation 5.30, the proof of Theorem 5.22
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Normal varieties -/

namespace IsNormalVariety

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}

/-- A normal variety is integral. -/
theorem isIntegral (h : IsNormalVariety k f) : IsIntegral X := h.1.toIsIntegral

/-- A normal variety is a normal scheme. -/
theorem isNormal (h : IsNormalVariety k f) : IsNormal X := h.2

/-- A normal variety is locally Noetherian. -/
theorem isLocallyNoetherian (h : IsNormalVariety k f) : IsLocallyNoetherian X :=
  haveI := h.1.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian f

end IsNormalVariety

/-! ### Restriction of divisors to an open subscheme -/

namespace DivisorWithCoeffs

variable {R : Type*} [Zero R] {X : Scheme.{u}}

/-- The restriction `D|_U` of a divisor `D` on `X` to an open subscheme `U ⊆ X`: the coefficient
of a prime divisor `W` of `U` is the coefficient of `D` at the prime divisor of `X` with the same
generic point, the closure of `W` in `X`. -/
def restrictOpen (U : X.Opens) (D : DivisorWithCoeffs R X) : DivisorWithCoeffs R U.toScheme :=
  Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap U.ι) D
    (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn

/-- The coefficient of `D|_U` at a prime divisor `W` of `U` is the coefficient of `D` at the
closure of `W` in `X`. -/
@[simp]
theorem coeff_restrictOpen (U : X.Opens) (D : DivisorWithCoeffs R X) (W : PrimeDivisor U.toScheme) :
    (D.restrictOpen U).coeff W = D.coeff (OpenWeilRestriction.primeDivisorMap U.ι W) :=
  rfl

end DivisorWithCoeffs

/-- `⌊Δ⌋ ≤ 0`, that is, `0 - ⌊Δ⌋` is effective, exactly when every coefficient of the
divisor `Δ` with coefficients in a floor ring is `< 1`. -/
theorem roundDown_nonpos_iff {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] {X : Scheme.{u}} {Δ : DivisorWithCoeffs R X} :
    Δ.roundDown ≤ 0 ↔ ∀ P : PrimeDivisor X, Δ.coeff P < 1 := by
  rw [DivisorWithCoeffs.le_iff_isEffective_sub]
  refine forall_congr' fun P => ?_
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundDown]
  change 0 ≤ (0 : ℤ) - _ ↔ _
  rw [sub_nonneg, Int.floor_le_iff]
  norm_num

/-! ### The total discrepancy and discrepancies over a closed subset -/

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace DivisorOver

variable {sX : X ⟶ Spec (.of k)}

/-- A divisor `(Y, f, E)` over `X` is *exceptional or a prime divisor of `X`* if it is exceptional
over `X` or it is a prime divisor `P` of the normal variety `X`, regarded as `(X, 𝟙_X, P)`. -/
def IsExceptionalOrPrimeDivisor (D : DivisorOver k sX) : Prop :=
  D.IsExceptional ∨ ∃ (hX : IsNormalVariety k sX) (P : PrimeDivisor X), D = ofPrimeDivisor k hX P

/-- An exceptional divisor over `X` is exceptional or a prime divisor of `X`. -/
theorem IsExceptional.isExceptionalOrPrimeDivisor {D : DivisorOver k sX} (h : D.IsExceptional) :
    D.IsExceptionalOrPrimeDivisor :=
  Or.inl h

/-- A prime divisor `P` of `X`, regarded as `(X, 𝟙_X, P)`, is exceptional or a prime divisor
of `X`. -/
theorem isExceptionalOrPrimeDivisor_ofPrimeDivisor (hX : IsNormalVariety k sX)
    (P : PrimeDivisor X) : (ofPrimeDivisor k hX P).IsExceptionalOrPrimeDivisor :=
  Or.inr ⟨hX, P, rfl⟩

end DivisorOver

section Discrep

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- **The total discrepancy** of a pair `(X, Δ)`, for a canonical divisor `K` of dimension `n`:
`totaldiscrep(X, Δ) = inf {a(E, X, Δ)} ∈ ℝ ∪ {±∞}`, the infimum of the discrepancies of all
exceptional divisors `E` over `X` and all prime divisors of `X`, with `inf ∅ = +∞`. -/
@[mmp "def_km2b_totaldiscrep"]
def totalDiscrep (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : EReal :=
  sInf {x : EReal | ∃ (D : DivisorOver k sX) (a : ℚ), D.IsExceptionalOrPrimeDivisor ∧
    IsDiscrepancy sX n K Δ D a ∧ x = ((a : ℝ) : EReal)}

/-- **The discrepancy over a closed subset.** For a pair `(X, Δ)`, a canonical divisor `K` of
dimension `n` and a closed subset `Z ⊆ X`,
`discrep(center ⊆ Z, X, Δ) = inf {a(E, X, Δ) | E exceptional over X, center_X E ⊆ Z}`, with
`inf ∅ = +∞`. -/
@[mmp "def_km5b_discrep_center_in"]
def discrepCenterIn (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (Z : Set X) : EReal :=
  sInf {x : EReal | ∃ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional ∧
    (D.center : Set X) ⊆ Z ∧ IsDiscrepancy sX n K Δ D a ∧ x = ((a : ℝ) : EReal)}

/-- **The total discrepancy over a closed subset.** For a pair `(X, Δ)`, a canonical divisor `K`
of dimension `n` and a closed subset `Z ⊆ X`, `totaldiscrep(center ⊆ Z, X, Δ)` is the infimum
of the discrepancies `a(E, X, Δ)` of the exceptional divisors over `X` and the prime divisors of
`X` whose center lies in `Z`, with `inf ∅ = +∞`. -/
@[mmp "def_km5b_totaldiscrep_center_in"]
def totalDiscrepCenterIn (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (Z : Set X) : EReal :=
  sInf {x : EReal | ∃ (D : DivisorOver k sX) (a : ℚ), D.IsExceptionalOrPrimeDivisor ∧
    (D.center : Set X) ⊆ Z ∧ IsDiscrepancy sX n K Δ D a ∧ x = ((a : ℝ) : EReal)}

variable {sX} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- `b ≤ totaldiscrep(X, Δ)` exactly when `b ≤ a(E, X, Δ)` for every divisor `E` over `X` that
is exceptional or a prime divisor of `X`. -/
theorem le_totalDiscrep_iff {b : EReal} :
    b ≤ totalDiscrep sX n K Δ ↔ ∀ (D : DivisorOver k sX) (a : ℚ),
      D.IsExceptionalOrPrimeDivisor → IsDiscrepancy sX n K Δ D a → b ≤ ((a : ℝ) : EReal) := by
  refine le_sInf_iff.trans ⟨fun h D a hD ha => h _ ⟨D, a, hD, ha, rfl⟩, ?_⟩
  rintro h _ ⟨D, a, hD, ha, rfl⟩
  exact h D a hD ha

/-- The total discrepancy is at most the discrepancy of every divisor over `X` that is
exceptional or a prime divisor of `X`. -/
theorem totalDiscrep_le {D : DivisorOver k sX} {a : ℚ} (hD : D.IsExceptionalOrPrimeDivisor)
    (ha : IsDiscrepancy sX n K Δ D a) : totalDiscrep sX n K Δ ≤ ((a : ℝ) : EReal) :=
  sInf_le ⟨D, a, hD, ha, rfl⟩

/-- The total discrepancy is at most the discrepancy. -/
theorem totalDiscrep_le_discrep : totalDiscrep sX n K Δ ≤ discrep sX n K Δ :=
  le_discrep_iff.mpr fun _ _ hD ha => totalDiscrep_le hD.isExceptionalOrPrimeDivisor ha

/-- Over a perfect field, the total discrepancy is at most `-coeff_P(Δ)` for every prime divisor
`P` of `X` whose discrepancy exists. -/
theorem totalDiscrep_le_neg_coeff [PerfectField k] (hX : IsNormalVariety k sX)
    {P : PrimeDivisor X} (h : ∃ a, IsDiscrepancy sX n K Δ (DivisorOver.ofPrimeDivisor k hX P) a) :
    totalDiscrep sX n K Δ ≤ (((-Δ.coeff P : ℚ) : ℝ) : EReal) := by
  obtain ⟨a, ha⟩ := h
  rw [← ha.eq_neg_coeff_of_ofPrimeDivisor hX]
  exact totalDiscrep_le (DivisorOver.isExceptionalOrPrimeDivisor_ofPrimeDivisor hX P) ha

/-- `b ≤ discrep(center ⊆ Z, X, Δ)` exactly when `b ≤ a(E, X, Δ)` for every exceptional
divisor `E` over `X` with `center_X E ⊆ Z`. -/
theorem le_discrepCenterIn_iff {Z : Set X} {b : EReal} :
    b ≤ discrepCenterIn sX n K Δ Z ↔ ∀ (D : DivisorOver k sX) (a : ℚ), D.IsExceptional →
      (D.center : Set X) ⊆ Z → IsDiscrepancy sX n K Δ D a → b ≤ ((a : ℝ) : EReal) := by
  refine le_sInf_iff.trans ⟨fun h D a hD hZ ha => h _ ⟨D, a, hD, hZ, ha, rfl⟩, ?_⟩
  rintro h _ ⟨D, a, hD, hZ, ha, rfl⟩
  exact h D a hD hZ ha

/-- The discrepancy over `Z` is at most the discrepancy of every exceptional divisor over `X`
with center in `Z`. -/
theorem discrepCenterIn_le {Z : Set X} {D : DivisorOver k sX} {a : ℚ} (hD : D.IsExceptional)
    (hZ : (D.center : Set X) ⊆ Z) (ha : IsDiscrepancy sX n K Δ D a) :
    discrepCenterIn sX n K Δ Z ≤ ((a : ℝ) : EReal) :=
  sInf_le ⟨D, a, hD, hZ, ha, rfl⟩

/-- `b ≤ totaldiscrep(center ⊆ Z, X, Δ)` exactly when `b ≤ a(E, X, Δ)` for every divisor `E`
over `X` that is exceptional or a prime divisor of `X` and has `center_X E ⊆ Z`. -/
theorem le_totalDiscrepCenterIn_iff {Z : Set X} {b : EReal} :
    b ≤ totalDiscrepCenterIn sX n K Δ Z ↔ ∀ (D : DivisorOver k sX) (a : ℚ),
      D.IsExceptionalOrPrimeDivisor → (D.center : Set X) ⊆ Z → IsDiscrepancy sX n K Δ D a →
        b ≤ ((a : ℝ) : EReal) := by
  refine le_sInf_iff.trans ⟨fun h D a hD hZ ha => h _ ⟨D, a, hD, hZ, ha, rfl⟩, ?_⟩
  rintro h _ ⟨D, a, hD, hZ, ha, rfl⟩
  exact h D a hD hZ ha

/-- The total discrepancy over `Z` is at most the discrepancy of every divisor over `X` that is
exceptional or a prime divisor of `X` and has center in `Z`. -/
theorem totalDiscrepCenterIn_le {Z : Set X} {D : DivisorOver k sX} {a : ℚ}
    (hD : D.IsExceptionalOrPrimeDivisor) (hZ : (D.center : Set X) ⊆ Z)
    (ha : IsDiscrepancy sX n K Δ D a) : totalDiscrepCenterIn sX n K Δ Z ≤ ((a : ℝ) : EReal) :=
  sInf_le ⟨D, a, hD, hZ, ha, rfl⟩

/-- Over the whole of `X`, the discrepancy over a closed subset is `discrep(X, Δ)`. -/
@[simp]
theorem discrepCenterIn_univ : discrepCenterIn sX n K Δ Set.univ = discrep sX n K Δ :=
  le_antisymm (le_discrep_iff.mpr fun _ _ hD ha => discrepCenterIn_le hD (Set.subset_univ _) ha)
    (le_discrepCenterIn_iff.mpr fun _ _ hD _ ha => discrep_le hD ha)

/-- Over the whole of `X`, the total discrepancy over a closed subset is `totaldiscrep(X, Δ)`. -/
@[simp]
theorem totalDiscrepCenterIn_univ :
    totalDiscrepCenterIn sX n K Δ Set.univ = totalDiscrep sX n K Δ :=
  le_antisymm
    (le_totalDiscrep_iff.mpr fun _ _ hD ha => totalDiscrepCenterIn_le hD (Set.subset_univ _) ha)
    (le_totalDiscrepCenterIn_iff.mpr fun _ _ hD _ ha => totalDiscrep_le hD ha)

/-- The total discrepancy over `Z` is at most the discrepancy over `Z`. -/
theorem totalDiscrepCenterIn_le_discrepCenterIn {Z : Set X} :
    totalDiscrepCenterIn sX n K Δ Z ≤ discrepCenterIn sX n K Δ Z :=
  le_discrepCenterIn_iff.mpr fun _ _ hD hZ ha =>
    totalDiscrepCenterIn_le hD.isExceptionalOrPrimeDivisor hZ ha

/-- The discrepancy over `Z` decreases as `Z` grows. -/
theorem discrepCenterIn_anti : Antitone (discrepCenterIn sX n K Δ) := fun _ _ h =>
  le_discrepCenterIn_iff.mpr fun _ _ hD hZ ha => discrepCenterIn_le hD (hZ.trans h) ha

/-- The total discrepancy over `Z` decreases as `Z` grows. -/
theorem totalDiscrepCenterIn_anti : Antitone (totalDiscrepCenterIn sX n K Δ) := fun _ _ h =>
  le_totalDiscrepCenterIn_iff.mpr fun _ _ hD hZ ha => totalDiscrepCenterIn_le hD (hZ.trans h) ha

end Discrep

/-! ### Terminal, canonical, plt, lc and dlt pairs -/

section Singularities

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- `(X, Δ)` is a *pair with canonical divisor `K`* of dimension `n`: `X` is a normal variety,
`K` is a canonical divisor of `X` of dimension `n`, and `K + Δ` is `ℚ`-Cartier. -/
def IsPairWith (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧ (Divisor.toQDivisor K + Δ).IsQCartier

omit [IsIntegral X] in
variable {sX} in
/-- A pair with canonical divisor `K` is a pair. -/
theorem IsPairWith.isPair {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsPairWith sX n K Δ) :
    IsPair sX Δ :=
  ⟨h.1, n, K, h.2.1, h.2.2⟩

/-- A pair `(X, Δ)`, with canonical divisor `K` of dimension `n`, is *terminal* if
`discrep(X, Δ) > 0`. -/
@[mmp "def_km2b_terminal"]
def IsTerminalPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ 0 < discrep sX n K Δ

/-- A pair `(X, Δ)`, with canonical divisor `K` of dimension `n`, is *canonical* if
`discrep(X, Δ) ≥ 0`. -/
@[mmp "def_km2b_canonical"]
def IsCanonicalPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ 0 ≤ discrep sX n K Δ

/-- A pair `(X, Δ)`, with canonical divisor `K` of dimension `n`, is *plt* (purely log terminal)
if `discrep(X, Δ) > -1`. -/
@[mmp "def_km2b_plt"]
def IsPltPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ -1 < discrep sX n K Δ

/-- A pair `(X, Δ)`, with canonical divisor `K` of dimension `n`, is *klt* (Kawamata log
terminal) if `discrep(X, Δ) > -1` and `⌊Δ⌋ ≤ 0`, that is, `-⌊Δ⌋` is effective, or equivalently
every coefficient of `Δ` is `< 1` (`MMP.Mori.roundDown_nonpos_iff`). -/
@[mmp "def_km2b_klt"]
def IsKltPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ -1 < discrep sX n K Δ ∧ Δ.roundDown ≤ 0

/-- A pair `(X, Δ)`, with canonical divisor `K` of dimension `n`, is *lc* (log canonical) if
`discrep(X, Δ) ≥ -1`. -/
@[mmp "def_km2b_lc"]
def IsLcPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ -1 ≤ discrep sX n K Δ

/-- A pair `(X, Δ = ∑ aᵢ Dᵢ)`, with canonical divisor `K` of dimension `n` and `0 ≤ aᵢ ≤ 1`, is
*dlt* (divisorial log terminal) if there is a closed subset `Z ⊆ X`, the complement of an open
`U`, such that `U = X \ Z` lies in the smooth locus of `X`, `Δ|_U` is an snc divisor, and
`a(E, X, Δ) > -1` for every divisor `(Y, f, E)` over `X` with `center_X E ⊆ Z`. -/
@[mmp "def_km2b_dlt"]
def IsDltPair (n : ℕ) (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsPairWith sX n K Δ ∧ (∀ P : PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1) ∧
    ∃ U : X.Opens, U ≤ smoothLocus sX ∧ (Δ.restrictOpen U).IsSNC (U.ι ≫ sX) ∧
      ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
        IsDiscrepancy sX n K Δ D a → -1 < a

variable {sX} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- A terminal pair is canonical. -/
theorem IsTerminalPair.isCanonicalPair (h : IsTerminalPair sX n K Δ) :
    IsCanonicalPair sX n K Δ :=
  ⟨h.1, h.2.le⟩

/-- A canonical pair is plt. -/
theorem IsCanonicalPair.isPltPair (h : IsCanonicalPair sX n K Δ) : IsPltPair sX n K Δ :=
  ⟨h.1, lt_of_lt_of_le (by norm_num) h.2⟩

/-- A klt pair is plt. -/
theorem IsKltPair.isPltPair (h : IsKltPair sX n K Δ) : IsPltPair sX n K Δ :=
  ⟨h.1, h.2.1⟩

/-- A klt pair is a pair. -/
theorem IsKltPair.isPair (h : IsKltPair sX n K Δ) : IsPair sX Δ := h.1.isPair

/-- A plt pair is lc. -/
theorem IsPltPair.isLcPair (h : IsPltPair sX n K Δ) : IsLcPair sX n K Δ :=
  ⟨h.1, h.2.le⟩

/-- A dlt pair is a pair with canonical divisor `K`. -/
theorem IsDltPair.isPairWith (h : IsDltPair sX n K Δ) : IsPairWith sX n K Δ :=
  h.1

/-- A terminal pair is a pair. -/
theorem IsTerminalPair.isPair (h : IsTerminalPair sX n K Δ) : IsPair sX Δ := h.1.isPair

/-- A canonical pair is a pair. -/
theorem IsCanonicalPair.isPair (h : IsCanonicalPair sX n K Δ) : IsPair sX Δ := h.1.isPair

/-- A plt pair is a pair. -/
theorem IsPltPair.isPair (h : IsPltPair sX n K Δ) : IsPair sX Δ := h.1.isPair

/-- An lc pair is a pair. -/
theorem IsLcPair.isPair (h : IsLcPair sX n K Δ) : IsPair sX Δ := h.1.isPair

/-- A dlt pair is a pair. -/
theorem IsDltPair.isPair (h : IsDltPair sX n K Δ) : IsPair sX Δ := h.1.isPair

end Singularities

/-! ### Properties of pairs near a subset -/

variable (k) in
/-- A property of pairs `(U, Δ_U)` with canonical divisor `K_U` of dimension `n`, such as being
terminal, canonical, klt, plt, lc or dlt: a predicate on a normal integral scheme `U` with
structure morphism `U ⟶ Spec k`, a dimension `n`, a divisor `K_U` and a `ℚ`-divisor `Δ_U`. -/
abbrev PairProperty : Type (u + 1) :=
  ∀ {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U], (U ⟶ Spec (.of k)) →
    ℕ → Divisor U → QDivisor U → Prop

section Near

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- **`𝒫` near `W`.** For a property `𝒫` of pairs (one of terminal, canonical, klt, plt, lc,
dlt), a pair `(X, Δ)` with canonical divisor `K` of dimension `n` is *`𝒫` near* a subset
`W ⊆ X` if there is a nonempty open subset `U ⊇ W` of `X` such that `(U, Δ|_U)`, with canonical
divisor `K|_U`, is `𝒫`. -/
@[mmp "not_km5b_near"]
def IsNear (P : PairProperty k) (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (W : Set X) : Prop :=
  ∃ U : X.Opens, W ⊆ U ∧ ∃ h : Nonempty U,
    haveI := h
    P (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U)

/-- **`𝒫` at `x`.** A pair `(X, Δ)` is *`𝒫` at* a point `x` if it is `𝒫` near `{x}`. -/
@[mmp "not_km5b_near"]
def IsAt (P : PairProperty k) (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (x : X) : Prop :=
  IsNear sX P n K Δ {x}

variable {sX}

/-- A pair that is `𝒫` near `W'` is `𝒫` near every subset `W ⊆ W'`. -/
theorem IsNear.mono {P : PairProperty k} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {W W' : Set X}
    (h : IsNear sX P n K Δ W') (hW : W ⊆ W') : IsNear sX P n K Δ W :=
  let ⟨U, hU, hne, hP⟩ := h
  ⟨U, hW.trans hU, hne, hP⟩

/-- A pair is `𝒫` at `x` exactly when it is `𝒫` near `{x}`. -/
theorem isAt_iff_isNear {P : PairProperty k} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {x : X} :
    IsAt sX P n K Δ x ↔ IsNear sX P n K Δ {x} :=
  Iff.rfl

/-- A pair that is `𝒫` near `W` is `𝒫` at every point of `W`. -/
theorem IsNear.isAt {P : PairProperty k} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {W : Set X}
    (h : IsNear sX P n K Δ W) {x : X} (hx : x ∈ W) : IsAt sX P n K Δ x :=
  h.mono (Set.singleton_subset_iff.mpr hx)

end Near

/-! ### Pairs on a divisor with disjoint normal components -/

section NormalDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- A *pair `(S, Θ)` on a reduced divisor `S = S₁ + ⋯ + S_s`* of the normal variety `X` whose
components `Sⱼ` are pairwise disjoint normal varieties: the components, the restrictions
`Θ|_{Sⱼ}` of the `ℚ`-divisor `Θ` on `S` and canonical divisors `K_{Sⱼ}` of dimension `dim`, with
`K_{Sⱼ} + Θ|_{Sⱼ}` `ℚ`-Cartier for every `j`. Each component `Sⱼ` is the integral closed
subscheme of `X` cut out by the prime divisor, with structure morphism `Sⱼ ⟶ X ⟶ Spec k`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
structure PairOnNormalDivisor where
  /-- The components `S₁, …, S_s` of `S`. -/
  components : Finset (PrimeDivisor X)
  /-- The components are pairwise disjoint. -/
  pairwise_disjoint : (components : Set (PrimeDivisor X)).Pairwise
    fun E E' => Disjoint E.support E'.support
  /-- Each component is a normal variety. -/
  isNormalVariety : ∀ E : components, IsNormalVariety k (E.1.idealSheaf.subschemeι ≫ sX)
  /-- The common dimension of the canonical divisors of the components. -/
  dim : ℕ
  /-- A canonical divisor `K_{Sⱼ}` of each component. -/
  K : ∀ E : components, Divisor E.1.idealSheaf.subscheme
  /-- The restriction `Θ|_{Sⱼ}` of `Θ` to each component. -/
  Θ : ∀ E : components, QDivisor E.1.idealSheaf.subscheme
  /-- `K_{Sⱼ}` is a canonical divisor of `Sⱼ` of dimension `dim`. -/
  isCanonicalDivisor : ∀ E : components,
    haveI := (isNormalVariety E).isLocallyNoetherian
    haveI := (isNormalVariety E).isNormal
    (K E).IsCanonicalDivisor (E.1.idealSheaf.subschemeι ≫ sX) dim
  /-- `K_{Sⱼ} + Θ|_{Sⱼ}` is `ℚ`-Cartier. -/
  isQCartier : ∀ E : components,
    haveI := (isNormalVariety E).isLocallyNoetherian
    haveI := (isNormalVariety E).isNormal
    (Divisor.toQDivisor (K E) + Θ E).IsQCartier

namespace PairOnNormalDivisor

variable {sX} (T : PairOnNormalDivisor sX)

/-- `(S, Θ)` is `𝒫`, for `𝒫` one of terminal, canonical, klt, plt, lc, dlt, if every
`(Sⱼ, Θ|_{Sⱼ})` is `𝒫`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
def Satisfies (P : PairProperty k) : Prop :=
  ∀ E : T.components,
    haveI := (T.isNormalVariety E).isIntegral
    haveI := (T.isNormalVariety E).isLocallyNoetherian
    haveI := (T.isNormalVariety E).isNormal
    P (E.1.idealSheaf.subschemeι ≫ sX) T.dim (T.K E) (T.Θ E)

/-- A *divisor over `S`* is a divisor over some component `Sⱼ`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
abbrev DivisorOver : Type (u + 1) :=
  Σ E : T.components, MMP.Mori.DivisorOver k (E.1.idealSheaf.subschemeι ≫ sX)

/-- The discrepancy `a(F, S, Θ) := a(F, Sⱼ, Θ|_{Sⱼ})` of a divisor `F` over a component `Sⱼ`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
def IsDiscrepancy (F : T.DivisorOver) (a : ℚ) : Prop :=
  haveI := (T.isNormalVariety F.1).isIntegral
  haveI := (T.isNormalVariety F.1).isLocallyNoetherian
  haveI := (T.isNormalVariety F.1).isNormal
  MMP.Mori.IsDiscrepancy (F.1.1.idealSheaf.subschemeι ≫ sX) T.dim (T.K F.1) (T.Θ F.1) F.2 a

/-- `discrep(S, Θ)`: the infimum over `j` of `discrep(Sⱼ, Θ|_{Sⱼ})`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
def discrep : EReal :=
  ⨅ E : T.components,
    haveI := (T.isNormalVariety E).isIntegral
    haveI := (T.isNormalVariety E).isLocallyNoetherian
    haveI := (T.isNormalVariety E).isNormal
    MMP.Mori.discrep (E.1.idealSheaf.subschemeι ≫ sX) T.dim (T.K E) (T.Θ E)

/-- `totaldiscrep(S, Θ)`: the infimum over `j` of `totaldiscrep(Sⱼ, Θ|_{Sⱼ})`. -/
@[mmp "not_km5b_pairs_on_normal_divisors"]
def totalDiscrep : EReal :=
  ⨅ E : T.components,
    haveI := (T.isNormalVariety E).isIntegral
    haveI := (T.isNormalVariety E).isLocallyNoetherian
    haveI := (T.isNormalVariety E).isNormal
    MMP.Mori.totalDiscrep (E.1.idealSheaf.subschemeι ≫ sX) T.dim (T.K E) (T.Θ E)

/-- `totaldiscrep(center ⊆ Z, S, Θ)` for a closed subset `Z ⊆ X`: the infimum over `j` of
`totaldiscrep(center ⊆ Z ∩ Sⱼ, Sⱼ, Θ|_{Sⱼ})`. -/
@[mmp "def_km5b_totaldiscrep_center_in"]
def totalDiscrepCenterIn (Z : Set X) : EReal :=
  ⨅ E : T.components,
    haveI := (T.isNormalVariety E).isIntegral
    haveI := (T.isNormalVariety E).isLocallyNoetherian
    haveI := (T.isNormalVariety E).isNormal
    MMP.Mori.totalDiscrepCenterIn (E.1.idealSheaf.subschemeι ≫ sX) T.dim (T.K E) (T.Θ E)
      (E.1.idealSheaf.subschemeι ⁻¹' Z)

end PairOnNormalDivisor

end NormalDivisor

/-! ### The negative and positive parts of the discrepancy -/

section Parts

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- **The negative part of the discrepancy.** For a pair `(X, Δ)` with canonical divisor `K` of
dimension `n` and a birational morphism `f : Y ⟶ X` from a normal variety, a `ℚ`-divisor `A` on
`Y` is `A_f = ∑_E max {-a(E, X, Δ), 0} E`, the sum over the prime divisors `E` of `Y`: every `E`
has a discrepancy `a(E, X, Δ)` and `coeff_E(A) = max {-a(E, X, Δ), 0}`. -/
@[mmp "def_km5d_discrepancy_negative_part"]
def IsDiscrepancyNegativePart (n : ℕ) (K : Divisor X) (Δ : QDivisor X) {Y : Scheme.{u}}
    (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (A : QDivisor Y) : Prop :=
  IsPairWith sX n K Δ ∧ ∀ F : PrimeDivisor Y, ∃ a : ℚ,
    IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a ∧ A.coeff F = max (-a) 0

/-- **The positive part of the discrepancy.** In the situation of
`MMP.Mori.IsDiscrepancyNegativePart`, a `ℚ`-divisor `B` on `Y` is
`B_f = ∑_E max {a(E, X, Δ), 0} E`. -/
@[mmp "def_km5d_discrepancy_positive_part"]
def IsDiscrepancyPositivePart (n : ℕ) (K : Divisor X) (Δ : QDivisor X) {Y : Scheme.{u}}
    (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (B : QDivisor Y) : Prop :=
  IsPairWith sX n K Δ ∧ ∀ F : PrimeDivisor Y, ∃ a : ℚ,
    IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, F⟩ a ∧ B.coeff F = max a 0

variable {sX} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
  {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}

/-- The negative part of the discrepancy is the part of the crepant boundary `Δ_Y` with positive
coefficients: `A_f = ∑_E max {coeff_E(Δ_Y), 0} E`. -/
theorem IsCrepantBoundary.isDiscrepancyNegativePart {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K Δ f hY hf ΔY) (hP : IsPairWith sX n K Δ) :
    IsDiscrepancyNegativePart sX n K Δ f hY hf (ΔY.mapCoeffs (max · 0) (by simp)) :=
  ⟨hP, fun F => ⟨-ΔY.coeff F, h F, by simp⟩⟩

/-- The positive part of the discrepancy is minus the part of the crepant boundary `Δ_Y` with
negative coefficients: `B_f = ∑_E max {-coeff_E(Δ_Y), 0} E`. -/
theorem IsCrepantBoundary.isDiscrepancyPositivePart {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K Δ f hY hf ΔY) (hP : IsPairWith sX n K Δ) :
    IsDiscrepancyPositivePart sX n K Δ f hY hf ((-ΔY).mapCoeffs (max · 0) (by simp)) :=
  ⟨hP, fun F => ⟨-ΔY.coeff F, h F, by simp [DivisorWithCoeffs.coeff_neg]⟩⟩

/-- Over a perfect field the negative part of the discrepancy is unique. -/
theorem IsDiscrepancyNegativePart.eq [PerfectField k] {A A' : QDivisor Y}
    (h : IsDiscrepancyNegativePart sX n K Δ f hY hf A)
    (h' : IsDiscrepancyNegativePart sX n K Δ f hY hf A') : A = A' := by
  refine DivisorWithCoeffs.ext' fun F => ?_
  obtain ⟨a, ha, hA⟩ := h.2 F
  obtain ⟨a', ha', hA'⟩ := h'.2 F
  rw [hA, hA', ha.eq ha']

/-- Over a perfect field the positive part of the discrepancy is unique. -/
theorem IsDiscrepancyPositivePart.eq [PerfectField k] {B B' : QDivisor Y}
    (h : IsDiscrepancyPositivePart sX n K Δ f hY hf B)
    (h' : IsDiscrepancyPositivePart sX n K Δ f hY hf B') : B = B' := by
  refine DivisorWithCoeffs.ext' fun F => ?_
  obtain ⟨a, ha, hB⟩ := h.2 F
  obtain ⟨a', ha', hB'⟩ := h'.2 F
  rw [hB, hB', ha.eq ha']

/-- Over a perfect field, `A_f - B_f` is the crepant boundary: `K_Y ≡ f^*(K_X + Δ) - A_f + B_f`. -/
theorem IsDiscrepancyNegativePart.sub_eq [PerfectField k] {A B ΔY : QDivisor Y}
    (hA : IsDiscrepancyNegativePart sX n K Δ f hY hf A)
    (hB : IsDiscrepancyPositivePart sX n K Δ f hY hf B)
    (h : IsCrepantBoundary sX n K Δ f hY hf ΔY) : A - B = ΔY := by
  rw [hA.eq (h.isDiscrepancyNegativePart hA.1), hB.eq (h.isDiscrepancyPositivePart hA.1)]
  refine DivisorWithCoeffs.ext' fun F => ?_
  simp [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg]

end Parts

/-! ### Algebraic valuations -/

variable (k) in
/-- A valuation `v` of the function field `k(X)` of a variety `X` is *algebraic* (over `X`) if
`v = v(E, Y)` for a birational morphism `f : Y ⟶ X` from a normal variety `Y` and a prime divisor
`E ⊆ Y`, that is, if it is the valuation of a divisor over `X`. -/
@[mmp "def_km2b_algebraic_valuation"]
def IsAlgebraicValuation [IsIntegral X] (sX : X ⟶ Spec (.of k))
    (v : Valuation X.functionField ℤᵐ⁰) : Prop :=
  IsVariety k sX ∧ ∃ D : DivisorOver k sX, D.valuation = v

/-- The valuation of a divisor over a variety `X` is algebraic. -/
theorem isAlgebraicValuation_valuation [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : IsVariety k sX) (D : DivisorOver k sX) : IsAlgebraicValuation k sX D.valuation :=
  ⟨hX, D, rfl⟩

/-! ### The divisor of a rational top form and the sheaves `ω_X(D)` -/

section TopForms

variable [IsIntegral X] (sX : X ⟶ Spec (.of k))

/-- The *rational `n`-forms* `Ω^n_{k(X)}` of an integral scheme `X` over `k`, the `k(X)`-vector
space `⋀ⁿ Ω_{k(X)/k}` (one-dimensional when `n = dim X` and `k` is perfect). -/
def RationalTopForms (n : ℕ) : Type u :=
  letI := functionFieldAlgebra sX
  ⋀[X.functionField]^n Ω[X.functionField⁄k]

/-- The rational `n`-forms form an additive commutative group. -/
instance (n : ℕ) : AddCommGroup (RationalTopForms sX n) := by
  unfold RationalTopForms; infer_instance

/-- The rational `n`-forms form a `k(X)`-vector space. -/
instance (n : ℕ) : Module X.functionField (RationalTopForms sX n) := by
  unfold RationalTopForms; infer_instance

/-- A rational `n`-form `σ`, regarded as a rational `1`-canonical form `σ ∈ (Ω^n_{k(X)})^{⊗1}`. -/
def RationalTopForms.toPluriForms {n : ℕ} (σ : RationalTopForms sX n) :
    RationalPluriForms sX n 1 :=
  letI := functionFieldAlgebra sX
  (PiTensorProduct.tprod X.functionField
      fun _ : Fin 1 => (σ : ⋀[X.functionField]^n Ω[X.functionField⁄k]) :
    ⨂[X.functionField]^1 (⋀[X.functionField]^n Ω[X.functionField⁄k]))

variable [IsLocallyNoetherian X]

/-- **The divisor of a rational top form.** For a nonzero rational `n`-form `σ ∈ Ω^n_{k(X)}` on
a normal variety `X` of dimension `n` and a prime divisor `P` of `X`, `ord_P(σ) = v_P(σ / σ_P)`
for a generator `σ_P` of the stalk of `Ω^n_X` at the generic point of `P`, and
`div(σ) = ∑_P ord_P(σ) P`, a finite sum. -/
@[mmp "def_km5b_divisor_of_form"]
def topFormDivisor [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} (σ : RationalTopForms sX n) :
    Divisor X :=
  divisorOfForm (σ.toPluriForms sX)

/-- The coefficient of `div(σ)` at a prime divisor `P` is `ord_P(σ)`. -/
@[simp]
theorem coeff_topFormDivisor [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    (σ : RationalTopForms sX n) (P : PrimeDivisor X) :
    (topFormDivisor sX σ).coeff P = P.ordForm (σ.toPluriForms sX) :=
  rfl

variable [IsNormal X]

/-- **The sheaf `ω_X(D)`.** For a normal variety `X` of dimension `n` and a divisor `D` on `X`,
`ω_X(D)` is the subsheaf of the constant sheaf `Ω^n_{k(X)} = (Ω^n_{k(X)})^{⊗1}` whose sections
over a nonempty open `U` are `0` and the forms `σ ≠ 0` with `div(σ) + D ≥ 0` on `U`; it is
`𝒪_X(K_X + D)`, `MMP.Mori.pluricanonicalSheaf` for `m = 1`. -/
@[mmp "not_km5b_canonical_sheaf"]
abbrev twistedCanonicalSheaf (n : ℕ) (D : Divisor X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  pluricanonicalSheaf sX n 1 D

/-- The sheaf `ω_X = ω_X(0)`. -/
@[mmp "not_km5b_canonical_sheaf"]
abbrev omega (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  twistedCanonicalSheaf sX n 0

end TopForms

end MMP.Mori
