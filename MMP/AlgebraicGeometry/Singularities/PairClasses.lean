/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Contraction.Defs

/-!
# Discrepancies of pairs and classes of singularities in *Flips and abundance*

The discrepancy `a_ω(E, X, D)` of a divisor over `X` with respect to a `ℚ`-divisor (FA 1.15), the
total discrepancy `discrep(X, D)` (FA 1.15), terminal and canonical pairs (FA 1.16), and log
canonical, log terminal and Kawamata log terminal log varieties (FA 2.10, 2.13.1, 2.13.5).

## Main definitions

* `MMP.Flips.IsQDiscrepancyWith`: `a = a_ω(E, X, D)` for a `ℚ`-divisor `D`.
* `MMP.Flips.discrep`: `discrep(X, D) ∈ ℝ ∪ {±∞}`.
* `MMP.Flips.IsTerminalPair`, `MMP.Flips.IsCanonicalPair`.
* `MMP.Flips.IsLogCanonical`, `MMP.Flips.IsLogTerminal`, `MMP.Flips.IsKawamataLogTerminal`.

## Implementation notes

As in `MMP.Flips.IsDiscrepancy`, a discrepancy is a predicate on its value, and the conditions
"`a(F, D) ≥ -1` for every `F`" quantify over every value `a` satisfying it. A canonical divisor
`K_X` of dimension `n` is an explicit argument, as in `MMP.Mori.Divisor.IsCanonicalDivisor`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 1.15, 1.16,
  2.10, 2.13.1, 2.13.5
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-! ### Discrepancies with respect to a `ℚ`-divisor -/

/-- Let `X` be a normal variety of dimension `n`, `D` a `ℚ`-divisor on `X` (not necessarily
effective) and `ω ≠ 0` a rational `n`-form with `div_X(ω) + D` `ℚ`-Cartier. For a divisor
`(Y, f, E)` over `X`, the rational number `a` is the *discrepancy* `a_ω(E, X, D)` of `E` with
respect to `(X, D)`, computed with `ω`, if it is the coefficient of `E` in the `ℚ`-divisor
`div_Y(f^*ω) - f^*(div_X(ω) + D)` on `Y`: `a = ord_E(f^*ω) - coeff_E(f^*(div_X(ω) + D))`, with the
pull-back `MMP.Mori.QDivisor.IsPullback` of `ℚ`-Cartier divisors. -/
@[mmp "def_fa1a_discrepancy_pair"]
def IsQDiscrepancyWith (n : ℕ) (D : QDivisor X) (ω : RationalPluriForms sX n 1)
    (E : ProperDivisorOver k sX) (a : ℚ) : Prop :=
  IsNormalVariety k sX ∧ topologicalKrullDim X = n ∧ ω ≠ 0 ∧
    (Divisor.toQDivisor (divisorOfForm ω) + D).IsQCartier ∧
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∃ (hB : ∀ Z : irreducibleComponents E.Y,
        E.f (componentGenericPoint E.Y Z) ∉ (Divisor.toQDivisor (divisorOfForm ω) + D).supp)
      (G : QDivisor E.Y),
      (Divisor.toQDivisor (divisorOfForm ω) + D).IsPullback E.f hB G ∧
      a = (E.toDivisorOver.ordPullback ω : ℚ) - G.coeff E.E

/-- The *discrepancy* `discrep(X, D) ∈ ℝ ∪ {±∞}` of a normal variety `X` of dimension `n` and a
`ℚ`-divisor `D` with `K_X + D` `ℚ`-Cartier: the infimum of `a_ω(E, X, D)` over all exceptional
divisors `(Y, f, E)` over `X` and all nonzero rational `n`-forms `ω`, with `inf ∅ = +∞`. -/
@[mmp "def_fa1a_discrep_pair"]
def discrep (n : ℕ) (D : QDivisor X) : EReal :=
  sInf {x : EReal | ∃ (E : ProperDivisorOver k sX) (ω : RationalPluriForms sX n 1) (a : ℚ),
    E.IsExceptional ∧ IsQDiscrepancyWith sX n D ω E a ∧ x = ((a : ℝ) : EReal)}

/-- Let `X` be a normal variety with canonical divisor `K` of dimension `n` and `D` an effective
`ℚ`-divisor with `K_X + D` `ℚ`-Cartier. The pair `(X, D)` is *terminal* if `discrep(X, D) > 0`. -/
@[mmp "def_fa1a_terminal_pair"]
def IsTerminalPair (n : ℕ) (K : Divisor X) (D : QDivisor X) : Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧ D.IsEffective ∧
    (Divisor.toQDivisor K + D).IsQCartier ∧ 0 < discrep sX n D

/-- Let `X` be a normal variety with canonical divisor `K` of dimension `n` and `D` an effective
`ℚ`-divisor with `K_X + D` `ℚ`-Cartier. The pair `(X, D)` is *canonical* if
`discrep(X, D) ≥ 0`. -/
@[mmp "def_fa1a_canonical_pair"]
def IsCanonicalPair (n : ℕ) (K : Divisor X) (D : QDivisor X) : Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧ D.IsEffective ∧
    (Divisor.toQDivisor K + D).IsQCartier ∧ 0 ≤ discrep sX n D

/-! ### Log canonical, log terminal and Kawamata log terminal log varieties -/

/-- Let `D_X` be a boundary on a normal variety `X` with canonical divisor `K` of dimension `n`.
`K_X + D_X` (or `(X, D_X)`) is *log canonical* (lc) if `K_X + D_X` is `ℝ`-Cartier and
`a(F, D_X) ≥ -1` for every divisor `F` of `k(X)` with nonempty center on `X`; equivalently
`a_ℓ(F, D_X) ≥ 0` (`MMP.Flips.isLogCanonical_iff_logDiscrepancy`). -/
@[mmp "def_fa2_lc"]
def IsLogCanonical (n : ℕ) (K : Divisor X) (D : RDivisor X) : Prop :=
  IsLogVariety k sX D ∧ K.IsCanonicalDivisor sX n ∧
    IsCartierCombination (Divisor.toRDivisor K + D) ∧
    ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
      ∀ a : ℝ, IsDiscrepancy sX n K D F a → -1 ≤ a

/-- A log variety is log canonical exactly when every log discrepancy `a_ℓ(F, D_X)` of a divisor
`F` with nonempty center is `≥ 0`. -/
@[mmp "def_fa2_lc"]
theorem isLogCanonical_iff_logDiscrepancy (n : ℕ) (K : Divisor X) (D : RDivisor X) :
    IsLogCanonical sX n K D ↔
      IsLogVariety k sX D ∧ K.IsCanonicalDivisor sX n ∧
        IsCartierCombination (Divisor.toRDivisor K + D) ∧
        ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
          ∀ b : ℝ, IsLogDiscrepancy sX n K D F b → 0 ≤ b := by
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' fun F => imp_congr_right fun _ => ⟨fun h b hb => ?_, fun h a ha => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hb
    linarith [h a ha]
  · linarith [h (1 + a) ⟨a, ha, rfl⟩]

/-- Let `(X, D)` be a log variety with `K_X + D` `ℝ`-Cartier. `(X, D)` is *log terminal* (lt) if
there is a log resolution `f : Y ⟶ X` such that `a_ℓ(E, D) > 0` for every prime divisor `E` of
`Y` exceptional over `X` (the divisor `(Y, f, E)` over `X` being exceptional). -/
@[mmp "def_fa2_lt"]
def IsLogTerminal (n : ℕ) (K : Divisor X) (D : RDivisor X) : Prop :=
  IsLogVariety k sX D ∧ K.IsCanonicalDivisor sX n ∧
    IsCartierCombination (Divisor.toRDivisor K + D) ∧
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX D f ∧
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f)
        (E : Mori.PrimeDivisor Y),
        (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ hp).IsExceptional →
        ∀ b : ℝ, IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ hp).valuation b →
          0 < b

/-- Let `(X, D)` be a log variety with `K_X + D` `ℝ`-Cartier. `(X, D)` is *Kawamata log terminal*
(klt) if `a_ℓ(F, D) > 0` for every divisor `F` of `k(X)` with nonempty center on `X`. -/
@[mmp "def_fa2_klt"]
def IsKawamataLogTerminal (n : ℕ) (K : Divisor X) (D : RDivisor X) : Prop :=
  IsLogVariety k sX D ∧ K.IsCanonicalDivisor sX n ∧
    IsCartierCombination (Divisor.toRDivisor K + D) ∧
    ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
      ∀ b : ℝ, IsLogDiscrepancy sX n K D F b → 0 < b

end MMP.Flips
