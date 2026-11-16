/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.Singularities.PairClasses

/-!
# Sequences of flips and the divisors counted by `e(X, B)` in *Flips and abundance*

The exceptional divisors of small discrepancy `𝓔(X, B)` and their number `e(X, B)` (FA 6.6), and
sequences of flips for a pair `(X, D)` (FA 4.10, with extremal steps as in FA 2.26.3).

## Main definitions

* `MMP.Flips.smallDiscrepancySet`: `𝓔(X, B)`, the exceptional divisors `E` of `k(X)` with center
  on `X` and `a(E, X, B) ≤ 0`.
* `MMP.Flips.eCount`: `e(X, B) = #𝓔(X, B) ∈ ℕ ∪ {∞}`.
* `MMP.Flips.SequenceOfFlips`: a sequence of flips for `(X, D)`, with its length
  `L ∈ ℕ_{≥1} ∪ {∞}`, and `MMP.Flips.SequenceOfFlips.Terminates`.

## Implementation notes

A sequence of flips records its models `(X_i, D_i)` as the terms of a dependent pair (a scheme,
its structure morphism, a canonical divisor `K_i` of dimension `n` and the `ℚ`-divisor `D_i`),
indexed by `i : ℕ` and used for `i < L`; the condition `(X_0, D_0) = (X, D)` is an equality of such
terms.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.26.3, 4.10,
  6.6
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

/-! ### The divisors counted by `e(X, B)` -/

section Count

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- For a pair `(X, B)` (with canonical divisor `K` of dimension `n`), `𝓔(X, B)` is the set of
exceptional divisors `E` of `k(X)` (divisorial valuations, not divisors on `X`) with center on `X`
and `a(E, X, B) ≤ 0`, i.e. with log discrepancy `a_ℓ(E, X, B) ≤ 1`
(`MMP.Flips.mem_smallDiscrepancySet_iff_logDiscrepancy`). An exceptional divisor of `k(X)` with
center on `X` is the valuation `ord_E` of an exceptional divisor `(Y, f, E)` over `X`. -/
@[mmp "def_fa6_small_discrepancy_set"]
def smallDiscrepancySet (n : ℕ) (K : Divisor X) (B : RDivisor X) :
    Set (Valuation X.functionField ℤᵐ⁰) :=
  {v | (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = v) ∧
    ∃ a : ℝ, IsDiscrepancy sX n K B v a ∧ a ≤ 0}

/-- `E ∈ 𝓔(X, B)` exactly when its log discrepancy `a_ℓ(E, X, B)` is at most `1`. -/
@[mmp "def_fa6_small_discrepancy_set"]
theorem mem_smallDiscrepancySet_iff_logDiscrepancy (n : ℕ) (K : Divisor X) (B : RDivisor X)
    (v : Valuation X.functionField ℤᵐ⁰) :
    v ∈ smallDiscrepancySet sX n K B ↔
      (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = v) ∧
        ∃ b : ℝ, IsLogDiscrepancy sX n K B v b ∧ b ≤ 1 := by
  refine and_congr_right fun _ => ⟨fun ⟨a, ha, ha0⟩ => ⟨1 + a, ⟨a, ha, rfl⟩, by linarith⟩, ?_⟩
  rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
  exact ⟨a, ha, by linarith⟩

/-- For a klt pair `(X, B)`, `e(X, B) = #𝓔(X, B) ∈ ℕ ∪ {∞}` (finite by FA 6.5); for `B = 0` it is
written `e(X)`. -/
@[mmp "def_fa6_e_count"]
def eCount (n : ℕ) (K : Divisor X) (B : RDivisor X)
    (_hB : IsKawamataLogTerminal sX n K B) : ℕ∞ :=
  (smallDiscrepancySet sX n K B).encard

/-- `e(X) = e(X, 0)`, for `X` with `(X, 0)` klt. -/
@[mmp "def_fa6_e_count"]
abbrev eCountZero (n : ℕ) (K : Divisor X) (hX : IsKawamataLogTerminal sX n K 0) : ℕ∞ :=
  eCount sX n K 0 hX

end Count

/-! ### Sequences of flips -/

variable (k : Type u) [Field k]

/-- A *model* in a sequence of flips: a scheme `X_i` with its structure morphism over `k`, a
canonical divisor `K_i` and a `ℚ`-divisor `D_i`. -/
abbrev FlipModel : Type (u + 1) :=
  Σ Y : Scheme.{u}, (Y ⟶ Spec (.of k)) × Divisor Y × QDivisor Y

variable {k} {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A *sequence of flips* for `(X, D)`, `X` a normal variety with canonical divisor `K` of
dimension `n` and `D` a `ℚ`-divisor with `K_X + D` `ℚ`-Cartier: a length `L ∈ {1, 2, …} ∪ {∞}`,
pairs `(X_i, D_i)_{0 ≤ i < L}` (with canonical divisors `K_i`) with `(X_0, D_0) = (X, D)`, and, for
every `i` with `i + 1 < L`, a `(K_{X_i} + D_i)`-negative extremal contraction `φ_i : X_i ⟶ Z_i`
which is small, and a flip `φ_i⁺ : X_{i+1} ⟶ Z_i` of `φ_i` with respect to `K_{X_i} + D_i`, with
birational map `g_i : X_i ⤏ X_{i+1}` over `Z_i`, such that `D_{i+1} = g_{i*} D_i`. -/
@[mmp "def_fa4_sequence_of_flips"]
structure SequenceOfFlips (n : ℕ) (K : Divisor X) (D : QDivisor X) where
  /-- `X` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sX
  /-- `K` is a canonical divisor of `X`. -/
  isCanonicalDivisor : ∃ _ : IsLocallyNoetherian X, ∃ _ : IsNormal X, K.IsCanonicalDivisor sX n
  /-- `K_X + D` is `ℚ`-Cartier. -/
  isQCartier : ∃ _ : IsLocallyNoetherian X, ∃ _ : IsNormal X,
    (Divisor.toQDivisor K + D).IsQCartier
  /-- The length `L ∈ {1, 2, …} ∪ {∞}`. -/
  length : ℕ∞
  /-- The length is at least `1`. -/
  one_le_length : 1 ≤ length
  /-- The models `(X_i, K_i, D_i)`, used for `i < L`. -/
  model : ℕ → FlipModel k
  /-- `(X_0, D_0) = (X, D)` (with `K_0 = K`). -/
  model_zero : model 0 = ⟨X, sX, K, D⟩
  /-- The models are normal varieties. -/
  isNormalVariety_model : ∀ i : ℕ, (i : ℕ∞) < length → IsNormalVariety k (model i).2.1
  /-- Each `X_i` is locally Noetherian. -/
  isLocallyNoetherian_model : ∀ i, IsLocallyNoetherian (model i).1
  /-- Each `X_i` is normal. -/
  isNormal_model : ∀ i, IsNormal (model i).1
  /-- Each `X_i` is quasi-compact. -/
  compactSpace_model : ∀ i, CompactSpace (model i).1
  /-- `K_i` is a canonical divisor of `X_i`. -/
  isCanonicalDivisor_model : ∀ i : ℕ, (i : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    (model i).2.2.1.IsCanonicalDivisor (model i).2.1 n
  /-- The bases `Z_i` of the contractions. -/
  base : ℕ → Scheme.{u}
  /-- The structure morphisms of the `Z_i`. -/
  baseStr : ∀ i, base i ⟶ Spec (.of k)
  /-- The contractions `φ_i : X_i ⟶ Z_i`. -/
  contraction : ∀ i, (model i).1 ⟶ base i
  /-- The flips `φ_i⁺ : X_{i+1} ⟶ Z_i`. -/
  flip : ∀ i, (model (i + 1)).1 ⟶ base i
  /-- The birational maps `g_i : X_i ⤏ X_{i+1}`. -/
  flipMap : ∀ i, (model i).1.RationalMap (model (i + 1)).1
  /-- `φ_i` is a `(K_{X_i} + D_i)`-negative extremal contraction. -/
  isNegativeExtremalContraction : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    haveI := compactSpace_model i
    IsNegativeExtremalContraction k (model i).2.1 (baseStr i)
      (logCanonicalDivisor (model i).2.2.1 (QDivisor.toRDivisor (model i).2.2.2))
      (contraction i)
  /-- `φ_i` is small. -/
  isSmall : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    IsSmall k (baseStr i) (model i).2.1 (contraction i)
  /-- `φ_i⁺` is a flip of `φ_i` with respect to `K_{X_i} + D_i`, with birational map `g_i` over
  `Z_i`. -/
  isFlip : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    haveI := isLocallyNoetherian_model i
    haveI := isNormal_model i
    haveI := compactSpace_model i
    haveI := isLocallyNoetherian_model (i + 1)
    haveI := isNormal_model (i + 1)
    haveI := compactSpace_model (i + 1)
    IsFlip k (model i).2.1 (baseStr i) (model (i + 1)).2.1
      (logCanonicalDivisor (model i).2.2.1 (QDivisor.toRDivisor (model i).2.2.2))
      (contraction i) (flip i) (flipMap i)
  /-- `D_{i+1} = g_{i*} D_i`. -/
  transform_eq : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < length →
    (model (i + 1)).2.2.2 = Mori.RationalMap.transformDivisor (flipMap i) (model i).2.2.2

/-- A sequence of flips *terminates* if its length is finite. -/
@[mmp "def_fa4_sequence_of_flips"]
def SequenceOfFlips.Terminates {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (S : SequenceOfFlips sX n K D) : Prop :=
  S.length < ⊤

end MMP.Flips
