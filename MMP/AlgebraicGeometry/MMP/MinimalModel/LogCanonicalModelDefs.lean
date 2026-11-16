/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.Singularities.PairClasses

/-!
# Log flips, flops and log canonical models in *Flips and abundance*

Log flips and flops (FA 2.26.5.1), relative (weak) log canonical models (FA 2.15.2–2.15.3),
(weak) log canonical models of a morphism with respect to `𝓕` (FA 2.21.1, 2.21.3), and numerical
triviality on the fibre over a point (FA 2.28.2.2).

## Main definitions

* `MMP.Flips.IsLogFlip`, `MMP.Flips.IsFlop`.
* `MMP.Flips.IsRelativeLogCanonicalModel`, `MMP.Flips.IsRelativeWeakLogCanonicalModel`.
* `MMP.Flips.IsWeakLogCanonicalModelOf`, `MMP.Flips.IsLogCanonicalModelOf`.
* `MMP.Flips.IsNumericallyTrivialOverPoint`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.15.2,
  2.15.3, 2.21.1, 2.21.3, 2.26.5.1, 2.28.2.2
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

/-! ### Log flips and flops -/

section Flips

variable (k : Type u) [Field k] {X Z X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sZ : Z ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']

/-- Let `(X, B_X)` be a log variety with canonical divisor `K` of dimension `n` and `K_X + B_X`
`ℝ`-Cartier, and `f : X ⟶ Z` a small birational contraction with `-(K_X + B_X)` `f`-ample. A
*log flip* of `f` is a flip of `f` with respect to `E = K_X + B_X` (`MMP.Flips.IsFlip`, which
records that `f` is a small birational contraction, that `E` is `ℝ`-Cartier and that `-E` is
`f`-ample). For `B_X = 0` this is a *flip*. -/
@[mmp "def_fa2_log_flip"]
def IsLogFlip (n : ℕ) (K : Divisor X) (B : RDivisor X) (f : X ⟶ Z) (fp : X' ⟶ Z)
    (g : X.RationalMap X') : Prop :=
  IsLogVariety k sX B ∧ K.IsCanonicalDivisor sX n ∧
    IsFlip k sX sZ sX' (logCanonicalDivisor K B) f fp g

/-- If, in a flip of `f : X ⟶ Z` with respect to `E`, the canonical divisor `K_X` (of dimension
`n`) is `ℝ`-Cartier and numerically `f`-trivial, the flip is an *`E`-flop* of `f`. -/
@[mmp "def_fa2_flop"]
def IsFlop [QuasiCompact sX] (n : ℕ) (K : Divisor X) (E : RDivisor X) (f : X ⟶ Z) (fp : X' ⟶ Z)
    (g : X.RationalMap X') : Prop :=
  K.IsCanonicalDivisor sX n ∧ IsCartierCombination (Divisor.toRDivisor K) ∧
    IsNumericallyTrivialOver k sX f (Divisor.toRDivisor K) ∧ IsFlip k sX sZ sX' E f fp g

end Flips

/-! ### Relative log canonical models -/

section Models

variable {k : Type u} [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
  [QuasiCompact sY]

/-- Let `(Y, D_Y)` be a log variety with canonical divisor `K` of dimension `n` and `K_Y + D_Y`
`ℝ`-Cartier, and `g : Y ⟶ Z` a proper morphism. Then `g : (Y, D_Y) ⟶ Z` is a *relative log
canonical model* if `K_Y + D_Y` is `g`-ample and `(Y, D_Y)` is lc. For `Z = Spec k` this is a
*log canonical model*. -/
@[mmp "def_fa2_relative_log_canonical_model"]
def IsRelativeLogCanonicalModel (n : ℕ) (K : Divisor Y) (D : RDivisor Y) (g : Y ⟶ Z) : Prop :=
  IsProper g ∧ IsLogCanonical sY n K D ∧ IsRelativelyAmple g (logCanonicalDivisor K D)

/-- Let `(Y, D_Y)` be a log variety with canonical divisor `K` of dimension `n` and `K_Y + D_Y`
`ℝ`-Cartier, and `g : Y ⟶ Z` a proper morphism. Then `g : (Y, D_Y) ⟶ Z` is a *relative weak log
canonical model* if `K_Y + D_Y` is `g`-nef and `(Y, D_Y)` is lc. -/
@[mmp "def_fa2_relative_weak_log_canonical_model"]
def IsRelativeWeakLogCanonicalModel (n : ℕ) (K : Divisor Y) (D : RDivisor Y) (g : Y ⟶ Z) :
    Prop :=
  IsProper g ∧ IsLogCanonical sY n K D ∧ IsRelativelyNef k sY g (logCanonicalDivisor K D)

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **Weak log canonical models of a morphism.** In the setting of FA 2.21: `f : X ⟶ Z` and
`g : Y ⟶ Z` are proper morphisms, `(X, D_X)` has canonical divisor `K_X` of dimension `n`, `Y` has
canonical divisor `K_Y`, and `φ : X ⤏ Y` is a modification of `f` into `g` satisfying, with the
`φ⁻¹`-exceptional primes `F_i` of `Y`, the hypotheses of the `𝓕`-birational transform, with an
admissible `𝓕 = (c_i)` (`1 ≥ c_i ≥ min {1, -a(F_i, D_X)}`); all of this is
`MMP.Flips.IsFBirationalTransform`, with `G = D_{𝓕,Y}`. Then `g : (Y, D_{𝓕,Y}) ⟶ Z` is a *weak log
canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕`* if `K_Y + D_{𝓕,Y}` is `ℝ`-Cartier,
`g : (Y, D_{𝓕,Y}) ⟶ Z` is a relative weak log canonical model, and
`a(ord_P, D_{𝓕,Y}) ≥ a(ord_P, D_X)` for every prime divisor `P` of `X` with `φ_*P = 0`; here
`ord_P`, a divisor of `k(X) = k(Y)`, is realized over `Y` through `φ⁻¹` by a divisor `E` over `Y`
(`MMP.Flips.IsRealizedOver`). -/
@[mmp "def_fa2_weak_lc_model_of_morphism"]
def IsWeakLogCanonicalModelOf (n : ℕ) (K_X : Divisor X) (D_X : RDivisor X) (K_Y : Divisor Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (φ : X.RationalMap Y) (c : Mori.PrimeDivisor Y → ℝ)
    (G : RDivisor Y) : Prop :=
  IsProper f ∧ IsProper g ∧ IsModificationOf f g φ ∧
    IsFBirationalTransform sX sY n K_X D_X φ c G ∧
    IsCartierCombination (Divisor.toRDivisor K_Y + G) ∧
    IsRelativeWeakLogCanonicalModel sY n K_Y G g ∧
    ∀ (hφ : Mori.RationalMap.IsBirational φ) (P : Mori.PrimeDivisor X),
      Mori.RationalMap.transformPrimeDivisor φ P = none →
      ∀ (E : ProperDivisorOver k sY) (a a' : ℝ), IsRealizedOver sY hφ.inverse P E →
        IsDiscrepancy sY n K_Y G E.valuation a →
          IsDiscrepancy sX n K_X D_X P.divisorialValuation a' → a' ≤ a

/-- `g : (Y, D_{𝓕,Y}) ⟶ Z` is a *log canonical model of `f` with respect to `𝓕`* if it is a weak
log canonical model of `f` and a relative log canonical model. -/
@[mmp "def_fa2_lc_model_of_morphism"]
def IsLogCanonicalModelOf (n : ℕ) (K_X : Divisor X) (D_X : RDivisor X) (K_Y : Divisor Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (φ : X.RationalMap Y) (c : Mori.PrimeDivisor Y → ℝ)
    (G : RDivisor Y) : Prop :=
  IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G ∧
    IsRelativeLogCanonicalModel sY n K_Y G g

end Models

/-! ### Numerical triviality over a point -/

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Let `f : X ⟶ Z` be a proper morphism of normal varieties, `A` an `ℝ`-Cartier divisor on `X`
and `b ∈ Z` a point. `A` is *numerically trivial on `f⁻¹(b)`* if there is a dense open subset `V`
of `closure {b}` such that `A · C = 0` for every irreducible curve `C ⊆ X` with `f(C) = {z}`,
`z ∈ V` a closed point. A dense open subset of the irreducible closed set `closure {b}` is one
containing its generic point `b`, that is, `V = U ∩ closure {b}` for an open `U ∋ b` of `Z`. -/
@[mmp "def_fa2_numerically_trivial_over_point"]
def IsNumericallyTrivialOverPoint (f : X ⟶ Z) (A : RDivisor X) (b : Z) : Prop :=
  IsCartierCombination A ∧
    ∃ U : Z.Opens, b ∈ U ∧
      ∀ C : ProperCurve sX, C.IsContractedBy f → f C.point ∈ U → f C.point ∈ closure {b} →
        IsClosed {f C.point} →
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
          IsRIntersectionNumber k sX A r L C x → x = 0

end MMP.Flips
