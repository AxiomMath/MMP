/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SNC

/-!
# Basic notions of *Flips and abundance for algebraic threefolds*

The definitions of §1.6.2 and §§2.1–2.3 of Kollár et al., *Flips and abundance for algebraic
threefolds* (FA): divisors of the function field and divisors over a variety, their centers,
exceptional divisors, snc divisors, maps over a base, `ℝ`-divisors and their supports,
boundaries, log varieties and `ℝ`-Cartier divisors.

FA works over `ℂ`; here the base is an arbitrary field `k`, and a variety is a `k`-scheme `X`
with structure morphism `s_X : X ⟶ Spec k` (`MMP.Mori.IsNormalVariety`).

Several of these notions are those of Kollár–Mori, already formalized in `MMP.Mori`; they are
registered here under their FA labels:
* an `ℝ`-divisor (resp. `ℚ`-divisor) is `MMP.Mori.RDivisor` (resp. `MMP.Mori.QDivisor`), finite
  formal sums of prime divisors, ordered coefficientwise, with effectivity
  `MMP.Mori.DivisorWithCoeffs.IsEffective`;
* the support is `MMP.Mori.DivisorWithCoeffs.supp`;
* a map `Y ⤏ X` is Mathlib's `AlgebraicGeometry.Scheme.RationalMap`, with domain of definition
  `AlgebraicGeometry.Scheme.RationalMap.domain`; it is a morphism when
  `MMP.Mori.RationalMap.IsMorphism`, and a modification when `MMP.Mori.RationalMap.IsBirational`.

## Main definitions

* `MMP.Flips.IsDivisorOfFunctionField`: a divisor of `k(X)`, the valuation `ord_E` of a prime
  divisor `E` on a normal variety `Y` with `k(Y) ≅ k(X)` over `k`.
* `MMP.Flips.ProperDivisorOver`: a divisor `(Y, f, E)` over `X` in the sense of FA, with `f`
  proper birational; its center `MMP.Flips.ProperDivisorOver.center = f(E)`, and
  `MMP.Flips.ProperDivisorOver.IsExceptional`: `dim f(E) ≤ dim X - 2`.
* `MMP.Flips.HasNonemptyCenter`: a divisor of `k(X)` realized by a divisor over `X`.
* `MMP.Flips.IsSNCDivisor`: reduced divisors with smooth components whose local equations at
  every closed point are part of a regular system of parameters.
* `MMP.Flips.RationalMap.IsOver`: a map over a base `Z`.
* `MMP.Flips.IsBoundary`, `MMP.Flips.IsLogVariety`, `MMP.Flips.logCanonicalDivisor`.
* `MMP.Flips.IsCartierCombination`: `ℝ`-Cartier (resp. `ℚ`-Cartier) divisors, `ℝ`- (resp.
  `ℚ`-)linear combinations of Cartier divisors.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.6.2),
  (1.14.2), Definitions 2.1–2.3
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

/-! ### Notions of Kollár–Mori, under their FA labels -/

attribute [mmp "def_fa2_r_divisor"] MMP.Mori.RDivisor MMP.Mori.QDivisor
  MMP.Mori.DivisorWithCoeffs.coeff MMP.Mori.DivisorWithCoeffs.IsEffective
attribute [mmp "def_fa2_support"] MMP.Mori.DivisorWithCoeffs.supp
attribute [mmp "def_fa2_map"] MMP.Mori.RationalMap.IsMorphism
attribute [mmp "def_fa2_modification"] MMP.Mori.RationalMap.IsBirational

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### Divisors of the function field and divisors over a variety -/

/-- A valuation `v` of the function field `k(X)` of an integral `k`-scheme is a *divisor of
`k(X)`* if there are a normal variety `Y` over `k`, a `k`-isomorphism `k(X) ≅ k(Y)` and a prime
divisor `E ⊆ Y` with `v = ord_E` under this isomorphism. The valuation `ord_E` is
`MMP.Mori.PrimeDivisor.divisorialValuation`, whose valuation ring is `𝒪_{Y,E}`. -/
@[mmp "def_fa1a_divisor_of_function_field"]
def IsDivisorOfFunctionField [IsIntegral X] (v : Valuation X.functionField ℤᵐ⁰) : Prop :=
  letI := functionFieldAlgebra sX
  ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k sY) (E : Mori.PrimeDivisor Y),
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsNormal Y := hY.2
    haveI : IsLocallyNoetherian Y :=
      haveI := hY.1.toLocallyOfFiniteType
      LocallyOfFiniteType.isLocallyNoetherian sY
    letI := functionFieldAlgebra sY
    ∃ e : X.functionField ≃ₐ[k] Y.functionField,
      v = E.divisorialValuation.comap (e : X.functionField →+* Y.functionField)

/-- A *divisor over* a variety `X` in the sense of FA: a divisor `(Y, f, E)` over `X`
(`MMP.Mori.DivisorOver`: `Y` a normal variety, `f : Y ⟶ X` birational, `E ⊆ Y` a prime divisor)
with `f` proper. Its valuation `ord_E`, a valuation of `k(X)` through `f`, is
`MMP.Mori.DivisorOver.valuation`. -/
@[mmp "def_fa1a_divisor_over_x"]
structure ProperDivisorOver extends DivisorOver k sX where
  /-- `f : Y ⟶ X` is proper. -/
  isProper : IsProper f

namespace ProperDivisorOver

variable {k sX} (D : ProperDivisorOver k sX)

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X`, a valuation of `k(X)`. -/
@[mmp "def_fa1a_divisor_over_x"]
abbrev valuation [IsIntegral X] : Valuation X.functionField ℤᵐ⁰ :=
  D.toDivisorOver.valuation

/-- The image `f(E)` of the prime divisor `E` under the proper morphism `f` is closed in `X`. -/
theorem isClosed_image_support : IsClosed (D.f '' D.E.support) :=
  haveI := D.isProper
  D.f.isClosedMap _ (by
    rw [show (D.E.support : Set D.Y) = closure {D.E.genericPoint} from
      AlgebraicGeometry.PrimeDivisor.support_eq_closure D.E]
    exact isClosed_closure)

/-- The *center* `Center_X(E) = f(E)` of a divisor `(Y, f, E)` over `X`, an irreducible closed
subset of `X` (closed because `f` is proper). -/
@[mmp "def_fa1a_center"]
def center : IrreducibleCloseds X where
  carrier := D.f '' D.E.support
  isIrreducible' := D.toDivisorOver.isIrreducible_image_support
  isClosed' := D.isClosed_image_support

/-- The underlying set of `Center_X(E)` is `f(E)`. -/
theorem coe_center : (D.center : Set X) = D.f '' D.E.support := rfl

/-- The FA center `f(E)` is the Kollár–Mori center `closure (f(E))`. -/
theorem center_eq_toDivisorOver_center : D.center = D.toDivisorOver.center :=
  IrreducibleCloseds.ext D.isClosed_image_support.closure_eq.symm

/-- A divisor `(Y, f, E)` over `X` is *exceptional* if `dim Center_X(E) ≤ dim X - 2`. -/
@[mmp "def_fa1a_exceptional_divisor"]
def IsExceptional : Prop :=
  topologicalKrullDim (D.center : Set X) + 2 ≤ topologicalKrullDim X

end ProperDivisorOver

/-- A divisor `v` of `k(X)` *has nonempty center on `X`* if `v = ord_E` for some divisor
`(Y, f, E)` over `X` (with `f` proper). -/
@[mmp "def_fa1a_nonempty_center"]
def HasNonemptyCenter [IsIntegral X] (v : Valuation X.functionField ℤᵐ⁰) : Prop :=
  IsDivisorOfFunctionField k sX v ∧ ∃ D : ProperDivisorOver k sX, D.valuation = v

/-! ### Simple normal crossing divisors -/

variable {k} in
/-- A reduced divisor `D = D₁ + ⋯ + D_r` (the `Dᵢ` distinct prime divisors) on a (smooth) variety
`X` is a *simple normal crossing* (*snc*) divisor if every `Dᵢ` is smooth and, at every closed
point `p ∈ X`, local equations at `p` of those `Dᵢ` containing `p` are part of a regular system
of parameters of `𝒪_{X,p}`: there are a regular system of parameters `z₁, …, zₙ` of `𝒪_{X,p}`
and an injective `j` from `{i : p ∈ Dᵢ}` to `{1, …, n}` with `z_{j(i)}` generating the ideal of
`Dᵢ` in `𝒪_{X,p}`. -/
@[mmp "def_fa1a_snc_divisor"]
def IsSNCDivisor (D : Divisor X) : Prop :=
  (∀ E : Mori.PrimeDivisor X, D.coeff E = 0 ∨ D.coeff E = 1) ∧
    (∀ E ∈ D.support, IsSmoothScheme (E.idealSheaf.subschemeι ≫ sX)) ∧
    ∀ p : X, IsClosed ({p} : Set X) → ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
      (j : {E : Mori.PrimeDivisor X // E ∈ D.support ∧ p ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf p = Ideal.span {z (j E)}

/-! ### Maps over a base -/

namespace RationalMap

variable {Y Z : Scheme.{u}}

/-- For morphisms `p : Y ⟶ Z` and `q : X ⟶ Z` (proper, in FA), a map `f : Y ⤏ X` is a map
*over `Z`* if `q ∘ f = p` as maps. -/
@[mmp "def_fa2_map"]
def IsOver (p : Y ⟶ Z) (q : X ⟶ Z) (f : Y.RationalMap X) : Prop :=
  f.compHom q = p.toRationalMap

end RationalMap

/-! ### Boundaries and log varieties -/

/-- An `ℝ`-divisor `D = ∑ dᵢ Dᵢ` is a *boundary* if `0 ≤ dᵢ ≤ 1` for all `i`. -/
@[mmp "def_fa2_boundary"]
def IsBoundary {X : Scheme.{u}} (D : RDivisor X) : Prop :=
  ∀ E : Mori.PrimeDivisor X, 0 ≤ D.coeff E ∧ D.coeff E ≤ 1

/-- A *log variety* `(X, D_X)`: a normal variety `X` together with a boundary `D_X` on `X`. -/
@[mmp "def_fa2_log_variety"]
structure IsLogVariety (D : RDivisor X) : Prop where
  /-- `X` is a normal variety. -/
  isNormalVariety : IsNormalVariety k sX
  /-- `D` is a boundary. -/
  isBoundary : IsBoundary D

/-- The *log canonical divisor* `K_X + D_X` of a log variety `(X, D_X)`, for a canonical divisor
`K_X` (`MMP.Mori.Divisor.IsCanonicalDivisor`, determined up to linear equivalence). -/
@[mmp "def_fa2_log_variety"]
def logCanonicalDivisor {X : Scheme.{u}} (K : Divisor X) (D : RDivisor X) : RDivisor X :=
  Divisor.toRDivisor K + D

/-! ### `ℝ`-Cartier divisors -/

/-- An `ℝ`-divisor (resp. `ℚ`-divisor) `D` on a normal variety is *`ℝ`-Cartier* (resp.
*`ℚ`-Cartier*) if `D = ∑_{j=1}^m r_j L_j` for some `m ≥ 0`, some `r_j ∈ ℝ` (resp. `ℚ`) and some
(Weil divisors of) Cartier divisors `L_j`, which need not be prime or reduced. Here `K` is the
coefficient ring, `ℝ` or `ℚ`. -/
@[mmp "def_fa2_r_cartier"]
def IsCartierCombination {K : Type*} [Ring K] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (D : DivisorWithCoeffs K X) : Prop :=
  ∃ (m : ℕ) (r : Fin m → K) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
    D = ∑ j, r j • (L j).mapCoeffs (Int.cast : ℤ → K) Int.cast_zero

end MMP.Flips
