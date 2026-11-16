module

public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation

/-!
# Normalized divisorial valuations

Let `X` be an integral variety over `k`. A *normalized divisorial valuation* of `k(X)` is
`ord_E`, for a prime divisor `E` on a normal variety `W` with a proper birational morphism
`g : W ⟶ X` (over `k`). Its *centre* `c_X(v)` is the closure of `g(η_E)`, and `v` is
*exceptional over `X`* when the centre has codimension at least two.

The triples `(W, g, E)` with `g` birational (not necessarily proper) are the divisors
over `X`, `MMP.Mori.DivisorOver`, with valuation `MMP.Mori.DivisorOver.valuation` (the valuation
of the discrete valuation ring `𝒪_{W,E}`, transported to `k(X)` along `k(X) ↪ k(W)`; it is
`exp (-ord_E)` in Mathlib's multiplicative convention,
`MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord`) and centre
`MMP.Mori.DivisorOver.center`, the closure of `g(η_E)`
(`MMP.Mori.DivisorOver.center_eq_closure_genericPoint`). The definitions below add properness of
`g`. The generic point `η_V` of a closed irreducible `V` is Mathlib's `IsIrreducible.genericPoint`.

## Main definitions

* `MMP.Intersection.IsNormalizedDivisorialValuation`, `MMP.Intersection.IsCentre`,
  `MMP.Intersection.IsExceptionalValuation`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection

attribute [mmp "def_shared_divisorial_valuation_ord_e"] MMP.Mori.DivisorOver
  MMP.Mori.DivisorOver.valuation MMP.Mori.DivisorOver.center
  MMP.Mori.DivisorOver.center_eq_closure_genericPoint

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- `v` is a *normalized divisorial valuation* of `k(X)`: `v = ord_E` for a prime divisor `E` on a
normal variety `W` with a proper birational morphism `W ⟶ X`. -/
@[mmp "def_shared_divisorial_valuation_ord_e"]
def IsNormalizedDivisorialValuation (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    Prop :=
  ∃ D : MMP.Mori.DivisorOver k sX, IsProper D.f ∧ v = D.valuation

/-- `Z` is the *centre* `c_X(v)` of the normalized divisorial valuation `v`: the closure of the
image of the generic point of `E`, for `v = ord_E` as above. -/
@[mmp "def_shared_divisorial_valuation_ord_e"]
def IsCentre (v : Valuation X.functionField (WithZero (Multiplicative ℤ)))
    (Z : IrreducibleCloseds X) : Prop :=
  ∃ D : MMP.Mori.DivisorOver k sX, IsProper D.f ∧ v = D.valuation ∧ Z = D.center

/-- A normalized divisorial valuation `v` is *exceptional over `X`*: its centre has codimension
at least two in `X`. -/
@[mmp "def_shared_divisorial_valuation_ord_e"]
def IsExceptionalValuation (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    Prop :=
  ∃ D : MMP.Mori.DivisorOver k sX, IsProper D.f ∧ v = D.valuation ∧ 2 ≤ codimension D.center

end MMP.Intersection
