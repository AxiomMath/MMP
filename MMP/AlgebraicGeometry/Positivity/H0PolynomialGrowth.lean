module
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial

/-!
# Polynomial growth of `h⁰` of multiples of a Cartier divisor

Let `X` be a projective scheme over a field `k` of dimension at most `n` and `B` a Cartier
divisor on `X`. Then `h⁰(X, 𝒪_X(mB))` grows at most like `mⁿ`: there is `C > 0` with
`h⁰(X, 𝒪_X(mB)) ≤ C mⁿ` for every integer `m > 0`.

## Main results

* `MMP.Mori.exists_cartierH0_smul_le_pow`: the bound `h⁰(X, 𝒪_X(mB)) ≤ C mⁿ`.

## Implementation notes

The dimension hypothesis is the upper bound `dim X ≤ n` rather than the equality `dim X = n`;
this is the form in which the bound is applied to subschemes of smaller dimension, and it
includes the empty scheme. `h⁰` is `MMP.Mori.cartierH0`, the `k`-dimension of the global
sections of the invertible sheaf attached to a Cartier divisor, with `k`-structure given by the
structure morphism `f : X ⟶ Spec k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.58
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP.Mori

/-- `h⁰` of a Cartier divisor is the `k`-dimension of degree-zero cohomology of its sheaf. -/
private theorem cartierH0_eq_finrank_cohomologyOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (D : X.CartierDivisor) :
    cartierH0 k f D =
      Module.finrank k (cohomologyOverField k f (MMP.CartierDivisor.sheaf D) 0) :=
  ((cohomologyOverFieldZeroIsoSections k f
    (MMP.CartierDivisor.sheaf D)).toLinearEquiv.finrank_eq).symm

/-- **Growth of `h⁰` of multiples (KM 2.58).** On a projective scheme `X` over `k` of dimension
at most `n`, for a Cartier divisor `B` there is `C > 0` with `h⁰(X, 𝒪_X(mB)) ≤ C mⁿ` for every
integer `m > 0`. -/
@[mmp "lem_km2c_h0_growth_bound"]
public theorem exists_cartierH0_smul_le_pow {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : IsProjective f) {n : ℕ} (hn : topologicalKrullDim X ≤ n)
    (B : X.CartierDivisor) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℤ, 0 < m → (cartierH0 k f (m • B) : ℝ) ≤ C * (m : ℝ) ^ n := by
  have : IsProper f := hf.isProper
  obtain ⟨C, hC, hb⟩ := MMP.Foundations.exists_finrank_cohomologyOverField_zero_twistedSheaf_le_pow
    k f (MMP.CartierDivisor.sheaf B) (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f) n
    (by rwa [topologicalKrullDim_supp_unit])
  refine ⟨C, hC, fun m hm => ?_⟩
  obtain ⟨e⟩ := MMP.Resolution.Bridges.cartierSheaf_sum_iso_twistedSheaf (fun _ : Fin 1 => B)
    (fun _ => m)
  rw [cartierH0_eq_finrank_cohomologyOverField, show m • B = ∑ _ : Fin 1, m • B by simp,
    finrank_cohomologyOverField_eq_of_iso k f e 0]
  exact hb m hm

end MMP.Mori

end
