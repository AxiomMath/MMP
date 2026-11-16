module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogForms

/-!
# The finite cover used for the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` be an integral smooth projective variety, `D = S + Supp Bn` a relative
simple normal crossing divisor with `S` reduced and `0 ≤ Bn < N`, and `ψ` a rational function
with `N M = Bn + div ψ`. The degeneration at `E₁` of the fractional logarithmic complex is proved
on a finite surjective cover `g : V' ⟶ V` by an integral smooth projective variety on which the
reduced inverse image `S'` of `S` is a relative simple normal crossing divisor and `g^*ψ` has an
`N`-th root `z` in the function field of `V'`. The existence of such a cover is the statement
`MMP.FourfoldProofs.FractionalLogComplexProof.CoverDatum` below.

Since `N · div z = g^*(N M - Bn)`, every coefficient of `g^* Bn` is divisible by `N`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.CoverDatum`: the existence of the cover.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open scoped Classical in
/-- **The cover for the fractional logarithmic complex.** For an integral `V` over `ℂ`, a divisor
`S` and a rational function `ψ`, there are an integral smooth projective variety `V'` of
the same dimension, a finite surjective morphism `g : V' ⟶ V`, the reduced inverse image `S'` of
`S`, a relative simple normal crossing divisor on `V'`, and an `N`-th root in the function field
of `V'` of the pull-back of `ψ`. -/
def CoverDatum (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ)) [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (S : MMP.Mori.Divisor V) (N : ℕ)
    (ψ : (MMP.Mori.RationalFunctions V)ˣ) : Prop :=
  ∃ (V' : Scheme.{0}) (g : V' ⟶ V) (_ : IsFinite g) (_ : Surjective g) (_ : IsIntegral V')
    (_ : SmoothOfRelativeDimension n (g ≫ π)) (_ : IsProjective (g ≫ π))
    (_ : IsLocallyNoetherian V') (_ : IsNormal V') (_ : CompactSpace V')
    (S' : MMP.Mori.Divisor V') (_ : S'.IsRelativeSNC n (g ≫ π)),
    (∀ E' : MMP.Mori.PrimeDivisor V', S' E' =
      if ∃ E ∈ S.support, g E'.genericPoint = E.genericPoint then 1 else 0) ∧
    ∃ z : V'.functionField, z ^ N =
      functionFieldMap g (MMP.Mori.rationalFunctionsEquivFunctionField V ψ)

end MMP.FourfoldProofs.FractionalLogComplexProof
