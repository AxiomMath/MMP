module

public import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres

/-!
# Negativity for `ℚ`-Cartier `ℚ`-divisors

Let `q : T ⟶ V` be a proper birational morphism of normal varieties over a field `k` and `E` a
`ℚ`-Cartier `ℚ`-divisor on `T` such that `-E` is `q`-nef. If the pushforward `q_* E` is
effective, then `E` is effective.

## Main results

* `MMP.Mori.QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg`

## Implementation notes

The source assumes `q` projective; only properness is used, and a projective morphism is proper,
so the statement is made for proper `q`. The pushforward `q_* E` of a divisor along a birational
morphism is its birational transform `MMP.Mori.RationalMap.transformDivisor` along
`q.toRationalMap`, which keeps the coefficients of the non-exceptional prime divisors. The ground
field `k` is arbitrary.

The proof is the reverse implication of the negativity lemma
`MMP.Mori.QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39(1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-- **Negativity lemma.** Let `q : T ⟶ V` be a proper birational morphism of normal varieties
over `k` and `E` a `ℚ`-Cartier `ℚ`-divisor on `T` with `-E` `q`-nef. If the pushforward `q_* E`
is effective, then `E` is effective. -/
@[mmp "lem_mmp_rational_negativity"]
public theorem QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg
    (k : Type u) [Field k] {T V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (sT : T ⟶ Spec (.of k)) [QuasiCompact sT] [IsLocallyNoetherian T] [IsNormal T]
    (hV : IsNormalVariety k sV) (hT : IsNormalVariety k sT)
    (q : T ⟶ V) (hq : q ≫ sV = sT) [IsProper q] (hqb : IsBirationalMorphism q)
    {E : QDivisor T} (hE : E.IsQCartier) (hnef : (-E).IsRelativelyNef sT q)
    (heff : (RationalMap.transformDivisor (X := T) q.toRationalMap E).IsEffective) :
    E.IsEffective :=
  (QDivisor.isEffective_iff_isEffective_transformDivisor_of_isRelativelyNef_neg
    k sV sT hV hT q hq hqb hE hnef).2 heff

end MMP.Mori
