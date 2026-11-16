module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs

/-!
# The spaces `N¹(X)_ℝ` and `N₁(X)_ℝ` and their intersection pairing

For a variety `X` over a field `k`, `N¹(X)_ℝ` is the real vector space of `ℝ`-Cartier divisors
modulo numerical equivalence (`D ≡ 0` when `(D · C) = 0` for every integral curve `C ⊆ X`
proper over `k`), and `N₁(X)_ℝ` is the real vector space of real `1`-cycles modulo numerical
equivalence. Intersection `([D], [Z]) ↦ (D · Z)` is a bilinear pairing between them.

All three already exist in the library, so this file only registers them:

* `MMP.Fourfold.NumericalDivisorClasses`: `N¹(X)_ℝ`, the quotient of `KCartierDivisor ℝ X` by the
  numerically trivial divisors;
* `MMP.Mori.NumericalCurveClasses`: `N₁(X)_ℝ`, the quotient of `OneCycle ℝ sX` by the
  numerically trivial cycles;
* `MMP.Fourfold.numericalPairing`: the intersection pairing `N¹(X)_ℝ × N₁(X)_ℝ → ℝ`.

## Implementation notes

The pairing is nondegenerate by construction: `MMP.Fourfold.numericalPairing_injective` and, on
an integral scheme, `MMP.Fourfold.numericalPairing_flip_injective`. Its perfectness for a
projective variety is the finite-dimensionality of `N¹(X)_ℝ` (the theorem of the base), which is
a separate result and not part of this definition.
-/

attribute [mmp "def_oai4_bg_numerical_classes"] MMP.Fourfold.NumericalDivisorClasses
attribute [mmp "def_oai4_bg_numerical_classes"] MMP.Mori.NumericalCurveClasses
attribute [mmp "def_oai4_bg_numerical_classes"] MMP.Fourfold.numericalPairing
