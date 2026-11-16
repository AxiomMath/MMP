module

public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.FiberTypeQFactorialPullback

section

/-!
# The base of a fibre type contraction of a `ℚ`-factorial klt pair is `ℚ`-factorial

Let `X` be a `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero and `(X, Δ)` a klt pair with `Δ` effective. Let `R` be an extremal ray of the
closed cone of curves `NE̅(X)` on which `K_X + Δ` is negative away from `0`, and let `g : X ⟶ Z`
be a contraction of `R` of fibre type, i.e. with `dim Z < dim X`. Then `Z` is `ℚ`-factorial.

## Main results

* `MMP.Mori.isQFactorial_of_isFiberTypeContraction`: the statement above.

## Implementation notes

The fibre type contraction is `MMP.Mori.IsFiberTypeContraction`, which carries the extremality
of `R`, the contraction `MMP.Mori.IsContractionOfFace` and the inequality of dimensions. The
`ℚ`-factoriality of `Z` is `MMP.Fourfold.IsQFactorial`, which is stated for a locally noetherian
normal scheme; these two properties of `Z` follow from `Z` being the target of a contraction of a
normal projective variety, and are taken as instance arguments so that Weil divisors on `Z` make
sense in the statement.

Every invertible sheaf on `X` of degree `0` on the curves with class in `R` descends to `Z`
(`MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace`), so `(R, g)` has the
pullback property, and `Z` is `ℚ`-factorial by
`MMP.Mori.isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **The base of a fibre type contraction is `ℚ`-factorial** (Kollár–Mori 3.18). Let `X` be a
`ℚ`-factorial projective variety over an algebraically closed field `k` of characteristic zero,
`(X, Δ)` a klt pair with canonical divisor `K` and `Δ` effective, `R` a set of numerical curve
classes with `(K + Δ) · z < 0` for every nonzero `z ∈ R`, and `g : X ⟶ Z` a fibre type
contraction of the extremal ray `R`. Then `Z` is `ℚ`-factorial. -/
@[mmp "thm_km3b_fiber_contraction_q_factorial"]
public theorem isQFactorial_of_isFiberTypeContraction {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] (hQ : MMP.Fourfold.IsQFactorial sX)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {R : Set (NumericalCurveClasses sX)}
    (hneg : ∀ z ∈ R, z ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z < 0)
    {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsFiberTypeContraction k sX sZ R g) :
    MMP.Fourfold.IsQFactorial sZ :=
  isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback hQ hg fun L _ hL ↦
    exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ
      ⟨hg.isExtremalRay.1, hg.isExtremalRay.1.2.2.1, hneg⟩ hg.isContractionOfFace L hL

end MMP.Mori

end
