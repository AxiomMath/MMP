module

public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program

/-!
# The rational birational program property `Q(d)`

For `d ≥ 1`, the property `Q(d)` asserts that the log minimal model program runs, over a fixed
projective base, for smooth rational snc pairs with coefficients less than one: for every
projective birational morphism `p : W ⟶ Z` of normal projective complex `d`-folds with `W`
smooth, and every effective `ℚ`-divisor `C` on `W` with snc support and all coefficients less
than one, there is a finite negative program from `(W, C)` over `Z` ending with a projective
`ℚ`-factorial klt pair `(Y, C_Y)` over `Z` whose adjoint `K_Y + C_Y` is nef over `Z`, where
`C_Y` is the push-forward of `C` and the induced birational map `W ⤏ Y` extracts no prime
divisor.

## Main definitions

* `MMP.Fourfold.RationalBirationalProgramProperty`: the property `Q(d)`.

## Implementation notes

The finite negative program over `Z` is a relative elementary dlt program
`MMP.Fourfold.RelativeDltProgram` over `Z` with finitely many birational steps, all of whose
models are projective (`MMP.Fourfold.RelativeDltProgram.IsProjective`), and with no final
fibre-type contraction. Its steps are divisorial contractions and flips of
`(K + B)`-negative extremal rays of the relative cones of curves over `Z`.

The map `φ : W ⤏ Y` induced by the program is described as a birational map over `Z`: since
`Y ⟶ Z` is birational, there is exactly one rational map `φ` with `q ∘ φ = p` as rational maps,
where `q : Y ⟶ Z`. That the boundary of `Y` is the push-forward of `C` is `C_Y = φ_* C`, and that
the program extracts no prime divisor is that every prime divisor of `Y` is the birational
transform `φ_* P` of a prime divisor `P` of `W`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **The rational birational program property `Q(d)`.** For every projective birational
morphism `p : W ⟶ Z` (over `ℂ`) of normal projective complex varieties of dimension `d`, with `W`
smooth, every canonical divisor `K` of `W` and every effective `ℚ`-divisor `C` on `W` with snc
support and all coefficients less than one, there is a relative elementary dlt program `P` from
`(W, C)` over `Z`, with canonical divisors `K_i` and boundaries `C_i`, such that

* `P` has finitely many birational steps `n`, all its models are projective and it does not stop
  with a fibre-type contraction;
* the last model `Y = X_n`, with `q : Y ⟶ Z`, is `ℚ`-factorial and projective, `q` is projective,
  `(Y, C_n)` is klt and `K_n + C_n` is nef over `Z`;
* there is a birational map `φ : W ⤏ Y` over `Z` (`q ∘ φ = p`) with `C_n = φ_* C`, such that every
  prime divisor of `Y` is the birational transform `φ_* P` of a prime divisor `P` of `W`. -/
@[mmp "def_fourfold_rational_birational_program_property"]
def RationalBirationalProgramProperty (d : ℕ) : Prop :=
  1 ≤ d ∧
  ∀ (W : Scheme.{0}) [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (p : W ⟶ Z),
    MMP.Mori.IsProjectiveVariety ℂ sW → IsNormalVariety ℂ sW → IsSmoothScheme sW →
    topologicalKrullDim W = d →
    MMP.Mori.IsProjectiveVariety ℂ sZ → IsNormalVariety ℂ sZ → topologicalKrullDim Z = d →
    p ≫ sZ = sW → IsProjectiveMorphism p → IsBirationalMorphism p →
    ∀ K : Divisor W, K.IsCanonicalDivisor sW d →
    ∀ C : QDivisor W, (∀ P, 0 ≤ C.coeff P ∧ C.coeff P < 1) → DivisorWithCoeffs.IsSNC sW C →
    ∃ P : RelativeDltProgram sW sZ p K C,
      P.n ≠ ⊤ ∧ P.IsProjective ∧ ¬ P.hasFinal ∧
      IsQFactorial (modelStr sW P.sY P.n.toNat) ∧
      MMP.Mori.IsProjectiveVariety ℂ (modelStr sW P.sY P.n.toNat) ∧
      IsProjectiveMorphism (modelMap p P.πY P.n.toNat) ∧
      IsKltPair (modelStr sW P.sY P.n.toNat) (divisorSeq C P.BY P.n.toNat) ∧
      QDivisor.IsRelativelyNef (modelStr sW P.sY P.n.toNat) (modelMap p P.πY P.n.toNat)
        (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq C P.BY P.n.toNat) ∧
      ∃ φ : W.RationalMap (modelSeq W P.Y P.n.toNat),
        MMP.Mori.RationalMap.IsBirational φ ∧
        MMP.Flips.RationalMap.IsOver p (modelMap p P.πY P.n.toNat) φ ∧
        divisorSeq C P.BY P.n.toNat = MMP.Mori.RationalMap.transformDivisor φ C ∧
        ∀ Q : MMP.Mori.PrimeDivisor (modelSeq W P.Y P.n.toNat),
          ∃ D : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor φ D = some Q

end MMP.Fourfold
