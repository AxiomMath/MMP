module

public import MMP.AlgebraicGeometry.Divisor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ProjectiveLayer

/-!
# The data of the fractional logarithmic complex on an open and closed piece

For an open `U` of `V`, restriction of divisors to `U`
(`MMP.FourfoldProofs.FractionalLogComplexProof.restrictDivisor`) is additive and preserves
effectivity, so the numerical conditions on `D = S + Supp Bn` and on `0 ≤ Bn < N` restrict. When
`U` is also closed, `U` is compact if `V` is, and `U ⟶ V ⟶ Spec ℂ` is projective if `π` is.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.restrictDivisor_add`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictDivisor_zsmul`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.restrictDivisor_nonneg`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.compactSpace_of_isClosed`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.isProjective_opens_ι_comp`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {X : Scheme.{u}} (U : X.Opens)

/-- Restriction of divisors to an open `U` is additive. -/
theorem restrictDivisor_add (D D' : MMP.Mori.Divisor X) :
    restrictDivisor U (D + D') = restrictDivisor U D + restrictDivisor U D' :=
  Finsupp.ext fun E => by simp [restrictDivisor_apply]

/-- Restriction of divisors to an open `U` commutes with integer scalar multiplication. -/
theorem restrictDivisor_zsmul (m : ℤ) (D : MMP.Mori.Divisor X) :
    restrictDivisor U (m • D) = m • restrictDivisor U D :=
  Finsupp.ext fun E => by simp [restrictDivisor_apply]

/-- The restriction of an effective divisor to an open `U` is effective. -/
theorem restrictDivisor_nonneg {D : MMP.Mori.Divisor X} (hD : 0 ≤ D) :
    0 ≤ restrictDivisor U D :=
  Finsupp.le_def.2 fun E => by
    rw [restrictDivisor_apply]
    exact Finsupp.le_def.1 hD _

/-- A closed open subscheme of a compact scheme is compact. -/
theorem compactSpace_of_isClosed [CompactSpace X] (hU : IsClosed (U : Set X)) :
    CompactSpace U.toScheme :=
  isCompact_iff_compactSpace.mp hU.isCompact

/-- The restriction of a projective morphism to an open and closed subscheme is projective. -/
theorem isProjective_opens_ι_comp {T : Scheme.{u}} (f : X ⟶ T) (hf : IsProjective f)
    (hU : IsClosed (U : Set X)) : IsProjective (U.ι ≫ f) := by
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]; exact hU)
  exact hf.isClosedImmersion_comp U.ι

end MMP.FourfoldProofs.FractionalLogComplexProof
