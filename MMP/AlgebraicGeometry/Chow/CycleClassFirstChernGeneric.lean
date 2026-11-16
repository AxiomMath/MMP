module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.SectionIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksEulerClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import MMP.AlgebraicTopology.SingularCohomology.Relative

/-!
# The topological first Chern class of a line bundle

For a quasi-coherent `𝒪_X`-module `ℰ` on a complex scheme `X`, finite locally free of rank one,
the *topological first Chern class* of the line bundle `𝐕(ℰ)` is the pull-back
`c₁ᵗᵒᵖ(ℰ) = 0^* u_ℰ ∈ H²(X(ℂ); R)` of the Thom class `u_ℰ` along the zero section.

## Main definitions

* `MMP.Modules.topFirstChernClass`: `c₁ᵗᵒᵖ(ℰ) = 0^* u_ℰ ∈ H²(X(ℂ))`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Stacks.Chow
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (E : X.Modules)
  [E.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]

/-! ### The topological first Chern class -/

/-- **The topological first Chern class** `c₁ᵗᵒᵖ(ℰ) = 0^* u_ℰ ∈ H²(X(ℂ); R)` of the line bundle
`𝐕(ℰ)` of a quasi-coherent module `ℰ`, finite locally free of rank one: the pull-back of the Thom
class along the zero section (Fulton, §19.1). It is the Euler class of `𝐕(ℰ)(ℂ) → X(ℂ)`
(`MMP.Modules.cast_eulerClass_eq_map_thomClass`). -/
def topFirstChernClass :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) univ
      ((2 * 1 : ℕ) : ℤ) :=
  (relativeSingularCohomology.map R (ModuleCat.of R R) (zeroSectionHom E) (A' := univᶜ)
    (fun x hx ↦ (hx (mem_univ x)).elim) ((2 * 1 : ℕ) : ℤ)).hom (thomClass R E 1)

end MMP.Modules
