module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts

/-!
# The vector bundle of a finite locally free module is an affine-space bundle

## Main results

* `MMP.Modules.isAffineSpaceBundle_proj`: the projection `𝐕(ℰ) ⟶ X` of a finite locally free
  module of rank `r` is an affine-space bundle of rank `r`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace MMP.Modules

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- The projection of the vector bundle of a finite locally free module of rank `r` is an
affine-space bundle of rank `r`. -/
theorem isAffineSpaceBundle_proj : Stacks.Chow.IsAffineSpaceBundle (proj E) r :=
  Stacks.Chow.isAffineSpaceBundle_vectorBundleToBase E r

end MMP.Modules
