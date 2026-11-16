module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeAffineHom
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleOfModule

/-!
# The total space of a Stacks vector bundle on a complex scheme is a complex scheme

Let `ℰ` be a quasi-coherent `𝒪_X`-module, finite locally free of rank `r`, on a complex scheme
`X`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`). The
projection is affine and locally of finite type, so `𝐕(ℰ)` is a complex scheme
(`MMP.IsComplexScheme.of_isAffineHom`).

## Implementation notes

These are theorems, not instances: the rank `r` does not appear in their conclusions, so
instance search could not find it. Statements about `𝐕(ℰ)` as a complex scheme take
`[IsComplexScheme (totalSpace E)]`, discharged by `isComplexScheme_totalSpace E r`.

## Main results

* `MMP.Modules.locallyOfFiniteType_proj`, `MMP.Modules.flat_proj`: `π` is locally of finite type
  and flat.
* `MMP.Modules.isComplexScheme_totalSpace`: `𝐕(ℰ)` is a complex scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Modules

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

include r

/-- The projection of the vector bundle of a finite locally free module is locally of finite
type. -/
theorem locallyOfFiniteType_proj : LocallyOfFiniteType (proj E) :=
  Stacks.Chow.locallyOfFiniteType_vectorBundleToBase E r

/-- The projection of the vector bundle of a finite locally free module is flat. -/
theorem flat_proj : Flat (proj E) :=
  Stacks.Chow.flat_vectorBundleToBase E r

/-- **The total space of a Stacks vector bundle on a complex scheme is a complex scheme**: its
projection is affine of finite type. -/
theorem isComplexScheme_totalSpace [X.Over (Spec (.of ℂ))] [IsComplexScheme X] :
    IsComplexScheme (totalSpace E) :=
  haveI := locallyOfFiniteType_proj E r
  haveI : IsAffineHom (proj E) := Scheme.Modules.isAffineHom_vectorBundleToBase (S := X) (E := E)
  IsComplexScheme.of_isAffineHom (proj E)

end MMP.Modules
