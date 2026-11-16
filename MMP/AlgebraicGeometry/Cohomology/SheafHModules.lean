module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Sheaf cohomology of a module on a scheme is derived global sections

For an `𝒪_X`-module `F` on a scheme `X`, Mathlib's sheaf cohomology `Sheaf.H` of the underlying
abelian sheaf of `F` is, naturally in `F`, the right derived functor of global sections computed
in `𝒪_X`-modules, with its module structure forgotten.

## Main definitions

* `MMP.Cohomology.toSheafCompRightDerivedGlobalSectionsIso`: deriving `Γ(X, -)` on abelian sheaves
  after forgetting the module structure is deriving `Γ(X, -)` on `𝒪_X`-modules.
* `MMP.Cohomology.toSheafCompFunctorHIso`: the same for `Sheaf.H`.

## Main results

* `MMP.Cohomology.subsingleton_sheafH_iff`: `Hⁿ(X, F)` vanishes exactly when the `n`-th derived
  global sections of `F` in `𝒪_X`-modules vanish.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace MMP.Cohomology

variable (X : Scheme.{u})

/-- **Derived global sections of abelian sheaves agree with derived global sections of
modules.** For an `𝒪_X`-module `F`, `Rⁿ Γ(X, F)` computed on the underlying abelian sheaf is,
naturally in `F`, the `n`-th right derived functor of `Γ(X, -)` on `𝒪_X`-modules. -/
def toSheafCompRightDerivedGlobalSectionsIso (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op ⊤)).rightDerived n ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  (Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ n).symm ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ n).symm

/-- **Sheaf cohomology of a module is its derived global sections.** For an `𝒪_X`-module `F`,
Mathlib's sheaf cohomology `Hⁿ(X, F)` of the underlying abelian sheaf is, naturally in `F`, the
`n`-th right derived functor of `Γ(X, -)` on `𝒪_X`-modules. -/
def toSheafCompFunctorHIso (n : ℕ) :
    SheafOfModules.toSheaf X.ringCatSheaf ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology X) n ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _
      (Stacks.Cohomology.TopDegree.functorHIsoSectionsRightDerived X.toTopCat n) ≪≫
    toSheafCompRightDerivedGlobalSectionsIso X n

variable {X}

/-- **`Hⁿ(X, F)` vanishes exactly when the derived global sections of `F` do.** -/
theorem subsingleton_sheafH_iff (F : X.Modules) (n : ℕ) :
    Subsingleton (Sheaf.H.{u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) ↔
      Subsingleton (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj F) :=
  ((toSheafCompFunctorHIso X n).app F).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr

end MMP.Cohomology

end
