/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.AlgebraicGeometry.Curves.LocallyFreeDualizingDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.FiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothEquidimensionalOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Duality.ModelComparisonRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceDevissage
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.UpperShriekStructureSheafTrivial

/-!
# Serre duality for vector bundles on a smooth projective variety

Let `X` be a smooth projective variety of dimension `n` over a field `k`, with structure morphism
`f : X ⟶ Spec k`, canonical sheaf `ω_X = ⋀^n Ω_{X/k}`, and let `ℰ` be a locally free
`𝒪_X`-module of finite rank. Serre duality says that for every `i` there is an isomorphism of
`k`-vector spaces

  `H^i(X, ℰ^∨) ≅ H^{n-i}(X, ω_X ⊗ ℰ)^∨`.

The proof follows [Stacks, Tag 0FVV] and [Stacks, Tag 0BS4]. Since `f` is proper and smooth of
relative dimension `n`, the dualizing complex is `ω_X^• = f^×(𝒪_{Spec k}) ≅ ω_X[n]`. For a finite
locally free `ℱ`, duality gives `H^{-j}(X, ℱ)^∨ ≅ H^j(X, (- ⊗ ℱ^∨)~(ω_X^•))`, and the right-hand
side is `H^{n+j}(X, ω_X ⊗ ℱ^∨)`, the functor `- ⊗ ℱ^∨` being exact. Taking `ℱ = ℰ^∨`, using
`ℰ^∨∨ ≅ ℰ`, and dualizing once more (the cohomology of a coherent sheaf on a proper scheme is
finite dimensional) gives the statement.

As a consequence, for a line bundle `L` on `X`, `H^i(X, L^{-1}) = 0` if and only if
`H^{n-i}(X, ω_X ⊗ L) = 0` (Kollár--Mori, Remark 2.66).

## Main results

* `MMP.Mori.nonempty_dual_linearEquiv_exteriorPower_tensor_dual`: for `X` proper and smooth of
  relative dimension `n` over `k` and `ℱ` finite locally free,
  `H^i(X, ℱ)^∨ ≅ H^{n-i}(X, ω_X ⊗ ℱ^∨)`.
* `MMP.Mori.nonempty_linearEquiv_dual_exteriorPower_tensor`: Serre duality
  `H^i(X, ℰ^∨) ≅ H^{n-i}(X, ω_X ⊗ ℰ)^∨` on a smooth projective variety.
* `MMP.Mori.subsingleton_dual_iff_subsingleton_exteriorPower_tensor`:
  `H^i(X, L^{-1}) = 0 ↔ H^{n-i}(X, ω_X ⊗ L) = 0` for a line bundle `L`.

## Implementation notes

* `H^j(X, ℱ)` for `j : ℤ` is the hypercohomology `Stacks.Duality.derivedCohomologyOverField f`
  of `ℱ` placed in degree zero, a `k`-vector space; it agrees with sheaf cohomology in degrees
  `j ≥ 0` (`Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField`) and
  vanishes in negative degrees. With integer indices the statements hold for every `i : ℤ`, in
  particular for `0 ≤ i ≤ n`.
* `ω_X = ⋀^n Ω_{X/k}` is `Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n`,
  the dual `ℰ^∨ = 𝓗om(ℰ, 𝒪_X)` is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, and
  `⊗` is the sheaf tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`.
* A *smooth projective variety of dimension `n`* is a projective variety
  (`MMP.Mori.IsProjectiveVariety`) whose smooth locus is everything (`MMP.Mori.IsSmoothScheme`)
  and whose dimension `topologicalKrullDim X` is `n`. A *locally free sheaf of finite rank* is a
  finite locally free module; a *line bundle* is an invertible module, and `L^{-1}` is its dual
  `L^∨`.

## References

* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Remark 2.66
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- On a scheme proper over a field `k`, the cohomology `H^m(X, ℱ)` of a coherent module is a
finite-dimensional `k`-vector space for every `m : ℤ`: it vanishes for `m < 0`, and for `m ≥ 0` it
is sheaf cohomology of a coherent module on a proper scheme ([Stacks, Tag 02O6]). -/
theorem finiteDimensional_derivedCohomologyOverField_single_of_isCoherent [IsProper f]
    (F : X.Modules) [F.IsCoherent] (m : ℤ) :
    FiniteDimensional k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  rcases lt_or_ge m 0 with hm | hm
  · haveI := DerivedCategory.TStructure.t.isGE_shift
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by omega)
    haveI : Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) :=
      ⟨fun a b => by
        rw [DerivedCategory.TStructure.t.zero a 0 (-m) (by omega),
          DerivedCategory.TStructure.t.zero b 0 (-m) (by omega)]⟩
    haveI := (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).some.toEquiv.subsingleton
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, by omega⟩
    haveI := finiteDimensional_cohomologyOverField_of_isProper k f F n
    exact Module.Finite.equiv
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f F n)

/-- `H^{-i}(X, K⟦n⟧) ≅ H^{n-i}(X, K)` for an object `K` of `D(𝒪_X)` and integers `n`, `i`. -/
def derivedCohomologyOverFieldShiftNegIso (K : DerivedCategory X.Modules) (n i : ℤ) :
    Stacks.Duality.derivedCohomologyOverField f (K⟦n⟧) (-i) ≅
      Stacks.Duality.derivedCohomologyOverField f K (n - i) :=
  (Stacks.Duality.derivedCohomologyShiftIso f (K⟦n⟧) (-i)).symm ≪≫
    (derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
        ((shiftFunctorAdd' (DerivedCategory X.Modules) n (-i) (n - i) (by omega)).app K).symm ≪≫
    Stacks.Duality.derivedCohomologyShiftIso f K (n - i)

open Stacks.Duality.LocallyFreeTwist in
/-- **Duality for a finite locally free module on a smooth proper scheme.** If `X` is proper and
smooth of relative dimension `n` over `k` and `ℱ` is finite locally free, then for every `i : ℤ`
there is a `k`-linear isomorphism `H^i(X, ℱ)^∨ ≅ H^{n-i}(X, ω_X ⊗ ℱ^∨)` with
`ω_X = ⋀^n Ω_{X/k}`. -/
theorem nonempty_dual_linearEquiv_exteriorPower_tensor_dual [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] (F : Stacks.Duality.LocallyFreeTwist.Mod X)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (i : ℤ) :
    Nonempty (Module.Dual k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) i) ≃ₗ[k]
      Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (R X)).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
              (dual F))) (n - i)) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e⟩ :=
    (Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f n).1
  have L := dualityTwistLinearEquiv F (hE := hF) f (-i)
  rw [neg_neg] at L
  exact ⟨L ≪≫ₗ ((derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).mapIso
        ((GT F (hE := hF)).mapIso e ≪≫
          ((twist X (dual F)).mapDerivedCategorySingleFunctor (-(n : ℤ))).app _ ≪≫
          (((DerivedCategory.singleFunctors X.Modules).shiftIso (n : ℤ) (-(n : ℤ)) 0
            (by omega)).app _).symm) ≪≫
      derivedCohomologyOverFieldShiftNegIso f _ n i).toLinearEquiv⟩

/-- **Serre duality for a vector bundle on a smooth projective variety.** Let `X` be a smooth
projective variety of dimension `n` over `k`, `ω_X = ⋀^n Ω_{X/k}`, and `ℰ` a locally free sheaf of
finite rank on `X`. Then for every `i` there is an isomorphism of `k`-vector spaces
`H^i(X, ℰ^∨) ≅ H^{n-i}(X, ω_X ⊗ ℰ)^∨`. -/
@[mmp "lem_mmp_foundation_smooth_projective_serre_duality"]
theorem nonempty_linearEquiv_dual_exteriorPower_tensor [hX : IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) (n : ℕ) (hn : topologicalKrullDim X = n) (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (i : ℤ) :
    Nonempty (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E)) i ≃ₗ[k]
      Module.Dual k (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj E))
        (n - i))) := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hX.isProjective
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  haveI := smoothOfRelativeDimension_of_equidimensional k f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) n hn
  have hD : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
  obtain ⟨L⟩ := nonempty_dual_linearEquiv_exteriorPower_tensor_dual f n
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) (hF := hD) i
  haveI := Stacks.Chow.isIso_toDoubleDual_of_isFiniteLocallyFree E hE
  let L' := L ≪≫ₗ ((derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n - i)).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.toRingedSpace.sheaf).obj
              (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).mapIso
            (asIso (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual E)).symm))).toLinearEquiv
  haveI : (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _
  haveI := finiteDimensional_derivedCohomologyOverField_single_of_isCoherent f
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E) i
  exact ⟨Module.evalEquiv k _ ≪≫ₗ L'.symm.dualMap⟩

/-- **Kodaira-type vanishing is symmetric under Serre duality** (Kollár--Mori, Remark 2.66). Let
`X` be a smooth projective variety of dimension `n` over `k` and `L` a line bundle on `X`. Then
`H^i(X, L^{-1}) = 0` if and only if `H^{n-i}(X, ω_X ⊗ L) = 0`, for every `i` (in particular for
`0 ≤ i ≤ n`), where `ω_X = ⋀^n Ω_{X/k}`. -/
@[mmp "lem_km2c_serre_duality_vanishing_equiv"]
theorem subsingleton_dual_iff_subsingleton_exteriorPower_tensor [IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) (n : ℕ) (hn : topologicalKrullDim X = n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (i : ℤ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L)) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj L))
        (n - i)) := by
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  obtain ⟨e⟩ := nonempty_linearEquiv_dual_exteriorPower_tensor f hsm n hn L (hE := hL) i
  rw [e.toEquiv.subsingleton_congr]
  exact Module.subsingleton_dual_iff k

end MMP.Mori
