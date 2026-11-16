module

public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule

/-!
# Sections of a vector bundle twisted by a large negative power of an ample line bundle

Let `X` be a smooth projective variety of dimension `n ≥ 1` over a field `k`, `ℰ` a locally free
`𝒪_X`-module of finite rank and `L` an ample invertible `𝒪_X`-module. Then
`H⁰(X, ℰ ⊗ L^{⊗ -m}) = 0` for all `m ≫ 0`.

By Serre duality `H⁰(X, ℰ ⊗ L^{⊗ -m})^∨ ≅ Hⁿ(X, ω_X ⊗ (ℰ ⊗ L^{⊗ -m})^∨)`, and
`ω_X ⊗ (ℰ ⊗ L^{⊗ -m})^∨ ≅ (ω_X ⊗ ℰ^∨) ⊗ L^{⊗ m}`. Since `n > 0`, Serre vanishing for the
coherent sheaf `ω_X ⊗ ℰ^∨` and the ample `L` kills the right-hand side for `m ≫ 0`.

## Main results

* `MMP.Mori.exists_subsingleton_sections_tensor_tensorPowModule_neg`: for `ℰ` locally free of
  finite rank and `L` ample on a smooth projective variety of positive dimension,
  `Γ(X, ℰ ⊗ L^{⊗ -m}) = 0` for all large `m`.

## Implementation notes

* `L^{⊗ j}` for `j : ℤ` is `Stacks.Ample.tensorPowModule`, and `⊗` is the sheaf tensor product
  `Stacks.SheafOfModules.Tensor.sheafTensor`. The global sections are `Γ(ℱ, ⊤)`.
* The hypothesis `0 < n` cannot be dropped: on a point every module has nonzero sections.

## References

* [R. Hartshorne, *Algebraic Geometry*][Hartshorne1977], Theorem III.7.6 and
  Proposition III.5.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

section Helpers

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-- `(A ⊗ B)^∨ ≅ B^∨ ⊗ A^∨` for finite locally free `A` and `B`: both are right duals of
`A ⊗ B`. -/
private def dualSheafTensorIso {X : Scheme.{u}} (A B : Stacks.Duality.LocallyFreeTwist.Mod X)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (hB : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} B) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf B)).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf A) :=
  @rightDualIso (Stacks.Duality.LocallyFreeTwist.Mod X) _ _ _ _ _
    (@Stacks.Duality.LocallyFreeTwist.pairing X (A ⊗ B)
      (Stacks.Chow.isFiniteLocallyFree_tensor hA hB))
    (@ExactPairing.tensor _ _ _ A B (Stacks.Duality.LocallyFreeTwist.dual A)
      (Stacks.Duality.LocallyFreeTwist.dual B)
      (@Stacks.Duality.LocallyFreeTwist.pairing X A hA)
      (@Stacks.Duality.LocallyFreeTwist.pairing X B hB))

/-- The inverse associator `A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C` of the sheaf tensor product. -/
private def sheafTensorAssocIso {X : Scheme.{u}} (A B C : Stacks.Duality.LocallyFreeTwist.Mod X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj A).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          B).obj C) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          A).obj B)).obj C :=
  (α_ A B C).symm

end Helpers

/-- **Sections of a vector bundle twisted by a large negative power of an ample line bundle
vanish.** Let `X` be a smooth projective variety of dimension `n ≥ 1` over a field `k`, `ℰ` a
locally free `𝒪_X`-module of finite rank and `L` an ample invertible `𝒪_X`-module. Then
`Γ(X, ℰ ⊗ L^{⊗ -m}) = 0` for all `m ≫ 0`. -/
public theorem exists_subsingleton_sections_tensor_tensorPowModule_neg {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    (n : ℕ) (hn : topologicalKrullDim X = n) (hn0 : 0 < n) (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Subsingleton Γ(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.toRingedSpace.sheaf).obj E).obj (Stacks.Ample.tensorPowModule X L (-(m : ℤ))), ⊤) := by
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  haveI : IsProper f := isProper_of_isProjectiveMorphism f ‹IsProjectiveVariety k f›.isProjective
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  haveI := smoothOfRelativeDimension_of_equidimensional k f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) n hn
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf
  let Ωn := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n
  let D := Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E
  have hD : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} D :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
  haveI := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  have hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Ωn :=
    Scheme.Modules.isFiniteLocallyFree_exteriorPower _ n inferInstance
  have hcoh : _root_.SheafOfModules.IsCoherent ((T.obj Ωn).obj D) :=
    @Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X _ _
      (Stacks.Chow.isFiniteLocallyFree_tensor hΩ hD)
  obtain ⟨m₀, hm₀⟩ :=
    @Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist X k _ _ f _
      ((T.obj Ωn).obj D) L hcoh _ hL
  refine ⟨m₀, fun m hm => ?_⟩
  let M := Stacks.Ample.tensorPowModule X L (-(m : ℤ))
  haveI hMi : Stacks.Ample.IsInvertibleModule X M :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L _
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
  have hF := Stacks.Chow.isFiniteLocallyFree_tensor hE hM
  obtain ⟨e⟩ := nonempty_dual_linearEquiv_exteriorPower_tensor_dual f n ((T.obj E).obj M)
    (hF := hF) 0
  -- `M^∨ ≅ L^{⊗ m}`
  let eM : Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf M ≅
      Stacks.Ample.tensorPowModule X L (m : ℤ) :=
    (Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _
      (Stacks.Ample.tensorPowModuleAddIso X L (-(m : ℤ)) (-(-(m : ℤ))) ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (add_neg_cancel _) ≪≫
        Stacks.Ample.tensorPowModuleZeroIso X L)).symm ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (neg_neg _)
  let eT : (T.obj Ωn).obj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((T.obj E).obj M)) ≅
      (T.obj ((T.obj Ωn).obj D)).obj (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
    (T.obj Ωn).mapIso (dualSheafTensorIso E M hE hM ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.toRingedSpace.sheaf).app _).app _ ≪≫
      (T.obj D).mapIso eM) ≪≫ sheafTensorAssocIso Ωn D _
  have hz := hm₀ m n hm hn0
  haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ n
      ((T.obj ((T.obj Ωn).obj D)).obj (Stacks.Ample.tensorPowModule X L (m : ℤ)))) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  haveI : Subsingleton (cohomologyOverField k f
      ((T.obj ((T.obj Ωn).obj D)).obj (Stacks.Ample.tensorPowModule X L (m : ℤ))) n) :=
    (cohomologyOverFieldAddEquivHgroup k f _ n).toEquiv.subsingleton
  have h1 : Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((T.obj ((T.obj Ωn).obj D)).obj (Stacks.Ample.tensorPowModule X L (m : ℤ)))) n) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
      n).toEquiv.symm.subsingleton
  have h2 : Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((T.obj Ωn).obj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((T.obj E).obj M)))) ((n : ℤ) - 0)) := by
    rw [sub_zero]
    exact @Equiv.subsingleton _ _ ((derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso eT)).toLinearEquiv.toEquiv h1
  haveI : Subsingleton (Module.Dual k (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj ((T.obj E).obj M)) 0)) :=
    @Equiv.subsingleton _ _ e.toEquiv h2
  haveI := (Module.subsingleton_dual_iff k).1 this
  haveI : Subsingleton (cohomologyOverField k f ((T.obj E).obj M) 0) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
      0).toEquiv.subsingleton
  exact (cohomologyOverFieldZeroEquivSections k f ((T.obj E).obj M)).symm.subsingleton

end MMP.Mori
