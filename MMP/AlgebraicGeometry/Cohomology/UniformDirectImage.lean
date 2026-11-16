module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeAcyclic

/-!
# Uniform Serre vanishing and locally free direct images for a finite list of sheaves

Let `f : X ⟶ S` be a proper morphism to a Noetherian scheme, `L` an invertible module on `X`
which is relatively ample over `S`, and `F₁, …, F_r` finitely many coherent `𝒪_X`-modules whose
twists `F_j ⊗ L^n` are flat over `S`. Then there is one exponent `n₀` such that for all `n ≥ n₀`
and all `j`:

* `R^i f_* (F_j ⊗ L^n) = 0` for `i > 0` (Serre vanishing, `Tag 02O1`, one bound for the finite
  list: the maximum of the bounds of the members);
* `f_* (F_j ⊗ L^n)` is finite locally free (`Tag 0D4E`);
* the formation of `f_* (F_j ⊗ L^n)` commutes with every base change `S' ⟶ S`: the canonical
  comparison `g^* f_* ⟶ f'_* g'^*` is an isomorphism for every cartesian square.

## Main results

* `MMP.Chow.exists_forall_isZero_higherDirectImage_and_isFiniteLocallyFree_and_isIso_baseChange`.
* `MMP.Chow.exists_forall_subsingleton_rightDerived_moduleGlobalSections`: the absolute form over
  `Spec R`.

## Implementation notes

The vanishing is `exists_isZero_rightDerivedPlus_pushforward_tensorPowModule` (in the namespace
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity`) applied to each member of the finite list; the
other two conclusions are
`isFiniteLocallyFree_pushforward_and_isIso_baseChange_of_isZero_higherDirectImage` (in the
namespace `Stacks.AlgebraicGeometry.VanishingHigherDirectImages`). Flatness is assumed for the
twists themselves (it holds, for instance, when `f` is flat and `F_j` is finite locally free).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample
open Stacks.RelativeVeryAmple (tensorModules)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace MMP.Chow

/-- **Uniform Serre vanishing, local freeness and base change for a finite list of sheaves.** -/
public theorem exists_forall_isZero_higherDirectImage_and_isFiniteLocallyFree_and_isIso_baseChange
    {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsNoetherian S] [IsProper f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    {ι : Type*} [Finite ι] (F : ι → X.Modules) [∀ j, (F j).IsCoherent]
    (hflat : ∀ (j : ι) (n : ℕ), IsFlatOver f.toLRSHom.toShHom
      (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ι,
      (∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj
          (tensorModules X (F j) (tensorPowModule X L (n : ℤ))))) ∧
      SheafOfModules.IsFiniteLocallyFree (R := S.ringCatSheaf)
        ((Scheme.Modules.pushforward f).obj
          (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
          (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) := by
  classical
  have hX : LocallyOfFinitePresentation f := inferInstance
  have key : ∀ j : ι, ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj
        (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) := fun j =>
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
      f (F j) L hL
  choose k hk using key
  have _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup k, fun n hn j => ?_⟩
  have hvan : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj
      (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) := by
    intro i hi
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg hi.le⟩
    exact hk j n p ((Finset.le_sup (Finset.mem_univ j)).trans hn) (by exact_mod_cast hi)
  have hfp : (tensorModules X (F j) (tensorPowModule X L (n : ℤ))).IsFinitePresentation := by
    have : (tensorModules X (F j) (tensorPowModule X L (n : ℤ))).IsCoherent :=
      haveI : IsInvertibleModule X (tensorPowModule X L (n : ℤ)) :=
        isInvertibleModule_tensorPowModule X L (n : ℤ)
      AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X (F j)
        (tensorPowModule X L (n : ℤ))
    exact Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_of_isCoherent' _
  have hfpm : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hsupp : letI : LocallyOfFinitePresentation f := hfpm.locallyOfFinitePresentation
      ∃ Z : TopologicalSpace.Closeds X, IsProperOver f Z ∧
        SheafOfModules.supp (tensorModules X (F j) (tensorPowModule X L (n : ℤ))) ⊆ (Z : Set X) :=
    ⟨⊤, show IsProper _ by infer_instance, fun _ _ => trivial⟩
  obtain ⟨h1, h2⟩ :=
    Stacks.AlgebraicGeometry.VanishingHigherDirectImages.isFiniteLocallyFree_pushforward_and_isIso_baseChange_of_isZero_higherDirectImage
      f hfpm _ (hflat j n) hsupp hvan
  exact ⟨hvan, h1, fun g f' g' hsq => h2 g f' g' hsq⟩

/-- **Uniform Serre vanishing of global cohomology over an affine Noetherian base, in the form
the cohomology-and-base-change theorem consumes.** For `f : X ⟶ Spec R` proper with `R`
Noetherian, `L` ample and finitely many coherent `F_j`, there is `n₀` with
`H^p(X, F_j ⊗ L^n) = 0` for all `p > 0`, `n ≥ n₀` and all `j`, stated as the vanishing of the
derived functors of `moduleGlobalSections`. This is the hypothesis `hvan` of
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing`, which
then gives (for flat twists) vanishing of the higher cohomology of every base change of the
fibre and the base change isomorphism `Γ(X, F_j ⊗ L^n) ⊗_R B ≅ Γ(X', F_j' ⊗ L'^n)`. -/
public theorem exists_forall_subsingleton_rightDerived_moduleGlobalSections
    {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Spec (.of R))
    [IsProper f] (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    {ι : Type*} [Finite ι] (F : ι → X.Modules) [∀ j, (F j).IsCoherent] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ j : ι, ∀ p : ℕ, 0 < p → Subsingleton
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
        (tensorModules X (F j) (tensorPowModule X L (n : ℤ)))) := by
  classical
  have key : ∀ j : ι, ∃ n₀ : ℕ, ∀ d p : ℕ, n₀ ≤ d → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (tensorModules X (F j) (tensorPowModule X L (d : ℤ)))) :=
    fun j => Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      f (F j) L hL
  choose k hk using key
  have _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup k, fun n hn j p hp => ?_⟩
  have h := hk j n p ((Finset.le_sup (Finset.mem_univ j)).trans hn) hp
  exact ModuleCat.subsingleton_of_isZero
    ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ p _).2 h)

end MMP.Chow

end
