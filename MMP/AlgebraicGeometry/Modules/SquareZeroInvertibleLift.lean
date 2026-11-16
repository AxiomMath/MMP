module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardRestrictionPullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback

/-!
# Lifting invertible sheaves over square-zero thickenings

For a closed immersion `i : X ⟶ Y` with square-zero ideal sheaf `J` and `H²(Y, J) = 0`, every
invertible sheaf on `X` is the pullback of an invertible sheaf on `Y`.

## Main results

* `MMP.Resolution.Bridges.exists_isInvertibleModule_pullback_iso_of_ker_sq_eq_bot`: lifting of
  invertible sheaves, from the exact sequence `Pic(Y) → Pic(X) → H²(Y, J)` of the thickening.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP.Resolution.Bridges

section LineBundleLifting

open Stacks.Thickenings

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] hasExtAbelianSheaf

/-- **Lifting an invertible sheaf across a square-zero thickening.** Let `i : X ⟶ Y` be a closed
immersion whose ideal sheaf `J` (the kernel of `𝒪_Y ⟶ i_* 𝒪_X`) satisfies `J ^ 2 = 0`, and
suppose `H²(Y, J) = 0` (cohomology of `J` as a sheaf of abelian groups on `Y`). Then every
invertible sheaf `L` on `X` is isomorphic to the pullback `i^* M` of an invertible sheaf `M` on
`Y`. -/
@[mmp "thm_mmp_square_zero_line_bundle_lifting"]
theorem exists_isInvertibleModule_pullback_iso_of_ker_sq_eq_bot {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (h2 : ∀ x : CategoryTheory.Sheaf.H.{u} (idealAddSheaf i) 2, x = 0)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    ∃ (M : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y M),
      Nonempty ((Scheme.Modules.pullback i).obj M ≅ L) := by
  have hi : IsFirstOrderThickening i := ⟨inferInstance, hsq⟩
  have h2' : ∀ x : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 2, x = 0 := fun x =>
    (idealCohomologyEquiv i hi 2).injective ((h2 _).trans (_root_.map_zero _).symm)
  have hsurj := Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_of_forall_eq_zero
    i hi h2'
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  obtain ⟨m, hm⟩ := hsurj (X.picardClass L hL)
  set R := Stacks.Picard.picardRepresentative Y.toRingedSpace m
  have hRinv : Stacks.Ample.IsInvertibleModule Y R.obj :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ R.obj).mp R.property
  refine ⟨R.obj, hRinv, ?_⟩
  have hpb : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((Scheme.Modules.pullback i).obj R.obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of i.toLRSHom.toShHom _ R.property
  exact (X.picardClass_eq_iff _ L hpb hL).1 hm

end LineBundleLifting

end MMP.Resolution.Bridges
