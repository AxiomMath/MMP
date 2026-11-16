/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# High powers of an ample line bundle over a Noetherian affine base are very ample

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` projective and `L` an ample invertible
`𝒪_X`-module. Then there is `N₀ ≥ 1` such that for every `N ≥ N₀` the tensor power `L ^⊗ N` is
very ample relative to `f`, and is the pull-back of `𝒪(1)` along a closed immersion
`X ⟶ ℙ^M_A` over `Spec A`: the pull-backs of the homogeneous coordinates are global sections of
`L ^⊗ N`, and they define the closed embedding.

## Main results

* `MMP.Resolution.eventually_isRelativelyVeryAmple_and_isClosedImmersion_of_isAmple`: both
  conclusions, for all sufficiently large `N`.
* `MMP.Resolution.isClosedImmersion_of_isImmersion_of_isProper`: a proper immersion is a closed
  immersion.

## Implementation notes

The affine-base theorem `Stacks.AmpleRelativeFiniteType.tfae_six` (Stacks Tag 01VT) gives, for
all large `N`, both relative very ampleness of `L ^⊗ N` and an immersion `j_N : X ⟶ ℙ^M_A` over
`Spec A` with `j_N^* 𝒪(1) ≅ L ^⊗ N`. A projective morphism is proper and `ℙ^M_A` is separated
over `Spec A`, so `j_N` is proper; a proper immersion has closed image, hence is a closed
immersion. The Noetherian hypothesis on `A` is the source's and is not needed by the argument.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace MMP.Resolution

/-- A proper immersion of schemes is a closed immersion: its image is closed. -/
theorem isClosedImmersion_of_isImmersion_of_isProper {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsImmersion i] [IsProper i] : IsClosedImmersion i :=
  { isClosedEmbedding := ⟨i.isEmbedding, i.isClosedMap.isClosed_range⟩ }

/-- **High powers of an ample line bundle over a Noetherian affine base are very ample.** Let `A`
be a Noetherian ring, `f : X ⟶ Spec A` projective and `L` an ample invertible `𝒪_X`-module. Then
for every sufficiently large `N` the power `L ^⊗ N` is very ample relative to `f`, and there is a
closed immersion `i : X ⟶ ℙ^M_A` over `Spec A` with `i^* 𝒪(1) ≅ L ^⊗ N`, i.e. given by the global
sections of `L ^⊗ N` pulled back from the homogeneous coordinates. -/
@[mmp "lem_mmp_foundation_noetherian_affine_base_ample_power_very_ample"]
theorem eventually_isRelativelyVeryAmple_and_isClosedImmersion_of_isAmple
    {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec A)
    (hf : IsProjectiveMorphism f) (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (N : ℤ)) ∧
      ∃ (M : ℕ) (i : X ⟶ projectiveSpaceOver M (Spec A)),
        IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver M (Spec A) ↘ Spec A) = f ∧
        Nonempty (tensorPowModule X L (N : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf M (Spec A))) := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hf
  have hT := Stacks.AmpleRelativeFiniteType.tfae_six f L
  obtain ⟨a, ha, hva⟩ := (hT.out 1 4).mp hL
  obtain ⟨b, -, himm⟩ := (hT.out 1 6).mp hL
  refine ⟨max a b, le_trans ha (le_max_left _ _), fun N hN => ⟨hva N (le_of_max_le_left hN), ?_⟩⟩
  obtain ⟨M, i, hi, hover, he⟩ := himm N (le_of_max_le_right hN)
  have hover' : i ≫ (projectiveSpaceOver M (Spec A) ↘ Spec A) = f := hover
  have := hi
  have : IsProper (i ≫ (projectiveSpaceOver M (Spec A) ↘ Spec A)) := by
    rw [hover']; infer_instance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver M (Spec A) ↘ Spec A)
  exact ⟨M, i, isClosedImmersion_of_isImmersion_of_isProper i, hover', he⟩

end MMP.Resolution

end
