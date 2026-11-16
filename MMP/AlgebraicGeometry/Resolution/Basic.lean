module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic

/-!
# Resolutions and strong resolutions of varieties (Kollár, *Resolution*, 3.2, 3.3, 3.19)

This file states the notions opening Kollár's third chapter.

* The *singular locus* `Sing X` of a scheme `X` of finite type over `k` is the complement of the
  union `X°` of the opens smooth over `k`, with its reduced closed subscheme structure.
* A *resolution* of a variety `X` over `k` is a projective birational morphism `f : X' ⟶ X` from
  a smooth variety `X'`.
* A *strong resolution* is a resolution which is an isomorphism over the smooth locus
  `X^ns = X ∖ Sing X` and such that `f⁻¹(Sing X)_red` is a simple normal crossing divisor.
* A blow-up `π_{Z,X} : B_Z X ⟶ X`, together with its center `Z`, is a *smooth blow-up* if `X`
  and `Z` are both smooth over `k`.

## Main definitions

* `MMP.Resolution.reducedSingularLocus`: `Sing X` with its reduced closed subscheme structure.
* `MMP.Resolution.IsResolutionOfVariety`: resolutions of a variety.
* `MMP.Resolution.IsStrongResolution`: strong resolutions.
* `MMP.Resolution.IsSmoothBlowup`: smooth blow-ups.

## Implementation notes

Several of the notions are already in the library and are not restated:

* the singular locus, as a closed set, is `MMP.Mori.singularLocus` (registered below), the
  complement of `MMP.Mori.smoothLocus`, the union of the opens smooth over the base; its
  reduced structure is Mathlib's `Scheme.IdealSheafData.vanishingIdeal`;
* the exceptional divisor `F = π⁻¹(Z)` of a blow-up, cut out by `I_Z · 𝒪_{B_Z X}`, is
  StacksDraft's `Stacks.Blowup.exceptionalIdeal` (the inverse image `Scheme.IdealSheafData.comap`
  of `I_Z` under `Stacks.Blowup.blowUpToBase`) and `Stacks.Blowup.exceptionalDivisor`;
* simple normal crossing divisors (Kollár Def. 1.44) are `MMP.Resolution.IsSNCSubscheme`.

A *variety* is `AlgebraicGeometry.IsVariety`: integral, separated and of finite type over `k`.
Smoothness of a `k`-scheme is `MMP.Mori.IsSmoothScheme`, its smooth locus being everything.

The resolution of Kollár 3.2 differs from `MMP.Mori.IsSmoothResolution` (KM 0.4) by asking
`f` projective rather than proper and `X`, `X'` to be varieties, and from
`MMP.Resolution.IsProjectiveSurfaceResolution` by not fixing the dimension two.

Hypotheses of the source that only restrict the domain are dropped: separatedness and finite type
of `X` for the singular locus, and finite type of `X` for smooth blow-ups (smoothness of `X` and
`Z` over `k` is still asked). A smooth blow-up is a property of the center `Z ⊆ X`, the blow-up
itself being determined by it.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.2, 3.3, 3.19]
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

/-! ### Notions recorded from the library -/

attribute [mmp "def_kr3a_singular_locus"] MMP.Mori.singularLocus

namespace MMP.Resolution

variable {k : Type u} [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-! ### The singular locus -/

/-- The *singular locus* `Sing X` of a `k`-scheme `X` (structure morphism `s_X`), the complement
of the union of the opens of `X` smooth over `k`, with its reduced closed subscheme structure. -/
@[mmp "def_kr3a_singular_locus"]
def reducedSingularLocus : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (singularLocus sX)

/-- The singular locus is a closed subset of `X`. -/
@[mmp "def_kr3a_singular_locus"]
theorem isClosed_singularLocus : IsClosed (singularLocus sX : Set X) :=
  (singularLocus sX).isClosed

/-- The reduced closed subscheme `Sing X` has the singular locus as its underlying set. -/
@[simp, mmp "def_kr3a_singular_locus"]
theorem support_reducedSingularLocus : (reducedSingularLocus sX).support = singularLocus sX := by
  unfold reducedSingularLocus
  exact Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-! ### Resolutions -/

/-- A *resolution* of a variety `X` over `k` (Kollár 3.2) is a projective birational morphism
`f : X' ⟶ X` from a smooth variety `X'`, the structure morphism of `X'` being `f ≫ s_X`.
Projective is meant in the sense of EGA ([Stacks, Tag 01W8], `AlgebraicGeometry.IsProjective`):
a closed immersion into the projective bundle of a finite-type quasi-coherent module. This is the
notion stable under composition, which a composite of blow-ups satisfies. -/
@[mmp "def_kr3a_resolution"]
structure IsResolutionOfVariety (f : X' ⟶ X) : Prop where
  /-- `X` is a variety over `k`. -/
  isVariety : AlgebraicGeometry.IsVariety k sX
  /-- `X'` is a variety over `k`. -/
  isVariety_source : AlgebraicGeometry.IsVariety k (f ≫ sX)
  /-- `f` is projective. -/
  isProjective : AlgebraicGeometry.IsProjective f
  /-- `f` is birational. -/
  isBirationalMorphism : IsBirationalMorphism f
  /-- `X'` is smooth over `k`. -/
  isSmoothScheme : IsSmoothScheme (f ≫ sX)

/-- A *strong resolution* of a variety `X` over `k` (Kollár 3.3) is a resolution `f : X' ⟶ X`
which restricts to an isomorphism `f⁻¹(X^ns) ⟶ X^ns` over the smooth locus `X^ns` and such that
the reduced closed subscheme `f⁻¹(Sing X)_red` of `X'` is a simple normal crossing divisor (the
empty divisor if `X` is smooth). -/
@[mmp "def_kr3a_strong_resolution"]
structure IsStrongResolution (f : X' ⟶ X) : Prop extends IsResolutionOfVariety sX f where
  /-- `f` is an isomorphism over the smooth locus `X^ns`. -/
  isIso_restrict_smoothLocus : IsIso (f ∣_ smoothLocus sX)
  /-- `f⁻¹(Sing X)_red` is a simple normal crossing divisor. -/
  isSNCSubscheme : IsSNCSubscheme
    (Scheme.IdealSheafData.vanishingIdeal ((singularLocus sX).preimage f.continuous))

/-- The singular locus of a smooth morphism is empty. -/
theorem singularLocus_eq_bot_of_isSmoothScheme {Y : Scheme.{u}} {g : X ⟶ Y}
    (h : IsSmoothScheme g) : singularLocus g = ⊥ := by
  unfold MMP.Mori.singularLocus
  rw [show smoothLocus g = ⊤ from h]
  exact Closeds.ext (by simp)

/-- If `X` is smooth over `k`, the reduced closed subscheme `f⁻¹(Sing X)_red` of `X'` is empty:
its ideal is the unit ideal, the empty divisor. -/
@[mmp "def_kr3a_strong_resolution"]
theorem vanishingIdeal_preimage_singularLocus_eq_top_of_isSmoothScheme (f : X' ⟶ X)
    (h : IsSmoothScheme sX) :
    Scheme.IdealSheafData.vanishingIdeal ((singularLocus sX).preimage f.continuous) = ⊤ := by
  rw [singularLocus_eq_bot_of_isSmoothScheme h,
    show (⊥ : Closeds X).preimage f.continuous = ⊥ from Closeds.ext (by simp)]
  exact Scheme.IdealSheafData.vanishingIdeal_bot

/-! ### Smooth blow-ups -/

/-- A closed subscheme `Z` (ideal `I`) of a `k`-scheme `X` is the center of a *smooth blow-up*
`π_{Z,X} : B_Z X ⟶ X` if `X` and `Z` are both smooth over `k`. -/
@[mmp "def_kr3a_smooth_blowup"]
def IsSmoothBlowup (I : X.IdealSheafData) : Prop :=
  IsSmoothScheme sX ∧ IsSmoothScheme (I.subschemeι ≫ sX)

end MMP.Resolution
