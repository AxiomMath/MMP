/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction

/-!
# Push-forwards of smooth blow-up sequences are smooth (Kollár 3.30.3)

Let `X` be smooth over a field `k`, `j : S ↪ X` a closed subscheme, `𝐁(S)` a smooth blow-up
sequence starting with `S` and `𝐁^X` a push-forward of `𝐁(S)` along `j`. Then `𝐁^X` is a smooth
blow-up sequence.

The morphisms `j_i : S_i → X_i` of the push-forward are those of the restriction `𝐁^X|_S`
(`MMP.Resolution.Kollar.restrict_eq_of_isPushforward`), hence closed immersions: `j_0 = j`, and
`j_{i+1}` is the canonical lift of `j_i` along `Z^X_i`, a closed immersion by
`MMP.Resolution.Bridges.isClosedImmersion_canonicalLift` (as in
`MMP.Resolution.Kollar.isClosedImmersion_restrictHom_truncate`). A closed immersion maps a closed
subscheme isomorphically onto its scheme-theoretic image, so `Z^X_i = (j_i)_*Z^S_i ≅ Z^S_i` is
smooth over `k`. Inductively `X_i` is smooth over `k`: if it is, `π_i` is a smooth blow-up and
`X_{i+1} = B_{Z^X_i}X_i` is smooth
(`MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup`).

## Main results

* `MMP.Mori.isSmoothScheme_of_smooth`, `MMP.Mori.IsSmoothScheme.smooth`: a morphism is smooth
  exactly when it is smooth at every point.
* `MMP.Resolution.isSmoothScheme_map_subschemeι_comp`: the scheme-theoretic image of a smooth
  closed subscheme under a closed immersion is smooth.
* `MMP.Resolution.ClosedBlowupSequence.IsPushforward.isSmooth`: a push-forward along a closed
  immersion into a smooth scheme of a smooth blow-up sequence is smooth.
* `MMP.Resolution.ClosedBlowupSequence.isSmooth_of_isPushforward`: Kollár 3.30.3, for the
  inclusion of a closed subscheme.

## Implementation notes

The source does not assume `X` smooth; without it the statement is false (`X = (xy = z²)`, `S`
the origin, `𝐁(S)` the blow-up of `S` along itself: the push-forward blows up the singular `X`
at the origin). The induction is made for an arbitrary closed immersion `j : S → X`, so that it
applies to the closed immersions `j_i`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.29, 3.30]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- A smooth morphism is smooth at every point: its smooth locus is all of the source. -/
theorem _root_.MMP.Mori.isSmoothScheme_of_smooth {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : Smooth f) : MMP.Mori.IsSmoothScheme f :=
  eq_top_iff.2 (MMP.Mori.le_smoothLocus f inferInstance)

/-- A morphism smooth at every point is smooth. -/
theorem _root_.MMP.Mori.IsSmoothScheme.smooth {X Y : Scheme.{u}} {f : X ⟶ Y}
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

variable {k : Type u} [Field k]

/-- **The image of a smooth closed subscheme under a closed immersion is smooth.** Let
`j : S → X` be a closed immersion, `sX : X → Y` a morphism and `Z ⊆ S` a closed subscheme smooth
over `Y`. Then its scheme-theoretic image `j_*Z ⊆ X` is smooth over `Y`: it is isomorphic to `Z`
over `X`. -/
theorem isSmoothScheme_map_subschemeι_comp {S X Y : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] (sX : X ⟶ Y) (Z : S.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ j ≫ sX)) :
    MMP.Mori.IsSmoothScheme ((Z.map j).subschemeι ≫ sX) := by
  set f := Z.subschemeι ≫ j
  change MMP.Mori.IsSmoothScheme (f.imageι ≫ sX)
  have hf : f.imageι = inv f.toImage ≫ f := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  have : Smooth (f ≫ sX) := by
    simpa only [f, Category.assoc] using hZ.smooth
  apply MMP.Mori.isSmoothScheme_of_smooth
  rw [hf, Category.assoc]
  infer_instance

namespace ClosedBlowupSequence

/-- **Push-forwards of smooth blow-up sequences along closed immersions into smooth schemes are
smooth.** Let `j : S → X` be a closed immersion, `X` smooth over `k`, `𝐁(S)` a smooth blow-up
sequence starting with `S` (over `k` by `S → X → Spec k`) and `𝐁^X` a push-forward of `𝐁(S)`
along `j`. Then `𝐁^X` is a smooth blow-up sequence. -/
theorem IsPushforward.isSmooth {S X : Scheme.{u}} {j : S ⟶ X} [IsClosedImmersion j]
    {sX : X ⟶ Spec (.of k)} {BS : ClosedBlowupSequence S} {BX : ClosedBlowupSequence X}
    (hP : IsPushforward j BS BX) (hX : MMP.Mori.IsSmoothScheme sX)
    (hS : BS.IsSmooth (j ≫ sX)) : BX.IsSmooth sX := by
  induction BS generalizing X with
  | nil S =>
    cases BX with
    | nil => trivial
    | cons ZX BX => exact hP.elim
  | cons ZS BS ih =>
    cases BX with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨hc, hm, hP⟩ := hP
      subst hc
      obtain ⟨-, hZS, hBS⟩ := hS
      rw [eqToHom_refl, Category.id_comp] at hP
      have hZX : MMP.Mori.IsSmoothScheme (ZX.subschemeι ≫ sX) := by
        rw [hm]
        exact isSmoothScheme_map_subschemeι_comp j sX _ hZS
      refine ⟨hX, hZX, ?_⟩
      have := Bridges.isClosedImmersion_canonicalLift j ZX
      refine ih (j := canonicalLift j ZX) hP ?_ ?_
      · exact MMP.Mori.isSmoothScheme_of_smooth
          (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX ZX ⟨hX, hZX⟩).1
      · rwa [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc]

/-- **Kollár 3.30.3, corrected.** Let `X` be a scheme smooth over a field `k`, `S ⊆ X` a closed
subscheme, `𝐁(S)` a smooth blow-up sequence starting with `S` and `𝐁^X` a push-forward of
`𝐁(S)` along the inclusion `j : S ↪ X`. Then `𝐁^X` is a smooth blow-up sequence. -/
@[mmp "lem_kr3b_pushforward_smooth"]
theorem isSmooth_of_isPushforward {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) (S : X.IdealSheafData)
    {BS : ClosedBlowupSequence S.subscheme} {BX : ClosedBlowupSequence X}
    (hS : BS.IsSmooth (S.subschemeι ≫ sX)) (hP : IsPushforward S.subschemeι BS BX) :
    BX.IsSmooth sX :=
  hP.isSmooth hX hS

end ClosedBlowupSequence

end MMP.Resolution
