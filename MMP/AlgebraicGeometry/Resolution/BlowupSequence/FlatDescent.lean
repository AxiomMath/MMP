module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafZariskiGluing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# Blow-up sequences: faithfully flat descent and restriction of push-forwards (Kollár 3.30)

Let `h : Y → X` be a flat surjective morphism. Inverse image along `h` is injective on ideal
sheaves: at a point `y` the stalk map `𝒪_{X,h(y)} → 𝒪_{Y,y}` is a flat local homomorphism, hence
faithfully flat, so an ideal of `𝒪_{X,h(y)}` is the contraction of its extension, and every point
of `X` is of the form `h(y)`. Consequently a blow-up sequence starting with `X` is determined by
its pull-back along `h`: the first centres agree, the canonical lift `B_{h⁻¹Z}Y → B_ZX` is again
flat and surjective, being a base change of `h`, and one inducts on the sequence.

The companion statement for the Zariski topology is gluing: ideal sheaves on the members of a
jointly surjective family of open immersions into `X` that agree on the overlaps glue to an ideal
sheaf on `X` (`AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_isOpenImmersion`), and
an ideal sheaf on `X` is determined by its pull-backs to the members
(`AlgebraicGeometry.Scheme.IdealSheafData.ext_of_comap_eq_of_isOpenImmersion`).

Let `j : S → X` be a morphism and `𝐁^X` a push-forward of a blow-up sequence `𝐁(S)` along `j`.
Then the pull-back `j^*𝐁^X` is `𝐁(S)`; for a closed subscheme `S ⊆ X` this says that the
restriction `𝐁^X|_S` is `𝐁(S)`.

## Main statements

* `MMP.Resolution.Kollar.eq_of_comap_eq_of_flat_of_surjective`: inverse image along a flat
  surjective morphism is injective on ideal sheaves.
* `MMP.Resolution.Kollar.eq_of_pullback_eq_of_flat_of_surjective`: a blow-up sequence is
  determined by its pull-back along a flat surjective morphism (Kollár 3.30.1).
* `MMP.Resolution.Kollar.pullback_eq_of_isPushforward`: the pull-back of a push-forward along
  `j` is the original sequence.
* `MMP.Resolution.Kollar.restrict_eq_of_isPushforward`: the restriction of a push-forward
  `𝐁^X` of `𝐁(S)` to `S` is `𝐁(S)` (Kollár 3.30.3, 3.34).

## Implementation notes

Local noetherianity, assumed in the source, is not used and is dropped. The push-forward
statement holds for an arbitrary morphism `j`, the hypothesis `j⁻¹Z^X_i = Z^S_i` being part of
`MMP.Resolution.ClosedBlowupSequence.IsPushforward`; this generality is what makes the induction
on the sequence go through.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.30, 3.34]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

universe u

namespace MMP.Resolution.Kollar

/-- Inverse image along a flat surjective morphism `h : Y → X` reflects inclusions of ideal
sheaves. -/
theorem le_of_comap_le_of_flat_of_surjective {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [Surjective h] {I J : X.IdealSheafData} (hIJ : I.comap h ≤ J.comap h) : I ≤ J := by
  refine IdealSheafData.le_of_stalk_le I J fun x => ?_
  obtain ⟨y, rfl⟩ := h.surjective x
  have hy : IdealSheafData.stalk (I.comap h) y ≤ IdealSheafData.stalk (J.comap h) y :=
    iSup₂_mono fun U _ => Ideal.map_mono (hIJ U)
  rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_comap] at hy
  algebraize [(h.stalkMap y).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap h y) (h.toLRSHom.prop y)
  have hc := Ideal.comap_mono (f := algebraMap (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) hy
  have e := fun K : Ideal (X.presheaf.stalk (h y)) =>
    Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) K
  rwa [← RingHom.algebraMap_toAlgebra (h.stalkMap y).hom, e, e] at hc

/-- **Faithfully flat descent of ideal sheaves.** Inverse image along a flat surjective morphism
is injective on ideal sheaves. -/
theorem eq_of_comap_eq_of_flat_of_surjective {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [Surjective h] {I J : X.IdealSheafData} (hIJ : I.comap h = J.comap h) : I = J :=
  le_antisymm (le_of_comap_le_of_flat_of_surjective h hIJ.le)
    (le_of_comap_le_of_flat_of_surjective h hIJ.ge)

/-- The canonical lift of a flat surjective morphism is surjective: it is a base change of it
by `MMP.Resolution.Kollar.isPullback_canonicalLift_of_flat`. -/
theorem surjective_canonicalLift {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] [Surjective h]
    (Z : X.IdealSheafData) : Surjective (canonicalLift h Z) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_canonicalLift_of_flat h Z) ‹_›

/-- **Kollár 3.30.1.** Let `h : Y → X` be flat and surjective (for instance a smooth surjection,
or `⊔ U_α → X` for an open cover) and `𝐁`, `𝐁'` blow-up sequences starting with `X`. If
`h^*𝐁 = h^*𝐁'`, then `𝐁 = 𝐁'`. -/
@[mmp "lem_kr3b_pullback_surjective_determines"]
theorem eq_of_pullback_eq_of_flat_of_surjective {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [Surjective h] {B B' : ClosedBlowupSequence X} (hB : B.pullback h = B'.pullback h) :
    B = B' := by
  induction B generalizing Y with
  | nil X =>
    cases B' with
    | nil => rfl
    | cons Z' B' => cases hB
  | cons Z B ih =>
    cases B' with
    | nil => cases hB
    | cons Z' B' =>
      obtain ⟨hZ, hT⟩ := ClosedBlowupSequence.cons_eq_cons_iff.mp hB
      obtain rfl := eq_of_comap_eq_of_flat_of_surjective h hZ
      have := flat_canonicalLift h Z
      have := surjective_canonicalLift h Z
      rw [ih (canonicalLift h Z) (eq_of_heq hT)]

/-- The pull-back of a push-forward: if `𝐁^X` is a push-forward of `𝐁(S)` along a morphism
`j : S → X`, then `j^*𝐁^X = 𝐁(S)`. -/
theorem pullback_eq_of_isPushforward {S X : Scheme.{u}} (j : S ⟶ X)
    {BS : ClosedBlowupSequence S} {BX : ClosedBlowupSequence X}
    (hP : ClosedBlowupSequence.IsPushforward j BS BX) : BX.pullback j = BS := by
  induction BS generalizing X with
  | nil S =>
    cases BX with
    | nil => rfl
    | cons ZX BX => exact hP.elim
  | cons ZS BS ih =>
    cases BX with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨hc, -, hP⟩ := hP
      subst hc
      change ClosedBlowupSequence.cons _ (BX.pullback (canonicalLift j ZX)) = _
      rw [← ih _ hP, eqToHom_refl, Category.id_comp]

/-- **Kollár 3.30.3, 3.34.** Let `S ⊆ X` be a closed subscheme with inclusion `j`, `𝐁(S)` a
blow-up sequence starting with `S` and `𝐁^X` a push-forward of `𝐁(S)` along `j`. Then the
restriction `𝐁^X|_S` is `𝐁(S)`. -/
@[mmp "lem_kr3b_restriction_of_pushforward"]
theorem restrict_eq_of_isPushforward {X : Scheme.{u}} (S : X.IdealSheafData)
    {BS : ClosedBlowupSequence S.subscheme} {BX : ClosedBlowupSequence X}
    (hP : ClosedBlowupSequence.IsPushforward S.subschemeι BS BX) : BX.restrict S = BS :=
  pullback_eq_of_isPushforward S.subschemeι hP

end MMP.Resolution.Kollar
