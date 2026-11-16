module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange

/-!
# Pull-backs of blow-up sequences along flat morphisms (Kollár 3.30.1)

Let `𝐁 = (X_i, Z_i)` be a blow-up sequence of length `r` starting with `X` and `h : Y → X` a
flat morphism. The pull-back `h^*𝐁 = (Y_i, W_i)`, with `h_i : Y_i → X_i`, is then the fibre
product of `𝐁` with `Y`: for every `0 ≤ i ≤ r` the morphism `(h_i, Π^Y_i) : Y_i → X_i ×_X Y` is
an isomorphism, `Π^Y_i : Y_i → Y` being the composite of the first `i` blow-ups of `h^*𝐁`, and
under it `W_i = h_i⁻¹Z_i` corresponds to `Z_i ×_X Y`.

## Main statements

* `MMP.Resolution.Kollar.isPullback_pullback_toBase_of_flat`: the square formed by
  `Π^Y_r : Y_r → Y`, `h_r : Y_r → X_r`, `h` and `Π_r : X_r → X` is cartesian.
* `MMP.Resolution.Kollar.isIso_lift_pullbackHom_toBase_truncate`: for every `i`,
  `(h_i, Π^Y_i) : Y_i → X_i ×_X Y` is an isomorphism.
* `MMP.Resolution.Kollar.comap_pullbackHom_truncate_eq`: under this isomorphism the inverse image
  `h_i⁻¹Z` of a closed subscheme `Z ⊆ X_i`, in particular `W_i = h_i⁻¹Z_i`, is the inverse image
  of `Z ×_X Y` along the first projection.
* `MMP.Resolution.Kollar.pullback_truncate`: the first `i` steps of `h^*𝐁` are the pull-back of
  the first `i` steps of `𝐁`.

## Implementation notes

The `i`-th stage of `h^*𝐁` is read on the truncation: `Y_i` is the target of
`(𝐁.truncate i).pullback h` and `h_i` is `(𝐁.truncate i).pullbackHom h`, which is legitimate by
`MMP.Resolution.Kollar.pullback_truncate`. The proof is induction on the sequence: blowing up
commutes with flat base change ([Stacks, Tag 0805]), the comparison morphism being the canonical
lift by uniqueness in the universal property of the blow-up; the canonical lift is then flat, as
a base change of a flat morphism, and the cartesian squares paste. Local noetherianity is not
needed and is dropped.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.30]
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

universe u

namespace MMP.Resolution.Kollar

/-- Blowing up commutes with flat base change, the comparison morphism being the canonical lift:
for flat `h : Y → X` the square `B_{h⁻¹Z}Y → B_ZX`, `Y → X` is cartesian. -/
theorem isPullback_canonicalLift_of_flat {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    (Z : X.IdealSheafData) :
    IsPullback (blowUpToBase (Z.comap h)) (canonicalLift h Z) h (blowUpToBase Z) := by
  obtain ⟨g, hg⟩ := exists_isPullback_blowUpToBase_comap h Z
  have hgl : g = canonicalLift h Z :=
    blowUpLift_unique _ _ _ _ hg.w.symm
  exact hgl ▸ hg

/-- The canonical lift of a flat morphism is flat. -/
theorem flat_canonicalLift {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] (Z : X.IdealSheafData) :
    Flat (canonicalLift h Z) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_canonicalLift_of_flat h Z) ‹_›

/-- **Pull-back along a flat morphism is base change** (Kollár 3.30.1): for flat `h : Y → X`
the square formed by `Π^Y_r : Y_r → Y`, `h_r : Y_r → X_r`, `h` and `Π_r : X_r → X` is
cartesian, that is, `Y_r = X_r ×_X Y`. -/
@[mmp "lem_kr3b_pullback_is_blowup_sequence"]
theorem isPullback_pullback_toBase_of_flat {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [Flat h] :
    IsPullback (B.pullback h).toBase (B.pullbackHom h) h B.toBase := by
  induction B generalizing Y with
  | nil X =>
    change IsPullback (𝟙 Y) h h (𝟙 X)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | cons Z B ih =>
    have := flat_canonicalLift h Z
    exact (ih (canonicalLift h Z)).paste_horiz (isPullback_canonicalLift_of_flat h Z)

/-- The first `i` steps of the pull-back `h^*𝐁` are the pull-back of the first `i` steps of
`𝐁`. -/
@[mmp "lem_kr3b_pullback_is_blowup_sequence"]
theorem pullback_truncate {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) (i : ℕ) :
    (B.pullback h).truncate i = (B.truncate i).pullback h := by
  induction B generalizing Y i with
  | nil X => rfl
  | cons Z B ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.truncate]
      rw [ih]

/-- `h_r` and `Π^Y_r` agree over `X`: `h_r ≫ Π_r = Π^Y_r ≫ h`. -/
@[reassoc]
theorem pullbackHom_toBase_comm {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) :
    B.pullbackHom h ≫ B.toBase = (B.pullback h).toBase ≫ h := by
  induction B generalizing Y with
  | nil X =>
    change h ≫ 𝟙 X = 𝟙 Y ≫ h
    simp
  | cons Z B ih =>
    change B.pullbackHom (canonicalLift h Z) ≫ B.toBase ≫ blowUpToBase Z =
      ((B.pullback (canonicalLift h Z)).toBase ≫ blowUpToBase (Z.comap h)) ≫ h
    rw [reassoc_of% ih, Category.assoc, canonicalLift_comp_blowUpToBase]

/-- **Kollár 3.30.1.** Let `h : Y → X` be flat and `𝐁` a blow-up sequence starting with `X`.
For every `i`, the morphism `(h_i, Π^Y_i) : Y_i → X_i ×_X Y` is an isomorphism. -/
@[mmp "lem_kr3b_pullback_is_blowup_sequence"]
theorem isIso_lift_pullbackHom_toBase_truncate {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [Flat h] (i : ℕ) :
    IsIso (pullback.lift ((B.truncate i).pullbackHom h) ((B.truncate i).pullback h).toBase
      (pullbackHom_toBase_comm (B.truncate i) h)) := by
  have hP := (isPullback_pullback_toBase_of_flat (B.truncate i) h).flip
  have he : pullback.lift ((B.truncate i).pullbackHom h) ((B.truncate i).pullback h).toBase
      (pullbackHom_toBase_comm (B.truncate i) h) = hP.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, hP.isoPullback_hom_fst]
    · rw [pullback.lift_snd, hP.isoPullback_hom_snd]
  rw [he]
  infer_instance

/-- **Kollár 3.30.1, the centres.** Under `(h_i, Π^Y_i) : Y_i → X_i ×_X Y` (an isomorphism
when `h` is flat), the inverse image `h_i⁻¹Z` of a closed subscheme `Z ⊆ X_i` — for `Z = Z_i`
this is the centre `W_i` of `h^*𝐁` — corresponds to `Z ×_X Y`,
the inverse image of `Z` along the first projection. -/
@[mmp "lem_kr3b_pullback_is_blowup_sequence"]
theorem comap_pullbackHom_truncate_eq {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) (i : ℕ) (Z : (B.truncate i).target.IdealSheafData) :
    Z.comap ((B.truncate i).pullbackHom h) =
      (Z.comap (pullback.fst (B.truncate i).toBase h)).comap
        (pullback.lift ((B.truncate i).pullbackHom h) ((B.truncate i).pullback h).toBase
          (pullbackHom_toBase_comm (B.truncate i) h)) := by
  rw [← Scheme.IdealSheafData.comap_comp, pullback.lift_fst]

end MMP.Resolution.Kollar
