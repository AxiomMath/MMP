module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationSteps
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationZeroFibre
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange

/-!
# The orientation class at zero (Fulton, proof of Theorem 19.2)

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `W` Stacks'
blowup at infinity of `ker f`, `σ : Y ⟶ W` the lift of the zero section of `𝐏¹_Y` and
`e_W : X ×_ℂ 𝐏¹_ℂ ⟶ W` the trivial family. The square

```
X --(x ↦ (x, 0))--> X ×_ℂ 𝐏¹_ℂ
|                       | e_W
v                       v
Y ---------σ----------> W
```

is cartesian: it is the top half of the cartesian square `X ⟶ 𝐏¹_X`, `Y ⟶ 𝐏¹_Y` of zero
sections, whose bottom half `Y ⟶ W ⟶ 𝐏¹_Y` is cartesian (`MMP.Chow.isPullback_blowupZeroSection`).
So `σ^* u_x` is an orientation class of `f` (Fulton, Lemma 19.2 (a)), and by uniqueness it is `u`.

## Main definitions

* `MMP.Chow.lineFamilyZeroSection`: `X ⟶ X ×_ℂ 𝐏¹_ℂ`, `x ↦ (x, 0)`.

## Main results

* `MMP.Chow.isPullback_lineFamily_blowupZeroSection`: the square above is cartesian.
* `MMP.Chow.orientationAtZero`: `MMP.Chow.OrientationAtZero` for every regular closed immersion.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] blowupAtInfinityOver

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] (f : X ⟶ Y)
  [IsClosedImmersion f]

/-- **The zero section `x ↦ (x, 0)` of the trivial family** `X ⟶ X ×_ℂ 𝐏¹_ℂ`. -/
def lineFamilyZeroSection :
    X ⟶ pullback (X ↘ Spec (.of ℂ)) (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ)) :=
  lineZeroSection X ≫ (relativeProjectiveLineIsoProjectiveLineProduct (X ↘ Spec (.of ℂ))).hom

/-- The first projection of `x ↦ (x, 0)` is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem lineFamilyZeroSection_fst :
    lineFamilyZeroSection (X := X) ≫ pullback.fst _ _ = 𝟙 X := by
  rw [lineFamilyZeroSection, Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst,
    lineZeroSection_comp]

/-- `x ↦ (x, 0)` is a morphism over `ℂ`. -/
theorem isOver_lineFamilyZeroSection : (lineFamilyZeroSection (X := X)).IsOver (Spec (.of ℂ)) :=
  ⟨by
    rw [← comp_over (pullback.fst (X ↘ Spec (.of ℂ))
      (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ)),
      lineFamilyZeroSection_fst_assoc]⟩

omit [Y.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`X = e_W⁻¹(σ(Y))`**: the square `x ↦ (x, 0)`, `f`, `e_W`, `σ` is cartesian. -/
theorem isPullback_lineFamily_blowupZeroSection :
    IsPullback f lineFamilyZeroSection (blowupZeroSection f.ker) (lineFamily f) := by
  have hbot := isPullback_blowupZeroSection f.ker
  have hout : IsPullback (lineZeroSection X) (f ≫ 𝟙 Y)
      (lineToBlowupAtInfinityOfClosedImmersion f ≫ blowupAtInfinityToLine f.ker)
      (lineZeroSection Y) := by
    rw [Category.comp_id, lineToBlowupAtInfinityOfClosedImmersion_comp]
    exact isPullback_lineZeroSection_projectiveLineBaseChange f
  have hw : lineZeroSection X ≫ lineToBlowupAtInfinityOfClosedImmersion f =
      f ≫ blowupZeroSection f.ker := by
    have hl := hbot.lift_fst (lineZeroSection X ≫ lineToBlowupAtInfinityOfClosedImmersion f) f
      (by simpa using hout.w)
    have hs := hbot.lift_snd (lineZeroSection X ≫ lineToBlowupAtInfinityOfClosedImmersion f) f
      (by simpa using hout.w)
    rw [Category.comp_id] at hs
    rw [← hl, hs]
  have htop : IsPullback (lineZeroSection X) f (lineToBlowupAtInfinityOfClosedImmersion f)
      (blowupZeroSection f.ker) := IsPullback.of_bot hout hw hbot
  have hiso : IsPullback (relativeProjectiveLineIsoProjectiveLineProduct
      (X ↘ Spec (.of ℂ))).hom (lineToBlowupAtInfinityOfClosedImmersion f) (lineFamily f) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [lineFamily]⟩
  have h := htop.paste_horiz hiso
  rw [Category.comp_id] at h
  exact h.flip

variable [f.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] {d : ℕ}
  (R : Type) [CommRing R]

/-- **The orientation class at zero** (Fulton, proof of Theorem 19.2): `σ^* u_x = u` for every
orientation class `u_x` of `e_W` and `u` of `f`. -/
theorem orientationAtZero (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) :
    OrientationAtZero f R hf u := by
  have := isOver_blowupZeroSection (Y := Y) f.ker
  have := isOver_lineFamily f
  have := isOver_lineFamilyZeroSection (X := X)
  intro ux hux hu
  exact MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq R
    (isRegularClosedImmersionOfCodim_lineFamily f hf) hf
    (isPullback_lineFamily_blowupZeroSection f) hux hu

end MMP.Chow
