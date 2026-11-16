module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibre
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier

/-!
# The fibre at zero of the deformation `M° ⟶ 𝐏¹_ℂ`

Let `X` be a scheme over `ℂ`, `Z ⊆ X` cut out by a quasi-coherent ideal sheaf `ℐ`, `b : W ⟶ 𝐏¹_X`
Stacks' blowup at infinity (Stacks 0FBG) and `ρ : M° ⟶ 𝐏¹_ℂ` the deformation map
(`MMP.Chow.strictTransformComplToLine`). The zero section `0 : X ⟶ 𝐏¹_X` lands in the open
`𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` over which `b` is an isomorphism (Stacks 0FBG (1)), so it lifts to a section
`X ⟶ W`, which misses the strict transform `X' ⊆ W_∞` and so lands in `M°`. The square

```
X ----> M°
|        | ρ
v        v
Spec ℂ --0--> 𝐏¹_ℂ
```

is cartesian: `X` is the fibre of `ρ` at `0`.

## Main definitions

* `MMP.Chow.blowupZeroSection`: the lift `X ⟶ W` of the zero section of `𝐏¹_X`.
* `MMP.Chow.strictTransformComplZeroSection`: the same, as a morphism `X ⟶ M°`.

## Main results

* `MMP.Chow.isPullback_lineZeroSection_projectiveLineBaseChange`: the zero section of `𝐏¹_{X'}`
  is the base change of that of `𝐏¹_X`.
* `MMP.Chow.isPullback_blowupZeroSection`: `X = b⁻¹(0(X))`.
* `MMP.Chow.isPullback_strictTransformComplZeroSection`: `X = ρ⁻¹(0)`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [W. Fulton, *Intersection Theory*][fulton1998], §5.1 and §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace MMP.Chow

/-- **The zero section of `𝐏¹_{X'}` is the base change of that of `𝐏¹_X`** along `f : X' ⟶ X`. -/
theorem isPullback_lineZeroSection_projectiveLineBaseChange {X' X : Scheme.{u}} (f : X' ⟶ X) :
    IsPullback (lineZeroSection X') f (projectiveLineBaseChange f) (lineZeroSection X) := by
  refine IsPullback.of_right (h₁₂ := relativeProjectiveLine X' ↘ X')
    (h₂₂ := relativeProjectiveLine X ↘ X) (v₁₃ := f) ?_
    (absoluteConstantSection_comp_projectiveLineBaseChange integralZeroSection f)
    (isPullback_projectiveLineBaseChange f)
  rw [lineZeroSection_comp, lineZeroSection_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The zero section of `𝐏¹_X` lands in the open `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` over which the blowup at
infinity is an isomorphism. -/
theorem range_lineZeroSection_subset_isomorphismLocusAtInfinity :
    Set.range (lineZeroSection X) ⊆
      (isomorphismLocusAtInfinity ℐ : Set (relativeProjectiveLine X)) :=
  fun _ hp ↦ (le_sup_left : (affineChart X).opensRange ≤ isomorphismLocusAtInfinity ℐ)
    (range_lineZeroSection_subset_range_affineChart X hp)

/-- The zero section of `𝐏¹_X`, as a morphism into `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}`. -/
def lineZeroSectionToIsomorphismLocus : X ⟶ (isomorphismLocusAtInfinity ℐ).toScheme :=
  IsOpenImmersion.lift (isomorphismLocusAtInfinity ℐ).ι (lineZeroSection X) (by
    rw [Scheme.Opens.range_ι]
    exact range_lineZeroSection_subset_isomorphismLocusAtInfinity ℐ)

/-- The zero section into `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` followed by the inclusion of that open is the zero
section of `𝐏¹_X`. -/
@[reassoc (attr := simp)]
theorem lineZeroSectionToIsomorphismLocus_ι :
    lineZeroSectionToIsomorphismLocus ℐ ≫ (isomorphismLocusAtInfinity ℐ).ι = lineZeroSection X :=
  IsOpenImmersion.lift_fac _ _ _

/-- The zero section of `𝐏¹_X`, lifted to `b⁻¹(𝐀¹_X ∪ 𝐏¹_{X ∖ Z}) ⊆ W` along the isomorphism `b`
over that open (Stacks 0FBG (1)). -/
def blowupZeroSectionToPreimage :
    X ⟶ (blowupAtInfinityToLine ℐ ⁻¹ᵁ isomorphismLocusAtInfinity ℐ).toScheme :=
  haveI := isIso_blowupAtInfinityToLine_restrict ℐ
  lineZeroSectionToIsomorphismLocus ℐ ≫
    inv (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ)

/-- **The lift `X ⟶ W` of the zero section of `𝐏¹_X`** to the blowup at infinity. -/
def blowupZeroSection : X ⟶ blowupAtInfinity ℐ :=
  blowupZeroSectionToPreimage ℐ ≫
    (blowupAtInfinityToLine ℐ ⁻¹ᵁ isomorphismLocusAtInfinity ℐ).ι

/-- The lift of the zero section followed by `b` is the zero section. -/
@[reassoc (attr := simp)]
theorem blowupZeroSection_comp_blowupAtInfinityToLine :
    blowupZeroSection ℐ ≫ blowupAtInfinityToLine ℐ = lineZeroSection X := by
  have := isIso_blowupAtInfinityToLine_restrict ℐ
  rw [blowupZeroSection, blowupZeroSectionToPreimage, Category.assoc, Category.assoc,
    ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, lineZeroSectionToIsomorphismLocus_ι]

/-- **`X = b⁻¹(0(X))`**: the square `X ⟶ W`, `X = X`, `b`, `0 : X ⟶ 𝐏¹_X` is cartesian. -/
theorem isPullback_blowupZeroSection :
    IsPullback (blowupZeroSection ℐ) (𝟙 X) (blowupAtInfinityToLine ℐ) (lineZeroSection X) := by
  have := isIso_blowupAtInfinityToLine_restrict ℐ
  have h₁ : IsPullback (blowupZeroSectionToPreimage ℐ) (𝟙 X)
      (blowupAtInfinityToLine ℐ ∣_ isomorphismLocusAtInfinity ℐ)
      (lineZeroSectionToIsomorphismLocus ℐ) :=
    IsPullback.of_vert_isIso ⟨by simp [blowupZeroSectionToPreimage]⟩
  have h := h₁.paste_horiz
    (isPullback_morphismRestrict (blowupAtInfinityToLine ℐ) (isomorphismLocusAtInfinity ℐ)).flip
  rwa [lineZeroSectionToIsomorphismLocus_ι] at h

/-- The lift of the zero section misses the strict transform `X' ⊆ W_∞`: `X'` lies in the fibre
at infinity, and the zero and infinity sections of `𝐏¹_X` are disjoint. -/
theorem range_blowupZeroSection_subset_strictTransformComplAtInfinity :
    Set.range (blowupZeroSection ℐ) ⊆
      (strictTransformComplAtInfinity ℐ : Set (blowupAtInfinity ℐ)) := by
  rintro _ ⟨x, rfl⟩ hx
  have h₁ : (strictTransformIdealAtInfinity ℐ).support ≤ (fibreIdealAtInfinity ℐ).support := by
    rw [fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity,
      Scheme.IdealSheafData.support_mul]
    exact le_sup_right
  have h₂ := h₁ hx
  rw [fibreIdealAtInfinity, Scheme.IdealSheafData.support_comap] at h₂
  change (blowupAtInfinityToLine ℐ) (blowupZeroSection ℐ x) ∈
    ((lineInfinityDivisor X).support : Set (relativeProjectiveLine X)) at h₂
  rw [coe_support_lineInfinityDivisor, ← Scheme.Hom.comp_apply,
    blowupZeroSection_comp_blowupAtInfinityToLine] at h₂
  exact Set.disjoint_left.1 (disjoint_range_lineZeroSection_lineInfinitySection X)
    (Set.mem_range_self x) h₂

/-- **The lift `X ⟶ M°` of the zero section of `𝐏¹_X`** to the open deformation space. -/
def strictTransformComplZeroSection : X ⟶ (strictTransformComplAtInfinity ℐ).toScheme :=
  IsOpenImmersion.lift (strictTransformComplAtInfinity ℐ).ι (blowupZeroSection ℐ) (by
    rw [Scheme.Opens.range_ι]
    exact range_blowupZeroSection_subset_strictTransformComplAtInfinity ℐ)

/-- The lift `X ⟶ M°` followed by the inclusion `M° ⊆ W` is the lift `X ⟶ W` of the zero
section. -/
@[reassoc (attr := simp)]
theorem strictTransformComplZeroSection_ι :
    strictTransformComplZeroSection ℐ ≫ (strictTransformComplAtInfinity ℐ).ι =
      blowupZeroSection ℐ :=
  IsOpenImmersion.lift_fac _ _ _

end MMP.Chow

namespace MMP.Chow

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (ℐ : X.IdealSheafData)

/-- **`X = ρ⁻¹(0)`**: the square `X ⟶ M°`, `X ⟶ Spec ℂ`, `ρ : M° ⟶ 𝐏¹_ℂ`, `0 : Spec ℂ ⟶ 𝐏¹_ℂ` is
cartesian. -/
theorem isPullback_strictTransformComplZeroSection :
    IsPullback (strictTransformComplZeroSection ℐ) (X ↘ Spec (.of ℂ))
      (strictTransformComplToLine ℐ) (lineZeroSection (Spec (.of ℂ))) := by
  have h₀ : IsPullback (strictTransformComplZeroSection ℐ) (𝟙 X)
      (strictTransformComplAtInfinity ℐ).ι (blowupZeroSection ℐ) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := (h₀.paste_vert (isPullback_blowupZeroSection ℐ)).paste_vert
    (isPullback_lineZeroSection_projectiveLineBaseChange (X ↘ Spec (.of ℂ)))
  simpa [strictTransformComplToLine] using h

end MMP.Chow
