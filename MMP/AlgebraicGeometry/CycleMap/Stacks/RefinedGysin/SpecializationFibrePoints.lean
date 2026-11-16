module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationZeroFibre
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.DeformationNeighbourhood
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ChainBaseChangeGeneric
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The complex points of the fibres of `M° ⟶ 𝐏¹_ℂ` at `0` and `∞`

Let `X` be a scheme over `ℂ`, `Z ⊆ X` cut out by `ℐ`, and `ρ : M° ⟶ 𝐏¹_ℂ` Stacks' deformation
to the normal cone (`MMP.Chow.strictTransformComplToLine`). This file identifies the complex
points of its two distinguished fibres:

* `X(ℂ) ≅ ρ⁻¹(0) ⊆ M°(ℂ)`, along the lift `X ⟶ M°` of the zero section
  (`MMP.Chow.isPullback_strictTransformComplZeroSection`);
* `ρ⁻¹(∞)(ℂ) = ρ(ℂ)⁻¹(∞) ⊆ M°(ℂ)` for the closed subscheme `ρ⁻¹(∞)` of `M°`, which is the normal
  cone `C_ZX` when `Z` is cut out by a closed immersion
  (`MMP.Chow.normalConeIsoLineInfinityFibre`).

## Main definitions

* `MMP.Chow.lineZeroComplexPoint`, `MMP.Chow.lineInfinityComplexPoint`: `0, ∞ ∈ 𝐏¹(ℂ)`.
* `MMP.Chow.strictTransformComplZeroFibreHomeomorph`: `X(ℂ) ≅ ρ(ℂ)⁻¹(0)`.

## Main results

* `MMP.Chow.range_map_strictTransformComplZeroSection`: `X(ℂ) = ρ(ℂ)⁻¹(0)` inside `M°(ℂ)`.
* `MMP.Chow.range_map_lineInfinityFibre`: `ρ⁻¹(∞)(ℂ) = ρ(ℂ)⁻¹(∞)` inside `M°(ℂ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open scoped MMP.SubschemeOver

namespace MMP.Chow

attribute [local instance] blowupAtInfinityOver strictTransformComplAtInfinityOver
  isOver_strictTransformComplToLine

/-- The point `0` of `𝐏¹(ℂ)`. -/
def lineZeroComplexPoint : UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))) :=
  ⟨lineZeroSection _, lineZeroSection_comp _⟩

/-- The point `∞` of `𝐏¹(ℂ)`. -/
def lineInfinityComplexPoint : UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))) :=
  ⟨lineInfinitySection _, lineInfinitySection_comp _⟩

/-- The structure morphism of `Spec ℂ` over itself is the identity. -/
lemma spec_over_spec_eq_id : Spec (.of ℂ) ↘ Spec (.of ℂ) = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- A point of `Spec ℂ` over `ℂ` is the identity. -/
lemma toHom_eq_id_of_spec (p : UnderlyingSpace ℂ (Spec (.of ℂ))) : p.toHom = 𝟙 _ := by
  simpa [spec_over_spec_eq_id] using p.toHom_comp_over

/-- The image of a morphism from the spectrum of a field is a single point. -/
lemma range_base_spec {T : Scheme.{0}} (s : Spec (.of ℂ) ⟶ T) :
    range s.base = {s (IsLocalRing.closedPoint ℂ)} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨_, (mem_singleton_iff.1 hx).symm⟩⟩
  rintro ⟨p, rfl⟩
  rw [mem_singleton_iff, Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (ℐ : X.IdealSheafData)

/-- The lift `X ⟶ M°` of the zero section is a morphism over `ℂ`. -/
theorem isOver_strictTransformComplZeroSection :
    (strictTransformComplZeroSection ℐ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change strictTransformComplZeroSection ℐ ≫ (strictTransformComplAtInfinity ℐ).ι ≫
        blowupAtInfinityToLine ℐ ≫ relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ) =
      X ↘ Spec (.of ℂ)
    rw [strictTransformComplZeroSection_ι_assoc,
      blowupZeroSection_comp_blowupAtInfinityToLine_assoc, ← Category.assoc,
      lineZeroSection_comp, Category.id_comp]⟩

attribute [local instance] isOver_strictTransformComplZeroSection

/-- The lift `X ⟶ M°` of the zero section is a closed immersion: it is the base change along
`ρ` of the zero section of `𝐏¹_ℂ`. -/
theorem isClosedImmersion_strictTransformComplZeroSection :
    IsClosedImmersion (strictTransformComplZeroSection ℐ) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_strictTransformComplZeroSection ℐ).flip inferInstance

attribute [local instance] isClosedImmersion_strictTransformComplZeroSection

/-- **`X(ℂ) = ρ(ℂ)⁻¹(0)`**: the complex points of the fibre at `0` of `ρ : M° ⟶ 𝐏¹_ℂ` are those
of the image of the lift `X ⟶ M°` of the zero section. -/
theorem range_map_strictTransformComplZeroSection :
    range (UnderlyingSpace.map (K := ℂ) (strictTransformComplZeroSection ℐ)) =
      UnderlyingSpace.map (K := ℂ) (strictTransformComplToLine ℐ) ⁻¹'
        {lineZeroComplexPoint} := by
  have : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [spec_over_spec_eq_id, Category.comp_id]⟩
  have : (lineZeroSection (Spec (.of ℂ))).IsOver (Spec (.of ℂ)) :=
    ⟨by simp [spec_over_spec_eq_id]⟩
  rw [range_map_eq_preimage_of_isPullback (isPullback_strictTransformComplZeroSection ℐ)]
  congr 1
  ext p
  simp only [mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    refine UnderlyingSpace.ext ?_
    change q.toHom ≫ lineZeroSection _ = lineZeroSection _
    rw [toHom_eq_id_of_spec, Category.id_comp]
  · rintro rfl
    exact ⟨⟨𝟙 _, by rw [spec_over_spec_eq_id, Category.id_comp]⟩,
      UnderlyingSpace.ext (Category.id_comp _)⟩

/-- **`X(ℂ) ≅ ρ(ℂ)⁻¹(0)`** (Fulton, proof of Theorem 19.2: `X(ℂ)` is the fibre of `M°(ℂ)` over
`0`), along the lift `X ⟶ M°` of the zero section. -/
def strictTransformComplZeroFibreHomeomorph :
    UnderlyingSpace ℂ X ≃ₜ
      (UnderlyingSpace.map (K := ℂ) (strictTransformComplToLine ℐ) ⁻¹' {lineZeroComplexPoint} :
        Set (UnderlyingSpace ℂ (strictTransformComplAtInfinity ℐ).toScheme)) :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (strictTransformComplZeroSection ℐ)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_map_strictTransformComplZeroSection ℐ))

/-- The homeomorphism `X(ℂ) ≅ ρ(ℂ)⁻¹(0)` sends a point to its image under the lift `X ⟶ M°` of
the zero section. -/
@[simp]
lemma coe_strictTransformComplZeroFibreHomeomorph (x : UnderlyingSpace ℂ X) :
    (strictTransformComplZeroFibreHomeomorph ℐ x : UnderlyingSpace ℂ _) =
      UnderlyingSpace.map (K := ℂ) (strictTransformComplZeroSection ℐ) x :=
  rfl

/-- **`ρ⁻¹(∞)(ℂ) = ρ(ℂ)⁻¹(∞)`**: the complex points of the closed subscheme `ρ⁻¹(∞) ⊆ M°`, cut
out by the inverse image of the divisor at infinity of `𝐏¹_ℂ`, are the points of `M°(ℂ)` over
`∞`. -/
theorem range_map_lineInfinityFibre
    [LocallyOfFiniteType ((strictTransformComplAtInfinity ℐ).toScheme ↘ Spec (.of ℂ))] :
    range (UnderlyingSpace.map (K := ℂ)
        ((lineInfinityDivisor (Spec (.of ℂ))).comap (strictTransformComplToLine ℐ)).subschemeι) =
      UnderlyingSpace.map (K := ℂ) (strictTransformComplToLine ℐ) ⁻¹'
        {lineInfinityComplexPoint} := by
  rw [range_map_of_isClosedImmersion, preimage_map_singleton]
  congr 1
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, coe_support_lineInfinityDivisor,
    range_base_spec]
  rfl

end MMP.Chow
