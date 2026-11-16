module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# Closed immersions are H-projective

A closed immersion `f : X ⟶ Y` is H-projective in the sense of [Stacks, Tag 01W8]
(`AlgebraicGeometry.IsProjectiveMorphism`): it is a closed immersion into `ℙ⁰_Y ≅ Y` over `Y`.

Stacks states the composite form, `Stacks.SectionsVanishingOnSubscheme.
isProjectiveMorphism_comp_of_isClosedImmersion`; this file records the case of the identity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- A closed immersion is H-projective: it is a closed immersion into `ℙ⁰_Y ≅ Y` over `Y`. -/
theorem isProjectiveMorphism_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : IsProjectiveMorphism f :=
  ⟨0, f ≫ (projectiveSpaceOver.zeroIsoBase Y).inv, inferInstance, by
    rw [Category.assoc, projectiveSpaceOver.zeroIsoBase_inv_comp_over, Category.comp_id]⟩

end MMP
