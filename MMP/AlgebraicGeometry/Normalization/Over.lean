module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme

/-!
# The normalization of a scheme over a base

If `X` is a scheme over `S`, its normalization `X̃`
(`AlgebraicGeometry.Scheme.normalizationScheme`) is a scheme over `S` through the normalization
morphism `X̃ → X`, and the normalization morphism is a morphism over `S`.

## Main definitions

* `MMP.normalizationSchemeOver`: the normalization of a scheme over `S` is a scheme over `S`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

variable {S : Scheme.{u}} (X : Scheme.{u}) [X.Over S]
  (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)

/-- The normalization `X̃` of a scheme `X` over `S` is a scheme over `S`, through the
normalization morphism `X̃ → X`. -/
instance normalizationSchemeOver : (X.normalizationScheme hX).Over S :=
  ⟨X.normalization hX ≫ X ↘ S⟩

/-- The normalization morphism of a scheme over `S` is a morphism over `S`. -/
instance normalization_isOver : (X.normalization hX).IsOver S :=
  ⟨rfl⟩

end MMP
