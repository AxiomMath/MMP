module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.AssemblyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksClass
public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatBaseChangeComposition

/-!
# The statement of Fulton's Theorem 19.2 on Stacks' Chow groups

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, with
orientation class `u ∈ H^{2d}(Y, Y - X)` (`MMP.Modules.IsRegularImbeddingOrientationClass`), and
`g : Y' ⟶ Y` a morphism of complex schemes, with fibre product `X' = X ×_Y Y'`
(`pullback f g`, over `ℂ` through `X`). For `α ∈ A_{m+d}(Y')` of Stacks' Chow group over
`fieldChowSituation ℂ`, Fulton's Theorem 19.2 states

  `cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))`,

where `f^! α = c(X ⟶ Y, 𝒩) ∩ α` is the cap product with Stacks' class of the normal sheaf
(`Stacks.Chow.regularNormalGysinClass`, Stacks 0FBK), `cl = MMP.Chow.chowCycleClass`, and
`cl_{X'}(f^! α)` is read in `H_{2m}(g⁻¹(X(ℂ)))` along `X'(ℂ) ≅ g⁻¹(X(ℂ))`
(`MMP.fibreSquarePointsHom`). This file states the formula
(`MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`).

## Main definitions

* `MMP.Chow.fibreProductOver`: `X ×_Y Y'` over `ℂ` through `X`.
* `MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`: Fulton's formula for one class `α`.

## Implementation notes

`fibreProductOver`, `isOver_fibreProduct_fst`, `isOver_fibreProduct_snd` and
`isComplexScheme_fibreProduct` are local instances only: a global `Over` instance on every
`pullback f g` would clash with Mathlib's on `pullback (V ↘ S) (W ↘ S)`. A file using the
formula activates them with `attribute [local instance]`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Theorem 19.2.
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace MMP.Chow

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))]

/-- The fibre product `X ×_Y Y'`, over `ℂ` through its first projection to `X`. -/
abbrev fibreProductOver : (pullback f g).Over (Spec (.of ℂ)) :=
  ⟨pullback.fst f g ≫ X ↘ Spec (.of ℂ)⟩

attribute [local instance] fibreProductOver

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The first projection `X ×_Y Y' ⟶ X` is a morphism over `ℂ`. -/
theorem isOver_fibreProduct_fst : (pullback.fst f g).IsOver (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- The second projection `X ×_Y Y' ⟶ Y'` is a morphism over `ℂ`. -/
theorem isOver_fibreProduct_snd : (pullback.snd f g).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change pullback.snd f g ≫ Y' ↘ Spec (.of ℂ) = pullback.fst f g ≫ X ↘ Spec (.of ℂ)
    rw [← comp_over g, ← comp_over f, pullback.condition_assoc]⟩

attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd

/-- The fibre product of a closed immersion of complex schemes is a complex scheme. -/
theorem isComplexScheme_fibreProduct [IsComplexScheme Y'] [IsClosedImmersion f] :
    IsComplexScheme (pullback f g) :=
  isComplexScheme_of_isClosedImmersion (pullback.snd f g)

variable (R : Type) [CommRing R] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

attribute [local instance] isComplexScheme_fibreProduct

/-- **Fulton's Theorem 19.2 for one class, on Stacks' Chow groups.** For a regular closed
immersion `f : X ⟶ Y` of codimension `d`, a class `u ∈ H^{2d}(Y, Y - X)`, `g : Y' ⟶ Y` and
`α ∈ A_{m+d}(Y')`: `cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))`, where
`X' = X ×_Y Y'`, `f^! α = c(X ⟶ Y, 𝒩) ∩ α` (`Stacks.Chow.regularNormalGysinClass`), and
`cl_{X'}(f^! α)` is read along `X'(ℂ) ≅ g⁻¹(X(ℂ))`. -/
def ChowCycleMapRefinedGysinFormulaAt (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) : Prop :=
  borelMooreHomology.pushforward R (ModuleCat.of R R)
      (fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip)
      (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip) (2 * m : ℕ)
      (chowCycleClass (X := pullback f g) R m
        (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f g ≫ X ↘ Spec (.of ℂ))
          (natCast_add_sub_natCast m d)
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap g ((m + d : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
              (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α)))) =
    BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul_eq m d)
      (borelMooreHomology.capProductSupportPullback R
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
        (hasProperNeighbourhoodDeformations_preimage_range_map f g)
        ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) u (chowCycleClass R (m + d) α))

end MMP.Chow
