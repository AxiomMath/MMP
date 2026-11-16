module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.PushforwardReduction
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorBaseChange
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorTransversal
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorExcess

/-!
# Fulton's Theorem 19.2 on Stacks' Chow groups for an effective Cartier divisor

Let `f : X ⟶ Y` be a regular closed immersion of codimension one of complex schemes, that is an
effective Cartier divisor
(`MMP.isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one`), with orientation
class `u ∈ H²(Y, Y - X)`, and let `g : Y' ⟶ Y` be a morphism from a complex
scheme carrying an ample invertible module. Then Fulton's Theorem 19.2,
`cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))` for `α ∈ A_{m+1}(Y')`
(`MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`), holds without the deformation to the normal cone.

The proof is Fulton's for divisors. Both sides are additive and compatible with proper
push-forward, so it suffices to treat `α = [V]` for an integral closed subscheme `V ⊆ Y'`
(`MMP.Chow.chowCycleMapRefinedGysinFormulaAt_of_forall_fundamentalChowClass`). The base change
`X ×_Y V ⟶ V` is then either an isomorphism or again a divisor
(`MMP.Chow.isIso_or_isRegularClosedImmersionOfCodim_one_pullback_snd`):

* if it is a divisor, `f^![V] = [X ×_Y V]` (Stacks 0FBM at vanishing excess) and Fulton's
  Lemma 19.1.3 for the canonical section of `𝒪_V(X ×_Y V)` gives the formula
  (`MMP.Chow.chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isRegular`);
* if `V` lies in `X`, `f^![V] = c₁(N|_V) ∩ [V]` (Stacks 0FBM at full excess), and Fulton's
  Proposition 19.2 for line bundles with `u|_X = c₁ᵗᵒᵖ(N)` gives the formula
  (`MMP.Chow.chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isIso`).

## Main results

* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt_of_isEffectiveCartierDivisor`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.1.3, Proposition 19.2, Theorem 19.2.
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf MMP.Modules Stacks.Ample

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))]
  (R : Type) [CommRing R] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g]

/-- **Fulton's Theorem 19.2 for an effective Cartier divisor, on Stacks' Chow groups.** Let
`f : X ⟶ Y` be a regular closed immersion of codimension one of complex schemes with orientation
class `u ∈ H²(Y, Y - X)`, and `g : Y' ⟶ Y` a morphism from a complex scheme carrying an ample
invertible module `A`. Then `cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))` for
every `α ∈ A_{m+1}(Y')`, where `X' = X ×_Y Y'`. -/
theorem chowCycleMapRefinedGysinFormulaAt_of_isEffectiveCartierDivisor
    (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u)
    (A : Y'.Modules) [IsInvertibleModule Y' A] (hA : IsAmple Y' A) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + 1 : ℕ)) :
    ChowCycleMapRefinedGysinFormulaAt f g R hf u m α := by
  refine chowCycleMapRefinedGysinFormulaAt_of_forall_fundamentalChowClass f g R hf u m
    (fun x hx ↦ ?_) α
  set i := (integralComponentAt x).subschemeι
  have hn := natCast_eq_dimension_integralComponentAt x hx
  have : IsInvertibleModule (integralComponentAt x).subscheme
      ((Scheme.Modules.pullback i).obj A) := isInvertibleModule_pullback i A
  have hA' : IsAmple (integralComponentAt x).subscheme ((Scheme.Modules.pullback i).obj A) := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.toRingedSpace.presheaf
        (structureSheafRing Y'.toRingedSpace).property A := ‹IsInvertibleModule Y' A›
    have : AlgebraicGeometry.SheafOfModules.IsInvertible
        (integralComponentAt x).subscheme.toRingedSpace.presheaf
        (structureSheafRing (integralComponentAt x).subscheme.toRingedSpace).property
        ((Scheme.Modules.pullback i).obj A) := ‹IsInvertibleModule _ _›
    exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion i A
        ((Stacks.AmpleBridge.isAmple_iff_isAmple Y' A).mp hA))
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  rcases isIso_or_isRegularClosedImmersionOfCodim_one_pullback_snd f (i ≫ g) hf with h | h
  · have := h
    exact chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isIso f R (i ≫ g) hf hu hn
      _ hA'
  · exact chowCycleMapRefinedGysinFormulaAt_fundamentalChowClass_of_isRegular f R (i ≫ g) hf hu
      hn h

end MMP.Chow
