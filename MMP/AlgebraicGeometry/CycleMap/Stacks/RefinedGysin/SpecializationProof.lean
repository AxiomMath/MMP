module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationAssembly
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationOrientationZero
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.Theorem
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibreCapInfinity
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThom
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibreCapZero

/-!
# Fulton's Theorem 19.2 on Stacks' Chow groups, from the specializations at `0` and `∞`

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes with
orientation class `u`, `g : Y' ⟶ Y` and `α ∈ A_{m+d}(Y')`. The specialization step
`MMP.Chow.SpecializationFormula` is the assembly `MMP.Chow.specializationFormula_of_steps` applied
to its four inputs: the specializations at `0` and `∞` of the deformation on the test scheme
(`MMP.Chow.specializationAtZero`, `MMP.Chow.specializationAtInfinity`), the orientation class at
zero (`MMP.Chow.orientationAtZero`) and the cone at infinity (`MMP.Chow.coneThomAtInfinity`).
With Stacks 0FBK and Lemma 19.2(d)
(`MMP.Chow.chowCycleMapRefinedGysinFormulaAt_of_specializationFormula`) this gives Theorem 19.2.

## Main results

* `MMP.Chow.specializationFormula`: the specialization step, for every `α`.
* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt`: Fulton's Theorem 19.2 on Stacks' Chow groups.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace MMP.Chow

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (R : Type) [CommRing R]

/-- **The specialization step of Fulton's proof of Theorem 19.2** (Fulton, §19.2, "Deformation"):
for a regular closed immersion `f : X ⟶ Y` of codimension `d` of complex schemes, every class
`u ∈ H^{2d}(Y, Y - X)`, `g : Y' ⟶ Y` and `α ∈ A_{m+d}(Y')`,
`u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))`. -/
theorem specializationFormula (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    SpecializationFormula f g R hf u m α :=
  specializationFormula_of_steps f g R hf u m α (specializationAtZero f g R m α)
    (specializationAtInfinity f g R m α) (orientationAtZero f R hf u)
    (coneThomAtInfinity f g hf R m α)

/-- **Fulton's Theorem 19.2 on Stacks' Chow groups.** For a regular closed immersion
`f : X ⟶ Y` of codimension `d` of complex schemes with orientation class `u`, `g : Y' ⟶ Y`,
`X' = X ×_Y Y'` and `α ∈ A_{m+d}(Y')`: `cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in
`H_{2m}(g⁻¹(X(ℂ)))`, where `f^! α = c(X ⟶ Y, 𝒩) ∩ α` (`Stacks.Chow.regularNormalGysinClass`). -/
theorem chowCycleMapRefinedGysinFormulaAt (hf : IsRegularClosedImmersionOfCodim f d)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f d u) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    ChowCycleMapRefinedGysinFormulaAt f g R hf u m α :=
  chowCycleMapRefinedGysinFormulaAt_of_specializationFormula f g R hf hu m α
    (specializationFormula f g R hf u m α)

end MMP.Chow
