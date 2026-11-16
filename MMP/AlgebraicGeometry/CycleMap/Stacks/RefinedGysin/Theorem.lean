module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.NormalConeLink
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.ProjectionPullback

/-!
# Fulton's Theorem 19.2 on Stacks' Chow groups, from the specialization step

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes with
orientation class `u`, `g : Y' ⟶ Y`, `X' = X ×_Y Y'`, and `α ∈ A_{m+d}(Y')`. Fulton's proof of
Theorem 19.2, `cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)`, runs on the vector bundle
`π : 𝐕(E') = N ×_Y Y' ⟶ X'` of the normal sheaf:

* `cl_{X'}(f^! α) = u_{E'} ∩ cl(π^* f^! α)` (Lemma 19.2(d),
  `MMP.Chow.chowCycleClass_regularNormalGysinClass_cap_eq_thomCap`);
* `π^* f^! α` is the specialization `(ι_* ∘ j^* ∘ C) ∩ α` of `α` to the normal cone (Stacks 0FBK,
  `MMP.Chow.flatPullbackChow_proj_regularNormalGysinClass_cap_heq`);
* `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl(α)`: the specialization step
  `MMP.Chow.SpecializationFormula`, the deformation to the normal cone.

This file assembles the three
(`MMP.Chow.chowCycleMapRefinedGysinFormulaAt_of_specializationFormula`):
Theorem 19.2 at `α` holds as soon as the specialization step does.

## Main results

* `MMP.Chow.flatPullbackChow_proj_regularNormalGysinClass_cap_eq`
* `MMP.Chow.chowCycleMapRefinedGysinFormulaAt_of_specializationFormula`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Theorem 19.2.
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule

/-- `chowGroupCongrDegree` changes an element only up to heterogeneous equality. -/
theorem chowGroupCongrDegree_heq {D : ChowSituation.{0}} {Z : Scheme.{0}} (s : Z ⟶ D.S)
    [LocallyOfFiniteType s] {j k : ℤ} (h : j = k) (a : chowGroup D s j) :
    chowGroupCongrDegree D s h a ≍ a := by
  subst h
  rfl

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

/-- **Stacks 0FBK on `𝐕(E')`.** For `α ∈ A_{m+d}(Y')`, the flat pull-back along
`π : 𝐕(E') ⟶ X'` of `f^! α ∈ A_m(X')` is the specialization `(ι_* ∘ j^* ∘ C) ∩ α` of `α` to the
normal cone (`MMP.Chow.specializedConeClass`). -/
theorem flatPullbackChow_proj_regularNormalGysinClass_cap_eq
    (hf : IsRegularClosedImmersionOfCodim f d) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    haveI := locallyOfFiniteType_proj (fibreNormalModule f g hf) d
    haveI := flat_proj (fibreNormalModule f g hf) d
    flatPullbackChow (fieldChowSituation ℂ)
        (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ))
        (pullback f g ↘ Spec (.of ℂ)) (proj (fibreNormalModule f g hf)) rfl d
        (relativeDimension_proj _ d) m
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (chowGroupCongrDegree (fieldChowSituation ℂ)
          (pullback.fst f g ≫ X ↘ Spec (.of ℂ)) (natCast_add_sub_natCast m d)
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap g ((m + d : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
              (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α))) =
      specializedConeClass f g hf (m + d) α := by
  have := locallyOfFiniteType_proj (fibreNormalModule f g hf) d
  have := flat_proj (fibreNormalModule f g hf) d
  refine eq_of_heq (HEq.trans ?_ (flatPullbackChow_proj_regularNormalGysinClass_cap_heq f g hf
    (m + d) (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
      (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α)))
  exact flatPullbackChow_heq_congr (fieldChowSituation ℂ)
    (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) (pullback f g ↘ Spec (.of ℂ))
    (proj (fibreNormalModule f g hf)) (proj (fibreNormalModule f g hf)) rfl rfl rfl rfl _ _
    (natCast_add_sub_natCast m d).symm _ _ _ _ (chowGroupCongrDegree_heq _ _ _)

variable (R : Type) [CommRing R]

/-- **Fulton's Theorem 19.2 on Stacks' Chow groups, from the specialization step.** For a regular
closed immersion `f : X ⟶ Y` of codimension `d` with orientation class `u`, `g : Y' ⟶ Y` and
`α ∈ A_{m+d}(Y')`: if the specialization step holds at `α`
(`MMP.Chow.SpecializationFormula`: `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl(α)`), then
`cl_{X'}(f^! α) = g^* u ∩ cl_{Y'}(α)` in `H_{2m}(g⁻¹(X(ℂ)))`. -/
theorem chowCycleMapRefinedGysinFormulaAt_of_specializationFormula
    (hf : IsRegularClosedImmersionOfCodim f d)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f d u) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ))
    (hS : SpecializationFormula f g R hf u m α) :
    ChowCycleMapRefinedGysinFormulaAt f g R hf u m α := by
  unfold ChowCycleMapRefinedGysinFormulaAt
  rw [chowCycleClass_regularNormalGysinClass_cap_eq_thomCap f g R hf m α,
    flatPullbackChow_proj_regularNormalGysinClass_cap_eq f g hf m α]
  exact hS hu

end MMP.Chow
