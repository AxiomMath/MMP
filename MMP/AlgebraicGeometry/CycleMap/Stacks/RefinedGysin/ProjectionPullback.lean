module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationStatement

/-!
# The projection pull-back step of Fulton's proof of Theorem 19.2, on Stacks' Chow groups

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `g : Y' ⟶ Y`,
`X' = X ×_Y Y'`, and `π : 𝐕(E') ⟶ X'` the vector bundle of `E' = (X' ⟶ X)^*(𝒩^∨)`
(`MMP.Chow.fibreNormalModule`), `𝒩` the normal sheaf of `f`, with Thom class `u_{E'}`. For
`α ∈ A_{m+d}(Y')`, the cycle class of the refined Gysin pull-back `f^! α ∈ A_m(X')` is the cap
product of `u_{E'}` with the cycle class of its flat pull-back `π^*(f^! α)` to the bundle:

  `cl_{X'}(f^! α) = u_{E'} ∩ cl_{𝐕(E')}(π^* f^! α)`  in `H_{2m} X'`,

read through `0(X'(ℂ)) ≅ X'(ℂ)` (`MMP.Chow.chowCycleClass_regularNormalGysinClass_cap_eq_thomCap`).
This is Fulton's Lemma 19.2(d) (`MMP.Chow.thomCap_chowCycleClass_flatPullbackChow_proj`) at
`f^! α`.

## Main results

* `MMP.Chow.chowCycleClass_regularNormalGysinClass_cap_eq_thomCap`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Lemma 19.2(d) and the proof of
  Theorem 19.2.
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

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (R : Type) [CommRing R]

/-- **The projection pull-back step of Fulton's proof of Theorem 19.2.** For `α ∈ A_{m+d}(Y')`,
`cl_{X'}(f^! α) = u_{E'} ∩ cl_{𝐕(E')}(π^* f^! α)` in `H_{2m} X'`, read through
`0(X'(ℂ)) ≅ X'(ℂ)`, where `f^! α = c(X ⟶ Y, 𝒩) ∩ α` (`Stacks.Chow.regularNormalGysinClass`). -/
theorem chowCycleClass_regularNormalGysinClass_cap_eq_thomCap
    (hf : IsRegularClosedImmersionOfCodim f d) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    haveI := locallyOfFiniteType_proj (fibreNormalModule f g hf) d
    haveI := flat_proj (fibreNormalModule f g hf) d
    chowCycleClass (X := pullback f g) R m
        (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f g ≫ X ↘ Spec (.of ℂ))
          (natCast_add_sub_natCast m d)
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap g ((m + d : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
              (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α))) =
      BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m d)
        (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (zeroSectionInvHom (fibreNormalModule f g hf))
          (isProperMap_zeroSectionInvHom (fibreNormalModule f g hf)) _
          (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
            (hasProperNeighbourhoodDeformations_range_zeroSection (fibreNormalModule f g hf))
            ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) (thomClass R (fibreNormalModule f g hf) d)
            (chowCycleClass R (m + d)
              (flatPullbackChow (fieldChowSituation ℂ)
                (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ))
                (pullback f g ↘ Spec (.of ℂ)) (proj (fibreNormalModule f g hf)) rfl d
                (relativeDimension_proj _ d) m
                (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
                (chowGroupCongrDegree (fieldChowSituation ℂ)
                  (pullback.fst f g ≫ X ↘ Spec (.of ℂ)) (natCast_add_sub_natCast m d)
                  ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
                      (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap g ((m + d : ℕ) : ℤ)
                    (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
                      (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ)
                      α))))))) :=
  (thomCap_chowCycleClass_flatPullbackChow_proj (fibreNormalModule f g hf) d R _).symm

end MMP.Chow
