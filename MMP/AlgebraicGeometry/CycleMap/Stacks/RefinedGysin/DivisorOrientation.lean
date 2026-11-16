module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksGlue
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainZeroSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange
public import MMP.AlgebraicGeometry.Analytic.DivisorOrientationDatum
public import MMP.AlgebraicGeometry.RegularImmersion.CodimOne
public import MMP.AlgebraicGeometry.Chow.FirstChernClassTopNaturalGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric

/-!
# The orientation class of the zero scheme of a section (Fulton, §19.2)

Let `ℰ` be a quasi-coherent `𝒪_Y`-module, finite locally free of rank `r`, on a complex scheme `Y`,
with vector bundle `π : 𝐕(ℰ) ⟶ Y` and zero section `0 : Y ⟶ 𝐕(ℰ)`, and let `σ : Y ⟶ 𝐕(ℰ)` be a
section. If a closed immersion `f : X ⟶ Y` has ideal sheaf the zero scheme `Z(σ) = σ⁻¹(0(Y))`
(`MMP.Modules.zeroLocus`), then `X` is the fibre product of `σ` and the zero section, and when `f`
is regular of codimension `r` its orientation class is the pull-back `σ^* u_ℰ` of the Thom class.

## Main results

* `MMP.Chow.isPullback_zeroLocus_zeroSection`: `X = Y ×_{σ, 𝐕(ℰ), 0} Y`.
* `MMP.Chow.eq_forget_pullback_thomClass`: the orientation class of `f` is `σ^* u_ℰ`.
* `MMP.Chow.exists_zeroLocus_globalSectionMap_eq_ker`: a regular closed immersion `f` of
  codimension one is the zero scheme of a section of an invertible module: `1_D ∈ Γ(𝒪_Y(D))`
  for `D = ker f` (`MMP.Topology.zeroLocus_canonicalSectionMap`).
* `MMP.Chow.isPullback_canonicalSectionMap_ker`, `MMP.Chow.comp_canonicalSectionMap_ker`:
  `X = Y ×_{σ_D, 𝐕(𝒪_Y(D)^∨), 0} Y`, so `σ_D ∘ f = 0 ∘ f`.
* `MMP.Chow.eq_forget_pullback_thomClass_canonicalSectionMap`: the orientation class of a
  divisor `f` is `σ_D^* u_{𝒪_Y(D)^∨}`.
* `MMP.Chow.forget_pullback_eq_topFirstChernClass`: its restriction `f^* u` to `X`, read in
  `H²(X(ℂ))`, is `c₁ᵗᵒᵖ(f^* 𝒪_Y(D)^∨)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2 and Appendix B.3.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf MMP.Modules

namespace MMP.Chow

/-! ### The orientation class of the zero scheme of a section -/

section Orientation

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- **The zero scheme of a section is the fibre product with the zero section**: if the closed
immersion `f : X ⟶ Y` has ideal sheaf `Z(σ)`, then `X = Y ×_{σ, 𝐕(ℰ), 0} Y`. -/
theorem isPullback_zeroLocus_zeroSection {E : Y.Modules} [E.IsQuasicoherent]
    (σ : Y ⟶ totalSpace E) (hσ : σ ≫ proj E = 𝟙 Y) (h : zeroLocus E σ = f.ker) :
    IsPullback f f σ (zeroSection E) := by
  refine isPullback_of_isClosedImmersion f (zeroSection E) f σ ?_ h
  have hker : (pullback.fst σ (zeroSection E)).ker ≤ f.ker := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← h]
    exact le_rfl
  have hsnd : pullback.snd σ (zeroSection E) = pullback.fst σ (zeroSection E) := by
    rw [← Category.comp_id (pullback.snd σ (zeroSection E)), ← zeroSection_proj E,
      ← Category.assoc, ← pullback.condition, Category.assoc, hσ, Category.comp_id]
  rw [← IsClosedImmersion.lift_fac _ f hker, Category.assoc, Category.assoc, pullback.condition,
    hsnd]

variable [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]

/-- **The orientation class of the zero scheme of a section is the pulled-back Thom class**
(Fulton, §19.2): for a regular closed immersion `f` of codimension `r` which is the zero scheme
of a section `σ` of a rank `r` bundle `ℰ`, every orientation class of `f` is `σ^* u_ℰ`. -/
theorem eq_forget_pullback_thomClass (R : Type) [CommRing R] [IsComplexScheme Y] {r : ℕ}
    (hf : IsRegularClosedImmersionOfCodim f r) {E : Y.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]
    (σ : Y ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 Y)
    (h : zeroLocus E σ = f.ker)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * r : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f r u) :
    u = (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback (isPullback_zeroLocus_zeroSection f σ hσ h)).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) _ _).hom (thomClass R E r)) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  exact MMP.Modules.IsRegularImbeddingOrientationClass.eq R hf hu
    (MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback R
      (isRegularClosedImmersionOfCodim_zeroSection E r) hf
      (isPullback_zeroLocus_zeroSection f σ hσ h)
      (isRegularImbeddingOrientationClass_thomClass E r R))

end Orientation

/-! ### Divisors: the canonical section of `𝒪_Y(D)` -/

section Divisor

open MMP.Topology

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- **A regular closed immersion of codimension one is the zero scheme of a section of an
invertible module**: `ℒ = 𝒪_Y(D)` and `s = 1_D` for `D = ker f`. -/
theorem exists_zeroLocus_globalSectionMap_eq_ker (hf : IsRegularClosedImmersionOfCodim f 1) :
    ∃ (L : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y L) (s : Γ(L, ⊤)),
      zeroLocus (Scheme.Modules.dual L) (globalSectionMap L s) = f.ker := by
  have := isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one f hf
  exact ⟨_, inferInstance, _, zeroLocus_canonicalSectionMap f.ker⟩

variable [Stacks.Divisors.IsEffectiveCartierDivisor f.ker]

/-- **A divisor is the fibre product of its canonical section with the zero section**:
`X = Y ×_{σ_D, 𝐕(𝒪_Y(D)^∨), 0} Y` for `D = ker f`. -/
theorem isPullback_canonicalSectionMap_ker :
    IsPullback f f (canonicalSectionMap f.ker) (zeroSection (divisorDualSheaf f.ker)) :=
  isPullback_zeroLocus_zeroSection f _ (canonicalSectionMap_proj f.ker)
    (zeroLocus_canonicalSectionMap f.ker)

/-- The canonical section `σ_D` agrees with the zero section on the divisor `D = ker f`. -/
@[reassoc]
theorem comp_canonicalSectionMap_ker :
    f ≫ canonicalSectionMap f.ker = f ≫ zeroSection (divisorDualSheaf f.ker) :=
  (isPullback_canonicalSectionMap_ker f).w

variable [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]

/-- **The orientation class of a divisor is the pulled-back Thom class of its line bundle**
(Fulton, §19.2): for a regular closed immersion `f` of codimension one with divisor `D = ker f`,
every orientation class of `f` is `σ_D^* u_{𝒪_Y(D)^∨}`. -/
theorem eq_forget_pullback_thomClass_canonicalSectionMap (R : Type) [CommRing R]
    [IsComplexScheme Y] (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u) :
    u = (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback (isPullback_canonicalSectionMap_ker f)).ge _).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (canonicalSectionMap f.ker))) _ _).hom
          (thomClass R (divisorDualSheaf f.ker) 1)) :=
  eq_forget_pullback_thomClass f R hf _ (canonicalSectionMap_proj f.ker)
    (zeroLocus_canonicalSectionMap f.ker) hu

/-- **The orientation class of a divisor restricts to the first Chern class of its normal
bundle**: for a divisor `f : X ⟶ Y` with orientation class `u`, the image of `f^* u` in
`H²(X(ℂ))` is `c₁ᵗᵒᵖ(f^* 𝒪_Y(D)^∨)`, `D = ker f`. -/
theorem forget_pullback_eq_topFirstChernClass (R : Type) [CommRing R] [IsComplexScheme Y]
    (hf : IsRegularClosedImmersionOfCodim f 1)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f 1 u) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
        (subset_univ _) _).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) _ _).hom u) =
      topFirstChernClass R ((Scheme.Modules.pullback f).obj (divisorDualSheaf f.ker)) := by
  rw [eq_forget_pullback_thomClass_canonicalSectionMap f R hf hu,
    ← pullback_topFirstChernClass, topFirstChernClass]
  simp only [cohomologyWithSupports.pullback, cohomologyWithSupports.forget]
  have he (A : Set (TopCat.of (UnderlyingSpace ℂ X))) :
      (univ : Set (TopCat.of (UnderlyingSpace ℂ X)))ᶜ ⊆ A := fun _ hx ↦ (hx trivial).elim
  refine ((relativeSingularCohomology.map_hom_comp_apply R _ _ _ _ (he _) _ _).symm.trans
    ?_).trans (relativeSingularCohomology.map_hom_comp_apply R _ _ _ _ (he _) _ _)
  refine ((relativeSingularCohomology.map_hom_comp_apply R _ _ _ _ (he _) _ _).symm.trans ?_)
  refine ((relativeSingularCohomology.map_hom_comp_apply R _ _ _ _ (he _) _ _).symm.trans ?_)
  refine congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (relativeSingularCohomology.map_eq_map_of_hom_eq R ?_ _ _ _)
  refine ConcreteCategory.hom_ext _ _ fun p ↦ UnderlyingSpace.ext ?_
  simp [zeroSectionHom, toHom_map, comp_canonicalSectionMap_ker]

end Divisor

end MMP.Chow
