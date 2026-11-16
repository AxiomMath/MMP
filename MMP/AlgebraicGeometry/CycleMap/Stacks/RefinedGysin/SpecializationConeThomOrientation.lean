module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThomSpace
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksTransport
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSection

/-!
# The orientation class of the trivial family on the cone at `∞`

In Fulton's proof of Theorem 19.2, at the end at `∞` of the family chain: let `u_x` be an
orientation class of the trivial family `e_W : X × 𝐏¹ ⟶ W` (`MMP.Chow.lineFamily`), and `u_{E'}`
the Thom class of `E'`. On the cone `C' = C_X Y ×_Y Y'` of the test scheme
(`MMP.Chow.coneTestSpace`), the pull-back of `u_x` along `H : C' ⟶ W_∞ ×_Y Y' ⟶ W' ⟶ W` and the
pull-back of `u_{E'}` along the isomorphism `ψ : C' ⟶ 𝐕(E')` are both orientation classes of the
vertex `0 : X' ⟶ C'`: the squares `X' = C' ×_W (X × 𝐏¹)` and `X' = C' ×_{𝐕(E')} X'` are cartesian
(`MMP.Chow.isPullback_coneTestZeroSection_lineFamily`,
`MMP.Chow.isPullback_coneTestZeroSection_coneTestToBundle`) and the vertex is regular of
codimension `d`. By the uniqueness of orientation classes they agree.

## Main results

* `MMP.Chow.forget_pullback_orientationClass_eq_thomClass`: `H^* u_x = ψ^* u_{E'}` in
  `H^{2d}(C', C' - 0(X'))`.
* `MMP.Chow.pushforward_capProductSupportPullback_coneTestToBlowup_eq`: the corresponding equality
  of cap products, pushed into `H_*(0(X'))`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules MMP.UnderlyingSpace MMP.borelMooreHomology

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule
  coneTestSpaceOver

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (hf : IsRegularClosedImmersionOfCodim f d)

/-- **The map `H : C' ⟶ W_∞ ×_Y Y' ⟶ W' ⟶ W`** from the cone on the test scheme. -/
abbrev coneTestToBlowup : coneTestSpace f g hf ⟶ blowupAtInfinity f.ker :=
  coneTestMap f g hf ≫ testInfinityInclusion f g ≫ pullback.fst _ g

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- `H : C' ⟶ W` is a morphism over `ℂ`. -/
theorem isOver_coneTestToBlowup : (coneTestToBlowup f g hf).IsOver (Spec (.of ℂ)) :=
  haveI := isOver_coneTestMap f g hf
  haveI := isOver_testInfinityInclusion f g
  haveI := isOver_testDeformationSpace_fst f g
  inferInstance

omit [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `x ↦ (x, ∞)`, `X' ⟶ X ⟶ X × 𝐏¹`, is a morphism over `ℂ`. -/
theorem isOver_fst_infinitySection :
    (pullback.fst f g ≫ infinitySection (X ↘ Spec (.of ℂ))).IsOver (Spec (.of ℂ)) :=
  ⟨by
    rw [← comp_over (pullback.fst (X ↘ Spec (.of ℂ))
      (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ)), Category.assoc,
      ← Category.assoc (infinitySection _), infinitySection_comp_fst, Category.id_comp]
    rfl⟩

attribute [local instance] isOver_lineFamily isOver_coneTestToBlowup isOver_coneTestToBundle
  isOver_coneTestZeroSection isOver_fst_infinitySection isComplexScheme_coneTestSpace

variable (R : Type) [CommRing R]

/-- **The orientation class of the trivial family on the cone is the pulled-back Thom class**
(Fulton, proof of Theorem 19.2): for an orientation class `u_x` of `e_W : X × 𝐏¹ ⟶ W`,
`H^* u_x = ψ^* u_{E'}` in `H^{2d}(C', C' - 0(X'))`, both being orientation classes of the vertex
`0 : X' ⟶ C'` (`MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq`). -/
theorem forget_pullback_orientationClass_eq_thomClass
    {ux : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
      (range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) (2 * d : ℕ)}
    (hux : MMP.Modules.IsRegularImbeddingOrientationClass R (lineFamily f) d ux) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback
          (isPullback_coneTestZeroSection_lineFamily f g hf)).ge _).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBlowup f g hf))) _ _).hom ux) =
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (range_map_eq_preimage_of_isPullback
          (isPullback_coneTestZeroSection_coneTestToBundle f g hf)).ge _).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf))) _ _).hom
          (thomClass R (fibreNormalModule f g hf) d)) := by
  have h0 := isRegularClosedImmersionOfCodim_coneTestZeroSection f g hf
  have h1 := MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback R
    (isRegularClosedImmersionOfCodim_zeroSection (fibreNormalModule f g hf) d) h0
    (isPullback_coneTestZeroSection_coneTestToBundle f g hf)
    (MMP.Modules.isRegularImbeddingOrientationClass_thomClass (fibreNormalModule f g hf) d R)
  exact MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq R
    (isRegularClosedImmersionOfCodim_lineFamily f hf) h0
    (isPullback_coneTestZeroSection_lineFamily f g hf) hux h1

omit [IsComplexScheme Y] [LocallyOfFiniteType g] [IsComplexScheme Y'] in
omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- `0(X') = ψ⁻¹(0(X'))` in `C'(ℂ)`: the support of `ψ^* u_{E'}` is the vertex of the cone. -/
theorem preimage_range_zeroSection_coneTestToBundle_subset :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (zeroSection (fibreNormalModule f g hf))) ⊆
      range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf)) :=
  (range_map_eq_preimage_of_isPullback
    (isPullback_coneTestZeroSection_coneTestToBundle f g hf)).ge

omit [LocallyOfFiniteType g] [IsComplexScheme Y] in
/-- The vertex `0(X')` of the cone has arbitrarily small proper neighbourhood deformations in
`C'(ℂ)`. -/
theorem hasProperNeighbourhoodDeformations_range_coneTestZeroSection :
    HasProperNeighbourhoodDeformations
      (range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf))) := by
  rw [range_map_eq_preimage_of_isPullback (isPullback_coneTestZeroSection_coneTestToBundle f g hf)]
  exact hasProperNeighbourhoodDeformations_preimage_range_zeroSection _ _

/-- **The cap products with `H^* u_x` and `ψ^* u_{E'}` agree on the vertex of the cone**
(Fulton, proof of Theorem 19.2): for an orientation class `u_x` of the trivial family and any
`b ∈ H_k(C'(ℂ))`, `H^* u_x ∩ b` and `ψ^* u_{E'} ∩ b`, pushed forward into `H_{k-2d}(0(X'))`,
are equal. Here `F` is any map of spaces equal to `H(ℂ)`. -/
theorem pushforward_capProductSupportPullback_coneTestToBlowup_eq
    {ux : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
      (range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) (2 * d : ℕ)}
    (hux : MMP.Modules.IsRegularImbeddingOrientationClass R (lineFamily f) d ux)
    (F : TopCat.of (UnderlyingSpace ℂ (coneTestSpace f g hf)) ⟶
      TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
    (hF : F = TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBlowup f g hf)))
    (hdF : HasProperNeighbourhoodDeformations
      (F ⁻¹' range (UnderlyingSpace.map (K := ℂ) (lineFamily f))))
    (hS : F.hom ⁻¹' range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf)))
    (k : ℤ) (b : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (coneTestSpace f g hf))) k) :
    (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hS)
        (isProperMap_subsetInclusionOfSubset
          ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
            (lineFamily f)).isClosed_range.preimage F.hom.continuous) hS)
        (k - ((2 * d : ℕ) : ℤ))).hom
      (capProductSupportPullback R F
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range hdF
        ((2 * d : ℕ) : ℤ) k ux b) =
    (pushforward R (ModuleCat.of R R)
        (subsetInclusionOfSubset (preimage_range_zeroSection_coneTestToBundle_subset f g hf))
        (isProperMap_subsetInclusionOfSubset
          (isClosed_range_zeroSection.preimage (UnderlyingSpace.map (K := ℂ) _).continuous)
          (preimage_range_zeroSection_coneTestToBundle_subset f g hf))
        (k - ((2 * d : ℕ) : ℤ))).hom
      (capProductSupportPullback R
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf)))
        isClosed_range_zeroSection
        (hasProperNeighbourhoodDeformations_preimage_range_zeroSection _ _)
        ((2 * d : ℕ) : ℤ) k (thomClass R (fibreNormalModule f g hf) d) b) := by
  subst hF
  have hR := hasProperNeighbourhoodDeformations_range_coneTestZeroSection f g hf
  have hRc : IsClosed (range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf))) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) _).isClosed_range
  rw [capProductSupportPullback_apply, capProductSupportPullback_apply,
    pushforward_subsetInclusionOfSubset_capProductSupport R _ _ hRc _ hR,
    pushforward_subsetInclusionOfSubset_capProductSupport R _ _ hRc _ hR]
  exact congrArg (fun c ↦ capProductSupport R _ hRc hR _ k c b)
    (forget_pullback_orientationClass_eq_thomClass f g hf R hux)

end MMP.Chow
