module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThomOrientation
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThomChow
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThomExcision
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OpenRestriction

/-!
# The cone and the Thom class at infinity (Fulton, proof of Theorem 19.2)

This file proves `MMP.Chow.ConeThomAtInfinity`, the end at `∞` of the family chain of Fulton's
proof of Theorem 19.2 on Stacks' Chow groups: for an orientation class `u_x` of the trivial family
`e_W : X × 𝐏¹ ⟶ W`, the class `h^* u_x ∩ cl(C ∩ α)` for `h : W_∞ ×_Y Y' ⟶ W' ⟶ W`, read in
`H_*(X')` along `h⁻¹(e_W(X × 𝐏¹)) ⟶ X'(ℂ)`, is `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)`.

*Proof* (Fulton). The trivial family meets `W_∞ ×_Y Y'` in the vertex of the open cone
`C' = C_X Y ×_Y Y'` (`MMP.Chow.isPullback_coneTestZeroSection_comp_coneTestMap_lineFamily`), so by
excision (`MMP.borelMooreHomology.capProductSupportPullback_eq_pushforward_of_restrict`) and the
compatibility of the cycle class with open restriction (`MMP.Chow.restrict_chowCycleClass`) the cap
product only sees `j^*(C ∩ α)` on `C'`. There `h^* u_x = ψ^* u_{E'}` for the isomorphism
`ψ : C' ⟶ 𝐕(E')` (`MMP.Chow.pushforward_capProductSupportPullback_coneTestToBlowup_eq`), and the
projection formula (`MMP.Modules.pushforward_zeroSectionInvHom_capProductSupport_pushforward`)
together with `cl((ι_* ∘ j^* ∘ C) ∩ α) = ψ_* cl(j^*(C ∩ α))`
(`MMP.Chow.chowCycleClass_specializedConeClass`) gives the claim; the two readings of the
points in `H_*(X')` agree because both are the inverse of the vertex `0 : X'(ℂ) ⟶ C'(ℂ)`.

## Main results

* `MMP.Chow.coneThomAtInfinity`: `MMP.Chow.ConeThomAtInfinity` holds.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
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

attribute [local instance] isOver_lineFamily isOver_coneTestToBlowup isOver_coneTestToBundle
  isOver_coneTestZeroSection isOver_fst_infinitySection isComplexScheme_coneTestSpace
  isOver_coneTestMap isOver_testInfinityInclusion isOver_testDeformationSpace_fst
  isOver_testTrivialFamily isOver_testDeformationToLine isComplexScheme_testInfinityFibre

/-! ### Points of the vertex -/

/-- **`0(X'(ℂ)) ≅ X'(ℂ)`**: the inverse of the vertex `0 : X'(ℂ) ⟶ C'(ℂ)` of the cone on the test
scheme, on its image. -/
def coneTestVertexInvHom :
    TopCat.of (range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf))) ⟶
      TopCat.of (UnderlyingSpace ℂ (pullback f g)) :=
  TopCat.ofHom ⟨(isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
      (coneTestZeroSection f g hf)).isEmbedding.toHomeomorph.symm,
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
      (coneTestZeroSection f g hf)).isEmbedding.toHomeomorph.symm.continuous⟩

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The vertex `0 : X'(ℂ) ⟶ C'(ℂ)` sends `coneTestVertexInvHom p` back to `p`. -/
theorem map_coneTestVertexInvHom
    (p : range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf))) :
    UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf) (coneTestVertexInvHom f g hf p) =
      p :=
  congrArg Subtype.val ((isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (coneTestZeroSection f g hf)).isEmbedding.toHomeomorph.apply_symm_apply p)

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The inverse `0(X'(ℂ)) ⟶ X'(ℂ)` of the vertex is a proper map. -/
theorem isProperMap_coneTestVertexInvHom : IsProperMap (coneTestVertexInvHom f g hf) :=
  (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (coneTestZeroSection f g hf)).isEmbedding.toHomeomorph.symm.isProperMap

omit [IsComplexScheme Y] [LocallyOfFiniteType g] in
/-- **The points of `ψ⁻¹(0(X'))` read in `X'(ℂ)`** through the zero section of `𝐕(E')` and through
the vertex of the cone agree. -/
theorem zeroSectionPreimageHom_coneTestToBundle :
    zeroSectionPreimageHom (fibreNormalModule f g hf) (coneTestToBundle f g hf) =
      subsetInclusionOfSubset (preimage_range_zeroSection_coneTestToBundle_subset f g hf) ≫
        coneTestVertexInvHom f g hf := by
  refine TopCat.ext fun z => ?_
  apply (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (zeroSection (fibreNormalModule f g hf))).injective
  change UnderlyingSpace.map (K := ℂ) (zeroSection (fibreNormalModule f g hf))
      (zeroSectionHomeomorph (fibreNormalModule f g hf)
        ⟨UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf) z.1, z.2⟩) = _
  rw [map_zeroSection_zeroSectionHomeomorph]
  have key : ∀ x, UnderlyingSpace.map (K := ℂ) (zeroSection (fibreNormalModule f g hf)) x =
      UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf)
        (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf) x) := fun x ↦
    UnderlyingSpace.ext (by
      rw [toHom_map, toHom_map, toHom_map, Category.assoc,
        coneTestZeroSection_comp_coneTestToBundle])
  change _ = UnderlyingSpace.map (K := ℂ) (zeroSection (fibreNormalModule f g hf))
    (coneTestVertexInvHom f g hf ⟨z.1, _⟩)
  rw [key, map_coneTestVertexInvHom]

omit [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- `x ↦ (x, ∞)`, `Z ⟶ Z × 𝐏¹`, is a morphism over `ℂ`. -/
theorem isOver_infinitySection {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] :
    (infinitySection (Z ↘ Spec (.of ℂ))).IsOver (Spec (.of ℂ)) :=
  ⟨by
    rw [← comp_over (pullback.fst (Z ↘ Spec (.of ℂ))
      (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ)),
      ← Category.assoc, infinitySection_comp_fst, Category.id_comp]⟩

omit [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- The point `(z, ∞)` of `Z × 𝐏¹` is the image of `z` under `x ↦ (x, ∞)`. -/
theorem homeomorphProd_symm_lineInfinityComplexPoint {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (z : UnderlyingSpace ℂ Z) :
    haveI := isOver_infinitySection (Z := Z)
    (homeomorphProd Z (relativeProjectiveLine (Spec (.of ℂ)))).symm (z, lineInfinityComplexPoint) =
      UnderlyingSpace.map (K := ℂ) (infinitySection (Z ↘ Spec (.of ℂ))) z := by
  have := isOver_infinitySection (Z := Z)
  rw [Homeomorph.symm_apply_eq, homeomorphProd_apply]
  refine Prod.ext (UnderlyingSpace.ext ?_) (UnderlyingSpace.ext ?_)
  · change z.toHom = (z.toHom ≫ infinitySection _) ≫ pullback.fst _ _
    rw [Category.assoc, infinitySection_comp_fst, Category.comp_id]
  · change lineInfinitySection _ = (z.toHom ≫ infinitySection _) ≫ pullback.snd _ _
    rw [Category.assoc, infinitySection_comp_snd, ← Category.assoc, z.toHom_comp_over,
      Category.id_comp]

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- The open embedding `o(ℂ) : C'(ℂ) ⟶ (W_∞ ×_Y Y')(ℂ)` followed by `H' : W_∞ ×_Y Y' ⟶ W' ⟶ W` is
`H(ℂ)`. -/
theorem ofHom_map_coneTestMap_comp :
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf)) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g ≫ pullback.fst _ g)) =
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBlowup f g hf)) := by
  refine TopCat.ext fun z => UnderlyingSpace.ext ?_
  exact Category.assoc _ _ _

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- The points `z` of `C'(ℂ)` whose image under `H(ℂ)` lies in the trivial family `e_W(X × 𝐏¹)`
lie in the vertex `0(X'(ℂ))`. -/
theorem preimage_range_lineFamily_coneTestMap_subset :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf)) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testInfinityInclusion f g ≫ pullback.fst _ g))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      range (UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf)) := by
  rw [ofHom_map_coneTestMap_comp]
  exact (range_map_eq_preimage_of_isPullback (isPullback_coneTestZeroSection_lineFamily f g hf)).ge

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- **The support of `h^* u_x` lies in the open cone `C' ⊆ W_∞ ×_Y Y'`**: the trivial family meets
`W_∞ ×_Y Y'` in the vertex of `C'`. -/
theorem preimage_range_lineFamily_subset_opensRangeMap :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
        (testInfinityInclusion f g ≫ pullback.fst _ g))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      (opensRangeMap (coneTestMap f g hf) : Set (UnderlyingSpace ℂ (testInfinityFibre f g))) := by
  intro p hp
  have h := (range_map_eq_preimage_of_isPullback
    (isPullback_coneTestZeroSection_comp_coneTestMap_lineFamily f g hf)).ge hp
  obtain ⟨x, rfl⟩ := h
  exact ⟨UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf) x,
    UnderlyingSpace.ext (by rw [toHom_map, toHom_map, toHom_map, Category.assoc])⟩

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- **The end map of the family chain, on the cone**: a point `z` of `C'(ℂ)` with `H(z)` in the
trivial family is the vertex `0(x')`, and the end map `h⁻¹(e_W(X × 𝐏¹)) ⟶ X'(ℂ)`
(`MMP.borelMooreHomology.familyFibreProj`) sends `o(z)` to `x'`. -/
theorem restrictPreimage_comp_familyFibreProj :
    TopCat.ofHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
        (coneTestMap f g hf))).hom.restrictPreimage
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testInfinityInclusion f g ≫ pullback.fst _ g))).hom ⁻¹'
            range (UnderlyingSpace.map (K := ℂ) (lineFamily f)))) ≫
      familyFibreProj (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testDeformationToLine f g)))
        (trivialFamilyHomeomorph (testTrivialFamily f g))
        (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g))
        lineInfinityComplexPoint
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)))
        (map_testInfinityInclusion_mem f g)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
        (preimage_range_lineFamily_subset f g) _ (ofHom_map_testInfinityInclusion_comp f g) =
      subsetInclusionOfSubset (preimage_range_lineFamily_coneTestMap_subset f g hf) ≫
        coneTestVertexInvHom f g hf := by
  have := isOver_infinitySection (Z := pullback f g)
  refine TopCat.ext fun z => ?_
  set x' := coneTestVertexInvHom f g hf
    ⟨z.1, preimage_range_lineFamily_coneTestMap_subset f g hf z.2⟩
  have hx' : UnderlyingSpace.map (K := ℂ) (coneTestZeroSection f g hf) x' = z.1 :=
    map_coneTestVertexInvHom f g hf _
  have h1 := familyFibreProj_spec (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
    (T := TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
    (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
    (trivialFamilyHomeomorph (testTrivialFamily f g))
    (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g))
    lineInfinityComplexPoint
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)))
    (map_testInfinityInclusion_mem f g)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
    (preimage_range_lineFamily_subset f g) _ (ofHom_map_testInfinityInclusion_comp f g)
    ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf))).hom.restrictPreimage _ z)
  have h2 : (trivialFamilyHomeomorph (testTrivialFamily f g) (x', lineInfinityComplexPoint) :
      UnderlyingSpace ℂ (testDeformationSpace f g)) =
      UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)
        (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf) z.1) := by
    rw [coe_trivialFamilyHomeomorph, homeomorphProd_symm_lineInfinityComplexPoint, ← hx']
    refine UnderlyingSpace.ext ?_
    rw [toHom_map, toHom_map, toHom_map, toHom_map, toHom_map, Category.assoc,
      infinitySection_testTrivialFamily f g hf, Category.assoc, Category.assoc]
  have h3 := (trivialFamilyHomeomorph (testTrivialFamily f g)).injective
    (Subtype.ext (h1.trans h2.symm))
  exact congrArg Prod.fst h3

variable (R : Type) [CommRing R]

/-- **The cone and Thom class at infinity** (Fulton, proof of Theorem 19.2): for every orientation
class `u_x` of the trivial family `e_W : X × 𝐏¹ ⟶ W`, `h^* u_x ∩ cl(C ∩ α)` for
`h : W_∞ ×_Y Y' ⟶ W' ⟶ W`, read in `H_*(X')` along `h⁻¹(e_W(X × 𝐏¹)) ⟶ X'(ℂ)`, is
`u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)` read in `H_*(X')` along `0(X'(ℂ)) ≅ X'(ℂ)`. -/
theorem coneThomAtInfinity (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    ConeThomAtInfinity f g R hf m α := by
  have := isComplexScheme_blowupAtInfinity (X := Y) f.ker
  intro ux hux
  have hd' : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf)) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testInfinityInclusion f g ≫ pullback.fst _ g))) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) := by
    rw [ofHom_map_coneTestMap_comp]
    exact hasProperNeighbourhoodDeformations_preimage_range_map _ _
  have hb := (restrict_chowCycleClass R (coneTestMap f g hf)
    (gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
        (Y ↘ Spec (.of ℂ))) g ((m + d : ℕ) : ℤ)
      (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
        (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α))).symm
  have e1 := capProductSupportPullback_eq_pushforward_of_restrict R
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g ≫ pullback.fst _ g)))
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
    (hasProperNeighbourhoodDeformations_preimage_range_map (lineFamily f)
      (testInfinityInclusion f g ≫ pullback.fst _ g))
    (opensRangeMap (coneTestMap f g hf)) (preimage_range_lineFamily_subset_opensRangeMap f g hf)
    (homeomorphOpensRangeMap (coneTestMap f g hf))
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf)))
    (by intro x; exact (coe_homeomorphOpensRangeMap_apply (coneTestMap f g hf) x).symm) hd'
    ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) ux _ _ hb
  rw [e1]
  have hP2 := restrictPreimage_comp_familyFibreProj f g hf
  have hcl : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestMap f g hf)) ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
        (testInfinityInclusion f g ≫ pullback.fst _ g))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range.preimage
      (ContinuousMap.continuous _)
  have hi1 := isProperMap_subsetInclusionOfSubset hcl
    (preimage_range_lineFamily_coneTestMap_subset f g hf)
  have hq := isProperMap_coneTestVertexInvHom f g hf
  have hq1 : IsProperMap (subsetInclusionOfSubset
      (preimage_range_lineFamily_coneTestMap_subset f g hf) ≫ coneTestVertexInvHom f g hf) :=
    hq.comp hi1
  refine (pushforward_comp_apply R _ _ _ _ (hP2 ▸ hq1) _ _).trans ?_
  refine (pushforward_apply_congr R hP2 _ hq1 _ _).trans ?_
  refine (pushforward_comp_apply R _ _ hi1 hq hq1 _ _).symm.trans ?_
  refine (congrArg (pushforward R (ModuleCat.of R R) (coneTestVertexInvHom f g hf) hq _).hom
    (pushforward_capProductSupportPullback_coneTestToBlowup_eq f g hf R hux _
      (ofHom_map_coneTestMap_comp f g hf) hd' (preimage_range_lineFamily_coneTestMap_subset f g hf)
      _ _)).trans ?_
  have hi2 := isProperMap_subsetInclusionOfSubset
    (isClosed_range_zeroSection.preimage (UnderlyingSpace.map (K := ℂ) _).continuous)
    (preimage_range_zeroSection_coneTestToBundle_subset f g hf)
  have hq2 : IsProperMap (subsetInclusionOfSubset
      (preimage_range_zeroSection_coneTestToBundle_subset f g hf) ≫ coneTestVertexInvHom f g hf) :=
    hq.comp hi2
  refine (pushforward_comp_apply R _ _ hi2 hq hq2 _ _).trans ?_
  refine (pushforward_apply_congr R (zeroSectionPreimageHom_coneTestToBundle f g hf).symm hq2
    (isProperMap_zeroSectionPreimageHom _ _) _ _).trans ?_
  rw [chowCycleClass_specializedConeClass f g hf R]
  exact (pushforward_zeroSectionInvHom_capProductSupport_pushforward _ R _ _ _ _ _).symm

end MMP.Chow
