module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationTestFibres
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFamilyChain
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.DeformationNeighbourhood
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksExists

/-!
# The four inputs of the specialization step of Fulton's Theorem 19.2

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `g : Y' ⟶ Y`,
`X' = X ×_Y Y'`, and `α ∈ A_{m+d}(Y')`. Fulton's proof of the specialization step
(`MMP.Chow.SpecializationFormula`) runs the family chain
(`UnderlyingSpace.pushforward_interFibre_capProductSupportPullback_eq_of_stacksOrientationClass`)
on Stacks' deformation space on the test scheme, `ρ' : W' = W ×_Y Y' ⟶ 𝐏¹_ℂ`
(`MMP.Chow.testDeformationSpace`), with the trivial family `e : X' × 𝐏¹ ⟶ W'`, the class
`w = G^* u_x` for `G : W' ⟶ W` and an orientation class `u_x` of the trivial family
`e_W : X × 𝐏¹ ⟶ W` (`MMP.Chow.lineFamily`), and `a = cl(β)` for a lift `β ∈ A_{m+d+1}(W')` of `α`
in the sense of Stacks 0F9J (`Stacks.Chow.IsModificationLift`). This file states the four facts
the chain is read with:

* `MMP.Chow.SpecializationAtZero`: `ρ'^* u_0 ∩ cl(β) = cl(α)` on the fibre `ρ'⁻¹(0) ⊇ Y'`;
* `MMP.Chow.SpecializationAtInfinity`: `ρ'^* u_∞ ∩ cl(β) = cl(C ∩ α)` on the fibre
  `ρ'⁻¹(∞) ⊇ W_∞ ×_Y Y'`, `C ∩ α` Stacks' class at infinity (Stacks 0F9J,
  `Stacks.Chow.gysinCapAtInfinity`);
* `MMP.Chow.OrientationAtZero`: `σ^* u_x = u` for the lift `σ : Y ⟶ W` of the zero section;
* `MMP.Chow.ConeThomAtInfinity`: the end at `∞` of the chain,
  `G^* u_x ∩ cl(C ∩ α)` read in `H_*(X')`, is `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)`.

The first two are Theorem 19.2 for the effective Cartier divisors `W_0`, `W_∞ ⊆ W` (with the
refined Gysin map along `G`); the third the uniqueness of orientation classes; the fourth the
cone and Thom-class identification of Fulton's proof at `∞`.

## Main definitions

* `MMP.Chow.lineFamily`: `e_W : X × 𝐏¹ ⟶ W`.
* `MMP.Chow.SpecializationAtZero`, `MMP.Chow.SpecializationAtInfinity`,
  `MMP.Chow.OrientationAtZero`, `MMP.Chow.ConeThomAtInfinity`.
* `MMP.borelMooreHomology.familyFibreProj`: `h⁻¹(D) ⟶ X`, the end map of the family chain.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
open MMP.UnderlyingSpace MMP.borelMooreHomology
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP

namespace borelMooreHomology

variable {X T M N W : TopCat.{0}} {ρ : M ⟶ T} {A : Set M}

/-- If `G⁻¹(D) ⊆ A` and `h = G ∘ F`, then `F` maps every point of `h⁻¹(D)` into `A`. -/
lemma mem_of_mem_preimage (F : W ⟶ M) (G : M ⟶ N) {D : Set N} (hDA : G ⁻¹' D ⊆ A)
    (h : W ⟶ N) (hh : F ≫ G = h) (z : h ⁻¹' D) : F z.1 ∈ A :=
  hDA (by subst hh; exact z.2)

/-- **The end map `h⁻¹(D) ⟶ X` of the family chain**: for `F : W ⟶ M` landing in `ρ⁻¹(t)` and
`h = G ∘ F` with `G⁻¹(D) ⊆ A ≅ X × T`, the point `z` goes to the `X`-coordinate of `F z ∈ A`. -/
def familyFibreProj (φ : (X × T) ≃ₜ A) (hφ : ∀ p, ρ (φ p : M) = p.2) (t : T) (F : W ⟶ M)
    (hFt : ∀ z, ρ (F z) = t) (G : M ⟶ N) {D : Set N} (hDA : G ⁻¹' D ⊆ A) (h : W ⟶ N)
    (hh : F ≫ G = h) : TopCat.of (h ⁻¹' D) ⟶ X :=
  TopCat.ofHom ⟨fun z ↦ interFibreHomeomorph φ hφ t
      ⟨F z.1, mem_of_mem_preimage F G hDA h hh z, hFt z.1⟩,
    (interFibreHomeomorph φ hφ t).continuous.comp
      ((F.hom.continuous.comp continuous_subtype_val).subtype_mk _)⟩

/-- `φ` sends `(familyFibreProj φ hφ t F hFt G hDA h hh z, t)` to `F z`. -/
theorem familyFibreProj_spec (φ : (X × T) ≃ₜ A) (hφ : ∀ p, ρ (φ p : M) = p.2) (t : T)
    (F : W ⟶ M) (hFt : ∀ z, ρ (F z) = t) (G : M ⟶ N) {D : Set N} (hDA : G ⁻¹' D ⊆ A)
    (h : W ⟶ N) (hh : F ≫ G = h) (z : h ⁻¹' D) :
    (φ (familyFibreProj φ hφ t F hFt G hDA h hh z, t) : M) = F z.1 := by
  have := (interFibreHomeomorph φ hφ t).symm_apply_apply
    ⟨F z.1, mem_of_mem_preimage F G hDA h hh z, hFt z.1⟩
  exact congrArg Subtype.val this

/-- `familyFibreProj` is proper when `F` is a closed embedding and `D` is closed. -/
theorem isProperMap_familyFibreProj (φ : (X × T) ≃ₜ A) (hφ : ∀ p, ρ (φ p : M) = p.2) (t : T)
    (F : W ⟶ M) (hF : IsClosedEmbedding F) (hFt : ∀ z, ρ (F z) = t) (G : M ⟶ N) {D : Set N}
    (hD : IsClosed D) (hDA : G ⁻¹' D ⊆ A) (h : W ⟶ N) (hh : F ≫ G = h) :
    IsProperMap (familyFibreProj φ hφ t F hFt G hDA h hh) := by
  have hc : IsClosed (h ⁻¹' D) := hD.preimage h.hom.continuous
  have h1 : IsProperMap (fun z : h ⁻¹' D ↦
      (⟨F z.1, mem_of_mem_preimage F G hDA h hh z, hFt z.1⟩ : (A ∩ ρ ⁻¹' {t} : Set M))) :=
    isProperMap_of_comp_of_inj (g := Subtype.val)
      ((F.hom.continuous.comp continuous_subtype_val).subtype_mk _) continuous_subtype_val
      (hF.isProperMap.comp hc.isProperMap_subtypeVal) Subtype.val_injective
  exact (interFibreHomeomorph φ hφ t).isProperMap.comp h1

end borelMooreHomology

namespace Chow

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

/-! ### The trivial family on `W` -/

/-- **The trivial family `e_W : X × 𝐏¹_ℂ ⟶ W`** of Stacks 0FBG (8), on the product
`X ×_ℂ 𝐏¹_ℂ ≅ 𝐏¹_X`. -/
def lineFamily :
    pullback (X ↘ Spec (.of ℂ)) (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ)) ⟶
      blowupAtInfinity f.ker :=
  (relativeProjectiveLineIsoProjectiveLineProduct (X ↘ Spec (.of ℂ))).inv ≫
    lineToBlowupAtInfinityOfClosedImmersion f

/-- `e_W : X × 𝐏¹_ℂ ⟶ W` is a closed immersion. -/
instance isClosedImmersion_lineFamily : IsClosedImmersion (lineFamily f) := by
  rw [lineFamily]
  infer_instance

omit [Y'.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] in
omit [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `e_W` followed by `W ⟶ Y` is `X × 𝐏¹ ⟶ X ⟶ Y`. -/
@[reassoc]
theorem lineFamily_comp_blowupAtInfinityToBase :
    lineFamily f ≫ blowupAtInfinityToBase f.ker = pullback.fst _ _ ≫ f := by
  rw [lineFamily, Category.assoc, ← modificationProjection_testDeformationSpace,
    lineToBlowupAtInfinityOfClosedImmersion_modificationProjection, Iso.inv_comp_eq,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_fst_assoc]

omit [Y'.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsClosedImmersion f] in
/-- `e_W` is a morphism over `ℂ`. -/
theorem isOver_lineFamily : (lineFamily f).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change lineFamily f ≫ blowupAtInfinityToBase f.ker ≫ Y ↘ Spec (.of ℂ) = _
    rw [lineFamily_comp_blowupAtInfinityToBase_assoc, comp_over f]
    exact comp_over (pullback.fst (X ↘ Spec (.of ℂ))
      (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ))⟩

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] in
/-- The base change `𝐏¹_X ⟶ 𝐏¹_Z` along an isomorphism is an isomorphism. -/
instance isIso_projectiveLineBaseChange {Z : Scheme.{0}} (ε : X ⟶ Z) [IsIso ε] :
    IsIso (projectiveLineBaseChange ε) :=
  ⟨projectiveLineBaseChange (inv ε), by
    rw [← projectiveLineBaseChange_comp, IsIso.hom_inv_id, projectiveLineBaseChange_id],
    by rw [← projectiveLineBaseChange_comp, IsIso.inv_hom_id, projectiveLineBaseChange_id]⟩

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] in
/-- **`e_W` is regular of codimension `d` when `f` is** (Stacks 0FE9). -/
theorem isRegularClosedImmersionOfCodim_lineFamily (hf : IsRegularClosedImmersionOfCodim f d) :
    IsRegularClosedImmersionOfCodim (lineFamily f) d := by
  have h := isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity f hf
  have h' := IsRegularClosedImmersionOfCodim.iso_comp
    (asIso ((relativeProjectiveLineIsoProjectiveLineProduct (X ↘ Spec (.of ℂ))).inv ≫
      projectiveLineBaseChange f.toImage)) _ h
  simpa [lineFamily, lineToBlowupAtInfinityOfClosedImmersion] using h'

/-! ### The four inputs -/

omit [IsComplexScheme X] [LocallyOfFiniteType g] in
/-- The fibres `ρ'(ℂ)⁻¹(s)` of the deformation map on the test scheme have arbitrarily small
proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_testFibre
    (s : UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))) :
    haveI := isOver_testDeformationToLine f g
    HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)) :
        TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
          TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {s}) :=
  haveI := isComplexScheme_testDeformationSpace f g
  haveI := isOver_testTrivialFamily f g
  haveI := isOver_testDeformationToLine f g
  (UnderlyingSpace.hasProperNeighbourhoodDeformations_trivialFamily (testTrivialFamily f g)
    (testDeformationToLine f g)).2.1 s

omit [f.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y]
  [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The projection `G : W' ⟶ W` is a morphism over `ℂ`. -/
theorem isOver_testDeformationSpace_fst :
    (pullback.fst (modificationProjection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g).IsOver
        (Spec (.of ℂ)) :=
  ⟨by
    change _ ≫ blowupAtInfinityToBase f.ker ≫ Y ↘ Spec (.of ℂ) = pullback.fst _ g ≫ _ ≫ _
    rw [modificationProjection_testDeformationSpace]⟩

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [g.IsOver (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`G⁻¹(e_W(X × 𝐏¹)) ⊆ e(X' × 𝐏¹)`** on `ℂ`-points: the trivial family on the test scheme is
the base change of `e_W` (`MMP.Chow.isPullback_testLineMap`). -/
theorem preimage_range_lineFamily_subset :
    haveI := isOver_testDeformationSpace_fst f g
    haveI := isOver_lineFamily f
    haveI := isOver_testTrivialFamily f g
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)) :
        TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
          TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      range (UnderlyingSpace.map (K := ℂ) (testTrivialFamily f g)) := by
  have := isOver_testDeformationSpace_fst f g
  have := isOver_lineFamily f
  have := isOver_testTrivialFamily f g
  let := relativeProjectiveLineOver (X := pullback f g)
  let := relativeProjectiveLineOver (X := X)
  have : (projectiveLineBaseChange (pullback.fst f g)).IsOver (Spec (.of ℂ)) :=
    ⟨by
      change _ ≫ relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ) =
        relativeProjectiveLine (pullback f g) ↘ pullback f g ≫ pullback.fst f g ≫ _
      rw [projectiveLineBaseChange_over_assoc]⟩
  have : (lineToBlowupAtInfinityOfClosedImmersion f).IsOver (Spec (.of ℂ)) :=
    ⟨by
      change _ ≫ blowupAtInfinityToBase f.ker ≫ Y ↘ Spec (.of ℂ) =
        relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ)
      rw [← modificationProjection_testDeformationSpace f, ← Category.assoc,
        lineToBlowupAtInfinityOfClosedImmersion_modificationProjection, Category.assoc,
        comp_over f]⟩
  have : (testLineMap f g).IsOver (Spec (.of ℂ)) :=
    ⟨by
      change testLineMap f g ≫ pullback.fst _ g ≫ _ ≫ Y ↘ Spec (.of ℂ) =
        relativeProjectiveLine (pullback f g) ↘ pullback f g ≫ pullback.fst f g ≫ _
      rw [testLineMap_fst_assoc, ← Category.assoc (lineToBlowupAtInfinityOfClosedImmersion f),
        lineToBlowupAtInfinityOfClosedImmersion_modificationProjection, Category.assoc,
        comp_over f, ← Category.assoc, projectiveLineBaseChange_over, Category.assoc]⟩
  have : (relativeProjectiveLineIsoProjectiveLineProduct
      (pullback f g ↘ Spec (.of ℂ))).hom.IsOver (Spec (.of ℂ)) :=
    ⟨by
      rw [← comp_over (pullback.fst (pullback f g ↘ Spec (.of ℂ))
        (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ)),
        relativeProjectiveLineIsoProjectiveLineProduct_hom_fst_assoc]
      rfl⟩
  have : (relativeProjectiveLineIsoProjectiveLineProduct
      (X ↘ Spec (.of ℂ))).inv.IsOver (Spec (.of ℂ)) :=
    ⟨by
      rw [← comp_over (pullback.fst (X ↘ Spec (.of ℂ))
        (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ))]
      change _ ≫ relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ) = pullback.fst _ _ ≫ _
      rw [← Category.assoc]
      exact congrArg (· ≫ X ↘ Spec (.of ℂ)) (by
        rw [Iso.inv_comp_eq, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst])⟩
  intro p hp
  have hp' : p ∈ range (UnderlyingSpace.map (K := ℂ) (testLineMap f g)) := by
    rw [range_map_eq_preimage_of_isPullback (isPullback_testLineMap f g)]
    obtain ⟨q, hq⟩ := hp
    refine ⟨UnderlyingSpace.map (K := ℂ)
      (relativeProjectiveLineIsoProjectiveLineProduct (X ↘ Spec (.of ℂ))).inv q, ?_⟩
    exact (UnderlyingSpace.ext (by simp [lineFamily])).trans hq
  obtain ⟨q, rfl⟩ := hp'
  refine ⟨UnderlyingSpace.map (K := ℂ)
    (relativeProjectiveLineIsoProjectiveLineProduct (pullback f g ↘ Spec (.of ℂ))).hom q, ?_⟩
  exact UnderlyingSpace.ext (by simp [testTrivialFamily])

omit [Y'.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsClosedImmersion f] in
/-- **`σ⁻¹(e_W(X × 𝐏¹)) ⊆ X`** on `ℂ`-points, for the lift `σ : Y ⟶ W` of the zero section:
`e_W` lies over `X ⊆ Y` and `σ` is a section of `W ⟶ Y`. -/
theorem preimage_range_lineFamily_subset_range :
    haveI := isOver_blowupZeroSection (Y := Y) f.ker
    haveI := isOver_lineFamily f
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
        TopCat.of (UnderlyingSpace ℂ Y) ⟶
          TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      range (UnderlyingSpace.map (K := ℂ) f) := by
  have := isOver_blowupZeroSection (Y := Y) f.ker
  have := isOver_lineFamily f
  rintro y ⟨q, hq⟩
  refine ⟨UnderlyingSpace.map (K := ℂ) (pullback.fst _ _) q, UnderlyingSpace.ext ?_⟩
  have h := congrArg (fun p : UnderlyingSpace ℂ (blowupAtInfinity f.ker) ↦
    p.toHom ≫ blowupAtInfinityToBase f.ker) hq
  simp only [toHom_map, Category.assoc, lineFamily_comp_blowupAtInfinityToBase] at h
  change q.toHom ≫ pullback.fst _ _ ≫ f = y.toHom
  rw [h]
  change (y.toHom ≫ blowupZeroSection f.ker) ≫ blowupAtInfinityToBase f.ker = y.toHom
  rw [Category.assoc, blowupZeroSection_comp_blowupAtInfinityToBase, Category.comp_id]

variable (R : Type) [CommRing R]

/-- **The orientation class at zero** (Fulton, proof of Theorem 19.2): for every orientation
class `u_x` of the trivial family `e_W : X × 𝐏¹ ⟶ W` and every orientation class `u` of `f`, the
pull-back of `u_x` along the lift `σ : Y ⟶ W` of the zero section is `u`. The square
`X ⟶ X × 𝐏¹`, `Y ⟶ W` is cartesian with `X ⟶ Y` regular of the same codimension, so `σ^* u_x`
is an orientation class of `f`
(`MMP.Modules.IsRegularImbeddingOrientationClass.pullback_of_isPullback`), and orientation classes
are unique. -/
def OrientationAtZero (_hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) : Prop :=
  haveI := isOver_blowupZeroSection (Y := Y) f.ker
  haveI := isOver_lineFamily f
  ∀ ux, MMP.Modules.IsRegularImbeddingOrientationClass R (lineFamily f) d ux →
    MMP.Modules.IsRegularImbeddingOrientationClass R f d u →
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (preimage_range_lineFamily_subset_range f) _).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker))) _ _).hom ux) = u

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [X.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
omit [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `ρ'(W_∞ ×_Y Y') = ∞` on `ℂ`-points. -/
theorem map_testInfinityInclusion_mem (z : UnderlyingSpace ℂ (testInfinityFibre f g)) :
    haveI := isOver_testInfinityInclusion f g
    haveI := isOver_testDeformationToLine f g
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)) :
        TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
          TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)) :
        TopCat.of (UnderlyingSpace ℂ (testInfinityFibre f g)) ⟶
          TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g))) z) =
      lineInfinityComplexPoint :=
  haveI := isOver_testInfinityInclusion f g
  haveI := isOver_testDeformationToLine f g
  map_mem_preimage_singleton _ _ _ (testInfinityInclusion_comp_testDeformationToLine f g) z

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [f.IsOver (Spec (.of ℂ))] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The two ways of reading `W_∞ ×_Y Y' ⟶ W' ⟶ W` on `ℂ`-points agree. -/
theorem ofHom_map_testInfinityInclusion_comp :
    haveI := isOver_testInfinityInclusion f g
    haveI := isOver_testDeformationSpace_fst f g
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)) =
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
        (testInfinityInclusion f g ≫ pullback.fst _ g)) :
          TopCat.of (UnderlyingSpace ℂ (testInfinityFibre f g)) ⟶
            TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) := by
  ext z : 1
  exact UnderlyingSpace.ext (Category.assoc _ _ _)

/-- **The cone and Thom class at infinity** (Fulton, proof of Theorem 19.2, the end at `∞` of the
family chain): for every orientation class `u_x` of the trivial family `e_W`, the class
`h^* u_x ∩ cl(C ∩ α)` for `h : W_∞ ×_Y Y' ⟶ W' ⟶ W`, read in `H_*(X')` along
`h⁻¹(e_W(X × 𝐏¹)) ⟶ X'(ℂ)` (`MMP.borelMooreHomology.familyFibreProj`), is
`u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)` read in `H_*(X')` along `0(X'(ℂ)) ≅ X'(ℂ)`. Here `C ∩ α` is
Stacks' class at infinity (`Stacks.Chow.gysinCapAtInfinity`) and `(ι_* ∘ j^* ∘ C) ∩ α` the
specialization of `α` to the normal cone (`MMP.Chow.specializedConeClass`): the support of
`h^* u_x` lies in the open `C_{X}Y ×_Y Y' ⊆ W_∞ ×_Y Y'`, on which `u_x` restricts to the Thom
class of the normal bundle. -/
def ConeThomAtInfinity (hf : IsRegularClosedImmersionOfCodim f d) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) : Prop :=
  haveI := isComplexScheme_testDeformationSpace f g
  haveI := isComplexScheme_testInfinityFibre f g
  haveI := isComplexScheme_blowupAtInfinity (X := Y) f.ker
  haveI := isOver_testTrivialFamily f g
  haveI := isOver_testDeformationToLine f g
  haveI := isOver_testInfinityInclusion f g
  haveI := isOver_testDeformationSpace_fst f g
  haveI := isOver_lineFamily f
  ∀ ux, MMP.Modules.IsRegularImbeddingOrientationClass R (lineFamily f) d ux →
    (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (familyFibreProj (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
            (testDeformationToLine f g)))
          (trivialFamilyHomeomorph (testTrivialFamily f g))
          (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g))
          lineInfinityComplexPoint
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g)))
          (map_testInfinityInclusion_mem f g)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
          (preimage_range_lineFamily_subset f g) _ (ofHom_map_testInfinityInclusion_comp f g))
        (isProperMap_familyFibreProj (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
            (testDeformationToLine f g))) _ _ _ _
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (testInfinityInclusion f g)) _ _
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range _ _ _)
        (((2 * (m + d) : ℕ) : ℤ) - ((2 * d : ℕ) : ℤ))).hom
      (capProductSupportPullback R
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testInfinityInclusion f g ≫ pullback.fst _ g)))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
        (hasProperNeighbourhoodDeformations_preimage_range_map (lineFamily f)
          (testInfinityInclusion f g ≫ pullback.fst _ g))
        ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) ux
        (chowCycleClass R (m + d)
          (gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
            (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
              (Y ↘ Spec (.of ℂ))) g ((m + d : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
              (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α)))) =
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
          (zeroSectionInvHom (fibreNormalModule f g hf))
          (isProperMap_zeroSectionInvHom (fibreNormalModule f g hf)) _).hom
        (capProductSupport R _ isClosed_range_zeroSection
          (hasProperNeighbourhoodDeformations_range_zeroSection (fibreNormalModule f g hf))
          ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) (thomClass R (fibreNormalModule f g hf) d)
          (chowCycleClass R (m + d) (specializedConeClass f g hf (m + d) α)))

/-- **The specialization at zero** (Fulton, proof of Theorem 19.2): for every lift
`β ∈ A_{m+d+1}(W')` of `α ∈ A_{m+d}(Y')` (Stacks 0F9J) and every orientation class `u_0` of the
point `0` of `𝐏¹_ℂ`, `ρ'^* u_0 ∩ cl(β) = σ'_* cl(α)` in `H_{2(m+d)}(ρ'⁻¹(0))`, for the section
at zero `σ' : Y' ⟶ W'`. This is Theorem 19.2 for the effective Cartier divisor `W_0 ⊆ W` along
`W' ⟶ W`, with `i_0^* β = α` (Stacks 0F9J). -/
def SpecializationAtZero (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) : Prop :=
  haveI := isComplexScheme_testDeformationSpace f g
  haveI := isOver_testTrivialFamily f g
  haveI := isOver_testDeformationToLine f g
  haveI := isOver_testZeroSection f g
  haveI := isClosedImmersion_testZeroSection f g
  ∀ (β : chowGroup (fieldChowSituation ℂ) (testDeformationSpace f g ↘ Spec (.of ℂ))
      ((m + d + 1 : ℕ) : ℤ)),
    IsModificationLift (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
      ((m + d : ℕ) : ℤ)
      (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
        (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) β →
    ∀ u₀ : cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
        (range (UnderlyingSpace.map (K := ℂ) lineZeroComplexPoint.toHom)) (2 * 1 : ℕ),
      MMP.Modules.IsRegularImbeddingOrientationClass R lineZeroComplexPoint.toHom 1 u₀ →
      capProductSupportPullback R (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testDeformationToLine f g))) isClosed_singleton
          (hasProperNeighbourhoodDeformations_testFibre f g lineZeroComplexPoint)
          (2 * 1 : ℕ) ((2 * (m + d + 1) : ℕ) : ℤ)
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _
            (range_map_toHom lineZeroComplexPoint).le _).hom u₀)
          (chowCycleClass R (m + d + 1) β) =
        BorelMooreCross.congrDegree R _ (by push_cast; ring)
          ((pushforward R (ModuleCat.of R R)
            (fibrePointsHom (testZeroSection f g) (testDeformationToLine f g) lineZeroComplexPoint
              (testZeroSection_comp_testDeformationToLine f g))
            (isProperMap_fibrePointsHom _ _ _ _) ((2 * (m + d) : ℕ) : ℤ)).hom
            (chowCycleClass R (m + d) α))

/-- **The specialization at infinity** (Fulton, proof of Theorem 19.2): for every lift
`β ∈ A_{m+d+1}(W')` of `α ∈ A_{m+d}(Y')` (Stacks 0F9J) and every orientation class `u_∞` of the
point `∞` of `𝐏¹_ℂ`, `ρ'^* u_∞ ∩ cl(β) = cl(C ∩ α)` in `H_{2(m+d)}(ρ'⁻¹(∞))`, where
`C ∩ α = i_∞^* β ∈ A_{m+d}(W_∞ ×_Y Y')` is Stacks' class at infinity
(`Stacks.Chow.gysinCapAtInfinity`). This is Theorem 19.2 for the effective Cartier divisor
`W_∞ ⊆ W` along `W' ⟶ W`. -/
def SpecializationAtInfinity (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) : Prop :=
  haveI := isComplexScheme_testDeformationSpace f g
  haveI := isComplexScheme_testInfinityFibre f g
  haveI := isOver_testTrivialFamily f g
  haveI := isOver_testDeformationToLine f g
  haveI := isOver_testInfinityInclusion f g
  ∀ (β : chowGroup (fieldChowSituation ℂ) (testDeformationSpace f g ↘ Spec (.of ℂ))
      ((m + d + 1 : ℕ) : ℤ)),
    IsModificationLift (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
      ((m + d : ℕ) : ℤ)
      (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
        (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) β →
    ∀ u₁ : cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
        (range (UnderlyingSpace.map (K := ℂ) lineInfinityComplexPoint.toHom)) (2 * 1 : ℕ),
      MMP.Modules.IsRegularImbeddingOrientationClass R lineInfinityComplexPoint.toHom 1 u₁ →
      capProductSupportPullback R (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (testDeformationToLine f g))) isClosed_singleton
          (hasProperNeighbourhoodDeformations_testFibre f g lineInfinityComplexPoint)
          (2 * 1 : ℕ) ((2 * (m + d + 1) : ℕ) : ℤ)
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _
            (range_map_toHom lineInfinityComplexPoint).le _).hom u₁)
          (chowCycleClass R (m + d + 1) β) =
        BorelMooreCross.congrDegree R _ (by push_cast; ring)
          ((pushforward R (ModuleCat.of R R)
            (fibrePointsHom (testInfinityInclusion f g) (testDeformationToLine f g)
              lineInfinityComplexPoint (testInfinityInclusion_comp_testDeformationToLine f g))
            (isProperMap_fibrePointsHom _ _ _ _) ((2 * (m + d) : ℕ) : ℤ)).hom
            (chowCycleClass R (m + d)
              (gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
                (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
                (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
                  (Y ↘ Spec (.of ℂ))) g ((m + d : ℕ) : ℤ)
                (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
                  (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α))))

end Chow

end MMP
