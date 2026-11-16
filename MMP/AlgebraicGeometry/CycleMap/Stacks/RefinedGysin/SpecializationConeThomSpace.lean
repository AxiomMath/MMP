module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationSteps
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.VectorBundleIso
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleChangeOfCentre

/-!
# The normal cone on the test scheme, at the end at `∞` of Fulton's proof of Theorem 19.2

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes with normal
bundle `N = 𝐕(𝒩^∨)` (`MMP.Chow.normalBundleOfRegular`), `g : Y' ⟶ Y` and `X' = X ×_Y Y'`. Stacks'
construction of the Gysin class restricts the class at infinity `C ∩ α` on `W_∞ ×_Y Y'` to the open
`C' = C_X Y ×_Y Y'` (`Stacks.Chow.normalConeTestMap`, the base change of the open immersion
`j : C_X Y ⟶ W_∞` of Stacks 0FBH) and pushes it forward along `C' ⟶ N ×_Y Y' ≅ 𝐕(E')`. This file
sets up the scheme `C'` and its maps:

* `MMP.Chow.coneTestSpace`: `C' = C_X Y ×_Y Y'`, a scheme over `ℂ` through `C' ⟶ C_X Y ⟶ X`;
* `MMP.Chow.coneTestMap`: the open immersion `o : C' ⟶ W_∞ ×_Y Y'`;
* `MMP.Chow.coneTestToBundle`: `ψ : C' ⟶ N ×_Y Y' ≅ 𝐕(E')`, an isomorphism since `C_X Y ⟶ N` is one
  for a regular immersion (Stacks 063M);
* `MMP.Chow.coneTestZeroSection`: the vertex `0 : X' ⟶ C'` of the cone.

It proves the two cartesian squares through which the orientation class of the trivial family and
the Thom class of `E'` are compared on `C'`:

* `MMP.Chow.coneTestZeroSection_comp_coneTestToBundle`: `ψ ∘ 0 = 0_{E'}`, so
  `X' = C' ×_{𝐕(E')} X'` (`MMP.Chow.isPullback_coneTestZeroSection_coneTestToBundle`);
* `MMP.Chow.isPullback_coneTestZeroSection_lineFamily`: `X' = C' ×_W (X × 𝐏¹)` for the map
  `C' ⟶ W_∞ ×_Y Y' ⟶ W' ⟶ W` and the trivial family `e_W : X × 𝐏¹ ⟶ W` (`MMP.Chow.lineFamily`),
  `X' ⟶ X × 𝐏¹` being `x ↦ (x, ∞)`; this is Stacks 0FE9 (the base change of `𝐏¹_X ⟶ W` by `∞`
  is the vertex of the cone) base-changed to `Y'`;

and that the vertex is a regular closed immersion of codimension `d`. On the way it identifies the
zero section `vectorBundleLiftZero` of Stacks' universal property of `𝐕(ℱ)` with the zero section
`vectorBundleZeroSection` (`MMP.Chow.vectorBundleLiftZero_eq_zeroSection`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow Opposite
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

/-! ### The two zero sections of a vector bundle -/

/-- The zero section `vectorBundleLiftZeroOver` of the universal property of `𝐕(ℱ)` has module
morphism `0`. -/
theorem vectorBundleHomEquiv_vectorBundleLiftZeroOver {X : Scheme.{0}} (F : X.Modules)
    [F.IsQuasicoherent] :
    Scheme.Modules.vectorBundleHomEquiv F _ (Scheme.Modules.vectorBundleLiftZeroOver F) =
      (0 : F ⟶ Scheme.Modules.structurePushforward (𝟙 X)) := by
  have hB : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => U.1) := by
    simpa using X.isBasis_affineOpens
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis hB fun U s => ?_
  have hf := Scheme.Modules.vectorBundleHomEquiv_apply F (Over.mk (𝟙 X))
    (Scheme.Modules.vectorBundleLiftZeroOver F)
  refine (congrArg (fun φ : F ⟶ Scheme.Modules.structurePushforward (𝟙 X) => (φ.app U.1).hom s)
    hf).trans ?_
  have h2 : Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
      (Scheme.Modules.vectorBundleLiftZeroOver F) = _ :=
    Scheme.Modules.pushforwardAlgebraMap_vectorBundleLift F _
  rw [h2, Iso.inv_hom_id_assoc]
  change ((Stacks.SymAlgSheaf.algebraLift _ F _).right.hom.app (op U.1)).hom
    (((Scheme.Modules.symmetricAlgebraSheafComparison F).hom.right.hom.app (op U.1)).hom
      (Stacks.RelativeSpec.ungradedAlgebraSheafIncl X _ _ 1 U.1
        ((Scheme.Modules.symmetricAlgebraGen X F).val.app (op U.1) s))) = _
  rw [Stacks.Chow.ProjectiveCompletion.symmetricAlgebraSheafComparison_hom_ungradedAlgebraSheafIncl]
  erw [Stacks.SymAlgSheaf.algebraLift_ungradedIncl_gen]
  rfl

/-- **The two zero sections of `𝐕(ℱ)` agree**: the zero section `vectorBundleLiftZero` of the
universal property (the morphism with classifying map `0`) is the zero section
`vectorBundleZeroSection` cut out by the augmentation. -/
theorem vectorBundleLiftZero_eq_zeroSection {X : Scheme.{0}} (F : X.Modules) [F.IsQuasicoherent] :
    Scheme.Modules.vectorBundleLiftZero F = MMP.Modules.zeroSection F := by
  have h : Scheme.Modules.vectorBundleLiftZeroOver F =
      Scheme.Modules.vectorBundleOverZeroSection F :=
    (Scheme.Modules.vectorBundleHomEquiv F _).injective
      ((vectorBundleHomEquiv_vectorBundleLiftZeroOver F).trans
        (Scheme.Modules.vectorBundleHomEquiv_vectorBundleOverZeroSection F).symm)
  exact (congrArg CommaMorphism.left h).trans
    (Scheme.Modules.vectorBundleOverZeroSection_left F)

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) (g : Y' ⟶ Y) [IsClosedImmersion f] [IsComplexScheme X]
  {d : ℕ} (hf : IsRegularClosedImmersionOfCodim f d)

/-! ### The normal cone on the test scheme -/

/-- **The normal cone on the test scheme**, `C' = C_X Y ×_Y Y'`, with `C_X Y ⟶ Y` written as
`C_X Y ⟶ N ⟶ X ⟶ Y`: the open subscheme of `W_∞ ×_Y Y'` to which Stacks' construction of the
Gysin class restricts the class at infinity (`Stacks.Chow.normalConeTestMap`). -/
abbrev coneTestSpace : Scheme.{0} :=
  pullback ((normalBundleOfRegular f hf).normalConeEmbedding ≫
    (normalBundleOfRegular f hf).projection ≫ f) g

/-- `C'` over `ℂ`, through `C' ⟶ C_X Y ⟶ X`: the structure morphism of its Chow groups in
Stacks' construction. -/
abbrev coneTestSpaceOver : (coneTestSpace f g hf).Over (Spec (.of ℂ)) :=
  ⟨pullback.fst _ g ≫ Stacks.Conormal.normalConeToBase f ≫ X ↘ Spec (.of ℂ)⟩

attribute [local instance] coneTestSpaceOver

/-- **The open immersion `o : C' ⟶ W_∞ ×_Y Y'`**, the base change of `j : C_X Y ⟶ W_∞` (Stacks
0FBH). -/
abbrev coneTestMap : coneTestSpace f g hf ⟶ testInfinityFibre f g :=
  normalConeTestMap (Y ↘ Spec (.of ℂ)) f (normalBundleOfRegular f hf) g

/-- `o : C' ⟶ W_∞ ×_Y Y'` is an open immersion. -/
instance isOpenImmersion_coneTestMap : IsOpenImmersion (coneTestMap f g hf) := by
  unfold coneTestMap normalConeTestMap
  infer_instance

omit [Y'.Over (Spec (.of ℂ))] in
/-- `o : C' ⟶ W_∞ ×_Y Y'` followed by `W_∞ ×_Y Y' ⟶ W_∞` is `C' ⟶ C_X Y ⟶ W_∞`. -/
@[reassoc]
theorem coneTestMap_fst :
    coneTestMap f g hf ≫ pullback.fst _ g =
      pullback.fst _ g ≫ normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ)) :=
  pullback.lift_fst _ _ _

omit [Y'.Over (Spec (.of ℂ))] in
/-- `o : C' ⟶ W_∞ ×_Y Y'` is a morphism over `Y'`. -/
@[reassoc]
theorem coneTestMap_snd :
    coneTestMap f g hf ≫ pullback.snd _ g = pullback.snd _ g := by
  simp [coneTestMap, normalConeTestMap]

variable [f.IsOver (Spec (.of ℂ))]

omit [Y'.Over (Spec (.of ℂ))] in
/-- `o : C' ⟶ W_∞ ×_Y Y'` is a morphism over `ℂ`. -/
theorem isOver_coneTestMap : (coneTestMap f g hf).IsOver (Spec (.of ℂ)) :=
  ⟨normalConeTestMap_comp_structureMorphism (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
    (comp_over f _) (normalBundleOfRegular f hf) g⟩

omit [f.IsOver (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] in
/-- **The map `C' ⟶ W_∞ ×_Y Y' ⟶ W' ⟶ W`** is `C' ⟶ C_X Y ⟶ W_∞ ⟶ W`. -/
@[reassoc]
theorem coneTestMap_testInfinityInclusion_fst :
    coneTestMap f g hf ≫ testInfinityInclusion f g ≫ pullback.fst _ g =
      pullback.fst _ g ≫ normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ)) ≫
        modificationInclusionAtInfinity (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) := by
  rw [modificationInfinityBaseChange_comp_fst, coneTestMap_fst_assoc]

/-- The base change `C' ⟶ N ×_Y Y'` of `ι : C_X Y ⟶ N`, with `N ⟶ X` written as
`vectorBundleToBase` (`Stacks.Chow.bivariantPushforwardBaseChange`, read on the source of
`MMP.Chow.fibreNormalConeIso`). -/
def coneTestToBundleBase : coneTestSpace f g hf ⟶
    pullback (Scheme.Modules.vectorBundleToBase X
      (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g :=
  pullback.map _ g _ g (normalBundleOfRegular f hf).normalConeEmbedding (𝟙 Y') (𝟙 Y)
    (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- `C' ⟶ N ×_Y Y'` followed by `N ×_Y Y' ⟶ N` is `C' ⟶ C_X Y ⟶ N`. -/
@[reassoc (attr := simp)]
theorem coneTestToBundleBase_fst :
    coneTestToBundleBase f g hf ≫ pullback.fst _ g =
      pullback.fst _ g ≫ (normalBundleOfRegular f hf).normalConeEmbedding :=
  pullback.lift_fst _ _ _

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- `C' ⟶ N ×_Y Y'` is a morphism over `Y'`. -/
@[reassoc (attr := simp)]
theorem coneTestToBundleBase_snd :
    coneTestToBundleBase f g hf ≫ pullback.snd _ g = pullback.snd _ g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- `coneTestToBundleBase` is Stacks' base change of `ι` along the test scheme. -/
theorem coneTestToBundleBase_eq :
    coneTestToBundleBase f g hf = bivariantPushforwardBaseChange
      (normalBundleOfRegular f hf).normalConeEmbedding
      ((normalBundleOfRegular f hf).projection ≫ f) g :=
  rfl

omit [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- `ι : C_X Y ⟶ N` followed by `N ⟶ X`, written as `vectorBundleToBase`, is `C_X Y ⟶ X`. -/
theorem normalConeEmbedding_vectorBundleToBase :
    (normalBundleOfRegular f hf).normalConeEmbedding ≫
        Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) =
      Stacks.Conormal.normalConeToBase f :=
  (normalBundleOfRegular f hf).normalConeEmbedding_projection

omit [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- `ι : C_X Y ⟶ N` followed by `N ⟶ X` and then `h : X ⟶ Z` is `C_X Y ⟶ X ⟶ Z`. -/
theorem normalConeEmbedding_vectorBundleToBase_assoc {Z : Scheme.{0}} (h : X ⟶ Z) :
    (normalBundleOfRegular f hf).normalConeEmbedding ≫
        Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ h =
      Stacks.Conormal.normalConeToBase f ≫ h :=
  (Category.assoc (normalBundleOfRegular f hf).normalConeEmbedding
    (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle))
      h).symm.trans
    (congrArg (· ≫ h) (normalConeEmbedding_vectorBundleToBase f hf))

/-- **`ψ : C' ⟶ N ×_Y Y' ≅ 𝐕(E')`**, the base change of `ι : C_X Y ⟶ N` followed by
`N ×_Y Y' ≅ 𝐕(E')` (`MMP.Chow.fibreNormalConeIso`). -/
def coneTestToBundle : coneTestSpace f g hf ⟶ totalSpace (fibreNormalModule f g hf) :=
  coneTestToBundleBase f g hf ≫ (fibreNormalConeIso f g hf).hom

/-- **`ψ` is an isomorphism**: `ι : C_X Y ⟶ N` is one for the regular immersion `f` (Stacks 063M,
`Stacks.Chow.VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion`). -/
instance isIso_coneTestToBundle : IsIso (coneTestToBundle f g hf) := by
  have : IsIso (normalBundleOfRegular f hf).normalConeEmbedding :=
    VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hf.isRegularImmersion
  have h1 := isIso_bivariantPushforwardBaseChange_normalConeEmbedding f g
    (normalBundleOfRegular f hf)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (fibreNormalConeIso f g hf).isIso_hom

variable [g.IsOver (Spec (.of ℂ))]

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- `ψ` followed by `𝐕(E') ⟶ ℂ` is the structure morphism of `C'`. -/
theorem coneTestToBundle_comp_over :
    coneTestToBundle f g hf ≫ totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ) =
      pullback.fst _ g ≫ Stacks.Conormal.normalConeToBase f ≫ X ↘ Spec (.of ℂ) := by
  refine (Category.assoc (coneTestToBundleBase f g hf) _ _).trans ?_
  refine (congrArg (coneTestToBundleBase f g hf ≫ ·)
    (fibreNormalConeIso_hom_comp_over f g hf)).trans ?_
  refine (Category.assoc (coneTestToBundleBase f g hf) (pullback.fst _ g) _).symm.trans ?_
  refine (congrArg (· ≫ _) (coneTestToBundleBase_fst f g hf)).trans ?_
  refine (Category.assoc (pullback.fst _ g) (normalBundleOfRegular f hf).normalConeEmbedding
    _).trans ?_
  exact congrArg (pullback.fst _ g ≫ ·) (normalConeEmbedding_vectorBundleToBase_assoc f hf _)

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- `ψ : C' ⟶ 𝐕(E')` is a morphism over `ℂ`. -/
theorem isOver_coneTestToBundle : (coneTestToBundle f g hf).IsOver (Spec (.of ℂ)) :=
  ⟨coneTestToBundle_comp_over f g hf⟩

variable [IsComplexScheme Y'] in
/-- **`C'` is a complex scheme**: it is isomorphic to `𝐕(E')` over `ℂ`. -/
theorem isComplexScheme_coneTestSpace : IsComplexScheme (coneTestSpace f g hf) :=
  haveI := isOver_coneTestToBundle f g hf
  isComplexScheme_of_isClosedImmersion (coneTestToBundle f g hf)

/-! ### The vertex of the cone -/

/-- **The vertex `0 : X' ⟶ C'` of the cone on the test scheme**: the base change of the vertex
`X ⟶ C_X Y` of the normal cone (`Stacks.Chow.normalConeZeroSection`). -/
def coneTestZeroSection : pullback f g ⟶ coneTestSpace f g hf :=
  pullback.lift (pullback.fst f g ≫ normalConeZeroSection f) (pullback.snd f g) (by
    rw [Category.assoc, (normalBundleOfRegular f hf).normalConeEmbedding_projection_assoc,
      normalConeZeroSection_toBase_assoc, pullback.condition])

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The vertex `0 : X' ⟶ C'` followed by `C' ⟶ C_X Y` is `X' ⟶ X ⟶ C_X Y`. -/
@[reassoc (attr := simp)]
theorem coneTestZeroSection_fst :
    coneTestZeroSection f g hf ≫ pullback.fst _ g = pullback.fst f g ≫ normalConeZeroSection f :=
  pullback.lift_fst _ _ _

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The vertex `0 : X' ⟶ C'` is a morphism over `Y'`. -/
@[reassoc (attr := simp)]
theorem coneTestZeroSection_snd :
    coneTestZeroSection f g hf ≫ pullback.snd _ g = pullback.snd f g :=
  pullback.lift_snd _ _ _

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- **`ψ ∘ 0 = 0_{E'}`**: the vertex of the cone on the test scheme goes to the zero section of
`𝐕(E')` (the vertex of `C_X Y` is the zero section of `N`,
`Stacks.Chow.normalConeZeroSectionOver_comp_normalConeEmbedding`, and zero sections are stable
under base change). -/
theorem coneTestZeroSection_comp_coneTestToBundle :
    coneTestZeroSection f g hf ≫ coneTestToBundle f g hf =
      MMP.Modules.zeroSection (fibreNormalModule f g hf) := by
  have h0 : normalConeZeroSection f ≫ (normalBundleOfRegular f hf).normalConeEmbedding =
      Scheme.Modules.vectorBundleLiftZero (dualSheaf (normalBundleOfRegular f hf).bundle) :=
    congrArg Over.Hom.left (normalConeZeroSectionOver_comp_normalConeEmbedding f
      (normalBundleOfRegular f hf))
  set M := dualSheaf (normalBundleOfRegular f hf).bundle
  have hK : coneTestZeroSection f g hf ≫ coneTestToBundleBase f g hf ≫
      (pullbackRightPullbackFstIso f g (Scheme.Modules.vectorBundleToBase X M)).inv =
      Scheme.Modules.vectorBundleLiftZero (fibreNormalModule f g hf) ≫
        (Scheme.Modules.vectorBundlePullbackIso (pullback.fst f g) M).inv := by
    refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (pullbackRightPullbackFstIso_inv_fst f g _)))).trans ?_
      refine (congrArg (_ ≫ ·) (coneTestToBundleBase_fst f g hf)).trans ?_
      refine ((coneTestZeroSection_fst_assoc f g hf _).trans
        (congrArg (pullback.fst f g ≫ ·) h0)).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact (Scheme.Modules.vectorBundleLiftZero_comp_vectorBundlePullbackProjection
        (pullback.fst f g) M).symm
    · have e1 : (Scheme.Modules.vectorBundlePullbackIso (pullback.fst f g) M).inv ≫
          pullback.snd _ _ = Scheme.Modules.vectorBundleToBase _ (fibreNormalModule f g hf) := by
        rw [Iso.inv_comp_eq, Scheme.Modules.vectorBundlePullbackIso_hom_vectorBundleToBase]
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) e1).trans
        (Scheme.Modules.vectorBundleLiftZero_toBase _)).symm
      refine pullback.hom_ext ?_ ?_
      · change coneTestZeroSection f g hf ≫ coneTestToBundleBase f g hf ≫
          ((pullbackRightPullbackFstIso f g (Scheme.Modules.vectorBundleToBase X M)).inv ≫
            pullback.snd _ _ ≫ pullback.fst f g) = 𝟙 _ ≫ pullback.fst f g
        rw [pullbackRightPullbackFstIso_inv_snd_fst, coneTestToBundleBase_fst_assoc]
        refine (congrArg (coneTestZeroSection f g hf ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg (pullback.fst _ g ≫ ·) (normalConeEmbedding_vectorBundleToBase f hf)))).trans ?_
        rw [coneTestZeroSection_fst_assoc, normalConeZeroSection_toBase, Category.comp_id,
          Category.id_comp]
      · change coneTestZeroSection f g hf ≫ coneTestToBundleBase f g hf ≫
          ((pullbackRightPullbackFstIso f g (Scheme.Modules.vectorBundleToBase X M)).inv ≫
            pullback.snd _ _ ≫ pullback.snd f g) = 𝟙 _ ≫ pullback.snd f g
        rw [pullbackRightPullbackFstIso_inv_snd_snd, coneTestToBundleBase_snd,
          coneTestZeroSection_snd, Category.id_comp]
  rw [← vectorBundleLiftZero_eq_zeroSection]
  have e2 : coneTestZeroSection f g hf ≫ coneTestToBundle f g hf =
      (coneTestZeroSection f g hf ≫ coneTestToBundleBase f g hf ≫
        (pullbackRightPullbackFstIso f g (Scheme.Modules.vectorBundleToBase X M)).inv) ≫
        (Scheme.Modules.vectorBundlePullbackIso (pullback.fst f g) M).hom := by
    simp only [coneTestToBundle, fibreNormalConeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rfl
  rw [e2, hK, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- **`X' = C' ×_{𝐕(E')} X'`**: the vertex of the cone on the test scheme is the base change of
the zero section of `𝐕(E')` along the isomorphism `ψ`. -/
theorem isPullback_coneTestZeroSection_coneTestToBundle :
    IsPullback (coneTestZeroSection f g hf) (𝟙 _) (coneTestToBundle f g hf)
      (MMP.Modules.zeroSection (fibreNormalModule f g hf)) :=
  IsPullback.of_vert_isIso ⟨by rw [coneTestZeroSection_comp_coneTestToBundle, Category.id_comp]⟩

variable [IsComplexScheme Y'] [IsComplexScheme Y] in
/-- **The vertex of the cone on the test scheme is a regular closed immersion of codimension
`d`**: it is the base change of the zero section of `𝐕(E')` along the isomorphism `ψ`. -/
theorem isRegularClosedImmersionOfCodim_coneTestZeroSection :
    IsRegularClosedImmersionOfCodim (coneTestZeroSection f g hf) d :=
  IsRegularClosedImmersionOfCodim.of_isPullback
    (isPullback_coneTestZeroSection_coneTestToBundle f g hf).flip
    (isRegularClosedImmersionOfCodim_zeroSection (fibreNormalModule f g hf) d)

omit [g.IsOver (Spec (.of ℂ))] in
/-- `x ↦ (x, ∞)` followed by `Z × 𝐏¹ ≅ 𝐏¹_Z` is the infinity section of `𝐏¹_Z`. -/
theorem infinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_inv
    {Z : Scheme.{0}} (s : Z ⟶ Spec (.of ℂ)) :
    infinitySection s ≫ (relativeProjectiveLineIsoProjectiveLineProduct s).inv =
      lineInfinitySection Z := by
  rw [← lineInfinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [f.IsOver (Spec (.of ℂ))] in
/-- **Stacks 0FE9 on `X × 𝐏¹`, at `W_∞`**: the base change of the trivial family
`e_W : X × 𝐏¹ ⟶ W` along `W_∞ ⟶ W` is the vertex `X ⟶ C_X Y ⟶ W_∞`, with `X ⟶ X × 𝐏¹` the
section `x ↦ (x, ∞)`. -/
theorem isPullback_infinitySection_lineFamily :
    IsPullback (infinitySection (X ↘ Spec (.of ℂ)))
      (normalConeZeroSection f ≫ normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ))) (lineFamily f)
      (modificationInclusionAtInfinity (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) := by
  have S0 := isPullback_lineToBlowupAtInfinity_modificationFibreAtInfinity f (Y ↘ Spec (.of ℂ))
  let φ := (relativeProjectiveLineIsoProjectiveLineProduct (X ↘ Spec (.of ℂ))).inv ≫
    projectiveLineBaseChange f.toImage
  have hφ : infinitySection (X ↘ Spec (.of ℂ)) ≫ φ =
      f.toImage ≫ lineInfinitySection f.ker.subscheme := by
    rw [← Category.assoc, infinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_inv]
    exact (isPullback_lineInfinitySection_projectiveLineBaseChange f.toImage).w
  have T : IsPullback φ (lineFamily f) (lineToBlowupAtInfinity f.ker) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, lineFamily, lineToBlowupAtInfinityOfClosedImmersion, Category.assoc]⟩
  have big : IsPullback (infinitySection (X ↘ Spec (.of ℂ)) ≫ φ)
      (normalConeZeroSection f ≫ normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ)))
      (lineToBlowupAtInfinity f.ker)
      (modificationInclusionAtInfinity (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) ≫ 𝟙 _) := by
    rw [hφ, Category.comp_id]
    exact S0
  exact IsPullback.of_right big (by
    rw [lineFamily, lineToBlowupAtInfinityOfClosedImmersion, ← Category.assoc, ← Category.assoc,
      Category.assoc _ _ (projectiveLineBaseChange f.toImage)]
    exact (congrArg (· ≫ lineToBlowupAtInfinity f.ker) hφ).trans S0.w) T

omit [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [f.IsOver (Spec (.of ℂ))] in
/-- **Stacks 0FE9 on `X × 𝐏¹`**: the base change of the trivial family `e_W : X × 𝐏¹ ⟶ W` along
`C_X Y ⟶ W_∞ ⟶ W` is the vertex `X ⟶ C_X Y`, with `X ⟶ X × 𝐏¹` the section `x ↦ (x, ∞)`. -/
theorem isPullback_normalConeZeroSection_lineFamily :
    IsPullback (normalConeZeroSection f) (infinitySection (X ↘ Spec (.of ℂ)))
      (normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ)) ≫
        modificationInclusionAtInfinity (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))))
      (lineFamily f) := by
  simpa using (IsPullback.of_vert_isIso_mono (fst := normalConeZeroSection f) (snd := 𝟙 _)
    (f := normalConeToFibreAtInfinity f (Y ↘ Spec (.of ℂ)))
    ⟨(Category.id_comp _).symm⟩).paste_vert
      (isPullback_infinitySection_lineFamily f).flip

omit [g.IsOver (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] in
/-- **`X' = C' ×_W (X × 𝐏¹)`** (Stacks 0FE9 on the test scheme): the base change of the trivial
family `e_W : X × 𝐏¹ ⟶ W` along `C' ⟶ W_∞ ×_Y Y' ⟶ W' ⟶ W` is the vertex `0 : X' ⟶ C'`, with
`X' ⟶ X × 𝐏¹` the map `x ↦ (x, ∞)` through `X' ⟶ X`. -/
theorem isPullback_coneTestZeroSection_lineFamily :
    IsPullback (coneTestZeroSection f g hf)
      (pullback.fst f g ≫ infinitySection (X ↘ Spec (.of ℂ)))
      (coneTestMap f g hf ≫ testInfinityInclusion f g ≫ pullback.fst _ g) (lineFamily f) := by
  have hO : IsPullback (coneTestZeroSection f g hf) (pullback.fst f g) (pullback.fst _ g)
      (normalConeZeroSection f) := by
    refine IsPullback.of_right ?_ (coneTestZeroSection_fst f g hf)
      (IsPullback.of_hasPullback _ g).flip
    rw [coneTestZeroSection_snd, (normalBundleOfRegular f hf).normalConeEmbedding_projection_assoc,
      normalConeZeroSection_toBase_assoc]
    exact (IsPullback.of_hasPullback f g).flip
  rw [coneTestMap_testInfinityInclusion_fst]
  exact hO.paste_vert (isPullback_normalConeZeroSection_lineFamily f)

omit [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- **`X' = (W_∞ ×_Y Y') ×_W (X × 𝐏¹)`** (Stacks 0FE9 on the test scheme): the base change of the
trivial family `e_W` along `W_∞ ×_Y Y' ⟶ W' ⟶ W` is `X' ⟶ C' ⟶ W_∞ ×_Y Y'`, the vertex of the cone
followed by the open immersion `o`. In particular the trivial family meets `W_∞ ×_Y Y'` inside the
open `C'`. -/
theorem isPullback_coneTestZeroSection_comp_coneTestMap_lineFamily :
    IsPullback (coneTestZeroSection f g hf ≫ coneTestMap f g hf)
      (pullback.fst f g ≫ infinitySection (X ↘ Spec (.of ℂ)))
      (testInfinityInclusion f g ≫ pullback.fst _ g) (lineFamily f) := by
  have hP : IsPullback (coneTestZeroSection f g hf ≫ coneTestMap f g hf) (pullback.fst f g)
      (pullback.fst _ g) (normalConeZeroSection f ≫ normalConeToFibreAtInfinity f
        (Y ↘ Spec (.of ℂ))) := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, coneTestMap_fst,
      coneTestZeroSection_fst_assoc]) (IsPullback.of_hasPullback _ g).flip
    rw [Category.assoc, coneTestMap_snd, coneTestZeroSection_snd, Category.assoc,
      normalConeToFibreAtInfinity_comp_projection, normalConeZeroSection_toBase_assoc]
    exact (IsPullback.of_hasPullback f g).flip
  rw [modificationInfinityBaseChange_comp_fst]
  exact hP.paste_vert (isPullback_infinitySection_lineFamily f).flip

omit [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
/-- **The vertex of the cone on the test scheme is the trivial family at `∞`**: `x ↦ (x, ∞)`
followed by the trivial family `e : X' × 𝐏¹ ⟶ W'` is `X' ⟶ C' ⟶ W_∞ ×_Y Y' ⟶ W'`. -/
theorem infinitySection_testTrivialFamily :
    infinitySection (pullback f g ↘ Spec (.of ℂ)) ≫ testTrivialFamily f g =
      coneTestZeroSection f g hf ≫ coneTestMap f g hf ≫ testInfinityInclusion f g := by
  refine pullback.hom_ext ?_ ?_
  · have hw := (isPullback_coneTestZeroSection_comp_coneTestMap_lineFamily f g hf).w
    simp only [Category.assoc] at hw ⊢
    rw [hw, testTrivialFamily, Category.assoc, testLineMap_fst, lineFamily,
      ← Category.assoc (infinitySection _),
      infinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_inv,
      ← Category.assoc (infinitySection _),
      infinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_inv,
      ← Category.assoc, (isPullback_lineInfinitySection_projectiveLineBaseChange _).w,
      Category.assoc]
  · simp only [Category.assoc]
    rw [modificationInfinityBaseChange_comp_snd, coneTestMap_snd,
      coneTestZeroSection_snd, testTrivialFamily, Category.assoc, testLineMap_snd,
      ← Category.assoc (infinitySection _),
      infinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_inv,
      ← Category.assoc, lineInfinitySection_comp, Category.id_comp]

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The vertex `0 : X' ⟶ C'` of the cone on the test scheme is a morphism over `ℂ`. -/
theorem isOver_coneTestZeroSection : (coneTestZeroSection f g hf).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change coneTestZeroSection f g hf ≫ pullback.fst _ g ≫ Stacks.Conormal.normalConeToBase f ≫
      X ↘ Spec (.of ℂ) = pullback.fst f g ≫ X ↘ Spec (.of ℂ)
    rw [coneTestZeroSection_fst_assoc, normalConeZeroSection_toBase_assoc]⟩

/-- The vertex `0 : X' ⟶ C'` of the cone on the test scheme is a closed immersion. -/
instance isClosedImmersion_coneTestZeroSection :
    IsClosedImmersion (coneTestZeroSection f g hf) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_coneTestZeroSection_coneTestToBundle f g hf).flip inferInstance

end MMP.Chow
