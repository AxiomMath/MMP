module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HigherDirectImageVanishing
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Resolution.Blowup.SncValuationExtraction
import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.ResolutionVanishing
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# lem mmp lc bpf local small model rational unit

Chain fold of: `lem_mmp_lc_bpf_local_small_model_rational_unit`.
-/

/-! ### `lem_mmp_lc_bpf_local_small_model_rational_unit` -/

namespace MMP.Fold06.LemMmpLcBpfLocalSmallModelRationalUnit

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

section Leray

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.AffineHigherDirectImage
open DerivedCategory

/-- `H^i(Rf_*(𝒪_X[0]))` vanishes exactly when `R^i f_* 𝒪_X` does, for `i : ℕ`. -/
private theorem isZero_homology_derivedPushforward_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (i : ℕ) :
    IsZero ((homologyFunctor Y.Modules i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj F))) ↔
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj F) := by
  obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso f F i
  rw [e.isZero_iff, Stacks.DerivedIndexing.isZero_rightDerived_obj_iff]

/-- The cohomology sheaves of `Rf_*(𝒪_X[0])` vanish in negative degrees. -/
private theorem isZero_homology_derivedPushforward_of_neg {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (j : ℤ) (hj : j < 0) :
    IsZero ((homologyFunctor Y.Modules j).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj F))) := by
  obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso f F j
  exact (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
    (Scheme.Modules.pushforward f) j hj F).of_iso e

/-- If `𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism, then `H^0(Rf_*(𝒪_X[0])) ≅ 𝒪_Y`. -/
private noncomputable def homologyZeroDerivedPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsIso f.c) :
    (homologyFunctor Y.Modules 0).obj ((derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (nonempty_homologyFunctor_derivedPushforward_iso f _ 0).some ≪≫
    Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso (Scheme.Modules.pushforward f) _ ≪≫
    (@asIso Y.Modules _ _ _ _
      (isIso_unitToPushforwardObjUnit_of_isIso_c f hf)).symm

open RingedSpaceModuleAdjunction in
/-- `Rf_*` moves cohomology to the right: if `E` lies in degrees `≥ a`, so does `Rf_* E`. On a
bounded below object the unbounded derived direct image is the one computed on `D⁺`. -/
private theorem isGE_derivedPushforward_obj {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules (structureSheafRing X))) (a : ℤ) (hE : E.IsGE a) :
    ((derivedPushforward f).obj E).IsGE a := by
  let E' : DerivedCategory.Plus (SheafOfModules (structureSheafRing X)) := ⟨E, ⟨a, hE⟩⟩
  haveI : E'.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff E' a).mp hE
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (modulePushforward f) (derivedPushforward f) (derivedPushforwardUnit f)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI) E' a hE
  have hRP : ((modulePushforward f).rightDerivedFunctorPlus.obj E').IsGE a :=
    CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj _ E' a
  have hR : DerivedCategory.TStructure.t.IsGE
      ((modulePushforward f).rightDerivedFunctorPlus.obj E').obj a :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ a).mpr hRP
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

/-- **Leray for the structure sheaf.** If `𝒪_Y ≅ Rf_* 𝒪_X` (that is, `f.c` is an isomorphism and
`R^i f_* 𝒪_X = 0` for `i > 0`), then `R^i (f ≫ g)_* 𝒪_X` vanishes whenever `R^i g_* 𝒪_Y` does. -/
private theorem isZero_rightDerived_comp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f.c)
    (hf' : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
        (SheafOfModules.unit X.ringCatSheaf)))
    (i : ℕ) (hg : IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj
        (SheafOfModules.unit Y.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let K := (derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj OX)
  have hK : ∀ j : ℤ, j ≠ 0 → IsZero ((homologyFunctor Y.Modules j).obj K) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · exact isZero_homology_derivedPushforward_of_neg f OX j h
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, by omega⟩
      exact (isZero_homology_derivedPushforward_iff f OX m).2 (hf' m (by omega))
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun j hj => hK j (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun j hj => hK j (by omega)
  obtain ⟨Y0, ⟨eK⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let eY0 : Y0 ≅ SheafOfModules.unit Y.ringCatSheaf :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app Y0).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules 0).mapIso eK.symm ≪≫
      homologyZeroDerivedPushforwardIso f hf
  let L := (derivedPushforward g.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf))
  let eL : (derivedPushforward (f ≫ g).toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj OX) ≅ L :=
    ((derivedPushforwardCompIso f.toLRSHom.toShHom g.toLRSHom.toShHom).app _).symm ≪≫
      (derivedPushforward g.toLRSHom.toShHom).mapIso
        (eK ≪≫ (DerivedCategory.singleFunctor Y.Modules 0).mapIso eY0)
  refine (isZero_homology_derivedPushforward_iff (f ≫ g) OX i).1
    (IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor Z.Modules i).mapIso eL))
  exact (isZero_homology_derivedPushforward_iff g _ i).2 hg

/-- **The low-degree Leray injection for the structure sheaf.** If `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism, then `R^1 g_* 𝒪_Y = 0` whenever `R^1 (f ≫ g)_* 𝒪_X = 0`. -/
private theorem isZero_rightDerived_one_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f.c)
    (h : IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let K := (derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj OX)
  obtain ⟨A, B, hA, hB, f₁, f₂, f₃, hT⟩ := TStructure.t.exists_triangle K 0 1 (by norm_num)
  haveI : A.IsLE 0 := ⟨hA⟩
  haveI : B.IsGE 1 := ⟨hB⟩
  have hAneg : ∀ j : ℤ, j < 0 → IsZero ((homologyFunctor Y.Modules j).obj A) := by
    intro j hj
    exact (HomologySequence.exact₁ _ hT (j - 1) j (by omega)).isZero_X₂
      ((B.isZero_of_isGE 1 (j - 1) (by omega)).eq_of_src _ _)
      ((isZero_homology_derivedPushforward_of_neg f OX j hj).eq_of_tgt _ _)
  haveI : A.IsGE 0 := (DerivedCategory.isGE_iff A 0).2 fun j hj => hAneg j hj
  obtain ⟨A0, ⟨eA⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A 0
  have hmono : Mono ((homologyFunctor Y.Modules 0).map f₁) :=
    (HomologySequence.exact₁ _ hT (-1) 0 (by omega)).mono_g
      ((B.isZero_of_isGE 1 (-1) (by omega)).eq_of_src _ _)
  have hepi : Epi ((homologyFunctor Y.Modules 0).map f₁) :=
    (HomologySequence.exact₂ _ hT 0).epi_f ((B.isZero_of_isGE 1 0 (by omega)).eq_of_tgt _ _)
  have hiso : IsIso ((homologyFunctor Y.Modules 0).map f₁) := isIso_of_mono_of_epi _
  let eA0 : A0 ≅ SheafOfModules.unit Y.ringCatSheaf :=
    ((singleFunctorCompHomologyFunctorIso Y.Modules 0).app A0).symm ≪≫
      (homologyFunctor Y.Modules 0).mapIso eA.symm ≪≫
      @asIso _ _ _ _ ((homologyFunctor Y.Modules 0).map f₁) hiso ≪≫
      homologyZeroDerivedPushforwardIso f hf
  let G := derivedPushforward g.toLRSHom.toShHom
  letI : G.CommShift ℤ := derivedPushforwardCommShift g.toLRSHom.toShHom
  haveI : G.IsTriangulated := derivedPushforward_isTriangulated g.toLRSHom.toShHom
  haveI : (G.obj B).IsGE 1 := isGE_derivedPushforward_obj g.toLRSHom.toShHom B 1 ⟨hB⟩
  have hGK : IsZero ((homologyFunctor Z.Modules 1).obj (G.obj K)) :=
    ((isZero_homology_derivedPushforward_iff (f ≫ g) OX 1).2 h).of_iso
      ((homologyFunctor Z.Modules 1).mapIso
        ((derivedPushforwardCompIso f.toLRSHom.toShHom g.toLRSHom.toShHom).app _))
  have hGA : IsZero ((homologyFunctor Z.Modules 1).obj (G.obj A)) :=
    (HomologySequence.exact₁ _ (G.map_distinguished _ hT) 0 1 (by omega)).isZero_X₂
      (((G.obj B).isZero_of_isGE 1 0 (by omega)).eq_of_src _ _) (hGK.eq_of_tgt _ _)
  refine (isZero_homology_derivedPushforward_iff g _ 1).1 (hGA.of_iso ?_)
  exact (homologyFunctor Z.Modules 1).mapIso
    (G.mapIso (eA ≪≫ (singleFunctor Y.Modules 0).mapIso eA0)).symm

end Leray

section Geometry

open MMP.Mori

/-- The single steps of a smooth blow-up sequence: blow-ups of a variety along a proper smooth
centre with smooth ambient space, up to isomorphism over the base. -/
private abbrev smoothBlowupStep (k : Type u) [Field k] : MorphismProperty Scheme.{u} :=
  fun W' W b => ∃ (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData),
    MMP.Mori.IsVariety k sW ∧ MMP.Resolution.IsSmoothBlowup sW I ∧ I.support ≠ ⊤ ∧
      ∃ e : W' ≅ blowUp I, e.hom ≫ blowUpToBase I = b

/-- A smooth blow-up sequence of a variety with nonempty last scheme is a finite composition of
smooth blow-ups of varieties along proper centres; its last scheme is a variety and its composite
is proper. -/
private theorem multiplicativeClosure_toBase_and_isVariety_of_isSmooth {k : Type u} [Field k]
    {X : Scheme.{u}}
    (B : MMP.Resolution.ClosedBlowupSequence X) :
    ∀ (s : X ⟶ Spec (.of k)), MMP.Mori.IsVariety k s → B.IsSmooth s → Nonempty B.target →
      (smoothBlowupStep k).multiplicativeClosure B.toBase ∧
        MMP.Mori.IsVariety k (B.toBase ≫ s) ∧ IsProper B.toBase := by
  induction B with
  | nil X =>
    intro s hs _ _
    refine ⟨MorphismProperty.multiplicativeClosure.id X, ?_, ?_⟩
    · change MMP.Mori.IsVariety k (𝟙 X ≫ s)
      rwa [Category.id_comp]
    · change IsProper (𝟙 X)
      infer_instance
  | cons Z B ih =>
    intro s hs hB hne
    obtain ⟨h1, h2, h3⟩ := hB
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      exact (isEmpty_blowUp_bot _).false (B.toBase hne.some)
    haveI := hs
    obtain ⟨hv, hp, -⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational s Z hZ
    obtain ⟨ihc, ihv, ihp⟩ := ih (blowUpToBase Z ≫ s) hv h3 hne
    haveI := hs.toIsIntegral
    have hsupp : Z.support ≠ ⊤ := by rwa [Ne, Scheme.IdealSheafData.support_eq_top_iff]
    refine ⟨.comp_of _ _ ihc ⟨s, Z, hs, ⟨h1, h2⟩, hsupp, Iso.refl _, Category.id_comp _⟩, ?_, ?_⟩
    · change MMP.Mori.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ s)
      rwa [Category.assoc]
    · haveI := hp.isProper
      change IsProper (B.toBase ≫ blowUpToBase Z)
      infer_instance

/-- A proper birational morphism onto a normal variety is biregular at the generic point. -/
private theorem genericPoint_mem_biregularLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) :
    genericPoint X ∈ biregularLocus f := by
  haveI : IsNormal X := hX.2
  have h := two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX.1) (hX := hY) hf
  by_contra hη
  have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h) (genericPoint X) hη
  have h0 : Order.coheight (genericPoint X) = 0 := Order.coheight_eq_zero.mpr fun y _ =>
    (Scheme.le_iff_specializes).mpr ((genericPoint_spec X).specializes (Set.mem_univ y))
  rw [h0] at h2
  exact absurd h2 (by decide)

/-- A base change of a morphism that is an isomorphism over `V` is an isomorphism over every
open contained in the preimage of `V`. -/
private theorem isIso_morphismRestrict_pullbackSnd {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {V : Y.Opens} {W : Y'.Opens} (hW : W ≤ g ⁻¹ᵁ V) (hf : IsIso (f ∣_ V)) :
    IsIso (pullback.snd f g ∣_ W) := by
  have hUY : pullback.snd f g ⁻¹ᵁ W =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ pullback.snd f g ⁻¹ᵁ W := by
    refine (inf_eq_right.mpr ?_).symm
    calc pullback.snd f g ⁻¹ᵁ W ≤ pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) := Scheme.Hom.preimage_mono _ hW
      _ = pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hW le_rfl hUY
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at H
  exact H.isIso_snd_of_isIso hf

/-- A scheme containing a dense open isomorphic to a nonempty open of an irreducible scheme is
irreducible. -/
private theorem irreducibleSpace_of_iso_of_dense {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (U : X.Opens) (V : Y.Opens) (hU : Dense (U : Set X)) (hV : (V : Set Y).Nonempty)
    (e : U.toScheme ≅ V.toScheme) : IrreducibleSpace X := by
  have hVirr : IsIrreducible (V : Set Y) :=
    ⟨hV, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset V.isOpen
      (Set.subset_univ _)⟩
  haveI : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hVirr
  have hrange : Set.range (e.inv ≫ U.ι) = (U : Set X) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e.inv v).2
    · intro hx
      obtain ⟨u, rfl⟩ : x ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
      refine ⟨e.hom u, ?_⟩
      change (e.hom ≫ e.inv ≫ U.ι) u = U.ι u
      rw [e.hom_inv_id_assoc]
  have hirr : IsIrreducible (U : Set X) := by
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (e.inv ≫ U.ι).continuous.continuousOn
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hU.closure_eq]
  exact hirr.closure

/-- A morphism of irreducible schemes that is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] : IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hU
  have hV : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := ⟨_, ((inv (f ∣_ U)) ⟨y, hy⟩).2⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U hV ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- If `j ≫ f = O.ι` for an open immersion `j` and a separated `f` from an irreducible scheme,
with `O` nonempty, then `f` is an isomorphism over `O`. -/
private theorem isIso_morphismRestrict_of_comp_eq_ι {Γ X : Scheme.{u}} [IrreducibleSpace Γ]
    (f : Γ ⟶ X) [IsSeparated f] (O : X.Opens) (hO : (O : Set X).Nonempty)
    (j : O.toScheme ⟶ Γ) [IsOpenImmersion j] (hj : j ≫ f = O.ι) :
    IsIso (f ∣_ O) := by
  have hrange : Set.range j ⊆ Set.range (f ⁻¹ᵁ O).ι := by
    rintro _ ⟨o, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (j o) ∈ O
    rw [← Scheme.Hom.comp_apply, hj]
    exact o.2
  set j₀ := IsOpenImmersion.lift (f ⁻¹ᵁ O).ι j hrange with hj₀def
  have hj₀ : j₀ ≫ (f ⁻¹ᵁ O).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hsec : j₀ ≫ f ∣_ O = 𝟙 _ := by
    rw [← cancel_mono O.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hj₀, hj,
      Category.id_comp]
  haveI : IsOpenImmersion (j₀ ≫ (f ⁻¹ᵁ O).ι) := by rw [hj₀]; infer_instance
  haveI : IsOpenImmersion j₀ := IsOpenImmersion.of_comp j₀ (f ⁻¹ᵁ O).ι
  haveI : IsClosedImmersion (j₀ ≫ f ∣_ O) := by rw [hsec]; infer_instance
  haveI : IsClosedImmersion j₀ := IsClosedImmersion.of_comp j₀ (f ∣_ O)
  have hsurj : Function.Surjective j₀ := by
    have hpre : _root_.IsPreconnected (Set.univ : Set (f ⁻¹ᵁ O).toScheme) := by
      have hirr : IsPreirreducible ((f ⁻¹ᵁ O : Γ.Opens) : Set Γ) :=
        (IrreducibleSpace.isIrreducible_univ Γ).isPreirreducible.open_subset (f ⁻¹ᵁ O).isOpen
          (Set.subset_univ _)
      exact (Subtype.preconnectedSpace hirr.isPreconnected).isPreconnected_univ
    obtain ⟨o, ho⟩ := hO
    have hcl := hpre.subset_isClopen (s := Set.univ)
      ⟨j₀.isClosedEmbedding.isClosed_range, j₀.isOpenEmbedding.isOpen_range⟩
      ⟨j₀ ⟨o, ho⟩, Set.mem_univ _, ⟨o, ho⟩, rfl⟩
    exact fun x => hcl (Set.mem_univ x)
  haveI : IsIso j₀ := (isIso_iff_isOpenImmersion_and_surjective j₀).2 ⟨inferInstance, ⟨hsurj⟩⟩
  have : IsIso (j₀ ≫ f ∣_ O) := by rw [hsec]; infer_instance
  exact IsIso.of_isIso_comp_left j₀ (f ∣_ O)

/-- If `a ≫ g` is dominant and `g` is an isomorphism over an open containing the generic point,
then `a` is dominant. -/
private theorem isDominant_of_isDominant_comp_of_isIso_morphismRestrict {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (a : X ⟶ Y) (g : Y ⟶ Z) [IsDominant (a ≫ g)]
    (W : Z.Opens) (hW : IsIso (g ∣_ W)) (hη : genericPoint Z ∈ W) : IsDominant a := by
  have h1 : g (a (genericPoint X)) = genericPoint Z := by
    rw [← Scheme.Hom.comp_apply]
    exact map_genericPoint_of_isDominant (a ≫ g)
  have h2 : g (genericPoint Y) = genericPoint Z := by
    have hs : g (genericPoint Y) ⤳ g (a (genericPoint X)) :=
      (genericPoint_specializes _).map g.continuous
    rw [h1] at hs
    exact (hs.antisymm (genericPoint_specializes _)).eq
  have inj : ∀ u v : Y, g u ∈ W → g v ∈ W → g u = g v → u = v := by
    intro u v hu hv huv
    obtain ⟨p, rfl⟩ : u ∈ Set.range (g ⁻¹ᵁ W).ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨p', rfl⟩ : v ∈ Set.range (g ⁻¹ᵁ W).ι := by rwa [Scheme.Opens.range_ι]
    have e1 : ∀ x, W.ι ((g ∣_ W) x) = g ((g ⁻¹ᵁ W).ι x) := fun x => by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
    have : (g ∣_ W) p = (g ∣_ W) p' :=
      W.ι.isOpenEmbedding.injective (by rw [e1, e1, huv])
    rw [(g ∣_ W).isOpenEmbedding.injective this]
  have key : a (genericPoint X) = genericPoint Y :=
    inj _ _ (by rw [h1]; exact hη) (by rw [h2]; exact hη) (by rw [h1, h2])
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  refine closure_mono (Set.singleton_subset_iff.2 (Set.mem_range.2 ⟨_, key⟩)) ?_
  exact specializes_iff_mem_closure.mp (genericPoint_specializes y)

/-- If `a ≫ g` is birational, `a` dominant and of finite type, and `g` dominant, then `a` is
birational. -/
private theorem isBirationalMorphism_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (a : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType a] [IsDominant a]
    [IsDominant g] (h : IsBirationalMorphism (a ≫ g)) : IsBirationalMorphism a := by
  haveI : IsDominant (a ≫ g) := h.isDominant
  refine MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational a
    (isBirational_of_surjective_functionFieldMap a fun t => ?_)
  obtain ⟨z, hz⟩ := h.functionFieldMap_bijective.2 t
  exact ⟨functionFieldMap g z, by rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply a g rfl, hz]⟩

/-- A proper birational morphism onto a normal variety induces an isomorphism on structure
sheaves. -/
private theorem isIso_c_of_isProper_of_isBirationalMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X) [IsProper f]
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hX : IsNormalVariety k sX)
    (hf : IsBirationalMorphism f) : IsIso f.c := by
  have := MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism (f ≫ sX) sX hY hX f hf
  haveI : ∀ U, IsIso (f.c.app U) := fun U => this U.unop
  exact NatIso.isIso_of_isIso_app _

/-- **Vanishing of `R^1 g_* 𝒪` through a dominating model.** Let `p : X ⟶ S` be a proper
birational morphism from a smooth quasi-projective variety with `R^1 p_* 𝒪_X = 0`, and let
`g : Y' ⟶ S` be proper birational with `S` and `Y'` normal varieties. If `Y'` and `X` are
dominated by a common `Γ`, with `r : Γ ⟶ X` projective birational and `q ≫ g = r ≫ p`, then
`R^1 g_* 𝒪_{Y'} = 0`. -/
private theorem isZero_rightDerived_one_of_dominated {S X Y' Γ : Scheme.{0}} [IsIntegral S]
    [IsIntegral Y'] [IsIntegral Γ] {sS : S ⟶ Spec (.of ℂ)} (p : X ⟶ S) [IsProper p]
    (hXqp : IsQuasiProjectiveVariety ℂ (p ≫ sS)) (hXs : IsSmoothScheme (p ≫ sS))
    (hpb : IsBirationalMorphism p)
    (hp1 : IsZero (((Scheme.Modules.pushforward p).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (g : Y' ⟶ S) [IsProper g] (hgb : IsBirationalMorphism g) (hS : IsNormalVariety ℂ sS)
    (hY' : IsNormalVariety ℂ (g ≫ sS)) (r : Γ ⟶ X) (hrp : IsProjectiveMorphism r)
    (hrb : IsBirationalMorphism r) (q : Γ ⟶ Y') (hq : q ≫ g = r ≫ p) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit Y'.ringCatSheaf)) := by
  haveI := hXqp.toIsVariety
  haveI : IsIntegral X := hXqp.toIsVariety.toIsIntegral
  obtain ⟨-, -, B, g', hBs, hBb, hfac⟩ :=
    MMP.Resolution.exists_iso_blowUp_of_isSmoothScheme (p ≫ sS) hXqp hXs r hrp hrb
  have hBne : Nonempty B.target := by
    obtain ⟨e, -⟩ := hBb
    obtain ⟨y, hy⟩ := e.dense_target.nonempty
    exact ⟨(e.iso.inv ⟨y, hy⟩).1⟩
  obtain ⟨hmc, hBv, hBp⟩ :=
    multiplicativeClosure_toBase_and_isVariety_of_isSmooth B (p ≫ sS) inferInstance hBs hBne
  obtain ⟨hBc, hBvan⟩ :=
    MMP.LcBpf.isIso_c_and_isZero_rightDerived_of_multiplicativeClosure_smoothBlowup ℂ B.toBase hmc
  haveI : IsIntegral B.target := hBv.toIsIntegral
  haveI := hBp
  let a : B.target ⟶ Y' := g' ≫ q
  have ha : a ≫ g = B.toBase ≫ p := by
    rw [← hfac]
    simp only [a, Category.assoc, hq]
  haveI : IsProper (a ≫ g) := by rw [ha]; infer_instance
  haveI : IsProper a := IsProper.of_comp a g
  have hagb : IsBirationalMorphism (a ≫ g) := by
    rw [ha]
    exact MMP.Mori.isBirationalMorphism_comp hBb hpb
  haveI : IsDominant (a ≫ g) := hagb.isDominant
  haveI : IsDominant a := isDominant_of_isDominant_comp_of_isIso_morphismRestrict a g
    (biregularLocus g) (isBiregular_biregularLocus g)
    (genericPoint_mem_biregularLocus hS g hY'.1 hgb)
  haveI : IsDominant g := hgb.isDominant
  have hav : AlgebraicGeometry.IsVariety ℂ (a ≫ g ≫ sS) := by
    rw [← Category.assoc, ha, Category.assoc]
    exact hBv
  refine isZero_rightDerived_one_of_comp a g (isIso_c_of_isProper_of_isBirationalMorphism a hav hY'
    (isBirationalMorphism_of_comp a g hagb)) ?_
  rw [ha]
  exact isZero_rightDerived_comp_unit B.toBase p hBc hBvan 1 hp1

/-- If `f : X ⟶ Y` from an irreducible scheme is an isomorphism over `V`, and the first projection
of `X ×_Y Y'` is open, then `X ×_Y Y'` is irreducible as soon as `Y'` is and `g⁻¹ V` is
nonempty. -/
private theorem irreducibleSpace_pullback_of_isIso_morphismRestrict {X Y Y' : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y'] (f : X ⟶ Y) (g : Y' ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] (hfst : IsOpenMap (pullback.fst f g))
    (hV : ((g ⁻¹ᵁ V : Y'.Opens) : Set Y').Nonempty) :
    IrreducibleSpace (pullback f g : Scheme.{u}) := by
  obtain ⟨y, hy⟩ := hV
  have hd : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    (f ⁻¹ᵁ V).isOpen.dense ⟨_, ((inv (f ∣_ V)) ⟨g y, hy⟩).2⟩
  have heq : pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) = pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  haveI : IsIso (pullback.snd f g ∣_ (g ⁻¹ᵁ V)) :=
    isIso_morphismRestrict_pullbackSnd f g le_rfl inferInstance
  refine irreducibleSpace_of_iso_of_dense (pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V)) (g ⁻¹ᵁ V) ?_
    ⟨y, hy⟩ (asIso (pullback.snd f g ∣_ (g ⁻¹ᵁ V)))
  rw [heq]
  exact hd.preimage hfst

/-- A projective `g : Y' ⟶ Z` and a morphism `p : X ⟶ Z` from a variety, both isomorphisms over
opens containing the generic point of `Z`, are dominated by an integral `Γ` (the graph of the
rational map `X ⇢ Y'`) with `r : Γ ⟶ X` projective birational. -/
private theorem exists_isProjectiveMorphism_isBirationalMorphism_comp_eq {X Y' Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Z] (p : X ⟶ Z) (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] (g : Y' ⟶ Z) (hg : IsProjectiveMorphism g)
    (W₁ : Z.Opens) [IsIso (p ∣_ W₁)] (hη₁ : genericPoint Z ∈ W₁)
    (hη : genericPoint Z ∈ biregularLocus g) :
    ∃ (Γ : Scheme.{0}) (_ : IsIntegral Γ) (r : Γ ⟶ X) (q : Γ ⟶ Y'),
      IsProjectiveMorphism r ∧ IsBirationalMorphism r ∧ q ≫ g = r ≫ p := by
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  haveI : IsProper g := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hg).2
  let W : Z.Opens := W₁ ⊓ biregularLocus g
  let O : X.Opens := p ⁻¹ᵁ W
  have hOne : (O : Set X).Nonempty := by
    obtain ⟨y, hy⟩ : genericPoint Z ∈ Set.range W₁.ι := by rwa [Scheme.Opens.range_ι]
    let x := (p ⁻¹ᵁ W₁).ι ((inv (p ∣_ W₁)) y)
    have hx : p x = genericPoint Z := by
      rw [← hy]
      change ((inv (p ∣_ W₁)) ≫ (p ⁻¹ᵁ W₁).ι ≫ p) y = _
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    refine ⟨x, ?_⟩
    change p x ∈ W
    rw [hx]
    exact ⟨hη₁, hη⟩
  haveI : Nonempty O := hOne.to_subtype
  let k : O.toScheme ⟶ Y' := (p ∣_ W) ≫ Z.homOfLE inf_le_right ≫
    inv (g ∣_ biregularLocus g) ≫ (g ⁻¹ᵁ biregularLocus g).ι
  have hk : k ≫ g = O.ι ≫ p := by
    simp only [k, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      Scheme.homOfLE_ι]
    exact morphismRestrict_ι _ _
  let s : O.toScheme ⟶ pullback g p := pullback.lift k O.ι hk
  have hs : s ≫ pullback.snd g p = O.ι := pullback.lift_snd _ _ _
  haveI : IsImmersion s := by
    have : IsImmersion (s ≫ pullback.snd g p) := by rw [hs]; infer_instance
    exact IsImmersion.of_comp s (pullback.snd g p)
  haveI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType sX
  haveI : NoetherianSpace O := NoetherianSpace.set (O : Set X)
  haveI : QuasiCompact s := quasiCompact_of_noetherianSpace_source s
  haveI : IsOpenImmersion s.toImage := isOpenImmersion_toImage s (.inl inferInstance)
  have hΓv : AlgebraicGeometry.IsVariety ℂ (s.imageι ≫ pullback.snd g p ≫ sX) :=
    Scheme.Hom.isVariety_image ℂ s (pullback.snd g p ≫ sX)
  haveI : IsIntegral s.image := hΓv.toIsIntegral
  let r : s.image ⟶ X := s.imageι ≫ pullback.snd g p
  have hrp : IsProjectiveMorphism r :=
    (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp (hg.baseChange p)
  haveI : IsProper r := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hrp).2
  have hj : s.toImage ≫ r = O.ι := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs]
  haveI : IsIso (r ∣_ O) := isIso_morphismRestrict_of_comp_eq_ι r O hOne s.toImage hj
  exact ⟨s.image, inferInstance, r, s.imageι ≫ pullback.fst g p, hrp,
    isBirationalMorphism_of_isIso_morphismRestrict r O hOne,
    by simp only [r, Category.assoc, pullback.condition]⟩

/-- Let `p : X ⟶ Z` be a proper morphism from a smooth quasi-projective variety onto a normal
variety, an isomorphism over an open containing the generic point, with `R^1 p_* 𝒪_X = 0`. For a
projective birational `g : Y' ⟶ Z` with `Y'` normal, `𝒪_Z ⟶ g_* 𝒪_{Y'}` is an isomorphism and
`R^1 g_* 𝒪_{Y'} = 0`. -/
private theorem isIso_unitToPushforwardObjUnit_and_isZero_of_resolution {X Y' Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Z] [IsNormal Y'] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) (p : X ⟶ Z) [IsProper p]
    (hXqp : IsQuasiProjectiveVariety ℂ (p ≫ sZ)) (hXs : IsSmoothScheme (p ≫ sZ))
    (hp1 : IsZero (((Scheme.Modules.pushforward p).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (W₁ : Z.Opens) [IsIso (p ∣_ W₁)] (hη : genericPoint Z ∈ W₁)
    (g : Y' ⟶ Z) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ∧
      IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (SheafOfModules.unit Y'.ringCatSheaf)) := by
  haveI : IsProper g := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hg).2
  haveI := hZ.1
  haveI : IrreducibleSpace Y' := by
    obtain ⟨e, -⟩ := hgb
    exact irreducibleSpace_of_iso_of_dense e.source e.target e.dense_source
      e.dense_target.nonempty e.iso
  haveI : IsIntegral Y' := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI hY'v : AlgebraicGeometry.IsVariety ℂ (g ≫ sZ) := {}
  refine ⟨isIso_unitToPushforwardObjUnit_of_isIso_c g
    (isIso_c_of_isProper_of_isBirationalMorphism g hY'v hZ hgb), ?_⟩
  haveI := hXqp.toIsVariety
  obtain ⟨Γ, _, r, q, hrp, hrb, hq⟩ := exists_isProjectiveMorphism_isBirationalMorphism_comp_eq
    p (p ≫ sZ) g hg W₁ hη (genericPoint_mem_biregularLocus hZ g hY'v hgb)
  exact isZero_rightDerived_one_of_dominated p hXqp hXs
    (isBirationalMorphism_of_isIso_morphismRestrict p W₁ ⟨_, hη⟩) hp1 g hgb hZ
    ⟨hY'v, inferInstance⟩ r hrp hrb q hq

end Geometry

end MMP.Fold06.LemMmpLcBpfLocalSmallModelRationalUnit

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Fold06.LemMmpLcBpfLocalSmallModelRationalUnit

variable {Y Yt Y' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
  {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}

/-- Let `(Y, Θ, T, π)` be a local setting and `E = (Y_e, q, η', L̃)` a local étale datum. For a
projective birational morphism `g : Y' ⟶ Y_e` with `Y'` normal, the canonical map
`𝒪_{Y_e} ⟶ g_* 𝒪_{Y'}` is an isomorphism and `R^1 g_* 𝒪_{Y'} = 0`. -/
@[mmp "lem_mmp_lc_bpf_local_small_model_rational_unit"]
public theorem LocalEtaleDatum.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived_one
    (h : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L) [IsNormal Y']
    (g : Y' ⟶ E.scheme) (hg : IsProjectiveMorphism g) (hb : IsBirationalMorphism g) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ∧
      IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (SheafOfModules.unit Y'.ringCatSheaf)) := by
  obtain ⟨hYv, hYtv, hYts, hπp, hπb⟩ := h.isResolution
  haveI := hYv
  haveI := hYtv
  haveI : IsIntegral Yt := hYtv.toIsIntegral
  haveI : IsNormal Yt := h.isNormal_resolution
  haveI : IsProper π := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hπp).2
  have hYe := E.isQuasiProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ (E.map ≫ sY) := hYe.toIsVariety
  haveI : IsIntegral E.scheme := hYe.toIsVariety.toIsIntegral
  haveI : IsNormal E.scheme := E.isNormal
  have hπep : IsProjectiveMorphism E.resolutionMap := hπp.baseChange E.map
  haveI : IsProper E.resolutionMap :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hπep).2
  have hπevan : IsZero (((Scheme.Modules.pushforward E.resolutionMap).rightDerived 1).obj
      (SheafOfModules.unit E.resolution.ringCatSheaf)) :=
    open Stacks.AlgebraicGeometry.FlatBaseChangeDerived in
    isZero_rightDerived_pushforward_unit_of_isPullback (IsPullback.of_hasPullback π E.map) 1
      ((h.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived).2 1 one_pos)
  have hηY : genericPoint Y ∈ biregularLocus π :=
    genericPoint_mem_biregularLocus ⟨hYv, inferInstance⟩ π hYtv hπb
  have hπV : IsIso (π ∣_ biregularLocus π) := isBiregular_biregularLocus π
  let W₁ : E.scheme.Opens := E.map ⁻¹ᵁ biregularLocus π
  have hπeW : IsIso (E.resolutionMap ∣_ W₁) :=
    isIso_morphismRestrict_pullbackSnd π E.map le_rfl hπV
  haveI : Nonempty E.scheme := ⟨E.point⟩
  haveI : IsDominant E.map := ⟨E.map.isOpenMap.isOpen_range.dense ⟨_, E.point, rfl⟩⟩
  have hηYe : genericPoint E.scheme ∈ W₁ := by
    change E.map (genericPoint E.scheme) ∈ biregularLocus π
    rwa [map_genericPoint_of_isDominant]
  haveI : IrreducibleSpace E.resolution :=
    irreducibleSpace_pullback_of_isIso_morphismRestrict π E.map (biregularLocus π)
      (pullback.fst π E.map).isOpenMap ⟨_, hηYe⟩
  haveI : IsIntegral E.resolution := isIntegral_of_irreducibleSpace_of_isReduced _
  let sYe : E.resolution ⟶ Spec (.of ℂ) := E.resolutionMap ≫ E.map ≫ sY
  haveI : AlgebraicGeometry.IsVariety ℂ sYe := {}
  have hYeqp : IsQuasiProjectiveVariety ℂ sYe :=
    (isQuasiProjectiveVariety_iff ℂ _).2 ⟨inferInstance,
      IsQuasiProjective.comp _ _ hπep.isQuasiProjective hYe.isQuasiProjective⟩
  have hYes : IsSmoothScheme sYe := by
    haveI : LocallyOfFinitePresentation (π ≫ sY) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
    haveI : LocallyOfFinitePresentation sYe :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
    haveI : Smooth (π ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).1 hYts
    have e : sYe = pullback.fst π E.map ≫ π ≫ sY := (pullback.condition_assoc _).symm
    rw [MMP.Mori.isSmoothScheme_iff, e]
    infer_instance
  exact isIso_unitToPushforwardObjUnit_and_isZero_of_resolution ⟨inferInstance, inferInstance⟩
    E.resolutionMap hYeqp hYes hπevan W₁ hηYe g hg hb

end MMP.Fourfold
