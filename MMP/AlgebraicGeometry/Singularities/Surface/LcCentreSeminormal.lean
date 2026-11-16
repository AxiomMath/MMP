module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
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
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
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
import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.LcCentrePushforwardStructureSheaf
import MMP.AlgebraicGeometry.Singularities.SNCGluing
import MMP.AlgebraicGeometry.Singularities.ConnectednessPushforwardSurjective

/-!
# Sections on the normalization of a union of lc centres on a surface

Let `(X, B)` be an lc pair with effective `ℚ`-boundary on a normal projective complex surface,
and let `W ⊆ X` be the reduced closed subscheme supported on a finite union of lc centres of
dimension at most one (curves and isolated points). Let `ν : W^ν ⟶ W` be the normalization and
`L` a line bundle on `W`. A section `s` of `ν^* L` over `ν⁻¹ U` comes from a (unique) section of
`L` over `U` if and only if, at every closed point `w ∈ U`, the values of `s` at the points of
`ν⁻¹ w` agree in the fibre `L(w)`. In other words, a union of lc centres of dimension at most one
is seminormal.

## Main results

* `MMP.Mori.IsLcPair.existsUnique_unit_app_eq_iff_of_isNormalization`: the descent criterion.

## Implementation notes

The normalization is not a chosen construction: `ν` is any integral morphism from a normal
scheme that is an isomorphism over a dense open of `W` with dense preimage, which characterizes
the normalization of the reduced scheme `W`. The pullback map on sections is the unit of the
adjunction `ν^* ⊣ ν_*`. That the values of `s` over `w` agree in `L(w)` is stated without fibres:
there is a section `t` of `L` near `w` such that `s - ν^* t` vanishes at every point `w'` over `w`,
and vanishing of a section of the line bundle `ν^* L` at `w'` means that near `w'` it is `f • τ`
for a function `f` vanishing at `w'`. The statement is local on `W` (any open `U`), which also
covers the global sections.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar13]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open MMP.Intersection.Scheme.Modules (IsLineBundle)
open MMP.Mori

namespace Proof_lem_mmp_surface_lc_centre_curve_functions

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{0}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{0}} (L : X.Modules) {V : X.Opens} (σ : Γ(L, V)) :
    L.presheaf.map (homOfLE (le_refl V)).op σ = σ := by
  rw [show homOfLE (le_refl V) = 𝟙 V from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

open Stacks.AlgebraicGeometry.TwistMapsInvertible in
/-- A locally free module of rank one is invertible. -/
private theorem isInvertibleModule_of_isLineBundle {X : Scheme.{0}} (L : X.Modules)
    (hL : IsLineBundle L) : Stacks.Ample.IsInvertibleModule X L := by
  refine isInvertibleModule_of_forall_exists_restrict_isoUnit L fun x => ?_
  obtain ⟨U, hx, ⟨e⟩⟩ := hL x
  exact ⟨U, hx, ⟨e ≪≫ Limits.coproductUniqueIso _⟩⟩

/-- A local generator of an invertible module pulls back, along the unit of `b^* ⊣ b_*`, to a
local generator. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{0}} (b : X ⟶ Y) (A : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y A] {K : Y.Opens} (a : Γ(A, K))
    (ha : ∀ (W : Y.Opens) (hW : W ≤ K),
      Function.Bijective (fun c : Γ(Y, W) => c • A.presheaf.map (homOfLE hW).op a))
    (W : X.Opens) (hW : W ≤ b ⁻¹ᵁ K) :
    Function.Bijective (fun c : Γ(X, W) =>
      c • ((Scheme.Modules.pullback b).obj A).presheaf.map (homOfLE hW).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app A).app K a)) := by
  have hpb : Stacks.Ample.IsInvertibleModule X
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b A
  have hpb' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback b.toLRSHom.toShHom).obj A) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hpb
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) _ (Stacks.RingedSpace.pullbackUnit b.toLRSHom.toShHom A (op K) a)
    _ hW fun x hx => ?_
  have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul A a ha (b.base x) (hW hx)
  rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff b A a x
    (hW hx)] at h1
  rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1

/-- Pulling back along a morphism `ν : Y ⟶ W` onto a reduced scheme, which is quasi-compact and an
isomorphism over a dense open, is injective on the sections of a line bundle. -/
private theorem unit_app_injective {W Y : Scheme.{0}} [IsReduced W] (ν : Y ⟶ W) [QuasiCompact ν]
    (hν : ∃ U₀ : W.Opens, Dense U₀.carrier ∧ Dense (ν ⁻¹ᵁ U₀).carrier ∧
      IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl))
    (L : W.Modules) (hL : IsLineBundle L) (U : W.Opens) :
    Function.Injective
      (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U) := by
  have hLi := isInvertibleModule_of_isLineBundle L hL
  have : IsDominant ν := by
    obtain ⟨U₀, hU₀, -, hiso⟩ := hν
    refine ⟨hU₀.mono fun w hw => ?_⟩
    obtain ⟨y, hy⟩ := (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl).surjective ⟨w, hw⟩
    have h2 := congrArg (fun z => U₀.ι z) hy
    simp only [Scheme.Opens.ι_apply] at h2
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply] at h2
    exact ⟨_, h2⟩
  have : IsSchemeTheoreticallyDominant ν := .of_isDominant _
  have hLs : Stacks.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
      (structureSheafRing W.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hLi
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L
  rw [injective_iff_map_eq_zero]
  intro t ht
  have key : ∀ x : U, ∃ (K : W.Opens) (hKU : K ≤ U), x.1 ∈ K ∧
      L.presheaf.map (homOfLE hKU).op t = 0 := by
    intro x
    obtain ⟨K, hxK, a, ha⟩ : ∃ (K : W.Opens) (_ : x.1 ∈ K) (a : Γ(L, K)), ∀ (V : W.Opens)
        (hV : V ≤ K), Function.Bijective
          (fun c : Γ(W, V) => c • L.presheaf.map (homOfLE hV).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible W.toRingedSpace _ L hLs x.1
    refine ⟨K ⊓ U, inf_le_right, ⟨hxK, x.2⟩, ?_⟩
    set a' := L.presheaf.map (homOfLE (inf_le_left : K ⊓ U ≤ K)).op a
    have ha' : ∀ (V : W.Opens) (hV : V ≤ K ⊓ U), Function.Bijective
        (fun c : Γ(W, V) => c • L.presheaf.map (homOfLE hV).op a') := fun V hV => by
      simpa only [a', map_map_homOfLE] using ha V (hV.trans inf_le_left)
    obtain ⟨f, hf⟩ := (ha' (K ⊓ U) le_rfl).2 (L.presheaf.map (homOfLE inf_le_right).op t)
    have hgen := bijective_smul_unit_app ν L a' ha' (ν ⁻¹ᵁ (K ⊓ U)) le_rfl
    have hηt : η.app (K ⊓ U) (L.presheaf.map (homOfLE inf_le_right).op t) = 0 := by
      refine (PresheafOfModules.naturality_apply η.val (homOfLE inf_le_right).op t).trans ?_
      change _ = (0 : _)
      erw [ht, map_zero]
      rfl
    have hνf : ν.app (K ⊓ U) f = 0 := by
      refine hgen.1 ?_
      dsimp only
      rw [zero_smul]
      refine Eq.trans ?_ hηt
      refine (congrArg (ν.app (K ⊓ U) f • ·)
        (map_homOfLE_refl ((Scheme.Modules.pullback ν).obj L) _)).trans ?_
      rw [← hf, Scheme.Modules.Hom.app_smul, map_homOfLE_refl L a']
      rfl
    have hf0 : f = 0 := ν.app_injective (K ⊓ U) (by rw [hνf, map_zero])
    rw [← hf, hf0]
    exact zero_smul _ _
  choose K hKU hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K U
    (fun x => homOfLE (hKU x))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxK ⟨x, hx⟩⟩) t 0 fun x => ?_
  change L.presheaf.map (homOfLE (hKU x)).op t = L.presheaf.map (homOfLE (hKU x)).op 0
  rw [hK x, map_zero]

/-- The unit of `ν^* ⊣ ν_*` commutes with restriction of sections. -/
private theorem unit_app_map {W Y : Scheme.{0}} (ν : Y ⟶ W) (L : W.Modules) {V V' : W.Opens}
    (h : V' ≤ V) (t : Γ(L, V)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V'
        (L.presheaf.map (homOfLE h).op t) =
      ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono h)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).val (homOfLE h).op t

/-- **Local descent glues.** If a section `s` of `ν^* L` over `ν⁻¹ U` is, near every point of
`U`, the pullback of a section of `L`, then it is the pullback of a section of `L` over `U`. -/
private theorem exists_unit_app_eq_of_locally {W Y : Scheme.{0}} [IsReduced W] (ν : Y ⟶ W)
    [QuasiCompact ν]
    (hν : ∃ U₀ : W.Opens, Dense U₀.carrier ∧ Dense (ν ⁻¹ᵁ U₀).carrier ∧
      IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl))
    (L : W.Modules) (hL : IsLineBundle L) (U : W.Opens)
    (s : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U))
    (hloc : ∀ w ∈ U, ∃ (V : W.Opens) (hVU : V ≤ U) (t : Γ(L, V)), w ∈ V ∧
      ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t =
        ((Scheme.Modules.pullback ν).obj L).presheaf.map
          (homOfLE (ν.preimage_mono hVU)).op s) :
    ∃ t : Γ(L, U), ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U t = s := by
  choose V hVU t hwV ht using hloc
  let Vi : U → W.Opens := fun w => V w.1 w.2
  let ti : ∀ w : U, Γ(L, Vi w) := fun w => t w.1 w.2
  have hcover : U ≤ iSup Vi := fun w hw =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hwV w hw⟩
  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf Vi ti := by
    intro i j
    apply unit_app_injective ν hν L hL
    change ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app _
        (L.presheaf.map (homOfLE inf_le_left).op (ti i)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app _
        (L.presheaf.map (homOfLE inf_le_right).op (ti j))
    rw [unit_app_map, unit_app_map]
    change ((Scheme.Modules.pullback ν).obj L).presheaf.map _
        (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app _ (t i.1 i.2)) =
      ((Scheme.Modules.pullback ν).obj L).presheaf.map _
        (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app _ (t j.1 j.2))
    rw [ht, ht, map_map_homOfLE, map_map_homOfLE]
  obtain ⟨τ, hτ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨L.presheaf, L.isSheaf⟩ Vi U
    (fun i => homOfLE (hVU i.1 i.2)) hcover ti hcompat
  refine ⟨τ, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨((Scheme.Modules.pullback ν).obj L).presheaf, ((Scheme.Modules.pullback ν).obj L).isSheaf⟩
    (fun i => ν ⁻¹ᵁ Vi i) (ν ⁻¹ᵁ U) (fun i => homOfLE (ν.preimage_mono (hVU i.1 i.2)))
    (fun y hy => ?_) (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U τ) s
    fun i => ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hy)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · change ((Scheme.Modules.pullback ν).obj L).presheaf.map
          (homOfLE (ν.preimage_mono (hVU i.1 i.2))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U τ) =
        ((Scheme.Modules.pullback ν).obj L).presheaf.map
          (homOfLE (ν.preimage_mono (hVU i.1 i.2))).op s
    rw [← unit_app_map ν L (hVU i.1 i.2)]
    have := hτ i
    change L.presheaf.map (homOfLE (hVU i.1 i.2)).op τ = t i.1 i.2 at this
    rw [this, ht]

/-- Over an open on which `ν` restricts to an isomorphism, `ν` is an isomorphism on sections. -/
private theorem isIso_app_of_le {W Y : Scheme.{0}} (ν : Y ⟶ W) {U₀ : W.Opens}
    (hiso : IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl)) {V : W.Opens} (hV : V ≤ U₀) :
    IsIso (ν.app V) := by
  have : IsIso (ν ∣_ U₀) := by
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  have h2 : IsIso (ν.app (U₀.ι ''ᵁ (U₀.ι ⁻¹ᵁ V))) := by
    have h3 : IsIso (Scheme.Hom.app (ν ∣_ U₀) (U₀.ι ⁻¹ᵁ V)) := inferInstance
    rw [morphismRestrict_app] at h3
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Functor.map_isIso _ _) h3
  have e : U₀.ι ''ᵁ (U₀.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hV
  rwa [e] at h2

/-- **Descent at a seminormal point.** Let `z` be a point of `W` near which every function on the
normalization that vanishes at all points over `z` is, near `z`, a function on `W`. If some local
section `t` of `L` near `z` has `s - ν^* t` vanishing at every point over `z`, then near `z` the
section `s` of `ν^* L` is the pullback of a section of `L`. -/
private theorem exists_local_unit_app_eq_of_seminormalAt {W Y : Scheme.{0}} (ν : Y ⟶ W)
    (L : W.Modules) (hL : IsLineBundle L) (U : W.Opens)
    (s : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)) (z : W)
    (hsn : ∃ V₀ : W.Opens, z ∈ V₀ ∧ ∀ V : W.Opens, V ≤ V₀ → z ∈ V → ∀ ψ : Γ(Y, ν ⁻¹ᵁ V),
      (∀ y : Y, ν y = z → y ∉ Y.basicOpen ψ) →
      ∃ (V' : W.Opens) (hV' : V' ≤ V) (c : Γ(W, V')), z ∈ V' ∧
        ν.app V' c = Y.presheaf.map (homOfLE (ν.preimage_mono hV')).op ψ)
    (hval : ∃ (V : W.Opens) (hVU : V ≤ U) (t : Γ(L, V)), z ∈ V ∧
      ∀ y : Y, ν y = z →
        ∃ (V' : Y.Opens) (hV' : V' ≤ ν ⁻¹ᵁ V) (f : Γ(Y, V'))
          (τ : Γ((Scheme.Modules.pullback ν).obj L, V')),
          y ∈ V' ∧ y ∉ Y.basicOpen f ∧
          ((Scheme.Modules.pullback ν).obj L).presheaf.map
              (homOfLE (hV'.trans (ν.preimage_mono hVU))).op s -
            ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE hV').op
              (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t) =
            f • τ) :
    ∃ (V : W.Opens) (hVU : V ≤ U) (t : Γ(L, V)), z ∈ V ∧
      ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t =
        ((Scheme.Modules.pullback ν).obj L).presheaf.map
          (homOfLE (ν.preimage_mono hVU)).op s := by
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L
  obtain ⟨V₀, hzV₀, hsn⟩ := hsn
  obtain ⟨V, hVU, t, hzV, hfib⟩ := hval
  have hLi := isInvertibleModule_of_isLineBundle L hL
  have hLs : Stacks.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
      (structureSheafRing W.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hLi
  obtain ⟨K, hzK, a, ha⟩ : ∃ (K : W.Opens) (_ : z ∈ K) (a : Γ(L, K)), ∀ (V : W.Opens)
      (hV : V ≤ K), Function.Bijective
        (fun c : Γ(W, V) => c • L.presheaf.map (homOfLE hV).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible W.toRingedSpace _ L hLs z
  set N := K ⊓ V ⊓ V₀
  have hNK : N ≤ K := inf_le_left.trans inf_le_left
  have hNV : N ≤ V := inf_le_left.trans inf_le_right
  have hNV₀ : N ≤ V₀ := inf_le_right
  have hNU : N ≤ U := hNV.trans hVU
  have hzN : z ∈ N := ⟨⟨hzK, hzV⟩, hzV₀⟩
  set a' := L.presheaf.map (homOfLE hNK).op a
  have ha' : ∀ (V' : W.Opens) (hV' : V' ≤ N), Function.Bijective
      (fun c : Γ(W, V') => c • L.presheaf.map (homOfLE hV').op a') := fun V' hV' => by
    simpa only [a', map_map_homOfLE] using ha V' (hV'.trans hNK)
  set α : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ N) := η.app N a'
  set ηt : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ V) := η.app V t
  have hα := bijective_smul_unit_app ν L a' ha'
  obtain ⟨g, hg⟩ := (hα (ν ⁻¹ᵁ N) le_rfl).2
    (((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono hNU)).op s)
  change g • ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE le_rfl).op α = _ at hg
  rw [map_homOfLE_refl] at hg
  obtain ⟨c, hc⟩ := (ha' N le_rfl).2 (L.presheaf.map (homOfLE hNV).op t)
  replace hc : c • a' = L.presheaf.map (homOfLE hNV).op t := by
    rw [← hc]
    dsimp only
    rw [map_homOfLE_refl]
  have hηt :
      ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono hNV)).op ηt =
        ν.app N c • α := by
    rw [← unit_app_map ν L hNV, ← hc, Scheme.Modules.Hom.app_smul]
    rfl
  set ψ := g - ν.app N c
  have key : ∀ y : Y, ν y = z → y ∉ Y.basicOpen ψ := by
    intro y hy hyψ
    obtain ⟨V', hV', f, τ, hyV', hf, heq⟩ := hfib y hy
    set V'' := V' ⊓ ν ⁻¹ᵁ N
    have i1 : V'' ≤ V' := inf_le_left
    have i2 : V'' ≤ ν ⁻¹ᵁ N := inf_le_right
    have hy'' : y ∈ V'' := ⟨hyV', show ν y ∈ N by rw [hy]; exact hzN⟩
    obtain ⟨h, hh⟩ := (hα V'' i2).2
      (((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE i1).op τ)
    change h • ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE i2).op α = _ at hh
    have heq' := congrArg (((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE i1).op) heq
    rw [map_sub, map_map_homOfLE, map_map_homOfLE, Scheme.Modules.map_smul, ← hh] at heq'
    have e1 : ((Scheme.Modules.pullback ν).obj L).presheaf.map
          (homOfLE (i1.trans (hV'.trans (ν.preimage_mono hVU)))).op s =
        Y.presheaf.map (homOfLE i2).op g •
          ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE i2).op α := by
      rw [← Scheme.Modules.map_smul, hg, map_map_homOfLE]
    have e2 : ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (i1.trans hV')).op ηt =
        Y.presheaf.map (homOfLE i2).op (ν.app N c) •
          ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE i2).op α := by
      rw [← Scheme.Modules.map_smul, ← hηt, map_map_homOfLE]
    rw [e1, e2, ← sub_smul, smul_smul, ← map_sub] at heq'
    have hψf : Y.presheaf.map (homOfLE i2).op ψ = Y.presheaf.map (homOfLE i1).op f * h :=
      (hα V'' i2).1 heq'
    have : y ∈ Y.basicOpen (Y.presheaf.map (homOfLE i2).op ψ) := by
      rw [Scheme.basicOpen_res]
      exact ⟨hy'', hyψ⟩
    rw [hψf, Scheme.basicOpen_mul, Scheme.basicOpen_res] at this
    exact hf this.1.2
  obtain ⟨V', hV'N, d, hzV', hd⟩ := hsn N hNV₀ hzN ψ key
  refine ⟨V', hV'N.trans hNU, (W.presheaf.map (homOfLE hV'N).op c + d) •
    L.presheaf.map (homOfLE hV'N).op a', hzV', ?_⟩
  have e1 : (η.app V' (L.presheaf.map (homOfLE hV'N).op a') :
      Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ V')) =
      ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE (ν.preimage_mono hV'N)).op α :=
    unit_app_map ν L hV'N a'
  have e2 : ν.app V' (W.presheaf.map (homOfLE hV'N).op c) =
      Y.presheaf.map (homOfLE (ν.preimage_mono hV'N)).op (ν.app N c) := by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
    rfl
  have e3 : ν.app V' (W.presheaf.map (homOfLE hV'N).op c + d) =
      Y.presheaf.map (homOfLE (ν.preimage_mono hV'N)).op g := by
    rw [map_add, hd, e2, ← map_add, add_sub_cancel]
  set β : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ V') :=
    η.app V' (L.presheaf.map (homOfLE hV'N).op a')
  rw [Scheme.Modules.Hom.app_smul]
  change ν.app V' (W.presheaf.map (homOfLE hV'N).op c + d) • β = _
  rw [show β = _ from e1, e3, ← Scheme.Modules.map_smul, hg, map_map_homOfLE]

/-- In a quasi-sober Jacobson space, a non-closed point of an irreducible closed set of dimension
at most one is its generic point. -/
private theorem closure_singleton_eq_of_not_isClosed {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] [JacobsonSpace α] (Z : IrreducibleCloseds α)
    (hZ : topologicalKrullDim (Z : Set α) ≤ 1) {p : α} (hp : p ∈ Z)
    (hpc : ¬ IsClosed ({p} : Set α)) : closure {p} = Z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
  have hηZ : η ∈ (Z : Set α) := hη ▸ subset_closure rfl
  have hpZ : closure {p} ⊆ Z := closure_minimal (Set.singleton_subset_iff.mpr hp) Z.isClosed
  by_contra hne
  have hηp : η ∉ closure {p} := fun h => hne (hpZ.antisymm (by
    rw [← hη]; exact closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure))
  obtain ⟨q, hq, hqc⟩ := nonempty_inter_closedPoints (Z := closure {p}) ⟨p, subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  have hqc' : IsClosed ({q} : Set α) := hqc
  have hqp : p ∉ closure {q} := by
    rw [hqc'.closure_eq]
    rintro rfl
    exact hpc hqc'
  let K : ↥(Z : Set α) → IrreducibleCloseds (Z : Set α) := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hmemK : ∀ x y : (Z : Set α), x ∈ K y ↔ x.1 ∈ closure {y.1} := by
    intro x y
    change x ∈ closure ({y} : Set (Z : Set α)) ↔ _
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    rfl
  have hlt : ∀ x y : (Z : Set α), x.1 ∈ closure {y.1} → y.1 ∉ closure {x.1} → K x < K y := by
    intro x y hxy hyx
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun a ha => ?_, y, ?_, ?_⟩
    · rw [hmemK] at ha ⊢
      exact closure_minimal (Set.singleton_subset_iff.mpr hxy) isClosed_closure ha
    · exact (hmemK y y).mpr (subset_closure rfl)
    · exact mt (hmemK y x).mp hyx
  let q' : (Z : Set α) := ⟨q, hpZ hq⟩
  let p' : (Z : Set α) := ⟨p, hp⟩
  let η' : (Z : Set α) := ⟨η, hηZ⟩
  have h1 : K q' < K p' := hlt q' p' hq hqp
  have h2 : K p' < K η' := hlt p' η' (by rw [hη]; exact hp) hηp
  let s : LTSeries (IrreducibleCloseds (Z : Set α)) :=
    ⟨2, ![K q', K p', K η'], fun i => by fin_cases i; exacts [h1, h2]⟩
  have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim s).trans hZ
  norm_num at h3

/-- Let `Y ⟶ X` be a closed immersion onto a finite union of irreducible closed sets of dimension
at most one in a Jacobson scheme. Every point of `Y` outside a dense open `U₀` is closed. -/
private theorem isClosed_singleton_of_notMem_of_dense {X Y : Scheme.{0}} [JacobsonSpace X]
    (S : Finset (IrreducibleCloseds X)) (hSdim : ∀ Z ∈ S, topologicalKrullDim (Z : Set X) ≤ 1)
    (ι : Y ⟶ X) [IsClosedImmersion ι] (hι : Set.range ι = ⋃ Z ∈ S, (Z : Set X))
    {U₀ : Y.Opens} (hU₀ : Dense (U₀ : Set Y)) {p : Y} (hp : p ∉ U₀) :
    IsClosed ({p} : Set Y) := by
  classical
  by_contra hpc
  have hemb := ι.isClosedEmbedding
  have hpc' : ¬ IsClosed ({ι p} : Set X) := fun h => hpc (by
    rw [hemb.isClosed_iff_image_isClosed, Set.image_singleton]; exact h)
  set O : Set X := (⋃ (Z : IrreducibleCloseds X)
    (_ : Z ∈ S.filter (fun Z : IrreducibleCloseds X => ι p ∉ (Z : Set X))), (Z : Set X))ᶜ
    with hOdef
  have hO : IsOpen O := (isClosed_biUnion_finset
    fun (Z : IrreducibleCloseds X) _ => Z.isClosed).isOpen_compl
  have hpO : ι p ∈ O := by
    simp only [hOdef, Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, not_exists]
    rintro Z ⟨-, h⟩ h'; exact h h'
  obtain ⟨u, huO, huU⟩ := hU₀.inter_open_nonempty (ι ⁻¹' O) (hO.preimage ι.continuous) ⟨p, hpO⟩
  obtain ⟨Z, hZ, huZ⟩ : ∃ Z ∈ S, ι u ∈ (Z : Set X) := by
    have := hι ▸ Set.mem_range_self u
    simpa using this
  have hpZ : ι p ∈ (Z : Set X) := by
    by_contra h
    exact huO (Set.mem_iUnion₂.mpr ⟨Z, Finset.mem_filter.mpr ⟨hZ, h⟩, huZ⟩)
  have hspec : ι p ⤳ ι u := specializes_iff_mem_closure.mpr (by
    rw [closure_singleton_eq_of_not_isClosed Z (hSdim Z hZ) hpZ hpc']; exact huZ)
  exact hp ((hemb.isInducing.specializes_iff.mp hspec).mem_open U₀.isOpen huU)

/-- In a Noetherian quasi-sober space, if every point of a closed set `F` is closed, then every
point `z` has an open neighbourhood meeting `F` at most in `z`. -/
private theorem exists_isOpen_forall_notMem_or_eq {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {F : Set α} (hF : IsClosed F)
    (hFc : ∀ p ∈ F, IsClosed ({p} : Set α)) (z : α) :
    ∃ V : Set α, IsOpen V ∧ z ∈ V ∧ ∀ w ∈ V, w ∉ F ∨ w = z := by
  set A := F \ {z}
  have hAF : closure A ⊆ F := closure_minimal Set.diff_subset hF
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := A))
  have hsing : ∀ t ∈ S, z ∈ t → t = {z} := by
    intro t ht hzt
    obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hηt : η ∈ t := hη ▸ subset_closure rfl
    have hηc : IsClosed ({η} : Set α) := hFc η (hAF (hS ▸ Set.mem_sUnion_of_mem hηt ht))
    have hteq : t = {η} := by
      have : closure ({η} : Set α) = t := hη
      rw [← this, hηc.closure_eq]
    rw [hteq] at hzt ⊢
    rw [Set.mem_singleton_iff.mp hzt]
  refine ⟨(⋃₀ {t ∈ S | z ∉ t})ᶜ, ?_, ?_, ?_⟩
  · exact ((hSf.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hSc t ht.1).isOpen_compl
  · simp
  · intro w hw
    by_contra h
    push Not at h
    have hwA : w ∈ closure A := subset_closure ⟨h.1, h.2⟩
    rw [hS] at hwA
    obtain ⟨t, ht, hwt⟩ := hwA
    by_cases hzt : z ∈ t
    · rw [hsing t ht hzt] at hwt
      exact h.2 hwt
    · exact hw ⟨t, ⟨ht, hzt⟩, hwt⟩

/-- Two distinct components of an snc divisor meet in a reduced subscheme: at a common point their
ideals are generated by two members of a regular system of parameters, and the quotient by them is
a regular local ring. -/
private theorem isReduced_subscheme_sup {k : Type} [Field k] {R : Scheme.{0}}
    [IsLocallyNoetherian R] {sR : R ⟶ Spec (.of k)} {D : MMP.Mori.Divisor R}
    (hD : MMP.Mori.DivisorWithCoeffs.IsSNC sR D) {E E' : MMP.Mori.PrimeDivisor R}
    (hE : E ∈ D.support) (hE' : E' ∈ D.support) (hne : E ≠ E') :
    IsReduced (E.idealSheaf ⊔ E'.idealSheaf).subscheme := by
  have hst : ∀ q : (E.idealSheaf ⊔ E'.idealSheaf).subscheme,
      _root_.IsReduced ((E.idealSheaf ⊔ E'.idealSheaf).subscheme.presheaf.stalk q) := by
    intro q
    have hx : (E.idealSheaf ⊔ E'.idealSheaf).subschemeι q ∈
        ((E.idealSheaf ⊔ E'.idealSheaf).support : Set R) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.support_sup] at hx
    obtain ⟨hxE, hxE'⟩ := hx
    obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 ((E.idealSheaf ⊔ E'.idealSheaf).subschemeι q)
    have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    have hab : j ⟨E, hE, hxE⟩ ≠ j ⟨E', hE', hxE'⟩ := fun h =>
      hne (congrArg Subtype.val (hj h))
    obtain ⟨hreg, -⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz
      {j ⟨E, hE, hxE⟩, j ⟨E', hE', hxE'⟩}
    have hspan : Ideal.span (z '' (({j ⟨E, hE, hxE⟩, j ⟨E', hE', hxE'⟩} : Finset (Fin n)) :
        Set (Fin n))) = IdealSheafData.stalk (E.idealSheaf ⊔ E'.idealSheaf)
          ((E.idealSheaf ⊔ E'.idealSheaf).subschemeι q) := by
      rw [IdealSheafData.stalk_sup, hI ⟨E, hE, hxE⟩, hI ⟨E', hE', hxE'⟩, Finset.coe_pair,
        Set.image_pair, Ideal.span_insert]
    rw [hspan] at hreg
    have : IsDomain (R.presheaf.stalk ((E.idealSheaf ⊔ E'.idealSheaf).subschemeι q) ⧸
        IdealSheafData.stalk (E.idealSheaf ⊔ E'.idealSheaf)
          ((E.idealSheaf ⊔ E'.idealSheaf).subschemeι q)) :=
      IsRegularLocalRing.isDomain _
    exact isReduced_of_injective (IdealSheafData.subschemeStalkQuotEquiv _ q).symm
      (IdealSheafData.subschemeStalkQuotEquiv _ q).symm.injective
  exact isReduced_of_isReduced_stalk _

/-- **Pulling a function on the normalization back to a normal component.** Let `h : P ⟶ W` be a
morphism from an integral normal scheme meeting `V ⊓ U₀`, where `ν : W^ν ⟶ W` is integral and an
isomorphism over `U₀`. A function `ψ` on `ν⁻¹ V` defines, through `ν⁻¹` over `U₀`, a rational
function on `P`; it is integral over every local ring of `h⁻¹ V`, hence a function `σ` on
`h⁻¹ V`. Over `U₀`, `σ` is the pullback of `ψ` read on `W`, and `σ` vanishes at every point over a
closed point `z` over which `ψ` vanishes: the maximal ideal at such a point pulls back to a prime
of the functions on `ν⁻¹ N` lying over `z`. -/
private theorem exists_pullback_section {W Wν P : Scheme.{0}} [IsIntegral P] [IsNormal P]
    (ν : Wν ⟶ W) [IsIntegralHom ν] {U₀ : W.Opens}
    (hiso : IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl)) (h : P ⟶ W) {V : W.Opens}
    (hξ : ∃ x : P, h x ∈ V ⊓ U₀) (ψ : Γ(Wν, ν ⁻¹ᵁ V)) :
    ∃ σ : Γ(P, h ⁻¹ᵁ V),
      (∀ a : Γ(W, V ⊓ U₀), ν.app _ a =
          Wν.presheaf.map (homOfLE (ν.preimage_mono inf_le_left)).op ψ →
        P.presheaf.map (homOfLE (h.preimage_mono inf_le_left)).op σ = h.app _ a) ∧
      ∀ z : W, IsClosed {z} → (∀ y : Wν, ν y = z → y ∉ Wν.basicOpen ψ) →
        ∀ x : P, h x = z → x ∉ P.basicOpen σ := by
  classical
  set ξ := genericPoint P
  have hgen : ∀ x : P, ξ ⤳ x := fun x => (genericPoint_spec P).specializes (Set.mem_univ x)
  have hmemξ : ∀ (N : W.Opens) (x : P), h x ∈ N → h ξ ∈ N := fun N x hx =>
    ((hgen x).map h.continuous).mem_open N.2 hx
  replace hξ : h ξ ∈ V ⊓ U₀ := hmemξ _ hξ.choose hξ.choose_spec
  obtain ⟨y₀', hy₀'⟩ := (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl).surjective ⟨h ξ, hξ.2⟩
  have hνy₀ : ν y₀'.1 = h ξ := by
    have h2 := congrArg (fun z => U₀.ι z) hy₀'
    simp only [Scheme.Opens.ι_apply] at h2
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply] at h2
    exact h2
  set y₀ := y₀'.1
  have hst : IsIso (ν.stalkMap y₀) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (ν.resLEStalkMap (le_refl (ν ⁻¹ᵁ U₀)) y₀')).mp
      (((isIso_iff_isIso_stalkMap _).mp hiso).2 y₀')
  have hsp : h ξ ⤳ ν y₀ := by rw [hνy₀]
  have hy₀N : ∀ N : W.Opens, h ξ ∈ N → y₀ ∈ ν ⁻¹ᵁ N := fun N hN => by
    show ν y₀ ∈ N
    rw [hνy₀]
    exact hN
  let θ : ∀ N : W.Opens, h ξ ∈ N → (Γ(Wν, ν ⁻¹ᵁ N) →+* P.functionField) := fun N hN =>
    (h.stalkMap ξ).hom.comp ((W.presheaf.stalkSpecializes hsp).hom.comp
      ((inv (ν.stalkMap y₀)).hom.comp
        (Wν.presheaf.germ (ν ⁻¹ᵁ N) y₀ (hy₀N N hN)).hom))
  have hθres : ∀ (N N' : W.Opens) (hN' : h ξ ∈ N') (hle : N' ≤ N) (b : Γ(Wν, ν ⁻¹ᵁ N)),
      θ N' hN' (Wν.presheaf.map (homOfLE (ν.preimage_mono hle)).op b) = θ N (hle hN') b := by
    intro N N' hN' hle b
    simp only [θ, RingHom.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply]
  have hθν : ∀ (N : W.Opens) (hN : h ξ ∈ N) (a : Γ(W, N)),
      θ N hN (ν.app N a) = P.presheaf.germ (h ⁻¹ᵁ N) ξ hN (h.app N a) := by
    intro N hN a
    simp only [θ, RingHom.comp_apply]
    have hνN : ν y₀ ∈ N := hy₀N N hN
    rw [← Scheme.Hom.germ_stalkMap_apply ν N y₀ hνN,
      ← ConcreteCategory.comp_apply (ν.stalkMap y₀), IsIso.hom_inv_id, CommRingCat.id_apply]
    have hhN : h ξ ∈ N := hN
    rw [show (W.presheaf.stalkSpecializes hsp).hom (W.presheaf.germ N (ν y₀) hνN a) =
        W.presheaf.germ N (h ξ) hhN a from TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _]
    exact Scheme.Hom.germ_stalkMap_apply h N ξ hhN a
  have hθalg : ∀ (N : W.Opens) (x : P) (hx : x ∈ h ⁻¹ᵁ N) (a : Γ(W, N)),
      θ N (hmemξ N x hx) (ν.app N a) =
        algebraMap (P.presheaf.stalk x) P.functionField
          (P.presheaf.germ (h ⁻¹ᵁ N) x hx (h.app N a)) := by
    intro N x hx a
    haveI : Nonempty (h ⁻¹ᵁ N) := ⟨⟨x, hx⟩⟩
    rw [hθν N (hmemξ N x hx), Scheme.algebraMap_germ_eq_germToFunctionField]
  have hint : ∀ (N : W.Opens), IsAffineOpen N → ∀ (x : P) (hx : x ∈ h ⁻¹ᵁ N)
      (b : Γ(Wν, ν ⁻¹ᵁ N)),
      θ N (hmemξ N x hx) b ∈ (algebraMap (P.presheaf.stalk x) P.functionField).range := by
    intro N hN x hx b
    obtain ⟨p, hpm, hp⟩ := ν.isIntegral_app N hN b
    refine RingHom.mem_range.mpr (IsIntegrallyClosed.isIntegral_iff.mp ?_)
    refine ⟨p.map ((P.presheaf.germ (h ⁻¹ᵁ N) x hx).hom.comp (h.app N).hom), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap (P.presheaf.stalk x) P.functionField).comp
        ((P.presheaf.germ (h ⁻¹ᵁ N) x hx).hom.comp (h.app N).hom) =
        (θ N (hmemξ N x hx)).comp (ν.app N).hom :=
      RingHom.ext fun a => (hθalg N x hx a).symm
    rw [this, ← Polynomial.hom_eval₂, hp, map_zero]
  have hξV : h ξ ∈ V := hξ.1
  haveI : Nonempty (h ⁻¹ᵁ V) := ⟨⟨ξ, hξV⟩⟩
  obtain ⟨σ, hσ⟩ := MMP.Intersection.exists_germToFunctionField_eq_of_forall_mem_range_stalk
    (h ⁻¹ᵁ V) (z := θ V hξV ψ) fun x hx => by
      obtain ⟨_, ⟨N, hN, rfl⟩, hxN, hNV⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
        (show h x ∈ (V : Set W) from hx) V.2
      rw [← hθres V N (hmemξ N x hxN) hNV ψ]
      exact hint N hN x hxN _
  refine ⟨σ, fun a ha => ?_, fun z hz hψz x hxz hxσ => ?_⟩
  · haveI : Nonempty (h ⁻¹ᵁ (V ⊓ U₀)) := ⟨⟨ξ, hξ⟩⟩
    apply P.germToFunctionField_injective (h ⁻¹ᵁ (V ⊓ U₀))
    rw [MMP.Intersection.germToFunctionField_map, hσ,
      ← hθres V (V ⊓ U₀) hξ inf_le_left ψ, ← ha, hθν (V ⊓ U₀) hξ]
  · have hxV : x ∈ h ⁻¹ᵁ V := P.basicOpen_le σ hxσ
    have hzV : z ∈ V := hxz ▸ hxV
    obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (V : Set W) from hzV) V.2
    have hNV' : N ≤ V := hNV
    replace hN : IsAffineOpen N := hN
    haveI := hN.isOpenImmersion_fromSpec
    have hxN : x ∈ h ⁻¹ᵁ N := show h x ∈ N from hxz ▸ hzN
    have hinj := IsFractionRing.injective (P.presheaf.stalk x) P.functionField
    set A := (algebraMap (P.presheaf.stalk x) P.functionField).range
    let e : P.presheaf.stalk x ≃+* A := RingEquiv.ofBijective
      (algebraMap (P.presheaf.stalk x) P.functionField).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab),
        (algebraMap (P.presheaf.stalk x) P.functionField).rangeRestrict_surjective⟩
    let θx : Γ(Wν, ν ⁻¹ᵁ N) →+* P.presheaf.stalk x :=
      e.symm.toRingHom.comp ((θ N (hmemξ N x hxN)).codRestrict A (hint N hN x hxN))
    have hθx : ∀ b, algebraMap _ P.functionField (θx b) = θ N (hmemξ N x hxN) b := by
      intro b
      have : e (θx b) = (θ N (hmemξ N x hxN)).codRestrict A (hint N hN x hxN) b :=
        e.apply_symm_apply _
      exact congrArg Subtype.val this
    have hθxν : ∀ a : Γ(W, N),
        θx (ν.app N a) = P.presheaf.germ (h ⁻¹ᵁ N) x hxN (h.app N a) := fun a =>
      hinj (by rw [hθx, hθalg])
    let Q := Ideal.comap θx (IsLocalRing.maximalIdeal (P.presheaf.stalk x))
    haveI hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hN' : IsAffineOpen (ν ⁻¹ᵁ N) := hN.preimage ν
    let q : ↥(Spec Γ(Wν, ν ⁻¹ᵁ N)) := ⟨Q, hQ⟩
    set y := hN'.fromSpec q with hy
    have h1 : hN.fromSpec (Spec.map (ν.appLE N (ν ⁻¹ᵁ N) le_rfl) q) = ν y := by
      rw [hy, ← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec ν hN hN' le_rfl,
        Scheme.Hom.comp_apply]
    set pz := hN.primeIdealOf ⟨z, hzN⟩
    have hpz : hN.fromSpec pz = z := hN.fromSpec_primeIdealOf ⟨z, hzN⟩
    have hpzmax : pz.asIdeal.IsMaximal := by
      rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      have : hN.fromSpec ⁻¹' {z} = {pz} := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hq
          exact hN.fromSpec.isOpenEmbedding.injective (hq.trans hpz.symm)
        · rintro rfl
          exact hpz
      have hc : IsClosed (hN.fromSpec ⁻¹' {z}) := hz.preimage hN.fromSpec.continuous
      rw [this] at hc
      exact hc
    have hle : pz.asIdeal ≤ Q.comap (ν.appLE N (ν ⁻¹ᵁ N) le_rfl).hom := by
      intro a ha
      show θx ((ν.appLE N (ν ⁻¹ᵁ N) le_rfl) a) ∈ IsLocalRing.maximalIdeal _
      rw [← Scheme.Hom.app_eq_appLE, hθxν, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        ← Scheme.mem_basicOpen _ _ x hxN, ← Scheme.preimage_basicOpen]
      intro hxa
      have hza : z ∈ W.basicOpen a := hxz ▸ hxa
      have : pz ∈ hN.fromSpec ⁻¹ᵁ W.basicOpen a := by
        change hN.fromSpec pz ∈ W.basicOpen a
        rw [hpz]
        exact hza
      rw [hN.fromSpec_preimage_basicOpen] at this
      exact this ha
    have hcomap : Spec.map (ν.appLE N (ν ⁻¹ᵁ N) le_rfl) q = pz :=
      PrimeSpectrum.ext (hpzmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
    have hνy : ν y = z := by rw [← h1, hcomap, hpz]
    have hψQ : Wν.presheaf.map (homOfLE (ν.preimage_mono hNV')).op ψ ∈ Q := by
      by_contra hn
      have hmem : q ∈
          PrimeSpectrum.basicOpen (Wν.presheaf.map (homOfLE (ν.preimage_mono hNV')).op ψ) := hn
      rw [← hN'.fromSpec_preimage_basicOpen] at hmem
      have hmem' : y ∈ Wν.basicOpen (Wν.presheaf.map (homOfLE (ν.preimage_mono hNV')).op ψ) :=
        hmem
      rw [Scheme.basicOpen_res] at hmem'
      exact hψz y hνy hmem'.2
    have hgerm : P.presheaf.germ (h ⁻¹ᵁ V) x hxV σ =
        θx (Wν.presheaf.map (homOfLE (ν.preimage_mono hNV')).op ψ) :=
      hinj (by rw [hθx, hθres V N (hmemξ N x hxN) hNV' ψ,
        Scheme.algebraMap_germ_eq_germToFunctionField, hσ])
    rw [Scheme.mem_basicOpen _ _ x hxV, hgerm] at hxσ
    exact (IsLocalRing.mem_maximalIdeal _).mp hψQ hxσ

/-- The non-vanishing locus of a difference lies in the union of the non-vanishing loci. -/
private theorem basicOpen_sub_le {X : Scheme.{0}} {U : X.Opens} (f g : Γ(X, U)) :
    X.basicOpen (f - g) ≤ X.basicOpen f ⊔ X.basicOpen g := by
  rw [sub_eq_add_neg]
  refine (X.basicOpen_add_le f (-g)).trans (sup_le_sup_left ?_ _)
  rw [← neg_one_mul, Scheme.basicOpen_mul]
  exact inf_le_right

/-- **Descent of functions through the lc-centre resolution.** Let `φ : T ⟶ W` be a surjective
morphism from the support of an snc divisor `D` on a smooth variety `R` inducing isomorphisms on
all rings of sections, let `ν : W^ν ⟶ W` be integral from a normal scheme and an isomorphism over
`U₀`, and let `z` be a closed point. On an open `V` all of whose points other than `z` lie in `U₀`,
every function on `ν⁻¹ V` vanishing at all points over `z` is the pullback of a function on `V`. -/
private theorem exists_app_eq_of_forall_mem_or_eq {W Wν R : Scheme.{0}} [IsNormal Wν]
    (ν : Wν ⟶ W) [IsIntegralHom ν] {U₀ : W.Opens}
    (hiso : IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl))
    [IsLocallyNoetherian R] {sR : R ⟶ Spec (.of ℂ)} [Smooth sR] (hR : MMP.Mori.IsVariety ℂ sR)
    {D : MMP.Mori.Divisor R} (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC sR D)
    (hDsnc : MMP.Intersection.IsSNCDivisor sR D)
    (φ : D.suppIdeal.subscheme ⟶ W) (hφsurj : Function.Surjective φ)
    (hφiso : ∀ U, IsIso (φ.app U))
    {z : W} (hz : IsClosed {z}) {V : W.Opens} (hVU : ∀ w ∈ V, w ∈ U₀ ∨ w = z)
    (ψ : Γ(Wν, ν ⁻¹ᵁ V)) (hψ : ∀ y : Wν, ν y = z → y ∉ Wν.basicOpen ψ) :
    ∃ c : Γ(W, V), ν.app V c = ψ := by
  classical
  haveI : IsReduced D.suppIdeal.subscheme :=
    inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme)
  haveI : IsReduced Wν := isReduced_of_isNormal Wν
  obtain ⟨URs, hURo, hUR⟩ :=
    D.suppIdeal.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp (φ ⁻¹ᵁ V).2
  let UR : R.Opens := ⟨URs, hURo⟩
  have hTV : D.suppIdeal.subschemeι ⁻¹ᵁ UR = φ ⁻¹ᵁ V := Opens.ext hUR
  have hle : ∀ E : D.support, D.suppIdeal ≤ E.1.idealSheaf := fun E =>
    (MMP.Intersection.suppIdeal_eq_finsetInf D).le.trans (Finset.inf_le E.2)
  let incl : ∀ E : D.support, E.1.idealSheaf.subscheme ⟶ D.suppIdeal.subscheme := fun E =>
    Scheme.IdealSheafData.inclusion (hle E)
  let hh : ∀ E : D.support, E.1.idealSheaf.subscheme ⟶ W := fun E => incl E ≫ φ
  have hinclι : ∀ E : D.support,
      incl E ≫ D.suppIdeal.subschemeι = E.1.idealSheaf.subschemeι := fun E =>
    Scheme.IdealSheafData.inclusion_subschemeι (hle E)
  have hEU : ∀ E : D.support, E.1.idealSheaf.subschemeι ⁻¹ᵁ UR = hh E ⁻¹ᵁ V := by
    intro E
    rw [← hinclι E, Scheme.Hom.comp_preimage, hTV, ← Scheme.Hom.comp_preimage]
  have hcover : ∀ τ : D.suppIdeal.subscheme,
      ∃ (E : D.support) (e : E.1.idealSheaf.subscheme), incl E e = τ := by
    intro τ
    have h1 : D.suppIdeal.subschemeι τ ∈ (D.suppIdeal.support : Set R) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨τ, rfl⟩
    rw [MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal, SetLike.mem_coe,
      MMP.Mori.DivisorWithCoeffs.mem_supp_iff] at h1
    obtain ⟨P, hP, hxP⟩ := h1
    have hPs : P ∈ D.support := Finsupp.mem_support_iff.mpr hP
    have h2 : D.suppIdeal.subschemeι τ ∈ (P.idealSheaf.support : Set R) := hxP
    rw [← Scheme.IdealSheafData.range_subschemeι] at h2
    obtain ⟨e, he⟩ := h2
    refine ⟨⟨P, hPs⟩, e, D.suppIdeal.subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hinclι ⟨P, hPs⟩, he]
  have hnorm : ∀ E : D.support, IsNormal E.1.idealSheaf.subscheme := fun E => by
    haveI : Smooth (E.1.idealSheaf.subschemeι ≫ sR) :=
      (MMP.Mori.isSmoothScheme_iff _).mp (hsnc.1 E.1 E.2)
    exact isNormal_of_smooth_over_field (E.1.idealSheaf.subschemeι ≫ sR)
  have hcomp : ∀ E : D.support, (∃ e, hh E e ∈ V ⊓ U₀) →
      ∃ σ : Γ(E.1.idealSheaf.subscheme, hh E ⁻¹ᵁ V),
        (∀ a : Γ(W, V ⊓ U₀), ν.app _ a =
            Wν.presheaf.map (homOfLE (ν.preimage_mono inf_le_left)).op ψ →
          E.1.idealSheaf.subscheme.presheaf.map
            (homOfLE ((hh E).preimage_mono inf_le_left)).op σ = (hh E).app _ a) ∧
        ∀ z : W, IsClosed {z} → (∀ y : Wν, ν y = z → y ∉ Wν.basicOpen ψ) →
          ∀ x, hh E x = z → x ∉ E.1.idealSheaf.subscheme.basicOpen σ := fun E hA => by
    haveI := E.1.integral
    haveI := hnorm E
    exact exists_pullback_section ν hiso (hh E) hA ψ
  choose σ hσU hσz using hcomp
  haveI : IsIso (ν.app (V ⊓ U₀)) := isIso_app_of_le ν hiso inf_le_right
  obtain ⟨ψ₀, hψ₀⟩ := (ConcreteCategory.bijective_of_isIso (ν.app (V ⊓ U₀))).2
    (Wν.presheaf.map (homOfLE (ν.preimage_mono inf_le_left)).op ψ)
  let s : ∀ E : D.support, Γ(E.1.idealSheaf.subscheme, E.1.idealSheaf.subschemeι ⁻¹ᵁ UR) :=
    fun E => if hA : ∃ e, hh E e ∈ V ⊓ U₀ then
      E.1.idealSheaf.subscheme.presheaf.map (homOfLE (hEU E).le).op (σ E hA) else 0
  have hs0 : ∀ (E : D.support) (e : E.1.idealSheaf.subscheme), hh E e = z →
      e ∉ E.1.idealSheaf.subscheme.basicOpen (s E) := by
    intro E e he
    by_cases hA : ∃ e, hh E e ∈ V ⊓ U₀
    · simp only [s, dif_pos hA, Scheme.basicOpen_res]
      exact fun h => hσz E hA z hz hψ e he h.2
    · simp only [s, dif_neg hA, Scheme.basicOpen_zero]
      exact id
  have hsU : ∀ (E : D.support) (hA : ∃ e, hh E e ∈ V ⊓ U₀)
      (hle' : hh E ⁻¹ᵁ (V ⊓ U₀) ≤ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR),
      E.1.idealSheaf.subscheme.presheaf.map (homOfLE hle').op (s E) = (hh E).app _ ψ₀ := by
    intro E hA hle'
    simp only [s, dif_pos hA]
    exact (TopCat.Presheaf.restrict_restrict _ _ _).trans (hσU E hA ψ₀ hψ₀)
  have hagree : ∀ E E' : D.support,
      (Scheme.IdealSheafData.inclusion le_sup_left).appLE
          (E.1.idealSheaf.subschemeι ⁻¹ᵁ UR)
          ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ UR)
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
          (s E) =
        (Scheme.IdealSheafData.inclusion le_sup_right).appLE
          (E'.1.idealSheaf.subschemeι ⁻¹ᵁ UR)
          ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ UR)
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
          (s E') := by
    intro E E'
    by_cases hEE : E = E'
    · subst hEE; rfl
    have hne : E.1 ≠ E'.1 := fun h => hEE (Subtype.ext h)
    haveI := isReduced_subscheme_sup hsnc E.2 E'.2 hne
    set I := E.1.idealSheaf ⊔ E'.1.idealSheaf
    set i₁ := Scheme.IdealSheafData.inclusion (le_sup_left : E.1.idealSheaf ≤ I)
    set i₂ := Scheme.IdealSheafData.inclusion (le_sup_right : E'.1.idealSheaf ≤ I)
    have hi₁ : i₁ ≫ E.1.idealSheaf.subschemeι = I.subschemeι :=
      Scheme.IdealSheafData.inclusion_subschemeι _
    have hi₂ : i₂ ≫ E'.1.idealSheaf.subschemeι = I.subschemeι :=
      Scheme.IdealSheafData.inclusion_subschemeι _
    have hcommon : i₁ ≫ hh E = i₂ ≫ hh E' := by
      have : i₁ ≫ incl E = i₂ ≫ incl E' := by
        rw [← cancel_mono D.suppIdeal.subschemeι, Category.assoc, Category.assoc, hinclι,
          hinclι, hi₁, hi₂]
      simp only [hh, ← Category.assoc, this]
    have e₁ : I.subschemeι ⁻¹ᵁ UR ≤ i₁ ⁻¹ᵁ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR := by
      rw [← Scheme.Hom.comp_preimage, hi₁]
    have e₂ : I.subschemeι ⁻¹ᵁ UR ≤ i₂ ⁻¹ᵁ E'.1.idealSheaf.subschemeι ⁻¹ᵁ UR := by
      rw [← Scheme.Hom.comp_preimage, hi₂]
    set a₁ := i₁.appLE (E.1.idealSheaf.subschemeι ⁻¹ᵁ UR) (I.subschemeι ⁻¹ᵁ UR) e₁ (s E)
    set a₂ := i₂.appLE (E'.1.idealSheaf.subschemeι ⁻¹ᵁ UR) (I.subschemeι ⁻¹ᵁ UR) e₂ (s E')
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    ext q
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hq
    have hqU : q ∈ I.subschemeι ⁻¹ᵁ UR := Scheme.basicOpen_le _ _ hq
    have hwV : hh E (i₁ q) ∈ V := by
      have : i₁ q ∈ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR := e₁ hqU
      rw [hEU E] at this
      exact this
    have hw : hh E' (i₂ q) = hh E (i₁ q) := by
      rw [← Scheme.Hom.comp_apply, ← hcommon, Scheme.Hom.comp_apply]
    rcases hVU _ hwV with hwU | hwz
    · have hA : ∃ e, hh E e ∈ V ⊓ U₀ := ⟨i₁ q, hwV, hwU⟩
      have hA' : ∃ e, hh E' e ∈ V ⊓ U₀ := ⟨i₂ q, hw ▸ hwV, hw ▸ hwU⟩
      set O := I.subschemeι ⁻¹ᵁ UR ⊓ (i₁ ≫ hh E) ⁻¹ᵁ (V ⊓ U₀)
      have hqO : q ∈ O := ⟨hqU, show hh E (i₁ q) ∈ V ⊓ U₀ from ⟨hwV, hwU⟩⟩
      have aux : ∀ (f g : I.subscheme ⟶ W) (_ : f = g) (h₁ : O ≤ f ⁻¹ᵁ (V ⊓ U₀))
          (h₂ : O ≤ g ⁻¹ᵁ (V ⊓ U₀)), f.appLE (V ⊓ U₀) O h₁ = g.appLE (V ⊓ U₀) O h₂ := by
        rintro f g rfl h₁ h₂; rfl
      have key : ∀ (F : D.support) (i : I.subscheme ⟶ F.1.idealSheaf.subscheme)
          (hi : i ≫ hh F = i₁ ≫ hh E) (hAF : ∃ e, hh F e ∈ V ⊓ U₀)
          (e : I.subschemeι ⁻¹ᵁ UR ≤ i ⁻¹ᵁ F.1.idealSheaf.subschemeι ⁻¹ᵁ UR),
          I.subscheme.presheaf.map (homOfLE (inf_le_left : O ≤ _)).op
              (i.appLE _ _ e (s F)) =
            (i₁ ≫ hh E).appLE (V ⊓ U₀) O inf_le_right ψ₀ := by
        intro F i hi hAF e
        have hO' : O ≤ i ⁻¹ᵁ (hh F ⁻¹ᵁ (V ⊓ U₀)) := by
          intro x hx
          have h2 : (i₁ ≫ hh E) x ∈ V ⊓ U₀ := hx.2
          show (i ≫ hh F) x ∈ V ⊓ U₀
          rw [hi]
          exact h2
        have hle' : hh F ⁻¹ᵁ (V ⊓ U₀) ≤ F.1.idealSheaf.subschemeι ⁻¹ᵁ UR := by
          rw [hEU F]
          exact (hh F).preimage_mono inf_le_left
        rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map,
          ← Scheme.Hom.map_appLE i hO' (homOfLE hle').op, ConcreteCategory.comp_apply,
          hsU F hAF hle', ← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE,
          Scheme.Hom.appLE_comp_appLE]
        exact congrArg (fun f => f.hom ψ₀) (aux _ _ hi _ _)
      have k1 := key E i₁ rfl hA e₁
      have k2 := key E' i₂ hcommon.symm hA' e₂
      have hzero : I.subscheme.presheaf.map (homOfLE (inf_le_left : O ≤ _)).op (a₁ - a₂) = 0 := by
        rw [map_sub, k1, k2, sub_self]
      have h3 := congrArg I.subscheme.basicOpen hzero
      simp only [Scheme.basicOpen_res, Scheme.basicOpen_zero] at h3
      have hmem : q ∈ O ⊓ I.subscheme.basicOpen (a₁ - a₂) := ⟨hqO, hq⟩
      rw [h3] at hmem
      exact hmem
    · have h1 := hs0 E (i₁ q) hwz
      have h2 := hs0 E' (i₂ q) (hw.trans hwz)
      rcases basicOpen_sub_le a₁ a₂ hq with h | h
      · rw [Scheme.basicOpen_appLE] at h
        exact h1 h.2
      · rw [Scheme.basicOpen_appLE] at h
        exact h2 h.2
  obtain ⟨t, ht, -⟩ := (hDsnc.existsUnique_glue hR UR).1 s hagree
  set t' : Γ(D.suppIdeal.subscheme, φ ⁻¹ᵁ V) :=
    D.suppIdeal.subscheme.presheaf.map (homOfLE hTV.ge).op t
  haveI := hφiso V
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (φ.app V)).2 t'
  refine ⟨c, ?_⟩
  have htE : ∀ (E : D.support) (O : E.1.idealSheaf.subscheme.Opens)
      (hO : O ≤ incl E ⁻¹ᵁ (φ ⁻¹ᵁ V)) (hO' : O ≤ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR),
      (incl E).appLE (φ ⁻¹ᵁ V) O hO t' =
        E.1.idealSheaf.subscheme.presheaf.map (homOfLE hO').op (s E) := by
    intro E O hO hO'
    rw [← ht E, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  ext y
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hy
  have hyV : y ∈ ν ⁻¹ᵁ V := Scheme.basicOpen_le _ _ hy
  rcases hVU (ν y) hyV with hyU | hyz
  · have hc₀ : W.presheaf.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op c = ψ₀ := by
      haveI := hφiso (V ⊓ U₀)
      apply (ConcreteCategory.bijective_of_isIso (φ.app (V ⊓ U₀))).1
      have hnat : φ.app (V ⊓ U₀) (W.presheaf.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op c) =
          D.suppIdeal.subscheme.presheaf.map
            (homOfLE (φ.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))).op t' := by
        rw [← hc, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
        rfl
      rw [hnat, ← sub_eq_zero]
      apply eq_zero_of_basicOpen_eq_bot
      ext τ
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hτ
      have hτV : τ ∈ φ ⁻¹ᵁ (V ⊓ U₀) := Scheme.basicOpen_le _ _ hτ
      obtain ⟨E, e, rfl⟩ := hcover τ
      have hA : ∃ e', hh E e' ∈ V ⊓ U₀ := ⟨e, hτV⟩
      have hle' : hh E ⁻¹ᵁ (V ⊓ U₀) ≤ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR := by
        rw [hEU E]
        exact (hh E).preimage_mono inf_le_left
      have hle'' : hh E ⁻¹ᵁ (V ⊓ U₀) ≤ incl E ⁻¹ᵁ (φ ⁻¹ᵁ V) :=
        (hh E).preimage_mono inf_le_left
      have hpull : (incl E).appLE (φ ⁻¹ᵁ (V ⊓ U₀)) (hh E ⁻¹ᵁ (V ⊓ U₀))
          (Scheme.Hom.comp_preimage (incl E) φ (V ⊓ U₀)).le
          (D.suppIdeal.subscheme.presheaf.map
              (homOfLE (φ.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))).op t' -
            φ.app (V ⊓ U₀) ψ₀) = 0 := by
        rw [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
          htE E _ hle'' hle', hsU E hA hle', ← ConcreteCategory.comp_apply,
          Scheme.Hom.app_eq_appLE]
        exact ConcreteCategory.congr_hom
          (Scheme.Hom.comp_appLE (incl E) φ (V ⊓ U₀) (hh E ⁻¹ᵁ (V ⊓ U₀)) le_rfl) ψ₀
      have h3 := congrArg E.1.idealSheaf.subscheme.basicOpen hpull
      simp only [Scheme.basicOpen_zero] at h3
      rw [Scheme.basicOpen_appLE] at h3
      have hmem : e ∈ hh E ⁻¹ᵁ (V ⊓ U₀) ⊓ incl E ⁻¹ᵁ D.suppIdeal.subscheme.basicOpen
          (D.suppIdeal.subscheme.presheaf.map
              (homOfLE (φ.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))).op t' -
            φ.app (V ⊓ U₀) ψ₀) := ⟨hτV, hτ⟩
      rw [h3] at hmem
      exact hmem
    have hnat : Wν.presheaf.map (homOfLE (ν.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))).op
        (ν.app V c) = ν.app (V ⊓ U₀) (W.presheaf.map (homOfLE inf_le_left).op c) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
      rfl
    have hzero : Wν.presheaf.map (homOfLE (ν.preimage_mono (inf_le_left : V ⊓ U₀ ≤ V))).op
        (ν.app V c - ψ) = 0 := by
      rw [map_sub, hnat, hc₀, hψ₀, sub_self]
    have h3 := congrArg Wν.basicOpen hzero
    simp only [Scheme.basicOpen_res, Scheme.basicOpen_zero] at h3
    have hmem : y ∈ ν ⁻¹ᵁ (V ⊓ U₀) ⊓ Wν.basicOpen (ν.app V c - ψ) := ⟨⟨hyV, hyU⟩, hy⟩
    rw [h3] at hmem
    exact hmem
  · have hzc : z ∉ W.basicOpen c := by
      intro hzc
      obtain ⟨τ, hτ⟩ := hφsurj z
      obtain ⟨E, e, rfl⟩ := hcover τ
      have hzV : z ∈ V := hyz ▸ hyV
      have heU : e ∈ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR := by
        rw [hEU E]
        show φ (incl E e) ∈ V
        rw [hτ]
        exact hzV
      have h1 : incl E e ∈ D.suppIdeal.subscheme.basicOpen t' := by
        rw [← hc, ← Scheme.preimage_basicOpen]
        show φ (incl E e) ∈ W.basicOpen c
        rw [hτ]
        exact hzc
      have h2 := htE E _ ((hEU E).trans (Scheme.Hom.comp_preimage (incl E) φ V)).le le_rfl
      have h3 := congrArg E.1.idealSheaf.subscheme.basicOpen h2
      simp only [Scheme.basicOpen_res] at h3
      rw [Scheme.basicOpen_appLE] at h3
      have hmem : e ∈ E.1.idealSheaf.subschemeι ⁻¹ᵁ UR ⊓
          incl E ⁻¹ᵁ D.suppIdeal.subscheme.basicOpen t' := ⟨heU, h1⟩
      rw [h3] at hmem
      exact hs0 E e hτ hmem.2
    rcases basicOpen_sub_le _ _ hy with h | h
    · rw [← Scheme.preimage_basicOpen] at h
      exact hzc (hyz ▸ h)
    · exact hψ y hyz h

/-- **A union of lc centres of dimension at most one on an lc surface is seminormal.** Near a
closed point `z` of `W`, a function on the normalization vanishing at every point over `z` is, near
`z`, a function on `W`. -/
private theorem exists_app_eq_of_notMem_basicOpen
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    {K : Divisor X} {B : QDivisor X} (hB : IsLcPair sX 2 K B) (hBeff : B.IsEffective)
    (S : Finset (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX 2 K B E (-1))
    (hSdim : ∀ Z ∈ S, topologicalKrullDim (Z : Set X) ≤ 1)
    {Wν : Scheme.{0}} [IsNormal Wν]
    (ν : Wν ⟶ (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme)
    [IsIntegralHom ν]
    (hν : ∃ U₀ : Opens _, Dense U₀.carrier ∧ Dense (ν ⁻¹ᵁ U₀).carrier ∧
      IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl))
    (z : (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme)
    (hz : IsClosed {z}) :
    ∃ V₀ : Opens _, z ∈ V₀ ∧ ∀ V : Opens _, V ≤ V₀ → z ∈ V → ∀ ψ : Γ(Wν, ν ⁻¹ᵁ V),
      (∀ y : Wν, ν y = z → y ∉ Wν.basicOpen ψ) →
      ∃ (V' : Opens _) (hV' : V' ≤ V) (c : Γ((Scheme.IdealSheafData.vanishingIdeal
        ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme,
          V')), z ∈ V' ∧
        ν.app V' c = Wν.presheaf.map (homOfLE (ν.preimage_mono hV')).op ψ := by
  obtain ⟨U₀, hU₀, -, hiso⟩ := hν
  by_cases hz₀ : z ∈ U₀
  · refine ⟨U₀, hz₀, fun V hV hzV ψ _ => ⟨V, le_rfl, ?_⟩⟩
    have : IsIso (ν.app V) := isIso_app_of_le ν hiso hV
    obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (ν.app V)).2 ψ
    refine ⟨c, hzV, hc.trans ?_⟩
    rw [show homOfLE (ν.preimage_mono (le_refl V)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  -- `z ∉ U₀`: near `z`, every other point of `W` lies in `U₀`
  classical
  have hιW : Set.range (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subschemeι =
        ⋃ Z ∈ S, (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : IsNoetherian X := {}
  haveI : NoetherianSpace (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme :=
    (Scheme.IdealSheafData.subschemeι _).isClosedEmbedding.isEmbedding.noetherianSpace
  have hFc : ∀ p ∈ (U₀ : Set _)ᶜ, IsClosed ({p} : Set _) := fun p hp =>
    isClosed_singleton_of_notMem_of_dense S hSdim _ hιW hU₀ hp
  obtain ⟨V₀s, hV₀o, hzV₀, hV₀⟩ :=
    exists_isOpen_forall_notMem_or_eq U₀.isOpen.isClosed_compl hFc z
  -- the lc-centre resolution `φ : T ⟶ W`, with `φ_* 𝒪_T = 𝒪_W`
  obtain ⟨R, _, _, _, sR, hR, g, T, φ, hsm, -, -, -, hsnc, hTW, hφ, hφiso, -⟩ :=
    exists_isIso_app_comp_subschemeι_vanishingIdeal_of_isLcPair sX hproj.isProjective hB hBeff
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩
      (S : Set (IrreducibleCloseds X)) hS rfl
  haveI : Smooth sR := (isSmoothScheme_iff sR).mp hsm
  have hφsurj : Function.Surjective φ := by
    intro w
    have h1 : (Scheme.IdealSheafData.subschemeι _) w ∈ ⋃ Z ∈ S, (Z : Set X) :=
      hιW.subset (Set.mem_range_self w)
    have hw : (Scheme.IdealSheafData.subschemeι _) w ∈ g.base '' ⋃ P ∈ T, (P.support : Set R) := by
      rw [hTW]
      exact h1
    obtain ⟨r, hr, hgr⟩ := hw
    obtain ⟨P, hP, hrP⟩ := Set.mem_iUnion₂.mp hr
    have hrT : r ∈ ((DivisorWithCoeffs.suppIdeal
        (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R)).support : Set R) := by
      rw [DivisorWithCoeffs.coe_support_suppIdeal, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
      refine ⟨P, ?_, hrP⟩
      rw [show DivisorWithCoeffs.coeff (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R) P =
          (MMP.Intersection.reducedDivisorOf T).coeff P from rfl,
        MMP.Intersection.coeff_reducedDivisorOf, if_pos hP]
      exact one_ne_zero
    rw [← Scheme.IdealSheafData.range_subschemeι] at hrT
    obtain ⟨τ, rfl⟩ := hrT
    refine ⟨τ, (Scheme.IdealSheafData.subschemeι _).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ, Scheme.Hom.comp_apply]
    exact hgr
  refine ⟨⟨V₀s, hV₀o⟩, hzV₀, fun V hVV₀ hzV ψ hψ => ?_⟩
  obtain ⟨c, hc⟩ := exists_app_eq_of_forall_mem_or_eq ν hiso hR.toIsVariety hsnc
    (hsnc.isSNCDivisor (MMP.Intersection.isReducedEffective_reducedDivisorOf T)) φ hφsurj hφiso hz
    (V := V) (fun w hw => (hV₀ w (hVV₀ hw)).imp_left fun h => by simpa using h) ψ hψ
  refine ⟨V, le_rfl, c, hzV, ?_⟩
  rw [hc, show homOfLE (ν.preimage_mono (le_refl V)) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end Proof_lem_mmp_surface_lc_centre_curve_functions

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open MMP.Intersection.Scheme.Modules (IsLineBundle)

namespace MMP.Mori

open Proof_lem_mmp_surface_lc_centre_curve_functions in
/-- **Seminormality of a union of lc centres on a surface.** Let `(X, B)` be an lc pair, with
effective `ℚ`-boundary `B` and canonical divisor `K`, on a normal projective complex surface `X`.
Let `S` be a finite set of lc centres of `(X, B)` of dimension at most one, `W` the reduced closed
subscheme supported on their union, `ν : W^ν ⟶ W` its normalization (an integral morphism from a
normal scheme which is an isomorphism over a dense open with dense preimage) and `L` a line bundle
on `W`. Then for every open `U ⊆ W`, a section `s` of `ν^* L` over `ν⁻¹ U` is the pullback of a
unique section of `L` over `U` if and only if for every closed point `w ∈ U` there is a section `t`
of `L` near `w` such that `s - ν^* t` vanishes at every point of `W^ν` over `w`, i.e. the values of
`s` over `w` agree in the fibre `L(w)`. -/
@[mmp "lem_mmp_surface_lc_centre_curve_functions"]
public theorem IsLcPair.existsUnique_unit_app_eq_iff_of_isNormalization
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hproj : IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 2)
    {K : Divisor X} {B : QDivisor X} (hB : IsLcPair sX 2 K B) (hBeff : B.IsEffective)
    (S : Finset (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX 2 K B E (-1))
    (hSdim : ∀ Z ∈ S, topologicalKrullDim (Z : Set X) ≤ 1)
    {Wν : Scheme.{0}} [IsNormal Wν]
    (ν : Wν ⟶ (Scheme.IdealSheafData.vanishingIdeal
      ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme)
    [IsIntegralHom ν]
    (hν : ∃ U₀ : Opens _, Dense U₀.carrier ∧ Dense (ν ⁻¹ᵁ U₀).carrier ∧
      IsIso (ν.resLE U₀ (ν ⁻¹ᵁ U₀) le_rfl))
    (L : Scheme.Modules _) (hL : IsLineBundle L) (U : Opens _)
    (s : Γ((Scheme.Modules.pullback ν).obj L, ν ⁻¹ᵁ U)) :
    (∃! t : Γ(L, U), ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app U t = s) ↔
      ∀ w ∈ U, IsClosed {w} →
        ∃ (V : Opens _) (hVU : V ≤ U) (t : Γ(L, V)), w ∈ V ∧
          ∀ w' : Wν, ν w' = w →
            ∃ (V' : Wν.Opens) (hV' : V' ≤ ν ⁻¹ᵁ V) (f : Γ(Wν, V'))
              (τ : Γ((Scheme.Modules.pullback ν).obj L, V')),
              w' ∈ V' ∧ w' ∉ Wν.basicOpen f ∧
              ((Scheme.Modules.pullback ν).obj L).presheaf.map
                  (homOfLE (hV'.trans (ν.preimage_mono hVU))).op s -
                ((Scheme.Modules.pullback ν).obj L).presheaf.map (homOfLE hV').op
                  (((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t) =
                f • τ := by
  constructor
  · rintro ⟨t, rfl, -⟩ w hw _
    refine ⟨U, le_rfl, t, hw, fun w' hw' => ⟨ν ⁻¹ᵁ U, le_rfl, 0, 0, ?_, ?_, ?_⟩⟩
    · show ν w' ∈ U
      rwa [hw']
    · simp
    · simp
  · intro h
    refine existsUnique_of_exists_of_unique ?_ fun t₁ t₂ h₁ h₂ =>
      unit_app_injective ν hν L hL U (h₁.trans h₂.symm)
    have : JacobsonSpace (Scheme.IdealSheafData.vanishingIdeal
        ⟨⋃ Z ∈ S, (Z : Set X), S.finite_toSet.isClosed_biUnion fun Z _ => Z.isClosed⟩).subscheme :=
      LocallyOfFiniteType.jacobsonSpace (Scheme.IdealSheafData.subschemeι _ ≫ sX)
    have core : ∀ z ∈ U, IsClosed {z} → ∃ (V : Opens _) (hVU : V ≤ U) (t : Γ(L, V)), z ∈ V ∧
        ((Scheme.Modules.pullbackPushforwardAdjunction ν).unit.app L).app V t =
          ((Scheme.Modules.pullback ν).obj L).presheaf.map
            (homOfLE (ν.preimage_mono hVU)).op s := by
      intro z hzU hz
      exact exists_local_unit_app_eq_of_seminormalAt ν L hL U s z
        (exists_app_eq_of_notMem_basicOpen hproj hB hBeff S hS hSdim ν hν z hz)
        (h z hzU hz)
    refine exists_unit_app_eq_of_locally ν hν L hL U s fun w hw => ?_
    obtain ⟨z, ⟨hzw, hzU⟩, hz⟩ := nonempty_inter_closedPoints (Z := closure {w} ∩ (U : Set _))
      ⟨w, subset_closure rfl, hw⟩ (isClosed_closure.isLocallyClosed.inter U.2.isLocallyClosed)
    obtain ⟨V, hVU, t, hzV, ht⟩ := core z hzU hz
    refine ⟨V, hVU, t, ?_, ht⟩
    by_contra hwV
    exact closure_minimal (Set.singleton_subset_iff.mpr hwV) V.2.isClosed_compl hzw hzV

end MMP.Mori
