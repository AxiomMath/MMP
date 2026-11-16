module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
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
import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesLocallyFree
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Direct images of the two floor sheaves on a log resolution of a dlt pair

Let `(X, B)` be a `ℚ`-factorial dlt pair, with `B` a `ℚ`-divisor, on a normal projective variety
over an algebraically closed field `k` of characteristic zero, and let `T = ⌊B⌋`, a reduced
divisor. Let `p : W ⟶ X` be a projective log resolution of `(X, B)` which is an isomorphism over
the generic point of every stratum of `T`. Write `K_W + Δ_W = p^*(K_X + B)` for the crepant
boundary, `S = p⁻¹_* T` for the strict transform of the floor, `Γ = Δ_W - S` and
`E = -⌊Γ⌋`. Then
`Rp_* 𝒪_W(E) = 𝒪_X` and `Rp_* 𝒪_W(E - S) = 𝓘_T = 𝒪_X(-T)`,
both concentrated in degree zero.

The vanishing is relative Kawamata–Viehweg vanishing for the boundaries `S + {Γ}` and `{Γ}`,
both with gap `-p^*(K_X + B)`, after the standard perturbation by an effective exceptional
divisor whose negative is `p`-ample (it exists because `X` is `ℚ`-factorial) and a small multiple
of `S`. The degree-zero statements are normal Hartogs: every exceptional coefficient of `Δ_W` is
`< 1` because no exceptional divisor of `p` has centre a stratum of `T`, so `E` is effective and
exceptional.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_floor_and_eq_idealSheaf`

## Implementation notes

* The degree-zero identifications are equalities of subsets of the function field
  `K(X) = K(W)`: the sections of `p_* 𝒪_W(G)` over `U` are
  `MMP.Intersection.multiplierIdealSections p G U`. Thus `p_* 𝒪_W(E) = 𝒪_X` says that these are
  exactly the regular functions on `U` (the image of `X.germToFunctionField U`), and
  `p_* 𝒪_W(E - S) = 𝓘_T` that on an affine open `U` they are exactly the images of the sections
  of the vanishing ideal of the reduced subscheme `Supp T`
  (`MMP.Mori.DivisorWithCoeffs.suppIdeal`), and on every open `U` the sections of `𝒪_X(-T)`,
  which are `MMP.Intersection.multiplierIdealSections (𝟙 X) (-T) U`.
* `R^i p_*` is the `i`-th right derived functor of `Scheme.Modules.pushforward p`, and
  `𝒪_W(G)` is `MMP.Mori.Divisor.divisorialSheaf`.
* The strata of `T` are `MMP.Fourfold.IsSNCStratum` of `B.roundDown` (this includes `X` itself);
  "`p` is an isomorphism over the generic point of `Z`" is the existence of an open `U` meeting
  `Z` over which `p` restricts to an isomorphism.
* The crepant boundary `Δ_W` is any `ℚ`-divisor with
  `MMP.Mori.IsCrepantBoundary sX n K B p hW hp Δ_W`, and the strict transform of `T` is
  `MMP.Mori.inverseTransformDivisor p B.roundDown`.
* A prime divisor `P` of `W` either lies over a prime divisor `Q` of `X`, where `p` is an
  isomorphism and the coefficients of `Δ_W`, `S`, `E` along `P` are those of `B`, `⌊B⌋`, `0`
  along `Q`, or `p(η_P)` has codimension at least two. In the second case a coefficient `1` of
  `Δ_W` would be a discrepancy `-1`; its centre meets the snc locus of the dlt pair, where the
  snc discrepancy bound makes it a stratum of `⌊B⌋`, over which `p` is an isomorphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

namespace MMP.Fourfold

/-! ### Serre's theorem for relatively ample Cartier divisors -/

section SerreTwist

open Stacks.Ample Stacks.RelativeVeryAmple MMP.Flips

private theorem exists_affine_nonvanishing_tensor {X : Scheme.{0}} (G P N : X.Modules)
    [IsInvertibleModule X G] [IsInvertibleModule X P] [IsInvertibleModule X N]
    (e : tensorModules X G P ≅ N)
    (t : G.sections) (s : Γ(P, ⊤)) (U : X.Opens)
    (hUs : (U : Set X) = nonvanishingLocus _ s) (hU : IsAffineOpen U) {x : X}
    (hxt : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) _ t)
    (hxU : x ∈ U) :
    ∃ f : Γ(N, ⊤), x ∈ nonvanishingLocus _ f ∧
        IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen X _ f) := by
  set s₀ := Stacks.SheafOfModules.sectionsOfTop _ s
  set v := SheafOfModules.sectionsMap e.hom (tensorSections G _ t s₀)
  have h2 : ∀ z : X, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) G t ↔
      z ∈ Stacks.NonvanishingOpen.nonvanishingOpen X G (t.eval (Opposite.op ⊤)) := fun z =>
    Set.ext_iff.1 (Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X G t) z
  have h1 : ∀ z : X, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) _ s₀ ↔
      z ∈ U := fun z => by
    rw [Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop, ← hUs]
    rfl
  have hmem : ∀ z : X,
      z ∈ nonvanishingLocus N (v.eval (Opposite.op ⊤)) ↔
      z ∈ U ∧ z ∈ Stacks.NonvanishingOpen.nonvanishingOpen X G (t.eval (Opposite.op ⊤)) := by
    intro z
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval]
    exact (nonvanishingLocus_iso e (tensorSections G _ t s₀) z).trans
      ((tensorSections_nonvanishing_iff t s₀ z).trans (and_comm.trans (and_congr (h1 z) (h2 z))))
  refine ⟨v.eval (Opposite.op ⊤), (hmem x).2 ⟨hxU, (h2 x).1 hxt⟩, ?_⟩
  convert Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (M := G) (s := t.eval (Opposite.op ⊤)) hU using 1
  ext z
  exact hmem z

/-- `(M ⊗ L^{⊗ j}) ⊗ L^{⊗ k} ≅ M ⊗ L^{⊗ (j + k)}`. -/
private noncomputable def splitIso {X : Scheme.{0}} (L M : X.Modules) [IsInvertibleModule X L]
    (j k : ℕ) :
    tensorModules X (tensorModules X M (tensorPowModule X L (j : ℤ)))
      (tensorPowModule X L (k : ℤ)) ≅ tensorModules X M (tensorPowModule X L ((j + k : ℕ) : ℤ)) :=
  Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
    tensorModulesMapIso X (Iso.refl _)
      (tensorPowModuleAddIso X _ (j : ℤ) (k : ℤ) ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))

/-- If `L` is ample and `M` is invertible, then `M ⊗ L^{⊗ m}` is ample for `m ≫ 0`. -/
private theorem eventually_isAmple_tensorModules_tensorPowModule {X : Scheme.{0}}
    (L M : X.Modules) [IsInvertibleModule X L] [IsInvertibleModule X M] (hL : IsAmple X L) :
    ∀ᶠ m : ℕ in Filter.atTop, IsAmple X (tensorModules X M (tensorPowModule X L (m : ℤ))) := by
  have : SheafOfModules.IsFiniteType.{0, 0, 0} M :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule M
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hL).2 M inferInstance inferInstance
  have : CompactSpace X := hL.1
  choose k hk s U hUs hxU hUaff using hL.2
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine Filter.eventually_atTop.2 ⟨T.sup k + n₀.toNat, fun m hm => ?_⟩
  refine Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus _ fun x => ?_
  obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  have hsup : k y ≤ T.sup k := Finset.le_sup hyT
  obtain ⟨j, rfl⟩ : ∃ j, m = j + k y := ⟨m - k y, by omega⟩
  obtain ⟨σ, -⟩ := hn₀ j (by omega)
  set G := tensorModules X M (tensorPowModule X L (j : ℤ))
  have : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property G :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _
  let _ := Stacks.SheafInternalHom.schemeMonoidalCategory X
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso X M
    (tensorPowModule X L (j : ℤ))
  have : @Epi (SheafOfModules.{0} X.ringCatSheaf) _ _ _ i.hom :=
    @IsIso.epi_of_iso _ _ _ _ i.hom i.isIso_hom
  obtain ⟨a, ha⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing G (σ.ofEpi i.hom) x
  exact exists_affine_nonvanishing_tensor G _ _ (splitIso L M j (k y)) _ (s y) (U y) (hUs y)
    (hUaff y) ha hxy

/-- The pull-back of `𝒪_Y(nH + F)` along `f : X ⟶ Y` is `f^*𝒪_Y(F) ⊗ (f^*𝒪_Y(H))^{⊗ n}`, for
Cartier divisors `H` and `F`. -/
private theorem nonempty_modulePullback_divisorialSheaf_nsmul_add_iso {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : X ⟶ Y) {H F : Divisor Y}
    (hH : H.IsCartier) (hF : F.IsCartier) (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
        (n • H + F).divisorialSheaf ≅
      tensorModules X ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
          F.divisorialSheaf)
        (tensorPowModule X ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj
          H.divisorialSheaf) (n : ℤ))) := by
  have := hH.isInvertibleModule_divisorialSheaf
  set P := RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      P.mapIso (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      pullbackTensorModulesIso f _ _ ≪≫
      tensorModulesMapIso X e (tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫ tensorPowModuleCongr X _ (by push_cast; ring))⟩

/-- If `H` is an `g`-ample Cartier divisor and `F` is any Cartier divisor, then `mH + F` is
`g`-ample for `m ≫ 0`, provided the base is quasi-compact. -/
private theorem eventually_isRelativelyAmpleCartier_nsmul_add {Y Z : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [CompactSpace Z] (g : Y ⟶ Z)
    [QuasiCompact g] {H F : Divisor Y} (hH : IsRelativelyAmpleCartier g H) (hF : F.IsCartier) :
    ∀ᶠ m : ℕ in Filter.atTop, IsRelativelyAmpleCartier g (m • H + F) := by
  obtain ⟨hHc, hHa⟩ := hH
  have := hHc.isInvertibleModule_divisorialSheaf
  have := hF.isInvertibleModule_divisorialSheaf
  choose V' hVa hzV _ using fun z : Z =>
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z : Z ↦ ((V' z : Z.Opens) : Set Z))
    (fun z ↦ (V' z).isOpen) (fun z _ ↦ Set.mem_iUnion.2 ⟨z, hzV z⟩)
  have hev : ∀ v ∈ T, ∀ᶠ m : ℕ in Filter.atTop,
      haveI := ((hHc.nsmul m).add hF).isInvertibleModule_divisorialSheaf
      IsAmple (g ⁻¹ᵁ V' v).toScheme
        ((RingedSpaceModuleAdjunction.modulePullback
          (g ⁻¹ᵁ V' v).ι.toLRSHom.toShHom).obj (m • H + F).divisorialSheaf) := by
    intro v _
    let W := (g ⁻¹ᵁ V' v).toScheme
    let P := RingedSpaceModuleAdjunction.modulePullback (g ⁻¹ᵁ V' v).ι.toLRSHom.toShHom
    have hPF : IsInvertibleModule W (P.obj F.divisorialSheaf) := inferInstance
    have hPH : IsInvertibleModule W (P.obj H.divisorialSheaf) := inferInstance
    filter_upwards [eventually_isAmple_tensorModules_tensorPowModule (P.obj H.divisorialSheaf)
      (P.obj F.divisorialSheaf) (hHa _ (hVa v))]
      with m hm
    have := ((hHc.nsmul m).add hF).isInvertibleModule_divisorialSheaf
    obtain ⟨e⟩ := nonempty_modulePullback_divisorialSheaf_nsmul_add_iso (g ⁻¹ᵁ V' v).ι hHc hF m
    exact (@isAmple_congr _ _ _ inferInstance
      (@Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules _ _ _ inferInstance
        (isInvertibleModule_tensorPowModule _ _ _)) e).2 hm
  filter_upwards [(Filter.eventually_all_finset T).2 hev] with m hm
  have hc := (hHc.nsmul m).add hF
  have := hc.isInvertibleModule_divisorialSheaf
  refine ⟨hc, ((Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover
    g _ inferInstance).2 fun z => ?_).2⟩
  obtain ⟨v, hvT, hzv⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
  exact ⟨V' v, hVa v, hzv, hm v hvT⟩

end SerreTwist

/-! ### Bridges between the notions of relative ampleness -/

section AmpleBridges

open Stacks.Ample

/-- `f`-ampleness of a Cartier divisor gives ampleness over every affine open of the base. -/
private theorem isRelativelyAmpleCartier_of_isRelativelyAmple {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ S) [QuasiCompact f]
    {L : Divisor X} (hL : L.IsCartier) (h : L.IsRelativelyAmple f hL) :
    MMP.Flips.IsRelativelyAmpleCartier f L := by
  have := hL.isInvertibleModule_divisorialSheaf
  exact ⟨hL, (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
    inferInstance h).2⟩

/-- Ampleness over every affine open of the base gives `f`-ampleness. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ S) {L : Divisor X}
    (h : MMP.Flips.IsRelativelyAmpleCartier f L) : L.IsRelativelyAmple f h.choose := by
  obtain ⟨hL, hamp⟩ := h
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  exact ⟨V, hV, hyV, hamp V hV⟩

end AmpleBridges

/-! ### Kawamata–Viehweg vanishing for a boundary with a reduced part -/

section Vanishing

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- **Relative vanishing for a boundary `S' + Θ₀` with `S'` reduced.** Let `p : W ⟶ X` be a
projective birational morphism from a smooth variety onto a `ℚ`-factorial normal variety, `K_W` a
canonical divisor, `S'` a reduced divisor without `p`-exceptional components and `Θ₀` a
`ℚ`-divisor with coefficients in `[0, 1)` and no component in common with `S'`, such that every
`ℚ`-divisor supported on `S' + Θ₀ + Ex(p)` is snc. If `M - (K_W + S' + Θ₀)` is the pull-back of a
`ℚ`-Cartier divisor `C/m` of `X`, then `R^i p_* 𝒪_W(M) = 0` for `i > 0`. -/
private theorem isZero_rightDerived_of_reducedBoundary (hQ : IsQFactorial sX)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) [IsDominant p] (hW : IsNormalVariety k (p ≫ sX))
    (hsm : IsSmoothScheme (p ≫ sX)) (hproj : IsProjectiveMorphism p)
    (hb : IsBirationalMorphism p) {n : ℕ} {KW : Divisor W}
    (hKW : KW.IsCanonicalDivisor (p ≫ sX) n) (M S' : Divisor W) (Θ₀ : QDivisor W)
    (hS'01 : ∀ P, S'.coeff P = 0 ∨ S'.coeff P = 1)
    (hS'ex : ∀ P, S'.coeff P ≠ 0 → ¬ RationalMap.IsExceptional (X := W) p.toRationalMap P)
    (hΘ0 : ∀ P, 0 ≤ Θ₀.coeff P) (hΘ1 : ∀ P, Θ₀.coeff P < 1)
    (hS'Θ : ∀ P, S'.coeff P ≠ 0 → Θ₀.coeff P = 0)
    (hsnc : ∀ G : QDivisor W, (∀ P, G.coeff P ≠ 0 → S'.coeff P ≠ 0 ∨ Θ₀.coeff P ≠ 0 ∨
      RationalMap.IsExceptional (X := W) p.toRationalMap P) →
        DivisorWithCoeffs.IsSNC (p ≫ sX) G)
    (m : ℕ) (hm : 0 < m) (C : Divisor X) (hC : C.IsCartier)
    (hCs : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ C.supp)
    (Cμ : Divisor W) (hCμ : C.IsPullback p hCs Cμ)
    (hCeq : Divisor.toQDivisor Cμ = (m : ℤ) • (Divisor.toQDivisor M -
      (Divisor.toQDivisor KW + Divisor.toQDivisor S' + Θ₀)))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj M.divisorialSheaf) := by
  classical
  have : MMP.Mori.IsVariety k sX := hQ.1.1
  have : MMP.Mori.IsVariety k (p ≫ sX) := hW.1
  have hp : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : UniversallyClosed p := hp.toUniversallyClosed
  have : QuasiCompact p := AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _
  have hcart : ∀ G : Divisor W, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨Fexc, e, he, hFexc0, hFexcEx, Dexc, hDexc, hDexceq, hDexcamp⟩ :=
    MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional sX (p ≫ sX) hQ hW p rfl hproj hb
  obtain ⟨r, hr, hr0⟩ := ((eventually_isRelativelyAmpleCartier_nsmul_add p
    (isRelativelyAmpleCartier_of_isRelativelyAmple p hDexc.neg hDexcamp) (hcart S')).and
      (Filter.eventually_gt_atTop 0)).exists
  have hAc : (r • (-Dexc) + S').IsCartier := hr.choose
  have hAamp : (r • (-Dexc) + S').IsRelativelyAmple p hAc :=
    isRelativelyAmple_of_isRelativelyAmpleCartier p hr
  -- the numbers
  set t : ℚ := ∑ P ∈ Fexc.support, Fexc.coeff P / (1 - Θ₀.coeff P)
  have ht0 : ∀ P ∈ Fexc.support, Fexc.coeff P / (1 - Θ₀.coeff P) ≤ t := fun P hP =>
    Finset.single_le_sum (f := fun P => Fexc.coeff P / (1 - Θ₀.coeff P))
      (fun Q _ => div_nonneg (hFexc0 Q) (by linarith [hΘ1 Q])) hP
  set N : ℕ := ⌈(r * e : ℚ) * t⌉₊ + 1 with hN
  set c : ℕ := m * N with hc
  have hc0 : 0 < c := Nat.mul_pos hm (by omega)
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc0
  have hct : (r * e : ℚ) * t < c := by
    have h1 := Nat.le_ceil ((r * e : ℚ) * t)
    have h2 : (N : ℚ) ≤ c := by
      rw [hc]; push_cast
      have : (1 : ℚ) ≤ m := by exact_mod_cast hm
      nlinarith [Nat.cast_nonneg (α := ℚ) N]
    have h3 : ((⌈(r * e : ℚ) * t⌉₊ : ℕ) : ℚ) + 1 = N := by rw [hN]; push_cast; ring
    linarith
  set ε : ℚ := 1 / c with hε
  set δ : ℚ := (r * e : ℚ) / c with hδ
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hcq]
    exact_mod_cast hc0
  have hδ0 : 0 ≤ δ := by positivity
  set Θ : QDivisor W := Θ₀ + (1 - ε) • Divisor.toQDivisor S' + δ • Fexc with hΘdef
  have hΘc : ∀ P, Θ.coeff P = Θ₀.coeff P + (1 - ε) * S'.coeff P + δ * Fexc.coeff P :=
    fun P => by simp [hΘdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
  have hFS : ∀ P, S'.coeff P ≠ 0 → Fexc.coeff P = 0 :=
    fun P hP => not_not.1 fun h => hS'ex P hP (hFexcEx P h)
  -- the boundary
  have hB0 : Θ.IsEffective := fun P => by
    rw [hΘc]
    have h1 : (0 : ℚ) ≤ (1 - ε) * S'.coeff P := by
      rcases hS'01 P with h | h <;> rw [h] <;> push_cast <;> nlinarith
    have h3 : 0 ≤ δ * Fexc.coeff P := mul_nonneg hδ0 (hFexc0 P)
    linarith [hΘ0 P]
  have hB1 : ∀ P, Θ.coeff P < 1 := fun P => by
    rw [hΘc]
    rcases hS'01 P with hP | hP
    · rw [hP]
      by_cases hF : Fexc.coeff P = 0
      · simpa [hF] using hΘ1 P
      · have hmem : P ∈ Fexc.support := Finsupp.mem_support_iff.2 hF
        have h1 := ht0 P hmem
        have hpos : 0 < 1 - Θ₀.coeff P := by linarith [hΘ1 P]
        have h2 : Fexc.coeff P ≤ t * (1 - Θ₀.coeff P) := by rwa [div_le_iff₀ hpos] at h1
        have h3 : δ * Fexc.coeff P ≤ δ * t * (1 - Θ₀.coeff P) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hδ0
        have h4 : δ * t < 1 := by
          rwa [hδ, div_mul_eq_mul_div, div_lt_one hcq]
        have h5 : δ * t * (1 - Θ₀.coeff P) < 1 - Θ₀.coeff P := by nlinarith
        simp only [Int.cast_zero, mul_zero, add_zero]
        linarith
    · have hne : S'.coeff P ≠ 0 := by simp [hP]
      rw [hP, hS'Θ P hne, hFS P hne]
      simp only [Int.cast_one, mul_one, mul_zero, add_zero, zero_add]
      linarith
  have hBsnc : DivisorWithCoeffs.IsSNC (p ≫ sX) Θ := hsnc Θ fun P hP => by
    by_contra hcon
    push Not at hcon
    obtain ⟨hS, hΘ, hEx⟩ := hcon
    apply hP
    have : Fexc.coeff P = 0 := not_not.1 fun h => hEx (hFexcEx P h)
    rw [hΘc, hS, hΘ, this]
    simp
  -- the gap
  have hCn := hCμ.zsmul hC (N : ℤ)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p _)
  have hLc : (r • (-Dexc) + S' + (N : ℤ) • Cμ).IsCartier := hcart _
  have hLamp : (r • (-Dexc) + S' + (N : ℤ) • Cμ).IsRelativelyAmple p hLc :=
    MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback p hAc hAamp (hC.zsmul _) hCn
      (hcart _)
  have heq : Divisor.toQDivisor (r • (-Dexc) + S' + (N : ℤ) • Cμ) =
      ((c : ℕ) : ℤ) • (Divisor.toQDivisor M - (Divisor.toQDivisor KW + Θ)) := by
    ext P
    have hC' : (Cμ.coeff P : ℚ) = m * (M.coeff P - (KW.coeff P + S'.coeff P + Θ₀.coeff P)) := by
      have := congrArg (fun G : QDivisor W => G.coeff P) hCeq
      simpa [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_add] using this
    have hD' : (Dexc.coeff P : ℚ) = e * Fexc.coeff P := by
      have := congrArg (fun G : QDivisor W => G.coeff P) hDexceq
      simpa [DivisorWithCoeffs.coeff_smul] using this
    have hΘP := hΘc P
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_neg, nsmul_eq_mul, zsmul_eq_mul,
      Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast, smul_eq_mul]
      at hC' hD' hΘP ⊢
    have hNq : (N : ℚ) ≠ 0 := by positivity
    have hmq : (m : ℚ) ≠ 0 := by positivity
    rw [hΘP, hC', hD', hε, hδ, hc]
    push_cast
    field_simp
    ring
  exact MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
    (p ≫ sX) sX hsm p rfl hproj hKW hB0 hBsnc hB1 (hcart M) ⟨c, hc0, _, hLc, heq, hLamp⟩ i hi

omit [IsAlgClosed k] in
/-- **A compatible canonical divisor on a smooth model.** For a birational morphism `p : W ⟶ X`
from a smooth variety and a canonical divisor `K = div(ω)` of `X`, `div(p^*ω)` is a canonical
divisor of `W`. -/
private theorem exists_divisorOfForm_pullback_isCanonicalDivisor {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (hX : IsNormalVariety k sX)
    {p : W ⟶ X} [IsDominant p] (hW : IsNormalVariety k (p ≫ sX)) (hsm : IsSmoothScheme (p ≫ sX))
    (hb : IsBirationalMorphism p) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K ∧
      (divisorOfForm (pullbackRationalPluriForms sX p ω)).IsCanonicalDivisor (p ≫ sX) n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (p ≫ sX) := hW.1
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  have hτ0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hb.functionFieldMap_bijective hd hω0
  have hdim : topologicalKrullDim W = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hb).symm
  obtain ⟨K₀, hK₀⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme _ _ _ _ _ k _ _ hW.1 hsm n hdim
  refine ⟨ω, hω0, Finsupp.ext hω, hK₀.of_linearlyEquivalent ?_⟩
  simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hK₀ hτ0

end Vanishing

/-! ### The floor sheaves -/

section Floor

open MMP.Intersection

section Geometry

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The generic point of a prime divisor has codimension one, so not at least two. -/
private theorem not_two_le_coheight_genericPoint (Q : MMP.Mori.PrimeDivisor X) :
    ¬ 2 ≤ Order.coheight Q.genericPoint := by
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  decide

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A valuation of `K(X)` with no pole on the stalk at the generic point is trivial, so it takes
no value `< 1`. -/
private theorem false_of_forall_valuation_le_one (x : X) (hx : x = genericPoint X)
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ)))
    (h1 : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    {g : X.functionField} (hg : v g = WithZero.exp (-1)) : False := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) g⁻¹
  have hu : IsUnit b := by
    subst hx
    exact isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, rfl⟩ := hu
  have hb1 : v (algebraMap _ X.functionField (c : X.presheaf.stalk x)) = 1 := by
    refine le_antisymm (h1 _) ?_
    by_contra hlt
    push Not at hlt
    have hm : v (algebraMap _ X.functionField (c : X.presheaf.stalk x)) *
        v (algebraMap _ X.functionField (↑c⁻¹ : X.presheaf.stalk x)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := mul_le_of_le_one_right' (a := v (algebraMap _ X.functionField
      (c : X.presheaf.stalk x))) (h1 (↑c⁻¹ : X.presheaf.stalk x))
    rw [hm] at h2
    exact lt_irrefl _ (h2.trans_lt hlt)
  have hle : v g⁻¹ ≤ 1 := by
    rw [← hab, map_div₀, hb1, div_one]
    exact h1 a
  rw [map_inv₀, hg] at hle
  exact absurd hle (by decide)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A dominant morphism of integral schemes inducing a surjection of function fields does not map
the generic point of a prime divisor to the generic point. -/
private theorem map_genericPoint_ne_genericPoint (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) (E : MMP.Mori.PrimeDivisor Y) :
    f E.genericPoint ≠ genericPoint X := by
  intro h
  have h1 : ∀ a : X.presheaf.stalk (f E.genericPoint),
      E.valuationOver f (algebraMap _ X.functionField a) ≤ 1 := by
    intro a
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, functionFieldMap_algebraMap_stalk,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨g, hg⟩ := hf (algebraMap E.localRing Y.functionField ϖ)
  have hgv : E.valuationOver f g = WithZero.exp (-1) := by
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, hg,
      MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_of_irreducible _ hϖ]
  exact false_of_forall_valuation_le_one _ h _ h1 hgv

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Under a dominant morphism inducing a surjection of function fields, the generic point of a
prime divisor maps either to the generic point of a prime divisor or to a point of codimension
at least two. -/
private theorem exists_map_genericPoint_eq_or_two_le_coheight (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) (E : MMP.Mori.PrimeDivisor Y) :
    (∃ Q : MMP.Mori.PrimeDivisor X, f E.genericPoint = Q.genericPoint) ∨
      2 ≤ Order.coheight (f E.genericPoint) := by
  by_cases h2 : 2 ≤ Order.coheight (f E.genericPoint)
  · exact Or.inr h2
  left
  have hne := map_genericPoint_ne_genericPoint f hf E
  have h0 : Order.coheight (f E.genericPoint) ≠ 0 := by
    intro h0
    have hmax : IsMax (f E.genericPoint) := Order.coheight_eq_zero.mp h0
    exact hne (Specializes.antisymm (hmax (genericPoint_specializes _))
      (genericPoint_specializes _)).eq
  have h1 : Order.coheight (f E.genericPoint) = 1 := by
    rw [not_le] at h2
    generalize Order.coheight (f E.genericPoint) = c at h0 h2 ⊢
    induction c using ENat.recTopCoe with
    | top => exact absurd h2 (by simp)
    | coe c =>
      norm_cast at h0 h2 ⊢
      omega
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm⟩

omit [IsLocallyNoetherian Y] in
/-- The coefficient of the strict transform `p⁻¹_* D` along a prime divisor `P` of `W` lying over
the prime divisor `Q` of `X` is the coefficient of `D` along `Q`. -/
private theorem coeff_inverseTransformDivisor_of_map_genericPoint {R : Type*} [AddCommMonoid R]
    (p : Y ⟶ X) [IsProper p] (hb : IsBirationalMorphism p) (D : DivisorWithCoeffs R X)
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor X}
    (h : p P.genericPoint = Q.genericPoint) :
    (inverseTransformDivisor p D).coeff P = D.coeff Q := by
  have hQ : inverseTransformPrimeDivisor p Q = some P :=
    (MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' p Q P).2
      ⟨MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb Q, h⟩
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' p Q' P).1 hQ').2.symm.trans
        h)) D

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- The strict transform `p⁻¹_* D` has no component over a point of codimension at least two. -/
private theorem coeff_inverseTransformDivisor_of_two_le_coheight {R : Type*} [AddCommMonoid R]
    (p : Y ⟶ X) (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor Y}
    (h : 2 ≤ Order.coheight (p P.genericPoint)) :
    (inverseTransformDivisor p D).coeff P = 0 :=
  MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun Q hQ => by
    rw [((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' p Q P).1 hQ).2] at h
    exact not_two_le_coheight_genericPoint Q h) D

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] in
/-- Over an open `V` above which `p` is an isomorphism, `p` preserves codimensions of points. -/
private theorem coheight_map_eq_of_isIso_restrict (p : Y ⟶ X) (V : X.Opens) [IsIso (p ∣_ V)]
    (y : Y) (hy : p y ∈ V) : Order.coheight (p y) = Order.coheight y := by
  have hst : IsIso (p.stalkMap y) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap p V ⟨y, hy⟩)).mp
      (((isIso_iff_isIso_stalkMap (p ∣_ V)).mp inferInstance).2 ⟨y, hy⟩)
  have h1 : ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (X.presheaf.stalk (p y)) :=
    (ringKrullDim_eq_of_ringEquiv (asIso (p.stalkMap y)).commRingCatIsoToRingEquiv).symm
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1.symm

end Geometry

section Model

variable {k : Type} [Field k] {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- A prime divisor `P` of a model `p : W ⟶ X` is `p`-exceptional exactly when its image
`p(η_P)` has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX) {p : W ⟶ X}
    (hW : IsNormalVariety k (p ≫ sX)) (hb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) p.toRationalMap P ↔
      2 ≤ Order.coheight (p P.genericPoint) :=
  MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX ⟨W, p, hW, hb, P⟩

omit [IsLocallyNoetherian W] in
/-- The crepant boundary along a prime divisor `P` of `W` lying over a prime divisor `Q` of `X` has
the coefficient of the boundary along `Q`. -/
private theorem coeff_crepantBoundary_of_map_genericPoint {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) {p : W ⟶ X} [IsProper p]
    {hW : IsNormalVariety k (p ≫ sX)} {hb : IsBirationalMorphism p} {ΔW : QDivisor W}
    (hΔ : IsCrepantBoundary sX n K B p hW hb ΔW) {P : MMP.Mori.PrimeDivisor W}
    {Q : MMP.Mori.PrimeDivisor X} (h : p P.genericPoint = Q.genericPoint) :
    ΔW.coeff P = B.coeff Q := by
  classical
  have hnex : ¬ RationalMap.IsExceptional (X := W) p.toRationalMap P := by
    rw [isExceptional_iff_two_le_coheight hP.1 hW hb, h,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    decide
  have heq := (hΔ.eq_inverseTransformDivisor_add_exceptional hP).1
  have h1 := congrArg (fun G : QDivisor W => G P) heq
  simp only [Finsupp.add_apply, Finsupp.filter_apply, if_neg hnex, add_zero] at h1
  rw [DivisorWithCoeffs.coeff_apply, h1, ← DivisorWithCoeffs.coeff_apply,
    coeff_inverseTransformDivisor_of_map_genericPoint p hb B h]

omit [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] in
/-- **No exceptional divisor of a stratum-preserving resolution of a dlt pair is an lc place.**
Let `(X, B)` be dlt and `p : W ⟶ X` a proper birational model which is an isomorphism over the
generic point of every stratum of `⌊B⌋`. Then every `p`-exceptional coefficient of the crepant
boundary `Δ_W` is `< 1`: a coefficient `1` is a discrepancy `-1`, whose centre meets the snc locus
of the dlt pair, where the snc discrepancy bound forces it to be a stratum of `⌊B⌋`. -/
private theorem coeff_crepantBoundary_lt_one [CharZero k] {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hdlt : IsDltPair sX n K B) {p : W ⟶ X}
    {hW : IsNormalVariety k (p ≫ sX)} {hb : IsBirationalMorphism p} {ΔW : QDivisor W}
    (hΔ : IsCrepantBoundary sX n K B p hW hb ΔW)
    (hstrata : ∀ Z : Set X, IsSNCStratum B.roundDown Z →
      ∃ U : X.Opens, (Z ∩ U).Nonempty ∧ IsIso (p ∣_ U))
    (P : MMP.Mori.PrimeDivisor W) (h2 : 2 ≤ Order.coheight (p P.genericPoint)) :
    ΔW.coeff P < 1 := by
  classical
  have hPW := hdlt.isPairWith
  have hX := hPW.1
  let D : DivisorOver k sX := ⟨W, p, hW, hb, P⟩
  have ha : IsDiscrepancy sX n K B D (-ΔW.coeff P) := hΔ P
  have hDex : D.IsExceptional := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).2 h2
  have hle : -1 ≤ -ΔW.coeff P := by
    have := hdlt.isLcPair.2.trans (discrep_le hDex ha)
    have h' : ((-1 : ℝ) : EReal) ≤ (((-ΔW.coeff P : ℚ) : ℝ) : EReal) := by simpa using this
    exact_mod_cast EReal.coe_le_coe_iff.mp h'
  by_contra hge
  push Not at hge
  have ha1 : -ΔW.coeff P = -1 := by linarith
  obtain ⟨-, hcoeff, U, hUsm, hUsnc, hUd⟩ := hdlt
  set x := p P.genericPoint with hxdef
  have hxc : (D.center : Set X) = closure {x} := D.center_eq_closure_genericPoint
  have hxU : x ∈ U := by
    by_contra hxU
    have hsub : (D.center : Set X) ⊆ (U : Set X)ᶜ := by
      rw [hxc]
      exact closure_minimal (Set.singleton_subset_iff.2 hxU) U.isOpen.isClosed_compl
    have := hUd D _ hsub ha
    linarith
  have hU : ((D.center : Set X) ∩ U).Nonempty := ⟨x, by rw [hxc]; exact subset_closure rfl, hxU⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW D U hU
  let D' : DivisorOver k (U.ι ≫ sX) := ⟨_, p ∣_ U, hY, hf, E'⟩
  have haU := (hiff _).1 ha
  set x' := (p ∣_ U) E'.genericPoint with hx'def
  have hx' : U.ι x' = x := by
    rw [hx'def, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hxdef]
    exact congrArg p ((OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm.trans
      (congrArg (fun Q => Q.genericPoint) hE'))
  have hXU := hX.restrictOpen U
  have hD'ex : D'.IsExceptional := by
    rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hXU]
    change 2 ≤ Order.coheight x'
    rw [← coheight_eq_of_isOpenImmersion U.ι, hx']
    exact h2
  set S := (B.restrictOpen U).support with hSdef
  have hsncS : DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (∑ E ∈ S, Finsupp.single E (1 : ℤ)) :=
    hUsnc.of_support_subset fun E hE => by
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hE
      by_contra hES
      exact hE <| Finset.sum_eq_zero fun E' hE' => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hES hE'
  obtain ⟨c, T', hc, hT', -, hcard, hT'S, hT'mem, hbound⟩ := le_isDiscrepancy_of_isSNC hXU
    (isSmoothScheme_ι_of_le_smoothLocus hUsm) (hPW.restrictOpen U).2.1 subset_rfl hsncS
    (fun E _ => (hcoeff _).2) D' hD'ex haU
  rw [ha1] at hbound
  have hnn : ∀ G ∈ T', 0 ≤ 1 - (B.restrictOpen U).coeff G := fun G _ => by
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    linarith [(hcoeff (OpenWeilRestriction.primeDivisorMap U.ι G)).2]
  have hsum := Finset.sum_nonneg hnn
  have hcq : (T'.card : ℚ) ≤ c := by exact_mod_cast hcard
  have hsum0 : ∑ G ∈ T', (1 - (B.restrictOpen U).coeff G) = 0 := by linarith
  have hcT : T'.card = c := by
    have : (c : ℚ) = T'.card := by linarith
    exact_mod_cast this.symm
  have hB1 : ∀ G ∈ T', B.coeff (OpenWeilRestriction.primeDivisorMap U.ι G) = 1 := fun G hG => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 G hG
    rw [DivisorWithCoeffs.coeff_restrictOpen] at this
    linarith
  -- the centre is a stratum of `⌊B⌋`
  have hsuppC : ∀ E : MMP.Mori.PrimeDivisor X, IsClosed (E.support : Set X) := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  let J : Finset (MMP.Mori.PrimeDivisor X) := T'.image (OpenWeilRestriction.primeDivisorMap U.ι)
  have hxJ : ∀ G ∈ T', x ∈ (OpenWeilRestriction.primeDivisorMap U.ι G).support := by
    intro G hG
    have hxG := hT'mem G hG
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxG ⊢
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap, ← hx']
    exact map_mem_closure U.ι.continuous hxG fun y hy => by rw [Set.mem_singleton_iff.mp hy]; rfl
  have hstr : IsSNCStratum B.roundDown (closure {x}) := by
    refine ⟨J, fun G' hG' => ?_, ⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hG'
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_roundDown, hB1 G hG]
      simp
    · refine closure_minimal (Set.singleton_subset_iff.2 ?_)
        (isClosed_biInter fun E _ => hsuppC E)
      simp only [Set.mem_iInter]
      intro G' hG'
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hG'
      exact hxJ G hG
    · rintro T'' ⟨hirr, hsub⟩ hZT''
      obtain ⟨w, hw⟩ := QuasiSober.sober hirr.closure isClosed_closure
      have hxT : x ∈ closure T'' := subset_closure (hZT'' (subset_closure rfl))
      have hwx : w ⤳ x := hw.specializes hxT
      have hwU : w ∈ U := hwx.mem_open U.isOpen hxU
      have hwsub : closure T'' ⊆ ⋂ E ∈ J, (E.support : Set X) :=
        closure_minimal hsub (isClosed_biInter fun E _ => hsuppC E)
      let w' : (U : X.Opens).toScheme := ⟨w, hwU⟩
      have hw' : U.ι w' = w := rfl
      have hw'x' : w' ⤳ x' := by
        rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hw', hx']
        exact hwx
      have hmemw : ∀ G ∈ T', w' ∈ G.support := by
        intro G hG
        have hwG : w ∈ (OpenWeilRestriction.primeDivisorMap U.ι G).support := by
          have := hwsub hw.mem
          simp only [Set.mem_iInter] at this
          exact this _ (Finset.mem_image_of_mem _ hG)
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          OpenWeilRestriction.genericPoint_primeDivisorMap, ← hw'] at hwG
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp
          (U.ι.isOpenEmbedding.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hwG))
      obtain ⟨N, z, j, hz, hj, -⟩ := exists_at_of_isSNC hsncS w'
      have hTN : T'.card ≤ N := by
        let ι' : T' → Fin N := fun G => j ⟨G.1, hT'S G.2, hmemw G.1 G.2⟩
        have hι' : Function.Injective ι' := by
          intro G₁ G₂ h
          have h' := congrArg Subtype.val (hj h)
          exact Subtype.ext h'
        simpa using Fintype.card_le_of_injective ι' hι'
      have hcw : Order.coheight w' = N := by
        have h := hz.2
        rw [ringKrullDim_stalk_eq_coheight] at h
        exact_mod_cast h
      have hww : w' = x' := by
        by_contra hne
        have hle' : x' ≤ w' := hw'x'
        have hlt : x' < w' := lt_of_le_not_ge hle' fun h => hne (Specializes.antisymm hw'x' h).eq
        have h1 := Order.coheight_add_one_le hlt
        rw [hcw, ← hc] at h1
        have h3 : N + 1 ≤ c := by exact_mod_cast h1
        omega
      have hwxe : w = x := by rw [← hw', hww, hx']
      rw [← hwxe, hw.def]
      exact subset_closure
  obtain ⟨V, hZV, hV⟩ := hstrata _ hstr
  have hxV : x ∈ V := by
    obtain ⟨y, hyZ, hyV⟩ := hZV
    exact (specializes_iff_mem_closure.mpr hyZ).mem_open V.isOpen hyV
  rw [hxdef, coheight_map_eq_of_isIso_restrict p V P.genericPoint hxV] at h2
  exact not_two_le_coheight_genericPoint P h2

/-- **Divisors on a log resolution are snc.** On a log resolution `p : W ⟶ X` of `(X, B)`, a
`ℚ`-divisor each of whose components lies over a point of codimension at least two or over a
component of `B` is snc: its support lies in the snc divisor `Ex(p) ∪ p⁻¹(Supp B)`. -/
private theorem isSNC_of_forall_two_le_coheight_or_coeff_ne_zero {B : QDivisor X} {p : W ⟶ X}
    [LocallyOfFiniteType (p ≫ sX)]
    (hres : MMP.Mori.IsLogResolution sX (QDivisor.toRDivisor B) p) (G : QDivisor W)
    (hG : ∀ P, G.coeff P ≠ 0 → 2 ≤ Order.coheight (p P.genericPoint) ∨
      ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint ∧ B.coeff Q ≠ 0) :
    DivisorWithCoeffs.IsSNC (p ≫ sX) G := by
  classical
  have hmem : ∀ P, G.coeff P ≠ 0 → P.genericPoint ∈
      ((exceptionalSet p ⊔ (QDivisor.toRDivisor B).supp.preimage p.continuous :
        TopologicalSpace.Closeds W) : Set W) := by
    intro P hGP
    rw [TopologicalSpace.Closeds.coe_sup]
    rcases hG P hGP with h2 | ⟨Q, h, hBQ⟩
    · left
      intro hP
      have : IsIso (p ∣_ biregularLocus p) := isBiregular_biregularLocus p
      rw [coheight_map_eq_of_isIso_restrict p (biregularLocus p) _
        (show p P.genericPoint ∈ _ from hP)] at h2
      exact not_two_le_coheight_genericPoint P h2
    · right
      change p P.genericPoint ∈ (QDivisor.toRDivisor B).supp
      rw [h]
      refine DivisorWithCoeffs.mem_supp_iff.2 ⟨Q, by simpa using hBQ, ?_⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rcases hres.isSNCSubset with hbot | ⟨s, hs, hsncs⟩
  · have hG0 : G = 0 := by
      ext P
      by_contra hP
      have := hmem P hP
      rw [hbot] at this
      exact this
    rw [hG0]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hres.isSmoothScheme
  · refine hsncs.of_support_subset fun P hP => ?_
    have hP' := hmem P (Finsupp.mem_support_iff.1 hP)
    rw [← hs] at hP'
    obtain ⟨F, hFs, hF⟩ := Set.mem_iUnion₂.1 hP'
    rw [(MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hF).symm, Finsupp.mem_support_iff,
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, hFs]

end Model

section Hartogs

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A function regular on `U` has no pole along a prime divisor of `W` whose generic point maps
into `U`. -/
private theorem valuationOver_germ_le_one (p : W ⟶ X) [IsDominant p] {U : X.Opens} [Nonempty U]
    (r : Γ(X, U)) (P : MMP.Mori.PrimeDivisor W) (hP : p P.genericPoint ∈ U) :
    P.valuationOver p (X.germToFunctionField U r) ≤ 1 := by
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hP,
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ⟨_, rfl⟩

/-- **Normal Hartogs.** A rational function without pole along the prime divisors meeting a
non-empty open `U` of a normal scheme is regular on `U`. -/
private theorem mem_range_germToFunctionField_of_forall (U : X.Opens) [Nonempty U]
    {g : X.functionField}
    (h : ∀ Q : MMP.Mori.PrimeDivisor X, (Q.support ∩ U).Nonempty → Q.divisorialValuation g ≤ 1) :
    g ∈ Set.range (X.germToFunctionField U) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, map_zero _⟩
  refine (exists_germToFunctionField_eq_iff_forall_zero_le_ord U hg0).mpr fun Q hQ => ?_
  rw [← Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) hg0]
  exact (Q.divisorialValuation_le_one_iff g).1 (h Q hQ)

/-- The sections of `𝒪_X(D)` over `U`, by orders along the prime divisors meeting `U`. -/
private theorem mem_multiplierIdealSections_id_iff (D : Divisor X) (U : X.Opens)
    (g : X.functionField) :
    g ∈ multiplierIdealSections (𝟙 X) D U ↔ (U = ⊥ → g = 0) ∧
      ∀ Q : MMP.Mori.PrimeDivisor X, (Q.support ∩ U).Nonempty →
        Q.divisorialValuation g ≤ WithZero.exp (D.coeff Q) := by
  simp only [multiplierIdealSections, Set.mem_ofPred_eq, Scheme.Hom.id_preimage,
    MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] in
/-- A morphism with dense image has empty preimage of `U` only for `U` empty. -/
private theorem preimage_eq_bot_iff (p : W ⟶ X) [IsDominant p] (U : X.Opens) :
    p ⁻¹ᵁ U = ⊥ ↔ U = ⊥ := by
  refine ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
  by_contra hU
  obtain ⟨u, hu⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).1 hU
  obtain ⟨_, hx', ⟨x', rfl⟩⟩ := p.denseRange.inter_open_nonempty U U.isOpen ⟨u, hu⟩
  have hmem : x' ∈ p ⁻¹ᵁ U := hx'
  rw [h] at hmem
  exact hmem

/-- **The push-forward of `𝒪_W(G)` by orders.** Let `p : W ⟶ X` be a proper birational morphism
of normal integral schemes, `D ≤ 0` a divisor on `X`, and `G` a divisor on `W` which agrees with
`D` along every prime divisor of `W` lying over a prime divisor of `X` and is effective along all
the others. Then `p_* 𝒪_W(G) = 𝒪_X(D)` inside `K(X)`. -/
private theorem multiplierIdealSections_eq_of_coeff (p : W ⟶ X) [IsDominant p]
    [UniversallyClosed p] [LocallyOfFiniteType p] (hbij : Function.Bijective (functionFieldMap p))
    (G : Divisor W) (D : Divisor X) (hD : ∀ Q, D.coeff Q ≤ 0)
    (hG1 : ∀ P : MMP.Mori.PrimeDivisor W,
      (∀ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint ≠ Q.genericPoint) → 0 ≤ G.coeff P)
    (hG2 : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → G.coeff P = D.coeff Q) (U : X.Opens) :
    multiplierIdealSections p G U = multiplierIdealSections (𝟙 X) D U := by
  ext g
  rw [mem_multiplierIdealSections_id_iff]
  constructor
  · rintro ⟨h0, hg⟩
    refine ⟨fun hU => h0 ((preimage_eq_bot_iff p U).2 hU), fun Q hQ => ?_⟩
    obtain ⟨x', hx', hco, -, -⟩ := exists_preimage_of_coheight_eq_one p hbij
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)
    let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hco
    have hPQ : p P.genericPoint = Q.genericPoint := by
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hco, hx']
    have hPU : (P.support ∩ p ⁻¹ᵁ U).Nonempty :=
      support_inter_nonempty_of_genericPoint_mem P (by
        change p P.genericPoint ∈ U
        rw [hPQ]
        exact genericPoint_mem_of_support_inter_nonempty Q hQ)
    have := hg P hPU
    rwa [Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint p hbij.2 P Q hPQ,
      hG2 P Q hPQ] at this
  · rintro ⟨h0, hg⟩
    by_cases hU : U = ⊥
    · obtain rfl := h0 hU
      exact ⟨fun _ => rfl, fun P _ => by simp⟩
    have : Nonempty U := by
      obtain ⟨u, hu⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty U).1 hU
      exact ⟨⟨u, hu⟩⟩
    obtain ⟨r, rfl⟩ := mem_range_germToFunctionField_of_forall U fun Q hQ =>
      (hg Q hQ).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; exact hD Q)
    refine ⟨fun h => absurd ((preimage_eq_bot_iff p U).1 h) hU, fun P hP => ?_⟩
    have hη : p P.genericPoint ∈ U := genericPoint_mem_of_support_inter_nonempty P hP
    by_cases hex : ∃ Q : MMP.Mori.PrimeDivisor X, p P.genericPoint = Q.genericPoint
    · obtain ⟨Q, hQ⟩ := hex
      rw [Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint p hbij.2 P Q hQ, hG2 P Q hQ]
      exact hg Q (support_inter_nonempty_of_genericPoint_mem Q (hQ ▸ hη))
    · push Not at hex
      refine (valuationOver_germ_le_one p r P hη).trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hG1 P hex

/-- **Normal Hartogs, `𝒪_X(0) = 𝒪_X`.** -/
private theorem multiplierIdealSections_id_zero (U : X.Opens) [Nonempty U] :
    multiplierIdealSections (𝟙 X) (0 : Divisor X) U = Set.range (X.germToFunctionField U) := by
  ext g
  rw [mem_multiplierIdealSections_id_iff]
  constructor
  · rintro ⟨-, hg⟩
    exact mem_range_germToFunctionField_of_forall U fun Q hQ => by
      simpa using hg Q hQ
  · rintro ⟨r, rfl⟩
    have hU : U ≠ ⊥ := by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      exact (TopologicalSpace.Opens.ne_bot_iff_nonempty U).2 ⟨u.1, u.2⟩
    refine ⟨fun h => absurd h hU, fun Q hQ => ?_⟩
    have := valuationOver_germ_le_one (𝟙 X) r Q
      (genericPoint_mem_of_support_inter_nonempty Q hQ)
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply] at this
    simpa using this

/-- In `ℤᵐ⁰`, a value `< 1` is at most `exp (-1)`. -/
private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A section over an affine open `U` lies in the vanishing ideal of a closed set `Z` exactly when
it vanishes at every point of `Z ∩ U`. -/
private theorem mem_vanishingIdeal_ideal_iff (U : X.affineOpens) (Z : TopologicalSpace.Closeds X)
    (f : Γ(X, (U : X.Opens))) :
    f ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U ↔
      ∀ y ∈ (Z : Set X), y ∈ (U : X.Opens) → y ∉ X.basicOpen f := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h y hyZ hyU
    obtain ⟨𝔭, rfl⟩ : y ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hyU
    intro hb
    have : 𝔭 ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hb
    rw [U.2.fromSpec_preimage_basicOpen] at this
    exact this (h 𝔭 hyZ)
  · intro h 𝔭 h𝔭
    by_contra hf
    have : 𝔭 ∈ PrimeSpectrum.basicOpen f := hf
    rw [← U.2.fromSpec_preimage_basicOpen] at this
    have hU : U.2.fromSpec 𝔭 ∈ (U : X.Opens) := by
      rw [← SetLike.mem_coe, ← U.2.range_fromSpec]
      exact ⟨𝔭, rfl⟩
    exact h _ h𝔭 hU this

/-- Along a prime divisor `Q` with generic point in `U`, a section over `U` has positive order
exactly when it vanishes at the generic point of `Q`. -/
private theorem divisorialValuation_germ_lt_one_iff {U : X.Opens} [Nonempty U] (f : Γ(X, U))
    (Q : MMP.Mori.PrimeDivisor X) (hQ : Q.genericPoint ∈ U) :
    Q.divisorialValuation (X.germToFunctionField U f) < 1 ↔ Q.genericPoint ∉ X.basicOpen f := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hQ,
    MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Scheme.mem_basicOpen X f _ hQ]

/-- **The ideal of the reduced support.** For an effective reduced divisor `T` (coefficients in
`{0, 1}`), the sections of `𝒪_X(-T)` over a non-empty affine open `U` are the regular functions on
`U` vanishing on `Supp T`. -/
private theorem multiplierIdealSections_id_neg_eq_image (T : Divisor X)
    (hT : ∀ Q, T.coeff Q = 0 ∨ T.coeff Q = 1) (U : X.affineOpens) [Nonempty (U : X.Opens)] :
    multiplierIdealSections (𝟙 X) (-T) U =
      X.germToFunctionField (U : X.Opens) '' (T.suppIdeal.ideal U : Set Γ(X, (U : X.Opens))) := by
  have hU : (U : X.Opens) ≠ ⊥ := by
    obtain ⟨u⟩ := (inferInstance : Nonempty (U : X.Opens))
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).2 ⟨u.1, u.2⟩
  ext g
  rw [mem_multiplierIdealSections_id_iff]
  constructor
  · rintro ⟨-, hg⟩
    have hle : ∀ Q : MMP.Mori.PrimeDivisor X, (Q.support ∩ (U : X.Opens)).Nonempty →
        Q.divisorialValuation g ≤ 1 := fun Q hQ =>
      (hg Q hQ).trans (by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp, DivisorWithCoeffs.coeff_neg]
        rcases hT Q with h | h <;> simp [h])
    obtain ⟨f, rfl⟩ := mem_range_germToFunctionField_of_forall (U : X.Opens) hle
    refine ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, DivisorWithCoeffs.suppIdeal, mem_vanishingIdeal_ideal_iff]
    intro y hyZ hyU hyf
    obtain ⟨Q, hQ0, hyQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hyZ
    have hQ1 : T.coeff Q = 1 := (hT Q).resolve_left hQ0
    have hsp : Q.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyQ
      exact specializes_iff_mem_closure.mpr hyQ
    have hQU : Q.genericPoint ∈ (U : X.Opens) := hsp.mem_open (U : X.Opens).isOpen hyU
    have hlt : Q.divisorialValuation (X.germToFunctionField (U : X.Opens) f) < 1 := by
      refine (hg Q (support_inter_nonempty_of_genericPoint_mem Q hQU)).trans_lt ?_
      rw [DivisorWithCoeffs.coeff_neg, hQ1, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      decide
    exact (divisorialValuation_germ_lt_one_iff f Q hQU).1 hlt
      (hsp.mem_open (X.basicOpen f).isOpen hyf)
  · rintro ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, DivisorWithCoeffs.suppIdeal, mem_vanishingIdeal_ideal_iff] at hf
    refine ⟨fun h => absurd h hU, fun Q hQ => ?_⟩
    have hQU := genericPoint_mem_of_support_inter_nonempty Q hQ
    rw [DivisorWithCoeffs.coeff_neg]
    rcases hT Q with h | h
    · rw [h, neg_zero, WithZero.exp_zero]
      have := valuationOver_germ_le_one (𝟙 X) f Q hQU
      rwa [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.functionFieldMap_id_apply] at this
    · rw [h]
      refine le_exp_neg_one_of_lt_one ((divisorialValuation_germ_lt_one_iff f Q hQU).2 ?_)
      refine hf _ (DivisorWithCoeffs.mem_supp_iff.2 ⟨Q, by simp [h], ?_⟩) hQU
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl

end Hartogs

/-- **The two floor sheaves of a log resolution of a dlt pair.** Let `(X, B)` be a `ℚ`-factorial
dlt pair (with canonical divisor `K` of dimension `n`) on a normal projective variety over an
algebraically closed field of characteristic zero, and let `p : W ⟶ X` be a projective log
resolution of `(X, B)` which is an isomorphism over the generic point of every stratum of
`T = ⌊B⌋`. Let `Δ_W` be the crepant boundary, `S = p⁻¹_* T`, `Γ = Δ_W - S` and `E = -⌊Γ⌋`. Then
`R^i p_* 𝒪_W(E) = 0 = R^i p_* 𝒪_W(E - S)` for `i > 0`, the sections of `p_* 𝒪_W(E)` over every
nonempty open `U` are the regular functions on `U`, and those of `p_* 𝒪_W(E - S)` are the sections
of `𝒪_X(-T)`, which over an affine `U` are the functions in the ideal of the reduced `Supp T`. -/
@[mmp "lem_fourfold_dlt_resolution_floor_ideal_vanishing"]
public theorem isZero_rightDerived_pushforward_floor_and_eq_idealSheaf
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (K : MMP.Mori.Divisor X) (B : MMP.Mori.QDivisor X)
    (hdlt : MMP.Mori.IsDltPair sX n K B) (hQ : MMP.Fourfold.IsQFactorial sX)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (p : W ⟶ X) [IsDominant p] (hres : MMP.Fourfold.IsLogResolution sX B p)
    (hW : MMP.Mori.IsNormalVariety k (p ≫ sX))
    (hstrata : ∀ Z : Set X, IsSNCStratum B.roundDown Z →
      ∃ U : X.Opens, (Z ∩ U).Nonempty ∧ IsIso (p ∣_ U))
    (ΔW : MMP.Mori.QDivisor W)
    (hΔ : MMP.Mori.IsCrepantBoundary sX n K B p hW
      hres.toIsLogResolution.isBirationalMorphism ΔW) :
    let T : MMP.Mori.Divisor X := B.roundDown
    let S : MMP.Mori.Divisor W := MMP.Mori.inverseTransformDivisor p T
    let E : MMP.Mori.Divisor W := -(ΔW - MMP.Mori.Divisor.toQDivisor S).roundDown
    -- `Rp_* 𝒪_W(E)` and `Rp_* 𝒪_W(E - S)` are concentrated in degree zero
    (∀ i : ℕ, 0 < i →
      Limits.IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj E.divisorialSheaf) ∧
      Limits.IsZero
        (((Scheme.Modules.pushforward p).rightDerived i).obj (E - S).divisorialSheaf)) ∧
    -- `p_* 𝒪_W(E) = 𝒪_X`
    (∀ (U : X.Opens) [Nonempty U],
      MMP.Intersection.multiplierIdealSections p E U = Set.range (X.germToFunctionField U)) ∧
    -- `p_* 𝒪_W(E - S) = 𝒪_X(-T)`
    (∀ U : X.Opens, MMP.Intersection.multiplierIdealSections p (E - S) U =
      MMP.Intersection.multiplierIdealSections (𝟙 X) (-T) U) ∧
    -- `p_* 𝒪_W(E - S) = 𝓘_T`, the ideal of the reduced subscheme `Supp T`
    (∀ (U : X.affineOpens) [Nonempty (U : X.Opens)],
      MMP.Intersection.multiplierIdealSections p (E - S) U =
        X.germToFunctionField (U : X.Opens) ''
          (T.suppIdeal.ideal U : Set Γ(X, (U : X.Opens)))) := by
  intro T S E
  classical
  have hPW : IsPairWith sX n K B := hdlt.isPairWith
  have hX : IsNormalVariety k sX := hPW.1
  have hP : MMP.Mori.IsPair sX B := hdlt.isPair
  have hb := hres.toIsLogResolution.isBirationalMorphism
  have : IsProper p := hres.toIsLogResolution.isProper
  have hbij := hb.functionFieldMap_bijective
  have hB01 : ∀ Q, 0 ≤ B.coeff Q ∧ B.coeff Q ≤ 1 := hdlt.2.1
  -- the coefficients of `T`, `S`, `Δ_W` and `E`
  have hT01 : ∀ Q, T.coeff Q = 0 ∨ T.coeff Q = 1 := by
    intro Q
    have h := hB01 Q
    simp only [T, DivisorWithCoeffs.coeff_roundDown]
    rcases h.2.lt_or_eq with h1 | h1
    · left
      exact Int.floor_eq_iff.2 ⟨by simpa using h.1, by simpa using h1⟩
    · right
      rw [h1]
      simp
  have hTB : ∀ Q, T.coeff Q = 1 → B.coeff Q = 1 := by
    intro Q hQ
    simp only [T, DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_iff] at hQ
    push_cast at hQ
    linarith [(hB01 Q).2]
  have hSc : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → S.coeff P = T.coeff Q := fun P Q h =>
    coeff_inverseTransformDivisor_of_map_genericPoint p hb T h
  have hS2 : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      S.coeff P = 0 := fun P h => coeff_inverseTransformDivisor_of_two_le_coheight p T h
  have hΔc : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → ΔW.coeff P = B.coeff Q := fun P Q h =>
    coeff_crepantBoundary_of_map_genericPoint hP hΔ h
  have hΔ1 : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      ΔW.coeff P < 1 := coeff_crepantBoundary_lt_one hdlt hΔ hstrata
  have hEc : ∀ P, E.coeff P = -⌊ΔW.coeff P - S.coeff P⌋ := fun P => by
    simp [E, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
  have hE0 : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → E.coeff P = 0 := by
    intro P Q h
    rw [hEc, hΔc P Q h, hSc P Q h]
    simp only [T, DivisorWithCoeffs.coeff_roundDown, neg_eq_zero]
    exact Int.floor_eq_iff.2 ⟨by push_cast; linarith [Int.floor_le (B.coeff Q)],
      by push_cast; linarith [Int.lt_floor_add_one (B.coeff Q)]⟩
  have hEnn : ∀ P, 0 ≤ E.coeff P := by
    intro P
    rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, h⟩ | h
    · rw [hE0 P Q h]
    · rw [hEc, hS2 P h]
      have := hΔ1 P h
      have : ⌊ΔW.coeff P - ((0 : ℤ) : ℚ)⌋ < 1 := Int.floor_lt.2 (by push_cast; linarith)
      omega
  -- the degree-zero direct images, by normal Hartogs
  have hdeg0 : ∀ U : X.Opens, multiplierIdealSections p (E - S) U =
      multiplierIdealSections (𝟙 X) (-T) U := by
    refine multiplierIdealSections_eq_of_coeff p hbij (E - S) (-T) (fun Q => ?_) (fun P hP => ?_)
      (fun P Q h => ?_)
    · rcases hT01 Q with h | h <;> simp [DivisorWithCoeffs.coeff_neg, h]
    · rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, h⟩ | h
      · exact absurd h (hP Q)
      · rw [DivisorWithCoeffs.coeff_sub, hS2 P h, sub_zero]
        exact hEnn P
    · rw [DivisorWithCoeffs.coeff_sub, hE0 P Q h, hSc P Q h, DivisorWithCoeffs.coeff_neg,
        zero_sub]
  have hdeg0' : ∀ (U : X.Opens) [Nonempty U],
      multiplierIdealSections p E U = Set.range (X.germToFunctionField U) := by
    intro U _
    refine (multiplierIdealSections_eq_of_coeff p hbij E 0 (fun Q => le_rfl)
      (fun P _ => hEnn P) (fun P Q h => ?_) U).trans (multiplierIdealSections_id_zero U)
    rw [hE0 P Q h]
    rfl
  refine ⟨?_, hdeg0', hdeg0, fun U _ =>
    (hdeg0 U).trans (multiplierIdealSections_id_neg_eq_image T hT01 U)⟩
  -- the higher direct images vanish
  have : MMP.Mori.IsVariety k sX := hX.1
  have : CompactSpace X := haveI := hX.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace W := haveI := hW.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  have hsm : IsSmoothScheme (p ≫ sX) := hres.toIsLogResolution.isSmoothScheme
  have hproj := hres.isProjectiveMorphism
  obtain ⟨ω, hω0, hωK, hKW⟩ := exists_divisorOfForm_pullback_isCanonicalDivisor sX hX hW hsm hb
    hPW.2.1
  set KW := divisorOfForm (pullbackRationalPluriForms sX p ω)
  obtain ⟨m, hm, D, hD, hDc⟩ := hPW.2.2.exists_pos
  obtain ⟨hpb, -, -⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP p hW hb hPW.2.1 hKW
    (Or.inl ⟨ω, hω0, hωK, rfl⟩) hΔ
  obtain ⟨DY, hDY, -, hB, hDYpb⟩ := hpb m hm D hD hDc
  have hCs := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p ((-1 : ℤ) • D)
  have hCμ := hDYpb.zsmul hDc (-1) hCs
  set Θ₀ : QDivisor W := ΔW - Divisor.toQDivisor S + Divisor.toQDivisor E with hΘ₀
  have hΘc : ∀ P, Θ₀.coeff P = Int.fract (ΔW.coeff P - S.coeff P) := by
    intro P
    rw [hΘ₀, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor, hEc P, Int.fract]
    push_cast
    ring
  have hΘ0 : ∀ P, 0 ≤ Θ₀.coeff P := fun P => by rw [hΘc]; exact Int.fract_nonneg _
  have hΘ1 : ∀ P, Θ₀.coeff P < 1 := fun P => by rw [hΘc]; exact Int.fract_lt_one _
  have hexc := isExceptional_iff_two_le_coheight hX hW hb
  have hS01 : ∀ P, S.coeff P = 0 ∨ S.coeff P = 1 := by
    intro P
    rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, h⟩ | h
    · rw [hSc P Q h]
      exact hT01 Q
    · exact Or.inl (hS2 P h)
  have hSex : ∀ P, S.coeff P ≠ 0 → ¬ RationalMap.IsExceptional (X := W) p.toRationalMap P :=
    fun P hP hE => hP (hS2 P ((hexc P).1 hE))
  have hSΘ : ∀ P, S.coeff P ≠ 0 → Θ₀.coeff P = 0 := by
    intro P hP
    rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, h⟩ | h
    · have hT1 : T.coeff Q = 1 := (hT01 Q).resolve_left (by rwa [← hSc P Q h])
      rw [hΘc, hΔc P Q h, hSc P Q h, hTB Q hT1, hT1]
      simp
    · exact absurd (hS2 P h) hP
  have hsnc : ∀ G : QDivisor W, (∀ P, G.coeff P ≠ 0 → S.coeff P ≠ 0 ∨ Θ₀.coeff P ≠ 0 ∨
      RationalMap.IsExceptional (X := W) p.toRationalMap P) →
        DivisorWithCoeffs.IsSNC (p ≫ sX) G := fun G hG =>
    isSNC_of_forall_two_le_coheight_or_coeff_ne_zero hres.toIsLogResolution G fun P hGP => by
      rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, h⟩ | h2
      · refine Or.inr ⟨Q, h, fun hB0 => ?_⟩
        have hT0 : T.coeff Q = 0 := by simp [T, hB0]
        rcases hG P hGP with hS | hΘ | hE
        · exact hS (by rw [hSc P Q h, hT0])
        · exact hΘ (by rw [hΘc, hΔc P Q h, hSc P Q h, hT0, hB0]; simp)
        · rw [hexc, h] at hE
          exact not_two_le_coheight_genericPoint Q hE
      · exact Or.inl h2
  have hgap : ∀ M S' : Divisor W, Divisor.toQDivisor M -
      (Divisor.toQDivisor KW + Divisor.toQDivisor S' + Θ₀) = -(Divisor.toQDivisor KW + ΔW) →
      Divisor.toQDivisor ((-1 : ℤ) • DY) =
        (m : ℤ) • (Divisor.toQDivisor M -
          (Divisor.toQDivisor KW + Divisor.toQDivisor S' + Θ₀)) := by
    intro M S' h
    rw [h, map_zsmul, hDY, smul_neg, neg_one_smul]
  intro i hi
  refine ⟨isZero_rightDerived_of_reducedBoundary sX hQ p hW hsm hproj hb hKW E S Θ₀ hS01 hSex
    hΘ0 hΘ1 hSΘ hsnc m hm _ (hDc.zsmul (-1)) hCs _ hCμ (hgap _ _ (by rw [hΘ₀]; abel)) i hi,
    isZero_rightDerived_of_reducedBoundary sX hQ p hW hsm hproj hb hKW (E - S) 0 Θ₀
    (fun P => Or.inl rfl) (fun P h => absurd rfl h) hΘ0 hΘ1 (fun P h => absurd rfl h)
    (fun G hG => hsnc G fun P hP => Or.inr ((hG P hP).resolve_left (· rfl))) m hm _
    (hDc.zsmul (-1)) hCs _ hCμ (hgap _ _ (by rw [hΘ₀, map_sub, map_zero]; abel)) i hi⟩

end Floor

end MMP.Fourfold
