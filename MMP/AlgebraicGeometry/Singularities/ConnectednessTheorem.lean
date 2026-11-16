module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Singularities.ConnectednessPushforwardSurjective
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Divisor.ExceptionalEffectivePushforward
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
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
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
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
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# The connectedness theorem

Let `h : X ⟶ Z` be a proper surjective morphism of normal varieties with connected fibres, and
`g : Y ⟶ X` a log resolution of `(X, D)` with `-(K_X + D)` `h`-nef and `h`-big. Then the locus of
`Y` where the discrepancy is at most `-1` is connected over every closed point of `Z` (FA 17.4).
The proof deduces connected fibres from the surjectivity of a direct image, via the Stein
factorization.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite MMP MMP.Mori MMP.Flips

namespace MMP.Fold06.ThmFa17Connectedness

noncomputable section

universe u

/-! ### The ideal sheaf of an effective divisor -/

section DivisorialIdeal

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

/-- The ideal of the functions on `U` whose divisor is at least `G` on `U`: the `a` with
`a ∈ 𝒪_Y(-G)(U)`, i.e. `v_E(a) ≥ g_E` for every prime divisor `E` meeting `U`. -/
private def divisorialIdeal (G : Divisor Y) (U : Y.Opens) : Ideal Γ(Y, U) :=
  ((-G).divisorialSubmodule U).comap
    (Algebra.linearMap Γ(Y, U) ((rationalFunctionsPresheaf Y).obj (op U)))

private theorem mem_divisorialIdeal {G : Divisor Y} {U : Y.Opens} {a : Γ(Y, U)} :
    a ∈ divisorialIdeal G U ↔
      (-G).IsDivisorialSection U ((toRationalFunctionsPresheaf Y).app (op U) a) :=
  Iff.rfl

/-- The ideals `divisorialIdeal G U` are compatible with localization to basic opens: a
function on `D(f) ⊆ U` with divisor at least `G` is, up to a power of `f`, the restriction of
one on `U`. -/
private theorem map_divisorialIdeal_basicOpen [CompactSpace Y] {G : Divisor Y} (hG : 0 ≤ G)
    (U : Y.Opens) (f : Γ(Y, U)) :
    (divisorialIdeal G U).map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom =
      divisorialIdeal G (Y.basicOpen f) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_divisorialIdeal, toRationalFunctionsPresheaf_app_map]
    exact ha.map _
  · intro a ha
    letI := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE (-G).divisorialSheaf
      (Y.basicOpen_le f)
    have hloc := Divisor.isLocalizedModule_divisorialSheaf_restrictₗ (-G) f
    obtain ⟨⟨φ, ⟨_, n, rfl⟩⟩, hφ⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ (-G).divisorialSheaf
        (Y.basicOpen_le f))
      (⟨(toRationalFunctionsPresheaf Y).app (op _) a, ha⟩ :
        (-G).divisorialSubmodule (Y.basicOpen f))
    have hφ0 : (0 : Divisor Y).IsDivisorialSection U φ.1 :=
      Divisor.IsDivisorialSection.mono φ.2 (neg_nonpos.mpr hG)
    obtain ⟨b, hb⟩ := hφ0.exists_eq
    have hbI : b ∈ divisorialIdeal G U := by
      rw [mem_divisorialIdeal, hb]
      exact φ.2
    set ρ := (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom
    have heq : ρ (f ^ n) * a = ρ b := by
      apply toRationalFunctionsPresheaf_app_injective
      rw [map_mul, toRationalFunctionsPresheaf_app_map (homOfLE (Y.basicOpen_le f)) b, hb]
      exact congrArg Subtype.val hφ
    have hu : IsUnit (ρ (f ^ n)) := by
      rw [map_pow]
      exact (Y.toRingedSpace.isUnit_res_basicOpen f).pow n
    have : a = ((hu.unit⁻¹ : (Γ(Y, Y.basicOpen f))ˣ) : Γ(Y, Y.basicOpen f)) * ρ b := by
      rw [← heq, ← mul_assoc, hu.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hbI)

variable [CompactSpace Y]

/-- The ideal sheaf `𝒪_Y(-G) ∩ 𝒪_Y` of an effective divisor `G`, the ideal of the closed
subscheme `G` of `Y`. -/
private def divisorialIdealSheaf {G : Divisor Y} (hG : 0 ≤ G) : Y.IdealSheafData where
  ideal U := divisorialIdeal G U.1
  map_ideal_basicOpen U f := map_divisorialIdeal_basicOpen hG U.1 f

private theorem ideal_divisorialIdealSheaf {G : Divisor Y} (hG : 0 ≤ G) (U : Y.affineOpens) :
    (divisorialIdealSheaf hG).ideal U = divisorialIdeal G U.1 := rfl

/-- The closed subscheme `G` has support `Supp G`. -/
private theorem coe_support_divisorialIdealSheaf {G : Divisor Y} (hG : 0 ≤ G) :
    ((divisorialIdealSheaf hG).support : Set Y) = G.supp := by
  ext x
  constructor
  · intro h
    by_contra hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVs⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx
      G.supp.isClosed.isOpen_compl
    have h' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).mp h
    rw [Scheme.mem_zeroLocus_iff] at h'
    refine h' 1 ?_ (by rwa [Scheme.basicOpen_one])
    rw [SetLike.mem_coe, ideal_divisorialIdealSheaf, mem_divisorialIdeal, map_one]
    intro E hE
    have hG0 : G.coeff E = 0 := by
      by_contra hne
      obtain ⟨y, hyE, hyV⟩ := hE
      exact hVs hyV (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hyE⟩)
    simpa [hG0] using Divisor.IsDivisorialSection.one (le_refl (0 : Divisor Y)) V E hE
  · intro hx
    obtain ⟨E, hE0, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mpr ?_
    rw [Scheme.mem_zeroLocus_iff]
    intro a ha hxa
    have hηa := E.genericPoint_mem_of_nonempty ⟨x, hxE, hxa⟩
    have hηU : E.genericPoint ∈ U := Y.basicOpen_le a hηa
    have hunit : IsUnit (Y.presheaf.germ U _ hηU a) := (Y.mem_basicOpen a _ hηU).mp hηa
    have hEU : (E.support ∩ U).Nonempty := ⟨x, hxE, hxU⟩
    have hval := (mem_divisorialIdeal.mp ha) E hEU
    have hgerm : (toRationalFunctionsPresheaf Y).app (op U) a
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEU⟩ =
        E.toComponent.hom (Y.presheaf.germ U _ hηU a) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hηU E.specializes_genericPoint a).symm
    rw [hgerm] at hval
    rcases hval with h0 | hv
    · exact (hunit.map E.toComponent.hom).ne_zero h0
    · rw [E.valuation_toComponent_of_isUnit hunit, DivisorWithCoeffs.coeff_neg, neg_neg,
        ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
      exact hE0 (le_antisymm hv (hG E))

end DivisorialIdeal

/-! ### Sections of sheaves of modules -/

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- An epimorphism of `𝒪_Z`-modules is locally surjective, as a morphism of presheaves of
abelian groups. -/
private theorem isLocallySurjective_mapPresheaf_of_epi {Z : Scheme.{u}} {M N : Z.Modules}
    (φ : M ⟶ N) [Epi φ] : TopCat.Presheaf.IsLocallySurjective (Scheme.Modules.Hom.mapPresheaf φ) :=
  Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi φ

/-- An epimorphism of `𝒪_Z`-modules is locally surjective on sections. -/
private theorem exists_app_eq_map_of_epi {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) [Epi φ]
    {U : Z.Opens} (t : Γ(N, U)) {z : Z} (hz : z ∈ U) :
    ∃ (V : Z.Opens) (hV : V ≤ U), z ∈ V ∧
      ∃ x : Γ(M, V), φ.app V x = N.presheaf.map (homOfLE hV).op t := by
  obtain ⟨V, i, ⟨x, hx⟩, hzV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    (isLocallySurjective_mapPresheaf_of_epi φ) U t z hz
  exact ⟨V, fun _ h => i h, hzV, x, hx⟩

/-- Left exactness of sections: a section of `N` over `W` killed by the cokernel projection of a
monomorphism `i : M ⟶ N` comes from a section of `M` over `W`. -/
private theorem exists_app_eq_of_cokernel_π_app_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (i : M ⟶ N) [Mono i] {W : X.Opens} (x : Γ(N, W)) (hx : (cokernel.π i).app W x = 0) :
    ∃ y : Γ(M, W), i.app W y = x := by
  let ev := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesLimits ev := evaluationPreservesLimits _
  have : PreservesLimits (Scheme.Modules.toPresheaf X ⋙ ev) := comp_preservesLimits _ _
  have hex := (ShortComplex.cokernelSequence_exact i).map_of_mono_of_preservesKernel
    (Scheme.Modules.toPresheaf X ⋙ ev) ‹Mono i› inferInstance
  exact (ShortComplex.ab_exact_iff _).1 hex x hx

/-- The cokernel projection kills the sections coming from the source. -/
private theorem cokernel_π_app_app_eq_zero {X : Scheme.{u}} {M N : X.Modules} (i : M ⟶ N)
    (U : X.Opens) (y : Γ(M, U)) : (cokernel.π i).app U (i.app U y) = 0 :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U) (cokernel.condition i)) y

/-- Restricting twice is restricting once. -/
private theorem presheaf_map_map_apply {X : TopCat.{u}} {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    (F : TopCat.Presheaf C X) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    (x : ToType (F.obj U)) : F.map j (F.map i x) = F.map k x := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  congr 2

/-- Morphisms of `𝒪_X`-modules commute with restriction of sections. -/
private theorem app_presheaf_map_apply {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

/-- Morphisms of schemes commute with restriction of functions. -/
private theorem presheaf_map_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens}
    (h : W ≤ V) (x : Γ(Y, V)) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app V x) =
      f.app W (Y.presheaf.map (homOfLE h).op x) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) x).symm

/-- Sections of an `𝒪_X`-module which agree locally are equal. -/
private theorem modules_eq_of_locally_eq {X : Scheme.{u}} (M : X.Modules) {W : X.Opens}
    (s t : Γ(M, W)) (h : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧
      M.presheaf.map (homOfLE hV).op s = M.presheaf.map (homOfLE hV).op t) : s = t := by
  choose V hV hxV hst using h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun x : W => V x.1 x.2) W (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) s t (fun x => hst x.1 x.2)

/-- Functions on a scheme which agree locally are equal. -/
private theorem scheme_eq_of_locally_eq (X : Scheme.{u}) {W : X.Opens} (s t : Γ(X, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧
      X.presheaf.map (homOfLE hV).op s = X.presheaf.map (homOfLE hV).op t) : s = t := by
  choose V hV hxV hst using h
  exact TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun x : W => V x.1 x.2) W (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) s t (fun x => hst x.1 x.2)

/-! ### The sections of `𝒪_{G}(H)` and functions on the subscheme `G` -/

section Cokernel

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {G H : Divisor Y} (hG : 0 ≤ G) (hH : 0 ≤ H) (hle : H - G ≤ H)

/-- The section `a · 1` of `𝒪_Y(H)` defined by a function `a` on `W`, for `H` effective: the
map `𝒪_Y ⟶ 𝒪_Y(H)` on sections over `W`. -/
private def unitSection (W : Y.Opens) : Γ(Y, W) →+ Γ(H.divisorialSheaf, W) :=
  (ConcreteCategory.hom ((Divisor.structureSheafToDivisorialSheaf hH).app W) :
    Γ(Y, W) →+ Γ(H.divisorialSheaf, W))

private theorem coe_unitSection (W : Y.Opens) (a : Γ(Y, W)) :
    (unitSection hH W a).1 = (toRationalFunctionsPresheaf Y).app (op W) a :=
  Divisor.coe_structureSheafToDivisorialSheaf_app hH W a

private theorem presheaf_map_unitSection {U V : Y.Opens} (i : V ⟶ U) (a : Γ(Y, U)) :
    H.divisorialSheaf.presheaf.map i.op (unitSection hH U a) =
      unitSection hH V (Y.presheaf.map i.op a) :=
  (app_presheaf_map_apply (M := Mori.structureSheafModule Y) _ i a).symm

include hG in
/-- A function vanishing on the closed subscheme `G` maps to zero in `𝒪_G(H)`, the cokernel
of `𝒪_Y(H - G) ⟶ 𝒪_Y(H)`. -/
private theorem cokernel_π_app_structureSheafToDivisorialSheaf_eq_zero {W : Y.Opens}
    (a : Γ(Y, W)) (ha : (divisorialIdealSheaf hG).subschemeι.app W a = 0) :
    (cokernel.π (Divisor.divisorialSheafInclusion hle)).app W
      (unitSection hH W a) = 0 := by
  apply modules_eq_of_locally_eq
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  replace hVW : V ≤ W := hVW
  refine ⟨V, hVW, hxV, ?_⟩
  rw [map_zero, ← app_presheaf_map_apply]
  set a' : Γ(Y, V) := Y.presheaf.map (homOfLE hVW).op a with ha'_def
  rw [presheaf_map_unitSection]
  have hι : (divisorialIdealSheaf hG).subschemeι.app V a' = 0 := by
    rw [ha'_def, ← presheaf_map_app_apply _ hVW, ha, map_zero]
  have ha' : a' ∈ divisorialIdeal G V := by
    rw [← ideal_divisorialIdealSheaf hG ⟨V, hV⟩, ← Scheme.IdealSheafData.ker_subschemeι_app]
    exact hι
  have hmem : (H - G).IsDivisorialSection V ((toRationalFunctionsPresheaf Y).app (op V) a') :=
    Divisor.IsDivisorialSection.mono ha' (by rw [sub_eq_add_neg]; exact le_add_of_nonneg_left hH)
  have heq : unitSection hH V a' = (Divisor.divisorialSheafInclusion hle).app V ⟨_, hmem⟩ :=
    Subtype.ext (coe_unitSection hH V a')
  rw [heq]
  exact cokernel_π_app_app_eq_zero _ _ _

include hG in
/-- Conversely, a function whose image in `𝒪_G(H)` vanishes vanishes on the closed subscheme
`G`, provided a function with divisor at least `G - H` has divisor at least `G`. -/
private theorem subschemeι_app_eq_zero_of_cokernel_π_app_eq_zero
    (hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    {W : Y.Opens} (a : Γ(Y, W))
    (ha : (cokernel.π (Divisor.divisorialSheafInclusion hle)).app W
      (unitSection hH W a) = 0) :
    (divisorialIdealSheaf hG).subschemeι.app W a = 0 := by
  obtain ⟨y, hy⟩ := exists_app_eq_of_cokernel_π_app_eq_zero _ _ ha
  have hmem : (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
    rw [← coe_unitSection hH W a, ← hy]
    exact y.2
  have hmem' := hann W a hmem
  apply scheme_eq_of_locally_eq
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  replace hVW : V ≤ W := hVW
  refine ⟨(divisorialIdealSheaf hG).subschemeι ⁻¹ᵁ V,
    (divisorialIdealSheaf hG).subschemeι.preimage_mono hVW, hxV, ?_⟩
  rw [map_zero]
  refine (presheaf_map_app_apply _ hVW a).trans ?_
  have ha' : Y.presheaf.map (homOfLE hVW).op a ∈ divisorialIdeal G V := by
    rw [mem_divisorialIdeal, toRationalFunctionsPresheaf_app_map]
    exact hmem'.map _
  rw [← ideal_divisorialIdealSheaf hG ⟨V, hV⟩, ← Scheme.IdealSheafData.ker_subschemeι_app] at ha'
  exact ha'

include hG in
/-- **Functions on the subscheme `G` come from `Z` near `z`.** Let `f : Y ⟶ Z` be such that
`f_* 𝒪_Y(H) ⟶ f_* 𝒪_G(H)` is an epimorphism and every section of `𝒪_Y(H)` over `f⁻¹ U` is
`f^♯ r` for a function `r` on `U`. Then every function `b` on `G ∩ f⁻¹ U` agrees, on
`G ∩ f⁻¹ U'` for a neighbourhood `U' ⊆ U` of `z`, with the pull-back of a function on `U'`. -/
private theorem exists_presheaf_map_eq_app_of_epi {Z : Scheme.{u}} (f : Y ⟶ Z)
    (hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    [Epi ((Scheme.Modules.pushforward f).map (cokernel.π (Divisor.divisorialSheafInclusion hle)))]
    (hsurj : ∀ U : Z.Opens, Function.Surjective fun r : Γ(Z, U) =>
      unitSection hH (f ⁻¹ᵁ U) (f.app U r))
    {U : Z.Opens} {z : Z} (hzU : z ∈ U)
    (b : Γ((divisorialIdealSheaf hG).subscheme,
      (divisorialIdealSheaf hG).subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U))) :
    ∃ (U' : Z.Opens) (hU' : U' ≤ U), z ∈ U' ∧ ∃ r : Γ(Z, U'),
      (divisorialIdealSheaf hG).subscheme.presheaf.map
          (homOfLE ((divisorialIdealSheaf hG).subschemeι.preimage_mono
            (f.preimage_mono hU'))).op b =
        (divisorialIdealSheaf hG).subschemeι.app (f ⁻¹ᵁ U') (f.app U' r) := by
  classical
  set incl := Divisor.divisorialSheafInclusion hle
  set π := cokernel.π incl
  -- local lifts of `b` to functions on `Y`
  have hA : ∀ y : (f ⁻¹ᵁ U : Set Y), ∃ (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U), (y : Y) ∈ V ∧
      ∃ a : Γ(Y, V), (divisorialIdealSheaf hG).subschemeι.app V a =
        (divisorialIdealSheaf hG).subscheme.presheaf.map
          (homOfLE ((divisorialIdealSheaf hG).subschemeι.preimage_mono hV)).op b := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open y.2 (f ⁻¹ᵁ U).isOpen
    replace hVU : V ≤ f ⁻¹ᵁ U := hVU
    obtain ⟨a, ha⟩ := (divisorialIdealSheaf hG).subschemeι_app_surjective ⟨V, hV⟩
      ((divisorialIdealSheaf hG).subscheme.presheaf.map
        (homOfLE ((divisorialIdealSheaf hG).subschemeι.preimage_mono hVU)).op b)
    exact ⟨V, hVU, hyV, a, ha⟩
  choose V hV hyV a ha using hA
  have hres : ∀ y (W : Y.Opens) (hW : W ≤ V y),
      (divisorialIdealSheaf hG).subschemeι.app W (Y.presheaf.map (homOfLE hW).op (a y)) =
        (divisorialIdealSheaf hG).subscheme.presheaf.map (homOfLE
          ((divisorialIdealSheaf hG).subschemeι.preimage_mono (hW.trans (hV y)))).op b := by
    intro y W hW
    rw [← presheaf_map_app_apply _ hW, ha y]
    exact presheaf_map_map_apply _ _ _ _ _
  -- their images in `𝒪_G(H)` glue
  let τ : ∀ y, Γ(cokernel incl, V y) := fun y => π.app (V y) (unitSection hH (V y) (a y))
  have hτres : ∀ y (W : Y.Opens) (hW : W ≤ V y), (cokernel incl).presheaf.map (homOfLE hW).op
      (τ y) = π.app W (unitSection hH W (Y.presheaf.map (homOfLE hW).op (a y))) := by
    intro y W hW
    rw [← app_presheaf_map_apply, presheaf_map_unitSection]
  have hcompat : ∀ y y' (W : Y.Opens) (hW : W ≤ V y) (hW' : W ≤ V y'),
      (cokernel incl).presheaf.map (homOfLE hW).op (τ y) =
        (cokernel incl).presheaf.map (homOfLE hW').op (τ y') := by
    intro y y' W hW hW'
    rw [hτres, hτres, ← sub_eq_zero, ← map_sub, ← map_sub]
    apply cokernel_π_app_structureSheafToDivisorialSheaf_eq_zero hG hH hle
    rw [map_sub, hres, hres, sub_self]
  obtain ⟨τg, hτg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(cokernel incl).presheaf, (cokernel incl).isSheaf⟩ : TopCat.Sheaf Ab Y) V (f ⁻¹ᵁ U)
    (fun y => homOfLE (hV y)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyV ⟨x, hx⟩⟩) τ
    (fun y y' => hcompat y y' _ inf_le_left inf_le_right)
  -- near `z`, the glued section comes from `𝒪_Y(H)`, hence from `𝒪_Z`
  obtain ⟨U', hU', hzU', x, hx⟩ :=
    exists_app_eq_map_of_epi ((Scheme.Modules.pushforward f).map π)
      (N := (Scheme.Modules.pushforward f).obj (cokernel incl)) τg hzU
  obtain ⟨r, rfl⟩ := hsurj U' x
  refine ⟨U', hU', hzU', r, ?_⟩
  have hτg' : ∀ y, (cokernel incl).presheaf.map (homOfLE (hV y)).op τg = τ y := hτg
  have hx' : π.app (f ⁻¹ᵁ U') (unitSection hH (f ⁻¹ᵁ U') (f.app U' r)) =
      (cokernel incl).presheaf.map (homOfLE (f.preimage_mono hU')).op τg := hx
  -- the equality is local on the subscheme
  apply scheme_eq_of_locally_eq
  intro p hp
  have hpU : (divisorialIdealSheaf hG).subschemeι p ∈ f ⁻¹ᵁ U := f.preimage_mono hU' hp
  set y : (f ⁻¹ᵁ U : Set Y) := ⟨_, hpU⟩
  have hWy : V y ⊓ f ⁻¹ᵁ U' ≤ V y := inf_le_left
  have hWU' : V y ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U' := inf_le_right
  refine ⟨(divisorialIdealSheaf hG).subschemeι ⁻¹ᵁ (V y ⊓ f ⁻¹ᵁ U'),
    (divisorialIdealSheaf hG).subschemeι.preimage_mono hWU', ⟨hyV y, hp⟩, ?_⟩
  have key := subschemeι_app_eq_zero_of_cokernel_π_app_eq_zero hG hH hle hann
    (Y.presheaf.map (homOfLE hWy).op (a y) - Y.presheaf.map (homOfLE hWU').op (f.app U' r)) ?_
  · rw [map_sub, sub_eq_zero, hres] at key
    rw [presheaf_map_map_apply _ _ _ (homOfLE ((divisorialIdealSheaf hG).subschemeι.preimage_mono
      (hWy.trans (hV y)))).op, key]
    exact (presheaf_map_app_apply _ hWU' (f.app U' r)).symm
  · rw [map_sub, map_sub, sub_eq_zero, ← hτres y _ hWy, ← hτg' y, ← presheaf_map_unitSection,
      app_presheaf_map_apply π, hx',
      presheaf_map_map_apply _ _ _ (homOfLE (hWy.trans (hV y))).op,
      presheaf_map_map_apply _ _ _ (homOfLE (hWy.trans (hV y))).op]

end Cokernel

/-- Let `c : S ⟶ Z` be quasi-compact and quasi-separated, `U` an affine open of `Z` and `z ∈ U`.
A function `b` on `c⁻¹ U` which agrees on `c⁻¹ U'`, for an open `z ∈ U' ⊆ U`, with `c^♯ r` for a
function `r` on `U'` satisfies `c^♯(s) b = c^♯(a)` for functions `s, a` on `U` with `s(z) ≠ 0`:
`Γ(Z, D(s))` and `Γ(S, c⁻¹ D(s))` are the localizations of `Γ(Z, U)` and `Γ(S, c⁻¹ U)` at
`s`. -/
private theorem exists_mul_eq_app_of_presheaf_map_eq {S Z : Scheme.{u}} (c : S ⟶ Z)
    [QuasiCompact c] [QuasiSeparated c] (U : Z.affineOpens) {z : Z} {U' : Z.Opens}
    (hU' : U' ≤ U.1) (hzU' : z ∈ U') (b : Γ(S, c ⁻¹ᵁ U.1)) (r : Γ(Z, U'))
    (hr : S.presheaf.map (homOfLE (c.preimage_mono hU')).op b = c.app U' r) :
    ∃ s a : Γ(Z, U.1), z ∈ Z.basicOpen s ∧ c.app U.1 s * b = c.app U.1 a := by
  obtain ⟨s, hsU', hzs⟩ := U.2.exists_basicOpen_le ⟨z, hzU'⟩ (hU' hzU')
  have hDU : Z.basicOpen s ≤ U.1 := Z.basicOpen_le s
  have := U.2.isLocalization_basicOpen s
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hra⟩ :=
    IsLocalization.surj (Submonoid.powers s) (Z.presheaf.map (homOfLE hsU').op r)
  have hb : S.presheaf.map (homOfLE (c.preimage_mono hDU)).op b =
      c.app (Z.basicOpen s) (Z.presheaf.map (homOfLE hsU').op r) := by
    rw [← presheaf_map_map_apply _ (homOfLE (c.preimage_mono hU')).op
      (homOfLE (c.preimage_mono hsU')).op, hr, presheaf_map_app_apply c]
  have hloc : IsLocalization.Away (c.app U.1 s) Γ(S, S.basicOpen (c.app U.1 s)) :=
    isLocalization_basicOpen_of_qcqs (c.isCompact_preimage U.2.isCompact)
      (c.isQuasiSeparated_preimage U.2.isQuasiSeparated) _
  have hk : S.basicOpen (c.app U.1 s) ≤ c ⁻¹ᵁ Z.basicOpen s := (Scheme.preimage_basicOpen c s).ge
  have hres : ∀ x : Γ(S, c ⁻¹ᵁ U.1), algebraMap _ Γ(S, S.basicOpen (c.app U.1 s)) x =
      S.presheaf.map (homOfLE hk).op (S.presheaf.map (homOfLE (c.preimage_mono hDU)).op x) :=
    fun x => (presheaf_map_map_apply _ _ _ _ x).symm
  have heq : algebraMap _ Γ(S, S.basicOpen (c.app U.1 s)) (c.app U.1 s ^ n * b) =
      algebraMap _ Γ(S, S.basicOpen (c.app U.1 s)) (c.app U.1 a) := by
    rw [hres, hres]
    congr 1
    rw [map_mul, map_pow, presheaf_map_app_apply c, hb, presheaf_map_app_apply c, ← map_pow,
      ← map_mul]
    congr 1
    rw [mul_comm, ← map_pow]
    exact hra
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (c.app U.1 s)) _).mp heq
  refine ⟨s ^ (m + n), s ^ m * a, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (m + n) with h0 | hpos
    · rw [h0, pow_zero, Scheme.basicOpen_one]
      exact hU' hzU'
    · rw [Scheme.basicOpen_pow _ _ hpos]
      exact hzs
  · simp only at hm
    rw [map_mul, map_pow, map_pow, pow_add, mul_assoc]
    exact hm

/-! ### Discrepancies on the log resolution -/

/-- If `d + c = n`, then `d + 2 ≤ n` exactly when `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

/-- A divisor over `X` is exceptional exactly when its center has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) :
    E.IsExceptional ↔ 2 ≤ Order.coheight (E.f E.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (E.f E.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- **The discrepancies of `g^*(K + D)`.** Let `ω` be a rational form with `div ω = K`, and let
`N = -m₀ (K + D)` be Cartier. Then the discrepancy of a prime divisor `E` on the model `Y` is
`a(E, D) = ord_E(g^* ω) + coeff_E(g^* N) / m₀`: it is computed with the one-term presentation
`div ω + D = -(1/m₀) N`. -/
private theorem eq_ordForm_add_coeff_pullback_of_isDiscrepancy {k : Type} [Field k]
    [PerfectField k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hX : IsNormalVariety k sX) {g : Y ⟶ X}
    [IsProper g]
    (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g) {n : ℕ} {K : Divisor X}
    {D : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hdivω : divisorOfForm ω = K)
    {m₀ : ℕ} (hm₀ : 0 < m₀) {N : Divisor X} (hNc : N.IsCartier)
    (hNM : Divisor.toQDivisor N = (m₀ : ℚ) • -(Divisor.toQDivisor K + D))
    (hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp)
    (E : Mori.PrimeDivisor Y) {a : ℚ}
    (ha : IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation a) :
    haveI : IsDominant g := hgb.isDominant
    a = (divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E +
      (m₀ : ℚ)⁻¹ * (N.pullback hNc hNB).coeff E := by
  have : IsDominant g := hgb.isDominant
  have hm : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hdisc : IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation
      (((divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E : ℝ) +
        (m₀ : ℝ)⁻¹ * ((N.pullback hNc hNB).coeff E : ℝ)) := by
    refine ⟨ha.1, ha.2.1, ha.2.2.1, _, ω, 1, fun _ => -(m₀ : ℝ)⁻¹, fun _ => N, rfl, hdivω, hX,
      ha.1.topologicalKrullDim_eq, hω0, fun _ => hNc, ?_, fun _ => N.pullback hNc hNB,
      fun _ => ⟨hNB, Divisor.isPullback_pullback hNc hNB⟩, ?_⟩
    · ext Γ
      have hΓ := congrArg (fun G : QDivisor X => ((G.coeff Γ : ℚ) : ℝ)) hNM
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_add] at hΓ
      push_cast at hΓ
      simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hdivω,
        QDivisor.coeff_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      rw [hΓ]
      field_simp
    · rw [Fin.sum_univ_one, coeff_divisorOfForm]
      change _ = (E.ordForm (pullbackRationalPluriForms sX g ω) : ℝ) - _
      ring
  have h : ((a : ℚ) : ℝ) = (((divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E +
      (m₀ : ℚ)⁻¹ * (N.pullback hNc hNB).coeff E : ℚ) : ℝ) := by
    push_cast
    exact ha.eq hdisc
  exact_mod_cast h

/-! ### Connected fibres from the Stein factorization -/

/-- Let `φ : A → B` be a ring map and `p` an ideal of `A` such that every `b ∈ B` satisfies
`φ(s) b = φ(a)` for some `s ∉ p` and `a ∈ A`. Then a prime of `B` lying over `p` contains every
ideal of `B` lying over `p`. -/
private theorem le_of_comap_eq_of_forall_exists_mul_eq {A B : Type*} [CommSemiring A]
    [CommSemiring B] (φ : A →+* B) {p : Ideal A} (H : ∀ b : B, ∃ s a : A, s ∉ p ∧ φ s * b = φ a)
    {q₁ q₂ : Ideal B} [hq : q₂.IsPrime] (h₁ : q₁.comap φ = p) (h₂ : q₂.comap φ = p) :
    q₁ ≤ q₂ := by
  intro b hb
  obtain ⟨s, a, hs, hsa⟩ := H b
  have ha : a ∈ p := by
    rw [← h₁, Ideal.mem_comap, ← hsa]
    exact q₁.mul_mem_left _ hb
  have hsab : φ s * b ∈ q₂ := by
    rw [hsa, ← Ideal.mem_comap, h₂]
    exact ha
  refine (hq.mem_or_mem hsab).resolve_left fun hs' => hs ?_
  rw [← h₂]
  exact hs'

/-- **Connected fibres from a cyclic direct image.** Let `c : S ⟶ Z` be proper, `U` an affine open
of `Z` and `z ∈ U`, such that every function `b` on `c⁻¹ U` satisfies `c^♯(s) b = c^♯(a)` for some
functions `s, a` on `U` with `s(z) ≠ 0`, i.e. `𝒪_{Z,z} → (c_* 𝒪_S)_z` is surjective. Then the
fibre `c⁻¹(z)` is connected (possibly empty): the Stein factorization of `c` has at most one
point over `z`, and its first factor has connected fibres. -/
private theorem isPreconnected_preimage_singleton_of_forall_exists_mul_eq {S Z : Scheme.{u}}
    (c : S ⟶ Z) [IsProper c] (U : Z.affineOpens) {z : Z} (hzU : z ∈ U.1)
    (hloc : ∀ b : Γ(S, c ⁻¹ᵁ U.1), ∃ s a : Γ(Z, U.1), z ∈ Z.basicOpen s ∧
      c.app U.1 s * b = c.app U.1 a) :
    _root_.IsPreconnected (c ⁻¹' {z}) := by
  have : QuasiCompact c := instQuasiCompactOfUniversallyClosed c
  have : QuasiSeparated c := IsSeparated.instQuasiSeparated c
  have := Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper c
  have huniq : ∀ w₁ w₂ : c.normalization, c.fromNormalization w₁ = z →
      c.fromNormalization w₂ = z → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂
    have : IsOpenImmersion (c.normalizationOpenCover.f U) := c.normalizationOpenCover.map_prop U
    have hmem : ∀ w, c.fromNormalization w = z →
        w ∈ Set.range (c.normalizationOpenCover.f U) := by
      intro w hw
      change w ∈ (c.normalizationOpenCover.f U).opensRange
      rw [← c.fromNormalization_preimage U]
      change c.fromNormalization w ∈ U.1
      rw [hw]
      exact hzU
    obtain ⟨q₁, rfl⟩ := hmem w₁ h₁
    obtain ⟨q₂, rfl⟩ := hmem w₂ h₂
    have hcomp : ∀ q, c.fromNormalization (c.normalizationOpenCover.f U q) =
        U.2.fromSpec (Spec.map (c.normalizationDiagramMap.app (op U.1)) q) := fun q => by
      rw [← Scheme.Hom.comp_apply, c.ι_fromNormalization U]
      rfl
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    set p := U.2.primeIdealOf ⟨z, hzU⟩ with hp_def
    have hp : ∀ q, c.fromNormalization (c.normalizationOpenCover.f U q) = z →
        Spec.map (c.normalizationDiagramMap.app (op U.1)) q = p := fun q hq =>
      U.2.fromSpec.isOpenEmbedding.injective (by rw [← hcomp, hq, U.2.fromSpec_primeIdealOf])
    set φ := (c.normalizationDiagramMap.app (op U.1)).hom with hφ
    have H : ∀ b, ∃ s a, s ∉ p.asIdeal ∧ φ s * b = φ a := by
      intro b
      obtain ⟨s, a, hs, hsa⟩ := hloc b.1
      refine ⟨s, a, ?_, Subtype.ext hsa⟩
      have hps : p ∈ U.2.fromSpec ⁻¹ᵁ Z.basicOpen s := by
        change U.2.fromSpec p ∈ Z.basicOpen s
        rw [hp_def, U.2.fromSpec_primeIdealOf]
        exact hs
      rw [U.2.fromSpec_preimage_basicOpen] at hps
      exact hps
    have h₁' : q₁.asIdeal.comap φ = p.asIdeal := congrArg PrimeSpectrum.asIdeal (hp q₁ h₁)
    have h₂' : q₂.asIdeal.comap φ = p.asIdeal := congrArg PrimeSpectrum.asIdeal (hp q₂ h₂)
    congr 1
    exact PrimeSpectrum.ext (le_antisymm
      (le_of_comap_eq_of_forall_exists_mul_eq φ H (hq := q₂.isPrime) h₁' h₂')
      (le_of_comap_eq_of_forall_exists_mul_eq φ H (hq := q₁.isPrime) h₂' h₁'))
  by_cases hne : (c ⁻¹' {z}).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hfx : ∀ x' : S, c.fromNormalization (c.toNormalization x') = c x' := fun x' => by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    have heq : c ⁻¹' {z} = c.toNormalization ⁻¹' {c.toNormalization x} := by
      ext x'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      exact ⟨fun h' => huniq _ _ ((hfx x').trans h') ((hfx x).trans hx),
        fun h' => by rw [← hfx, h', hfx, hx]⟩
    rw [heq]
    exact (c.toNormalization.isConnected_preimage_singleton _).isPreconnected
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

/-- **Connectedness of `Supp G` on the fibres.** Let `f : Y ⟶ Z` be proper and `G, H` effective
divisors on `Y` such that a function with divisor at least `G - H` has divisor at least `G`,
`f_* 𝒪_Y(H) ⟶ f_* 𝒪_G(H)` is an epimorphism and every section of `𝒪_Y(H)` over `f⁻¹ U` is
`f^♯ r` for a function `r` on `U`. Then `Supp G ∩ f⁻¹(z)` is connected for every point `z`:
it is the fibre over `z` of the restriction `c : G ⟶ Z` of `f`, and `𝒪_{Z,z} → (c_* 𝒪_G)_z`
is surjective. -/
private theorem isPreconnected_supp_inter_preimage_of_epi {Y Z : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {G H : Divisor Y} (hG : 0 ≤ G)
    (hH : 0 ≤ H) (hle : H - G ≤ H) (f : Y ⟶ Z) [IsProper f]
    (hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    [Epi ((Scheme.Modules.pushforward f).map (cokernel.π (Divisor.divisorialSheafInclusion hle)))]
    (hsurj : ∀ U : Z.Opens, Function.Surjective fun r : Γ(Z, U) =>
      unitSection hH (f ⁻¹ᵁ U) (f.app U r))
    (z : Z) : _root_.IsPreconnected ((G.supp : Set Y) ∩ f ⁻¹' {z}) := by
  set ι := (divisorialIdealSheaf hG).subschemeι
  have : QuasiCompact (ι ≫ f) := instQuasiCompactOfUniversallyClosed _
  have : QuasiSeparated (ι ≫ f) := IsSeparated.instQuasiSeparated _
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hconn := isPreconnected_preimage_singleton_of_forall_exists_mul_eq (ι ≫ f)
    ⟨U, hU⟩ hzU fun b => by
      obtain ⟨U', hU', hzU', r, hr⟩ := exists_presheaf_map_eq_app_of_epi hG hH hle f hann
        hsurj hzU b
      exact exists_mul_eq_app_of_presheaf_map_eq _ ⟨U, hU⟩ hU' hzU' b r hr
  have himg : ι '' ((ι ≫ f) ⁻¹' {z}) = (G.supp : Set Y) ∩ f ⁻¹' {z} := by
    rw [← coe_support_divisorialIdealSheaf hG, ← Scheme.IdealSheafData.range_subschemeι,
      ← Set.image_preimage_eq_range_inter]
    rfl
  rw [← himg]
  exact hconn.image _ ι.continuous.continuousOn

/-! ### Round-downs of divisors with coefficients `0` or at least `1` -/

section RoundDown

variable {Y : Scheme.{u}} {F : QDivisor Y}

/-- A `ℚ`-divisor whose nonzero coefficients are at least `1` has the support of its
round-down. -/
private theorem supp_roundDown_eq (hF : ∀ E, F.coeff E ≠ 0 → 1 ≤ F.coeff E) :
    F.roundDown.supp = F.supp := by
  ext x
  simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.coeff_roundDown]
  refine exists_congr fun E => and_congr_left fun _ =>
    ⟨fun hE h0 => hE (by rw [h0, Int.floor_zero]), fun hE => ?_⟩
  have := Int.le_floor.mpr (by exact_mod_cast hF E hE : ((1 : ℤ) : ℚ) ≤ F.coeff E)
  omega

/-- A `ℚ`-divisor whose nonzero coefficients are at least `1` has an effective round-down. -/
private theorem roundDown_nonneg (hF : ∀ E, F.coeff E ≠ 0 → 1 ≤ F.coeff E) :
    0 ≤ F.roundDown := fun E => by
  change (0 : ℤ) ≤ F.roundDown.coeff E
  rw [DivisorWithCoeffs.coeff_roundDown]
  by_cases hE : F.coeff E = 0
  · rw [hE, Int.floor_zero]
  · exact Int.floor_nonneg.mpr (zero_le_one.trans (hF E hE))

/-- A `ℚ`-divisor with coefficients `e(E)` where `e(E) > -1` and `0` elsewhere has an effective
round-up. -/
private theorem roundUp_nonneg {A : QDivisor Y} {e : Mori.PrimeDivisor Y → ℚ}
    (hA : ∀ E, A.coeff E = if -1 < e E then e E else 0) : 0 ≤ A.roundUp := fun E => by
  change (0 : ℤ) ≤ A.roundUp.coeff E
  rw [DivisorWithCoeffs.coeff_roundUp, hA]
  split_ifs with h1
  · have := Int.lt_ceil.mpr (show ((-1 : ℤ) : ℚ) < e E by push_cast; exact h1)
    omega
  · simp

/-- If `A` vanishes on the support of `F`, a function with divisor at least `⌊F⌋ - ⌈A⌉` has
divisor at least `⌊F⌋`. -/
private theorem isDivisorialSection_neg_roundDown_of_sub [IsLocallyNoetherian Y] [IsNormal Y]
    {A : QDivisor Y} (hAF : ∀ E, F.coeff E ≠ 0 → A.coeff E = 0) (W : Y.Opens) (a : Γ(Y, W))
    (ha : (A.roundUp - F.roundDown).IsDivisorialSection W
      ((toRationalFunctionsPresheaf Y).app (op W) a)) :
    (-F.roundDown).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
  intro E hE
  have hreg : (0 : Divisor Y).IsDivisorialSection W
      ((toRationalFunctionsPresheaf Y).app (op W) a) :=
    Divisor.isDivisorialSection_algebraMap le_rfl a
  by_cases hFE : F.coeff E = 0
  · have h0 : (-F.roundDown).coeff E = (0 : Divisor Y).coeff E := by
      rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown, hFE, Int.floor_zero,
        DivisorWithCoeffs.coeff_zero, neg_zero]
    rw [h0]
    exact hreg E hE
  · have h0 : (-F.roundDown).coeff E = (A.roundUp - F.roundDown).coeff E := by
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg,
        DivisorWithCoeffs.coeff_roundUp, hAF E hFE, Int.ceil_zero, zero_sub]
    rw [h0]
    exact ha E hE

end RoundDown

/-- A `ℚ`-Cartier `ℚ`-divisor `B` has a positive multiple `m₀ • -B` that is a Cartier divisor. -/
private theorem exists_isCartier_toQDivisor_eq_smul_neg {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {B : QDivisor X} (hB : B.IsQCartier) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ N : Divisor X, Divisor.toQDivisor N = (m₀ : ℚ) • -B ∧ N.IsCartier := by
  refine ⟨_, QDivisor.cartierIndex_pos hB, ?_⟩
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hB
  refine ⟨-D₀, ?_, hD₀c.neg⟩
  rw [map_neg, hD₀, smul_neg, natCast_zsmul, Nat.cast_smul_eq_nsmul]

/-- A component `E` of `⌈A⌉`, where `A = Σ_{e > -1} e(E) E`, has `e(E) > 0`: it is exceptional
over `X`, or the transform of a component `P` of `D` with `d_P = -e(E) < 0`, whose image in `Z`
has codimension at least two. -/
private theorem isExceptional_or_two_le_coheight_of_roundUp_ne_zero
    {k : Type} [Field k] [PerfectField k] {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)}
    {h : X ⟶ Z} {g : Y ⟶ X} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hhs : h ≫ sZ = sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {K : Divisor X} {D : QDivisor X}
    (hneg : ∀ P : Mori.PrimeDivisor X, D.coeff P < 0 → 2 ≤ Order.coheight (h P.genericPoint))
    [IsProper g] (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (e : Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E, IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E))
    {A : QDivisor Y} (hA : ∀ E, A.coeff E = if -1 < e E then e E else 0)
    (E : Mori.PrimeDivisor Y) (hE : A.roundUp E ≠ 0) :
    IsExceptionalPrimeDivisor (h ≫ sZ) g E ∨ 2 ≤ Order.coheight (h (g E.genericPoint)) := by
  have hpos : 0 < e E := by
    change A.roundUp.coeff E ≠ 0 at hE
    rw [DivisorWithCoeffs.coeff_roundUp, hA] at hE
    split_ifs at hE with h1
    · by_contra h2
      exact hE (le_antisymm (Int.ceil_le.mpr (by push_cast; linarith))
        (by have := Int.lt_ceil.mpr (show ((-1 : ℤ) : ℚ) < e E by push_cast; exact h1)
            omega))
    · exact absurd Int.ceil_zero hE
  rw [hhs]
  refine or_iff_not_imp_left.mpr fun hex => ?_
  set DE : ProperDivisorOver k sX := ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center, ← isExceptional_iff_two_le_coheight hn]
    exact fun h' => hex ⟨hY, hgb, inferInstance, h'⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
  push Not at hc
  obtain ⟨P, hv⟩ := hc
  have hvP : DE.valuation = P.divisorialValuation := by
    change DE.toDivisorOver.valuation = _
    rw [hv]
    ext φ
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  have hDP := (hvP ▸ he E).eq_neg_coeff
  rw [QDivisor.coeff_toRDivisor] at hDP
  rw [MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv]
  refine hneg P ?_
  have : (D.coeff P : ℝ) < 0 := by
    have : (0 : ℝ) < e E := by exact_mod_cast hpos
    linarith
  exact_mod_cast this

end

end MMP.Fold06.ThmFa17Connectedness

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori MMP.Fold06.ThmFa17Connectedness

/-- **Connectedness theorem (FA 17.4).** Let `h : X ⟶ Z` be a proper surjective morphism of
normal varieties over an algebraically closed field `k` of characteristic zero with connected
fibres, `K` a canonical divisor of `X` of dimension `n`, and `D` a `ℚ`-divisor on `X` with `K + D`
`ℚ`-Cartier, such that `codim_Z h(P) ≥ 2` for every prime divisor `P` with negative coefficient
in `D`, and with `-(K + D)` `h`-nef and `h`-big. Let `g : Y ⟶ X` be a log resolution of
`(X, (Supp D)_red)`, `e(E) = a(E, X, D)` the discrepancy of each prime divisor `E` of `Y`, and
`F` the `ℚ`-divisor with coefficient `-e(E)` where `e(E) ≤ -1` and `0` elsewhere. Then for every
closed point `z` of `Z`, `Supp F ∩ (g ≫ h)⁻¹(z) = Supp ⌊F⌋ ∩ (g ≫ h)⁻¹(z)`, and this set is
preconnected. -/
@[mmp "thm_fa17_connectedness"]
public theorem isPreconnected_supp_inter_preimage_of_isDiscrepancy
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {h : X ⟶ Z}
    {g : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hhs : h ≫ sZ = sX)
    [IsProper h] [Surjective h] (hfib : ∀ z : Z, _root_.IsConnected (h ⁻¹' {z}))
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X}
    (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (hneg : ∀ P : Mori.PrimeDivisor X, D.coeff P < 0 → 2 ≤ Order.coheight (h P.genericPoint))
    (hnef : (-(Divisor.toQDivisor K + D)).IsRelativelyNef sX h)
    (hbig : IsRelativelyBigOnGenericFiber h k sX sZ (-(Divisor.toQDivisor K + D)))
    (hg : MMP.Flips.IsLogResolution sX (Divisor.toRDivisor (MMP.Intersection.reducedDivisor D)) g)
    [IsProper g] (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (e : Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E, IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E))
    {F : QDivisor Y} (hF : ∀ E, F.coeff E = if e E ≤ -1 then -e E else 0)
    {z : Z} (_hz : IsClosed ({z} : Set Z)) :
    (F.supp : Set Y) ∩ (g ≫ h) ⁻¹' {z} = (F.roundDown.supp : Set Y) ∩ (g ≫ h) ⁻¹' {z} ∧
      IsPreconnected ((F.supp : Set Y) ∩ (g ≫ h) ⁻¹' {z}) := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant g := hgb.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  -- every coefficient of `F` is `0` or at least `1`, so `Supp F = Supp ⌊F⌋`
  have hF0 : ∀ E, F.coeff E ≠ 0 → e E ≤ -1 := fun E hE =>
    Classical.byContradiction fun h' => hE (by rw [hF, if_neg h'])
  have hF1 : ∀ E, F.coeff E ≠ 0 → 1 ≤ F.coeff E := fun E hE => by
    rw [hF, if_pos (hF0 E hE)]
    linarith [hF0 E hE]
  -- the discrepancies are the coefficients of `div(g^* ω) + m₀⁻¹ g^* N`, so finitely many are
  -- nonzero
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdivω : divisorOfForm ω = K := by
    ext Γ
    rw [coeff_divisorOfForm, hωK]
  obtain ⟨m₀, hm₀, N, hNM, hNc⟩ := exists_isCartier_toQDivisor_eq_smul_neg hKD
  have hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g N
  set Q : QDivisor Y := Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX g ω)) +
    (m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB) with hQ_def
  have hQ : ∀ E, Q.coeff E = e E := fun E => by
    rw [eq_ordForm_add_coeff_pullback_of_isDiscrepancy hX hY hgb hω0 hdivω hm₀ hNc hNM hNB E
      (he E), hQ_def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, smul_eq_mul]
  -- the divisor `A = Σ_{e > -1} e(E) E`
  let A : QDivisor Y := Finsupp.onFinset Q.support (fun E => if -1 < e E then e E else 0)
    (fun E hE => Finsupp.mem_support_iff.mpr fun h0 => hE (by
      rw [← DivisorWithCoeffs.coeff_apply, hQ] at h0
      rw [h0, ite_self]))
  have hA : ∀ E, A.coeff E = if -1 < e E then e E else 0 := fun E => rfl
  have hAF : ∀ E, F.coeff E ≠ 0 → A.coeff E = 0 := fun E hE => by
    rw [hA, if_neg (not_lt.mpr (hF0 E hE))]
  have hH : 0 ≤ A.roundUp := roundUp_nonneg hA
  have hG : 0 ≤ F.roundDown := roundDown_nonneg hF1
  have hle : A.roundUp - F.roundDown ≤ A.roundUp := sub_le_self _ hG
  have hepi := epi_pushforward_cokernel_π_divisorialSheafInclusion_roundUp_sub_roundDown hZ hX hhs
    hfib hK hKD hneg hnef hbig hg hY hgb e he hA hF hle
  have hcomp := isExceptional_or_two_le_coheight_of_roundUp_ne_zero hX hhs
    hK.topologicalKrullDim_eq hneg hY hgb e he hA
  -- `f_* 𝒪_Y(⌈A⌉) = 𝒪_Z`
  have hbij := bijective_structureSheafToDivisorialSheaf_app_comp sZ h g hZ (hhs ▸ hX)
    (by rw [hhs]; exact hY) hfib hgb A.roundUp hH hcomp
  rw [← supp_roundDown_eq hF1]
  exact ⟨rfl, isPreconnected_supp_inter_preimage_of_epi hG hH hle (g ≫ h)
    (isDivisorialSection_neg_roundDown_of_sub hAF)
    (fun U => (hbij U).2) z⟩

end MMP.Flips
