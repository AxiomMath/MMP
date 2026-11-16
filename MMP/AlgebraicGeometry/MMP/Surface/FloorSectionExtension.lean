module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.RestrictTensorPower
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.MMP.Surface.AdjointAmpleModel
import MMP.AlgebraicGeometry.Positivity.RelativeSemiampleGeneration
import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.Curves.Maps.Injectivity
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.PairClasses
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Divisor.ExceptionalEffectivePushforward
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyDictionary
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.ConnectednessPushforwardSurjective
import MMP.AlgebraicGeometry.Singularities.ConnectednessTheorem
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Modules.ProjectionFormulaInvertible
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Extending floor sections using the adjoint ample model of a projective lc surface

Let `(V, B)` be an lc pair, with `B ≥ 0` a `ℚ`-divisor, on a normal projective complex surface,
and `f : V ⟶ Z` a morphism to a projective variety with `D = K_V + B` `f`-nef and `f`-big. Fix the
adjoint ample model `h : V ⟶ V'`, `f' : V' ⟶ Z`, `k > 0` of
`MMP.Mori.IsLcPair.exists_isRelativelyAmple_of_isRelativelyNef_of_isRelativelyBig`, and let
`C = ⌊B⌋` with its reduced structure. Over an affine open `U ⊆ Z` put `V_U = f⁻¹U` and
`C_U = C ∩ V_U`. For `mD` Cartier and a section `t` of `𝒪_{C_U}(mD)`, and a finite set `P` of
closed points of `V_U` with `h(P) ∩ h(C_U) = ∅`, every sufficiently large `r` divisible by
`k / gcd(k, m)` admits a section `s` of `𝒪_{V_U}(rmD)` restricting to `t^r` on `C_U` and
nonvanishing at every point of `P`. If a nonempty finite family of sections `t_α` generates
`𝒪_{C_U}(mD)`, then every point of `V_U` has, for some `α`, such lifts of `t_α^r` nonvanishing
at that point.

## Main results

* `MMP.Mori.IsLcPair.exists_restrict_eq_pow_of_isRelativelyAmple`: the extension of powers of
  floor sections, with prescribed nonvanishing.

## Implementation notes

Everything on `V_U` is stated on the open subscheme `f ⁻¹ᵁ U`, with
`𝒪_{V_U}(E) = MMP.Mori.Divisor.restrictSheaf (f ⁻¹ᵁ U) E`; `C_U` is the open subscheme
`ι ⁻¹ᵁ f ⁻¹ᵁ U` of the reduced floor `ι : C ⟶ V`, mapped to `V_U` by `ι ∣_ f ⁻¹ᵁ U`, and
`𝒪_{C_U}(mD)` is the pull-back of `𝒪_{V_U}(mD)` along this closed immersion. A section of an
invertible sheaf is *nonzero at* `x` when it lies in `Stacks.Ample.nonvanishingLocus`, i.e. its
germ at `x` is not in `𝔪_x` times the stalk.

The restriction `s|_{C_U} = t^r` is written through local lifts of `t`: whenever `σ` is a section
of `𝒪(mD)` on an open `O ⊆ V_U` whose restriction to `C_U ∩ O` is `t`, the section `s|_O - σ^r` of
`𝒪(rmD)` restricts to zero on `C_U ∩ O`; here `σ^r` is the `r`-th power of `σ` as a rational
function. Since every section of the pull-back along a closed immersion is locally the
restriction of a section of `𝒪(mD)`, such lifts cover `C_U`, and the condition is equivalent to
`s|_{C_U} = t^r` under `𝒪_{C_U}(mD)^{⊗ r} ≅ 𝒪_{C_U}(rmD)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite MMP.Mori

namespace Proof_lem_mmp_surface_projective_floor_section_extension

/-- **A section and its pull-back vanish at the same points** (Stacks, Tag 0H78, over an open):
the germ of `i^* u` at `x'` lies in `𝔪_{x'} (i^* M)_{x'}` exactly when the germ of `u` at `i x'`
lies in `𝔪_{i x'} M_{i x'}`. -/
private theorem germ_unit_app_mem_maximalSmul_iff {X' X : Scheme.{0}} (i : X' ⟶ X)
    (M : X.Modules) {W : X.Opens} (u : Γ(M, W)) (x' : X') (hx' : x' ∈ i ⁻¹ᵁ W) :
    ((Scheme.Modules.pullback i).obj M).presheaf.germ (i ⁻¹ᵁ W) x' hx'
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W u) ∈
        Stacks.ModuleStalk.maximalSmul ((Scheme.Modules.pullback i).obj M) x' ↔
      M.presheaf.germ W (i.base x') hx' u ∈ Stacks.ModuleStalk.maximalSmul M (i.base x') := by
  refine Iff.symm ?_
  refine Iff.trans (Stacks.NonvanishingPullback.mem_maximalSmul_iff M (i.base x') _) ?_
  refine Iff.trans ?_
    (Stacks.NonvanishingPullback.mem_maximalSmul_iff ((Scheme.Modules.pullback i).obj M) x' _).symm
  refine Iff.trans
    (Stacks.NonvanishingPullback.mem_maximalIdeal_smul_iff_one_tmul
      (instAlg := Stacks.PullbackTensorIso.commStalkAlgebra i.toLRSHom.toShHom x')
      (instLoc := Stacks.NonvanishingPullback.isLocalHom_commStalkRingMap i x')
      (instMod := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val
        (i.base x'))
      ((M.presheaf.germ W (i.base x') hx').hom u)) ?_
  refine Iff.trans
    (Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv _
      (Stacks.PullbackTensorIso.pullbackStalkEquiv i.toLRSHom.toShHom x' M) _) ?_
  exact Iff.of_eq (congrArg (fun z => z ∈
    IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
      X'.toRingedSpace x') • ⊤)
    (Stacks.PullbackTensorIso.pullbackStalkEquiv_one_tmul i.toLRSHom.toShHom x' M W hx' u))

/-- Scalar multiplication on `𝒪(D)|_W`, read on rational functions. -/
private theorem restrictSection_smul_apply {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (W : X.Opens) {D : Divisor X} {V : W.toScheme.Opens} (c : Γ(W.toScheme, V))
    (φ : Γ(Divisor.restrictSheaf W D, V))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W.ι ''ᵁ V}) :
    (Divisor.restrictSection W (c • φ)).1 Z =
      X.presheaf.germ (W.ι ''ᵁ V) _ Z.2 c * (Divisor.restrictSection W φ).1 Z := by
  have hsm := Scheme.Modules.smul_restrictAppIso_hom_apply W.ι D.divisorialSheaf V c φ
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv] at hsm
  exact congrArg (fun s : Γ(D.divisorialSheaf, W.ι ''ᵁ V) =>
    (s : D.divisorialSubmodule _).1 Z) hsm

/-- The section `ψ⁻¹` of `𝒪(D)|_W` over an open `V` of `W` inside `U₀`, for a local equation `ψ`
of `D` on `U₀`. -/
private noncomputable def restrictInvSection {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (W : X.Opens) {D : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀) :
    Γ(Divisor.restrictSheaf W D, V) :=
  (hψ.mono hV).invSection

private theorem restrictSection_restrictInvSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (W : X.Opens) {D : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W.ι ''ᵁ V}) :
    (Divisor.restrictSection W (restrictInvSection W hψ hV)).1 Z =
      ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 := rfl

/-- If `ψ` is a local equation of `D` on `U₀`, then over every open `V` of `W` inside `U₀` the
section `ψ⁻¹` freely generates `𝒪(D)|_W`. -/
private theorem bijective_smul_restrictInvSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (W : X.Opens) {D : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀) :
    Function.Bijective fun c : Γ(W.toScheme, V) => c • restrictInvSection W hψ hV := by
  refine ⟨fun c c' h => ?_, fun φ => ?_⟩
  · apply toRationalFunctionsPresheaf_app_injective (W.ι ''ᵁ V)
    funext Z
    have := congrFun (congrArg (fun φ => (Divisor.restrictSection W φ).1) h) Z
    rw [restrictSection_smul_apply, restrictSection_smul_apply,
      restrictSection_restrictInvSection] at this
    have hu := (Pi.isUnit_iff.mp (ψ⁻¹).isUnit) Z.1
    exact hu.mul_left_injective this
  · have h0 : (0 : Divisor X).IsDivisorialSection (W.ι ''ᵁ V)
        (fun Z => (Divisor.restrictSection W φ).1 Z * (ψ : RationalFunctions X) Z.1) := by
      intro E hE
      have h1 := (Divisor.restrictSection W φ).2 E hE
      have h2 : E.OrdGE (D.coeff E) ((ψ : RationalFunctions X) E.component) :=
        Or.inr (by rw [PrimeDivisor.valuation_component,
          hψ E (hE.mono (Set.inter_subset_inter_right _ hV))])
      refine (h1.mul h2).mono (le_of_eq ?_)
      rw [DivisorWithCoeffs.coeff_zero]
      ring
    obtain ⟨c, hc⟩ := h0.exists_eq
    let c' : Γ(W.toScheme, V) := c
    refine ⟨c', Divisor.restrictSection_inj W (funext fun Z => ?_)⟩
    change (Divisor.restrictSection W (c' • restrictInvSection W hψ hV)).1 Z = _
    rw [restrictSection_smul_apply, restrictSection_restrictInvSection]
    have := congrFun hc Z
    rw [toRationalFunctionsPresheaf_app_apply] at this
    rw [this, mul_assoc, ← Pi.mul_apply (f := (ψ : RationalFunctions X)), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Pi.one_apply, mul_one]

/-- `ψ⁻¹` freely generates `𝒪(D)|_W` over every open inside the chart of `ψ`. -/
private theorem isLocalGenerator_restrictInvSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (W : X.Opens) {D : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀) :
    IsLocalGenerator (Divisor.restrictSheaf W D) V (restrictInvSection W hψ hV) := fun V' hV' => by
  have hres : (Divisor.restrictSheaf W D).presheaf.map (homOfLE hV').op
      (restrictInvSection W hψ hV) =
      restrictInvSection W hψ ((W.ι.image_mono hV').trans hV) :=
    Divisor.restrictSection_inj W rfl
  rw [hres]
  exact bijective_smul_restrictInvSection W hψ _

/-- `ψ ^ r` is a local equation of `r D` where `ψ` is one of `D`. -/
private theorem isLocalEquation_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {E : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ} (hψ : E.IsLocalEquation U₀ ψ)
    (r : ℕ) : (r • E).IsLocalEquation U₀ (ψ ^ (r : ℤ)) := fun E' hE' => by
  rw [DivisorWithCoeffs.coeff_smul, hψ E' hE', PrimeDivisor.ord_zpow, nsmul_eq_mul, smul_eq_mul]

/-- `(e ψ⁻¹)^r = e^r ψ^{-r}`, read on rational functions. -/
private theorem restrictSection_smul_pow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (W : X.Opens) {E : Divisor X} {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : E.IsLocalEquation U₀ ψ) (r : ℕ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀)
    (e : Γ(W.toScheme, V)) :
    (Divisor.restrictSection W (e ^ r • restrictInvSection W (isLocalEquation_zpow hψ r) hV)).1 =
      (Divisor.restrictSection W (e • restrictInvSection W hψ hV)).1 ^ r := by
  funext Z
  rw [restrictSection_smul_apply, restrictSection_restrictInvSection]
  change _ = ((Divisor.restrictSection W (e • restrictInvSection W hψ hV)).1 Z) ^ r
  rw [restrictSection_smul_apply, restrictSection_restrictInvSection, mul_pow]
  congr 1
  exact map_pow (X.presheaf.germ _ _ _).hom e r

/-- The section `ψ⁻¹` of `𝒪(D)|_W` vanishes nowhere on its open. -/
private theorem germ_restrictInvSection_notMem_maximalSmul {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (W : X.Opens) {D : Divisor X}
    (hD : D.IsCartier) {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀)
    (x : W.toScheme) (hx : x ∈ V) :
    (Divisor.restrictSheaf W D).presheaf.germ V x hx (restrictInvSection W hψ hV) ∉
      Stacks.ModuleStalk.maximalSmul (Divisor.restrictSheaf W D) x :=
  have := Divisor.isInvertibleModule_restrictSheaf W hD
  Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul _ _
    (isLocalGenerator_restrictInvSection W hψ hV) x hx

/-- **Nonvanishing of `c • ψ⁻¹`.** A section `c ψ⁻¹` of `𝒪(D)|_W` does not vanish at `x` exactly
when `c` is a unit at `x`. -/
private theorem germ_smul_restrictInvSection_notMem_maximalSmul_iff {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (W : X.Opens)
    {D : Divisor X} (hD : D.IsCartier) {U₀ : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation U₀ ψ) {V : W.toScheme.Opens} (hV : W.ι ''ᵁ V ≤ U₀)
    (c : Γ(W.toScheme, V)) (x : W.toScheme) (hx : x ∈ V) :
    (Divisor.restrictSheaf W D).presheaf.germ V x hx (c • restrictInvSection W hψ hV) ∉
        Stacks.ModuleStalk.maximalSmul (Divisor.restrictSheaf W D) x ↔
      IsUnit (W.toScheme.presheaf.germ V x hx c) := by
  rw [Stacks.ModuleStalk.germ_smul, Stacks.ModuleStalk.smul_mem_maximalSmul_iff, not_or, not_not]
  exact and_iff_left (germ_restrictInvSection_notMem_maximalSmul W hD hψ hV x hx)

/-- The unit of `i^* ⊣ i_*` is semilinear along `i^♯`. -/
private theorem unit_app_smul {X Y : Scheme.{0}} (i : X ⟶ Y) (F : Y.Modules) {O : Y.Opens}
    (a : Γ(Y, O)) (σ : Γ(F, O)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app O (a • σ) =
      (show Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ O) from i.app O a •
        (show Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ O) from
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app O σ)) := by
  rw [Scheme.Modules.Hom.app_smul]
  rfl

/-- Restriction along `U ≤ U` is the identity. -/
private theorem map_homOfLE_self_apply {X : Scheme.{0}} (M : X.Modules) {U : X.Opens}
    (hU : U ≤ U) (x : Γ(M, U)) : M.presheaf.map (homOfLE hU).op x = x := by
  rw [show homOfLE hU = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]; rfl

/-- A local generator of `ℱ` on `V` is a basis of `Γ(ℱ, V)`. -/
private theorem IsLocalGenerator.bijective_self {X : Scheme.{0}} {ℱ : X.Modules} {V : X.Opens}
    {g : Γ(ℱ, V)} (hg : IsLocalGenerator ℱ V g) : Function.Bijective fun r : Γ(X, V) => r • g := by
  have := hg V le_rfl
  rwa [map_homOfLE_self_apply] at this

/-- Over an affine open `O ⊆ W` inside the chart of a local equation `ψ` of `E`, every section of
`ι^* 𝒪(E)` on `C ∩ O` is the restriction of a section `a ψ⁻¹`. -/
private theorem exists_unit_app_smul_restrictInvSection_eq {V C : Scheme.{0}}
    [IsLocallyNoetherian V] [IsNormal V] (ι : C ⟶ V) [IsClosedImmersion ι] (W : V.Opens)
    {E : Divisor V} {U₀ : V.Opens} {ψ : (RationalFunctions V)ˣ} (hψ : E.IsLocalEquation U₀ ψ)
    [Stacks.Ample.IsInvertibleModule W.toScheme (Divisor.restrictSheaf W E)]
    {O : W.toScheme.Opens} (hOaff : IsAffineOpen O) (hV : W.ι ''ᵁ O ≤ U₀)
    (u : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), (ι ∣_ W) ⁻¹ᵁ O)) :
    ∃ a : Γ(W.toScheme, O), ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W E)).app O (a • restrictInvSection W hψ hV) = u := by
  obtain ⟨b, hb⟩ := (IsLocalGenerator.bijective_self (isLocalGenerator_pullback_unit (ι ∣_ W) _
    (isLocalGenerator_restrictInvSection W hψ hV))).2 u
  obtain ⟨a, rfl⟩ := (ι ∣_ W).app_surjective O hOaff b
  exact ⟨a, by rw [unit_app_smul]; exact hb⟩

section Reduction

variable {V C : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V] (ι : C ⟶ V) (W : V.Opens)

/-- `s|_{C ∩ W} = t ^ r`, read through local lifts of `t`: whenever `σ` is a section of `𝒪(E)` on
an open `O ⊆ W` restricting to `t` on `C ∩ O`, the section `s|_O - σ ^ r` of `𝒪(rE)` restricts to
zero on `C ∩ O`. -/
private def LiftsPow {E : Divisor V}
    (t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), ⊤)) (r : ℕ)
    (s : Γ(Divisor.restrictSheaf W (r • E), ⊤)) : Prop :=
  ∀ (O : W.toScheme.Opens) (σ : Γ(Divisor.restrictSheaf W E, O)),
    (((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W E)).app O σ :
          Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), (ι ∣_ W) ⁻¹ᵁ O)) =
      ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E)).presheaf.map
        (homOfLE le_top).op t →
    ∀ τ : Γ(Divisor.restrictSheaf W (r • E), O),
      (Divisor.restrictSection W τ).1 = (Divisor.restrictSection W σ).1 ^ r →
      ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
          (Divisor.restrictSheaf W (r • E))).app O
        ((Divisor.restrictSheaf W (r • E)).presheaf.map (homOfLE le_top).op s - τ) = 0

/-- If `s|_C = t ^ r` with `r > 0` and `t` does not vanish at `c`, then `s` does not vanish at
`ι c`. -/
private theorem mem_nonvanishingLocus_of_liftsPow [CompactSpace V] [IsClosedImmersion ι]
    {E : Divisor V} (hE : E.IsCartier)
    {t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), ⊤)} {r : ℕ}
    {s : Γ(Divisor.restrictSheaf W (r • E), ⊤)} (hs : LiftsPow ι W t r s)
    {c : (ι ⁻¹ᵁ W).toScheme} (hc : c ∈ Stacks.Ample.nonvanishingLocus _ t) :
    (ι ∣_ W).base c ∈ Stacks.Ample.nonvanishingLocus _ s := by
  let j := ι ∣_ W
  let x := j.base c
  have := Divisor.isInvertibleModule_restrictSheaf W hE
  obtain ⟨U₀, hxU₀, ψ, hψ⟩ := hE (W.ι.base x)
  obtain ⟨O, hOaff, hxO, hOle⟩ := exists_isAffineOpen_mem_and_subset
    (U := W.ι ⁻¹ᵁ U₀) (show x ∈ W.ι ⁻¹ᵁ U₀ from hxU₀)
  have hV : W.ι ''ᵁ O ≤ U₀ := (W.ι.image_mono hOle).trans (Scheme.Hom.image_preimage_le W.ι U₀)
  have hcO : c ∈ j ⁻¹ᵁ O := hxO
  -- near `x`, `t = a ψ⁻¹` with `a` a unit at `x`, and `t ^ r = a ^ r ψ⁻ʳ` does not vanish at `x`
  obtain ⟨a, ha⟩ := exists_unit_app_smul_restrictInvSection_eq ι W hψ hOaff hV
    (((Scheme.Modules.pullback j).obj _).presheaf.map (homOfLE le_top).op t)
  have hau : IsUnit (W.toScheme.presheaf.germ O x hxO a) := by
    rw [← germ_smul_restrictInvSection_notMem_maximalSmul_iff W hE hψ hV a x hxO,
      ← germ_unit_app_mem_maximalSmul_iff j _ _ c hcO, ha, TopCat.Presheaf.germ_res_apply]
    exact hc
  set τ : Γ(Divisor.restrictSheaf W (r • E), O) :=
    a ^ r • restrictInvSection W (isLocalEquation_zpow hψ r) hV
  have hτx : (Divisor.restrictSheaf W (r • E)).presheaf.germ O x hxO τ ∉
      Stacks.ModuleStalk.maximalSmul (Divisor.restrictSheaf W (r • E)) x :=
    (germ_smul_restrictInvSection_notMem_maximalSmul_iff W (hE.nsmul r) _ hV (a ^ r) x
      hxO).2 (by rw [map_pow]; exact hau.pow r)
  have hzero := hs O _ ha τ (restrictSection_smul_pow W hψ r hV a)
  have hdiff : (Divisor.restrictSheaf W (r • E)).presheaf.germ O x hxO
      ((Divisor.restrictSheaf W (r • E)).presheaf.map (homOfLE le_top).op s - τ) ∈
      Stacks.ModuleStalk.maximalSmul (Divisor.restrictSheaf W (r • E)) x := by
    rw [← germ_unit_app_mem_maximalSmul_iff j _ _ c hcO, hzero]
    have h0 := map_zero (((Scheme.Modules.pullback j).obj
      (Divisor.restrictSheaf W (r • E))).presheaf.germ (j ⁻¹ᵁ O) c hcO).hom
    exact h0 ▸ Submodule.zero_mem _
  rw [Stacks.Ample.mem_nonvanishingLocus_iff]
  intro hsx
  apply hτx
  have hsplit : (Divisor.restrictSheaf W (r • E)).presheaf.germ O x hxO τ =
      (Divisor.restrictSheaf W (r • E)).presheaf.germ O x hxO
          ((Divisor.restrictSheaf W (r • E)).presheaf.map (homOfLE le_top).op s) -
        (Divisor.restrictSheaf W (r • E)).presheaf.germ O x hxO
          ((Divisor.restrictSheaf W (r • E)).presheaf.map (homOfLE le_top).op s - τ) := by
    rw [map_sub]; abel
  rw [hsplit, TopCat.Presheaf.germ_res_apply]
  exact Submodule.sub_mem _ hsx hdiff

end Reduction

/-- If `E = m D` and `M = k D` as `ℚ`-divisors and `k / gcd(k, m)` divides `r`, then `rE` is the
integral multiple `(rm / k) M`. -/
private theorem exists_nsmul_eq_nsmul_of_dvd {X : Scheme.{0}} {E M : Divisor X} {D : QDivisor X}
    {k m r : ℕ} (hk : 0 < k) (hE : Divisor.toQDivisor E = (m : ℚ) • D)
    (hM : Divisor.toQDivisor M = (k : ℚ) • D) (hr : k / k.gcd m ∣ r) :
    ∃ j : ℕ, r • E = j • M ∧ r * m = j * k := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨k', hk'⟩ := Nat.gcd_dvd_left k m
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right k m
  have hg : 0 < k.gcd m := Nat.gcd_pos_of_pos_left m hk
  have hkk : k / k.gcd m = k' :=
    Nat.div_eq_of_eq_mul_left hg (by rw [mul_comm]; exact hk')
  have hq : ((k' * a : ℕ) : ℚ) * (m : ℚ) = ((a * m' : ℕ) : ℚ) * (k : ℚ) := by
    have h1 : (k : ℚ) = (k.gcd m : ℚ) * k' := by exact_mod_cast hk'
    have h2 : (m : ℚ) = (k.gcd m : ℚ) * m' := by exact_mod_cast hm'
    rw [h1, h2]; push_cast; ring
  rw [hkk]
  refine ⟨a * m', Divisor.toQDivisor_injective ?_, by exact_mod_cast hq⟩
  rw [map_nsmul, map_nsmul, hE, hM, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, smul_smul, hq]

/-- If no generic point of `X` maps into `Supp L`, the same holds for every multiple of `L`. -/
private theorem notMem_supp_zsmul {X Y : Scheme.{0}} (h : X ⟶ Y) {L : Divisor Y}
    (hM : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ L.supp) (n : ℤ)
    (Z : irreducibleComponents X) : h (componentGenericPoint X Z) ∉ (n • L).supp := fun hZ =>
  hM Z (by
    obtain ⟨E', hE', hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    rw [DivisorWithCoeffs.coeff_smul] at hE'
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨E', fun h0 => hE' (by rw [h0, smul_zero]), hxE⟩)

/-- If `L` pulls back to `M` and `r E = j M`, then `j L` pulls back to `r E`. -/
private theorem isPullback_nsmul_of_eq {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {h : X ⟶ Y} {L : Divisor Y} (hL : L.IsCartier)
    {hM : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ L.supp} {M : Divisor X}
    (hpb : L.IsPullback h hM M) {E : Divisor X} {r j : ℕ} (hrj : r • E = j • M) :
    (j • L).IsPullback h (fun Z => by rw [← natCast_zsmul]; exact notMem_supp_zsmul h hM j Z)
      (r • E) := by
  rw [hrj]
  have h1 := hpb.zsmul hL (j : ℤ) (notMem_supp_zsmul h hM j)
  rw [natCast_zsmul M j] at h1
  exact Divisor.IsPullback.of_eq (natCast_zsmul L j) h1

/-- In a Jacobson space, a point outside a closed set specializes to a closed point outside it. -/
private theorem exists_isClosed_singleton_specializes_notMem {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {S : Set X} (hS : IsClosed S) {x : X} (hx : x ∉ S) :
    ∃ x' : X, IsClosed ({x'} : Set X) ∧ x ⤳ x' ∧ x' ∉ S := by
  obtain ⟨x', ⟨hx'c, hx'S⟩, hx'⟩ := nonempty_inter_closedPoints
    (Z := closure {x} ∩ Sᶜ) ⟨x, subset_closure rfl, hx⟩
    (isClosed_closure.isLocallyClosed.inter hS.isOpen_compl.isLocallyClosed)
  exact ⟨x', hx', specializes_iff_mem_closure.mpr hx'c, hx'S⟩

/-- The image of a local equation `ψ` of `B` under `𝒪_{Y,η} ⟶ 𝒪_{Y,h(η_Z)} ⟶ 𝒪_{X,η_Z}` is the
pull-back `h^*_Z ψ` of `MMP.Mori.pullbackComponent`. -/
private theorem stalkMap_stalkSpecializes_eq_pullbackComponent {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] (h : X ⟶ Y) {B : Divisor Y}
    (hB : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ B.supp)
    {U : Y.Opens} {ψ : (RationalFunctions Y)ˣ} (hψ : B.IsLocalEquation U ψ)
    (Z : irreducibleComponents X) (hZ : h (componentGenericPoint X Z) ∈ U)
    (ZY : irreducibleComponents Y) (hW : h (componentGenericPoint X Z) ∈ ZY.1)
    (hsp : h.base (componentGenericPoint X Z) ⤳ componentGenericPoint Y ZY) :
    (Y.presheaf.stalkSpecializes hsp ≫ h.stalkMap _).hom ((ψ : RationalFunctions Y) ZY) =
      ((pullbackComponent h hB hψ Z hZ : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Z)) := by
  let a₀ : (Y.presheaf.stalk (h (componentGenericPoint X Z)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp).hom.toMonoidHom
      (Units.map (RationalFunctions.component Y ZY).toMonoidHom ψ)
  have ha : (stalkToRationalFunctions Y hW).hom a₀ = (ψ : RationalFunctions Y) ZY := by
    change (Y.presheaf.stalkSpecializes hsp ≫ stalkToRationalFunctions Y hW).hom
      ((ψ : RationalFunctions Y) ZY) = _
    rw [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
    rw [show (((isGenericPoint_componentGenericPoint Y ZY).specializes hW).trans hsp) =
      specializes_refl _ from rfl, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [pullbackComponent_eq hB hψ hZ hW a₀ ha]
  rfl

/-- The image in `X` of `(h ∣_ W)⁻¹ V₁` lies over every open of `Y` containing `W.ι '' V₁`. -/
private theorem image_preimage_morphismRestrict_le {X Y : Scheme.{0}} (h : X ⟶ Y) (W : Y.Opens)
    {U : Y.Opens}
    {V₁ : W.toScheme.Opens} (hV : W.ι ''ᵁ V₁ ≤ U) :
    (h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V₁) ≤ h ⁻¹ᵁ U := by
  rw [image_morphismRestrict_preimage]
  exact h.preimage_mono hV

/-- For a dominant morphism of integral schemes, the generic point of the source maps to a point
specializing to the generic point of the target. -/
private theorem specializes_componentGenericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (h : X ⟶ Y)
    [IsDominant h] (Z : irreducibleComponents X) (Z' : irreducibleComponents Y) :
    h.base (componentGenericPoint X Z) ⤳ componentGenericPoint Y Z' := by
  have hmemX : ∀ x : X, x ∈ Z.1 := fun x => by
    have h1 : Z.1 ∈ ({Set.univ} : Set (Set X)) := irreducibleComponents_eq_singleton (X := X) ▸ Z.2
    rw [Set.mem_singleton_iff.mp h1]; trivial
  rw [specializes_iff_mem_closure]
  have hr : Set.range h.base ⊆ closure {h.base (componentGenericPoint X Z)} := by
    rintro _ ⟨x, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((isGenericPoint_componentGenericPoint X Z).specializes (hmemX x)).map h.continuous)
  have := closure_minimal hr isClosed_closure
  rw [h.denseRange.closure_range] at this
  exact this (Set.mem_univ _)

section PullbackSections

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- `s` is the pull-back `h^* σ` of a section `σ` of `𝒪_Y(D')` over `W`: at the generic point of
every component of `X` meeting `h⁻¹ W`, the rational function `s` is the image of `σ` under the
map of local rings of `h`. -/
private def IsPullbackSection (h : X ⟶ Y) (W : Y.Opens) {D : Divisor X} {D' : Divisor Y}
    (σ : Γ(Divisor.restrictSheaf W D', ⊤)) (s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, ⊤)) :
    Prop :=
  ∀ (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ (h ⁻¹ᵁ W).ι ''ᵁ ⊤)
    (Z' : irreducibleComponents Y) (hZ' : componentGenericPoint Y Z' ∈ W.ι ''ᵁ ⊤)
    (hsp : h.base (componentGenericPoint X Z) ⤳ componentGenericPoint Y Z'),
    (Divisor.restrictSection (h ⁻¹ᵁ W) s).1 ⟨Z, hZ⟩ =
      (h.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp).hom
        ((Divisor.restrictSection W σ).1 ⟨Z', hZ'⟩))

/-- `s` is the pull-back `h^* σ` of a section `σ` of `𝒪_Y(D')` over an open `V₁` of `W`, read at
the generic points as in `IsPullbackSection`. -/
private def IsPullbackSectionOn (h : X ⟶ Y) (W : Y.Opens) (V₁ : W.toScheme.Opens)
    {D : Divisor X} {D' : Divisor Y} (σ : Γ(Divisor.restrictSheaf W D', V₁))
    (s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, (h ∣_ W) ⁻¹ᵁ V₁)) : Prop :=
  ∀ (Z : irreducibleComponents X)
    (hZ : componentGenericPoint X Z ∈ (h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V₁))
    (Z' : irreducibleComponents Y) (hZ' : componentGenericPoint Y Z' ∈ W.ι ''ᵁ V₁)
    (hsp : h.base (componentGenericPoint X Z) ⤳ componentGenericPoint Y Z'),
    (Divisor.restrictSection (h ⁻¹ᵁ W) s).1 ⟨Z, hZ⟩ =
      (h.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp).hom
        ((Divisor.restrictSection W σ).1 ⟨Z', hZ'⟩))

/-- **The local formula `h^*(a ψ⁻¹) = (h^♯ a) (h^* ψ)⁻¹`.** -/
private theorem isPullbackSectionOn_smul_restrictInvSection [IsIntegral X] [IsIntegral Y]
    (h : X ⟶ Y) {D' : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ D'.supp}
    {D : Divisor X} (hpb : D'.IsPullback h hB D) (W : Y.Opens) {U : Y.Opens}
    {ψ : (RationalFunctions Y)ˣ} (hψ : D'.IsLocalEquation U ψ) {V₁ : W.toScheme.Opens}
    (hV : W.ι ''ᵁ V₁ ≤ U) (a : Γ(W.toScheme, V₁)) :
    IsPullbackSectionOn h W V₁ (a • restrictInvSection W hψ hV)
      ((h ∣_ W).app V₁ a • restrictInvSection (h ⁻¹ᵁ W) (hpb.isLocalEquation hψ)
        (image_preimage_morphismRestrict_le h W hV)) := by
  intro Z hZ Z' hZ' hsp
  have hZ'' : h (componentGenericPoint X Z) ∈ W.ι ''ᵁ V₁ := by
    rw [image_morphismRestrict_preimage] at hZ
    exact hZ
  have hW' : h (componentGenericPoint X Z) ∈ Z'.1 := by
    have h1 : Z'.1 ∈ ({Set.univ} : Set (Set Y)) :=
      irreducibleComponents_eq_singleton (X := Y) ▸ Z'.2
    rw [Set.mem_singleton_iff.mp h1]; trivial
  rw [restrictSection_smul_apply, restrictSection_restrictInvSection, restrictSection_smul_apply,
    restrictSection_restrictInvSection, map_mul, map_mul]
  congr 1
  · let a' : Γ(Y, W.ι ''ᵁ V₁) := a
    have k1 : (Y.presheaf.stalkSpecializes hsp).hom
        ((Y.presheaf.germ (W.ι ''ᵁ V₁) _ hZ').hom a') =
        (Y.presheaf.germ (W.ι ''ᵁ V₁) _ hZ'').hom a' :=
      TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hZ' hsp a'
    have k2 : (h.stalkMap _).hom ((Y.presheaf.germ (W.ι ''ᵁ V₁) _ hZ'').hom a') =
        (X.presheaf.germ (h ⁻¹ᵁ (W.ι ''ᵁ V₁)) _ hZ'').hom ((h.app (W.ι ''ᵁ V₁)).hom a') :=
      Scheme.Hom.germ_stalkMap_apply h (W.ι ''ᵁ V₁) _ hZ'' a'
    have k3 : (X.presheaf.germ ((h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V₁)) _ hZ).hom
        (((h ∣_ W).app V₁).hom a) =
        (X.presheaf.germ (h ⁻¹ᵁ (W.ι ''ᵁ V₁)) _ hZ'').hom ((h.app (W.ι ''ᵁ V₁)).hom a') := by
      rw [morphismRestrict_app]
      exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ ((h.app (W.ι ''ᵁ V₁)).hom a')
    exact (k3.trans k2.symm).trans (congrArg (h.stalkMap _).hom k1.symm)
  · have h1 : Units.map (Y.presheaf.stalkSpecializes hsp ≫ h.stalkMap _).hom.toMonoidHom
        (Units.map (RationalFunctions.component Y Z').toMonoidHom ψ) =
        Units.map (RationalFunctions.component X Z).toMonoidHom
          (pullbackLocalEquation h hB hψ) := by
      rw [pullbackLocalEquation_apply h hB hψ Z (hV hZ'')]
      exact Units.ext (stalkMap_stalkSpecializes_eq_pullbackComponent h hB hψ Z (hV hZ'') Z'
        hW' hsp)
    have h2 := congrArg (fun u : (X.presheaf.stalk (componentGenericPoint X Z))ˣ =>
      ((u⁻¹ : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Z))) h1
    simp only [← map_inv, Units.coe_map] at h2
    exact h2.symm

/-- **Pull-back of sections of a Cartier divisorial sheaf.** If `D = h^* D'` with `D'` Cartier,
every section `σ` of `𝒪_Y(D')` over `W` pulls back to a section `h^* σ` of `𝒪_X(D)` over `h⁻¹ W`,
which vanishes at `x` exactly when `σ` vanishes at `h x`. -/
private theorem exists_isPullbackSection [IsIntegral X] [CompactSpace X] [IsIntegral Y]
    [CompactSpace Y] (h : X ⟶ Y) [IsDominant h] {D' : Divisor Y} (hD' : D'.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, h (componentGenericPoint X Z) ∉ D'.supp}
    {D : Divisor X} (hpb : D'.IsPullback h hB D) (W : Y.Opens)
    (σ : Γ(Divisor.restrictSheaf W D', ⊤)) :
    ∃ s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, ⊤), IsPullbackSection h W σ s ∧
      ∀ x : (h ⁻¹ᵁ W).toScheme,
        x ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (h ⁻¹ᵁ W) D) s ↔
          (h ∣_ W).base x ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf W D') σ := by
  classical
  have hsubY : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  let ZY : irreducibleComponents Y := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
  have hgenY : ∀ y : Y, componentGenericPoint Y ZY ⤳ y := fun y =>
    (isGenericPoint_componentGenericPoint Y ZY).specializes (Set.mem_univ y)
  have hsp := fun Z => specializes_componentGenericPoint h Z ZY
  have hZY : ∀ (Z : irreducibleComponents X),
      componentGenericPoint X Z ∈ (h ⁻¹ᵁ W).ι ''ᵁ ⊤ → componentGenericPoint Y ZY ∈ W.ι ''ᵁ ⊤ := by
    intro Z hZ
    rw [Scheme.Opens.ι_image_top] at hZ ⊢
    exact (hgenY _).mem_open W.isOpen hZ
  let κ : ∀ Z : irreducibleComponents X, Y.presheaf.stalk (componentGenericPoint Y ZY) →+*
      X.presheaf.stalk (componentGenericPoint X Z) := fun Z =>
    (Y.presheaf.stalkSpecializes (hsp Z) ≫ h.stalkMap _).hom
  let sfun : ToType ((rationalFunctionsPresheaf X).obj (op ((h ⁻¹ᵁ W).ι ''ᵁ ⊤))) := fun Z =>
    κ Z.1 ((Divisor.restrictSection W σ).1 ⟨ZY, hZY Z.1 Z.2⟩)
  -- the local formula `h^*(a ψ⁻¹) = (h^♯ a) (h^*ψ)⁻¹`
  have hloc : ∀ (U : Y.Opens) (ψ : (RationalFunctions Y)ˣ) (hψ : D'.IsLocalEquation U ψ)
      (V : W.toScheme.Opens) (hV : W.ι ''ᵁ V ≤ U) (a : Γ(W.toScheme, V)),
      (Divisor.restrictSheaf W D').presheaf.map (homOfLE le_top).op σ =
        a • restrictInvSection W hψ hV →
      ∀ (Z : irreducibleComponents X)
        (hZ : componentGenericPoint X Z ∈ (h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V)),
        sfun ⟨Z, (h ⁻¹ᵁ W).ι.image_mono le_top hZ⟩ =
          X.presheaf.germ _ _ hZ ((h ∣_ W).app V a) *
            (((pullbackLocalEquation h hB hψ)⁻¹ : (RationalFunctions X)ˣ) :
              RationalFunctions X) Z := by
    intro U ψ hψ V hV a ha Z hZ
    have hZ' : h (componentGenericPoint X Z) ∈ W.ι ''ᵁ V := by
      rw [image_morphismRestrict_preimage] at hZ
      exact hZ
    have key := isPullbackSectionOn_smul_restrictInvSection h hpb W hψ hV a Z hZ ZY
      ((hgenY _).mem_open (W.ι ''ᵁ V).isOpen hZ') (hsp Z)
    rw [restrictSection_smul_apply, restrictSection_restrictInvSection] at key
    refine Eq.trans ?_ key.symm
    rw [← ha]
    rfl
  -- charts
  have hchart : ∀ x : (h ⁻¹ᵁ W).toScheme, ∃ (U : Y.Opens) (ψ : (RationalFunctions Y)ˣ)
      (hψ : D'.IsLocalEquation U ψ) (V : W.toScheme.Opens) (hV : W.ι ''ᵁ V ≤ U)
      (a : Γ(W.toScheme, V)), (h ∣_ W).base x ∈ V ∧
        (Divisor.restrictSheaf W D').presheaf.map (homOfLE le_top).op σ =
          a • restrictInvSection W hψ hV := by
    intro x
    obtain ⟨U, hyU, ψ, hψ⟩ := hD' (W.ι.base ((h ∣_ W).base x))
    have hV : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) ≤ U := Scheme.Hom.image_preimage_le W.ι U
    obtain ⟨a, ha⟩ := (bijective_smul_restrictInvSection W hψ hV).2
      ((Divisor.restrictSheaf W D').presheaf.map (homOfLE le_top).op σ)
    exact ⟨U, ψ, hψ, W.ι ⁻¹ᵁ U, hV, a, hyU, ha.symm⟩
  have hD : D.IsCartier := hpb.isCartier hD'
  have hs : D.IsDivisorialSection ((h ⁻¹ᵁ W).ι ''ᵁ ⊤) sfun := by
    intro E hE
    have hηE : E.genericPoint ∈ (h ⁻¹ᵁ W).ι ''ᵁ ⊤ := E.genericPoint_mem_of_nonempty hE
    rw [Scheme.Opens.ι_image_top] at hηE
    let x : (h ⁻¹ᵁ W).toScheme := ⟨E.genericPoint, hηE⟩
    obtain ⟨U, ψ, hψ, V, hV, a, hxV, ha⟩ := hchart x
    have hφ := hpb.isLocalEquation hψ
    have hV' := image_preimage_morphismRestrict_le h W hV
    let τ : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, (h ∣_ W) ⁻¹ᵁ V) :=
      (h ∣_ W).app V a • restrictInvSection (h ⁻¹ᵁ W) hφ hV'
    have hEV : (E.support ∩ ((h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V) : Set X)).Nonempty :=
      ⟨E.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure (Set.mem_singleton _), x, hxV, rfl⟩
    have hτ := (Divisor.restrictSection (h ⁻¹ᵁ W) τ).2 E hEV
    have hZ := E.componentGenericPoint_mem_of_nonempty hEV
    have key := hloc U ψ hψ V hV a ha E.component hZ
    rw [restrictSection_smul_apply, restrictSection_restrictInvSection, ← key] at hτ
    exact hτ
  let s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, ⊤) := ⟨sfun, hs⟩
  refine ⟨s, ?_, fun x => ?_⟩
  · intro Z hZ Z' hZ' hsp'
    obtain rfl : Z' = ZY := Subsingleton.elim _ _
    rfl
  obtain ⟨U, ψ, hψ, V, hV, a, hxV, ha⟩ := hchart x
  have hφ := hpb.isLocalEquation hψ
  have hV' := image_preimage_morphismRestrict_le h W hV
  have hxV' : x ∈ (h ∣_ W) ⁻¹ᵁ V := hxV
  have hsV : (Divisor.restrictSheaf (h ⁻¹ᵁ W) D).presheaf.map (homOfLE le_top).op s =
      (h ∣_ W).app V a • restrictInvSection (h ⁻¹ᵁ W) hφ hV' := by
    apply Divisor.restrictSection_inj
    funext Z
    rw [restrictSection_smul_apply, restrictSection_restrictInvSection,
      ← hloc U ψ hψ V hV a ha Z.1 Z.2]
    rfl
  have e1 : (Divisor.restrictSheaf (h ⁻¹ᵁ W) D).presheaf.Γgerm x s =
      (Divisor.restrictSheaf (h ⁻¹ᵁ W) D).presheaf.germ _ x hxV'
        ((Divisor.restrictSheaf (h ⁻¹ᵁ W) D).presheaf.map (homOfLE le_top).op s) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have e2 : (Divisor.restrictSheaf W D').presheaf.Γgerm ((h ∣_ W).base x) σ =
      (Divisor.restrictSheaf W D').presheaf.germ _ _ hxV
        ((Divisor.restrictSheaf W D').presheaf.map (homOfLE le_top).op σ) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, Stacks.Ample.mem_nonvanishingLocus_iff, e1, e2,
    hsV, ha, germ_smul_restrictInvSection_notMem_maximalSmul_iff (h ⁻¹ᵁ W) hD hφ hV' _ x hxV',
    germ_smul_restrictInvSection_notMem_maximalSmul_iff W hD' hψ hV a _ hxV,
    ← Scheme.Hom.germ_stalkMap_apply (h ∣_ W) V x hxV a]
  exact isUnit_map_iff _ _

/-- A pull-back of sections restricts to a pull-back of sections. -/
private theorem IsPullbackSection.isPullbackSectionOn {h : X ⟶ Y} {W : Y.Opens} {D : Divisor X}
    {D' : Divisor Y} {σ : Γ(Divisor.restrictSheaf W D', ⊤)}
    {s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, ⊤)} (hs : IsPullbackSection h W σ s)
    (V₁ : W.toScheme.Opens) :
    IsPullbackSectionOn h W V₁ ((Divisor.restrictSheaf W D').presheaf.map (homOfLE le_top).op σ)
      ((Divisor.restrictSheaf (h ⁻¹ᵁ W) D).presheaf.map (homOfLE le_top).op s) :=
  fun Z hZ Z' hZ' hsp => hs Z ((h ⁻¹ᵁ W).ι.image_mono le_top hZ) Z' (W.ι.image_mono le_top hZ') hsp

/-- A pull-back of sections is unique. -/
private theorem IsPullbackSectionOn.eq [IsIntegral X] [IsIntegral Y] {h : X ⟶ Y} [IsDominant h]
    {W : Y.Opens} {D : Divisor X} {D' : Divisor Y} {V₁ : W.toScheme.Opens}
    {σ : Γ(Divisor.restrictSheaf W D', V₁)}
    {s s' : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ W) D, (h ∣_ W) ⁻¹ᵁ V₁)}
    (hs : IsPullbackSectionOn h W V₁ σ s) (hs' : IsPullbackSectionOn h W V₁ σ s') : s = s' := by
  let ZY : irreducibleComponents Y := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
  apply Divisor.restrictSection_inj
  funext ⟨Z, hZ⟩
  have hZ' : h (componentGenericPoint X Z) ∈ W.ι ''ᵁ V₁ := by
    have h2 : componentGenericPoint X Z ∈ (h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ V₁) := hZ
    rw [image_morphismRestrict_preimage] at h2
    exact h2
  have hsp := specializes_componentGenericPoint h Z ZY
  have hZY : componentGenericPoint Y ZY ∈ W.ι ''ᵁ V₁ :=
    ((isGenericPoint_componentGenericPoint Y ZY).specializes (Set.mem_univ _)).mem_open
      (W.ι ''ᵁ V₁).isOpen hZ'
  exact (hs Z hZ ZY hZY hsp).trans (hs' Z hZ ZY hZY hsp).symm

end PullbackSections

/-- **Serre surjectivity for a proper scheme over a Noetherian ring.** If `L` is ample on `X`,
proper over `Spec R`, and `i : T ⟶ X` is a closed immersion, then for all large `d` every section
of `i^* L^{⊗ d}` is the restriction of a global section of `L^{⊗ d}`: the ideal sheaf of `T` is
coherent, so `H¹(X, ℐ_T ⊗ L^{⊗ d}) = 0` for `d ≫ 0`. -/
private theorem exists_surjective_unit_app_tensorPower {R : Type} [CommRing R] [IsNoetherianRing R]
    {X T : Scheme.{0}} (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (i : T ⟶ X)
    [IsClosedImmersion i] :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (d : ℤ))).app ⊤) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hI : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
      (Stacks.Chow.isCoherent_pushforwardStructureSheaf i) _
  obtain ⟨n₀, hn₀⟩ := (Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL)) _ hI
  refine ⟨n₀, fun d hd => ?_⟩
  have := Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app i
    (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (d : ℤ)) (hn₀ d 1 hd Nat.one_pos)
  exact (ModuleCat.epi_iff_surjective _).mp this

section TensorPowers

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

/-- `𝒪(jL)|_W ≅ (𝒪(L)|_W)^{⊗ j}` for a Cartier divisor `L`, the tensor power of the ampleness
theory. -/
private noncomputable def restrictSheafNsmulIso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (W : X.Opens) {L : Divisor X} (hL : L.IsCartier)
    [Stacks.Ample.IsInvertibleModule W.toScheme (Divisor.restrictSheaf W L)] (j : ℕ) :
    Divisor.restrictSheaf W (j • L) ≅
      Stacks.Ample.tensorPowModule W.toScheme (Divisor.restrictSheaf W L) (j : ℤ) :=
  (Divisor.natTensorPowRestrictIso W hL j).symm ≪≫
    Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule _ _ j

end TensorPowers

/-- **Serre surjectivity over an affine open of the base.** Let `L` be a Cartier divisor on `X`,
ample relative to a proper `g : X ⟶ Z`, `U ⊆ Z` affine and `T ⟶ g⁻¹ U` a closed immersion. For all
large `j`, every section of `𝒪(jL)` on `T` is the restriction of a section over `g⁻¹ U`. -/
private theorem exists_unit_app_eq_of_isRelativelyAmple {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Z] (g : X ⟶ Z)
    [IsProper g] {L : Divisor X} (hL : L.IsCartier) (hamp : L.IsRelativelyAmple g hL)
    (U : Z.Opens) (hU : IsAffineOpen U) {T : Scheme.{0}} (ιT : T ⟶ (g ⁻¹ᵁ U).toScheme)
    [IsClosedImmersion ιT] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ τ : Γ((Scheme.Modules.pullback ιT).obj
        (Divisor.restrictSheaf (g ⁻¹ᵁ U) (j • L)), ⊤),
      ∃ σ : Γ(Divisor.restrictSheaf (g ⁻¹ᵁ U) (j • L), ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction ιT).unit.app
          (Divisor.restrictSheaf (g ⁻¹ᵁ U) (j • L))).app ⊤ σ = τ := by
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f₀ : (g ⁻¹ᵁ U).toScheme ⟶ Spec (.of Γ(Z, U)) := (g ∣_ U) ≫ hU.isoSpec.hom
  have : IsProper (g ∣_ U) := inferInstance
  have : IsProper hU.isoSpec.hom := inferInstance
  have : IsProper f₀ := inferInstanceAs (IsProper ((g ∣_ U) ≫ hU.isoSpec.hom))
  have hinv := hL.isInvertibleModule_divisorialSheaf
  have hst : Stacks.RelativeAmple.IsRelativelyAmple g L.divisorialSheaf :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover g _
      inferInstance).mpr hamp
  have hA := hst.isAmple_preimage g _ U hU
  have := Divisor.isInvertibleModule_restrictSheaf (g ⁻¹ᵁ U) hL
  have hinvP : Stacks.Ample.IsInvertibleModule (g ⁻¹ᵁ U).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (g ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (g ⁻¹ᵁ U).ι L.divisorialSheaf
  have hA' : Stacks.Ample.IsAmple (g ⁻¹ᵁ U).toScheme (Divisor.restrictSheaf (g ⁻¹ᵁ U) L) :=
    (Stacks.RelativeVeryAmple.isAmple_congr
      ((RingedSpaceModuleAdjunction.modulePullback (g ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) (Divisor.restrictSheaf (g ⁻¹ᵁ U) L)
      ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι).app L.divisorialSheaf).symm).mp hA
  obtain ⟨d₀, hd₀⟩ := exists_surjective_unit_app_tensorPower f₀ _ hA' ιT
  refine ⟨d₀, fun j hj τ => ?_⟩
  let e : Divisor.restrictSheaf (g ⁻¹ᵁ U) (j • L) ≅
      Stacks.SheafOfModules.Invertible.tensorPower (g ⁻¹ᵁ U).toScheme.toRingedSpace.presheaf
        (structureSheafRing (g ⁻¹ᵁ U).toScheme.toRingedSpace).property
        (Divisor.restrictSheaf (g ⁻¹ᵁ U) L) (j : ℤ) :=
    restrictSheafNsmulIso (g ⁻¹ᵁ U) hL j ≪≫
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso _ _ (j : ℤ)).symm
  let φ := (Scheme.Modules.pullback ιT).mapIso e
  obtain ⟨σ', hσ'⟩ := hd₀ j hj (φ.hom.app ⊤ τ)
  refine ⟨e.inv.app ⊤ σ', ?_⟩
  have hnat := congrArg (fun F => F.app ⊤ (e.inv.app ⊤ σ'))
    ((Scheme.Modules.pullbackPushforwardAdjunction ιT).unit.naturality e.hom)
  have h1 : e.hom.app ⊤ (e.inv.app ⊤ σ') = σ' := by
    have := congrArg (fun F => Scheme.Modules.Hom.app F ⊤ σ') e.inv_hom_id
    exact this
  have inj : ∀ y, φ.inv.app ⊤ (φ.hom.app ⊤ y) = y := fun y => by
    have := congrArg (fun F => Scheme.Modules.Hom.app F ⊤ y) φ.hom_inv_id
    exact this
  have k : φ.hom.app ⊤ (((Scheme.Modules.pullbackPushforwardAdjunction ιT).unit.app
      (Divisor.restrictSheaf (g ⁻¹ᵁ U) (j • L))).app ⊤ (e.inv.app ⊤ σ')) = φ.hom.app ⊤ τ := by
    refine (hnat.symm.trans ?_).trans hσ'
    exact congrArg _ h1
  exact (inj _).symm.trans ((congrArg (φ.inv.app ⊤) k).trans (inj τ))

/-- A section over one of two complementary clopen opens extends by zero over the other. -/
private theorem exists_section_res_eq_of_disjoint {T : Scheme.{0}} (N : T.Modules)
    (U V : T.Opens) (hdisj : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤) (a : Γ(N, U)) :
    ∃ s : Γ(N, ⊤), N.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s = a ∧
      N.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} T := ⟨N.presheaf, N.isSheaf⟩
  let W : Bool → T.Opens := fun b => cond b U V
  let t : ∀ b, F.obj.obj (op (W b)) := fun b => match b with
    | true => a
    | false => 0
  have hW : (⊤ : T.Opens) ≤ ⨆ b, W b := by
    intro x _
    have hx : x ∈ U ⊔ V := hcover ▸ trivial
    rcases hx with hx | hx
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hx⟩
  have hempty : ∀ A : T.Opens, A = ⊥ → Subsingleton (F.obj.obj (op A)) := by
    intro A hA
    subst A
    exact AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEmpty).isZero
  have ht : TopCat.Presheaf.IsCompatible F.obj W t := by
    intro b c
    cases b <;> cases c
    · rfl
    · exact @Subsingleton.elim _ (hempty (V ⊓ U) (by rw [inf_comm]; exact hdisj)) _ _
    · exact @Subsingleton.elim _ (hempty (U ⊓ V) hdisj) _ _
    · rfl
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) hW t ht
  exact ⟨s, hs true, hs false⟩

/-- If `i : T ⟶ Y` sends exactly the points of `i⁻¹ Ω` into a closed set `A`, then `i⁻¹ Ω` is
open and closed in `T`, and every section over it extends to `T` (by zero off it). -/
private theorem exists_section_res_eq_of_mem_iff {T Y : Scheme.{0}} (i : T ⟶ Y) (N : T.Modules)
    {A : Set Y} (hA : IsClosed A) (Ω : Y.Opens) (hΩ : ∀ z : T, i.base z ∈ Ω ↔ i.base z ∈ A)
    (τΩ : Γ(N, i ⁻¹ᵁ Ω)) :
    ∃ τ : Γ(N, ⊤), N.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ Ω ≤ ⊤)).op τ = τΩ := by
  obtain ⟨τ, h1, -⟩ := exists_section_res_eq_of_disjoint N (i ⁻¹ᵁ Ω)
    (i ⁻¹ᵁ ⟨Aᶜ, hA.isOpen_compl⟩) (le_antisymm (fun z hz => hz.2 ((hΩ z).1 hz.1)) bot_le)
    (le_antisymm le_top fun z _ => (em (i.base z ∈ A)).imp (hΩ z).2 id) τΩ
  exact ⟨τ, h1⟩

/-- At an isolated closed point `p`, an invertible module has a global section that does not
vanish at `p` and is zero away from `p`. -/
private theorem exists_section_notMem_maximalSmul_of_isOpen {T : Scheme.{0}} (N : T.Modules)
    [Stacks.Ample.IsInvertibleModule T N] (p : T) (hopen : IsOpen ({p} : Set T))
    (hclosed : IsClosed ({p} : Set T)) :
    ∃ s : Γ(N, ⊤), N.presheaf.germ ⊤ p trivial s ∉ Stacks.ModuleStalk.maximalSmul N p ∧
      N.presheaf.map (homOfLE le_top : (⟨{p}ᶜ, hclosed.isOpen_compl⟩ : T.Opens) ⟶ ⊤).op s = 0 := by
  obtain ⟨W, hpW, b, hb⟩ := MMP.Mori.exists_opens_nonvanishingLocusOn_of_isInvertibleModule N p
  let U : T.Opens := ⟨{p}, hopen⟩
  have hUW : U ≤ W := fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hpW
  obtain ⟨s, hsU, hsV⟩ := exists_section_res_eq_of_disjoint N U ⟨{p}ᶜ, hclosed.isOpen_compl⟩
    (SetLike.coe_injective (Set.inter_compl_self ({p} : Set T)))
    (SetLike.coe_injective (Set.union_compl_self ({p} : Set T))) (N.presheaf.map (homOfLE hUW).op b)
  refine ⟨s, ?_, hsV⟩
  have hpU : p ∈ U := Set.mem_singleton p
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE le_top : U ⟶ ⊤) p hpU, hsU,
    TopCat.Presheaf.germ_res_apply]
  exact (hb hpW).2

/-- `h ∣_ U` lies over `h` along the inclusions of `U` and `h⁻¹ U`. -/
private theorem ι_morphismRestrict_apply {X Y : Scheme.{0}} (h : X ⟶ Y) (U : Y.Opens)
    (z : (h ⁻¹ᵁ U).toScheme) : U.ι.base ((h ∣_ U).base z) = h.base ((h ⁻¹ᵁ U).ι.base z) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- If `h` is an isomorphism on sections, so is its restriction over an open. -/
private theorem isIso_morphismRestrict_app {X Y : Scheme.{0}} (h : X ⟶ Y)
    (hhO : ∀ U : Y.Opens, IsIso (h.app U)) (U : Y.Opens) (O : U.toScheme.Opens) :
    IsIso ((h ∣_ U).app O) := by
  rw [morphismRestrict_app]
  exact IsIso.comp_isIso' (hhO (U.ι ''ᵁ O))
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage h U O)).op).isIso_hom

/-- A point of an open `U` lying on a closed immersion `i` lifts to `i ∣_ U`. -/
private theorem exists_morphismRestrict_eq {T X : Scheme.{0}} (i : T ⟶ X) (U : X.Opens)
    (y : U.toScheme) (hy : U.ι.base y ∈ Set.range i.base) :
    ∃ z : (i ⁻¹ᵁ U).toScheme, (i ∣_ U).base z = y := by
  obtain ⟨w, hw⟩ := hy
  have hwU : i.base w ∈ U := hw ▸ y.2
  refine ⟨⟨w, hwU⟩, ?_⟩
  apply U.ι.isOpenEmbedding.injective
  exact (congrArg (fun φ : (i ⁻¹ᵁ U).toScheme ⟶ X => φ.base ⟨w, hwU⟩)
    (morphismRestrict_ι i U)).trans hw

section Descent

/-- Two sections of a sheaf of modules that agree locally agree. -/
private theorem eq_of_forall_exists_map_eq {X : Scheme.{0}} (M : X.Modules)
    {O : X.Opens} (x y : Γ(M, O))
    (H : ∀ c ∈ O, ∃ O' : X.Opens, ∃ hO' : O' ≤ O, c ∈ O' ∧
      M.presheaf.map (homOfLE hO').op x = M.presheaf.map (homOfLE hO').op y) :
    x = y := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} X := ⟨M.presheaf, M.isSheaf⟩
  choose O' hO' hcO h0 using H
  exact F.eq_of_locally_eq' (fun c : O => O' c.1 c.2) O (fun c => homOfLE (hO' c.1 c.2))
    (fun c hc => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c, hc⟩, hcO c hc⟩) x y fun c => h0 c.1 c.2

/-- The unit of `i^* ⊣ i_*` commutes with restriction. -/
private theorem unit_app_map {X Y : Scheme.{0}} (i : X ⟶ Y) (F : Y.Modules) {O O' : Y.Opens}
    (hle : O' ≤ O) (σ : Γ(F, O)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app O'
        (F.presheaf.map (homOfLE hle).op σ) =
      ((Scheme.Modules.pullback i).obj F).presheaf.map (homOfLE (i.preimage_mono hle)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app O σ) :=
  ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).mapPresheaf.naturality
      (homOfLE hle).op) σ

/-- **The restriction of `σ ^ r` to `C` only depends on the restriction of `σ`.** -/
private theorem unit_app_eq_of_unit_app_eq_of_pow {V C : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (ι : C ⟶ V) (W : V.Opens) {E : Divisor V} (hE : E.IsCartier)
    (r : ℕ) {O : W.toScheme.Opens} {σ σ' : Γ(Divisor.restrictSheaf W E, O)}
    (hσ : ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W E)).app O σ =
      ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W E)).app O σ')
    {τ τ' : Γ(Divisor.restrictSheaf W (r • E), O)}
    (hτ : (Divisor.restrictSection W τ).1 = (Divisor.restrictSection W σ).1 ^ r)
    (hτ' : (Divisor.restrictSection W τ').1 = (Divisor.restrictSection W σ').1 ^ r) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W (r • E))).app O τ =
      ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W (r • E))).app O τ' := by
  refine eq_of_forall_exists_map_eq
    ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E)))
    (O := (ι ∣_ W) ⁻¹ᵁ O) _ _ fun c hc => ?_
  let x := (ι ∣_ W).base c
  have := Divisor.isInvertibleModule_restrictSheaf W hE
  obtain ⟨U₀, hxU₀, ψ, hψ⟩ := hE (W.ι.base x)
  let O₁ : W.toScheme.Opens := O ⊓ W.ι ⁻¹ᵁ U₀
  have hO₁ : O₁ ≤ O := inf_le_left
  have hV : W.ι ''ᵁ O₁ ≤ U₀ :=
    (W.ι.image_mono (inf_le_right : O₁ ≤ W.ι ⁻¹ᵁ U₀)).trans (Scheme.Hom.image_preimage_le W.ι U₀)
  have hcO₁ : c ∈ (ι ∣_ W) ⁻¹ᵁ O₁ := ⟨hc, hxU₀⟩
  refine ⟨(ι ∣_ W) ⁻¹ᵁ O₁, (ι ∣_ W).preimage_mono hO₁, hcO₁, ?_⟩
  set β := restrictInvSection W hψ hV
  set βr := restrictInvSection W (isLocalEquation_zpow hψ r) hV
  obtain ⟨e, he⟩ := (bijective_smul_restrictInvSection W hψ hV).2
    ((Divisor.restrictSheaf W E).presheaf.map (homOfLE hO₁).op σ)
  obtain ⟨e', he'⟩ := (bijective_smul_restrictInvSection W hψ hV).2
    ((Divisor.restrictSheaf W E).presheaf.map (homOfLE hO₁).op σ')
  have key : ∀ (σ₁ : Γ(Divisor.restrictSheaf W E, O)) (τ₁ : Γ(Divisor.restrictSheaf W (r • E), O))
      (e₁ : Γ(W.toScheme, O₁)),
      (Divisor.restrictSection W τ₁).1 = (Divisor.restrictSection W σ₁).1 ^ r →
      e₁ • β = (Divisor.restrictSheaf W E).presheaf.map (homOfLE hO₁).op σ₁ →
      (Divisor.restrictSheaf W (r • E)).presheaf.map (homOfLE hO₁).op τ₁ = e₁ ^ r • βr := by
    intro σ₁ τ₁ e₁ h1 h2
    apply Divisor.restrictSection_inj W
    rw [restrictSection_smul_pow W hψ r hV e₁, h2]
    funext Z
    exact congrFun h1 ⟨Z.1, W.ι.image_mono hO₁ Z.2⟩
  have hgen := isLocalGenerator_pullback_unit (ι ∣_ W) _
    (isLocalGenerator_restrictInvSection W hψ hV)
  have hee : (ι ∣_ W).app O₁ e = (ι ∣_ W).app O₁ e' := by
    have h1 := congrArg (((Scheme.Modules.pullback (ι ∣_ W)).obj
      (Divisor.restrictSheaf W E)).presheaf.map (homOfLE ((ι ∣_ W).preimage_mono hO₁)).op) hσ
    rw [← unit_app_map _ _ hO₁, ← unit_app_map _ _ hO₁, ← he, ← he', unit_app_smul,
      unit_app_smul] at h1
    refine (hgen _ le_rfl).1 ?_
    change (ι ∣_ W).app O₁ e • _ = (ι ∣_ W).app O₁ e' • _
    convert h1 using 2 <;> exact map_homOfLE_self_apply _ _ _
  rw [← unit_app_map _ _ hO₁, ← unit_app_map _ _ hO₁, key σ τ e hτ he, key σ' τ' e' hτ' he',
    unit_app_smul, unit_app_smul, map_pow, map_pow, hee]

/-- **Local lifts of `t` and of `t ^ r`.** Near every point of `C ∩ W`, inside any given open,
`t` lifts to a section `σ` of `𝒪(E)` and `σ ^ r` is a section of `𝒪(rE)`. -/
private theorem exists_local_lift_pow {V C : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (ι : C ⟶ V) [IsClosedImmersion ι] (W : V.Opens) {E : Divisor V}
    (hE : E.IsCartier)
    (t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), ⊤))
    (r : ℕ) (c : (ι ⁻¹ᵁ W).toScheme) (N : W.toScheme.Opens) (hcN : (ι ∣_ W).base c ∈ N) :
    ∃ (O : W.toScheme.Opens) (_ : O ≤ N) (_ : (ι ∣_ W).base c ∈ O)
      (σ : Γ(Divisor.restrictSheaf W E, O)) (τ : Γ(Divisor.restrictSheaf W (r • E), O)),
      ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
          (Divisor.restrictSheaf W E)).app O σ =
        ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E)).presheaf.map
          (homOfLE le_top).op t ∧
      (Divisor.restrictSection W τ).1 = (Divisor.restrictSection W σ).1 ^ r := by
  let j := ι ∣_ W
  let F := Divisor.restrictSheaf W E
  let x := j.base c
  have := Divisor.isInvertibleModule_restrictSheaf W hE
  obtain ⟨U₀, hxU₀, ψ, hψ⟩ := hE (W.ι.base x)
  obtain ⟨O, hOaff, hxO, hOle⟩ := exists_isAffineOpen_mem_and_subset
    (U := N ⊓ W.ι ⁻¹ᵁ U₀) (show x ∈ N ⊓ W.ι ⁻¹ᵁ U₀ from ⟨hcN, hxU₀⟩)
  have hON : O ≤ N := fun y hy => (hOle hy).1
  have hV : W.ι ''ᵁ O ≤ U₀ :=
    (W.ι.image_mono (show O ≤ W.ι ⁻¹ᵁ U₀ from fun y hy => (hOle hy).2)).trans
      (Scheme.Hom.image_preimage_le W.ι U₀)
  obtain ⟨a, ha⟩ := exists_unit_app_smul_restrictInvSection_eq ι W hψ hOaff hV
    (((Scheme.Modules.pullback j).obj F).presheaf.map (homOfLE le_top).op t)
  exact ⟨O, hON, hxO, a • restrictInvSection W hψ hV,
    a ^ r • restrictInvSection W (isLocalEquation_zpow hψ r) hV, ha,
    restrictSection_smul_pow W hψ r hV a⟩

/-- Restriction of a lift of `t` is a lift of `t`. -/
private theorem unit_app_map_eq_of_eq {V C : Scheme.{0}} (ι : C ⟶ V) (W : V.Opens)
    (F : W.toScheme.Modules)
    (t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj F, ⊤)) {O O' : W.toScheme.Opens} (hle : O' ≤ O)
    {σ : Γ(F, O)}
    (hσ : ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app F).app O σ =
        ((Scheme.Modules.pullback (ι ∣_ W)).obj F).presheaf.map (homOfLE le_top).op t) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app F).app O'
        (F.presheaf.map (homOfLE hle).op σ) =
      ((Scheme.Modules.pullback (ι ∣_ W)).obj F).presheaf.map (homOfLE le_top).op t := by
  rw [unit_app_map, hσ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **The section `t ^ r`.** There is a section `T` of `ι^* 𝒪(rE)` on `C ∩ W` such that every
local `σ ^ r`, for a local lift `σ` of `t`, restricts to `T`. -/
private theorem exists_powSection {V C : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (ι : C ⟶ V) [IsClosedImmersion ι] (W : V.Opens) {E : Divisor V}
    (hE : E.IsCartier)
    (t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), ⊤))
    (r : ℕ) :
    ∃ T : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E)), ⊤),
      ∀ (O : W.toScheme.Opens) (σ : Γ(Divisor.restrictSheaf W E, O))
        (τ : Γ(Divisor.restrictSheaf W (r • E), O)),
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
            (Divisor.restrictSheaf W E)).app O σ =
          ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E)).presheaf.map
            (homOfLE le_top).op t →
        (Divisor.restrictSection W τ).1 = (Divisor.restrictSection W σ).1 ^ r →
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
            (Divisor.restrictSheaf W (r • E))).app O τ =
          ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E))).presheaf.map
            (homOfLE le_top).op T := by
  let M := (Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E))
  let Fs : TopCat.Sheaf AddCommGrpCat.{0} (ι ⁻¹ᵁ W).toScheme := ⟨M.presheaf, M.isSheaf⟩
  choose O _ hcO σ τ hσ hτ using fun c => exists_local_lift_pow ι W hE t r c ⊤ trivial
  let sf : ∀ c, Fs.obj.obj (op ((ι ∣_ W) ⁻¹ᵁ O c)) := fun c =>
    ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
      (Divisor.restrictSheaf W (r • E))).app (O c) (τ c)
  -- any local power agrees with the chosen ones on overlaps
  have hagree : ∀ (O' : W.toScheme.Opens) (σ' : Γ(Divisor.restrictSheaf W E, O'))
      (τ' : Γ(Divisor.restrictSheaf W (r • E), O')),
      ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
          (Divisor.restrictSheaf W E)).app O' σ' =
        ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E)).presheaf.map
          (homOfLE le_top).op t →
      (Divisor.restrictSection W τ').1 = (Divisor.restrictSection W σ').1 ^ r →
      ∀ c, M.presheaf.map (homOfLE ((ι ∣_ W).preimage_mono (inf_le_left : O' ⊓ O c ≤ O'))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
            (Divisor.restrictSheaf W (r • E))).app O' τ') =
        M.presheaf.map (homOfLE ((ι ∣_ W).preimage_mono (inf_le_right : O' ⊓ O c ≤ O c))).op
          (sf c) := by
    intro O' σ' τ' hσ' hτ' c
    rw [← unit_app_map _ _ inf_le_left, ← unit_app_map _ _ inf_le_right]
    refine unit_app_eq_of_unit_app_eq_of_pow ι W hE r
      (σ := (Divisor.restrictSheaf W E).presheaf.map (homOfLE inf_le_left).op σ')
      (σ' := (Divisor.restrictSheaf W E).presheaf.map (homOfLE inf_le_right).op (σ c)) ?_ ?_ ?_
    · rw [unit_app_map_eq_of_eq ι W _ t _ hσ', unit_app_map_eq_of_eq ι W _ t _ (hσ c)]
    · funext Z; exact congrFun hτ' ⟨Z.1, W.ι.image_mono inf_le_left Z.2⟩
    · funext Z; exact congrFun (hτ c) ⟨Z.1, W.ι.image_mono inf_le_right Z.2⟩
  have hcover : (⊤ : (ι ⁻¹ᵁ W).toScheme.Opens) ≤ ⨆ c, (ι ∣_ W) ⁻¹ᵁ O c := fun c _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨c, hcO c⟩
  have hcompat : TopCat.Presheaf.IsCompatible Fs.obj (fun c => (ι ∣_ W) ⁻¹ᵁ O c) sf := by
    intro c c'
    exact hagree (O c) (σ c) (τ c) (hσ c) (hτ c) c'
  obtain ⟨T, hT, -⟩ := Fs.existsUnique_gluing' (fun c => (ι ∣_ W) ⁻¹ᵁ O c) ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  refine ⟨T, fun O' σ' τ' hσ' hτ' => ?_⟩
  refine eq_of_forall_exists_map_eq M (O := (ι ∣_ W) ⁻¹ᵁ O') _ _ fun c hc => ?_
  refine ⟨(ι ∣_ W) ⁻¹ᵁ (O' ⊓ O c), (ι ∣_ W).preimage_mono inf_le_left, ⟨hc, hcO c⟩, ?_⟩
  have h1 := hagree O' σ' τ' hσ' hτ' c
  refine h1.trans ?_
  rw [← hT c, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

/-- If `s` restricts to `T = t ^ r` on `C`, then `s` lifts `t ^ r`. -/
private theorem liftsPow_of_unit_app_eq {V C : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (ι : C ⟶ V) (W : V.Opens) {E : Divisor V}
    {t : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E), ⊤)} {r : ℕ}
    {T : Γ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E)), ⊤)}
    (hT : ∀ (O : W.toScheme.Opens) (σ : Γ(Divisor.restrictSheaf W E, O))
        (τ : Γ(Divisor.restrictSheaf W (r • E), O)),
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
            (Divisor.restrictSheaf W E)).app O σ =
          ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W E)).presheaf.map
            (homOfLE le_top).op t →
        (Divisor.restrictSection W τ).1 = (Divisor.restrictSection W σ).1 ^ r →
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
            (Divisor.restrictSheaf W (r • E))).app O τ =
          ((Scheme.Modules.pullback (ι ∣_ W)).obj (Divisor.restrictSheaf W (r • E))).presheaf.map
            (homOfLE le_top).op T)
    {s : Γ(Divisor.restrictSheaf W (r • E), ⊤)}
    (hs : ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ W)).unit.app
        (Divisor.restrictSheaf W (r • E))).app ⊤ s = T) :
    LiftsPow ι W t r s := by
  intro O σ hσ τ hτ
  rw [map_sub, hT O σ τ hσ hτ, unit_app_map, hs]
  exact sub_self _

private theorem app_map_apply {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hle : U' ≤ U)
    (x : Γ(Y, U)) :
    f.app U' (Y.presheaf.map (homOfLE hle).op x) =
      X.presheaf.map (homOfLE (f.preimage_mono hle)).op (f.app U x) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE hle).op) x

/-- A function on `Y` killed by `f` is killed by `i` when every point of `O` in the range of `i`
lies in the range of `f` and the source of `i` is reduced. -/
private theorem app_eq_zero_of_range_subset {A B Y : Scheme.{0}} [IsReduced B] (f : A ⟶ Y)
    (i : B ⟶ Y) {O : Y.Opens} (hO : ∀ y ∈ O, y ∈ Set.range i.base → y ∈ Set.range f.base)
    (b : Γ(Y, O)) (hb : f.app O b = 0) : i.app O b = 0 := by
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  have hA : A.basicOpen (f.app O b) = ⊥ := by rw [hb, Scheme.basicOpen_zero]
  rw [← Scheme.preimage_basicOpen] at hA
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxO : i.base x ∈ O := Y.basicOpen_le b hx
  obtain ⟨a, ha⟩ := hO _ hxO ⟨x, rfl⟩
  have : a ∈ f ⁻¹ᵁ Y.basicOpen b := by
    change f.base a ∈ Y.basicOpen b
    rwa [ha]
  rwa [hA] at this

/-- Over a point `y` with finite fibre, a proper `h` is finite over a neighbourhood of `y`, so
`y` has arbitrarily small open neighbourhoods with affine preimage. -/
private theorem exists_le_isAffineOpen_preimage_of_finite {V V' : Scheme.{0}} (h : V ⟶ V')
    [IsProper h] (U' : V'.Opens) (V₀ : U'.toScheme.Opens) (y : U'.toScheme) (hy : y ∈ V₀)
    (hfin : (h.base ⁻¹' {U'.ι.base y}).Finite) :
    ∃ V₁ : U'.toScheme.Opens, V₁ ≤ V₀ ∧ y ∈ V₁ ∧ IsAffineOpen ((h ∣_ U') ⁻¹ᵁ V₁) := by
  obtain ⟨Vf, hyVf, hF⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton h _ hfin
  obtain ⟨V₂, hV₂aff, hyV₂, hV₂le⟩ := exists_isAffineOpen_mem_and_subset
    (U := Vf ⊓ U'.ι ''ᵁ V₀) (show U'.ι.base y ∈ Vf ⊓ U'.ι ''ᵁ V₀ from ⟨hyVf, y, hy, rfl⟩)
  have hV₂f : V₂ ≤ Vf := fun x hx => (hV₂le hx).1
  have hV₂U : V₂ ≤ U' := fun x hx => by
    obtain ⟨z, -, rfl⟩ := (hV₂le hx).2
    exact z.2
  refine ⟨U'.ι ⁻¹ᵁ V₂, fun x hx => ?_, hyV₂, ?_⟩
  · obtain ⟨z, hz, hzx⟩ := (hV₂le hx).2
    rwa [U'.ι.isOpenEmbedding.injective hzx] at hz
  have h1 : IsAffineOpen ((h ∣_ Vf) ⁻¹ᵁ (Vf.ι ⁻¹ᵁ V₂)) :=
    (hV₂aff.preimage_of_isOpenImmersion Vf.ι (by simpa using hV₂f)).preimage _
  have h2 : IsAffineOpen (h ⁻¹ᵁ V₂) := by
    have := h1.image_of_isOpenImmersion (h ⁻¹ᵁ Vf).ι
    rwa [image_morphismRestrict_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hV₂f] at this
  have h3 := h2.preimage_of_isOpenImmersion (h ⁻¹ᵁ U').ι
    (by simpa using h.preimage_mono hV₂U)
  convert h3 using 1
  ext x
  change (h ∣_ U').base x ∈ U'.ι ⁻¹ᵁ V₂ ↔ h.base ((h ⁻¹ᵁ U').ι.base x) ∈ V₂
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-! ### FA 17.4.3 and the floor -/

section FA17

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MMP MMP.Mori MMP.Flips

/-- `-D` is `h`-nef when a positive multiple of `D` is the pull-back of a Cartier divisor. -/
private theorem isRelativelyNef_neg_of_isPullback {V V' : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sV' : V' ⟶ Spec (.of ℂ)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [IsSeparated sV']
    [LocallyOfFiniteType sV']
    [QuasiCompact sV']
    (h : V ⟶ V') (hh : h ≫ sV' = sV) {D : QDivisor V} {k : ℕ} (hk : 0 < k) {L : Divisor V'}
    (hL : L.IsCartier) {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • D)
    (hMpb : ∃ hM, L.IsPullback h hM M) :
    (-D).IsRelativelyNef sV h := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace sV'
  obtain ⟨hM, hpb⟩ := hMpb
  have hnL : ((-1 : ℤ) • L).IsCartier := hL.zsmul (-1)
  have hpbn := hpb.zsmul hL (-1) (notMem_supp_zsmul h hM (-1))
  have hnM : ((-1 : ℤ) • M).IsCartier := hpbn.isCartier hnL
  have hnMeq : Divisor.toQDivisor ((-1 : ℤ) • M) = ((k : ℕ) : ℤ) • (-D) := by
    rw [map_zsmul, hMeq, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      smul_neg, ← neg_smul]
    push_cast; ring_nf
  have hDq : (-D).IsQCartier := ⟨k, by exact_mod_cast hk.ne', _, hnMeq, hnM⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (sX := sV) hDq
    fun C hC => ?_
  have := hnL.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sV C.ι C.dim_le (-D) hDq hk _ hnM hnMeq,
    Divisor.degreeOn_eq_degree_pushforward_of_iso h hh hnL hnM
      (hpbn.divisorialSheafIso (hBc := hnL)) C,
    C.pushforward_cycle_eq_zero_of_isContractedBy ℤ h hh hC, map_zero]
  simp

private theorem finrank_compHom_congr {K R M : Type*} [Field K] [CommRing R] [AddCommGroup M]
    [Module R M] {φ ψ : K →+* R} (h : φ = ψ) :
    @Module.finrank K M _ _ (Module.compHom M φ) =
      @Module.finrank K M _ _ (Module.compHom M ψ) := by
  subst h; rfl

private theorem genericFiberH0_eq_relativeGenericRank {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsIntegral X] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    genericFiberH0 f F = relativeGenericRank f F := by
  rw [MMP.Mori.relativeGenericRank_eq_finrank_fibre,
    LinearEquiv.finrank_eq (cohomologyOverFieldZeroLinearIso _ _ _).toLinearEquiv]
  unfold genericFiberH0
  refine finrank_compHom_congr ?_
  simp only [scalarsToGlobalSections, Scheme.Hom.appLE, Scheme.Hom.appTop]
  congr 2
  exact (Category.comp_id _).symm.trans (congrArg _ (CategoryTheory.Functor.map_id _ _).symm)

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AffineProjectionFormula in
private noncomputable def pushforwardPullbackIso {X Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : ∀ U : X.Opens, IsIso (f.app U))
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) ≅ N :=
  haveI : ∀ U, IsIso (f.c.app U) := fun U => hf U.unop
  haveI : IsIso f.c := NatIso.isIso_of_isIso_app _
  haveI : IsIso (unitToPushforwardStructure f.toLRSHom.toShHom) :=
    isIso_unitToPushforwardObjUnit_of_isIso_c f inferInstance
  haveI := (MMP.Resolution.Bridges.isIso_projectionFormulaMap_and_tmul f
    (structureModule Y.toRingedSpace) N).1
  (pushforwardFunctor f.toLRSHom.toShHom).mapIso
      (structureUnitor ((pullbackFunctor f.toLRSHom.toShHom).obj N)).symm ≪≫
    (asIso (Stacks.ProjectionFormula.projectionFormulaMap' f.toLRSHom.toShHom
      (structureModule Y.toRingedSpace) N)).symm ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      X.sheaf)).mapIso ((asIso (unitToPushforwardStructure f.toLRSHom.toShHom)).symm.prod
        (Iso.refl N)) ≪≫
    structureUnitor N

private theorem relativeGenericRank_pullback_eq_one {X Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : ∀ U : X.Opens, IsIso (f.app U))
    [IrreducibleSpace Y] (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] :
    relativeGenericRank f ((Scheme.Modules.pullback f).obj N) = 1 := by
  unfold relativeGenericRank
  rw [Scheme.Modules.fiberRank_eq_of_iso (pushforwardPullbackIso f hf N)]
  exact Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank N 1 _

private theorem isRelativelyBigOnGenericFiber_neg_of_isPullback {V V' : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)}
    {sV' : V' ⟶ Spec (.of ℂ)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    (hVv : MMP.Mori.IsVariety ℂ sV) (hV'v : MMP.Mori.IsVariety ℂ sV')
    (h : V ⟶ V') (hh : h ≫ sV' = sV) [IsProper h] [Surjective h]
    (hhO : ∀ U : V'.Opens, IsIso (h.app U)) {n : ℕ} (hdV : topologicalKrullDim V = n)
    (hdV' : topologicalKrullDim V' = n) {D : QDivisor V} {k : ℕ} (hk : 0 < k) {L : Divisor V'}
    (hL : L.IsCartier) {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • D)
    (hMpb : ∃ hM, L.IsPullback h hM M) :
    IsRelativelyBigOnGenericFiber h ℂ sV sV' (-D) := by
  obtain ⟨hM, hpb⟩ := hMpb
  have hrange : closure (Set.range h.base) = Set.univ := by
    rw [(h.isClosedMap.isClosed_range).closure_eq]
    exact Set.range_eq_univ.mpr h.surjective
  refine ⟨hVv, hV'v, hh, inferInstance, n, n, hdV, ?_, k, hk, -M, ?_, (hpb.isCartier hL).neg,
    1 / 2, by norm_num, 0, fun m _ => ?_⟩
  · rw [← hdV', hrange]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ V').isHomeomorph
  · rw [map_neg, hMeq, smul_neg]
  · rw [Nat.sub_self, pow_zero, mul_one]
    have hpm : Divisor.IsPullback h ((-m : ℤ) • L) (notMem_supp_zsmul h hM (-m)) ((m : ℤ) • -M) :=
      (show ((-m : ℤ)) • M = (m : ℤ) • -M by rw [neg_smul, smul_neg]) ▸
        hpb.zsmul hL (-m) (notMem_supp_zsmul h hM (-m))
    have := (hL.zsmul (-m)).isInvertibleModule_divisorialSheaf
    have hr : genericFiberH0 h ((m : ℤ) • -M).divisorialSheaf = 1 := by
      rw [genericFiberH0_eq_relativeGenericRank]
      unfold relativeGenericRank
      rw [Scheme.Modules.fiberRank_eq_of_iso ((Scheme.Modules.pushforward h).mapIso
        (Divisor.IsPullback.divisorialSheafIso (hBc := hL.zsmul (-m)) hpm))]
      exact relativeGenericRank_pullback_eq_one h hhO _
    rw [hr]
    norm_num

end FA17

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution
open MMP.Mori

universe u

/-! ### `ℝ`-Cartier divisors -/

/-- If `m(K + B)` is Cartier for some `m > 0`, then `K + B` is an `ℝ`-combination of Cartier
divisors. -/
private theorem isCartierCombination_toRDivisor_add {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {K : Divisor X} {B : QDivisor X} (h : (Divisor.toQDivisor K + B).IsQCartier) :
    MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor B) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := h.exists_pos
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add] at this
  have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by linear_combination this
  have h'' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast h'
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, h'', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
  field_simp

/-! ### Dlt pairs are log terminal -/

private theorem toRDivisor_toQDivisor {X : Scheme.{u}} (R : Divisor X) :
    QDivisor.toRDivisor (Divisor.toQDivisor R) = Divisor.toRDivisor R := by
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  rw [QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor, Divisor.coeff_toRDivisor]
  push_cast; rfl

/-- A log resolution, in the sense of *Flips and abundance*, of a normal variety with a reduced
divisor. -/
private theorem exists_isLogResolution_reducedDivisor {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n)
    (hX : IsNormalVariety k sX) (B : QDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      MMP.Flips.IsLogResolution sX (Divisor.toRDivisor (MMP.Intersection.reducedDivisor B)) g ∧
        IsResolutionOfVariety sX g := by
  classical
  set R := MMP.Intersection.reducedDivisor B
  have hlv : MMP.Flips.IsLogVariety k sX (QDivisor.toRDivisor (Divisor.toQDivisor R)) := by
    refine ⟨hX, fun E => ?_⟩
    rw [QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor]
    have : R.coeff E = 0 ∨ R.coeff E = 1 := by
      simp only [R, MMP.Intersection.reducedDivisor, MMP.Intersection.coeff_reducedDivisorOf]
      split_ifs <;> simp
    rcases this with h | h <;> rw [h] <;> norm_num
  obtain ⟨Y, f, hres, -, hsnc, -⟩ :=
    exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX (Divisor.toQDivisor R).support
  refine ⟨Y, f, ?_, hres⟩
  rw [← toRDivisor_toQDivisor]
  exact MMP.Intersection.isLogResolution_of_isSNCClosedSubset hn hlv hres hsnc

end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite MMP MMP.Mori MMP.Flips

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
private theorem isLocallySurjective_mapPresheaf_of_epi {Z : Scheme.{0}} {M N : Z.Modules}
    (φ : M ⟶ N) [Epi φ] : TopCat.Presheaf.IsLocallySurjective (Scheme.Modules.Hom.mapPresheaf φ) :=
  Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi φ

private theorem exists_app_eq_map_of_epi {Z : Scheme.{0}} {M N : Z.Modules} (φ : M ⟶ N) [Epi φ]
    {U : Z.Opens} (t : Γ(N, U)) {z : Z} (hz : z ∈ U) :
    ∃ (V : Z.Opens) (hV : V ≤ U), z ∈ V ∧
      ∃ x : Γ(M, V), φ.app V x = N.presheaf.map (homOfLE hV).op t := by
  obtain ⟨V, i, ⟨x, hx⟩, hzV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    (isLocallySurjective_mapPresheaf_of_epi φ) U t z hz
  exact ⟨V, fun _ h => i h, hzV, x, hx⟩

private theorem exists_app_eq_of_cokernel_π_app_eq_zero {X : Scheme.{0}} {M N : X.Modules}
    (i : M ⟶ N) [Mono i] {W : X.Opens} (x : Γ(N, W)) (hx : (cokernel.π i).app W x = 0) :
    ∃ y : Γ(M, W), i.app W y = x := by
  let ev := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op W)
  have : PreservesLimits ev := evaluationPreservesLimits _
  have : ev.PreservesZeroMorphisms := inferInstance
  have : PreservesLimits (Scheme.Modules.toPresheaf X ⋙ ev) := comp_preservesLimits _ _
  have hex := (ShortComplex.cokernelSequence_exact i).map_of_mono_of_preservesKernel
    (Scheme.Modules.toPresheaf X ⋙ ev) (by exact ‹Mono i›) inferInstance
  exact (ShortComplex.ab_exact_iff _).1 hex x hx

private theorem cokernel_π_app_app_eq_zero {X : Scheme.{0}} {M N : X.Modules} (i : M ⟶ N)
    (U : X.Opens) (y : Γ(M, U)) : (cokernel.π i).app U (i.app U y) = 0 :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U) (cokernel.condition i)) y

private theorem presheaf_map_map_apply {X : TopCat.{0}} {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    (F : TopCat.Presheaf C X) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    (x : ToType (F.obj U)) : F.map j (F.map i x) = F.map k x := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  congr 2

private theorem app_presheaf_map_apply {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

section Cokernel

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {G H : Divisor Y} (hH : 0 ≤ H) (hle : H - G ≤ H)

private noncomputable def unitSection (W : Y.Opens) : Γ(Y, W) →+ Γ(H.divisorialSheaf, W) :=
  (ConcreteCategory.hom ((Divisor.structureSheafToDivisorialSheaf hH).app W) :
    Γ(Y, W) →+ Γ(H.divisorialSheaf, W))

omit [CompactSpace Y] in
private theorem coe_unitSection (W : Y.Opens) (a : Γ(Y, W)) :
    (unitSection hH W a).1 = (toRationalFunctionsPresheaf Y).app (op W) a :=
  Divisor.coe_structureSheafToDivisorialSheaf_app hH W a

omit [CompactSpace Y] in
private theorem presheaf_map_unitSection {U V : Y.Opens} (i : V ⟶ U) (a : Γ(Y, U)) :
    H.divisorialSheaf.presheaf.map i.op (unitSection hH U a) =
      unitSection hH V (Y.presheaf.map i.op a) :=
  (app_presheaf_map_apply (M := Mori.structureSheafModule Y) _ i a).symm

omit [CompactSpace Y] in
private theorem cokernel_π_app_unitSection_eq_zero {W : Y.Opens} (a : Γ(Y, W))
    (ha : (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a)) :
    (cokernel.π (Divisor.divisorialSheafInclusion hle)).app W (unitSection hH W a) = 0 := by
  have hmem : (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) :=
    Divisor.IsDivisorialSection.mono ha (by rw [sub_eq_add_neg]; exact le_add_of_nonneg_left hH)
  have heq : unitSection hH W a = (Divisor.divisorialSheafInclusion hle).app W ⟨_, hmem⟩ :=
    Subtype.ext (coe_unitSection hH W a)
  rw [heq]
  exact cokernel_π_app_app_eq_zero _ _ _

omit [CompactSpace Y] in
private theorem isDivisorialSection_neg_of_cokernel_π_app_eq_zero
    (hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    {W : Y.Opens} (a : Γ(Y, W))
    (ha : (cokernel.π (Divisor.divisorialSheafInclusion hle)).app W (unitSection hH W a) = 0) :
    (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
  obtain ⟨y, hy⟩ := exists_app_eq_of_cokernel_π_app_eq_zero _ _ ha
  have hmem : (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
    rw [← coe_unitSection hH W a, ← hy]
    exact y.2
  exact hann W a hmem

/-- Compatible local functions modulo `𝒪_Y(-G)` agree, near `z`, with a pull-back from `Z`. -/
private theorem exists_isDivisorialSection_sub_app_of_epi {Z : Scheme.{0}} (f : Y ⟶ Z)
    (hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (H - G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    [Epi ((Scheme.Modules.pushforward f).map (cokernel.π (Divisor.divisorialSheafInclusion hle)))]
    (hsurj : ∀ U : Z.Opens, Function.Surjective fun r : Γ(Z, U) =>
      unitSection hH (f ⁻¹ᵁ U) (f.app U r))
    {U : Z.Opens} {z : Z} (hzU : z ∈ U) {ι : Type} (V : ι → Y.Opens)
    (hV : ∀ i, V i ≤ f ⁻¹ᵁ U) (hcov : f ⁻¹ᵁ U ≤ ⨆ i, V i) (a : ∀ i, Γ(Y, V i))
    (hcompat : ∀ i j, (-G).IsDivisorialSection (V i ⊓ V j)
      ((toRationalFunctionsPresheaf Y).app (op (V i ⊓ V j))
        (Y.presheaf.map (homOfLE inf_le_left).op (a i) -
          Y.presheaf.map (homOfLE inf_le_right).op (a j)))) :
    ∃ (U' : Z.Opens) (_ : U' ≤ U), z ∈ U' ∧ ∃ r : Γ(Z, U'), ∀ i,
      (-G).IsDivisorialSection (V i ⊓ f ⁻¹ᵁ U')
        ((toRationalFunctionsPresheaf Y).app (op (V i ⊓ f ⁻¹ᵁ U'))
          (Y.presheaf.map (homOfLE inf_le_left).op (a i) -
            Y.presheaf.map (homOfLE inf_le_right).op (f.app U' r))) := by
  classical
  set incl := Divisor.divisorialSheafInclusion hle
  set π := cokernel.π incl
  let τ : ∀ i, Γ(cokernel incl, V i) := fun i => π.app (V i) (unitSection hH (V i) (a i))
  have hτres : ∀ i (W : Y.Opens) (hW : W ≤ V i), (cokernel incl).presheaf.map (homOfLE hW).op
      (τ i) = π.app W (unitSection hH W (Y.presheaf.map (homOfLE hW).op (a i))) := by
    intro i W hW
    rw [← app_presheaf_map_apply, presheaf_map_unitSection]
  have hcomp : TopCat.Presheaf.IsCompatible (cokernel incl).presheaf V τ := by
    intro i j
    change (cokernel incl).presheaf.map (homOfLE inf_le_left).op (τ i) =
      (cokernel incl).presheaf.map (homOfLE inf_le_right).op (τ j)
    rw [hτres, hτres, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact cokernel_π_app_unitSection_eq_zero hH hle _ (hcompat i j)
  obtain ⟨τg, hτg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(cokernel incl).presheaf, (cokernel incl).isSheaf⟩ : TopCat.Sheaf Ab Y) V (f ⁻¹ᵁ U)
    (fun i => homOfLE (hV i)) hcov τ hcomp
  obtain ⟨U', hU', hzU', x, hx⟩ :=
    exists_app_eq_map_of_epi ((Scheme.Modules.pushforward f).map π)
      (N := (Scheme.Modules.pushforward f).obj (cokernel incl)) τg hzU
  obtain ⟨r, rfl⟩ := hsurj U' x
  refine ⟨U', hU', hzU', r, fun i => ?_⟩
  have hτg' : (cokernel incl).presheaf.map (homOfLE (hV i)).op τg = τ i := hτg i
  have hx' : π.app (f ⁻¹ᵁ U') (unitSection hH (f ⁻¹ᵁ U') (f.app U' r)) =
      (cokernel incl).presheaf.map (homOfLE (f.preimage_mono hU')).op τg := hx
  have hWy : V i ⊓ f ⁻¹ᵁ U' ≤ V i := inf_le_left
  have hWU' : V i ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U' := inf_le_right
  refine isDivisorialSection_neg_of_cokernel_π_app_eq_zero hH hle hann _ ?_
  rw [map_sub, map_sub, sub_eq_zero, ← hτres i _ hWy, ← hτg', ← presheaf_map_unitSection,
    app_presheaf_map_apply π, hx',
    presheaf_map_map_apply _ _ _ (homOfLE (hWy.trans (hV i))).op,
    presheaf_map_map_apply _ _ _ (homOfLE (hWy.trans (hV i))).op]

end Cokernel

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

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

/-- **The discrepancy of a non-exceptional divisor.** If a prime divisor `E` of a model
`g : Y ⟶ X` has its centre in codimension one, then `g` maps its generic point to that of a prime
divisor `P` of `X`, and the discrepancy of `E` with respect to `(X, D)` is `-D(P)`. -/
private theorem exists_eq_neg_coeff_of_not_two_le_codimension {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) [IsLocallyNoetherian Y]
    [IsNormal Y] {g : Y ⟶ X}
    [IsProper g]
    (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g) (E : Mori.PrimeDivisor Y)
    (hc : ¬ 2 ≤ codimension (⟨Y, g, hY, hgb, E⟩ : DivisorOver k sX).center) {n : ℕ}
    {K : Divisor X} {D : QDivisor X} {a : ℝ}
    (ha : MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation a) :
    ∃ P : Mori.PrimeDivisor X, g.base E.genericPoint = P.genericPoint ∧ a = -(D.coeff P : ℝ) := by
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
  push Not at hc
  obtain ⟨P, hv⟩ := hc
  set DE : ProperDivisorOver k sX := ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance
  have hvP : DE.valuation = P.divisorialValuation := by
    change DE.toDivisorOver.valuation = _
    rw [hv]
    ext φ
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  have hDP := (hvP ▸ ha).eq_neg_coeff
  rw [QDivisor.coeff_toRDivisor] at hDP
  exact ⟨P, MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv, hDP⟩

/-- **FA 17.4.3 for compatible local functions.** In the setting of FA 17.4, with `F` the
reduced part of the discrepancies `≤ -1`, a family of local functions on `Y` which agree along
`⌊F⌋` agrees along `⌊F⌋`, near any point `z` of `Z`, with the pull-back of a function on `Z`. -/
private theorem exists_isDivisorialSection_sub_app_of_isDiscrepancy
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
    : ∃ F : QDivisor Y, (∀ E, F.coeff E = if e E ≤ -1 then -e E else 0) ∧
      ∀ {U : Z.Opens} {z : Z} (_ : z ∈ U) {ι : Type} (V : ι → Y.Opens)
        (_ : ∀ i, V i ≤ (g ≫ h) ⁻¹ᵁ U) (_ : (g ≫ h) ⁻¹ᵁ U ≤ ⨆ i, V i) (a : ∀ i, Γ(Y, V i)),
        (∀ i j, (-F.roundDown).IsDivisorialSection (V i ⊓ V j)
          ((toRationalFunctionsPresheaf Y).app (op (V i ⊓ V j))
            (Y.presheaf.map (homOfLE inf_le_left).op (a i) -
              Y.presheaf.map (homOfLE inf_le_right).op (a j)))) →
        ∃ (U' : Z.Opens) (_ : U' ≤ U), z ∈ U' ∧ ∃ r : Γ(Z, U'), ∀ i,
          (-F.roundDown).IsDivisorialSection (V i ⊓ (g ≫ h) ⁻¹ᵁ U')
            ((toRationalFunctionsPresheaf Y).app (op (V i ⊓ (g ≫ h) ⁻¹ᵁ U'))
              (Y.presheaf.map (homOfLE inf_le_left).op (a i) -
                Y.presheaf.map (homOfLE inf_le_right).op ((g ≫ h).app U' r))) := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant g := hgb.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdivω : divisorOfForm ω = K := by
    ext Γ
    rw [coeff_divisorOfForm, hωK]
  obtain ⟨m₀, hm₀, N, hNM, hNc⟩ : ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ N : Divisor X,
      Divisor.toQDivisor N = (m₀ : ℚ) • -(Divisor.toQDivisor K + D) ∧ N.IsCartier := by
    refine ⟨_, QDivisor.cartierIndex_pos hKD, ?_⟩
    obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hKD
    refine ⟨-D₀, ?_, hD₀c.neg⟩
    rw [map_neg, hD₀, smul_neg, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g N
  set Q : QDivisor Y := Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX g ω)) +
    (m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB) with hQ_def
  have hQ : ∀ E, Q.coeff E = e E := fun E => by
    rw [eq_ordForm_add_coeff_pullback_of_isDiscrepancy hX hY hgb hω0 hdivω hm₀ hNc hNM hNB E
      (he E), hQ_def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, smul_eq_mul]
  let F : QDivisor Y := Finsupp.onFinset Q.support (fun E => if e E ≤ -1 then -e E else 0)
    (fun E hE => Finsupp.mem_support_iff.mpr fun h0 => hE (by
      rw [← DivisorWithCoeffs.coeff_apply, hQ] at h0
      rw [h0]; norm_num))
  have hF : ∀ E, F.coeff E = if e E ≤ -1 then -e E else 0 := fun E => rfl
  have hF0 : ∀ E, F.coeff E ≠ 0 → e E ≤ -1 := fun E hE => by
    by_contra h'
    exact hE (by rw [hF, ite_eq_right h'])
  have hF1 : ∀ E, F.coeff E ≠ 0 → 1 ≤ F.coeff E := fun E hE => by
    rw [hF, ite_eq_left (hF0 E hE)]
    linarith [hF0 E hE]
  let A : QDivisor Y := Finsupp.onFinset Q.support (fun E => if -1 < e E then e E else 0)
    (fun E hE => Finsupp.mem_support_iff.mpr fun h0 => hE (by
      rw [← DivisorWithCoeffs.coeff_apply, hQ] at h0
      rw [h0, ite_self]))
  have hA : ∀ E, A.coeff E = if -1 < e E then e E else 0 := fun E => rfl
  have hAF : ∀ E, F.coeff E ≠ 0 → A.coeff E = 0 := fun E hE => by
    rw [hA, ite_eq_right (not_lt.mpr (hF0 E hE))]
  have hH : 0 ≤ A.roundUp := fun E => by
    change (0 : ℤ) ≤ A.roundUp.coeff E
    rw [DivisorWithCoeffs.coeff_roundUp, hA]
    split_ifs with h1
    · have := Int.lt_ceil.mpr (show ((-1 : ℤ) : ℚ) < e E by push_cast; exact h1)
      omega
    · simp
  have hG : 0 ≤ F.roundDown := fun E => by
    change (0 : ℤ) ≤ F.roundDown.coeff E
    rw [DivisorWithCoeffs.coeff_roundDown]
    by_cases hE : F.coeff E = 0
    · rw [hE, Int.floor_zero]
    · exact Int.floor_nonneg.mpr (zero_le_one.trans (hF1 E hE))
  have hle : A.roundUp - F.roundDown ≤ A.roundUp := sub_le_self _ hG
  have hepi := epi_pushforward_cokernel_π_divisorialSheafInclusion_roundUp_sub_roundDown hZ hX hhs
    hfib hK hKD hneg hnef hbig hg hY hgb e he hA hF hle
  have hcomp : ∀ E : Mori.PrimeDivisor Y, A.roundUp E ≠ 0 →
      IsExceptionalPrimeDivisor (h ≫ sZ) g E ∨ 2 ≤ Order.coheight (h (g E.genericPoint)) := by
    intro E hE
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
    obtain ⟨P, hgen, hDP⟩ := exists_eq_neg_coeff_of_not_two_le_codimension hX hY hgb E hc (he E)
    rw [hgen]
    refine hneg P ?_
    have : (D.coeff P : ℝ) < 0 := by
      have : (0 : ℝ) < e E := by exact_mod_cast hpos
      linarith
    exact_mod_cast this
  have hbij := bijective_structureSheafToDivisorialSheaf_app_comp sZ h g hZ (hhs ▸ hX)
    (by rw [hhs]; exact hY) hfib hgb A.roundUp hH hcomp
  have hann : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      (A.roundUp - F.roundDown).IsDivisorialSection W
          ((toRationalFunctionsPresheaf Y).app (op W) a) →
        (-F.roundDown).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
    intro W a ha E hE
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
  refine ⟨F, hF, ?_⟩
  intro U z hzU ι V hV hcov a hcompat
  exact exists_isDivisorialSection_sub_app_of_epi hH hle (g ≫ h) hann (fun U => (hbij U).2) hzU V
    hV hcov a hcompat

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips

private theorem coeff_le_one_of_isLcPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) (E : Mori.PrimeDivisor X) :
    Δ.coeff E ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hX := h.1.1
  have hex := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair h.1.2.1
    (DivisorOver.ofPrimeDivisor ℂ hX E)
  have htot := totalDiscrep_le_neg_coeff hX hex
  have hc : (((-Δ.coeff E : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -Δ.coeff E < -1))
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd
    (htot.trans_lt (hc.trans_eq (by norm_num)))] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

private theorem isExceptional_iff_two_le_coheight' {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- **The discrepancies of an lc surface pair on a model.** Every prime divisor `E` of a proper
birational model `g : Y ⟶ V` has a discrepancy `e(E) = a(E, V, B)`, in the sense of *Flips and
abundance*, and `e(E) ≥ -1`. -/
private theorem exists_isDiscrepancy_family {V Y : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) [IsLocallyNoetherian Y]
    [IsNormal Y] {g : Y ⟶ V} [IsProper g] (hY : IsNormalVariety ℂ (g ≫ sV))
    (hgb : IsBirationalMorphism g) :
    ∃ e : Mori.PrimeDivisor Y → ℚ,
      (∀ E, IsDiscrepancy sV 2 K (QDivisor.toRDivisor B)
        (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E)) ∧
      ∀ E, -1 ≤ e E := by
  have hX := hlc.1.1
  have hK := hlc.1.2.1
  have hKD := hlc.1.2.2
  choose e he using fun E => MMP.Positivity.IsPair.exists_isDiscrepancy hlc.isPair hK
    (⟨Y, g, hY, hgb, E⟩ : DivisorOver ℂ sV)
  have hF : ∀ E, IsDiscrepancy sV 2 K (QDivisor.toRDivisor B)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E) := fun E => by
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (he E)
      (inferInstance : IsProper g)
    have h2 := MMP.Fourfold.isDiscrepancy_of_isLogDiscrepancy hX hK
      (isCartierCombination_toRDivisor_add hKD)
      (E := ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance) h1
    rwa [add_sub_cancel_left] at h2
  refine ⟨e, hF, fun E => ?_⟩
  by_cases hex : (⟨Y, g, hY, hgb, E⟩ : DivisorOver ℂ sV).IsExceptional
  · have h1 := discrep_le hex (he E)
    have h2 := (hlc.2).trans h1
    have : ((-1 : ℝ) : EReal) ≤ ((e E : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · set D : DivisorOver ℂ sV := ⟨Y, g, hY, hgb, E⟩
    have hc : ¬ 2 ≤ codimension D.center := by
      rw [MMP.Positivity.DivisorOver.codimension_center, ← isExceptional_iff_two_le_coheight' hX]
      exact hex
    obtain ⟨P, -, hDP⟩ := exists_eq_neg_coeff_of_not_two_le_codimension hX hY hgb E hc (hF E)
    have h1 : (B.coeff P : ℝ) ≤ 1 := by exact_mod_cast coeff_le_one_of_isLcPair hlc le_rfl P
    exact_mod_cast (show (-1 : ℝ) ≤ e E by linarith)

end

section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MMP MMP.Mori MMP.Flips

private theorem exists_primeDivisor_map_genericPoint_eq {X' X : Scheme.{0}} [IsIntegral X']
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (μ : X' ⟶ X) [IsProper μ]
    (hμ : MMP.Mori.IsBirationalMorphism μ) (P : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor X', μ E.genericPoint = P.genericPoint ∧
      IsIso (μ.stalkMap E.genericPoint) := by
  have hy := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal μ hμ
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  set W := MMP.Mori.biregularLocus μ
  have : IsIso (μ ∣_ W) := MMP.Mori.isBiregular_biregularLocus μ
  let z : W.toScheme := ⟨P.genericPoint, hy⟩
  let x' : (μ ⁻¹ᵁ W).toScheme := (inv (μ ∣_ W)).base z
  have hx' : (μ ∣_ W).base x' = z := by
    change ((inv (μ ∣_ W)) ≫ (μ ∣_ W)).base z = z
    rw [IsIso.inv_hom_id]; rfl
  have hμx : μ.base ((μ ⁻¹ᵁ W).ι.base x') = P.genericPoint := by
    have := congrArg (fun φ => φ.base x') (morphismRestrict_ι μ W)
    simp only [Scheme.Hom.comp_apply] at this
    rw [← this, hx']
    rfl
  have hcoh : Order.coheight ((μ ⁻¹ᵁ W).ι.base x') = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion (x := x') (μ ⁻¹ᵁ W).ι
    have h2 := coheight_eq_of_isOpenImmersion (x := x') ((μ ∣_ W) ≫ W.ι)
    rw [h1, ← h2, Scheme.Hom.comp_apply, hx']
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have hg : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh) = (μ ⁻¹ᵁ W).ι.base x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, ?_⟩ <;> rw [hg]
  · exact hμx
  · exact MMP.isIso_stalkMap_of_mem_biregularLocus μ (hμx ▸ hy)

private theorem not_isUnit_germ_of_isDivisorialSection_neg {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {G : Divisor Y} {W : Y.Opens} {a : Γ(Y, W)}
    (ha : (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a))
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint ∈ W) (hG : 1 ≤ G.coeff E) :
    ¬ IsUnit (Y.presheaf.germ W E.genericPoint hE a) := by
  intro hunit
  have hEW : (E.support ∩ W).Nonempty := ⟨E.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure (Set.mem_singleton _), hE⟩
  have hval := ha E hEW
  have hgerm : (toRationalFunctionsPresheaf Y).app (op W) a
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEW⟩ =
      E.toComponent.hom (Y.presheaf.germ W _ hE a) :=
    (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint a).symm
  rw [hgerm] at hval
  rcases hval with h0 | hv
  · exact (hunit.map E.toComponent.hom).ne_zero h0
  · rw [E.valuation_toComponent_of_isUnit hunit, DivisorWithCoeffs.coeff_neg, neg_neg,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
    omega

private theorem eq_zero_of_forall_exists_specializes_not_isUnit_germ {X : Scheme.{0}} [IsReduced X]
    {O : X.Opens} (s : Γ(X, O))
    (h : ∀ x ∈ O, ∃ (η : X) (hη : η ∈ O), η ⤳ x ∧ ¬ IsUnit (X.presheaf.germ O η hη s)) :
    s = 0 := by
  rw [← basicOpen_eq_bot_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨η, hη, hsp, hnu⟩ := h x (X.basicOpen_le s hx)
  exact hnu ((X.mem_basicOpen s η hη).mp (hsp.mem_open (X.basicOpen s).isOpen hx))

private theorem isClosed_singleton_of_two_le_coheight {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    (hn : topologicalKrullDim X = 2) {x : X} (hx : 2 ≤ Order.coheight x) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hsp : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hlt : y < x := lt_of_le_of_ne hsp (fun h => hne (Set.mem_singleton_iff.mpr
    (Inseparable.eq (show Inseparable x y from h)).symm))
  have h1 : Order.coheight x + 1 ≤ Order.coheight y := Order.coheight_add_one_le hlt
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX y
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {y} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h2 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ 2 := by
    rw [← h]; exact le_add_of_nonneg_left h0
  have h3 : Order.coheight y ≤ 2 := by
    have : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := h2
    exact WithBot.coe_le_coe.mp this
  have h4 : (2 : ℕ∞) + 1 ≤ Order.coheight x + 1 := by gcongr
  have : (3 : ℕ∞) ≤ 2 := (show (3 : ℕ∞) = 2 + 1 by norm_num) ▸ (h4.trans h1).trans h3
  exact absurd this (by decide)

private theorem ordGE_one_toComponent_of_mem_maximalIdeal {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {β : E.localRing}
    (hβ : β ∈ IsLocalRing.maximalIdeal E.localRing) :
    E.OrdGE 1 (E.toComponent.hom β) := by
  have := E.isDiscreteValuationRing_localRing
  by_cases h0 : β = 0
  · subst h0
    exact Or.inl (map_zero _)
  right
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at hβ
  obtain ⟨γ, rfl⟩ := hβ
  have hγ : γ ≠ 0 := fun hγ => h0 (by rw [hγ, zero_mul])
  rw [map_mul, map_mul, E.valuation_toComponent_of_irreducible hϖ]
  exact le_mul_of_one_le_left' (E.one_le_valuation_toComponent hγ)

private theorem isDivisorialSection_neg_of_germ_mem_maximalIdeal {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {G : Divisor Y}
    (hG : ∀ E, G.coeff E = 0 ∨ G.coeff E = 1) {W : Y.Opens} (a : Γ(Y, W))
    (h : ∀ E : MMP.Mori.PrimeDivisor Y, G.coeff E = 1 → ∀ hE : E.genericPoint ∈ W,
      Y.presheaf.germ W E.genericPoint hE a ∈ IsLocalRing.maximalIdeal _) :
    (-G).IsDivisorialSection W ((toRationalFunctionsPresheaf Y).app (op W) a) := by
  intro E hEW
  have hE := E.genericPoint_mem_of_nonempty hEW
  have hgerm : (toRationalFunctionsPresheaf Y).app (op W) a
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEW⟩ =
      E.toComponent.hom (Y.presheaf.germ W _ hE a) :=
    (TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hE E.specializes_genericPoint a).symm
  rcases hG E with h0 | h1
  · have hreg : (0 : Divisor Y).IsDivisorialSection W
        ((toRationalFunctionsPresheaf Y).app (op W) a) :=
      Divisor.isDivisorialSection_algebraMap le_rfl a
    have := hreg E hEW
    rw [DivisorWithCoeffs.coeff_neg, h0]
    simpa using this
  · rw [DivisorWithCoeffs.coeff_neg, h1, neg_neg, hgerm]
    exact ordGE_one_toComponent_of_mem_maximalIdeal E (h E h1 hE)

end

section L3

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MMP MMP.Mori MMP.Flips

/-- **`𝒪_{V'} → h_* 𝒪_{⌊B⌋}` is locally onto**, from FA 17.4.3. -/
private theorem exists_app_eq_of_floor_global {V V' : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sV' : V' ⟶ Spec (.of ℂ)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] [LocallyOfFiniteType sV] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    (hV'n : IsNormalVariety ℂ sV') (h : V ⟶ V') (hhs : h ≫ sV' = sV) [IsProper h]
    [Surjective h] (hfib : ∀ z : V', _root_.IsConnected (h ⁻¹' {z}))
    (hnef : (-(Divisor.toQDivisor K + B)).IsRelativelyNef sV h)
    (hbig : IsRelativelyBigOnGenericFiber h ℂ sV sV' (-(Divisor.toQDivisor K + B)))
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (W : V'.Opens) (g₀ : Γ(C, ι ⁻¹ᵁ (h ⁻¹ᵁ W))) {y : V'} (hy : y ∈ W) :
    ∃ (W₁ : V'.Opens) (hW₁ : W₁ ≤ W), y ∈ W₁ ∧ ∃ b : Γ(V', W₁),
      ι.app (h ⁻¹ᵁ W₁) (h.app W₁ b) =
        C.presheaf.map (homOfLE (ι.preimage_mono (h.preimage_mono hW₁))).op g₀ := by
  classical
  have hX : IsNormalVariety ℂ sV := hlc.1.1
  have hK := hlc.1.2.1
  have hKD := hlc.1.2.2
  have hn : topologicalKrullDim V = 2 := hK.topologicalKrullDim_eq
  have hneg : ∀ P : Mori.PrimeDivisor V, B.coeff P < 0 → 2 ≤ Order.coheight (h P.genericPoint) :=
    fun P hP => absurd hP (not_lt.mpr (hB P))
  obtain ⟨Y, gY, hg, hres⟩ := exists_isLogResolution_reducedDivisor (k := ℂ) hn hX B
  have hsr : IsSmoothResolution sV gY :=
    ⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  have : IsProper gY := hres.isProjective.isProper
  have : IsNormal Y := hsr.isNormal
  have : IsIntegral Y := hsr.isIntegral
  have hY : IsNormalVariety ℂ (gY ≫ sV) := (hsr.isNormalVariety hX).1
  have : IsLocallyNoetherian Y := hY.isLocallyNoetherian
  have hgb := hres.isBirationalMorphism
  obtain ⟨e, he, he1⟩ := exists_isDiscrepancy_family hlc hY hgb
  obtain ⟨F, hF, hlift⟩ := exists_isDivisorialSection_sub_app_of_isDiscrepancy hV'n hX hhs hfib
    hK hKD hneg hnef hbig hg hY hgb e he
  have hFl : ∀ E, F.roundDown.coeff E = if e E ≤ -1 then 1 else 0 := by
    intro E
    rw [DivisorWithCoeffs.coeff_roundDown, hF]
    split_ifs with h1
    · have : e E = -1 := le_antisymm h1 (he1 E)
      rw [this]; norm_num
    · simp
  have hG01 : ∀ E, F.roundDown.coeff E = 0 ∨ F.roundDown.coeff E = 1 := fun E => by
    rw [hFl]; split_ifs <;> simp
  have hcls : ∀ E : Mori.PrimeDivisor Y, e E ≤ -1 →
      gY.base E.genericPoint ∈ Set.range ι.base ∨
        2 ≤ Order.coheight (gY.base E.genericPoint) := by
    intro E hE
    set D : DivisorOver ℂ sV := ⟨Y, gY, hY, hgb, E⟩
    by_cases hex : D.IsExceptional
    · exact Or.inr ((isExceptional_iff_two_le_coheight' hX D).mp hex)
    · left
      have hc : ¬ 2 ≤ codimension D.center := by
        rw [MMP.Positivity.DivisorOver.codimension_center, ← isExceptional_iff_two_le_coheight' hX]
        exact hex
      obtain ⟨P, hgen, hDP⟩ := exists_eq_neg_coeff_of_not_two_le_codimension hX hY hgb E hc (he E)
      have hcoef : 1 ≤ B.coeff P := by
        have h1 : ((e E : ℚ) : ℝ) ≤ -1 := by exact_mod_cast hE
        have : (1 : ℝ) ≤ B.coeff P := by linarith
        exact_mod_cast this
      rw [hC, hgen]
      refine Set.mem_biUnion (x := P) ?_ ?_
      · rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro h0
        have h0' : (B.roundDown).coeff P = 0 := h0
        rw [DivisorWithCoeffs.coeff_roundDown] at h0'
        have := Int.le_floor.mpr (show ((1 : ℤ) : ℚ) ≤ B.coeff P by exact_mod_cast hcoef)
        omega
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
  let T : Set V :=
    (fun E : Mori.PrimeDivisor Y => gY.base E.genericPoint) '' {E | e E ≤ -1} \ Set.range ι.base
  have hTfin : T.Finite := by
    refine Set.Finite.subset (Set.Finite.image _ ((F.support.finite_toSet).subset ?_))
      Set.sdiff_subset
    intro E hE
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    have h0' : F.coeff E = 0 := h0
    have hE' : e E ≤ -1 := hE
    rw [hF, ite_eq_left hE'] at h0'
    linarith
  have hTcl : IsClosed T := by
    have hT : T = ⋃ v ∈ T, ({v} : Set V) := by simp
    rw [hT]
    refine hTfin.isClosed_biUnion fun v hv => ?_
    obtain ⟨⟨E, hE, rfl⟩, hvC⟩ := hv
    exact isClosed_singleton_of_two_le_coheight (sX := sV) hn ((hcls E hE).resolve_left hvC)
  have hrangecl : IsClosed (Set.range ι.base) := ι.isClosedEmbedding.isClosed_range
  have hdata : ∀ p : {p : Y // gY.base p ∈ h ⁻¹ᵁ W}, ∃ (O : V.Opens) (hO : O ≤ h ⁻¹ᵁ W),
      gY.base p.1 ∈ O ∧ ∃ g : Γ(V, O),
        ((O : Set V) ⊆ Tᶜ ∧ ι.app O g = C.presheaf.map (homOfLE (ι.preimage_mono hO)).op g₀) ∨
        ((O : Set V) ⊆ (Set.range ι.base)ᶜ ∧ g = 0) := by
    rintro ⟨p, hp⟩
    by_cases hpC : gY.base p ∈ Set.range ι.base
    · obtain ⟨O, hOaff, hpO, hOle⟩ := exists_isAffineOpen_mem_and_subset
        (U := h ⁻¹ᵁ W ⊓ ⟨Tᶜ, hTcl.isOpen_compl⟩)
        (show gY.base p ∈ h ⁻¹ᵁ W ⊓ ⟨Tᶜ, hTcl.isOpen_compl⟩ from ⟨hp, fun hT => hT.2 hpC⟩)
      have hOW : O ≤ h ⁻¹ᵁ W := fun x hx => (hOle hx).1
      obtain ⟨g, hg⟩ := ι.app_surjective O hOaff
        (C.presheaf.map (homOfLE (ι.preimage_mono hOW)).op g₀)
      exact ⟨O, hOW, hpO, g, Or.inl ⟨fun x hx => (hOle hx).2, hg⟩⟩
    · exact ⟨h ⁻¹ᵁ W ⊓ ⟨(Set.range ι.base)ᶜ, hrangecl.isOpen_compl⟩, inf_le_left, ⟨hp, hpC⟩, 0,
        Or.inr ⟨fun x hx => hx.2, rfl⟩⟩
  choose O hO hpO gl hgl using hdata
  let ιd := {p : Y // gY.base p ∈ h ⁻¹ᵁ W}
  let Vi : ιd → Y.Opens := fun i => gY ⁻¹ᵁ O i
  let ai : ∀ i, Γ(Y, Vi i) := fun i => gY.app (O i) (gl i)
  have hVi : ∀ i, Vi i ≤ (gY ≫ h) ⁻¹ᵁ W := fun i => gY.preimage_mono (hO i)
  have hcov : (gY ≫ h) ⁻¹ᵁ W ≤ ⨆ i, Vi i := fun p hp =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpO _⟩
  -- the germ of `gl i - gl j` at a point `v` of `O i ⊓ O j` on a component of `⌊F⌋`
  have hdiff : ∀ (i j : ιd) (E : Mori.PrimeDivisor Y), e E ≤ -1 →
      ∀ hv : gY.base E.genericPoint ∈ O i ⊓ O j,
      V.presheaf.germ (O i ⊓ O j) _ hv
        (V.presheaf.map (homOfLE inf_le_left).op (gl i) -
          V.presheaf.map (homOfLE inf_le_right).op (gl j)) ∈ IsLocalRing.maximalIdeal _ := by
    intro i j E hE hv
    by_cases hr : gY.base E.genericPoint ∈ Set.range ι.base
    · obtain ⟨c, hc⟩ := hr
      have hi := (hgl i).resolve_right fun h' => h'.1 hv.1 ⟨c, hc⟩
      have hj := (hgl j).resolve_right fun h' => h'.1 hv.2 ⟨c, hc⟩
      revert hv
      rw [← hc]
      intro hv
      have h0 : ι.app (O i ⊓ O j) (V.presheaf.map (homOfLE inf_le_left).op (gl i) -
          V.presheaf.map (homOfLE inf_le_right).op (gl j)) = 0 := by
        rw [map_sub, app_map_apply, app_map_apply, hi.2, hj.2, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact sub_eq_zero.mpr rfl
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (ι.stalkMap c).hom
      rw [Scheme.Hom.germ_stalkMap_apply, h0, map_zero] at hu'
      exact not_isUnit_zero hu'
    · have hvT : gY.base E.genericPoint ∈ T := ⟨⟨E, hE, rfl⟩, hr⟩
      have hi := (hgl i).resolve_left fun h' => h'.1 hv.1 hvT
      have hj := (hgl j).resolve_left fun h' => h'.1 hv.2 hvT
      rw [hi.2, hj.2, map_zero, map_zero, sub_zero, map_zero]
      exact Ideal.zero_mem _
  have hcompat : ∀ i j, (-F.roundDown).IsDivisorialSection (Vi i ⊓ Vi j)
      ((toRationalFunctionsPresheaf Y).app (op (Vi i ⊓ Vi j))
        (Y.presheaf.map (homOfLE inf_le_left).op (ai i) -
          Y.presheaf.map (homOfLE inf_le_right).op (ai j))) := by
    intro i j
    refine isDivisorialSection_neg_of_germ_mem_maximalIdeal hG01 _ fun E hE1 hEm => ?_
    have hE : e E ≤ -1 := by
      rw [hFl] at hE1
      split_ifs at hE1 with h'
      · exact h'
      · simp at hE1
    have hv : gY.base E.genericPoint ∈ O i ⊓ O j := hEm
    have hx := hdiff i j E hE hv
    have heq : Y.presheaf.germ (Vi i ⊓ Vi j) _ hEm
        (Y.presheaf.map (homOfLE inf_le_left).op (ai i) -
          Y.presheaf.map (homOfLE inf_le_right).op (ai j)) =
        (gY.stalkMap _).hom (V.presheaf.germ (O i ⊓ O j) _ hv
          (V.presheaf.map (homOfLE inf_le_left).op (gl i) -
            V.presheaf.map (homOfLE inf_le_right).op (gl j))) := by
      rw [Scheme.Hom.germ_stalkMap_apply, map_sub, map_sub, app_map_apply, app_map_apply,
        map_sub]
      simp only [TopCat.Presheaf.germ_res_apply]
      congr 1 <;> exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    rw [heq]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit _ _ hu)
  obtain ⟨W₁, hW₁, hyW₁, r, hr⟩ := hlift hy Vi hVi hcov ai hcompat
  refine ⟨W₁, hW₁, hyW₁, r, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists_specializes_not_isUnit_germ _ fun x hx => ?_
  have hxC : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
  rw [hC] at hxC
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hxC
  have hηC : P.genericPoint ∈ Set.range ι.base := by
    rw [hC]
    refine Set.mem_biUnion hP ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨c, hc⟩ := hηC
  have hcx : c ⤳ x := by
    rw [← ι.isClosedEmbedding.isInducing.specializes_iff, hc]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
    exact specializes_iff_mem_closure.mpr hxP
  have hcO : c ∈ ι ⁻¹ᵁ (h ⁻¹ᵁ W₁) := hcx.mem_open (ι ⁻¹ᵁ (h ⁻¹ᵁ W₁)).isOpen hx
  refine ⟨c, hcO, hcx, ?_⟩
  obtain ⟨E, hEgen, -⟩ := exists_primeDivisor_map_genericPoint_eq gY hgb P
  have hpt : gY.base E.genericPoint = ι.base c := hEgen.trans hc.symm
  have hEe : e E ≤ -1 := by
    set D : DivisorOver ℂ sV := ⟨Y, gY, hY, hgb, E⟩
    have hex : ¬ D.IsExceptional := by
      rw [isExceptional_iff_two_le_coheight' hX D]
      change ¬ 2 ≤ Order.coheight (gY.base E.genericPoint)
      rw [hEgen, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      decide
    have hc' : ¬ 2 ≤ codimension D.center := by
      rw [MMP.Positivity.DivisorOver.codimension_center, ← isExceptional_iff_two_le_coheight' hX]
      exact hex
    obtain ⟨P', hgen', hDP⟩ := exists_eq_neg_coeff_of_not_two_le_codimension hX hY hgb E hc' (he E)
    have hPP : P' = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hgen'.symm.trans hEgen)
    subst hPP
    have hfl : (B.roundDown).coeff P' ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [DivisorWithCoeffs.coeff_roundDown] at hfl
    have h1 : (1 : ℚ) ≤ B.coeff P' := by
      by_contra hlt
      push Not at hlt
      exact hfl (Int.floor_eq_zero_iff.mpr ⟨hB P', hlt⟩)
    have : (e E : ℝ) ≤ -1 := by rw [hDP]; have : (1 : ℝ) ≤ B.coeff P' := by exact_mod_cast h1
                                linarith
    exact_mod_cast this
  have hηW : gY.base E.genericPoint ∈ h ⁻¹ᵁ W := by
    rw [hpt]; exact h.preimage_mono hW₁ hcO
  let i : ιd := ⟨E.genericPoint, hηW⟩
  have hi := (hgl i).resolve_right fun h' => h'.1 (hpO i) ⟨c, hpt.symm⟩
  have hEmem : E.genericPoint ∈ Vi i ⊓ (gY ≫ h) ⁻¹ᵁ W₁ :=
    ⟨hpO i, show h.base (gY.base E.genericPoint) ∈ W₁ by rw [hpt]; exact hcO⟩
  have hnu := not_isUnit_germ_of_isDivisorialSection_neg (hr i) E hEmem
    (by rw [hFl, ite_eq_left hEe])
  have hv' : gY.base E.genericPoint ∈ O i ⊓ h ⁻¹ᵁ W₁ := hEmem
  set φ : Γ(V, O i ⊓ h ⁻¹ᵁ W₁) := V.presheaf.map (homOfLE inf_le_left).op (gl i) -
    V.presheaf.map (homOfLE inf_le_right).op (h.app W₁ r) with hφ
  have h1 : ¬ IsUnit (V.presheaf.germ (O i ⊓ h ⁻¹ᵁ W₁) _ hv' φ) := fun hu => hnu (by
    have := hu.map (gY.stalkMap E.genericPoint).hom
    rw [Scheme.Hom.germ_stalkMap_apply, hφ, map_sub, app_map_apply, app_map_apply, map_sub] at this
    rw [map_sub]
    simp only [TopCat.Presheaf.germ_res_apply] at this ⊢
    convert this using 2
    · exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    · exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm)
  revert h1 hv'
  rw [hpt]
  intro hv' h1
  have h2 : ¬ IsUnit (C.presheaf.germ (ι ⁻¹ᵁ (O i ⊓ h ⁻¹ᵁ W₁)) c hv' (ι.app _ φ)) := fun hu =>
    h1 (isUnit_of_map_unit (ι.stalkMap c).hom _ (by rw [Scheme.Hom.germ_stalkMap_apply]; exact hu))
  intro hu
  apply h2
  rw [hφ, map_sub, app_map_apply, app_map_apply, hi.2, map_sub]
  simp only at hu ⊢
  rw [map_sub] at hu
  have := hu.neg
  rw [neg_sub] at this
  convert this using 2
  · exact (TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE _) c hv' _).trans
      ((TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE _) c _ g₀).trans
        (TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE _) c hcO g₀).symm)
  · exact TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE _) c hv' _

end L3

section Transl

open CategoryTheory AlgebraicGeometry Opposite

private theorem exists_app_eq_restrict_of_global {V V' C : Scheme.{0}} (h : V ⟶ V') (ι : C ⟶ V)
    (U' : V'.Opens) (V₀ : U'.toScheme.Opens)
    (g : Γ((ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme, (ι ∣_ (h ⁻¹ᵁ U')) ⁻¹ᵁ ((h ∣_ U') ⁻¹ᵁ V₀)))
    (y : U'.toScheme)
    (H : ∀ g₀ : Γ(C, ι ⁻¹ᵁ (h ⁻¹ᵁ (U'.ι ''ᵁ V₀))), ∃ (W₁ : V'.Opens) (hW₁ : W₁ ≤ U'.ι ''ᵁ V₀),
      U'.ι.base y ∈ W₁ ∧ ∃ b : Γ(V', W₁), ι.app (h ⁻¹ᵁ W₁) (h.app W₁ b) =
        C.presheaf.map (homOfLE (ι.preimage_mono (h.preimage_mono hW₁))).op g₀) :
    ∃ (V₁ : U'.toScheme.Opens) (hV₁ : V₁ ≤ V₀), y ∈ V₁ ∧ ∃ b : Γ(U'.toScheme, V₁),
      (ι ∣_ (h ⁻¹ᵁ U')).app ((h ∣_ U') ⁻¹ᵁ V₁) ((h ∣_ U').app V₁ b) =
        (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme.presheaf.map
          (homOfLE ((ι ∣_ (h ⁻¹ᵁ U')).preimage_mono ((h ∣_ U').preimage_mono hV₁))).op g := by
  have hE : (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).ι ''ᵁ ((ι ∣_ (h ⁻¹ᵁ U')) ⁻¹ᵁ ((h ∣_ U') ⁻¹ᵁ V₀)) =
      ι ⁻¹ᵁ (h ⁻¹ᵁ (U'.ι ''ᵁ V₀)) := by
    rw [image_morphismRestrict_preimage, image_morphismRestrict_preimage]
  obtain ⟨W₁, hW₁, hyW₁, b', hb'⟩ := H (C.presheaf.map (eqToHom hE.symm).op g)
  have hV₁ : U'.ι ⁻¹ᵁ W₁ ≤ V₀ := fun x hx => by
    obtain ⟨z, hz, hzx⟩ := hW₁ hx
    rwa [U'.ι.isOpenEmbedding.injective hzx] at hz
  refine ⟨U'.ι ⁻¹ᵁ W₁, hV₁, hyW₁,
    V'.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le U'.ι W₁)).op b', ?_⟩
  have nat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (i : U' ⟶ U) (x : Γ(Y, U)),
      f.app U' (Y.presheaf.map i.op x) =
        X.presheaf.map (homOfLE (f.preimage_mono i.le)).op (f.app U x) :=
    fun f _ _ i x => app_map_apply f i.le x
  rw [morphismRestrict_app, morphismRestrict_app]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  erw [app_map_apply, nat, app_map_apply, hb']
  rw [Scheme.Opens.toScheme_presheaf_map]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  exact congrArg (fun f => (ConcreteCategory.hom (C.presheaf.map f)) g) (Subsingleton.elim _ _)

end Transl

/-- **`𝒪_{V'} → h_* 𝒪_{⌊B⌋}` is onto.** Every function on `⌊B⌋ ∩ h⁻¹(V₀)` is, near each point
of `V₀`, the pull-back of a function on `V'`. Together with the reducedness of `h(⌊B⌋)` this is
`h_* 𝒪_{⌊B⌋} = 𝒪_{h(⌊B⌋)}`; it rests on the connectedness of `⌊B⌋ ∩ h⁻¹(y)` and on the
seminormality of the union `h(⌊B⌋)` of lc centres. -/
private theorem exists_app_eq_of_floor {V V' : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (h : V ⟶ V') (hhs : h ≫ sV' = sV)
    (hV'n : IsNormalVariety ℂ sV') (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hhO : ∀ U : V'.Opens, IsIso (h.app U))
    (hlc' : IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B))
    {k : ℕ} (hk : 0 < k) {L : Divisor V'} (hL : L.IsCartier)
    {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B))
    (hMpb : ∃ hM, L.IsPullback h hM M)
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (U' : V'.Opens) (V₀ : U'.toScheme.Opens)
    (g : Γ((ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme, (ι ∣_ (h ⁻¹ᵁ U')) ⁻¹ᵁ ((h ∣_ U') ⁻¹ᵁ V₀)))
    (y : U'.toScheme) (hy : y ∈ V₀) :
    ∃ (V₁ : U'.toScheme.Opens) (hV₁ : V₁ ≤ V₀), y ∈ V₁ ∧ ∃ b : Γ(U'.toScheme, V₁),
      (ι ∣_ (h ⁻¹ᵁ U')).app ((h ∣_ U') ⁻¹ᵁ V₁) ((h ∣_ U').app V₁ b) =
        (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme.presheaf.map
          (homOfLE ((ι ∣_ (h ⁻¹ᵁ U')).preimage_mono ((h ∣_ U').preimage_mono hV₁))).op g := by
  have := isProper_of_isProjectiveMorphism h hhp
  have hpt : ∀ c : (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme,
      U'.ι.base ((h ∣_ U').base ((ι ∣_ (h ⁻¹ᵁ U')).base c)) = h.base (ι.base c.1) := fun c =>
    (ι_morphismRestrict_apply h U' _).trans (congrArg h.base (ι_morphismRestrict_apply ι _ c))
  by_cases hyW : U'.ι.base y ∈ h.base '' Set.range ι.base
  · by_cases hfin : (h.base ⁻¹' {U'.ι.base y}).Finite
    · -- a finite fibre: `h` is finite near `y`, and functions lift along the closed immersion
      obtain ⟨V₁, hV₁, hyV₁, hOaff⟩ := exists_le_isAffineOpen_preimage_of_finite h U' V₀ y hy hfin
      obtain ⟨a, ha⟩ := (ι ∣_ (h ⁻¹ᵁ U')).app_surjective _ hOaff
        ((ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme.presheaf.map
          (homOfLE ((ι ∣_ (h ⁻¹ᵁ U')).preimage_mono ((h ∣_ U').preimage_mono hV₁))).op g)
      have := isIso_morphismRestrict_app h hhO U' V₁
      refine ⟨V₁, hV₁, hyV₁, inv ((h ∣_ U').app V₁) a, ?_⟩
      have hinv : (h ∣_ U').app V₁ (inv ((h ∣_ U').app V₁) a) = a := by
        rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]; rfl
      rw [hinv, ha]
    · -- a positive-dimensional fibre meeting `⌊B⌋`: FA 17.4.3
      refine exists_app_eq_restrict_of_global h ι U' V₀ g y fun g₀ => ?_
      have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
      have : LocallyOfFiniteType sV := hlc.1.1.1.toLocallyOfFiniteType
      have : IsSeparated sV' := hV'n.1.toIsSeparated
      have : LocallyOfFiniteType sV' := hV'n.1.toLocallyOfFiniteType
      have : QuasiCompact sV' := hV'n.1.toQuasiCompact
      have : IsDominant h := hhb.isDominant
      have : Surjective h := Surjective.of_universallyClosed_of_isDominant h
      have hdV : topologicalKrullDim V = (2 : ℕ) := hlc.1.2.1.topologicalKrullDim_eq
      have hdV' : topologicalKrullDim V' = (2 : ℕ) := hlc'.1.2.1.topologicalKrullDim_eq
      exact exists_app_eq_of_floor_global hlc hB hV'n h hhs
        (Scheme.Hom.isConnected_preimage_singleton_of_isIso_app h hhO)
        (isRelativelyNef_neg_of_isPullback h hhs hk hL hMeq hMpb)
        (isRelativelyBigOnGenericFiber_neg_of_isPullback hlc.1.1.1 hV'n.1 h hhs hhO hdV hdV' hk hL
          hMeq hMpb)
        ι hC _ g₀ ⟨y, hy, rfl⟩
  · -- away from `h(⌊B⌋)` the floor is empty and there is nothing to lift
    have hWcl : IsClosed (h.base '' Set.range ι.base) :=
      h.isClosedMap _ ι.isClosedEmbedding.isClosed_range
    let Wc : V'.Opens := ⟨(h.base '' Set.range ι.base)ᶜ, hWcl.isOpen_compl⟩
    refine ⟨V₀ ⊓ U'.ι ⁻¹ᵁ Wc, inf_le_left, ⟨hy, hyW⟩, 0, ?_⟩
    have hbot : (ι ∣_ (h ⁻¹ᵁ U')) ⁻¹ᵁ ((h ∣_ U') ⁻¹ᵁ (V₀ ⊓ U'.ι ⁻¹ᵁ Wc)) = ⊥ := by
      refine le_antisymm (fun c hc => ?_) bot_le
      exfalso
      have hc' : U'.ι.base ((h ∣_ U').base ((ι ∣_ (h ⁻¹ᵁ U')).base c)) ∈
          (Wc : Set V') := hc.2
      rw [hpt] at hc'
      exact hc' ⟨_, ⟨c.1, rfl⟩, rfl⟩
    have : Subsingleton Γ((ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme,
        (ι ∣_ (h ⁻¹ᵁ U')) ⁻¹ᵁ ((h ∣_ U') ⁻¹ᵁ (V₀ ⊓ U'.ι ⁻¹ᵁ Wc))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _

/-- **Descent of powers of floor sections to `h(⌊B⌋)`.** Let `T ⊆ V'` be the reduced closed
subscheme on `h(C) ∪ h(P)` and `Ω` the complement of `h(P)`. For every `r > 0` with `rE = jM`
there is a section `τ` of `𝒪(jL)` on `T ∩ f'⁻¹ U` such that, for every section `τ'` agreeing with
`τ` on `T ∩ Ω`, the pull-back of every extension of `τ'` to `f'⁻¹ U` restricts to `t ^ r` on
`C_U`. Locally on `T ∩ Ω`, write `t ^ r = g · h^*ψ⁻¹` on `C` for a local equation `ψ` of `jL`;
`exists_app_eq_of_floor` writes `g` as the pull-back of a function `b` on `V'`, and `τ` is glued
from the restrictions of `b ψ⁻¹` to `T`. Two such local choices agree on `T`, because a function
on `V' ∖ h(P)` vanishing on `⌊B⌋` vanishes on the reduced scheme `T ∖ h(P) = h(⌊B⌋) ∖ h(P)`. -/
private theorem exists_descent_pow {V V' Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (h : V ⟶ V') (f' : V' ⟶ Z) (hhs : h ≫ sV' = sV)
    (hV'n : IsNormalVariety ℂ sV') (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hhO : ∀ U : V'.Opens, IsIso (h.app U))
    (hlc' : IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B))
    {k : ℕ} (hk : 0 < k) {L : Divisor V'} (hL : L.IsCartier)
    {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B))
    (hMpb : ∃ hM, L.IsPullback h hM M)
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (U : Z.Opens) {E : Divisor V} (hE : E.IsCartier)
    (t : Γ((Scheme.Modules.pullback (ι ∣_ (h ⁻¹ᵁ f' ⁻¹ᵁ U))).obj
        (Divisor.restrictSheaf (h ⁻¹ᵁ f' ⁻¹ᵁ U) E), ⊤))
    (P : Finset (h ⁻¹ᵁ f' ⁻¹ᵁ U).toScheme)
    (hdisj : Disjoint (h.base '' ((h ⁻¹ᵁ f' ⁻¹ᵁ U).ι.base '' (P : Set _)))
      (h.base '' (Set.range ι.base ∩ (h ⁻¹ᵁ f' ⁻¹ᵁ U : Set V))))
    (Tc : TopologicalSpace.Closeds V')
    (hTc : (Tc : Set V') = h.base '' Set.range ι.base ∪
      h.base '' ((h ⁻¹ᵁ f' ⁻¹ᵁ U).ι.base '' (P : Set _)))
    (Ω : V'.Opens)
    (hΩ : (Ω : Set V') = (h.base '' ((h ⁻¹ᵁ f' ⁻¹ᵁ U).ι.base '' (P : Set _)))ᶜ)
    {r j : ℕ} (hrj : r • E = j • M) :
    ∃ τ : Γ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
        (f' ⁻¹ᵁ U))).obj (Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L)), ⊤),
      ∀ τ' : Γ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
          (f' ⁻¹ᵁ U))).obj (Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L)), ⊤),
        ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
          (f' ⁻¹ᵁ U))).obj (Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L))).presheaf.map
            (homOfLE (le_top : ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
              (f' ⁻¹ᵁ U)) ⁻¹ᵁ ((f' ⁻¹ᵁ U).ι ⁻¹ᵁ Ω) ≤ ⊤)).op τ' =
          ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
          (f' ⁻¹ᵁ U))).obj (Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L))).presheaf.map
            (homOfLE (le_top : ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_
              (f' ⁻¹ᵁ U)) ⁻¹ᵁ ((f' ⁻¹ᵁ U).ι ⁻¹ᵁ Ω) ≤ ⊤)).op τ →
      ∀ σ : Γ(Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L), ⊤),
        ((Scheme.Modules.pullbackPushforwardAdjunction
          ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_ (f' ⁻¹ᵁ U))).unit.app
            (Divisor.restrictSheaf (f' ⁻¹ᵁ U) (j • L))).app ⊤ σ = τ' →
        ∀ s : Γ(Divisor.restrictSheaf (h ⁻¹ᵁ f' ⁻¹ᵁ U) (r • E), ⊤),
          IsPullbackSection h (f' ⁻¹ᵁ U) σ s → LiftsPow ι (h ⁻¹ᵁ f' ⁻¹ᵁ U) t r s := by
  classical
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨hM, hpb⟩ := hMpb
  have hpbj := isPullback_nsmul_of_eq hL hpb hrj
  have := hhb.isDominant
  let U' := f' ⁻¹ᵁ U
  let iT := (Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι
  let iTU := iT ∣_ U'
  let jι := ι ∣_ (h ⁻¹ᵁ U')
  let h' := h ∣_ U'
  let F := Divisor.restrictSheaf U' (j • L)
  let G := Divisor.restrictSheaf (h ⁻¹ᵁ U') (r • E)
  let N := (Scheme.Modules.pullback iTU).obj F
  let PG := (Scheme.Modules.pullback jι).obj G
  let ΩU : U'.toScheme.Opens := U'.ι ⁻¹ᵁ Ω
  have hFinv : Stacks.Ample.IsInvertibleModule _ F :=
    Divisor.isInvertibleModule_restrictSheaf U' (hL.nsmul j)
  have hGinv : Stacks.Ample.IsInvertibleModule _ G :=
    Divisor.isInvertibleModule_restrictSheaf (h ⁻¹ᵁ U') (hE.nsmul r)
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal Tc).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Tc
  obtain ⟨Tp, hTp⟩ := exists_powSection ι (h ⁻¹ᵁ U') hE t r
  have hpt : ∀ c : (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme,
      U'.ι.base (h'.base (jι.base c)) = h.base (ι.base c.1) := fun c =>
    (ι_morphismRestrict_apply h U' _).trans (congrArg h.base (ι_morphismRestrict_apply ι _ c))
  have hrangeT : Set.range iT.base = (Tc : Set V') := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hrangeCT : ∀ y ∈ (⊤ : U'.toScheme.Opens), y ∈ Set.range (jι ≫ h').base →
      y ∈ Set.range iTU.base := by
    rintro y - ⟨c, rfl⟩
    refine exists_morphismRestrict_eq iT U' _ ?_
    rw [Scheme.Hom.comp_apply, hpt, hrangeT, hTc]
    exact Or.inl ⟨_, ⟨c.1, rfl⟩, rfl⟩
  have hCΩ : ∀ c : (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme, h'.base (jι.base c) ∈ ΩU := by
    intro c
    change U'.ι.base (h'.base (jι.base c)) ∈ (Ω : Set V')
    rw [hΩ, hpt]
    exact fun hc' => Set.disjoint_left.mp hdisj hc' ⟨ι.base c.1, ⟨⟨c.1, rfl⟩, c.2⟩, rfl⟩
  have hzT : ∀ z : (iT ⁻¹ᵁ U').toScheme, U'.ι.base (iTU.base z) ∈ (Tc : Set V') := fun z => by
    rw [← hrangeT, ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrangeTC : ∀ y ∈ ΩU, y ∈ Set.range iTU.base → y ∈ Set.range (jι ≫ h').base := by
    rintro y hy ⟨z, rfl⟩
    rcases hTc ▸ hzT z with ⟨_, ⟨c₀, rfl⟩, hc₀⟩ | hP'
    · have hc₀U : c₀ ∈ ι ⁻¹ᵁ (h ⁻¹ᵁ U') := by
        change h.base (ι.base c₀) ∈ U'
        rw [hc₀]; exact (iTU.base z).2
      let c : (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme := ⟨c₀, hc₀U⟩
      refine ⟨c, U'.ι.isOpenEmbedding.injective ?_⟩
      rw [Scheme.Hom.comp_apply, hpt]
      exact hc₀
    · exfalso
      have hyΩ : U'.ι.base (iTU.base z) ∈ (Ω : Set V') := hy
      rw [hΩ] at hyΩ
      exact hyΩ hP'
  let Good : (V₁ : U'.toScheme.Opens) → Γ(N, iTU ⁻¹ᵁ V₁) → Prop := fun V₁ a =>
    ∀ (V₂ : U'.toScheme.Opens) (hV₂ : V₂ ≤ V₁) (b : Γ(F, V₂)),
      ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₂ b =
        N.presheaf.map (homOfLE (iTU.preimage_mono hV₂)).op a →
      ∀ s₀ : Γ(G, h' ⁻¹ᵁ V₂), IsPullbackSectionOn h U' V₂ b s₀ →
        ((Scheme.Modules.pullbackPushforwardAdjunction jι).unit.app G).app (h' ⁻¹ᵁ V₂) s₀ =
          PG.presheaf.map (homOfLE le_top).op Tp
  -- the local generators `ψ⁻¹` of `𝒪(jL)` and `h^*ψ⁻¹` of `𝒪(rE)` over a chart
  have hchart : ∀ {U₀ : V'.Opens} {ψ : (RationalFunctions V')ˣ}
      (hψ : (j • L).IsLocalEquation U₀ ψ) {V₃ : U'.toScheme.Opens} (hV : U'.ι ''ᵁ V₃ ≤ U₀),
      Function.Bijective (fun c : Γ((iT ⁻¹ᵁ U').toScheme, iTU ⁻¹ᵁ V₃) =>
        c • (show Γ(N, iTU ⁻¹ᵁ V₃) from
          ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₃
            (restrictInvSection U' hψ hV))) ∧
      Function.Bijective (fun c : Γ((ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme, jι ⁻¹ᵁ (h' ⁻¹ᵁ V₃)) =>
        c • (show Γ(PG, jι ⁻¹ᵁ (h' ⁻¹ᵁ V₃)) from
          ((Scheme.Modules.pullbackPushforwardAdjunction jι).unit.app G).app (h' ⁻¹ᵁ V₃)
            (restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
              (image_preimage_morphismRestrict_le h U' hV)))) := by
    intro U₀ ψ hψ V₃ hV
    exact ⟨IsLocalGenerator.bijective_self (isLocalGenerator_pullback_unit iTU F
        (isLocalGenerator_restrictInvSection U' hψ hV)),
      IsLocalGenerator.bijective_self (isLocalGenerator_pullback_unit jι G
        (isLocalGenerator_restrictInvSection (h ⁻¹ᵁ U')
        (hpbj.isLocalEquation hψ) (image_preimage_morphismRestrict_le h U' hV)))⟩
  have huniq : ∀ (V₁ V₁' : U'.toScheme.Opens) (a : Γ(N, iTU ⁻¹ᵁ V₁))
      (a' : Γ(N, iTU ⁻¹ᵁ V₁')), V₁ ≤ ΩU → Good V₁ a → Good V₁' a' →
      N.presheaf.map (homOfLE (iTU.preimage_mono (inf_le_left : V₁ ⊓ V₁' ≤ V₁))).op a =
        N.presheaf.map (homOfLE (iTU.preimage_mono (inf_le_right : V₁ ⊓ V₁' ≤ V₁'))).op a' := by
    intro V₁ V₁' a a' hV₁Ω hg hg'
    refine eq_of_forall_exists_map_eq N (O := iTU ⁻¹ᵁ (V₁ ⊓ V₁')) _ _ fun z hz => ?_
    obtain ⟨U₀, hyU₀, ψ, hψ⟩ := (hL.nsmul j) (U'.ι.base (iTU.base z))
    obtain ⟨V₃, hV₃aff, hyV₃, hV₃le⟩ := exists_isAffineOpen_mem_and_subset
      (U := (V₁ ⊓ V₁') ⊓ U'.ι ⁻¹ᵁ U₀) (show iTU.base z ∈ (V₁ ⊓ V₁') ⊓ U'.ι ⁻¹ᵁ U₀ from ⟨hz, hyU₀⟩)
    have hV₃ : V₃ ≤ V₁ ⊓ V₁' := fun x hx => (hV₃le hx).1
    have hV : U'.ι ''ᵁ V₃ ≤ U₀ :=
      (U'.ι.image_mono (fun x hx => (hV₃le hx).2 : V₃ ≤ U'.ι ⁻¹ᵁ U₀)).trans
        (Scheme.Hom.image_preimage_le U'.ι U₀)
    refine ⟨iTU ⁻¹ᵁ V₃, iTU.preimage_mono hV₃, hyV₃, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    obtain ⟨hgT, hgC⟩ := hchart hψ hV
    have hlift : ∀ (V₄ : U'.toScheme.Opens) (hV₄ : V₃ ≤ V₄) (x : Γ(N, iTU ⁻¹ᵁ V₄)), Good V₄ x →
        ∃ c : Γ(U'.toScheme, V₃),
          N.presheaf.map (homOfLE (iTU.preimage_mono hV₄)).op x =
            ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₃
              (c • restrictInvSection U' hψ hV) ∧
          ((Scheme.Modules.pullbackPushforwardAdjunction jι).unit.app G).app (h' ⁻¹ᵁ V₃)
              (h'.app V₃ c • restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
                (image_preimage_morphismRestrict_le h U' hV)) =
            PG.presheaf.map (homOfLE le_top).op Tp := by
      intro V₄ hV₄ x hx
      obtain ⟨c₀, hc₀⟩ := hgT.2 (N.presheaf.map (homOfLE (iTU.preimage_mono hV₄)).op x)
      obtain ⟨c, rfl⟩ := iTU.app_surjective V₃ hV₃aff c₀
      have e : N.presheaf.map (homOfLE (iTU.preimage_mono hV₄)).op x =
          ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₃
            (c • restrictInvSection U' hψ hV) := by
        rw [unit_app_smul]; exact hc₀.symm
      exact ⟨c, e, hx V₃ hV₄ _ e.symm _
        (isPullbackSectionOn_smul_restrictInvSection h hpbj U' hψ hV c)⟩
    obtain ⟨c, hc, hcC⟩ := hlift V₁ (hV₃.trans inf_le_left) a hg
    obtain ⟨c', hc', hcC'⟩ := hlift V₁' (hV₃.trans inf_le_right) a' hg'
    have hCC : jι.app (h' ⁻¹ᵁ V₃) (h'.app V₃ c) = jι.app (h' ⁻¹ᵁ V₃) (h'.app V₃ c') := by
      rw [unit_app_smul] at hcC hcC'
      exact hgC.1 (hcC.trans hcC'.symm)
    have h0 : iTU.app V₃ (c - c') = 0 := by
      refine app_eq_zero_of_range_subset (jι ≫ h') iTU
        (fun y hy => hrangeTC y (hV₁Ω ((hV₃.trans inf_le_left) hy))) _ ?_
      change jι.app (h' ⁻¹ᵁ V₃) (h'.app V₃ (c - c')) = 0
      rw [map_sub, map_sub, hCC, sub_self]
    have h1 : iTU.app V₃ c = iTU.app V₃ c' := by rw [map_sub, sub_eq_zero] at h0; exact h0
    have hc2 : ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₃
          (c • restrictInvSection U' hψ hV) =
        ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₃
          (c' • restrictInvSection U' hψ hV) := by
      rw [unit_app_smul, unit_app_smul, h1]
    exact hc.trans (hc2.trans hc'.symm)
  have hex : ∀ z : (iT ⁻¹ᵁ U').toScheme, z ∈ iTU ⁻¹ᵁ ΩU →
      ∃ V₁ : U'.toScheme.Opens, ∃ _ : V₁ ≤ ΩU, iTU.base z ∈ V₁ ∧ ∃ a, Good V₁ a := by
    intro z hz
    obtain ⟨U₀, hyU₀, ψ, hψ⟩ := (hL.nsmul j) (U'.ι.base (iTU.base z))
    let V₀ : U'.toScheme.Opens := ΩU ⊓ U'.ι ⁻¹ᵁ U₀
    have hV₀ : U'.ι ''ᵁ V₀ ≤ U₀ :=
      (U'.ι.image_mono (inf_le_right : V₀ ≤ U'.ι ⁻¹ᵁ U₀)).trans
        (Scheme.Hom.image_preimage_le U'.ι U₀)
    obtain ⟨-, hgC₀⟩ := hchart hψ hV₀
    obtain ⟨g, hg⟩ := hgC₀.2 (PG.presheaf.map (homOfLE le_top).op Tp)
    obtain ⟨V₁, hV₁, hyV₁, b₀, hb₀⟩ := exists_app_eq_of_floor hlc hB h hhs hV'n hhp hhb hhO hlc'
      hk hL hMeq ⟨hM, hpb⟩ ι hC U' V₀ g (iTU.base z) ⟨hz, hyU₀⟩
    have hV₁' : U'.ι ''ᵁ V₁ ≤ U₀ := (U'.ι.image_mono hV₁).trans hV₀
    refine ⟨V₁, hV₁.trans inf_le_left, hyV₁,
      ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app V₁
        (b₀ • restrictInvSection U' hψ hV₁'), ?_⟩
    intro V₂ hV₂ b hb s₀ hs₀
    have hV₂' : U'.ι ''ᵁ V₂ ≤ U₀ := (U'.ι.image_mono hV₂).trans hV₁'
    obtain ⟨hgT₂, hgC₂⟩ := hchart hψ hV₂'
    obtain ⟨d, hd⟩ := (bijective_smul_restrictInvSection U' hψ hV₂').2 b
    let b₂ : Γ(U'.toScheme, V₂) := U'.toScheme.presheaf.map (homOfLE hV₂).op b₀
    have hres1 : F.presheaf.map (homOfLE hV₂).op (b₀ • restrictInvSection U' hψ hV₁') =
        b₂ • restrictInvSection U' hψ hV₂' := by
      rw [Scheme.Modules.map_smul]
      congr 1
    have hT : iTU.app V₂ d = iTU.app V₂ b₂ := by
      have h1 := hb
      rw [← unit_app_map _ _ hV₂, hres1, ← hd, unit_app_smul, unit_app_smul] at h1
      exact hgT₂.1 h1
    have hC0 : (jι ≫ h').app V₂ (d - b₂) = 0 :=
      app_eq_zero_of_range_subset iTU (jι ≫ h') (fun y _ hy => hrangeCT y trivial hy) _
        (by rw [map_sub, hT, sub_self])
    have hCd : jι.app (h' ⁻¹ᵁ V₂) (h'.app V₂ d) = jι.app (h' ⁻¹ᵁ V₂) (h'.app V₂ b₂) := by
      have h2 : jι.app (h' ⁻¹ᵁ V₂) (h'.app V₂ (d - b₂)) = 0 := hC0
      rw [map_sub, map_sub, sub_eq_zero] at h2
      exact h2
    have hs₀' : s₀ = h'.app V₂ d • restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
        (image_preimage_morphismRestrict_le h U' hV₂') :=
      hs₀.eq (hd ▸ isPullbackSectionOn_smul_restrictInvSection h hpbj U' hψ hV₂' d)
    have hb₂ : jι.app (h' ⁻¹ᵁ V₂) (h'.app V₂ b₂) =
        (ι ⁻¹ᵁ (h ⁻¹ᵁ U')).toScheme.presheaf.map
          (homOfLE (jι.preimage_mono (h'.preimage_mono (hV₂.trans hV₁)))).op g := by
      rw [app_map_apply, app_map_apply, hb₀, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have hγ : G.presheaf.map (homOfLE (h'.preimage_mono (hV₂.trans hV₁))).op
        (restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
          (image_preimage_morphismRestrict_le h U' hV₀)) =
        restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
          (image_preimage_morphismRestrict_le h U' hV₂') :=
      Divisor.restrictSection_inj (h ⁻¹ᵁ U') rfl
    rw [hs₀', unit_app_smul, hCd, hb₂, ← hγ, unit_app_map]
    have h3 := congrArg
      (PG.presheaf.map (homOfLE (jι.preimage_mono (h'.preimage_mono (hV₂.trans hV₁)))).op) hg
    have h4 := Scheme.Modules.map_smul PG
      (homOfLE (jι.preimage_mono (h'.preimage_mono (hV₂.trans hV₁)))) g
      (show Γ(PG, jι ⁻¹ᵁ (h' ⁻¹ᵁ V₀)) from
        ((Scheme.Modules.pullbackPushforwardAdjunction jι).unit.app G).app (h' ⁻¹ᵁ V₀)
          (restrictInvSection (h ⁻¹ᵁ U') (hpbj.isLocalEquation hψ)
            (image_preimage_morphismRestrict_le h U' hV₀)))
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h3
    exact h4.symm.trans h3
  choose V₁ hV₁ hzV₁ a ha using hex
  obtain ⟨τΩ, hτΩ⟩ : ∃ τΩ : Γ(N, iTU ⁻¹ᵁ ΩU), ∀ z hz,
      N.presheaf.map (homOfLE (iTU.preimage_mono (hV₁ z hz))).op τΩ = a z hz := by
    let Fs : TopCat.Sheaf AddCommGrpCat.{0} (iT ⁻¹ᵁ U').toScheme := ⟨N.presheaf, N.isSheaf⟩
    let ι' := {z : (iT ⁻¹ᵁ U').toScheme // z ∈ iTU ⁻¹ᵁ ΩU}
    let Ui : ι' → (iT ⁻¹ᵁ U').toScheme.Opens := fun i => iTU ⁻¹ᵁ V₁ i.1 i.2
    let sf : ∀ i, Fs.obj.obj (op (Ui i)) := fun i => a i.1 i.2
    have hcover : iTU ⁻¹ᵁ ΩU ≤ ⨆ i, Ui i := fun z hz =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV₁ z hz⟩
    have hcompat : TopCat.Presheaf.IsCompatible Fs.obj Ui sf := fun i i' =>
      huniq _ _ _ _ (hV₁ i.1 i.2) (ha i.1 i.2) (ha i'.1 i'.2)
    obtain ⟨τΩ, hτΩ, -⟩ := Fs.existsUnique_gluing' Ui (iTU ⁻¹ᵁ ΩU)
      (fun i => homOfLE (iTU.preimage_mono (hV₁ i.1 i.2))) hcover sf hcompat
    exact ⟨τΩ, fun z hz => hτΩ ⟨z, hz⟩⟩
  -- `T ∩ Ω` is the part of `T` over `h(C)`, so `τΩ` extends to `T`
  have := isProper_of_isProjectiveMorphism h hhp
  obtain ⟨τ, hτ⟩ := exists_section_res_eq_of_mem_iff iTU N
    ((h.isClosedMap _ ι.isClosedEmbedding.isClosed_range).preimage U'.ι.continuous) ΩU
    (fun z => by
      change U'.ι.base (iTU.base z) ∈ (Ω : Set V') ↔ U'.ι.base (iTU.base z) ∈ h.base '' _
      rw [hΩ]
      refine ⟨fun hzΩ => (hTc ▸ hzT z).resolve_right hzΩ, ?_⟩
      rintro ⟨_, ⟨c₀, rfl⟩, hc₀⟩ hP'
      have hc₀U : ι.base c₀ ∈ (h ⁻¹ᵁ f' ⁻¹ᵁ U : Set V) := by
        change h.base (ι.base c₀) ∈ U'
        rw [hc₀]; exact (iTU.base z).2
      exact Set.disjoint_left.mp hdisj hP' ⟨ι.base c₀, ⟨⟨c₀, rfl⟩, hc₀U⟩, hc₀⟩)
    τΩ
  refine ⟨τ, fun τ' hτ' σ hσ s hs => liftsPow_of_unit_app_eq ι (h ⁻¹ᵁ U') hTp ?_⟩
  refine eq_of_forall_exists_map_eq PG (O := jι ⁻¹ᵁ ⊤) _ _ fun c _ => ?_
  obtain ⟨z, hz⟩ := hrangeCT _ trivial ⟨c, rfl⟩
  have hzΩ : z ∈ iTU ⁻¹ᵁ ΩU := by
    change iTU.base z ∈ ΩU
    rw [hz]; exact hCΩ c
  refine ⟨jι ⁻¹ᵁ (h' ⁻¹ᵁ V₁ z hzΩ), le_top, ?_, ?_⟩
  · change h'.base (jι.base c) ∈ V₁ z hzΩ
    rw [← Scheme.Hom.comp_apply, ← hz]; exact hzV₁ z hzΩ
  have hb : ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app (V₁ z hzΩ)
      (F.presheaf.map (homOfLE le_top).op σ) =
      N.presheaf.map (homOfLE (iTU.preimage_mono (le_refl (V₁ z hzΩ)))).op (a z hzΩ) := by
    have e1 : ((Scheme.Modules.pullbackPushforwardAdjunction iTU).unit.app F).app (V₁ z hzΩ)
        (F.presheaf.map (homOfLE le_top).op σ) =
        N.presheaf.map (homOfLE (le_top : iTU ⁻¹ᵁ V₁ z hzΩ ≤ ⊤)).op τ' :=
      (unit_app_map iTU F le_top σ).trans (congrArg _ hσ)
    have e2 : ∀ x : Γ(N, ⊤), N.presheaf.map (homOfLE (le_top : iTU ⁻¹ᵁ V₁ z hzΩ ≤ ⊤)).op x =
        N.presheaf.map (homOfLE (iTU.preimage_mono (hV₁ z hzΩ))).op
          (N.presheaf.map (homOfLE (le_top : iTU ⁻¹ᵁ ΩU ≤ ⊤)).op x) := fun x =>
      (presheaf_map_map_apply N.presheaf _ _ _ x).symm
    rw [map_homOfLE_self_apply, e1, e2, hτ', hτ, hτΩ z hzΩ]
  have key := ha z hzΩ (V₁ z hzΩ) le_rfl _ hb _ (hs.isPullbackSectionOn _)
  rw [unit_app_map] at key
  exact key

end Descent

/-- **The core construction.** For a section `t` of `𝒪_{C_U}(E)` and a finite set `P` of closed
points of `V_U` whose `h`-image avoids `h(C_U)`, all large `r` divisible by `k / gcd(k, m)` admit a
section `s` of `𝒪_{V_U}(rE)` with `s|_{C_U} = t ^ r` and nonvanishing on `P`. -/
private theorem exists_liftsPow_core
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    (hnef : QDivisor.IsRelativelyNef sV f (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig f (Divisor.toQDivisor K + B))
    {V' : Scheme.{0}} [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (h : V ⟶ V') (f' : V' ⟶ Z) (hhf : h ≫ f' = f)
    (hf' : f' ≫ sZ = sV') (hV'n : IsNormalVariety ℂ sV') (hV'p : MMP.Mori.IsProjectiveVariety ℂ sV')
    (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hhO : ∀ U : V'.Opens, IsIso (h.app U))
    (hlc' : IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B))
    {k : ℕ} (hk : 0 < k) {L : Divisor V'} (hL : L.IsCartier)
    (hLamp : L.IsRelativelyAmple f' hL)
    {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B))
    (hMpb : ∃ hM, L.IsPullback h hM M)
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (U : Z.Opens) (hU : IsAffineOpen U)
    {m : ℕ} (hm : 0 < m) {E : Divisor V} (hE : E.IsCartier)
    (hEeq : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) :
    ∀ (t : Γ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
        (Divisor.restrictSheaf (f ⁻¹ᵁ U) E), ⊤)) (P : Finset (f ⁻¹ᵁ U).toScheme),
      (∀ p ∈ P, IsClosed ({p} : Set (f ⁻¹ᵁ U).toScheme)) →
      Disjoint (h.base '' ((f ⁻¹ᵁ U).ι.base '' (P : Set (f ⁻¹ᵁ U).toScheme)))
        (h.base '' (Set.range ι.base ∩ (f ⁻¹ᵁ U : Set V))) →
      ∃ r₀ : ℕ, ∀ r ≥ r₀, k / k.gcd m ∣ r →
        ∃ s : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), ⊤),
          LiftsPow ι (f ⁻¹ᵁ U) t r s ∧
          ∀ p ∈ P,
            p ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)) s := by
  classical
  intro t P hP hdisj
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  subst hhf
  have := isProper_of_isProjectiveMorphism h hhp
  have hZv := hZ.toIsVariety
  have hV'v := hV'p.toIsVariety
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsProper sV' := (isProper_of_isProjectiveMorphism sV' hV'p.isProjective)
  have : IsProper (f' ≫ sZ) := hf' ▸ inferInstance
  have : IsProper f' := IsProper.of_comp f' sZ
  have hWcl : IsClosed (h.base '' Set.range ι.base) :=
    h.isClosedMap _ ι.isClosedEmbedding.isClosed_range
  have : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hPcl : IsClosed (h.base '' (((h ≫ f') ⁻¹ᵁ U).ι.base '' (P : Set _))) := by
    rw [Set.image_image, Set.image_eq_iUnion]
    refine P.finite_toSet.isClosed_biUnion fun p hp => ?_
    have hlc : IsLocallyClosed (((h ≫ f') ⁻¹ᵁ U).ι.base '' {p}) :=
      (hP p hp).isLocallyClosed.image ((h ≫ f') ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing
        ((h ≫ f') ⁻¹ᵁ U).ι.isOpenEmbedding.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    have hcl := h.isClosedMap _ (isClosed_singleton_of_isLocallyClosed_singleton hlc)
    rwa [Set.image_singleton] at hcl
  let Tc : TopologicalSpace.Closeds V' := ⟨_, hWcl.union hPcl⟩
  let U' : V'.Opens := f' ⁻¹ᵁ U
  obtain ⟨j₀, hj₀⟩ := exists_unit_app_eq_of_isRelativelyAmple f' hL hLamp U hU
    ((Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_ U')
  obtain ⟨hM, hpb⟩ := hMpb
  refine ⟨j₀ * k, fun r hr hd => ?_⟩
  obtain ⟨j, hj, hrm⟩ := exists_nsmul_eq_nsmul_of_dvd hk hEeq hMeq hd
  have hjj : j₀ ≤ j :=
    Nat.le_of_mul_le_mul_right (hr.trans ((Nat.le_mul_of_pos_right r hm).trans hrm.le)) hk
  let Ω : V'.Opens := ⟨_, hPcl.isOpen_compl⟩
  have hhs : h ≫ sV' = sV := by rw [← hf', ← Category.assoc, hf]
  obtain ⟨τ, hτ⟩ := exists_descent_pow hlc hB h f' hhs hV'n hhp hhb hhO hlc' hk hL hMeq
    ⟨hM, hpb⟩ ι hC U hE t P hdisj Tc rfl Ω rfl hj
  -- the closed subscheme `T ∩ f'⁻¹ U` and the module on it
  let iTU := (Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι ∣_ U'
  let F := Divisor.restrictSheaf U' (j • L)
  let N := (Scheme.Modules.pullback iTU).obj F
  have : Stacks.Ample.IsInvertibleModule U'.toScheme F :=
    Divisor.isInvertibleModule_restrictSheaf U' (hL.nsmul j)
  have hNinv : Stacks.Ample.IsInvertibleModule _ N :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback iTU F
  let h' := h ∣_ U'
  let P' : Finset U'.toScheme := P.image h'.base
  have hrangeT : Set.range iTU.base = U'.ι.base ⁻¹' (Tc : Set V') := by
    ext y
    refine ⟨?_, fun hy => exists_morphismRestrict_eq _ U' y (by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hy)⟩
    rintro ⟨z, rfl⟩
    change U'.ι.base (iTU.base z) ∈ (Tc : Set V')
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    have : Set.range (Scheme.IdealSheafData.vanishingIdeal Tc).subschemeι.base = (Tc : Set V') := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact this ▸ ⟨_, rfl⟩
  -- the points of `P'`
  have hP'P : ∀ y ∈ P', U'.ι.base y ∈ h.base '' (((h ≫ f') ⁻¹ᵁ U).ι.base '' (P : Set _)) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨_, ⟨q, hq, rfl⟩, (ι_morphismRestrict_apply h U' q).symm⟩
  have hP'W : ∀ y ∈ P', U'.ι.base y ∉ h.base '' Set.range ι.base := by
    intro y hy hyW
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    rw [ι_morphismRestrict_apply] at hyW
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hyW
    refine Set.disjoint_left.mp hdisj ⟨_, ⟨q, hq, rfl⟩, rfl⟩ ⟨ι.base c, ⟨⟨c, rfl⟩, ?_⟩, hc⟩
    change f'.base (h.base (ι.base c)) ∈ U
    rw [hc]
    exact q.2
  have hPP' : ∀ y : U'.toScheme,
      U'.ι.base y ∈ h.base '' (((h ≫ f') ⁻¹ᵁ U).ι.base '' (P : Set _)) → y ∈ P' := by
    rintro y ⟨_, ⟨q, hq, rfl⟩, hqy⟩
    exact Finset.mem_image.mpr
      ⟨q, hq, U'.ι.isOpenEmbedding.injective ((ι_morphismRestrict_apply h U' q).trans hqy)⟩
  have hP'cl : ∀ y ∈ P', IsClosed ({y} : Set U'.toScheme) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    rw [← Set.image_singleton]
    exact h'.isClosedMap _ (hP q hq)
  have hinjT : Function.Injective iTU.base := iTU.isClosedEmbedding.injective
  have hex : ∀ y : P', ∃ z, iTU.base z = y.1 := fun y => by
    have : y.1 ∈ Set.range iTU.base := by
      rw [hrangeT]; exact Or.inr (hP'P y.1 y.2)
    exact this
  choose pt hpt using hex
  have hptinj : Function.Injective pt := fun y y' hyy' =>
    Subtype.ext ((hpt y).symm.trans ((congrArg iTU.base hyy').trans (hpt y')))
  have hptcl : ∀ y : P', IsClosed ({pt y} : Set _) := fun y => by
    have : ({pt y} : Set _) = iTU.base ⁻¹' {y.1} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hz => hz ▸ hpt y, fun hz => hinjT (hz.trans (hpt y).symm)⟩
    rw [this]
    exact (hP'cl y.1 y.2).preimage iTU.continuous
  have hptop : ∀ y : P', IsOpen ({pt y} : Set _) := fun y => by
    let S : Set U'.toScheme := U'.ι.base ⁻¹' (h.base '' Set.range ι.base) ∪
      ⋃ y' ∈ P'.erase y.1, ({y'} : Set U'.toScheme)
    have hS : IsClosed S := (hWcl.preimage U'.ι.continuous).union
      (isClosed_biUnion_finset fun y' hy' => hP'cl y' (Finset.mem_of_mem_erase hy'))
    have hc : ({pt y} : Set _)ᶜ = iTU.base ⁻¹' S := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro hz
        have hzT : U'.ι.base (iTU.base z) ∈ (Tc : Set V') := by
          have : iTU.base z ∈ Set.range iTU.base := ⟨z, rfl⟩
          rwa [hrangeT] at this
        rcases hzT with hW | hPz
        · exact Or.inl hW
        · refine Or.inr (Set.mem_biUnion (Finset.mem_erase.mpr ⟨fun he => hz ?_,
            hPP' _ hPz⟩) (Set.mem_singleton _))
          exact hinjT (he.trans (hpt y).symm)
      · rintro (hW | hP2) rfl
        · exact hP'W y.1 y.2 (hpt y ▸ hW)
        · obtain ⟨y', hy', hy'z⟩ := Set.mem_iUnion₂.mp hP2
          rw [Set.mem_singleton_iff, hpt y] at hy'z
          exact (Finset.mem_erase.mp hy').1 hy'z.symm
    rw [← compl_compl ({pt y} : Set _), hc]
    exact (hS.preimage iTU.continuous).isOpen_compl
  have hptΩ : ∀ y : P',
      ((iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) : TopologicalSpace.Opens _) : Set _) ⊆ ({pt y} : Set _)ᶜ := by
    intro y z hz hzy
    rw [Set.mem_singleton_iff] at hzy
    subst hzy
    have : U'.ι.base (iTU.base (pt y)) ∈ (Ω : Set V') := hz
    rw [hpt y] at this
    exact this (hP'P y.1 y.2)
  -- sections supported at the points of `P'`
  have hsec : ∀ y : P', ∃ sy : Γ(N, ⊤),
      N.presheaf.germ ⊤ (pt y) trivial sy ∉ Stacks.ModuleStalk.maximalSmul N (pt y) ∧
      N.presheaf.map (homOfLE le_top :
        (⟨{pt y}ᶜ, (hptcl y).isOpen_compl⟩ : TopologicalSpace.Opens _) ⟶ ⊤).op sy = 0 :=
    fun y => exists_section_notMem_maximalSmul_of_isOpen N (pt y) (hptop y) (hptcl y)
  choose sy hsyNV hsy0 using hsec
  have hgerm0 : ∀ y y' : P', y ≠ y' → N.presheaf.germ ⊤ (pt y') trivial (sy y) = 0 := by
    intro y y' hne
    have hmem : pt y' ∈ (⟨{pt y}ᶜ, (hptcl y).isOpen_compl⟩ : TopologicalSpace.Opens _) :=
      fun he => hne (hptinj he).symm
    rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE le_top :
      (⟨{pt y}ᶜ, (hptcl y).isOpen_compl⟩ : TopologicalSpace.Opens _) ⟶ ⊤) (pt y') hmem,
      hsy0 y, map_zero]
  have hres : ∀ y : P', N.presheaf.map
      (homOfLE (le_top : iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) ≤ ⊤)).op (sy y) = 0 := by
    intro y
    have hle : iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) ≤ ⟨{pt y}ᶜ, (hptcl y).isOpen_compl⟩ := hptΩ y
    rw [show (homOfLE (le_top : iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) ≤ ⊤)) =
      homOfLE hle ≫ homOfLE le_top from rfl, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hsy0 y, map_zero]
  classical
  let bad : Finset P' := Finset.univ.filter fun y =>
    N.presheaf.germ ⊤ (pt y) trivial τ ∈ Stacks.ModuleStalk.maximalSmul N (pt y)
  let τ' : Γ(N, ⊤) := τ + ∑ y ∈ bad, sy y
  have hτ'Ω : N.presheaf.map (homOfLE (le_top : iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) ≤ ⊤)).op τ' =
      N.presheaf.map (homOfLE (le_top : iTU ⁻¹ᵁ (U'.ι ⁻¹ᵁ Ω) ≤ ⊤)).op τ := by
    simp only [τ', map_add, map_sum, hres, Finset.sum_const_zero, add_zero]
  have hτ'NV : ∀ y : P',
      N.presheaf.germ ⊤ (pt y) trivial τ' ∉ Stacks.ModuleStalk.maximalSmul N (pt y) := by
    intro y
    have hsum : N.presheaf.germ ⊤ (pt y) trivial τ' = N.presheaf.germ ⊤ (pt y) trivial τ +
        if y ∈ bad then N.presheaf.germ ⊤ (pt y) trivial (sy y) else 0 := by
      simp only [τ', map_add, map_sum]
      congr 1
      split_ifs with hb
      · exact Finset.sum_eq_single_of_mem y hb fun y' _ hne => hgerm0 y' y hne
      · exact Finset.sum_eq_zero fun y' hy' => hgerm0 y' y fun he => hb (he ▸ hy')
    rw [hsum]
    split_ifs with hb
    · intro hmem
      have hτm : N.presheaf.germ ⊤ (pt y) trivial τ ∈ Stacks.ModuleStalk.maximalSmul N (pt y) :=
        (Finset.mem_filter.mp hb).2
      apply hsyNV y
      have := Submodule.sub_mem _ hmem hτm
      rwa [add_sub_cancel_left] at this
    · rw [add_zero]
      exact fun hmem => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
  obtain ⟨σ, hστ⟩ := hj₀ j hjj τ'
  have hσP : ∀ p ∈ P, h'.base p ∈
      Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf U' (j • L)) σ := by
    intro p hp
    let y : P' := ⟨h'.base p, Finset.mem_image_of_mem _ hp⟩
    rw [Stacks.Ample.mem_nonvanishingLocus_iff]
    have hiff := germ_unit_app_mem_maximalSmul_iff iTU F σ (pt y) trivial
    rw [hpt y] at hiff
    intro hmem
    refine hτ'NV y ?_
    have := hiff.mpr hmem
    rwa [hστ] at this
  have hpbj := isPullback_nsmul_of_eq hL hpb hj
  have := hhb.isDominant
  obtain ⟨s, hs, hsNV⟩ := exists_isPullbackSection h (hL.nsmul j) hpbj U' σ
  exact ⟨s, hτ τ' hτ'Ω σ hστ s hs, fun p hp => (hsNV p).2 (hσP p hp)⟩

/-- **Nonvanishing is constant along the fibres of `h`.** For `r` divisible by `k / gcd(k, m)`,
`rE` is the pull-back of a multiple of `L`, so a section of `𝒪_{V_U}(rE)` that does not vanish at
one point of a fibre of `h` vanishes at no point of it. -/
private theorem mem_nonvanishingLocus_of_map_eq
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    (hnef : QDivisor.IsRelativelyNef sV f (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig f (Divisor.toQDivisor K + B))
    {V' : Scheme.{0}} [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (h : V ⟶ V') (f' : V' ⟶ Z) (hhf : h ≫ f' = f)
    (hf' : f' ≫ sZ = sV') (hV'n : IsNormalVariety ℂ sV') (hV'p : MMP.Mori.IsProjectiveVariety ℂ sV')
    (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hhO : ∀ U : V'.Opens, IsIso (h.app U))
    (hlc' : IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B))
    {k : ℕ} (hk : 0 < k) {L : Divisor V'} (hL : L.IsCartier)
    (hLeq : Divisor.toQDivisor L = (k : ℚ) • (Divisor.toQDivisor
      (RationalMap.transformDivisor h.toRationalMap K) +
        RationalMap.transformDivisor h.toRationalMap B))
    (hLamp : L.IsRelativelyAmple f' hL)
    {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B))
    (hMpb : ∃ hM, L.IsPullback h hM M)
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (U : Z.Opens) (hU : IsAffineOpen U)
    {m : ℕ} (hm : 0 < m) {E : Divisor V} (hE : E.IsCartier)
    (hEeq : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B))
    {r : ℕ} (hr : k / k.gcd m ∣ r) (s : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), ⊤))
    {x y : (f ⁻¹ᵁ U).toScheme} (hxy : h.base ((f ⁻¹ᵁ U).ι.base x) = h.base ((f ⁻¹ᵁ U).ι.base y))
    (hx : x ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)) s) :
    y ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)) s := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨j, hj, -⟩ := exists_nsmul_eq_nsmul_of_dvd hk hEeq hMeq hr
  obtain ⟨hM, hpb⟩ := hMpb
  subst hhf
  have hjL : ((j : ℤ) • L).IsCartier := hL.zsmul j
  have hpbj := hpb.zsmul hL (j : ℤ) (notMem_supp_zsmul h hM j)
  have hrE : r • E = (j : ℤ) • M := by rw [hj, natCast_zsmul]
  let G := ((j : ℤ) • L).divisorialSheaf
  let U' : V'.Opens := f' ⁻¹ᵁ U
  let h' : (h ⁻¹ᵁ U').toScheme ⟶ U'.toScheme := h ∣_ U'
  let A : U'.toScheme.Modules := (Scheme.Modules.pullback U'.ι).obj G
  have : Stacks.Ample.IsInvertibleModule V' G := hjL.isInvertibleModule_divisorialSheaf
  have : Stacks.Ample.IsInvertibleModule U'.toScheme A :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback U'.ι G
  let e : Divisor.restrictSheaf ((h ≫ f') ⁻¹ᵁ U) (r • E) ≅ (Scheme.Modules.pullback h').obj A :=
    (Scheme.Modules.restrictFunctor (h ⁻¹ᵁ U').ι).mapIso
        (eqToIso (congrArg Divisor.divisorialSheaf hrE) ≪≫
          hpbj.divisorialSheafIso (hBc := hjL)) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (h ⁻¹ᵁ U').ι).app _ ≪≫
      (Scheme.Modules.pullbackComp (h ⁻¹ᵁ U').ι h).app G ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι h U').symm).app G ≪≫
      ((Scheme.Modules.pullbackComp h' U'.ι).app G).symm
  let x' : (h ⁻¹ᵁ U').toScheme := x
  let y' : (h ⁻¹ᵁ U').toScheme := y
  have hxy' : h'.base y' = h'.base x' := by
    apply U'.ι.isOpenEmbedding.injective
    change U'.ι.base (h'.base y') = U'.ι.base (h'.base x')
    rw [ι_morphismRestrict_apply, ι_morphismRestrict_apply]
    exact hxy.symm
  rw [← Stacks.Ample.nonvanishingLocus_congr e s] at hx ⊢
  exact MMP.Mori.mem_nonvanishingLocus_pullback_of_map_eq h' (isIso_morphismRestrict_app h hhO U') A
    _ hxy' hx

end Proof_lem_mmp_surface_projective_floor_section_extension

end

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.Mori

/-- **Extending floor sections through the adjoint ample model.** Let `(V, B)` be an lc pair,
`B ≥ 0`, on a normal projective complex surface, with `f : V ⟶ Z` to a projective variety and
`K + B` `f`-nef and `f`-big, and let `h : V ⟶ V'`, `f'`, `k`, `L`, `M` be an adjoint ample model as
in `IsLcPair.exists_isRelativelyAmple_of_isRelativelyNef_of_isRelativelyBig`. Let `ι : C ⟶ V` be
the reduced floor `⌊B⌋`, `U ⊆ Z` affine, and `E = m(K + B)` Cartier with `m > 0`. Then:

* for every section `t` of `ι^* 𝒪(E)` over `C ∩ f⁻¹U` and every finite set `P` of closed points of
  `f⁻¹U` with `h(P) ∩ h(C ∩ f⁻¹U) = ∅`, for all large `r` divisible by `k / gcd(k, m)` there is a
  section `s` of `𝒪(rE)` over `f⁻¹U` restricting to `t^r` on `C ∩ f⁻¹U` and nonvanishing on `P`;
* if a nonempty finite family of sections `t_α` of `ι^* 𝒪(E)` over `C ∩ f⁻¹U` has no common zero,
  then for every `x ∈ f⁻¹U` there is `α` such that for all large `r` divisible by `k / gcd(k, m)`
  some section of `𝒪(rE)` over `f⁻¹U` restricts to `t_α^r` and is nonvanishing at `x`. -/
@[mmp "lem_mmp_surface_projective_floor_section_extension"]
public theorem IsLcPair.exists_restrict_eq_pow_of_isRelativelyAmple
    {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {K : Divisor V} {B : QDivisor V} (hlc : IsLcPair sV 2 K B) (hB : 0 ≤ B)
    (hV : IsProjectiveVariety ℂ sV) (hZ : IsProjectiveVariety ℂ sZ)
    (f : V ⟶ Z) (hf : f ≫ sZ = sV)
    (hnef : QDivisor.IsRelativelyNef sV f (Divisor.toQDivisor K + B))
    (hbig : QDivisor.IsRelativelyBig f (Divisor.toQDivisor K + B))
    {V' : Scheme.{0}} [IsIntegral V'] [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
    {sV' : V' ⟶ Spec (.of ℂ)} (h : V ⟶ V') (f' : V' ⟶ Z) (hhf : h ≫ f' = f)
    (hf' : f' ≫ sZ = sV') (hV'n : IsNormalVariety ℂ sV') (hV'p : IsProjectiveVariety ℂ sV')
    (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hhO : ∀ U : V'.Opens, IsIso (h.app U))
    (hlc' : IsLcPair sV' 2 (RationalMap.transformDivisor h.toRationalMap K)
      (RationalMap.transformDivisor h.toRationalMap B))
    {k : ℕ} (hk : 0 < k) {L : Divisor V'} (hL : L.IsCartier)
    (hLeq : Divisor.toQDivisor L = (k : ℚ) • (Divisor.toQDivisor
      (RationalMap.transformDivisor h.toRationalMap K) +
        RationalMap.transformDivisor h.toRationalMap B))
    (hLamp : L.IsRelativelyAmple f' hL)
    {M : Divisor V} (hMeq : Divisor.toQDivisor M = (k : ℚ) • (Divisor.toQDivisor K + B))
    (hMpb : ∃ hM, L.IsPullback h hM M)
    {C : Scheme.{0}} (ι : C ⟶ V) [IsClosedImmersion ι] [IsReduced C]
    (hC : Set.range ι.base = ⋃ E ∈ B.roundDown.support, (E.support : Set V))
    (U : Z.Opens) (hU : IsAffineOpen U)
    {m : ℕ} (hm : 0 < m) {E : Divisor V} (hE : E.IsCartier)
    (hEeq : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) :
    (∀ (t : Γ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
        (Divisor.restrictSheaf (f ⁻¹ᵁ U) E), ⊤)) (P : Finset (f ⁻¹ᵁ U).toScheme),
      (∀ p ∈ P, IsClosed ({p} : Set (f ⁻¹ᵁ U).toScheme)) →
      Disjoint (h.base '' ((f ⁻¹ᵁ U).ι.base '' (P : Set (f ⁻¹ᵁ U).toScheme)))
        (h.base '' (Set.range ι.base ∩ (f ⁻¹ᵁ U : Set V))) →
      ∃ r₀ : ℕ, ∀ r ≥ r₀, k / k.gcd m ∣ r →
        ∃ s : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), ⊤),
            (∀ (O : (f ⁻¹ᵁ U).toScheme.Opens) (σ : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) E, O)),
              (((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ (f ⁻¹ᵁ U))).unit.app
                  (Divisor.restrictSheaf (f ⁻¹ᵁ U) E)).app O σ :
                    Γ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
                      (Divisor.restrictSheaf (f ⁻¹ᵁ U) E), (ι ∣_ (f ⁻¹ᵁ U)) ⁻¹ᵁ O)) =
                ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
                  (Divisor.restrictSheaf (f ⁻¹ᵁ U) E)).presheaf.map
                    (homOfLE le_top).op t →
              ∀ τ : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), O),
                (Divisor.restrictSection (f ⁻¹ᵁ U) τ).1 =
                    (Divisor.restrictSection (f ⁻¹ᵁ U) σ).1 ^ r →
                ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ (f ⁻¹ᵁ U))).unit.app
                    (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E))).app O
                  ((Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)).presheaf.map
                    (homOfLE le_top).op s - τ) = 0) ∧
          ∀ p ∈ P, p ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)) s) ∧
    ∀ {A : Type} [Finite A] [Nonempty A] (t : A → Γ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
        (Divisor.restrictSheaf (f ⁻¹ᵁ U) E), ⊤)),
      (∀ c, ∃ α, c ∈ Stacks.Ample.nonvanishingLocus _ (t α)) →
      ∀ x : (f ⁻¹ᵁ U).toScheme, ∃ α : A, ∃ r₀ : ℕ, ∀ r ≥ r₀, k / k.gcd m ∣ r →
        ∃ s : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), ⊤),
            (∀ (O : (f ⁻¹ᵁ U).toScheme.Opens) (σ : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) E, O)),
              (((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ (f ⁻¹ᵁ U))).unit.app
                  (Divisor.restrictSheaf (f ⁻¹ᵁ U) E)).app O σ :
                    Γ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
                      (Divisor.restrictSheaf (f ⁻¹ᵁ U) E), (ι ∣_ (f ⁻¹ᵁ U)) ⁻¹ᵁ O)) =
                ((Scheme.Modules.pullback (ι ∣_ (f ⁻¹ᵁ U))).obj
                  (Divisor.restrictSheaf (f ⁻¹ᵁ U) E)).presheaf.map
                    (homOfLE le_top).op (t α) →
              ∀ τ : Γ(Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E), O),
                (Divisor.restrictSection (f ⁻¹ᵁ U) τ).1 =
                    (Divisor.restrictSection (f ⁻¹ᵁ U) σ).1 ^ r →
                ((Scheme.Modules.pullbackPushforwardAdjunction (ι ∣_ (f ⁻¹ᵁ U))).unit.app
                    (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E))).app O
                  ((Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)).presheaf.map
                    (homOfLE le_top).op s - τ) = 0) ∧
          x ∈ Stacks.Ample.nonvanishingLocus (Divisor.restrictSheaf (f ⁻¹ᵁ U) (r • E)) s := by
  open Limits TopologicalSpace MMP.Flips
    Proof_lem_mmp_surface_projective_floor_section_extension in
  · have core := exists_liftsPow_core hlc hB hV hZ f hf hnef hbig h f' hhf hf' hV'n hV'p hhp hhb
      hhO hlc' hk hL hLamp hMeq hMpb ι hC U hU hm hE hEeq
    refine ⟨fun t P hP hdisj => ?_, fun {A} _ _ t hgen x => ?_⟩
    · obtain ⟨r₀, hr₀⟩ := core t P hP hdisj
      exact ⟨r₀, fun r hr hd => (hr₀ r hr hd).imp fun s hs => ⟨hs.1, hs.2⟩⟩
    have hvar := hV.toIsVariety
    have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
    by_cases hx : h.base ((f ⁻¹ᵁ U).ι.base x) ∈ h.base '' (Set.range ι.base ∩ ((f ⁻¹ᵁ U) : Set V))
    · obtain ⟨v, ⟨⟨c₀, rfl⟩, hc₀⟩, hv⟩ := hx
      let c : (ι ⁻¹ᵁ (f ⁻¹ᵁ U)).toScheme := ⟨c₀, (hc₀ : ι.base c₀ ∈ f ⁻¹ᵁ U)⟩
      obtain ⟨α, hα⟩ := hgen c
      obtain ⟨r₀, hr₀⟩ := core (t α) ∅ (fun p hp => absurd hp (Finset.notMem_empty p))
        (by rw [Finset.coe_empty, Set.image_empty, Set.image_empty]; exact Set.empty_disjoint _)
      refine ⟨α, max r₀ 1, fun r hr hd => ?_⟩
      obtain ⟨s, hs, -⟩ := hr₀ r (le_of_max_le_left hr) hd
      refine ⟨s, hs,
        Proof_lem_mmp_surface_projective_floor_section_extension.mem_nonvanishingLocus_of_map_eq
        hlc hB hV hZ f hf hnef hbig h f' hhf hf' hV'n hV'p hhp hhb hhO hlc' hk hL hLeq hLamp hMeq
        hMpb ι hC U hU hm hE hEeq hd s (x := (ι ∣_ (f ⁻¹ᵁ U)).base c) ?_ ?_⟩
      · rw [← hv]
        congr 1
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        rfl
      · exact mem_nonvanishingLocus_of_liftsPow ι (f ⁻¹ᵁ U) hE hs hα
    · have hS : IsClosed {y : (f ⁻¹ᵁ U).toScheme |
          h.base ((f ⁻¹ᵁ U).ι.base y) ∈ h.base '' (Set.range ι.base ∩ ((f ⁻¹ᵁ U) : Set V))} := by
        have := isProper_of_isProjectiveMorphism h hhp
        have hcl : IsClosed (h.base '' Set.range ι.base) :=
          h.isClosedMap _ ι.isClosedEmbedding.isClosed_range
        convert hcl.preimage ((f ⁻¹ᵁ U).ι ≫ h).continuous using 1
        ext y
        refine ⟨fun ⟨v, ⟨hv₁, _⟩, hv⟩ => ⟨v, hv₁, hv⟩,
          fun ⟨v, ⟨c, hc⟩, hv⟩ => ⟨v, ⟨⟨c, hc⟩, ?_⟩, hv⟩⟩
        subst hc
        change f.base (ι.base c) ∈ U
        rw [← hhf, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, Category.assoc, hhf]
        exact y.2
      have : JacobsonSpace (f ⁻¹ᵁ U).toScheme :=
        LocallyOfFiniteType.jacobsonSpace ((f ⁻¹ᵁ U).ι ≫ sV)
      obtain ⟨x', hx'c, hxx', hx'S⟩ := exists_isClosed_singleton_specializes_notMem hS hx
      obtain ⟨α⟩ := (inferInstance : Nonempty A)
      obtain ⟨r₀, hr₀⟩ := core (t α) {x'}
        (fun p hp => by rw [Finset.mem_singleton] at hp; subst hp; exact hx'c) (by
        simp only [Finset.coe_singleton, Set.image_singleton, Set.disjoint_singleton_left]
        exact hx'S)
      refine ⟨α, r₀, fun r hr hd => ?_⟩
      obtain ⟨s, hs, hP⟩ := hr₀ r hr hd
      refine ⟨s, hs, hxx'.mem_open ?_ (hP x' (Finset.mem_singleton_self _))⟩
      have := Divisor.isInvertibleModule_restrictSheaf (f ⁻¹ᵁ U) (hE.nsmul r)
      exact Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ s

end MMP.Mori
