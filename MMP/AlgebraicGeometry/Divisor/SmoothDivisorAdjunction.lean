module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LineBundle
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
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
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Analytic.BorelMoore
import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass
import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafSpelling

/-!
# Adjunction for a smooth divisor, and the strip test divisor (KM 3.4, Step 9)

Let `Y` be a smooth variety of dimension `n + 1` over a field `k` and `T ⊆ Y` a smooth prime
divisor, the closed subscheme of an effective Cartier divisor `D_T` on `Y`, with closed immersion
`i : T ⟶ Y`. The adjunction formula identifies the restriction to `T` of
`ω_Y(T) = ω_Y ⊗ 𝒪_Y(T)` with the canonical sheaf of `T`:
`i^*(Ω^{n+1}_{Y/k} ⊗ 𝒪_Y(D_T)) ≅ Ω^n_{T/k}`.
Twisting by a Cartier divisor `B` on `Y` whose pull-back `B|_T` to `T` is defined, and writing
the canonical sheaves through canonical Cartier divisors `K_Y`, `K_T`, this gives
`i^* 𝒪_Y(K_Y + T + B) ≅ 𝒪_T(K_T + B|_T)`.

As an application, let `(X, Δ, a, H)` be a rationality datum, `p, q > 0` integers,
`(f; F_•; a_•; p_•; r_•)` a `(p, q)`-adapted resolution `f : Y ⟶ X` with tie-breaker `(j₀, c)`,
test boundary `A'`, and `F = F_{j₀}`. For `(p', q') ∈ ℤ²` the test divisor is
`N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F - K_Y`. Since `F` is a smooth prime divisor of the
smooth variety `Y`, adjunction `(K_Y + F)|_F ∼ K_F` gives
`N(p', q')|_F ≡ (f^*(p'H + q'a(K_X + Δ)) + A')|_F - K_F`.

## Main results

* `MMP.Intersection.nonempty_pullback_canonical_twist_iso`: `i^*(ω_Y ⊗ 𝒪_Y(T)) ≅ ω_T` for a
  smooth effective Cartier divisor `T`, not necessarily integral.
* `MMP.Intersection.nonempty_pullback_lineBundle_iso_of_smooth_divisor`: both adjunction
  isomorphisms.
* `MMP.Mori.nonempty_divisorialSheaf_iso_of_isCanonicalDivisor`: on a smooth scheme, the
  divisorial sheaf of a canonical divisor is the sheaf of top forms.
* `MMP.Mori.IsStripTieBreaker.numericallyEquivalent_restrictPrimeDivisor`: the restriction of
  the strip test divisor to the tie-breaking divisor.
* `MMP.Mori.PrimeDivisor.exists_isEffective_isSubschemeOfEffective_of_isSmoothVariety`: a prime
  divisor of a smooth variety is the closed subscheme of an effective Cartier divisor, with Weil
  divisor the prime divisor.

## Implementation notes

The divisor `T` is given by its ideal sheaf `I`, with `T = I.subscheme`, and `𝒪_Y(T)` is the line
bundle `MMP.CartierDivisor.sheaf D_T` of an effective Cartier divisor `D_T` whose closed
subscheme is `T` (`MMP.Intersection.IsSubschemeOfEffective`). The canonical sheaves are the top
exterior powers `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms` of the sheaves of
relative differentials over `Spec k`, and `K_Y`, `K_T` are Cartier divisors whose line bundles are
isomorphic to them. The restriction `B|_T` is a pull-back of `B` along `i`
(`MMP.Intersection.IsPullback`), defined when `T` is not contained in the support of `B`.

The first isomorphism is obtained from the conormal sequence
`0 ⟶ 𝒞_{T/Y} ⟶ i^*Ω_{Y/k} ⟶ Ω_{T/k} ⟶ 0`, short exact since `T` is smooth ([Stacks, Tag 06AA]),
rather than from the residue of the source: the conormal sheaf is `i^*ℐ` ([Stacks, Tag 0B3P]),
the ideal `ℐ` of `T` is `𝒪_Y(-D)`, `Ω_{T/k}` has rank `n` by rank additivity, and taking
determinants ([Stacks, Tag 0B38]) gives `i^*Ω^{n+1}_{Y/k} ≅ 𝒞_{T/Y} ⊗ Ω^n_{T/k}`; tensoring with
`i^*𝒪_Y(D)` and `𝒪_Y(-D) ⊗ 𝒪_Y(D) ≅ 𝒪_Y` concludes. The second isomorphism twists the first by
the pull-back of `𝒪_Y(B)`, which is `𝒪_T(B_T)` because the local equations of `B_T` are the
pull-backs of those of `B`.

Restriction of divisors to `F` (`MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`) is the
coefficientwise restriction, meaningful for divisors of which `F` is not a component, while
`N(p', q')` has `F` as a component. The relation is therefore stated for representatives: for
every `ℚ`-divisor `N₁ ≡ N(p', q')` and every `M₁ ≡ f^*(p'H + q'a(K_X + Δ)) + A'` on `Y` of which
`F` is not a component, `N₁|_F ≡ M₁|_F - K_F` on `F`. Numerical equivalence on `Y` restricts to
numerical equivalence on `F`, so this is the class-level statement of the source. The canonical
divisor `K_F` of `F` (of dimension `n - 1`) is an explicit argument, and the standing instances on
the subscheme `F` (locally Noetherian, normal) are assumed; they hold as `F` is smooth.
Writing `G` for a divisor linearly equivalent to `K_Y + F` of which `F` is not a component,
`N + G ≡ f^*(p'H + q'a(K_X + Δ)) + A'`, restriction to `F` preserves numerical equivalence, and
`G|_F ∼ K_F` by adjunction.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, Step 9
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace MMP.Intersection

open Opposite TopologicalSpace Stacks.SheafOfModules

/-- Cancelling fractions: if `g_Y = a_Y / b_Y`, `g_Z = a_Z / b_Z` and `g_Y = u g_Z`, and `G_Y`,
`G_Z` are the fractions of the images of `a_Y, b_Y` and `a_Z, b_Z` under `φ`, then
`G_Y = φ(u) G_Z`. -/
private theorem eq_map_mul_of_isFraction {A KA B KB : Type*} [CommRing A] [CommRing KA]
    [CommRing B] [CommRing KB] (ιA : A →+* KA) (hιA : Function.Injective ιA) (ιB : B →+* KB)
    (φ : A →+* B) {aY bY aZ bZ u : A} {gY gZ : KA} {GY GZ : KB}
    (hgY : ιA bY * gY = ιA aY) (hgZ : ιA bZ * gZ = ιA aZ) (hu : gY = ιA u * gZ)
    (hbY : IsUnit (ιB (φ bY))) (hbZ : IsUnit (ιB (φ bZ)))
    (hGY : ιB (φ bY) * GY = ιB (φ aY)) (hGZ : ιB (φ bZ) * GZ = ιB (φ aZ)) :
    GY = ιB (φ u) * GZ := by
  have h1 : aY * bZ = u * aZ * bY := by
    apply hιA
    simp only [map_mul, ← hgY, ← hgZ, hu]
    ring
  have h2 := congrArg (fun a => ιB (φ a)) h1
  simp only [map_mul, ← hGY, ← hGZ] at h2
  have h3 : (ιB (φ bY) * ιB (φ bZ)) * GY = (ιB (φ bY) * ιB (φ bZ)) * (ιB (φ u) * GZ) := by
    linear_combination h2
  exact (hbY.mul hbZ).mul_left_cancel h3

/-- Local data of a pull-back: around each `y ∈ Y` a local equation `G₀ = s_a / s_b` of `B` on an
open `V₀ ∋ f(y)` and a local equation `G` of `B'` on an open `W ∋ y` inside `f⁻¹(V₀)` whose germs
are the fractions `f^♯ s_a / f^♯ s_b`. -/
private theorem exists_pullback_localData {X Y : Scheme.{u}} {f : Y ⟶ X} {B : X.CartierDivisor}
    {B' : Y.CartierDivisor} (h : IsPullback f B B') (y : Y) :
    ∃ (V₀ : X.Opens) (G₀ : (X.totalQuotientSheaf.obj.obj (op V₀))ˣ)
      (sa sb : Γ(X, V₀)) (W : Y.Opens) (hW : W ≤ f ⁻¹ᵁ V₀) (_ : y ∈ W)
      (G : (Y.totalQuotientSheaf.obj.obj (op W))ˣ),
      IsLocalEquationOn B V₀ G₀ ∧ IsLocalEquationOn B' W G ∧
      (∀ (p : Y) (hp : p ∈ W), IsFraction
        (X.totalQuotientSheaf.presheaf.germ V₀ (f p) (hW hp) (G₀ : _))
        (X.presheaf.germ V₀ (f p) (hW hp) sa) (X.presheaf.germ V₀ (f p) (hW hp) sb)) ∧
      (∀ (p : Y) (hp : p ∈ W), IsFraction (Y.totalQuotientSheaf.presheaf.germ W p hp (G : _))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hW hp) sa))
        (f.stalkMap p (X.presheaf.germ V₀ (f p) (hW hp) sb))) := by
  obtain ⟨a, b, ⟨g, hg, hab⟩, -, -, g', hg', h'⟩ := h.2 y
  obtain ⟨V₀, hx₀, G₀, sa, sb, hG₀, rfl, rfl, V, hV, hxV, hfrac⟩ := exists_fraction_nhds hg hab
  have hb : IsUnit (stalkToTotalQuotient y
      (f.stalkMap y (X.presheaf.germ V₀ (f y) (hV hxV) sb))) := h'.1
  have ha : IsUnit (stalkToTotalQuotient y
      (f.stalkMap y (X.presheaf.germ V₀ (f y) (hV hxV) sa))) := by
    have := h'.2
    rw [← this]
    exact h'.1.mul hg'.isUnit
  obtain ⟨W, hW, hyW, G, hG⟩ := exists_pullback_fraction_nhds f hV sa sb hxV ha hb
  refine ⟨V₀, G₀, sa, sb, W, fun p hp => hV (hW hp), hyW, G, hG₀, ?_,
    fun p hp => hfrac (f p) (hW hp), hG⟩
  exact isLocalEquationOn_of_forall_isLocalEquationAt fun p hp =>
    h.isLocalEquationAt ⟨V₀, hV (hW hp), G₀, hG₀, rfl⟩ (hfrac (f p) (hW hp)) (hG p hp)

/-- Restricting the pull-back of a section is pulling back its restriction, then restricting. -/
private theorem map_map_pullbackUnit {X Y : Scheme.{u}} (f : Y ⟶ X) (A : X.Modules)
    {U U' : X.Opens} (hU : U' ≤ U) {W V : Y.Opens} (hW : W ≤ f ⁻¹ᵁ U) (hVW : V ≤ W)
    (hV : V ≤ f ⁻¹ᵁ U') (x : Γ(A, U)) :
    ((Scheme.Modules.pullback f).obj A).val.map (homOfLE hVW).op
        (((Scheme.Modules.pullback f).obj A).val.map (homOfLE hW).op
          (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom A (op U) x)) =
      ((Scheme.Modules.pullback f).obj A).val.map (homOfLE hV).op
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom A (op U')
          (A.val.map (homOfLE hU).op x)) := by
  have h : ((Scheme.Modules.pullback f).obj A).val.map (homOfLE (fun p hp => hU hp :
        f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U)).op
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom A (op U) x) =
      Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom A (op U')
        (A.val.map (homOfLE hU).op x) :=
    Stacks.RingedSpace.pullbackUnit_restrict f.toLRSHom.toShHom A (homOfLE hU).op x
  rw [← h]
  exact (modules_map_map _ _ _ _).trans (modules_map_map _ _ _ _).symm

/-- The pull-back of the line bundle of `B` is the line bundle of a pull-back divisor of `B`. -/
private theorem nonempty_pullback_lineBundle_iso_of_isPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (B : X.CartierDivisor) (B' : Y.CartierDivisor) (h : IsPullback f B B') :
    Nonempty ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf B) ≅
        MMP.CartierDivisor.sheaf B') := by
  classical
  choose V₀ G₀ sa sb W hW hyW G hG₀ hG hfX hfY using exists_pullback_localData h
  let M := (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf B)
  let e : ∀ y, GeneratorSections Y.toRingedSpace (MMP.CartierDivisor.sheaf B') (W y) :=
    fun y => ⟨MMP.CartierDivisor.invSection (hG y),
        MMP.CartierDivisor.isTrivializingGenerator_invSection (hG y)⟩
  let e₀ : ∀ y, GeneratorSections X.toRingedSpace (MMP.CartierDivisor.sheaf B) (V₀ y) :=
    fun y => ⟨MMP.CartierDivisor.invSection (hG₀ y),
        MMP.CartierDivisor.isTrivializingGenerator_invSection (hG₀ y)⟩
  let k : ∀ y, GeneratorSections Y.toRingedSpace M (W y) := fun y =>
    generatorRestrict M (hW y)
      (pullbackGenerator f (MMP.CartierDivisor.sheaf B) (MMP.CartierDivisor.isInvertibleModule_sheaf
          B) (V₀ y) (e₀ y))
  refine ⟨(isoOfTransitionEq (MMP.CartierDivisor.sheaf B') e k ?_ ?_).symm⟩
  · exact fun y _ => Opens.mem_iSup.mpr ⟨y, hyW y⟩
  intro y z V hy hz
  obtain ⟨u, hu⟩ := (hG₀ y).exists_units_eq_mul (hG₀ z)
  have hV : V ≤ f ⁻¹ᵁ (V₀ y ⊓ V₀ z) := fun p hp => ⟨hW y (hy hp), hW z (hz hp)⟩
  let φ : Γ(X, V₀ y ⊓ V₀ z) →+* Γ(Y, V) :=
    (Y.presheaf.map (homOfLE hV).op).hom.comp (f.app (V₀ y ⊓ V₀ z)).hom
  -- the local equations of `B'` on `W y`, `W z` differ on `V` by the pull-back of `u`
  have key : Y.totalQuotientSheaf.obj.map (homOfLE hy).op (G y : _) =
      toTotalQuotient V (φ u) * Y.totalQuotientSheaf.obj.map (homOfLE hz).op (G z : _) := by
    apply TopCat.Presheaf.section_ext Y.totalQuotientSheaf V
    intro p hp
    have hpy : p ∈ W y := hy hp
    have hpz : p ∈ W z := hz hp
    have hq : f p ∈ V₀ y ⊓ V₀ z := hV hp
    have hu' := congrArg (fun g : (X.totalQuotientSheaf.obj.obj (op (V₀ y ⊓ V₀ z)))ˣ =>
      X.totalQuotientSheaf.presheaf.germ _ (f p) hq (g : _)) hu
    simp only [Units.val_mul, map_mul] at hu'
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      germ_toTotalQuotient] at hu'
    rw [map_mul]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, germ_toTotalQuotient]
    have hφ : Y.presheaf.germ V p hp (φ u) =
        f.stalkMap p (X.presheaf.germ _ (f p) hq (u : Γ(X, V₀ y ⊓ V₀ z))) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hφ]
    exact eq_map_mul_of_isFraction (stalkToTotalQuotient (f p))
      (stalkToTotalQuotient_injective (f p)) (stalkToTotalQuotient p) (f.stalkMap p).hom
      (hfX y p hpy).2 (hfX z p hpz).2 hu' (hfY y p hpy).1 (hfY z p hpz).1 (hfY y p hpy).2
      (hfY z p hpz).2
  refine (generatorRatioUnit_eq _ V _ _ (Units.map φ.toMonoidHom u⁻¹) ?_).trans
    (generatorRatioUnit_eq _ V _ _ (Units.map φ.toMonoidHom u⁻¹) ?_).symm
  · apply MMP.CartierDivisorSheaf.sectionVal_injective (F := B') (V := V)
    change Y.totalQuotientSheaf.obj.map (homOfLE hy).op (↑(G y)⁻¹ : _) =
      toTotalQuotient V (φ ↑u⁻¹) * Y.totalQuotientSheaf.obj.map (homOfLE hz).op (↑(G z)⁻¹ : _)
    have hA : Y.totalQuotientSheaf.obj.map (homOfLE hy).op (G y : _) *
        Y.totalQuotientSheaf.obj.map (homOfLE hy).op (↑(G y)⁻¹ : _) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hZ : Y.totalQuotientSheaf.obj.map (homOfLE hz).op (G z : _) *
        Y.totalQuotientSheaf.obj.map (homOfLE hz).op (↑(G z)⁻¹ : _) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hc : toTotalQuotient V (φ u) * toTotalQuotient V (φ ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    linear_combination
      (toTotalQuotient V (φ ↑u⁻¹) *
          Y.totalQuotientSheaf.obj.map (homOfLE hz).op (↑(G z)⁻¹ : _)) * hA -
        (toTotalQuotient V (φ ↑u⁻¹) *
          Y.totalQuotientSheaf.obj.map (homOfLE hz).op (↑(G z)⁻¹ : _) *
          Y.totalQuotientSheaf.obj.map (homOfLE hy).op (↑(G y)⁻¹ : _)) * key -
        (Y.totalQuotientSheaf.obj.map (homOfLE hy).op (↑(G y)⁻¹ : _) *
          Y.totalQuotientSheaf.obj.map (homOfLE hz).op (G z : _) *
          Y.totalQuotientSheaf.obj.map (homOfLE hz).op (↑(G z)⁻¹ : _)) * hc -
        Y.totalQuotientSheaf.obj.map (homOfLE hy).op (↑(G y)⁻¹ : _) * hZ
  · let ey : Γ(MMP.CartierDivisor.sheaf B, V₀ y ⊓ V₀ z) := (MMP.CartierDivisor.sheaf B).presheaf.map
      (homOfLE (inf_le_left : V₀ y ⊓ V₀ z ≤ V₀ y)).op (MMP.CartierDivisor.invSection (hG₀ y))
    let ez : Γ(MMP.CartierDivisor.sheaf B, V₀ y ⊓ V₀ z) := (MMP.CartierDivisor.sheaf B).presheaf.map
      (homOfLE (inf_le_right : V₀ y ⊓ V₀ z ≤ V₀ z)).op (MMP.CartierDivisor.invSection (hG₀ z))
    have hX : ey = (↑u⁻¹ : Γ(X, V₀ y ⊓ V₀ z)) • ez := by
      apply MMP.CartierDivisorSheaf.sectionVal_injective (F := B) (V := V₀ y ⊓ V₀ z)
      change X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V₀ y ⊓ V₀ z ≤ V₀ y)).op
          (↑(G₀ y)⁻¹ : _) = toTotalQuotient _ (↑u⁻¹ : Γ(X, V₀ y ⊓ V₀ z)) *
          X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : V₀ y ⊓ V₀ z ≤ V₀ z)).op
            (↑(G₀ z)⁻¹ : _)
      have := congrArg (fun g : (X.totalQuotientSheaf.obj.obj (op (V₀ y ⊓ V₀ z)))ˣ =>
        ((g⁻¹ : _ˣ) : X.totalQuotientSheaf.obj.obj (op (V₀ y ⊓ V₀ z)))) hu
      simp only [mul_inv_rev, ← map_inv, Units.val_mul, Units.coe_map] at this
      rwa [mul_comm] at this
    have hy' := map_map_pullbackUnit f (MMP.CartierDivisor.sheaf B)
      (inf_le_left : V₀ y ⊓ V₀ z ≤ V₀ y) (hW y) hy hV (MMP.CartierDivisor.invSection (hG₀ y))
    have hz' := map_map_pullbackUnit f (MMP.CartierDivisor.sheaf B)
      (inf_le_right : V₀ y ⊓ V₀ z ≤ V₀ z) (hW z) hz hV (MMP.CartierDivisor.invSection (hG₀ z))
    refine (hy'.trans ?_).trans (congrArg (fun m : Γ(M, V) => (φ ↑u⁻¹) • m) hz'.symm)
    change M.val.map (homOfLE hV).op
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (MMP.CartierDivisor.sheaf B) _ ey) =
      (φ ↑u⁻¹) • M.presheaf.map (homOfLE hV).op
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom (MMP.CartierDivisor.sheaf B) _ ez)
    rw [hX]
    have hs := Stacks.RingedSpace.pullbackUnit_smul f.toLRSHom.toShHom (MMP.CartierDivisor.sheaf B)
      (op (V₀ y ⊓ V₀ z)) (↑u⁻¹ : Γ(X, V₀ y ⊓ V₀ z)) ez
    refine (congrArg (fun m => M.val.map (homOfLE hV).op m) hs).trans ?_
    exact PresheafOfModules.map_smul _ _ _ _

/-! ### The ideal sheaf of the subscheme of an effective Cartier divisor -/

/-- Around every point of an open `V` there is an affine open `U' ⊆ V` on which `D` has a local
equation `s ∈ Γ(U', 𝒪)` generating the ideal of `I`. -/
private theorem exists_affine_localEquation_le {Y : Scheme.{u}}
    {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) {V : Y.Opens} {x : Y}
    (hx : x ∈ V) :
    ∃ (U : Y.affineOpens) (_ : (U : Y.Opens) ≤ V) (_ : x ∈ (U : Y.Opens)) (s : Γ(Y, U))
      (hs : IsUnit (toTotalQuotient (U : Y.Opens) s)),
      IsLocalEquationOn D U hs.unit ∧ I.ideal U = Ideal.span {s} := by
  obtain ⟨U₀, hxU₀, s₀, hs₀, hloc, hid⟩ := hDI x
  obtain ⟨f, hfV, hxf⟩ := U₀.2.exists_basicOpen_le (V := V) ⟨x, hx⟩ hxU₀
  let U : Y.affineOpens := Y.affineBasicOpen f
  have hUU₀ : (U : Y.Opens) ≤ U₀ := Y.basicOpen_le f
  let s : Γ(Y, U) := Y.presheaf.map (homOfLE hUU₀).op s₀
  have hsres : toTotalQuotient (U : Y.Opens) s =
      Y.totalQuotientSheaf.obj.map (homOfLE hUU₀).op (toTotalQuotient (U₀ : Y.Opens) s₀) :=
    toTotalQuotient_res hUU₀ s₀
  have hs : IsUnit (toTotalQuotient (U : Y.Opens) s) := by
    rw [hsres]
    exact hs₀.map _
  refine ⟨U, hfV, hxf, s, hs, ?_, ?_⟩
  · convert hloc.res hUU₀ using 2
    exact Units.ext (by rw [IsUnit.unit_spec, hsres]; rfl)
  · rw [← I.map_ideal (show U ≤ U₀ from hUU₀), hid, Ideal.map_span, Set.image_singleton]
    rfl

/-- If `i.app V a = 0`, then `i` also kills the restriction of `a` to `V' ≤ V`. -/
private theorem app_res_eq_zero {Y Z : Scheme.{u}} (i : Z ⟶ Y) {V V' : Y.Opens} (h : V' ≤ V)
    {a : Γ(Y, V)} (ha : i.app V a = 0) :
    i.app V' ((Y.presheaf.map (homOfLE h).op).hom a) = 0 := by
  have := congr(($(i.naturality (homOfLE h).op)).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, ha, map_zero]

private theorem mem_lineBundleSections_neg_of_app_subschemeι_eq_zero {Y : Scheme.{u}}
    {I : Y.IdealSheafData} {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) {V : Y.Opens}
    {a : Γ(Y, V)}
    (ha : I.subschemeι.app V a = 0) : toTotalQuotient V a ∈ lineBundleSections (-D) V := by
  refine mem_lineBundleSections_of_locally _ fun x hx => ?_
  obtain ⟨U, hUV, hxU, s, hs, hloc, hid⟩ := exists_affine_localEquation_le hDI hx
  refine ⟨U, homOfLE hUV, hxU, ?_⟩
  have hker : (Y.presheaf.map (homOfLE hUV).op).hom a ∈ I.ideal U := by
    rw [← I.ker_subschemeι_app U, RingHom.mem_ker]
    exact app_res_eq_zero _ hUV ha
  rw [hid, Ideal.mem_span_singleton'] at hker
  obtain ⟨r, hr⟩ := hker
  rw [← toTotalQuotient_res hUV a, mem_lineBundleSections_iff_of_isLocalEquationOn' hloc.inv]
  refine ⟨r, ?_⟩
  rw [inv_inv, IsUnit.unit_spec, ← map_mul, hr]

private theorem app_subschemeι_eq_zero_of_mem_lineBundleSections_neg {Y : Scheme.{u}}
    {I : Y.IdealSheafData} {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) {V : Y.Opens}
    {a : Γ(Y, V)}
    (ha : toTotalQuotient V a ∈ lineBundleSections (-D) V) : I.subschemeι.app V a = 0 := by
  apply TopCat.Presheaf.section_ext I.subscheme.sheaf (I.subschemeι ⁻¹ᵁ V)
  intro z hz
  obtain ⟨U, hUV, hxU, s, hs, hloc, hid⟩ := exists_affine_localEquation_le hDI hz
  have hmem := res_mem (-D) hUV ha
  rw [← toTotalQuotient_res hUV a, mem_lineBundleSections_iff_of_isLocalEquationOn' hloc.inv,
    inv_inv, IsUnit.unit_spec] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [← map_mul] at hr
  have hres : I.subschemeι.app U ((Y.presheaf.map (homOfLE hUV).op).hom a) = 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app U, hid, ← injective_toTotalQuotient _ hr]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hzU : z ∈ I.subschemeι ⁻¹ᵁ (U : Y.Opens) := hxU
  have h1 := TopCat.Presheaf.germ_res_apply I.subscheme.presheaf
    (homOfLE (fun w hw => hUV hw : I.subschemeι ⁻¹ᵁ (U : Y.Opens) ≤ I.subschemeι ⁻¹ᵁ V)) z hzU
    (I.subschemeι.app V a)
  have h2 := congr(($(I.subschemeι.naturality (homOfLE hUV).op)).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  erw [map_zero]
  refine h1.symm.trans ?_
  erw [← h2, hres, map_zero]
  rfl

/-- **The ideal of the subscheme of `D` is `𝒪_Y(-D)`, on sections.** A section `a` of `𝒪_Y` over
`V` is killed by `I.subscheme ⟶ Y` exactly when, in `𝓜_Y`, it is a section of `𝒪_Y(-D)`. -/
private theorem app_subschemeι_eq_zero_iff {Y : Scheme.{u}}
    {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) (V : Y.Opens) (a : Γ(Y, V)) :
    I.subschemeι.app V a = 0 ↔ toTotalQuotient V a ∈ lineBundleSections (-D) V :=
  ⟨mem_lineBundleSections_neg_of_app_subschemeι_eq_zero hDI,
    app_subschemeι_eq_zero_of_mem_lineBundleSections_neg hDI⟩

/-- Every section of `𝒪_Y(-D)` is a section of `𝒪_Y`. -/
private theorem exists_toTotalQuotient_eq_of_mem_neg {Y : Scheme.{u}}
    {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) {V : Y.Opens}
    {σ : Y.totalQuotientSheaf.obj.obj (op V)} (hσ : σ ∈ lineBundleSections (-D) V) :
    ∃ a : Γ(Y, V), toTotalQuotient V a = σ := by
  refine exists_toTotalQuotient_eq_of_germ_mem σ fun x hx => ?_
  obtain ⟨U, hUV, hxU, s, hs, hloc, -⟩ := exists_affine_localEquation_le hDI hx
  have hmem := res_mem (-D) hUV hσ
  rw [mem_lineBundleSections_iff_of_isLocalEquationOn' hloc.inv, inv_inv,
    IsUnit.unit_spec] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [← map_mul] at hr
  refine ⟨Y.presheaf.germ (U : Y.Opens) x hxU (r * s), ?_⟩
  rw [← germ_toTotalQuotient, hr]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- A section of the ideal of `I`, as a section of `𝒪_Y(-D) ⊆ 𝓜_Y`. -/
private noncomputable def kerToNeg {Y : Scheme.{u}} {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) (V : Y.Opens) :
    (SheafOfModules.kerSubmodule (Stacks.Divisors.structureModuleHom I.subschemeι)
        ).toSheafOfModules.val.obj (op V) →ₗ[Y.ringCatSheaf.obj.obj (op V)]
      (MMP.CartierDivisor.sheaf (-D)).val.obj (op V) where
  toFun a := MMP.CartierDivisor.sectionOfMem ((app_subschemeι_eq_zero_iff hDI V a.1).mp
    ((Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff _ V a.1).mp a.2))
  map_add' a b := Subtype.ext (map_add (toTotalQuotient V) a.1 b.1)
  map_smul' c a := Subtype.ext (map_mul (toTotalQuotient V) c a.1)

private theorem kerToNeg_bijective {Y : Scheme.{u}}
    {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) (V : Y.Opens) :
    Function.Bijective (kerToNeg hDI V) := by
  refine ⟨fun a b h => Subtype.ext (injective_toTotalQuotient V (congrArg Subtype.val h)),
    fun σ => ?_⟩
  obtain ⟨a, ha⟩ := exists_toTotalQuotient_eq_of_mem_neg hDI
    (MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ)
  refine ⟨⟨a, (Stacks.Divisors.mem_kerSubmodule_structureModuleHom_iff _ V a).mpr
    ((app_subschemeι_eq_zero_iff hDI V a).mpr
      (ha ▸ (MMP.CartierDivisor.sectionVal_mem_lineBundleSections σ)))⟩, Subtype.ext ha⟩

/-- **`ℐ ≅ 𝒪_Y(-D)`**: the ideal sheaf of the subscheme of the effective Cartier divisor `D` is
the line bundle of `-D`. -/
private theorem nonempty_idealSheaf_iso_lineBundle_neg {Y : Scheme.{u}}
    {I : Y.IdealSheafData}
    {D : Y.CartierDivisor} (hDI : IsSubschemeOfEffective D I) :
    Nonempty (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom ≅
      MMP.CartierDivisor.sheaf (-D)) := by
  refine ⟨Stacks.Divisors.idealSheafIsoKerSubmodule _ ≪≫
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun V => (LinearEquiv.ofBijective (kerToNeg hDI V.unop)
          (kerToNeg_bijective hDI V.unop)).toModuleIso) ?_)⟩
  intro V V' g
  refine ModuleCat.hom_ext (LinearMap.ext fun a => Subtype.ext ?_)
  change toTotalQuotient V'.unop ((Y.presheaf.map (homOfLE (leOfHom g.unop)).op).hom a.1) =
    Y.totalQuotientSheaf.obj.map (homOfLE (leOfHom g.unop)).op (toTotalQuotient V.unop a.1)
  exact toTotalQuotient_res _ _

/-! ### Ranks, determinants and the tensor algebra -/

/-- **The quotient of a short exact sequence of finite locally free modules has the complementary
constant rank.** If `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is short exact, `ℱ₁` has rank `a`, `ℱ₂` has rank
`a + c` and `ℱ₃` is finite locally free, then `ℱ₃` has rank `c`. -/
private theorem isFiniteLocallyFreeOfRank_X₃_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (a c : ℕ)
    (h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ a)
    (h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (a + c))
    (h₃ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c := by
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₃ h₃ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ a).mpr h₁).restrict (U x).ι)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ (a + c) :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ (a + c)).mpr h₂).restrict (U x).ι)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ (r x) := hr x
    have hc : r x = c := by
      have := SheafOfModules.rank_add_of_shortExact (S.map G) hS' a (a + c) (r x)
        (⟨x, hx x⟩ : (U x).toScheme)
      omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hc ▸ hr x)

/-- **The determinant of a short exact sequence with a line subbundle** ([Stacks, Tag 0B38]):
for `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` short exact with `ℱ` of rank one and `ℒ` of rank `m + 1`,
`⋀¹ ℱ ⊗ ⋀^{m+1} ℒ ≅ ⋀^{m+2} ℰ`. -/
private theorem nonempty_tensor_exteriorPower_iso {X : Scheme.{u}} {F E L : X.Modules}
    (i : F ⟶ E) (q : E ⟶ L) (w : i ≫ q = 0) (hS : (ShortComplex.mk i q w).ShortExact) (m : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1]
    [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L (m + 1)] :
    Nonempty (Scheme.Modules.exteriorPower F ((1 : ℕ) : ℤ) ⊗
        Scheme.Modules.exteriorPower L ((m + 1 : ℕ) : ℤ) ≅
      Scheme.Modules.exteriorPower E ((1 + (m + 1) : ℕ) : ℤ)) :=
  ⟨@asIso _ _ _ _ _ (@Stacks.SheafOfModules.TopWedge.isIso_detComparison _ X.sheaf F E L
    (_root_.SheafOfModules.algebras _ F) (_root_.SheafOfModules.algebras _ E)
    (_root_.SheafOfModules.algebras _ L) i q w hS.exact hS.mono_f hS.epi_g 1 m hF hL)⟩

/-- **Adjunction for a smooth effective Cartier divisor.** Let `Y` be separated and smooth of
relative dimension `n + 1` over a field `k`, and `T = I.subscheme`, with closed immersion
`i : T ⟶ Y`, the closed subscheme of a Cartier divisor `D` on `Y`, smooth over `k`.
Then `i^*(Ω^{n+1}_{Y/k} ⊗ 𝒪_Y(D)) ≅ Ω^n_{T/k}`, that is `i^*(ω_Y ⊗ 𝒪_Y(T)) ≅ ω_T`.
Neither `Y` nor `T` need be integral. -/
public theorem nonempty_pullback_canonical_twist_iso
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] {n : ℕ} [SmoothOfRelativeDimension (n + 1) sY]
    (I : Y.IdealSheafData) [Smooth (I.subschemeι ≫ sY)]
    (D : Y.CartierDivisor) (hDI : IsSubschemeOfEffective D I) :
    Nonempty ((Scheme.Modules.pullback I.subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms sY (n + 1) ⊗ MMP.CartierDivisor.sheaf D) ≅
      Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ sY) n) := by
  classical
  let i := I.subschemeι
  let S := Stacks.ConormalSequenceRight.conormalShortComplex i sY
  have hS : S.ShortExact :=
    Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i sY inferInstance
  -- the conormal sheaf is `i^* 𝒪_Y(-D)`
  obtain ⟨eI⟩ := nonempty_idealSheaf_iso_lineBundle_neg hDI
  let eC : S.X₁ ≅ (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf (-D)) :=
    (RingedSpaceModuleAdjunction.modulePullback i.liftCoborder.toLRSHom.toShHom).mapIso
      (Stacks.SheafOfModules.kernelIsoKerObj _).symm ≪≫
      Stacks.CartierConormal.conormalSheafIsoNegativeTwist I ≪≫
      (Scheme.Modules.pullback i).mapIso eI
  -- ranks
  haveI hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eC.symm
      (Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj i _ 1)
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials sY) (n + 1) :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sY (n + 1)
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (1 + n) := by
    rw [Nat.add_comm]
    exact Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj i _ (n + 1)
  haveI h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ n :=
    isFiniteLocallyFreeOfRank_X₃_of_shortExact S hS 1 n hC h₂
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (i ≫ sY))
  -- `i^* Ω^{n+1}_{Y/k} ≅ 𝒞 ⊗ Ω^n_{T/k}`
  have key : Nonempty ((Scheme.Modules.pullback i).obj
      (Scheme.Hom.relativeDifferentialForms sY (n + 1)) ≅
      S.X₁ ⊗ Scheme.Hom.relativeDifferentialForms (i ≫ sY) n) := by
    have eP := Scheme.Modules.exteriorPowerPullbackIso i
      (Scheme.Hom.relativeDifferentials sY) ((n : ℤ) + 1)
    have g₁ := fun (M : I.subscheme.Modules) =>
      @asIso _ _ _ _ (Scheme.Modules.exteriorGenerator M)
        (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_gen _ M
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M))
    rcases n with _ | m
    · -- `Ω_T = 0`, so `𝒞 ≅ i^* Ω_Y`
      have hz : Limits.IsZero S.X₃ := Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero S.X₃
      have hg : S.g = 0 := hz.eq_of_tgt _ _
      haveI := hS.mono_f
      haveI : Epi S.f := hS.exact.epi_f hg
      haveI : IsIso S.f := isIso_of_mono_of_epi S.f
      refine ⟨eP ≪≫ eqToIso (by norm_num <;> rfl) ≪≫ (g₁ S.X₂).symm ≪≫ (asIso S.f).symm ≪≫
        (ρ_ _).symm ≪≫ whiskerLeftIso _
          ((Scheme.Hom.relativeDifferentialFormsZeroIso (i ≫ sY)).symm ≪≫
          eqToIso (by norm_num <;> rfl))⟩
    · obtain ⟨d⟩ := nonempty_tensor_exteriorPower_iso S.f S.g S.zero hS m
      refine ⟨eP ≪≫ eqToIso (by congr 1; push_cast; ring) ≪≫ d.symm ≪≫
        whiskerRightIso ((eqToIso (by norm_num <;> rfl)) ≪≫ (g₁ S.X₁).symm) _ ≪≫
        whiskerLeftIso _ (eqToIso (by push_cast; rfl))⟩
  -- `𝒞 ⊗ i^* 𝒪_Y(D) ≅ 𝒪_T`
  have hCL : Nonempty (S.X₁ ⊗ (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D) ≅
      𝟙_ I.subscheme.Modules) := by
    obtain ⟨e₀⟩ := MMP.Fourfold.nonempty_lineBundle_zero_iso_unit (X := Y)
    exact ⟨whiskerRightIso eC _ ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso i (MMP.CartierDivisor.sheaf (-D))
          (MMP.CartierDivisor.sheaf D)).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (MMP.CartierDivisorSheaf.sheafMulIso (-D) D ≪≫
        eqToIso (by rw [neg_add_cancel]) ≪≫ e₀) ≪≫
      @asIso _ _ _ _ _
        (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u} i.toRingCatSheafHom)⟩
  obtain ⟨e₁⟩ := key
  obtain ⟨e₂⟩ := hCL
  let β : Scheme.Hom.relativeDifferentialForms (i ≫ sY) n ⊗
      (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D) ≅
      (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf D) ⊗
        Scheme.Hom.relativeDifferentialForms (i ≫ sY) n :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding I.subscheme.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf I.subscheme) _ _
  exact ⟨Stacks.RelativeVeryAmple.pullbackTensorModulesIso i _ _ ≪≫ whiskerRightIso e₁ _ ≪≫
    α_ _ _ _ ≪≫ whiskerLeftIso _ β ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e₂ _ ≪≫ λ_ _⟩

/-- **Adjunction for a smooth divisor.** Let `Y` be a smooth variety of dimension `n + 1` over `k`
and `T = I.subscheme` a smooth prime divisor, the subscheme of the effective Cartier divisor `D`.
Then `i^*(Ω^{n+1}_{Y/k} ⊗ 𝒪_Y(D)) ≅ Ω^n_{T/k}`, and for Cartier divisors `K_Y`, `K_T` with
`𝒪_Y(K_Y) ≅ Ω^{n+1}_{Y/k}`, `𝒪_T(K_T) ≅ Ω^n_{T/k}`, every Cartier divisor `B` on `Y` and a
pull-back `B_T` of `B` to `T`: `i^* 𝒪_Y(K_Y + D + B) ≅ 𝒪_T(K_T + B_T)`. -/
@[mmp "lem_mmp_smooth_divisor_adjunction"]
public theorem nonempty_pullback_lineBundle_iso_of_smooth_divisor
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsSeparated sY] {n : ℕ} [SmoothOfRelativeDimension (n + 1) sY]
    (I : Y.IdealSheafData) [IsIntegral I.subscheme] [Smooth (I.subschemeι ≫ sY)]
    (D : Y.CartierDivisor) (_hD : IsEffective D) (hDI : IsSubschemeOfEffective D I) :
    Nonempty ((Scheme.Modules.pullback I.subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms sY (n + 1) ⊗ MMP.CartierDivisor.sheaf D) ≅
      Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ sY) n) ∧
    ∀ (KY B : Y.CartierDivisor) (KT BT : I.subscheme.CartierDivisor),
      Nonempty (MMP.CartierDivisor.sheaf KY ≅ Scheme.Hom.relativeDifferentialForms sY (n + 1)) →
      Nonempty (MMP.CartierDivisor.sheaf KT ≅
          Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ sY) n) →
      IsPullback I.subschemeι B BT →
      Nonempty ((Scheme.Modules.pullback I.subschemeι).obj (MMP.CartierDivisor.sheaf (KY + D + B)) ≅
        MMP.CartierDivisor.sheaf (KT + BT)) := by
  obtain ⟨e₀⟩ := nonempty_pullback_canonical_twist_iso (n := n) sY I D hDI
  refine ⟨⟨e₀⟩, fun KY B KT BT ⟨eY⟩ ⟨eT⟩ hB => ?_⟩
  let i := I.subschemeι
  let a₁ := (MMP.CartierDivisorSheaf.sheafMulIso (KY + D) B).symm
  let a₂ := (MMP.CartierDivisorSheaf.sheafMulIso KY D).symm
  let a₃ := (MMP.CartierDivisorSheaf.sheafMulIso KT BT).symm
  let p₁ : (Scheme.Modules.pullback i).obj (MMP.CartierDivisor.sheaf (KY + D) ⊗
      MMP.CartierDivisor.sheaf B) ≅ _ :=
    Stacks.RelativeVeryAmple.pullbackTensorModulesIso i (MMP.CartierDivisor.sheaf (KY + D))
        (MMP.CartierDivisor.sheaf B)
  obtain ⟨pB⟩ := nonempty_pullback_lineBundle_iso_of_isPullback i B BT hB
  let F := Scheme.Modules.pullback i
  refine ⟨F.mapIso a₁ ≪≫ p₁ ≪≫
    whiskerRightIso (F.mapIso (a₂ ≪≫ whiskerRightIso eY _) ≪≫ e₀ ≪≫ eT.symm) _ ≪≫
    whiskerLeftIso _ pB ≪≫ a₃.symm⟩

end MMP.Intersection

namespace MMP.Mori

open TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Numerical

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

private theorem isQCartier_neg {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hD⟩ := h
  exact ⟨m, hm, by rw [smul_neg]; exact hD.neg⟩

private theorem intersectionNumber_congr {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {D D' : QDivisor X} (h : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D'.intersectionNumber k sX i hdim hD' := by
  subst h
  rfl

private theorem intersectionNumber_neg {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (D : QDivisor X) (hD : D.IsQCartier)
    (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -D.intersectionNumber k sX i hdim hD := by
  have h0 : (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' k sX i hdim 0 0 QDivisor.isQCartier_zero
      QDivisor.isQCartier_zero (QDivisor.isQCartier_zero.add QDivisor.isQCartier_zero)
    rw [intersectionNumber_congr i hdim (add_zero 0) _ QDivisor.isQCartier_zero] at this
    linarith
  have := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD' (hD.add hD')
  rw [intersectionNumber_congr i hdim (add_neg_cancel D) _ QDivisor.isQCartier_zero, h0] at this
  linarith

private theorem numericallyEquivalent_add {D₁ D₂ E₁ E₂ : QDivisor X}
    (hD : D₁.NumericallyEquivalent k sX D₂) (hE : E₁.NumericallyEquivalent k sX E₂) :
    (D₁ + E₁).NumericallyEquivalent k sX (D₂ + E₂) := by
  obtain ⟨h₁, h₂, hD⟩ := hD
  obtain ⟨h₁', h₂', hE⟩ := hE
  refine ⟨h₁.add h₁', h₂.add h₂', fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC.le _ _ h₁ h₁',
    QDivisor.intersectionNumber_add' k sX i hC.le _ _ h₂ h₂', hD C i hC, hE C i hC]

private theorem numericallyEquivalent_neg {D₁ D₂ : QDivisor X}
    (hD : D₁.NumericallyEquivalent k sX D₂) :
    (-D₁).NumericallyEquivalent k sX (-D₂) := by
  obtain ⟨h₁, h₂, hD⟩ := hD
  refine ⟨isQCartier_neg h₁, isQCartier_neg h₂, fun C i _ _ _ hC => ?_⟩
  rw [intersectionNumber_neg i hC.le _ h₁, intersectionNumber_neg i hC.le _ h₂, hD C i hC]

end Numerical

section Restriction

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]

namespace DivisorWithCoeffs

/-- Restriction to a prime divisor `F` is additive on divisors of which `F` is not a
component. -/
public theorem restrictPrimeDivisor_add {R : Type*} [AddCommMonoid R]
    (D E : DivisorWithCoeffs R Y) (F : MMP.Mori.PrimeDivisor Y)
    (hD : D.coeff F = 0) (hE : E.coeff F = 0) :
    (D + E).restrictPrimeDivisor F = D.restrictPrimeDivisor F + E.restrictPrimeDivisor F := by
  haveI : IsNoetherian Y := ⟨⟩
  have hDE : (D + E).coeff F = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hD, hE, add_zero]
  ext Q
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hDE,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hD,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hE]
  exact Finsupp.sum_add_index' (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)

/-- Restriction to a prime divisor `F` commutes with integral multiples. -/
public theorem restrictPrimeDivisor_zsmul {R : Type*} [AddCommGroup R]
    (D : DivisorWithCoeffs R Y) (F : MMP.Mori.PrimeDivisor Y)
    (hD : D.coeff F = 0) (m : ℤ) :
    (m • D).restrictPrimeDivisor F = m • D.restrictPrimeDivisor F := by
  haveI : IsNoetherian Y := ⟨⟩
  have hD' : (m • D).coeff F = 0 := by
    rw [DivisorWithCoeffs.coeff_smul, hD, smul_zero]
  ext Q
  rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hD',
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hD]
  rw [Finsupp.sum_smul_index' (fun _ => smul_zero _), Finsupp.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

end DivisorWithCoeffs

/-- Restriction to a prime divisor `F` commutes with regarding a divisor as a `ℚ`-divisor. -/
public theorem Divisor.restrictPrimeDivisor_toQDivisor (E : Divisor Y)
    (F : MMP.Mori.PrimeDivisor Y) (hE : E.coeff F = 0) :
    (Divisor.toQDivisor E).restrictPrimeDivisor F =
      Divisor.toQDivisor (E.restrictPrimeDivisor F) := by
  haveI : IsNoetherian Y := ⟨⟩
  have hE' : (Divisor.toQDivisor E).coeff F = 0 := by
    rw [Divisor.coeff_toQDivisor, hE, Int.cast_zero]
  ext Q
  rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hE',
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hE]
  change Finsupp.sum (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ) E) _ = _
  rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.sum_mapRange_index (fun _ => smul_zero _)]
  simp [Finsupp.sum]

variable [IsNormal Y]

/-- If `F` is not a component of `D`, then `F ⊄ Supp D`: the subscheme `F` maps no generic point
of a component into `Supp D`. -/
private theorem notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] (D : DivisorWithCoeffs R Y)
    (F : MMP.Mori.PrimeDivisor Y) (hD : D.coeff F = 0) :
    ∀ Z : irreducibleComponents F.idealSheaf.subscheme,
      F.idealSheaf.subschemeι (componentGenericPoint F.idealSheaf.subscheme Z) ∉ D.supp := by
  intro Z hZ
  have := F.integral
  have hsF : F.idealSheaf.subschemeι (componentGenericPoint F.idealSheaf.subscheme Z) =
      F.genericPoint := by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    rfl
  rw [hsF, DivisorWithCoeffs.mem_supp_iff] at hZ
  obtain ⟨E, hE, hmem⟩ := hZ
  have hEF := E.eq_genericPoint_of_mem_support hmem F.coheight_genericPoint
  have : F = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEF
  exact hE (this ▸ hD)

end Restriction

section Projection

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
  [CompactSpace Y] {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {F : PrimeDivisor Y}
  [IsLocallyNoetherian F.idealSheaf.subscheme] [IsNormal F.idealSheaf.subscheme]

/-- **Projection formula for the restriction to a prime divisor.** Suppose that for every Cartier
divisor `E` of which `F` is not a component the restriction `E|_F` is the pull-back of `E` along
`F ⟶ Y`. Then for a `ℚ`-Cartier `ℚ`-divisor `D` of which `F` is not a component, `D|_F` is
`ℚ`-Cartier and `(D|_F · C)_F = (D · C)_Y` for every curve `C ⊆ F`. -/
private theorem exists_isQCartier_restrictPrimeDivisor_intersectionNumber_eq
    (hpb : ∀ (E : Divisor Y) (_ : E.IsCartier) (hE : E.coeff F = 0),
      E.IsPullback F.idealSheaf.subschemeι (notMem_supp_of_coeff_eq_zero E F hE)
        (E.restrictPrimeDivisor F))
    {D : QDivisor Y} (hD : D.IsQCartier) (h0 : D.coeff F = 0) :
    ∃ hq : QDivisor.IsQCartier (D.restrictPrimeDivisor F),
      ∀ (C : Scheme.{u}) (j : C ⟶ F.idealSheaf.subscheme)
        [IsProper (j ≫ F.idealSheaf.subschemeι ≫ sY)]
        [IsProper ((j ≫ F.idealSheaf.subschemeι) ≫ sY)]
        (hdim : topologicalKrullDim C ≤ 1),
        QDivisor.intersectionNumber k (F.idealSheaf.subschemeι ≫ sY) j hdim
          (D.restrictPrimeDivisor F) hq =
          D.intersectionNumber k sY (j ≫ F.idealSheaf.subschemeι) hdim hD := by
  obtain ⟨m, hm, E, hE, hEc⟩ := QDivisor.isQCartier_iff_exists_pos.mp hD
  have hEF : E.coeff F = 0 := by
    have := congrArg (fun G : QDivisor Y => G.coeff F) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, h0, smul_zero] at this
    exact_mod_cast this
  have hp := hpb E hEc hEF
  have hEFc := hp.isCartier hEc
  have hres : Divisor.toQDivisor (E.restrictPrimeDivisor F) =
      (m : ℤ) • D.restrictPrimeDivisor F := by
    rw [← E.restrictPrimeDivisor_toQDivisor F hEF, hE, D.restrictPrimeDivisor_zsmul F h0]
  have hq : QDivisor.IsQCartier (D.restrictPrimeDivisor F) :=
    ⟨m, by exact_mod_cast hm.ne', (⟨E.restrictPrimeDivisor F, hres, hEFc⟩ :
      QDivisor.IsCartierDivisor _)⟩
  refine ⟨hq, ?_⟩
  intro C j _ _ hdim
  have := F.integral
  have := QuasiCompact.compactSpace_of_compactSpace F.idealSheaf.subschemeι
  have := hEc.isInvertibleModule_divisorialSheaf
  have := hEFc.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul k _ j _ _ _ hm _ hEFc hres,
    QDivisor.intersectionNumber_eq_of_smul k sY (j ≫ F.idealSheaf.subschemeι) _ _ _ hm E hEc hE,
    Divisor.degreeOn, Divisor.degreeOn,
    degreeOn_eq_of_iso k _ j _ (hp.divisorialSheafIso (hBc := hEc)),
    degreeOn_pullback_eq_degreeOn_comp (sX := F.idealSheaf.subschemeι ≫ sY) sY
      F.idealSheaf.subschemeι j rfl]

/-- **Restriction preserves numerical equivalence**, granted that restriction of Cartier divisors
to `F` is pull-back along `F ⟶ Y`: for `ℚ`-divisors `D₁ ≡ D₂` on `Y` of which `F` is not a
component, `D₁|_F ≡ D₂|_F` on `F`. -/
private theorem numericallyEquivalent_restrictPrimeDivisor_of_isPullback
    (hpb : ∀ (E : Divisor Y) (_ : E.IsCartier) (hE : E.coeff F = 0),
      E.IsPullback F.idealSheaf.subschemeι (notMem_supp_of_coeff_eq_zero E F hE)
        (E.restrictPrimeDivisor F))
    {D₁ D₂ : QDivisor Y} (h₁ : D₁.coeff F = 0) (h₂ : D₂.coeff F = 0)
    (h : D₁.NumericallyEquivalent k sY D₂) :
    QDivisor.NumericallyEquivalent k (F.idealSheaf.subschemeι ≫ sY)
      (D₁.restrictPrimeDivisor F) (D₂.restrictPrimeDivisor F) := by
  obtain ⟨hD₁, hD₂, hh⟩ := h
  obtain ⟨hq₁, hI₁⟩ := exists_isQCartier_restrictPrimeDivisor_intersectionNumber_eq
    (k := k) (sY := sY) hpb hD₁ h₁
  obtain ⟨hq₂, hI₂⟩ := exists_isQCartier_restrictPrimeDivisor_intersectionNumber_eq
    (k := k) (sY := sY) hpb hD₂ h₂
  refine ⟨hq₁, hq₂, fun C j _ _ _ hC => ?_⟩
  have : IsProper ((j ≫ F.idealSheaf.subschemeι) ≫ sY) := by
    rw [Category.assoc]
    infer_instance
  rw [hI₁ C j hC.le, hI₂ C j hC.le]
  exact hh C (j ≫ F.idealSheaf.subschemeι) hC

end Projection

section PullbackRestriction

/-- On a locally Noetherian normal scheme, the order of vanishing along a prime divisor `Q` of a
nonzero element `t` of `𝒪_{X,Q}` is `length(𝒪_{X,Q}/(t))`. -/
private theorem valuation_toComponent_eq_length {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (Q : MMP.Mori.PrimeDivisor X) {t : Q.localRing} (ht : t ≠ 0) :
    Q.valuation (Q.toComponent.hom t) =
      WithZero.exp ((Module.length Q.localRing (Q.localRing ⧸ Ideal.span {t})).toNat : ℤ) := by
  let := Q.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Q.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Q.localRing := krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  have := Q.isDiscreteValuationRing_localRing
  change Ring.ordFrac Q.localRing (IsLocalization.algEquiv (nonZeroDivisors Q.localRing) _
    (FractionRing Q.localRing) (algebraMap Q.localRing _ t)) = _
  rw [AlgEquiv.commutes, Ring.ordFrac_eq_ord _ ht]
  have hnz : t ∈ nonZeroDivisors Q.localRing := mem_nonZeroDivisors_of_ne_zero ht
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ hnz (n := (Ring.ord Q.localRing t).toNat)
    (ENat.coe_toNat (Ring.ord_ne_top hnz)).symm]
  rfl

/-- If the ideal of `I` on `U` is generated by `g`, its stalk at `x ∈ U` is generated by the germ
of `g`. -/
public theorem stalkIdeal_eq_span_germ_of_ideal_eq_span {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {U : Y.affineOpens} {g : Γ(Y, U)} (h : I.ideal U = Ideal.span {g}) (x : Y)
    (hx : x ∈ (U : Y.Opens)) :
    I.stalkIdeal x = Ideal.span {(Y.presheaf.germ U x hx).hom g} := by
  rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hx, h, Ideal.map_span,
    Set.image_singleton]

/-- **A prime divisor of a smooth variety is an effective Cartier divisor.** A prime divisor `P` of
a smooth variety `Y` over `k` is the closed subscheme of an effective Cartier divisor `τ` whose
Weil divisor is `P` (when `Y` is Noetherian). -/
public theorem PrimeDivisor.exists_isEffective_isSubschemeOfEffective_of_isSmoothVariety
    (k : Type u) [Field k] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Spec (.of k)) [IsSmoothVariety k f] (P : PrimeDivisor Y) :
    ∃ τ : Y.CartierDivisor, MMP.Intersection.IsEffective τ ∧
      MMP.Intersection.IsSubschemeOfEffective τ P.idealSheaf ∧
      ∀ _ : IsNoetherian Y,
        (weilDivisorEquivFinsupp (cartierWeilDivisor τ) : Divisor Y) = Finsupp.single P 1 := by
  classical
  obtain ⟨-, hsm, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k f
  choose U hxU g φ hgerm hloc hideal using hsm P
  have hmemZ : ∀ (x : Y) (Z : irreducibleComponents Y), x ∈ Z.1 := fun x Z => by
    have h := Z.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
    rw [h]
    trivial
  have hcomp : ∀ (x : Y) (Z : irreducibleComponents Y),
      componentGenericPoint Y Z ∈ (U x : Y.Opens) := fun x Z =>
    ((isGenericPoint_componentGenericPoint Y Z).specializes (hmemZ x Z)).mem_open
      (U x).1.isOpen (hxU x)
  have hg0 : ∀ (x y : Y) (hy : y ∈ (U x : Y.Opens)), Y.presheaf.germ (U x) y hy (g x) ≠ 0 := by
    intro x y hy h0
    have hz : g x = 0 := germ_injective_of_isIntegral Y y hy (by rw [h0, map_zero])
    let Z := MMP.Mori.pointComponent x
    have h1 := hgerm x Z (hcomp x Z)
    rw [hz, map_zero] at h1
    haveI := (RationalFunctions.isField_stalk Y Z).nontrivial
    exact (Pi.isUnit_iff.1 (φ x).isUnit Z).ne_zero h1
  have hu : ∀ x, IsUnit (MMP.Intersection.toTotalQuotient (U x : Y.Opens) (g x)) := fun x =>
    isUnit_toTotalQuotientSheaf_app Y.sheaf (U x : Y.Opens) (g x)
      (fun y hy => show Y.presheaf.germ (U x) y hy (g x) ∈ nonZeroDivisors (Y.presheaf.stalk y)
        from mem_nonZeroDivisors_of_ne_zero (hg0 x y hy))
  have hst : ∀ (x p : Y) (hp : p ∈ (U x : Y.Opens)),
      P.idealSheaf.stalkIdeal p = Ideal.span {(Y.presheaf.germ (U x) p hp).hom (g x)} :=
    fun x => stalkIdeal_eq_span_germ_of_ideal_eq_span _ (hideal x)
  have hU : iSup (fun x => (U x : Y.Opens)) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨C, hC⟩ := MMP.Intersection.exists_isLocalEquationOn_of_germ_eq_mul
    (fun x => (U x : Y.Opens)) hU (fun x => (hu x).unit) (by
    intro i j p hi hj
    have hassoc : Associated (Y.presheaf.germ (U i) p hi (g i))
        (Y.presheaf.germ (U j) p hj (g j)) :=
      Ideal.span_singleton_eq_span_singleton.mp ((hst i p hi).symm.trans (hst j p hj))
    obtain ⟨w, hw⟩ := hassoc
    refine ⟨w, ?_⟩
    simp only [IsUnit.unit_spec]
    rw [MMP.Intersection.germ_toTotalQuotient, MMP.Intersection.germ_toTotalQuotient, ← hw,
      map_mul])
  refine ⟨C, fun x => ⟨U x, hxU x, g x, hu x, hC x⟩,
    fun x => ⟨U x, hxU x, g x, hu x, hC x, hideal x⟩, fun _ => ?_⟩
  ext Q
  set x := Q.genericPoint
  haveI : Nonempty (U x : Y.Opens) := ⟨⟨x, hxU x⟩⟩
  change (cartierWeilDivisor C).1 Q = _
  rw [cartierWeilDivisor_apply_of_local_eq C Q (U x : Y.Opens) (hxU x) (g x) 1 one_ne_zero
      (Additive.ofMul (hu x).unit) (by
        change (MMP.Intersection.toTotalQuotient (U x : Y.Opens) (g x)) *
          MMP.Intersection.toTotalQuotient (U x : Y.Opens) 1 = _
        rw [map_one, mul_one]
        rfl)
      ((hC x).symm.trans (MMP.Intersection.cartierClass_eq_raw _ _))]
  have h1 : Module.length (Y.presheaf.stalk Q.genericPoint)
      ((Y.presheaf.stalk Q.genericPoint) ⧸
        Ideal.span {Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x) 1}) = 0 := by
    rw [map_one, Ideal.span_singleton_one]
    have : Subsingleton ((Y.presheaf.stalk Q.genericPoint) ⧸ (⊤ : _root_.Ideal _)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
  rw [h1, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  -- the coefficient of `P` at `Q` is the order of `g` along `Q`
  have hQ : (Q.support ∩ ((U x : Y.Opens) : Set Y)).Nonempty :=
    (MMP.Mori.PrimeDivisor.genericPoint_mem_iff Q _).mp (hxU x)
  have hc := hloc x Q hQ
  rw [hc]
  have ht0 : Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x) (g x) ≠ 0 := hg0 x _ _
  have hv := Q.valuation_component (φ x)
  rw [hgerm x Q.component (hcomp x Q.component)] at hv
  have hsp : Q.toComponent.hom ((Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x)).hom
      (g x)) = (Y.presheaf.germ (U x : Y.Opens) _ (hcomp x Q.component)).hom (g x) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply ..
  rw [← hsp, valuation_toComponent_eq_length Q ht0] at hv
  exact WithZero.exp_injective hv

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {F : PrimeDivisor Y} [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme]

/-- The ideal of every prime divisor is locally generated by one regular function which is a
local equation of it (the second clause of
`MMP.Mori.Divisor.cartier_weil_dictionary_of_isSmoothVariety`). -/
private def HasPrincipalLocalEquations (Y : Scheme.{u}) [IsLocallyNoetherian Y] [IsNormal Y] :
    Prop :=
  ∀ (P : MMP.Mori.PrimeDivisor Y) (x : Y), ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
    ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
        (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
      Divisor.IsLocalEquation (Finsupp.single P 1) U φ ∧
      P.idealSheaf.ideal U = Ideal.span {g}

/-- **Restriction of a prime divisor is its pull-back.** If the ideal of every prime divisor of
`Y` is locally principal, generated by a local equation `g`, then for a prime divisor `P ≠ F`,
`P|_F = i^*P`: at a prime divisor `Q` of `F`, both coefficients are `length(𝒪_{F,Q}/(g|_F))`. -/
private theorem isPullback_single_restrictPrimeDivisor (hsm : HasPrincipalLocalEquations Y)
    (P : MMP.Mori.PrimeDivisor Y) (hPF : P ≠ F)
    (hP0 : DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ)) F = 0) :
    Divisor.IsPullback F.idealSheaf.subschemeι (Finsupp.single P 1)
      (notMem_supp_of_coeff_eq_zero _ F hP0)
      (DivisorWithCoeffs.restrictPrimeDivisor (Finsupp.single P (1 : ℤ)) F) := by
  haveI : IsNoetherian Y := ⟨⟩
  refine Divisor.IsPullback.of_forall_exists fun Q => ?_
  set i := F.idealSheaf.subschemeι with hi
  obtain ⟨U, hyU, g, φ, hgerm, hloc, hideal⟩ := hsm P (i Q.genericPoint)
  have hE : (Q.support ∩ i ⁻¹ᵁ (U : Y.Opens)).Nonempty :=
    (Q.genericPoint_mem_iff _).mp (show Q.genericPoint ∈ i ⁻¹ᵁ (U : Y.Opens) from hyU)
  refine ⟨U, φ, hloc, hE, ?_⟩
  have hst := stalkIdeal_eq_span_germ_of_ideal_eq_span P.idealSheaf hideal
  -- the element `t = g|_F` of `𝒪_{F,Q}`
  set t : Q.localRing := (i.stalkMap Q.genericPoint).hom ((Y.presheaf.germ U _ hyU).hom g)
    with ht
  -- the left-hand side is `length(𝒪_{F,Q}/(t))`
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hP0, Finsupp.sum_single_index (by simp),
    MMP.Mori.PrimeDivisor.intersectionLength, hst _ hyU, Ideal.map_span, Set.image_singleton]
  change (((Module.length Q.localRing (Q.localRing ⧸ Ideal.span {t})).toNat : ℕ) • (1 : ℤ)) = _
  -- the right-hand side
  set z := componentGenericPoint F.idealSheaf.subscheme Q.component with hz
  have hZ : i z ∈ (U : Y.Opens) := Q.map_componentGenericPoint_mem i hE
  have hzP : i z ∉ P.support := by
    intro hmem
    refine notMem_supp_of_coeff_eq_zero _ F hP0 Q.component ?_
    rw [DivisorWithCoeffs.mem_supp_iff]
    exact ⟨P, by simp [DivisorWithCoeffs.coeff_apply], hmem⟩
  have hunit : IsUnit ((Y.presheaf.germ U (i z) hZ).hom g) := by
    rw [← Ideal.span_singleton_eq_top, ← hst _ hZ]
    exact P.idealSheaf.stalkIdeal_eq_top_of_notMem_support hzP
  set W := MMP.Mori.pointComponent (i z)
  have hW : i z ∈ W.1 := MMP.Mori.mem_pointComponent _
  have hWU : componentGenericPoint Y W ∈ (U : Y.Opens) :=
    ((isGenericPoint_componentGenericPoint Y W).specializes hW).mem_open U.1.isOpen hZ
  have ha : (MMP.Mori.stalkToRationalFunctions Y hW).hom hunit.unit =
      (φ : RationalFunctions Y) W := by
    rw [hgerm W hWU, IsUnit.unit_spec]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply ..
  rw [MMP.Mori.pullbackComponent_eq _ hloc _ hW hunit.unit ha]
  set u := Units.map (i.stalkMap z).hom.toMonoidHom hunit.unit
  have hu : (u : F.idealSheaf.subscheme.presheaf.stalk z) = Q.toComponent.hom t := by
    change (i.stalkMap z).hom ((Y.presheaf.germ U (i z) hZ).hom g) =
      (F.idealSheaf.subscheme.presheaf.stalkSpecializes _).hom
        ((i.stalkMap Q.genericPoint).hom ((Y.presheaf.germ U _ hyU).hom g))
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply ..).symm
  have ht0 : t ≠ 0 := by
    intro h0
    have : (u : F.idealSheaf.subscheme.presheaf.stalk z) = 0 := by rw [hu, h0, map_zero]
    exact u.ne_zero this
  have h1 := Q.valuation_eq_exp_ordUnit u
  rw [hu, valuation_toComponent_eq_length Q ht0] at h1
  rw [← WithZero.exp_injective h1, nsmul_eq_mul, mul_one]

/-- **Restriction of a divisor is its pull-back**, under the hypotheses of
`isPullback_single_restrictPrimeDivisor` and that every divisor of `Y` is Cartier. -/
private theorem isPullback_restrictPrimeDivisor_of_hasPrincipalLocalEquations
    (hsm : HasPrincipalLocalEquations Y) (hcart : ∀ D : Divisor Y, D.IsCartier)
    (E : Divisor Y) (hEF : E.coeff F = 0) :
    Divisor.IsPullback F.idealSheaf.subschemeι E (notMem_supp_of_coeff_eq_zero E F hEF)
      (DivisorWithCoeffs.restrictPrimeDivisor E F) := by
  haveI : IsNoetherian Y := ⟨⟩
  induction E using Finsupp.induction with
  | zero =>
    have h0 : DivisorWithCoeffs.restrictPrimeDivisor (0 : Divisor Y) F = 0 := by
      ext Q
      rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ F hEF, Finsupp.sum_zero_index]
      rfl
    rw [h0]
    exact Divisor.isPullback_zero _
  | single_add P a E' hP ha ih =>
    have hEF' : DivisorWithCoeffs.coeff E' F = 0 ∧ P ≠ F := by
      by_cases hPF : P = F
      · subst hPF
        have h1 : DivisorWithCoeffs.coeff E' P = 0 := Finsupp.notMem_support_iff.mp hP
        exfalso
        apply ha
        rw [DivisorWithCoeffs.coeff_add, h1, add_zero] at hEF
        simpa [DivisorWithCoeffs.coeff_apply] using hEF
      · refine ⟨?_, hPF⟩
        rw [DivisorWithCoeffs.coeff_add] at hEF
        simpa [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hPF] using hEF
    obtain ⟨hE'F, hPF⟩ := hEF'
    have hP0 : DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ)) F = 0 := by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hPF]
    have hPa0 : DivisorWithCoeffs.coeff (Finsupp.single P a) F = 0 := by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hPF]
    have hsa : (Finsupp.single P a : Divisor Y) = a • (Finsupp.single P 1 : Divisor Y) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h₁ : Divisor.IsPullback F.idealSheaf.subschemeι (Finsupp.single P a)
        (notMem_supp_of_coeff_eq_zero _ F hPa0)
        (a • DivisorWithCoeffs.restrictPrimeDivisor (Finsupp.single P (1 : ℤ)) F) :=
      Divisor.IsPullback.of_eq hsa.symm
        (Divisor.IsPullback.zsmul (hcart _)
          (isPullback_single_restrictPrimeDivisor hsm P hPF hP0) a
          (by rw [← hsa]; exact notMem_supp_of_coeff_eq_zero _ F hPa0))
    have hres : DivisorWithCoeffs.restrictPrimeDivisor (Finsupp.single P a + E' : Divisor Y) F =
        a • DivisorWithCoeffs.restrictPrimeDivisor (Finsupp.single P (1 : ℤ)) F +
          DivisorWithCoeffs.restrictPrimeDivisor E' F := by
      rw [DivisorWithCoeffs.restrictPrimeDivisor_add _ _ F hPa0 hE'F, hsa,
        DivisorWithCoeffs.restrictPrimeDivisor_zsmul _ F hP0]
    rw [hres]
    exact Divisor.IsPullback.add (hcart _) (hcart _) _ h₁ (ih hE'F)

end PullbackRestriction

section Canonical

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- **The divisorial sheaf of a canonical divisor is the sheaf of top forms.** Let `X` be a
locally Noetherian normal scheme, smooth over a field `k` via `f`, and `K` a canonical divisor of
`X` of dimension `n` (its divisorial sheaf agrees with `Ω^n_{X/k}` on the smooth locus). Then
`𝒪_X(K) ≅ Ω^n_{X/k}` on all of `X`. -/
public theorem nonempty_divisorialSheaf_iso_of_isCanonicalDivisor {f : X ⟶ Spec (.of k)}
    (hf : MMP.Mori.IsSmoothScheme f) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms f n) := by
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso (smoothLocus f).ι f _ rfl n
  exact MMP.Flips.nonempty_iso_of_restrict_iso hf (hK.iso ≪≫ e₁.symm)

/-- **Linear equivalence implies numerical equivalence** for Cartier divisors. -/
private theorem numericallyEquivalent_toQDivisor_of_linearlyEquivalent [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {D₁ D₂ : Divisor X}
    (h : D₁.LinearlyEquivalent D₂) (h₁ : D₁.IsCartier) (h₂ : D₂.IsCartier) :
    (Divisor.toQDivisor D₁).NumericallyEquivalent k sX (Divisor.toQDivisor D₂) := by
  have hq₁ : (Divisor.toQDivisor D₁).IsQCartier := ⟨1, one_ne_zero, D₁, by rw [one_smul], h₁⟩
  have hq₂ : (Divisor.toQDivisor D₂).IsQCartier := ⟨1, one_ne_zero, D₂, by rw [one_smul], h₂⟩
  refine ⟨hq₁, hq₂, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq₁ one_pos D₁ h₁
      (by rw [Nat.cast_one, one_smul]),
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hq₂ one_pos D₂ h₂
      (by rw [Nat.cast_one, one_smul])]
  haveI := h₁.isInvertibleModule_divisorialSheaf
  haveI := h₂.isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, Divisor.degreeOn, degreeOn_eq_of_iso k sX i _ h.divisorialSheafIso]

end Canonical

section Strip

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
  {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
  {j₀ : Fin s} {c : ℚ}

/-- The divisor `p'H + q'a(K_X + Δ)` of a rationality datum is a Cartier divisor, hence
`ℚ`-Cartier. -/
private theorem isQCartier_stripDivisor (hR : IsRationalityDatum sX n K Δ a H) (p' q' : ℤ) :
    (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsQCartier := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := hR.isCartierDivisor
  refine ⟨1, one_ne_zero, p' • H + q' • D₀, ?_, (hR.isCartier_H.zsmul p').add (hD₀c.zsmul q')⟩
  rw [one_smul, map_add, map_zsmul, map_zsmul, hD₀, mul_smul]

/-- The source `Y` of a strip tie-breaker is a smooth variety over `k`. -/
private theorem isSmoothVariety_of_isStripTieBreaker
    (hT : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) : IsSmoothVariety k (f ≫ sX) :=
  have hv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hT.isProjectiveVariety.toIsVariety
  { toIsVariety := hv
    toSmooth := (MMP.Mori.isSmoothScheme_iff _).mp hT.isLogResolution.isSmoothScheme }

/-- **Adjunction for `F = F_{j₀}`.** There is a divisor `G ∼ K_Y + F` on `Y` of which `F` is not
a component, with `G|_F ≡ K_F` (`(K_Y + F)|_F ∼ K_F`,
`MMP.Intersection.nonempty_pullback_lineBundle_iso_of_smooth_divisor`). -/
private theorem exists_numericallyEquivalent_canonical_add_restrictPrimeDivisor
    (hT : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    [IsLocallyNoetherian (F j₀).idealSheaf.subscheme] [IsNormal (F j₀).idealSheaf.subscheme]
    {KF : Divisor (F j₀).idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) (n - 1)) :
    ∃ G : QDivisor Y, G.coeff (F j₀) = 0 ∧
      G.NumericallyEquivalent k (f ≫ sX) (Divisor.toQDivisor KY + Finsupp.single (F j₀) 1) ∧
      QDivisor.NumericallyEquivalent k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
        (G.restrictPrimeDivisor (F j₀)) (Divisor.toQDivisor KF) := by
  classical
  -- `Y` is a smooth variety
  haveI hsV := isSmoothVariety_of_isStripTieBreaker hT
  haveI : IsIntegral Y := hsV.toIsVariety.toIsIntegral
  have hsmY : MMP.Mori.IsSmoothScheme (f ≫ sX) := hT.isLogResolution.isSmoothScheme
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨hcart, hloc, -, hiso, -, -⟩ :=
    MMP.Mori.Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  -- `F` is a smooth variety
  have hPmem : (F j₀) ∈ (∑ j, Finsupp.single (F j) (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg (fun h => hj (hT.injective h))]
    · simp
  have hsmF : IsSmoothScheme ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) :=
    hT.isSNC.1 (F j₀) hPmem
  haveI : IsIntegral (F j₀).idealSheaf.subscheme := (F j₀).integral
  haveI hsF : Smooth ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) :=
    (isSmoothScheme_iff _).mp hsmF
  haveI hvF : AlgebraicGeometry.IsVariety k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) :=
    { toIsVariety := hvF, toSmooth := hsF }
  haveI : IsProper f := hT.isLogResolution.isProper
  haveI : CompactSpace (F j₀).idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (F j₀).idealSheaf.subschemeι
  obtain ⟨hcartF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
  -- the dimension of `Y` is `m + 1`
  have hn : n ≠ 0 := by
    rintro rfl
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
      (F j₀).genericPoint
    rw [(F j₀).coheight_genericPoint, hKY.1] at h
    have hne : topologicalKrullDim (closure {(F j₀).genericPoint} : Set Y) ≠ ⊥ :=
      (Order.krullDim_ne_bot_iff
        (α := IrreducibleCloseds (closure {(F j₀).genericPoint} : Set Y))).mpr
        ⟨IrreducibleCloseds.closureSingleton ⟨(F j₀).genericPoint, subset_closure rfl⟩⟩
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hne
    rw [← hb] at h
    norm_cast at h
    simp at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hKF' : KF.IsCanonicalDivisor ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) m := by simpa using hKF
  haveI : SmoothOfRelativeDimension (m + 1) (f ≫ sX) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (f ≫ sX) (m + 1) hKY.1
  -- the Cartier divisor `τ` of `F`
  obtain ⟨τ, hτe, hτs, hτW⟩ :=
    PrimeDivisor.exists_isEffective_isSubschemeOfEffective_of_isSmoothVariety k (f ≫ sX) (F j₀)
  obtain ⟨⟨eAdj⟩, -⟩ :=
    MMP.Intersection.nonempty_pullback_lineBundle_iso_of_smooth_divisor (f ≫ sX) (n := m)
      (F j₀).idealSheaf τ hτe hτs
  -- the moving lemma
  obtain ⟨t, ht⟩ := MMP.Flips.exists_primeDivisor_ord_eq (F j₀) (-(KY.coeff (F j₀) + 1))
  set G₀ : Divisor Y := KY + Finsupp.single (F j₀) 1 + MMP.Mori.principalDivisor t with hG₀
  have hG₀P : G₀.coeff (F j₀) = 0 := by
    rw [hG₀, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      MMP.Mori.coeff_principalDivisor, ht, DivisorWithCoeffs.coeff_apply (Finsupp.single (F j₀) 1),
      Finsupp.single_eq_same]
    ring
  have hlin : G₀.LinearlyEquivalent (KY + Finsupp.single (F j₀) 1) := ⟨t, by rw [hG₀]; abel⟩
  have hres := isPullback_restrictPrimeDivisor_of_hasPrincipalLocalEquations hloc hcart G₀ hG₀P
  -- `𝒪_F(G|_F) ≅ Ω^m_F ≅ 𝒪_F(K_F)`
  obtain ⟨eKY⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsmY hKY
  obtain ⟨eKF⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsmF hKF'
  have eτ : Nonempty (Divisor.divisorialSheaf (Finsupp.single (F j₀) 1 : Divisor Y) ≅
      MMP.CartierDivisor.sheaf τ) := by
    rw [← hτW ⟨⟩]
    exact hiso τ
  obtain ⟨eτ⟩ := eτ
  have eY : G₀.divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms (f ≫ sX) ((m : ℤ) + 1) ⊗
        MMP.CartierDivisor.sheaf τ :=
    hlin.divisorialSheafIso ≪≫
      ((hcart KY).divisorialSheafTensorIso (hcart (Finsupp.single (F j₀) 1))).symm ≪≫
      whiskerRightIso (eKY ≪≫ eqToIso (by push_cast; rfl)) _ ≪≫ whiskerLeftIso _ eτ
  have α : Divisor.divisorialSheaf (DivisorWithCoeffs.restrictPrimeDivisor G₀ (F j₀)) ≅
      KF.divisorialSheaf :=
    hres.divisorialSheafIso (hBc := hcart G₀) ≪≫
      (Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).mapIso eY ≪≫
      eAdj ≪≫ eKF.symm
  have hlinF := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso α
  refine ⟨Divisor.toQDivisor G₀, ?_, ?_, ?_⟩
  · rw [Divisor.coeff_toQDivisor, hG₀P, Int.cast_zero]
  · have h := numericallyEquivalent_toQDivisor_of_linearlyEquivalent (k := k) (sX := f ≫ sX)
      hlin (hcart _) (hcart _)
    have e : Divisor.toQDivisor (KY + Finsupp.single (F j₀) 1) =
        Divisor.toQDivisor KY + Finsupp.single (F j₀) 1 := by
      rw [map_add]
      congr 1
      ext Q
      rw [Divisor.coeff_toQDivisor]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rwa [e] at h
  · rw [G₀.restrictPrimeDivisor_toQDivisor (F j₀) hG₀P]
    exact numericallyEquivalent_toQDivisor_of_linearlyEquivalent hlinF (hcartF _) (hcartF _)

/-- **KM 3.4, Step 9.** For a tie-breaker `(j₀, c)` of a `(p, q)`-adapted resolution
`f : Y ⟶ X` of a rationality datum `(X, Δ, a, H)`, `F = F_{j₀}`, `(p', q') ∈ ℤ²`, the test
divisor `N = N(p', q')` (`MMP.Mori.IsStripTestDivisor`), a pull-back `B'` of
`p'H + q'a(K_X + Δ)` and a canonical divisor `K_F` of `F`:
`N|_F ≡ (B' + A')|_F - K_F`, where `A'` is the test boundary (`MMP.Mori.tieBreakerBoundary`).
Restrictions are taken of numerically equivalent representatives `N₁ ≡ N` and `M₁ ≡ B' + A'` of
which `F` is not a component. -/
@[mmp "lem_km3b_strip_restriction_adjunction"]
public theorem IsStripTieBreaker.numericallyEquivalent_restrictPrimeDivisor
    (hT : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c)
    {KY : Divisor Y} {p' q' : ℤ} {N : QDivisor Y}
    (hN : IsStripTestDivisor sX n K Δ a H f KY F aj pj rj j₀ c p' q' N)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
        (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).supp)
    {B' : QDivisor Y}
    (hB' : (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hB B')
    [IsLocallyNoetherian (F j₀).idealSheaf.subscheme] [IsNormal (F j₀).idealSheaf.subscheme]
    {KF : Divisor (F j₀).idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) (n - 1))
    {N₁ M₁ : QDivisor Y}
    (hN₁ : N₁.NumericallyEquivalent k (f ≫ sX) N) (hNF : N₁.coeff (F j₀) = 0)
    (hM₁ : M₁.NumericallyEquivalent k (f ≫ sX)
      (B' + tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j₀ c))
    (hMF : M₁.coeff (F j₀) = 0) :
    QDivisor.NumericallyEquivalent k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
      (N₁.restrictPrimeDivisor (F j₀))
      (M₁.restrictPrimeDivisor (F j₀) - Divisor.toQDivisor KF) := by
  obtain ⟨hKY, hB₂, B'', hB'', hNeq⟩ := hN
  -- the two pull-backs of `p'H + q'a(K_X + Δ)` agree
  have hBB : B'' = B' :=
    ((isQCartier_stripDivisor hT.toIsRationalityDatum p' q').existsUnique_isPullback hB).unique
      hB'' hB'
  subst hBB
  obtain ⟨G, hGF, hGY, hGKF⟩ :=
    exists_numericallyEquivalent_canonical_add_restrictPrimeDivisor hT hKY hKF
  -- `N₁ + G ≡ N + K_Y + F = B' + A' ≡ M₁` on `Y`
  have hY : (N₁ + G).NumericallyEquivalent k (f ≫ sX) M₁ := by
    refine (numericallyEquivalent_add hN₁ hGY).trans ?_
    convert hM₁.symm using 1
    rw [hNeq]
    abel
  have hNG : (N₁ + G).coeff (F j₀) = 0 := by
    rw [DivisorWithCoeffs.coeff_add, hNF, hGF, add_zero]
  haveI := isSmoothVariety_of_isStripTieBreaker hT
  obtain ⟨hcart, hloc, -⟩ := MMP.Mori.Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  have hF := numericallyEquivalent_restrictPrimeDivisor_of_isPullback
    (fun E _ hEF => isPullback_restrictPrimeDivisor_of_hasPrincipalLocalEquations hloc hcart E hEF)
    hNG hMF hY
  rw [DivisorWithCoeffs.restrictPrimeDivisor_add _ _ _ hNF hGF] at hF
  simpa [sub_eq_add_neg] using numericallyEquivalent_add hF (numericallyEquivalent_neg hGKF)

end Strip

end MMP.Mori

end
