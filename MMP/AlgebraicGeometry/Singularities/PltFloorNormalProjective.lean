module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
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
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
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
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.GeneralMember
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
import MMP.AlgebraicGeometry.Singularities.AdjointIdeal.ReducedSncBoundary
import MMP.AlgebraicGeometry.MMP.Models
import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesLocallyFree

/-!
# A prime plt floor on a projective `ℚ`-factorial variety is normal

Let `X` be a normal `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `S` a prime divisor and `B ≥ 0` a `ℚ`-divisor with `⌊B⌋ = 0` and no
component `S`, such that `(X, S + B)` is plt. Then `S` is normal.

Take a log resolution `p : W ⟶ X` of `(X, S + B)` and the strict transform `T` of `S`; `p` is an
isomorphism near the generic point of `S`, and `T` is a smooth component of the snc divisor
`Ex(p) ∪ p⁻¹(S + B)`. Write `K_W + Δ_W = p^*(K_X + S + B)` with `K_W = div(p^*ω)` for
`K_X = div(ω)`. The plt condition gives `coeff_P Δ_W < 1` for every prime `P ≠ T`, while
`coeff_T Δ_W = 1`, so `E = -⌊Δ_W - T⌋` is effective, `p`-exceptional and has no component `T`,
and `Θ₀ = Δ_W - T + E` has coefficients in `[0, 1)`. Since
`(E - T) - (K_W + Θ₀) = -p^*(K_X + S + B)`, relative Kawamata–Viehweg vanishing, after perturbing
`Θ₀` by a small multiple of an effective exceptional `F` with `-F` relatively ample
(`ℚ`-factoriality), gives `R¹p_* 𝒪_W(E - T) = 0`.

The restriction sequence `0 ⟶ 𝒪_W(E - T) ⟶ 𝒪_W(E) ⟶ ι_*𝒪_T(E|_T) ⟶ 0` then stays exact after
`p_*`, so every section of `μ_{T*}𝒪_T(E|_T)` over `S ∩ U` is locally the restriction of a section
of `p_* 𝒪_W(E)`, which is a regular function on `X` by normal Hartogs, `E` being exceptional.
Finally an element `y ∈ K(S)` integral over `𝒪_{S,x}` is, after multiplication by a unit, integral
over the sections on an open neighbourhood; it is then regular along every prime divisor of the
normal `T` over that neighbourhood, hence a section of `μ_{T*}𝒪_T(E|_T)`, hence the restriction of
a function regular at `x`. So `𝒪_{S,x}` is integrally closed.

## Main results

* `MMP.Mori.IsPltPair.isNormal_subscheme_of_isQFactorial_of_charZero`: the prime divisor `S` of a
  plt pair `(X, S + B)` on a projective `ℚ`-factorial variety over an algebraically closed field
  of characteristic zero is normal.
* `MMP.Mori.IsPltPair.isNormal_subscheme_of_isQFactorial`: the case `k = ℂ`.

## Implementation notes

The argument is usually concluded through `p_* 𝒪_T = 𝒪_S` and the normalization of `S`. Here the
lifting property of the restriction sequence is applied to the sections of `μ_{T*}𝒪_T(E|_T)` that
an integral element produces, which is the same mathematics without constructing the normalization.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Section 5.4
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.Fourfold

section FunctionFieldSections

variable {X : Scheme.{0}} [IsIntegral X]

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents' {Y : Scheme.{0}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

/-- The rational function of a section of `𝒦_Y` over `W`, read at a component meeting `W`. -/
private noncomputable def evFF {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom (φ Z)

private theorem index_eq {Y : Scheme.{0}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents' _).trans
    (eq_univ_of_irreducibleComponents' _).symm))

private theorem stalkSpecializes_genericPoint_injective {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes
      ((genericPoint_spec Y).specializes trivial :
        genericPoint Y ⤳ componentGenericPoint Y Z)).hom := by
  intro a b h
  have hsp : componentGenericPoint Y Z ⤳ genericPoint Y :=
    (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes
  have := congrArg (Y.presheaf.stalkSpecializes hsp).hom h
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_refl] at this
  exact this

/-- The section of `𝒦_Y` over `W` with a given rational function. -/
private noncomputable def ofFF {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens)
    (g : Y.functionField) : ToType ((rationalFunctionsPresheaf Y).obj (op W)) :=
  fun Z => (Y.presheaf.stalkSpecializes
    (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z.1)).specializes).hom g

private theorem evFF_ofFF {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (g : Y.functionField)
    (Z) : evFF (ofFF W g) Z = g := by
  rw [evFF, ofFF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private theorem ofFF_evFF {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    ofFF W (evFF φ Z) = φ := by
  funext Z'
  obtain rfl := index_eq Z Z'
  apply stalkSpecializes_genericPoint_injective Z.1
  change evFF (ofFF W (evFF φ Z)) Z = evFF φ Z
  rw [evFF_ofFF]

/-- `OrdGE` in terms of the divisorial valuation of the rational function. -/
private theorem ordGE_iff_divisorialValuation_le {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔ E.divisorialValuation
      ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom s) ≤
        WithZero.exp (-n) := by
  have hv : E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom s))⁻¹ := by
    rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
    rfl
  rw [MMP.Mori.PrimeDivisor.OrdGE, hv]
  set x := (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom s
  have h0 : s = 0 ↔ x = 0 :=
    ⟨fun h => by simp [x, h], fun h => (injective_iff_map_eq_zero' _).1
      (stalkSpecializes_genericPoint_injective E.component) s |>.1 h⟩
  rw [h0]
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · have hvx : E.divisorialValuation x ≠ 0 := (map_ne_zero _).2 hx
    simp only [hx, false_or]
    rw [← WithZero.exp_log hvx, ← WithZero.exp_neg, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

/-- A section of `𝒦_Y` over `μ⁻¹U` is a section of `𝒪_Y(G)` exactly when its rational function
lies in `μ_*𝒪_Y(G)(U)`. -/
private theorem mem_divisorialSubmodule_iff_mem_multiplierIdealSections {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (μ : Y ⟶ X) [IsDominant μ]
    (G : Divisor Y) (U : X.Opens) (σ : ToType ((rationalFunctionsPresheaf Y).obj (op (μ ⁻¹ᵁ U))))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ μ ⁻¹ᵁ U})
    (g : X.functionField) (hg : functionFieldMap μ g = evFF σ Z) :
    σ ∈ G.divisorialSubmodule (μ ⁻¹ᵁ U) ↔
      g ∈ MMP.Intersection.multiplierIdealSections μ G U := by
  have hne : μ ⁻¹ᵁ U ≠ ⊥ := by
    intro h
    obtain ⟨Z₁, hZ₁⟩ := Z
    rw [h] at hZ₁
    exact hZ₁
  rw [Divisor.mem_divisorialSubmodule]
  constructor
  · intro h
    refine ⟨fun h' => absurd h' hne, fun P hP => ?_⟩
    have := (ordGE_iff_divisorialValuation_le P _ _).1 (h P hP)
    rw [neg_neg] at this
    rw [PrimeDivisor.valuationOver_apply, hg]
    obtain rfl : (⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩ :
      {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ μ ⁻¹ᵁ U}) = Z := index_eq _ _
    exact this
  · rintro ⟨-, h⟩ P hP
    rw [ordGE_iff_divisorialValuation_le, neg_neg]
    have := h P hP
    rw [PrimeDivisor.valuationOver_apply, hg] at this
    obtain rfl : (⟨P.component, P.componentGenericPoint_mem_of_nonempty hP⟩ :
      {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ μ ⁻¹ᵁ U}) = Z := index_eq _ _
    exact this

/-- The index of the unique component of an integral scheme, in an open containing the generic
point. -/
private noncomputable def topIndex (Y : Scheme.{0}) [IsIntegral Y] {W : Y.Opens}
    (h : genericPoint Y ∈ W) : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
  ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, by
    rw [componentGenericPoint_eq_genericPoint]; exact h⟩

private theorem genericPoint_mem_of_index {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    genericPoint Y ∈ W := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

/-- The rational function of `r • σ`. -/
private theorem evFF_smul {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens} (r : Γ(Y, W))
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF (r • φ) Z = Y.presheaf.germ W (genericPoint Y) (genericPoint_mem_of_index Z) r *
      evFF φ Z := by
  rw [evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

private theorem evFF_add {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (φ ψ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF (φ + ψ) Z = evFF φ Z + evFF ψ Z :=
  map_add _ _ _

private theorem evFF_map {Y : Scheme.{0}} [IsIntegral Y] {W W' : Y.Opensᵒᵖ} (j : W ⟶ W')
    (φ : ToType ((rationalFunctionsPresheaf Y).obj W))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W'.unop}) :
    evFF (W := W'.unop) ((rationalFunctionsPresheaf Y).map j φ) Z =
      evFF (W := W.unop) φ ⟨Z.1, j.unop.le Z.2⟩ := rfl

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

private theorem eq_of_evFF_eq {W : Y.Opens}
    {φ ψ : ToType ((rationalFunctionsPresheaf Y).obj (op W))}
    (h : ∀ Z, evFF φ Z = evFF ψ Z) : φ = ψ := by
  funext Z
  rw [← ofFF_evFF φ Z, ← ofFF_evFF ψ Z, h Z]

private theorem genericPoint_mem_preimage (μ : Y ⟶ X) [IsDominant μ] {U : X.Opens}
    (h : genericPoint X ∈ U) : genericPoint Y ∈ μ ⁻¹ᵁ U := by
  change μ (genericPoint Y) ∈ U
  rwa [map_genericPoint_of_isDominant]

end FunctionFieldSections

section StrictTransform

variable {X Y : Scheme.{0}}

/-- A point of an open `V` over which `μ` is an isomorphism is the image of a point of the same
coheight. -/
private theorem exists_map_eq_coheight_eq (μ : Y ⟶ X) {V : X.Opens} (hV : IsIso (μ ∣_ V))
    {x : X} (hx : x ∈ V) : ∃ y : Y, μ y = x ∧ Order.coheight y = Order.coheight x := by
  let y : (μ ⁻¹ᵁ V).toScheme := (inv (μ ∣_ V)) ⟨x, hx⟩
  have hy : μ y.1 = x := by
    have h1 : (μ ∣_ V) y = ⟨x, hx⟩ := by
      change ((inv (μ ∣_ V)) ≫ (μ ∣_ V)) ⟨x, hx⟩ = _
      rw [IsIso.inv_hom_id]; rfl
    have h2 := congrArg Subtype.val h1
    rwa [morphismRestrict_base_coe] at h2
  refine ⟨y.1, hy, ?_⟩
  have hb : μ y.1 ∈ biregularLocus μ := le_biregularLocus hV (by rw [hy]; exact hx)
  rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus μ hb, hy]

/-- **The strict transform.** A prime divisor `S` of `X` whose generic point lies in an open
over which `μ` is an isomorphism has a strict transform: a prime divisor `T` of `Y` with
`μ(η_T) = η_S`, with ideal sheaf the vanishing ideal of the closure of `η_T`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (μ : Y ⟶ X) {V : X.Opens}
    (hV : IsIso (μ ∣_ V)) (S : MMP.Mori.PrimeDivisor X) (hS : S.genericPoint ∈ V) :
    ∃ T : MMP.Mori.PrimeDivisor Y, μ T.genericPoint = S.genericPoint ∧
      T.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({T.genericPoint} : Set Y)) := by
  obtain ⟨y, hy, hcoh⟩ := exists_map_eq_coheight_eq μ hV hS
  rw [S.coheight_genericPoint] at hcoh
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hcoh, ?_, ?_⟩
  · change μ (AlgebraicGeometry.PrimeDivisor.genericPoint _) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact hy
  · change _ = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {AlgebraicGeometry.PrimeDivisor.genericPoint _})
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; rfl

/-- `μ` maps the strict transform `T` of `S` into `S`. -/
private theorem le_map_idealSheaf (μ : Y ⟶ X) (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) (hT : μ T.genericPoint = S.genericPoint)
    (hTI : T.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({T.genericPoint} : Set Y))) :
    S.idealSheaf ≤ T.idealSheaf.map μ := by
  rw [hTI, Scheme.IdealSheafData.map_vanishingIdeal,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  have hsp : T.genericPoint ⤳ y := specializes_iff_mem_closure.2 hy
  have := hsp.map μ.continuous
  rw [hT] at this
  change μ y ∈ (S.support : Set X)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact specializes_iff_mem_closure.1 this

/-- The restriction `μ_T : T ⟶ S` of `μ` to a strict transform maps the generic point to the
generic point. -/
private theorem map_genericPoint_strictTransform (μ : Y ⟶ X) (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) (hT : μ T.genericPoint = S.genericPoint)
    (μT : T.idealSheaf.subscheme ⟶ S.idealSheaf.subscheme)
    (hμT : μT ≫ S.idealSheaf.subschemeι = T.idealSheaf.subschemeι ≫ μ) :
    haveI := S.integral; haveI := T.integral
    μT (genericPoint T.idealSheaf.subscheme) = genericPoint S.idealSheaf.subscheme := by
  haveI := S.integral; haveI := T.integral
  apply S.idealSheaf.subschemeι.isClosedEmbedding.injective
  change (μT ≫ S.idealSheaf.subschemeι) _ = S.genericPoint
  rw [hμT]
  exact hT

/-- The restriction `μ_T : T ⟶ S` of a proper `μ` to a strict transform is proper and
surjective. -/
private theorem isProper_surjective_strictTransform (μ : Y ⟶ X) [IsProper μ]
    (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) (hT : μ T.genericPoint = S.genericPoint)
    (μT : T.idealSheaf.subscheme ⟶ S.idealSheaf.subscheme)
    (hμT : μT ≫ S.idealSheaf.subschemeι = T.idealSheaf.subschemeι ≫ μ) :
    IsProper μT ∧ Surjective μT := by
  haveI := S.integral; haveI := T.integral
  have hp : IsProper μT := by
    have : IsProper (μT ≫ S.idealSheaf.subschemeι) := by rw [hμT]; infer_instance
    exact IsProper.of_comp μT S.idealSheaf.subschemeι
  refine ⟨hp, ?_⟩
  have hd : IsDominant μT := by
    refine ⟨?_⟩
    have hg := map_genericPoint_strictTransform μ S T hT μT hμT
    refine Dense.mono (Set.singleton_subset_iff.2 ⟨_, hg⟩) ?_
    exact dense_iff_closure_eq.2 (genericPoint_spec S.idealSheaf.subscheme)
  exact surjective_of_isDominant_of_isClosed_range μT μT.isClosedMap.isClosed_range

end StrictTransform

private theorem divisorialValuation_le_one_of_strictTransform {X Y₀ : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (μ₀ : Y₀ ⟶ X) [IsIntegral Y₀]
    [IsLocallyNoetherian Y₀] [IsNormal Y₀] [IsDominant μ₀] (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y₀) (hT : μ₀ T.genericPoint = S.genericPoint) {V : X.Opens}
    (hV : IsIso (μ₀ ∣_ V)) (hSV : S.genericPoint ∈ V) {g : X.functionField}
    (hg : T.divisorialValuation (functionFieldMap μ₀ g) ≤ 1) : S.divisorialValuation g ≤ 1 := by
  haveI := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus μ₀
    (MMP.Mori.le_biregularLocus hV (by rw [hT]; exact hSV))
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  rwa [T.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hg0),
    MMP.Positivity.ord_functionFieldMap_of_isIso μ₀ T S hT g,
    ← S.divisorialValuation_eq_exp_neg_ord hg0] at hg

/-- **Restricting a regular function commutes with the strict transform.** For a section `s` of
`𝒪_X` near `η_S`, pulling its restriction to `S` back along `μ_T` gives the restriction to `T` of
its pull-back along `μ₀`. -/
private theorem functionFieldMap_stalkMap_germ_strictTransform {X Y₀ : Scheme.{0}}
    (μ₀ : Y₀ ⟶ X) (S : MMP.Mori.PrimeDivisor X) (T : MMP.Mori.PrimeDivisor Y₀)
    [IsIntegral S.idealSheaf.subscheme] [IsIntegral T.idealSheaf.subscheme]
    (μT : T.idealSheaf.subscheme ⟶ S.idealSheaf.subscheme) [IsDominant μT]
    (hμT : μT ≫ S.idealSheaf.subschemeι = T.idealSheaf.subschemeι ≫ μ₀)
    (hT : μ₀ T.genericPoint = S.genericPoint) {W : X.Opens} (hηW : S.genericPoint ∈ W)
    (hTW : T.genericPoint ∈ μ₀ ⁻¹ᵁ W) (s : Γ(X, W)) :
    functionFieldMap μT (S.idealSheaf.subschemeι.stalkMap (genericPoint _)
      (X.presheaf.germ W S.genericPoint hηW s)) =
      (T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom
        (Y₀.presheaf.germ (μ₀ ⁻¹ᵁ W) T.genericPoint hTW (μ₀.app W s)) := by
  have hgW : genericPoint S.idealSheaf.subscheme ∈ S.idealSheaf.subschemeι ⁻¹ᵁ W := hηW
  have hZ : genericPoint T.idealSheaf.subscheme ∈ μT ⁻¹ᵁ (S.idealSheaf.subschemeι ⁻¹ᵁ W) := by
    change S.idealSheaf.subschemeι (μT (genericPoint _)) ∈ W
    rw [map_genericPoint_strictTransform μ₀ S T hT μT hμT]
    exact hηW
  change (functionFieldMap μT) ((S.idealSheaf.subschemeι.stalkMap _).hom
    (X.presheaf.germ W (S.idealSheaf.subschemeι (genericPoint _)) hgW s)) = _
  rw [Scheme.Hom.germ_stalkMap_apply S.idealSheaf.subschemeι W _ hgW s,
    functionFieldMap_germ μT (S.idealSheaf.subschemeι ⁻¹ᵁ W) hgW hZ]
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply T.idealSheaf.subschemeι (μ₀ ⁻¹ᵁ W)
    (genericPoint T.idealSheaf.subscheme) hTW (μ₀.app W s)).symm
  have key : ∀ (φ : T.idealSheaf.subscheme ⟶ X) (hφ : φ = T.idealSheaf.subschemeι ≫ μ₀)
      (h₁ : genericPoint T.idealSheaf.subscheme ∈ φ ⁻¹ᵁ W),
      T.idealSheaf.subscheme.presheaf.germ (φ ⁻¹ᵁ W) _ h₁ (φ.app W s) =
        T.idealSheaf.subscheme.presheaf.germ ((T.idealSheaf.subschemeι ≫ μ₀) ⁻¹ᵁ W) _
          (hφ ▸ h₁) ((T.idealSheaf.subschemeι ≫ μ₀).app W s) := by
    rintro φ rfl h₁; rfl
  exact key (μT ≫ S.idealSheaf.subschemeι) hμT hZ

/-! ### Auxiliary facts on restrictions and orders -/

section Auxiliary

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A rational function of positive order along `S` restricts to zero on `S`. -/
private theorem isRestrictionAlong_zero_of_lt_one (S : MMP.Mori.PrimeDivisor X)
    {g : X.functionField} (hg : S.divisorialValuation g < 1) :
    haveI := S.integral
    IsRestrictionAlong S g 0 := by
  have := S.integral
  obtain ⟨r, rfl⟩ := (S.divisorialValuation_le_one_iff g).1 hg.le
  have hr := (S.divisorialValuation_algebraMap_lt_one_iff r).1 hg
  refine ⟨r, rfl, ?_⟩
  set φ := S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme)
  have hl : IsLocalHom φ.hom := inferInstance
  have hnu : ¬ IsUnit (φ.hom r) := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hr (hl.map_nonunit r hu)
  by_contra h
  exact hnu (isUnit_iff_ne_zero.mpr h)

/-- A rational function restricting to zero on `S` has positive order along `S`. -/
private theorem lt_one_of_isRestrictionAlong_zero (S : MMP.Mori.PrimeDivisor X)
    {g : X.functionField} (hg : haveI := S.integral; IsRestrictionAlong S g 0) :
    S.divisorialValuation g < 1 := by
  have := S.integral
  obtain ⟨a, rfl, ha⟩ := hg
  set φ := S.idealSheaf.subschemeι.stalkMap (genericPoint S.idealSheaf.subscheme)
  have h1 : ¬ IsUnit a := fun hu => by
    have := hu.map φ.hom
    rw [ha] at this
    exact not_isUnit_zero this
  exact (S.divisorialValuation_algebraMap_lt_one_iff (a : S.localRing)).2
    ((IsLocalRing.mem_maximalIdeal _).2 h1)

/-- **Orders along a smooth prime divisor.** Let `P` be a smooth prime divisor of a smooth scheme
`X` over `k`, `G` a divisor of which `P` is not a component, `a` a unit of `𝒪_{X,η_P}` with image
`g ∈ K(X)`, and `Q` a prime divisor of `P`. Then `ord_Q(a|_P)` and `coeff_Q(G|_P)` are the sums
`∑ i(E, Q) ord_E g` and `∑ i(E, Q) coeff_E G` over one finite set of prime divisors `E` of `X`
passing through `η_Q`, with `i(E, Q)` the intersection length. -/
private theorem exists_ord_restrict_coeff_restrict_eq_sum {k : Type} [Field k]
    (sX : X ⟶ Spec (.of k)) [CompactSpace X]
    [Smooth sX] (P : MMP.Mori.PrimeDivisor X) [IsIntegral P.idealSheaf.subscheme]
    [IsLocallyNoetherian P.idealSheaf.subscheme]
    [IsNormal P.idealSheaf.subscheme] [Smooth (P.idealSheaf.subschemeι ≫ sX)]
    (G : Divisor X) (hGP : G.coeff P = 0)
    (a : X.presheaf.stalk (P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme)))
    (ha : IsUnit a) (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor X),
      (∀ E ∈ s, P.idealSheaf.subschemeι Q.genericPoint ∈ E.support) ∧
      P.idealSheaf.subscheme.ord ((P.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a)
          Q.genericPoint = ∑ E ∈ s, (E.intersectionLength P.idealSheaf.subschemeι Q : ℤ) *
            X.ord (algebraMap _ X.functionField a) E.genericPoint ∧
      (G.restrictPrimeDivisor P).coeff Q =
        ∑ E ∈ s, (E.intersectionLength P.idealSheaf.subschemeι Q : ℤ) * G.coeff E := by
  haveI : IsNoetherian X := ⟨⟩
  classical
  set g := algebraMap _ X.functionField a with hgdef
  have hg0 : g ≠ 0 := (ha.map (algebraMap (X.presheaf.stalk _) X.functionField)).ne_zero
  set s := G.support ∪ (principalDivisor (Units.map
    (rationalFunctionsEquivFunctionField X).symm.toMonoidHom (Units.mk0 g hg0))).support
  have hss : ∀ E : MMP.Mori.PrimeDivisor X, X.ord g E.genericPoint ≠ 0 → E ∈ s := fun E hE =>
    Finset.mem_union_right _ (by
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, coeff_principalDivisor_mk0]
      exact hE)
  have hfilter : ∀ f : MMP.Mori.PrimeDivisor X → ℤ,
      ∑ E ∈ s with P.idealSheaf.subschemeι Q.genericPoint ∈ E.support,
          (E.intersectionLength P.idealSheaf.subschemeι Q : ℤ) * f E =
        ∑ E ∈ s, (E.intersectionLength P.idealSheaf.subschemeι Q : ℤ) * f E :=
    fun f => Finset.sum_filter_of_ne fun E _ hE => by
      by_contra hmem
      rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E hmem] at hE
      simp at hE
  refine ⟨s.filter (P.idealSheaf.subschemeι Q.genericPoint ∈ ·.support),
    fun E hE => (Finset.mem_filter.1 hE).2, ?_, ?_⟩
  · rw [hfilter, MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord sX
      P.idealSheaf.subschemeι a ha Q s hss]
  · rw [hfilter, DivisorWithCoeffs.coeff_restrictPrimeDivisor G P hGP Q, Finsupp.sum]
    refine (Finset.sum_subset Finset.subset_union_left fun E _ hE => ?_).trans
      (Finset.sum_congr rfl fun E _ => by rw [nsmul_eq_mul, DivisorWithCoeffs.coeff_apply])
    rw [Finsupp.notMem_support_iff.mp hE, smul_zero]

/-- **Restricting a section to a smooth prime divisor.** Let `P` be a smooth prime divisor of a
smooth scheme `X` over `k`, `G` a divisor of which `P` is not a component, and `a` a unit of
`𝒪_{X,η_P}` whose image `g ∈ K(X)` satisfies `v_E(g) ≤ exp(coeff_E G)` along every prime divisor
`E` meeting an open `W`. Then `a|_P` satisfies the same bound for `G|_P` along every prime divisor
of `P` meeting `W`. -/
private theorem divisorialValuation_restrict_le {k : Type} [Field k]
    (sX : X ⟶ Spec (.of k)) [CompactSpace X]
    [Smooth sX] (P : MMP.Mori.PrimeDivisor X) [IsIntegral P.idealSheaf.subscheme]
    [IsLocallyNoetherian P.idealSheaf.subscheme]
    [IsNormal P.idealSheaf.subscheme] [Smooth (P.idealSheaf.subschemeι ≫ sX)]
    (G : Divisor X) (hGP : G.coeff P = 0) (W : X.Opens)
    (a : X.presheaf.stalk (P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme)))
    (ha : IsUnit a)
    (hg : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W).Nonempty →
      E.divisorialValuation (algebraMap _ X.functionField a) ≤ WithZero.exp (G.coeff E))
    (Q : MMP.Mori.PrimeDivisor P.idealSheaf.subscheme)
    (hQ : (Q.support ∩ (P.idealSheaf.subschemeι ⁻¹ᵁ W)).Nonempty) :
    Q.divisorialValuation ((P.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a :
      P.idealSheaf.subscheme.functionField) ≤
      WithZero.exp ((G.restrictPrimeDivisor P).coeff Q) := by
  have hg0 : algebraMap _ X.functionField a ≠ 0 :=
    (ha.map (algebraMap (X.presheaf.stalk _) X.functionField)).ne_zero
  have hQW : Q.genericPoint ∈ P.idealSheaf.subschemeι ⁻¹ᵁ W := (Q.genericPoint_mem_iff _).mpr hQ
  obtain ⟨s, hs, hord, hcoeff⟩ := exists_ord_restrict_coeff_restrict_eq_sum sX P G hGP a ha Q
  rw [Q.divisorialValuation_eq_exp_neg_ord
      (ha.map (P.idealSheaf.subschemeι.stalkMap _).hom).ne_zero,
    WithZero.exp_le_exp, hord, hcoeff, neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun E hE => ?_
  have h1 := hg E ⟨_, hs E hE, hQW⟩
  rw [E.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h1
  rw [← mul_add]
  exact mul_nonneg (by positivity) (by omega)

end Auxiliary

/-! ### The restriction sequence of a smooth prime divisor -/

section RestrictionSequence

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  (T : MMP.Mori.PrimeDivisor Y) [IsIntegral T.idealSheaf.subscheme]

/-- The restriction to `T` of a rational function is unique when it exists. -/
private theorem isRestrictionAlong_unique {g : Y.functionField}
    {h h' : T.idealSheaf.subscheme.functionField}
    (hh : IsRestrictionAlong T g h) (hh' : IsRestrictionAlong T g h') : h = h' := by
  obtain ⟨a, ha, rfl⟩ := hh
  obtain ⟨a', ha', rfl⟩ := hh'
  have hinj : Function.Injective (algebraMap T.localRing Y.functionField) :=
    IsFractionRing.injective T.localRing Y.functionField
  have : a = a' := hinj (ha.trans ha'.symm)
  rw [this]

/-- A rational function regular along `T` has a restriction to `T`. -/
private theorem exists_isRestrictionAlong_of_le_one {g : Y.functionField}
    (hg : T.divisorialValuation g ≤ 1) :
    ∃ h, IsRestrictionAlong T g h := by
  obtain ⟨r, rfl⟩ := (T.divisorialValuation_le_one_iff g).1 hg
  exact ⟨_, r, rfl, rfl⟩

private theorem le_one_of_isRestrictionAlong {g : Y.functionField}
    {h : T.idealSheaf.subscheme.functionField}
    (hh : IsRestrictionAlong T g h) : T.divisorialValuation g ≤ 1 := by
  obtain ⟨a, rfl, -⟩ := hh
  exact (T.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩

private theorem IsRestrictionAlong.add' {g₁ g₂ : Y.functionField}
    {h₁ h₂ : T.idealSheaf.subscheme.functionField}
    (hh₁ : IsRestrictionAlong T g₁ h₁) (hh₂ : IsRestrictionAlong T g₂ h₂) :
    IsRestrictionAlong T (g₁ + g₂) (h₁ + h₂) := by
  obtain ⟨a₁, rfl, rfl⟩ := hh₁
  obtain ⟨a₂, rfl, rfl⟩ := hh₂
  exact ⟨a₁ + a₂, map_add _ _ _, map_add _ _ _⟩

private theorem IsRestrictionAlong.mul' {g₁ g₂ : Y.functionField}
    {h₁ h₂ : T.idealSheaf.subscheme.functionField}
    (hh₁ : IsRestrictionAlong T g₁ h₁) (hh₂ : IsRestrictionAlong T g₂ h₂) :
    IsRestrictionAlong T (g₁ * g₂) (h₁ * h₂) := by
  obtain ⟨a₁, rfl, rfl⟩ := hh₁
  obtain ⟨a₂, rfl, rfl⟩ := hh₂
  exact ⟨a₁ * a₂, map_mul _ _ _, map_mul _ _ _⟩

/-- The restriction to `T` of a rational function regular along `T`, and `0` otherwise. -/
private noncomputable def restrictFF (g : Y.functionField) :
    T.idealSheaf.subscheme.functionField :=
  open Classical in
  if h : ∃ h, IsRestrictionAlong T g h then h.choose else 0

private theorem isRestrictionAlong_restrictFF {g : Y.functionField}
    (hg : T.divisorialValuation g ≤ 1) : IsRestrictionAlong T g (restrictFF T g) := by
  have h := exists_isRestrictionAlong_of_le_one T hg
  rw [restrictFF, dif_pos h]
  exact h.choose_spec

private theorem restrictFF_eq {g : Y.functionField}
    {h : T.idealSheaf.subscheme.functionField}
    (hh : IsRestrictionAlong T g h) : restrictFF T g = h :=
  isRestrictionAlong_unique T (isRestrictionAlong_restrictFF T (le_one_of_isRestrictionAlong T hh))
    hh

private theorem restrictFF_add {g₁ g₂ : Y.functionField} (h₁ : T.divisorialValuation g₁ ≤ 1)
    (h₂ : T.divisorialValuation g₂ ≤ 1) :
    restrictFF T (g₁ + g₂) = restrictFF T g₁ + restrictFF T g₂ :=
  restrictFF_eq T (IsRestrictionAlong.add' T (isRestrictionAlong_restrictFF T h₁)
    (isRestrictionAlong_restrictFF T h₂))

private theorem restrictFF_mul {g₁ g₂ : Y.functionField} (h₁ : T.divisorialValuation g₁ ≤ 1)
    (h₂ : T.divisorialValuation g₂ ≤ 1) :
    restrictFF T (g₁ * g₂) = restrictFF T g₁ * restrictFF T g₂ :=
  restrictFF_eq T (IsRestrictionAlong.mul' T (isRestrictionAlong_restrictFF T h₁)
    (isRestrictionAlong_restrictFF T h₂))

private theorem restrictFF_eq_zero_iff {g : Y.functionField} (hg : T.divisorialValuation g ≤ 1) :
    restrictFF T g = 0 ↔ T.divisorialValuation g < 1 := by
  refine ⟨fun h0 => ?_, fun h => restrictFF_eq T (isRestrictionAlong_zero_of_lt_one T h)⟩
  have := isRestrictionAlong_restrictFF T hg
  rw [h0] at this
  exact lt_one_of_isRestrictionAlong_zero T this

/-- Points of `T` lie on the support of `T`. -/
private theorem subschemeι_mem_support (z : T.idealSheaf.subscheme) :
    T.idealSheaf.subschemeι z ∈ T.support := by
  change _ ∈ (T.idealSheaf.support : Set Y)
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, rfl⟩

/-- A rational function of valuation one along `T` is a unit of the local ring. -/
private theorem exists_isUnit_of_divisorialValuation_eq_one {g : Y.functionField}
    (hg : T.divisorialValuation g = 1) :
    ∃ a : Y.presheaf.stalk (T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)),
      IsUnit a ∧ algebraMap _ Y.functionField a = g := by
  obtain ⟨a, ha⟩ := (T.divisorialValuation_le_one_iff _).1 hg.le
  refine ⟨a, ?_, ha⟩
  by_contra hna
  have := (T.divisorialValuation_algebraMap_lt_one_iff a).2
    ((IsLocalRing.mem_maximalIdeal _).2 hna)
  rw [ha, hg] at this
  exact lt_irrefl _ this

/-- The generic point of `T` lies in every open meeting it, and then so does that of `Y`. -/
private theorem genericPoint_mem_of_index_preimage {W : Y.Opens}
    (Z' : {Z : irreducibleComponents T.idealSheaf.subscheme //
      componentGenericPoint _ Z ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W}) : genericPoint Y ∈ W := by
  have h : genericPoint T.idealSheaf.subscheme ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W :=
    genericPoint_mem_of_index Z'
  exact ((genericPoint_spec Y).specializes
    (Set.mem_univ (T.idealSheaf.subschemeι (genericPoint _)))).mem_open W.isOpen h

private theorem support_inter_nonempty_of_index {W : Y.Opens}
    (Z' : {Z : irreducibleComponents T.idealSheaf.subscheme //
      componentGenericPoint _ Z ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W}) : (T.support ∩ W).Nonempty :=
  ⟨_, subschemeι_mem_support T _, genericPoint_mem_of_index Z'⟩

/-- The restriction to `T` of a section of `𝒦_Y` over `W`, a section of `𝒦_T` over `T ∩ W`. -/
private noncomputable def restrictSec {W : Y.Opens}
    (σ : ToType ((rationalFunctionsPresheaf Y).obj (op W))) :
    ToType ((rationalFunctionsPresheaf T.idealSheaf.subscheme).obj
      (op (T.idealSheaf.subschemeι ⁻¹ᵁ W))) :=
  fun Z' => ofFF _ (restrictFF T (evFF σ (topIndex Y (genericPoint_mem_of_index_preimage T Z')))) Z'

private theorem evFF_restrictSec {W : Y.Opens}
    (σ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z' : {Z : irreducibleComponents T.idealSheaf.subscheme //
      componentGenericPoint _ Z ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W})
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF (restrictSec T σ) Z' = restrictFF T (evFF σ Z) := by
  rw [show restrictSec T σ = ofFF _ (restrictFF T (evFF σ Z)) by
    funext Z''
    simp only [restrictSec]
    rw [index_eq (topIndex Y _) Z]]
  exact evFF_ofFF _ _ _

/-- The bound on a section of `𝒪_Y(L)` along a prime divisor meeting `W`. -/
private theorem divisorialValuation_evFF_le {L : Divisor Y} {W : Y.Opens}
    {σ : ToType ((rationalFunctionsPresheaf Y).obj (op W))} (hσ : σ ∈ L.divisorialSubmodule W)
    (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty)
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    E.divisorialValuation (evFF σ Z) ≤ WithZero.exp (L.coeff E) := by
  have := (ordGE_iff_divisorialValuation_le E _ _).1 (hσ E hE)
  rw [neg_neg] at this
  obtain rfl : (⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ :
    {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) = Z := index_eq _ _
  exact this

private theorem mem_divisorialSubmodule_of_divisorialValuation_evFF_le {L : Divisor Y}
    {W : Y.Opens} {σ : ToType ((rationalFunctionsPresheaf Y).obj (op W))}
    (h : ∀ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      E.divisorialValuation (evFF σ ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) ≤
        WithZero.exp (L.coeff E)) :
    σ ∈ L.divisorialSubmodule W := fun E hE => by
  rw [ordGE_iff_divisorialValuation_le, neg_neg]
  exact h E hE

/-- A section of `𝒪_Y(L)`, `coeff_T L = 0`, is regular along `T` when `W` meets `T`. -/
private theorem divisorialValuation_evFF_le_one {L : Divisor Y} (hL : L.coeff T = 0)
    {W : Y.Opens} {σ : ToType ((rationalFunctionsPresheaf Y).obj (op W))}
    (hσ : σ ∈ L.divisorialSubmodule W) (hT : (T.support ∩ W).Nonempty)
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    T.divisorialValuation (evFF σ Z) ≤ 1 := by
  have := divisorialValuation_evFF_le hσ T hT Z
  rwa [hL, WithZero.exp_zero] at this

/-- The restriction of a regular function on `W` is the restriction of its section. -/
private theorem isRestrictionAlong_germ {W : Y.Opens} (hW : genericPoint Y ∈ W)
    (hTW : genericPoint T.idealSheaf.subscheme ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W) (r : Γ(Y, W)) :
    IsRestrictionAlong T (Y.presheaf.germ W (genericPoint Y) hW r)
      (T.idealSheaf.subscheme.presheaf.germ _ (genericPoint _) hTW
        (T.idealSheaf.subschemeι.app W r)) :=
  ⟨Y.presheaf.germ W _ hTW r, TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _,
    Scheme.Hom.germ_stalkMap_apply _ _ _ _ _⟩

variable {k : Type} [Field k] (sY : Y ⟶ Spec (.of k)) [CompactSpace Y] [Smooth sY]
  [IsLocallyNoetherian T.idealSheaf.subscheme] [IsNormal T.idealSheaf.subscheme]
  [Smooth (T.idealSheaf.subschemeι ≫ sY)]

include sY in
/-- The restriction of a section of `𝒪_Y(L)` is a section of `𝒪_T(L|_T)`. -/
private theorem restrictSec_mem {L : Divisor Y} (hL : L.coeff T = 0) {W : Y.Opens}
    {σ : ToType ((rationalFunctionsPresheaf Y).obj (op W))} (hσ : σ ∈ L.divisorialSubmodule W) :
    restrictSec T σ ∈ Divisor.divisorialSubmodule (L.restrictPrimeDivisor T)
      (T.idealSheaf.subschemeι ⁻¹ᵁ W) := by
  refine mem_divisorialSubmodule_of_divisorialValuation_evFF_le fun Q hQ => ?_
  set Z' : {Z : irreducibleComponents T.idealSheaf.subscheme //
      componentGenericPoint _ Z ∈ T.idealSheaf.subschemeι ⁻¹ᵁ W} :=
    ⟨Q.component, Q.componentGenericPoint_mem_of_nonempty hQ⟩
  have hYW := genericPoint_mem_of_index_preimage T Z'
  set Z := topIndex Y hYW
  rw [evFF_restrictSec T σ Z' Z]
  have hTW := support_inter_nonempty_of_index T Z'
  have h1 := divisorialValuation_evFF_le_one T hL hσ hTW Z
  rcases h1.lt_or_eq with hlt | heq
  · rw [(restrictFF_eq_zero_iff T h1).2 hlt, map_zero]
    exact zero_le'
  · obtain ⟨a, hau, ha⟩ := exists_isUnit_of_divisorialValuation_eq_one T heq
    have hres : IsRestrictionAlong T (evFF σ Z)
        ((T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a) := ⟨a, ha, rfl⟩
    rw [restrictFF_eq T hres]
    refine divisorialValuation_restrict_le sY T L hL W a hau (fun E hE => ?_) Q hQ
    have := divisorialValuation_evFF_le hσ E hE Z
    rwa [← ha] at this

include sY in
/-- The components of the restriction morphism `𝒪_Y(L) ⟶ ι_*𝒪_T(L|_T)`. -/
private noncomputable def restrictionHomApp {L : Divisor Y} (hL : L.coeff T = 0)
    (U : Y.Opensᵒᵖ) :
    L.divisorialSheaf.val.obj U ⟶
      ((Scheme.Modules.pushforward T.idealSheaf.subschemeι).obj
        (Divisor.divisorialSheaf (L.restrictPrimeDivisor T))).val.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun σ => ⟨restrictSec T (σ : L.divisorialSubmodule U.unop).1,
        restrictSec_mem T sY hL (σ : L.divisorialSubmodule U.unop).2⟩
      map_add' := fun a b => Subtype.ext (eq_of_evFF_eq fun Z' => by
        let Z := topIndex Y (genericPoint_mem_of_index_preimage T Z')
        have hTW := support_inter_nonempty_of_index T Z'
        change evFF (restrictSec T ((a : L.divisorialSubmodule U.unop).1 +
            (b : L.divisorialSubmodule U.unop).1)) Z' =
          evFF (restrictSec T (a : L.divisorialSubmodule U.unop).1 +
            restrictSec T (b : L.divisorialSubmodule U.unop).1) Z'
        rw [evFF_add, evFF_restrictSec T _ Z' Z, evFF_restrictSec T _ Z' Z,
          evFF_restrictSec T _ Z' Z, evFF_add,
          restrictFF_add T (divisorialValuation_evFF_le_one T hL (a : L.divisorialSubmodule
            U.unop).2 hTW Z) (divisorialValuation_evFF_le_one T hL (b : L.divisorialSubmodule
            U.unop).2 hTW Z)])
      map_smul' := fun r a => Subtype.ext (eq_of_evFF_eq fun Z' => by
        have hYW := genericPoint_mem_of_index_preimage T Z'
        let Z := topIndex Y hYW
        have hTW := support_inter_nonempty_of_index T Z'
        change evFF (restrictSec T ((show Γ(Y, U.unop) from r) •
            (show ToType ((rationalFunctionsPresheaf Y).obj (op U.unop)) from
              (a : L.divisorialSubmodule U.unop).1))) Z' =
          evFF (T.idealSheaf.subschemeι.app U.unop (show Γ(Y, U.unop) from r) •
            restrictSec T (a : L.divisorialSubmodule U.unop).1) Z'
        have hr := isRestrictionAlong_germ T hYW (genericPoint_mem_of_index Z') r
        rw [evFF_smul, evFF_restrictSec T _ Z' Z, evFF_restrictSec T _ Z' Z, evFF_smul,
          restrictFF_mul T (le_one_of_isRestrictionAlong T hr)
            (divisorialValuation_evFF_le_one T hL (a : L.divisorialSubmodule U.unop).2 hTW Z),
          restrictFF_eq T hr]) }

include sY in
/-- **The restriction morphism** `𝒪_Y(L) ⟶ ι_*𝒪_T(L|_T)` for a divisor `L` of which `T` is not
a component: a rational function regular along `T` goes to its restriction. -/
private noncomputable def restrictionHom {L : Divisor Y} (hL : L.coeff T = 0) :
    L.divisorialSheaf ⟶ (Scheme.Modules.pushforward T.idealSheaf.subschemeι).obj
      (Divisor.divisorialSheaf (L.restrictPrimeDivisor T)) :=
  ⟨{ app U := restrictionHomApp T sY hL U
     naturality := fun {U V} i => by
      ext a
      refine Subtype.ext (eq_of_evFF_eq fun Z' => ?_)
      have hYW := genericPoint_mem_of_index_preimage T Z'
      change evFF (restrictSec T ((rationalFunctionsPresheaf Y).map i
          (a : L.divisorialSubmodule U.unop).1)) Z' =
        evFF ((rationalFunctionsPresheaf T.idealSheaf.subscheme).map
          ((Opens.map T.idealSheaf.subschemeι.base).op.map i)
          (restrictSec T (a : L.divisorialSubmodule U.unop).1)) Z'
      rw [evFF_map, evFF_restrictSec T _ Z' (topIndex Y hYW),
        evFF_restrictSec T _ _ (topIndex Y (i.unop.le hYW)), evFF_map]
      rfl }⟩

include sY in
/-- **Restricting a local equation.** If `a`, a unit at `η_T`, is a local equation of `L` on
`V`, then `a|_T` is one of `L|_T` along every prime divisor of `T` with generic point in `V`. -/
private theorem ord_restrict_eq_coeff {L : Divisor Y} (hL : L.coeff T = 0) (V : Y.Opens)
    (a : Y.presheaf.stalk (T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)))
    (ha : IsUnit a)
    (hloc : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ V).Nonempty →
      Y.ord (algebraMap _ Y.functionField a) E.genericPoint = L.coeff E)
    (Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme)
    (hQ : T.idealSheaf.subschemeι Q.genericPoint ∈ V) :
    T.idealSheaf.subscheme.ord ((T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a)
      Q.genericPoint = (L.restrictPrimeDivisor T).coeff Q := by
  obtain ⟨s, hs, hord, hcoeff⟩ := exists_ord_restrict_coeff_restrict_eq_sum sY T L hL a ha Q
  rw [hord, hcoeff]
  exact Finset.sum_congr rfl fun E hE => by rw [hloc E ⟨_, hs E hE, hQ⟩]

omit [CompactSpace Y] [Smooth sY] [IsLocallyNoetherian T.idealSheaf.subscheme]
  [IsNormal T.idealSheaf.subscheme] [Smooth (T.idealSheaf.subschemeι ≫ sY)] in
/-- A regular function on an open meeting `E` has valuation at most one along `E`. -/
private theorem divisorialValuation_germ_le_one (E : MMP.Mori.PrimeDivisor Y) {V : Y.Opens}
    (hE : (E.support ∩ V).Nonempty) (hV : genericPoint Y ∈ V) (b : Γ(Y, V)) :
    E.divisorialValuation (Y.presheaf.germ V (genericPoint Y) hV b) ≤ 1 :=
  (E.divisorialValuation_le_one_iff _).2
    ⟨Y.presheaf.germ V E.genericPoint (E.genericPoint_mem_of_nonempty hE) b, by
      change (Y.presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _⟩

include sY in
/-- **Local surjectivity of restriction.** Every section of `ι_*𝒪_T(L|_T)` lifts, near every
point, to a section of `𝒪_Y(L)`, for `L` Cartier. -/
private theorem exists_restrictionHom_lift {L : Divisor Y} (hL : L.coeff T = 0)
    (hLc : L.IsCartier) (U : Y.Opens)
    (t : Γ((Scheme.Modules.pushforward T.idealSheaf.subschemeι).obj
      (Divisor.divisorialSheaf (L.restrictPrimeDivisor T)), U)) (x : Y) (hx : x ∈ U) :
    ∃ (V : Y.Opens) (hV : V ≤ U), x ∈ V ∧ ∃ s : Γ(L.divisorialSheaf, V),
      (restrictionHom T sY hL).app V s =
        ((Scheme.Modules.pushforward T.idealSheaf.subschemeι).obj
          (Divisor.divisorialSheaf (L.restrictPrimeDivisor T))).presheaf.map
            (homOfLE hV).op t := by
  set t' : Divisor.divisorialSubmodule (L.restrictPrimeDivisor T)
    (T.idealSheaf.subschemeι ⁻¹ᵁ U) := t
  have hcl : IsClosed T.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  by_cases hxT : x ∈ T.support
  swap
  · -- away from `T` the target vanishes
    refine ⟨U ⊓ ⟨T.supportᶜ, hcl.isOpen_compl⟩, inf_le_left, ⟨hx, hxT⟩, 0, ?_⟩
    apply Subtype.ext
    funext Z'
    exfalso
    have h : genericPoint T.idealSheaf.subscheme ∈
        T.idealSheaf.subschemeι ⁻¹ᵁ (U ⊓ ⟨T.supportᶜ, hcl.isOpen_compl⟩) :=
      genericPoint_mem_of_index Z'
    exact h.2 (subschemeι_mem_support T _)
  obtain ⟨y, rfl⟩ : x ∈ Set.range T.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hxT
  have hyU : y ∈ T.idealSheaf.subschemeι ⁻¹ᵁ U := hx
  have hηTU : genericPoint T.idealSheaf.subscheme ∈ T.idealSheaf.subschemeι ⁻¹ᵁ U :=
    ((genericPoint_spec _).specializes (Set.mem_univ y)).mem_open
      (T.idealSheaf.subschemeι ⁻¹ᵁ U).isOpen hyU
  set ZT := topIndex T.idealSheaf.subscheme hηTU
  set τ := evFF t'.1 ZT with hτ
  -- a local equation of `L` near `x`
  obtain ⟨V₁, hxV₁, φ, hφ⟩ := hLc (T.idealSheaf.subschemeι y)
  set f := rationalFunctionsEquivFunctionField Y (φ : RationalFunctions Y) with hf
  have hf0 : f ≠ 0 := ((φ.isUnit).map (rationalFunctionsEquivFunctionField Y)).ne_zero
  have hord : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ V₁).Nonempty →
      Y.ord f E.genericPoint = L.coeff E := fun E hE => by
    rw [hφ E hE, MMP.Mori.PrimeDivisor.ord_eq_ord_rationalFunctionsEquivFunctionField]
  have hvf : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ V₁).Nonempty →
      E.divisorialValuation f = WithZero.exp (-L.coeff E) := fun E hE => by
    rw [E.divisorialValuation_eq_exp_neg_ord hf0, hord E hE]
  have hvfT : T.divisorialValuation f = 1 := by
    rw [hvf T ⟨_, hxT, hxV₁⟩, hL, neg_zero, WithZero.exp_zero]
  obtain ⟨a, ha, haf⟩ := exists_isUnit_of_divisorialValuation_eq_one T hvfT
  set fT := restrictFF T f with hfT
  have hfTa : fT = (T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a :=
    restrictFF_eq T ⟨a, haf, rfl⟩
  have hfinv : T.divisorialValuation f⁻¹ = 1 := by rw [map_inv₀, hvfT, inv_one]
  have hfmul : fT * restrictFF T f⁻¹ = 1 := by
    rw [hfT, ← restrictFF_mul T hvfT.le hfinv.le, mul_inv_cancel₀ hf0]
    exact restrictFF_eq T ⟨1, map_one _, map_one _⟩
  have hfT0 : fT ≠ 0 := left_ne_zero_of_mul_eq_one hfmul
  have hordT : ∀ Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme,
      T.idealSheaf.subschemeι Q.genericPoint ∈ V₁ →
      Q.divisorialValuation fT = WithZero.exp (-(L.restrictPrimeDivisor T).coeff Q) := by
    intro Q hQ
    rw [Q.divisorialValuation_eq_exp_neg_ord hfT0, hfTa,
      ord_restrict_eq_coeff T sY hL V₁ a ha (fun E hE => by rw [haf]; exact hord E hE) Q hQ]
  -- `τ · fT` is regular at `y`
  obtain ⟨c, hc⟩ : ∃ c : T.idealSheaf.subscheme.presheaf.stalk y,
      algebraMap _ T.idealSheaf.subscheme.functionField c = τ * fT := by
    by_cases h0 : τ * fT = 0
    · exact ⟨0, by rw [map_zero, h0]⟩
    refine MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord y h0
      fun Q hQ => ?_
    have hsp : Q.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hQ
      exact specializes_iff_mem_closure.mpr hQ
    have hQU : Q.genericPoint ∈ T.idealSheaf.subschemeι ⁻¹ᵁ U :=
      hsp.mem_open (T.idealSheaf.subschemeι ⁻¹ᵁ U).isOpen hyU
    have hQV₁ : T.idealSheaf.subschemeι Q.genericPoint ∈ V₁ :=
      (hsp.map T.idealSheaf.subschemeι.continuous).mem_open V₁.isOpen hxV₁
    have h1 := divisorialValuation_evFF_le t'.2 Q ⟨_, (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl), hQU⟩ ZT
    have h2 : Q.divisorialValuation (τ * fT) ≤ 1 := by
      rw [map_mul, hordT Q hQV₁]
      calc Q.divisorialValuation τ * WithZero.exp (-(L.restrictPrimeDivisor T).coeff Q)
          ≤ WithZero.exp ((L.restrictPrimeDivisor T).coeff Q) *
            WithZero.exp (-(L.restrictPrimeDivisor T).coeff Q) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    rw [Q.divisorialValuation_eq_exp_neg_ord h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    omega
  -- lift through the closed immersion
  obtain ⟨b, hb⟩ := T.idealSheaf.subschemeι.stalkMap_surjective y c
  obtain ⟨V₂, hxV₂, b₀, hb₀⟩ := Y.presheaf.germ_exist (x := T.idealSheaf.subschemeι y) b
  have hηV₂ : genericPoint Y ∈ V₂ :=
    ((genericPoint_spec Y).specializes (Set.mem_univ (T.idealSheaf.subschemeι y))).mem_open
      V₂.isOpen hxV₂
  have hηT₂ : genericPoint T.idealSheaf.subscheme ∈ T.idealSheaf.subschemeι ⁻¹ᵁ V₂ :=
    ((genericPoint_spec _).specializes (Set.mem_univ y)).mem_open
      (T.idealSheaf.subschemeι ⁻¹ᵁ V₂).isOpen hxV₂
  set g := Y.presheaf.germ V₂ (genericPoint Y) hηV₂ b₀ * f⁻¹ with hg
  set V := U ⊓ V₁ ⊓ V₂
  have hVU : V ≤ U := inf_le_left.trans inf_le_left
  have hmem : ofFF V g ∈ L.divisorialSubmodule V := by
    refine mem_divisorialSubmodule_of_divisorialValuation_evFF_le fun E hE => ?_
    rw [evFF_ofFF, hg, map_mul, map_inv₀]
    have hE₁ : (E.support ∩ V₁).Nonempty := hE.mono (Set.inter_subset_inter_right _
      (inf_le_left.trans inf_le_right))
    rw [hvf E hE₁, ← WithZero.exp_neg, neg_neg]
    exact mul_le_of_le_one_left' (divisorialValuation_germ_le_one E
      (hE.mono (Set.inter_subset_inter_right _ inf_le_right)) hηV₂ b₀)
  refine ⟨V, hVU, ⟨⟨hx, hxV₁⟩, hxV₂⟩, ⟨ofFF V g, hmem⟩, ?_⟩
  refine Subtype.ext (eq_of_evFF_eq fun Z' => ?_)
  have hYV := genericPoint_mem_of_index_preimage T Z'
  change evFF (restrictSec T (ofFF V g)) Z' = _
  change _ = evFF ((rationalFunctionsPresheaf T.idealSheaf.subscheme).map
    ((Opens.map T.idealSheaf.subschemeι.base).op.map (homOfLE hVU).op) t'.1) Z'
  rw [evFF_map, evFF_restrictSec T _ Z' (topIndex Y hYV), evFF_ofFF,
    index_eq ⟨Z'.1, _⟩ ZT, ← hτ]
  have hr := isRestrictionAlong_germ T hηV₂ hηT₂ b₀
  have hrb : T.idealSheaf.subscheme.presheaf.germ _ (genericPoint _) hηT₂
      (T.idealSheaf.subschemeι.app V₂ b₀) =
      τ * fT := by
    rw [← hc, ← hb, ← hb₀, Scheme.Hom.germ_stalkMap_apply]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  rw [hg, restrictFF_mul T (le_one_of_isRestrictionAlong T hr) hfinv.le, restrictFF_eq T hr, hrb,
    mul_assoc, hfmul, mul_one]

/-- `L - T ≤ L`. -/
private theorem sub_single_le (L : Divisor Y) : L - Finsupp.single T 1 ≤ L :=
  sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)

include sY in
private theorem inclusion_comp_restrictionHom {L : Divisor Y} (hL : L.coeff T = 0) :
    Divisor.divisorialSheafInclusion (sub_single_le T L) ≫ restrictionHom T sY hL = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext σ
  refine Subtype.ext (eq_of_evFF_eq fun Z' => ?_)
  have hYW := genericPoint_mem_of_index_preimage T Z'
  have hTW := support_inter_nonempty_of_index T Z'
  change evFF (restrictSec T (σ : Divisor.divisorialSubmodule _ U).1) Z' = evFF 0 Z'
  rw [evFF_restrictSec T _ Z' (topIndex Y hYW)]
  have h1 := divisorialValuation_evFF_le (σ : Divisor.divisorialSubmodule _ U).2 T hTW
    (topIndex Y hYW)
  rw [DivisorWithCoeffs.coeff_sub, hL, DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same,
    zero_sub] at h1
  have hlt : T.divisorialValuation (evFF (σ : Divisor.divisorialSubmodule _ U).1
      (topIndex Y hYW)) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  rw [(restrictFF_eq_zero_iff T hlt.le).2 hlt]
  exact (map_zero _).symm

include sY in
/-- **The restriction sequence** `0 ⟶ 𝒪_Y(L - T) ⟶ 𝒪_Y(L) ⟶ ι_*𝒪_T(L|_T) ⟶ 0`, for `L` Cartier
of which `T` is not a component. -/
private theorem shortExact_restrictionHom {L : Divisor Y} (hL : L.coeff T = 0)
    (hLc : L.IsCartier) :
    (ShortComplex.mk _ _ (inclusion_comp_restrictionHom T sY hL)).ShortExact := by
  haveI : Epi (restrictionHom T sY hL) :=
    Stacks.FundamentalGroup.epi_of_isLocallySurjective _ (exists_restrictionHom_lift T sY hL hLc)
  refine ⟨?_⟩
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_isOpenCover (fun _ : Unit => ⊤)
    (by simp [TopologicalSpace.IsOpenCover]) _ fun _ W _ z hz => ?_
  set z' : L.divisorialSubmodule W := z
  refine ⟨⟨z'.1, mem_divisorialSubmodule_of_divisorialValuation_evFF_le fun E hE => ?_⟩, rfl⟩
  by_cases hET : E = T
  · subst hET
    set Z := (⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ :
      {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W})
    have hηW : genericPoint E.idealSheaf.subscheme ∈ E.idealSheaf.subschemeι ⁻¹ᵁ W := by
      obtain ⟨p, hpE, hpW⟩ := hE
      obtain ⟨q, rfl⟩ : p ∈ Set.range E.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hpE
      exact ((genericPoint_spec _).specializes (Set.mem_univ q)).mem_open
        (E.idealSheaf.subschemeι ⁻¹ᵁ W).isOpen hpW
    have h0 := congrArg (fun w : Divisor.divisorialSubmodule (L.restrictPrimeDivisor E)
      (E.idealSheaf.subschemeι ⁻¹ᵁ W) => evFF w.1 (topIndex _ hηW)) hz
    change evFF (restrictSec E z'.1) (topIndex _ hηW) = evFF 0 (topIndex _ hηW) at h0
    rw [evFF_restrictSec E _ _ Z, show evFF (0 : ToType ((rationalFunctionsPresheaf
      E.idealSheaf.subscheme).obj (op (E.idealSheaf.subschemeι ⁻¹ᵁ W)))) (topIndex _ hηW) = 0 from
      map_zero _] at h0
    have h1 := divisorialValuation_evFF_le_one E hL z'.2 hE Z
    have hlt := (restrictFF_eq_zero_iff E h1).1 h0
    rw [DivisorWithCoeffs.coeff_sub, hL, DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same,
      zero_sub]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, E.divisorialValuation (evFF z'.1 Z) = WithZero.exp n ∨
        E.divisorialValuation (evFF z'.1 Z) = 0 := by
      rcases eq_or_ne (E.divisorialValuation (evFF z'.1 Z)) 0 with h | h
      · exact ⟨0, Or.inr h⟩
      · exact ⟨WithZero.log _, Or.inl (WithZero.exp_log h).symm⟩
    rcases hn with hn | hn
    · rw [hn] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]; omega
    · rw [hn]; exact zero_le'
  · have := divisorialValuation_evFF_le z'.2 E hE
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩
    rwa [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply (Finsupp.single T 1),
      Finsupp.single_eq_of_ne hET, sub_zero]

end RestrictionSequence

/-! ### Lifting sections from the strict transform -/

section Lifting

attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] {X Y₀ : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] (μ₀ : Y₀ ⟶ X) [IsIntegral Y₀] [IsLocallyNoetherian Y₀]
  [IsNormal Y₀] [IsDominant μ₀] (S : MMP.Mori.PrimeDivisor X) (T : MMP.Mori.PrimeDivisor Y₀)
  [IsIntegral S.idealSheaf.subscheme] [IsIntegral T.idealSheaf.subscheme]
  (μT : T.idealSheaf.subscheme ⟶ S.idealSheaf.subscheme) [IsDominant μT]
  (hμT : μT ≫ S.idealSheaf.subschemeι = T.idealSheaf.subschemeι ≫ μ₀)
  (hT : μ₀ T.genericPoint = S.genericPoint)

include hμT hT in
/-- **Restriction through the strict transform.** If `μ₀` is an isomorphism near `η_S` and the
pull-back of `g` restricts on `T` to the pull-back of `h`, then `g` restricts to `h` on `S`. -/
private theorem isRestrictionAlong_of_isRestrictionAlong_strictTransform {V : X.Opens}
    (hV : IsIso (μ₀ ∣_ V)) (hSV : S.genericPoint ∈ V) {g : X.functionField}
    {h : S.idealSheaf.subscheme.functionField}
    (hgh : IsRestrictionAlong T (functionFieldMap μ₀ g) (functionFieldMap μT h)) :
    IsRestrictionAlong S g h := by
  have hvT := le_one_of_isRestrictionAlong T hgh
  have hvS := divisorialValuation_le_one_of_strictTransform μ₀ S T hT hV hSV hvT
  obtain ⟨a, rfl⟩ := (S.divisorialValuation_le_one_iff _).1 hvS
  obtain ⟨W, hηW, s, rfl⟩ := X.presheaf.germ_exist (x := S.genericPoint) a
  have hTW : T.genericPoint ∈ μ₀ ⁻¹ᵁ W := by change μ₀ T.genericPoint ∈ W; rw [hT]; exact hηW
  set a₀ : Y₀.presheaf.stalk T.genericPoint :=
    Y₀.presheaf.germ (μ₀ ⁻¹ᵁ W) T.genericPoint hTW (μ₀.app W s) with ha₀def
  have hkey : _ = (T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a₀ :=
    functionFieldMap_stalkMap_germ_strictTransform μ₀ S T μT hμT hT hηW hTW s
  have hres : IsRestrictionAlong T (functionFieldMap μ₀
      (algebraMap S.localRing X.functionField (X.presheaf.germ W S.genericPoint hηW s)))
      ((T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom a₀) := by
    refine ⟨a₀, ?_, rfl⟩
    have hX : genericPoint X ∈ W :=
      ((genericPoint_spec X).specializes (Set.mem_univ S.genericPoint)).mem_open W.isOpen hηW
    have e1 : algebraMap S.localRing X.functionField (X.presheaf.germ W S.genericPoint hηW s) =
        X.presheaf.germ W (genericPoint X) hX s := by
      change (X.presheaf.stalkSpecializes _).hom _ = _
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [e1, functionFieldMap_germ μ₀ W hX (genericPoint_mem_preimage μ₀ hX)]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have huniq := isRestrictionAlong_unique T hgh hres
  rw [← hkey] at huniq
  rw [(functionFieldMap μT).injective huniq]
  exact ⟨_, rfl, rfl⟩

omit [IsDominant μT] in
include hμT in
private theorem preimage_strictTransform_eq (U : X.Opens) :
    μT ⁻¹ᵁ (S.idealSheaf.subschemeι ⁻¹ᵁ U) = T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ U) := by
  ext z
  change S.idealSheaf.subschemeι (μT z) ∈ U ↔ μ₀ (T.idealSheaf.subschemeι z) ∈ U
  have : S.idealSheaf.subschemeι (μT z) = μ₀ (T.idealSheaf.subschemeι z) := by
    change (μT ≫ S.idealSheaf.subschemeι) z = (T.idealSheaf.subschemeι ≫ μ₀) z
    rw [hμT]
  rw [this]

variable [CompactSpace Y₀] [Smooth (μ₀ ≫ sX)]
  [IsLocallyNoetherian T.idealSheaf.subscheme] [IsNormal T.idealSheaf.subscheme]
  [Smooth (T.idealSheaf.subschemeι ≫ μ₀ ≫ sX)]

include hμT in
/-- The section of `ι_*𝒪_T(L|_T)` over `μ₀⁻¹U` given by the pull-back of a section of
`μ_{T*}𝒪_T(L|_T)` over `S ∩ U`. -/
private theorem ofFF_mem_of_mem {L : Divisor Y₀} (U : X.Opens)
    {h : S.idealSheaf.subscheme.functionField}
    (hh : h ∈ MMP.Intersection.multiplierIdealSections μT (L.restrictPrimeDivisor T)
      (S.idealSheaf.subschemeι ⁻¹ᵁ U)) :
    ofFF (T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ U)) (functionFieldMap μT h) ∈
      Divisor.divisorialSubmodule (L.restrictPrimeDivisor T)
        (T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ U)) := by
  refine mem_divisorialSubmodule_of_divisorialValuation_evFF_le fun Q hQ => ?_
  rw [evFF_ofFF]
  have hQ' : (Q.support ∩ μT ⁻¹ᵁ (S.idealSheaf.subschemeι ⁻¹ᵁ U)).Nonempty := by
    rw [preimage_strictTransform_eq μ₀ S T μT hμT U]; exact hQ
  have := hh.2 Q hQ'
  rwa [MMP.Mori.PrimeDivisor.valuationOver_apply] at this

include sX hμT hT in
/-- A section of `𝒪_{Y₀}(L)` over `μ₀⁻¹V` restricting on `T` to the pull-back of `h` gives a
section of `μ₀_*𝒪_{Y₀}(L)` over `V` restricting to `h` on `S`. -/
private theorem exists_mem_of_restrictSec_eq {L : Divisor Y₀} (hL : L.coeff T = 0)
    {V' : X.Opens} (hV' : IsIso (μ₀ ∣_ V')) (hSV' : S.genericPoint ∈ V') {V : X.Opens}
    (hSV : S.genericPoint ∈ V)
    (hbij : Function.Bijective (functionFieldMap μ₀))
    (σ : L.divisorialSubmodule (μ₀ ⁻¹ᵁ V)) (h : S.idealSheaf.subscheme.functionField)
    (hσ : ∀ Z', evFF (restrictSec T σ.1) Z' = functionFieldMap μT h) :
    ∃ g ∈ MMP.Intersection.multiplierIdealSections μ₀ L V, IsRestrictionAlong S g h := by
  have hTV : T.genericPoint ∈ μ₀ ⁻¹ᵁ V := by change μ₀ T.genericPoint ∈ V; rw [hT]; exact hSV
  have hYV : genericPoint Y₀ ∈ μ₀ ⁻¹ᵁ V :=
    ((genericPoint_spec Y₀).specializes (Set.mem_univ T.genericPoint)).mem_open
      (μ₀ ⁻¹ᵁ V).isOpen hTV
  set Z := topIndex Y₀ hYV
  obtain ⟨g, hg⟩ := hbij.2 (evFF σ.1 Z)
  refine ⟨g, (mem_divisorialSubmodule_iff_mem_multiplierIdealSections μ₀ L V σ.1 Z g hg).1 σ.2,
    ?_⟩
  have hηT : genericPoint T.idealSheaf.subscheme ∈ T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ V) := by
    change T.idealSheaf.subschemeι (genericPoint _) ∈ μ₀ ⁻¹ᵁ V
    exact hTV
  have hTsupp : T.genericPoint ∈ T.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hTmeet : (T.support ∩ μ₀ ⁻¹ᵁ V).Nonempty := ⟨T.genericPoint, hTsupp, hTV⟩
  have h1 := hσ (topIndex _ hηT)
  rw [evFF_restrictSec T _ _ Z, ← hg] at h1
  have hle := divisorialValuation_evFF_le_one T hL σ.2 hTmeet Z
  rw [← hg] at hle
  have hr := isRestrictionAlong_restrictFF T hle
  rw [h1] at hr
  exact isRestrictionAlong_of_isRestrictionAlong_strictTransform μ₀ S T μT hμT hT hV' hSV' hr

include sX hμT hT in
/-- **Local lifting.** If `R¹μ₀_*𝒪(L - T) = 0`, every section of `μ_{T*}𝒪_T(L|_T)` over `S ∩ U`
is, near every point of `S ∩ U`, the restriction of a section of `μ₀_*𝒪_{Y₀}(L)`. -/
private theorem exists_local_lift_of_isZero_rightDerived_one {L : Divisor Y₀}
    (hL : L.coeff T = 0) (hLc : L.IsCartier) {V' : X.Opens} (hV' : IsIso (μ₀ ∣_ V'))
    (hSV' : S.genericPoint ∈ V') (hbij : Function.Bijective (functionFieldMap μ₀))
    (h1 : IsZero (((Scheme.Modules.pushforward μ₀).rightDerived 1).obj
      (L - Finsupp.single T 1).divisorialSheaf))
    (U : X.Opens) (h : S.idealSheaf.subscheme.functionField)
    (hh : h ∈ MMP.Intersection.multiplierIdealSections μT (L.restrictPrimeDivisor T)
      (S.idealSheaf.subschemeι ⁻¹ᵁ U))
    (x : S.idealSheaf.subscheme) (hx : x ∈ S.idealSheaf.subschemeι ⁻¹ᵁ U) :
    ∃ V : X.Opens, S.idealSheaf.subschemeι x ∈ V ∧ V ≤ U ∧
      ∃ g ∈ MMP.Intersection.multiplierIdealSections μ₀ L V, IsRestrictionAlong S g h := by
  have hSES := shortExact_restrictionHom T (μ₀ ≫ sX) hL hLc
  have hSES' := Stacks.Cohomology.SectionsEpi.shortExact_map_of_isZero_rightDerived_one
    (Scheme.Modules.pushforward μ₀) hSES h1
  haveI hepi : Epi ((Scheme.Modules.pushforward μ₀).map (restrictionHom T (μ₀ ≫ sX) hL)) :=
    hSES'.epi_g
  have hls := AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi X
    ((Scheme.Modules.pushforward μ₀).map (restrictionHom T (μ₀ ≫ sX) hL))
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hls
  set t : Divisor.divisorialSubmodule (L.restrictPrimeDivisor T)
    (T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ U)) :=
      ⟨ofFF _ (functionFieldMap μT h), ofFF_mem_of_mem μ₀ S T μT hμT U hh⟩ with ht
  obtain ⟨V, hVU, ⟨σ, hσ⟩, hxV⟩ := hls U t (S.idealSheaf.subschemeι x) hx
  have hSV : S.genericPoint ∈ V := by
    have hsp : S.genericPoint ⤳ S.idealSheaf.subschemeι x := by
      have hmem := subschemeι_mem_support S x
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
      exact specializes_iff_mem_closure.mpr hmem
    exact hsp.mem_open V.isOpen hxV
  refine ⟨V, hxV, hVU, exists_mem_of_restrictSec_eq sX μ₀ S T μT hμT hT hL hV' hSV' hSV hbij
    (show L.divisorialSubmodule (μ₀ ⁻¹ᵁ V) from σ) h fun Z' => ?_⟩
  have h2 : evFF (restrictSec T (show L.divisorialSubmodule (μ₀ ⁻¹ᵁ V) from σ).1) Z' =
      evFF ((rationalFunctionsPresheaf T.idealSheaf.subscheme).map
        ((Opens.map T.idealSheaf.subschemeι.base).op.map
          ((Opens.map μ₀.base).op.map (homOfLE hVU).op)) t.1) Z' :=
    congrArg (fun w : Divisor.divisorialSubmodule (L.restrictPrimeDivisor T)
      (T.idealSheaf.subschemeι ⁻¹ᵁ (μ₀ ⁻¹ᵁ V)) => evFF w.1 Z') hσ
  rw [h2, evFF_map, ht]
  exact evFF_ofFF _ _ _

end Lifting

/-! ### Normality of `S` from the lifting property -/

section Normality

/-- An element of `K(S)` integral over the local ring at `x` has a multiple `s · y`, with `s` a
unit at `x`, integral over the sections on an open neighbourhood of `x`. -/
private theorem exists_isIntegral_germToFunctionField_mul {S : Scheme.{0}} [IsIntegral S] (x : S)
    {y : S.functionField} (hy : IsIntegral (S.presheaf.stalk x) y) :
    ∃ (U : S.Opens) (hxU : x ∈ U) (s : Γ(S, U)), x ∈ S.basicOpen s ∧
      haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
      IsIntegral Γ(S, U) (S.germToFunctionField U s * y) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  let _hA := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, hxU⟩
  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have := functionField_isScalarTower S U ⟨x, hxU⟩
  obtain ⟨⟨s, hs⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl y hy
  refine ⟨U, hxU, s, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen _ _ _ hxU]
    exact IsLocalization.map_units (S.presheaf.stalk x)
      (⟨s, hs⟩ : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
  · rwa [Submonoid.mk_smul, Algebra.smul_def] at hint

/-- If `s · y` is integral over `Γ(S, U)`, then along every prime divisor `Q` of a normal `T` over
`S` with `μ(η_Q) ∈ D(s)`, the pull-back of `y` has valuation at most one. -/
private theorem divisorialValuation_functionFieldMap_le_one_of_isIntegral {S T : Scheme.{0}}
    [IsIntegral S] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (μ : T ⟶ S) [IsDominant μ] (U : S.Opens) [Nonempty U] (s : Γ(S, U)) {y : S.functionField}
    (hint : IsIntegral Γ(S, U) (S.germToFunctionField U s * y))
    (Q : MMP.Mori.PrimeDivisor T) (hQ : μ Q.genericPoint ∈ S.basicOpen s) :
    Q.divisorialValuation (functionFieldMap μ y) ≤ 1 := by
  have hQU : Q.genericPoint ∈ μ ⁻¹ᵁ U := S.basicOpen_le s hQ
  have hSU : genericPoint S ∈ U :=
    ((genericPoint_spec S).specializes (Set.mem_univ (μ Q.genericPoint))).mem_open U.isOpen hQU
  have hTU : genericPoint T ∈ μ ⁻¹ᵁ U :=
    ((genericPoint_spec T).specializes (Set.mem_univ Q.genericPoint)).mem_open
      (μ ⁻¹ᵁ U).isOpen hQU
  let φ : Γ(S, U) →+* T.presheaf.stalk Q.genericPoint :=
    (T.presheaf.germ (μ ⁻¹ᵁ U) Q.genericPoint hQU).hom.comp (μ.app U).hom
  have hφ : ∀ a, algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField (φ a) =
      functionFieldMap μ (S.germToFunctionField U a) := by
    intro a
    change _ = functionFieldMap μ (S.presheaf.germ U (genericPoint S) hSU a)
    rw [functionFieldMap_germ μ U hSU hTU]
    exact T.presheaf.germ_stalkSpecializes_apply hQU _ _
  have hint' := IsIntegral.map_of_comp_eq φ (functionFieldMap μ) (RingHom.ext hφ) hint
  haveI := IsNormal.stalk_normal (X := T) Q.genericPoint
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T.presheaf.stalk Q.genericPoint)
    (K := T.functionField)).1 hint'
  have h1 : Q.divisorialValuation (functionFieldMap μ (S.germToFunctionField U s * y)) ≤ 1 :=
    (Q.divisorialValuation_le_one_iff _).2 ⟨r, hr⟩
  have hu : IsUnit (φ s) := by
    have : Q.genericPoint ∈ μ ⁻¹ᵁ S.basicOpen s := hQ
    rw [Scheme.preimage_basicOpen] at this
    exact (T.mem_basicOpen _ _ hQU).1 this
  have h2 : Q.divisorialValuation (functionFieldMap μ (S.germToFunctionField U s)) = 1 := by
    rw [← hφ]
    obtain ⟨u, hu'⟩ := hu
    have ha := (Q.divisorialValuation_le_one_iff
      (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        (u : T.presheaf.stalk Q.genericPoint))).2 ⟨_, rfl⟩
    have hb := (Q.divisorialValuation_le_one_iff
      (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
        ((u⁻¹ : (T.presheaf.stalk Q.genericPoint)ˣ) : T.presheaf.stalk Q.genericPoint))).2 ⟨_, rfl⟩
    have hab : Q.divisorialValuation (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          (u : T.presheaf.stalk Q.genericPoint)) *
        Q.divisorialValuation (algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
          ((u⁻¹ : (T.presheaf.stalk Q.genericPoint)ˣ) : T.presheaf.stalk Q.genericPoint)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [← hu']
    exact le_antisymm ha (hab.symm.le.trans (mul_le_of_le_one_right' hb))
  rw [map_mul, map_mul, h2, one_mul] at h1
  exact h1

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The restriction to `S` of a rational function regular at `ι(x)` is regular at `x`. -/
private theorem exists_algebraMap_eq_of_isRestrictionAlong (S : MMP.Mori.PrimeDivisor X)
    [IsIntegral S.idealSheaf.subscheme] {x : S.idealSheaf.subscheme} {g : X.functionField}
    (hg : ∀ Γ : MMP.Mori.PrimeDivisor X, S.idealSheaf.subschemeι x ∈ Γ.support →
      Γ.divisorialValuation g ≤ 1)
    {h : S.idealSheaf.subscheme.functionField} (hgh : IsRestrictionAlong S g h) :
    ∃ r : S.idealSheaf.subscheme.presheaf.stalk x,
      algebraMap _ S.idealSheaf.subscheme.functionField r = h := by
  rcases eq_or_ne g 0 with rfl | hg0
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact isRestrictionAlong_unique S ⟨0, map_zero _, map_zero _⟩ hgh
  obtain ⟨b, hb⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord
    (S.idealSheaf.subschemeι x) hg0 fun Γ hΓ => by
      have := hg Γ hΓ
      rw [Γ.divisorialValuation_eq_exp_neg_ord hg0, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at this
      omega
  have hsp : S.idealSheaf.subschemeι (genericPoint S.idealSheaf.subscheme) ⤳
      S.idealSheaf.subschemeι x :=
    (genericPoint_specializes x).map S.idealSheaf.subschemeι.continuous
  have hres : IsRestrictionAlong S g
      ((S.idealSheaf.subschemeι.stalkMap _).hom ((X.presheaf.stalkSpecializes hsp).hom b)) := by
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom b, ?_, rfl⟩
    rw [← hb, TopCat.Presheaf.stalkSpecializes_comp_apply]
    rfl
  refine ⟨(S.idealSheaf.subschemeι.stalkMap x).hom b, ?_⟩
  rw [isRestrictionAlong_unique S hgh hres, Scheme.Hom.stalkSpecializes_stalkMap_apply]
  rfl

/-- **Normality from lifting.** Let `μ_T : T ⟶ S` be a surjective dominant morphism from a normal
integral scheme and `G` an effective divisor on `T`. Suppose every section of `μ_{T*}𝒪_T(G)` over
`S ∩ U` is, near every point `x` of `S ∩ U`, the restriction of a rational function on `X` regular
at `x`. Then `S` is normal. -/
private theorem isNormal_subscheme_of_forall_exists_isRestrictionAlong
    (S : MMP.Mori.PrimeDivisor X) [IsIntegral S.idealSheaf.subscheme] {T : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (μT : T ⟶ S.idealSheaf.subscheme)
    [IsDominant μT] [Surjective μT] (G : Divisor T) (hG : ∀ Q, 0 ≤ G.coeff Q)
    (hlift : ∀ (U : X.Opens) (h : S.idealSheaf.subscheme.functionField),
      h ∈ MMP.Intersection.multiplierIdealSections μT G (S.idealSheaf.subschemeι ⁻¹ᵁ U) →
      ∀ x ∈ S.idealSheaf.subschemeι ⁻¹ᵁ U, ∃ g : X.functionField,
        (∀ Γ : MMP.Mori.PrimeDivisor X, S.idealSheaf.subschemeι x ∈ Γ.support →
          Γ.divisorialValuation g ≤ 1) ∧ IsRestrictionAlong S g h) :
    IsNormal S.idealSheaf.subscheme := by
  refine ⟨fun x => inferInstance, fun x => ?_⟩
  rw [isIntegrallyClosed_iff S.idealSheaf.subscheme.functionField]
  intro y hy
  obtain ⟨U, hxU, s, hxs, hint⟩ := exists_isIntegral_germToFunctionField_mul x hy
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨U', hU'o, hU'⟩ :=
    S.idealSheaf.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1
      (S.idealSheaf.subscheme.basicOpen s).isOpen
  let U'' : X.Opens := ⟨U', hU'o⟩
  have hpre : S.idealSheaf.subschemeι ⁻¹ᵁ U'' = S.idealSheaf.subscheme.basicOpen s :=
    Opens.ext hU'
  have hmem : y ∈ MMP.Intersection.multiplierIdealSections μT G
      (S.idealSheaf.subschemeι ⁻¹ᵁ U'') := by
    refine ⟨fun h0 => ?_, fun Q hQ => ?_⟩
    · exfalso
      obtain ⟨t, ht⟩ := μT.surjective x
      have : t ∈ μT ⁻¹ᵁ (S.idealSheaf.subschemeι ⁻¹ᵁ U'') := by
        change μT t ∈ S.idealSheaf.subschemeι ⁻¹ᵁ U''
        rw [ht, hpre]
        exact hxs
      rw [h0] at this
      exact this
    · rw [PrimeDivisor.valuationOver_apply]
      have hQ' : μT Q.genericPoint ∈ S.idealSheaf.subscheme.basicOpen s := by
        rw [← hpre]
        exact (Q.genericPoint_mem_iff _).mpr hQ
      refine (divisorialValuation_functionFieldMap_le_one_of_isIntegral μT U s hint Q hQ').trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hG Q
  have hx' : x ∈ S.idealSheaf.subschemeι ⁻¹ᵁ U'' := by
    rw [hpre]
    exact hxs
  obtain ⟨g, hg, hgh⟩ := hlift U'' y hmem x hx'
  exact exists_algebraMap_eq_of_isRestrictionAlong S hg hgh

end Normality

/-! ### Kawamata–Viehweg vanishing on the log resolution -/

section Vanishing

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- **Relative vanishing for a fractional boundary.** Let `p : W ⟶ X` be a projective birational
morphism from a smooth variety onto a `ℚ`-factorial normal variety, `K_W` a canonical divisor and
`Θ₀` a `ℚ`-divisor with coefficients in `[0, 1)` such that every `ℚ`-divisor supported on
`Θ₀ + Ex(p)` is snc. If `M - (K_W + Θ₀)` is the pull-back of a `ℚ`-Cartier divisor `C/m` of `X`,
then `R^i p_* 𝒪_W(M) = 0` for `i > 0`: perturb `Θ₀` by a small multiple of an effective
exceptional divisor `F` with `-F` relatively ample. -/
private theorem isZero_rightDerived_of_fractionalBoundary (hQ : IsQFactorial sX)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) [IsDominant p] (hW : IsNormalVariety k (p ≫ sX))
    (hsm : IsSmoothScheme (p ≫ sX)) (hproj : IsProjectiveMorphism p)
    (hb : IsBirationalMorphism p) {n : ℕ} {KW : Divisor W}
    (hKW : KW.IsCanonicalDivisor (p ≫ sX) n) (M : Divisor W) (Θ₀ : QDivisor W)
    (hΘ0 : ∀ P, 0 ≤ Θ₀.coeff P) (hΘ1 : ∀ P, Θ₀.coeff P < 1)
    (hsnc : ∀ G : QDivisor W, (∀ P, G.coeff P ≠ 0 → Θ₀.coeff P ≠ 0 ∨
      RationalMap.IsExceptional (X := W) p.toRationalMap P) →
        DivisorWithCoeffs.IsSNC (p ≫ sX) G)
    (m : ℕ) (hm : 0 < m) (C : Divisor X) (hC : C.IsCartier)
    (hCs : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ C.supp)
    (Cμ : Divisor W) (hCμ : C.IsPullback p hCs Cμ)
    (hCeq : Divisor.toQDivisor Cμ = (m : ℤ) • (Divisor.toQDivisor M -
      (Divisor.toQDivisor KW + Θ₀)))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward p).rightDerived i).obj M.divisorialSheaf) := by
  classical
  haveI : MMP.Mori.IsVariety k sX := hQ.1.1
  haveI : MMP.Mori.IsVariety k (p ≫ sX) := hW.1
  have hcart : ∀ G : Divisor W, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨Fexc, e, he, hFexc0, hFexcEx, Dexc, hDexc, hDexceq, hDexcamp⟩ :=
    MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional sX (p ≫ sX) hQ hW p rfl hproj hb
  set t : ℚ := ∑ P ∈ Fexc.support, Fexc.coeff P / (1 - Θ₀.coeff P) with ht
  have ht0 : ∀ P ∈ Fexc.support, Fexc.coeff P / (1 - Θ₀.coeff P) ≤ t := fun P hP =>
    Finset.single_le_sum (f := fun P => Fexc.coeff P / (1 - Θ₀.coeff P))
      (fun Q _ => div_nonneg (hFexc0 Q) (by linarith [hΘ1 Q])) hP
  set N : ℕ := ⌈(e : ℚ) * t⌉₊ + 1 with hN
  set c : ℕ := m * N with hc
  have hc0 : 0 < c := Nat.mul_pos hm (by omega)
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc0
  have hct : (e : ℚ) * t < c := by
    have h1 := Nat.le_ceil ((e : ℚ) * t)
    have h2 : (N : ℚ) ≤ c := by exact_mod_cast Nat.le_mul_of_pos_left N hm
    have h3 : ((⌈(e : ℚ) * t⌉₊ : ℕ) : ℚ) + 1 = N := by rw [hN]; push_cast; ring
    linarith
  set δ : ℚ := (e : ℚ) / c with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set Θ : QDivisor W := Θ₀ + δ • Fexc with hΘdef
  have hΘc : ∀ P, Θ.coeff P = Θ₀.coeff P + δ * Fexc.coeff P :=
    fun P => by simp [hΘdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
  have hB0 : Θ.IsEffective := fun P => by
    rw [hΘc]
    have h3 : 0 ≤ δ * Fexc.coeff P := mul_nonneg hδ0 (hFexc0 P)
    linarith [hΘ0 P]
  have hB1 : ∀ P, Θ.coeff P < 1 := fun P => by
    rw [hΘc]
    by_cases hF : Fexc.coeff P = 0
    · simpa [hF] using hΘ1 P
    · have hmem : P ∈ Fexc.support := Finsupp.mem_support_iff.2 hF
      have h1 := ht0 P hmem
      have hpos : 0 < 1 - Θ₀.coeff P := by linarith [hΘ1 P]
      have h2 : Fexc.coeff P ≤ t * (1 - Θ₀.coeff P) := by rwa [div_le_iff₀ hpos] at h1
      have h3 : δ * Fexc.coeff P ≤ δ * t * (1 - Θ₀.coeff P) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h2 hδ0
      have h4 : δ * t < 1 := by
        rwa [hδ, div_mul_eq_mul_div, div_lt_one hcq]
      have h5 : δ * t * (1 - Θ₀.coeff P) < 1 - Θ₀.coeff P := by nlinarith
      linarith
  have hBsnc : DivisorWithCoeffs.IsSNC (p ≫ sX) Θ := hsnc Θ fun P hP => by
    by_contra hcon
    push Not at hcon
    obtain ⟨hΘ, hEx⟩ := hcon
    apply hP
    have : Fexc.coeff P = 0 := by
      by_contra h
      exact hEx (hFexcEx P h)
    rw [hΘc, hΘ, this]; simp
  have hCn := hCμ.zsmul hC (N : ℤ)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p _)
  have hLc : (-Dexc + (N : ℤ) • Cμ).IsCartier := hcart _
  have hLamp : (-Dexc + (N : ℤ) • Cμ).IsRelativelyAmple p hLc :=
    MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback p hDexc.neg hDexcamp
      (hC.zsmul _) hCn (hcart _)
  have heq : Divisor.toQDivisor (-Dexc + (N : ℤ) • Cμ) =
      ((c : ℕ) : ℤ) • (Divisor.toQDivisor M - (Divisor.toQDivisor KW + Θ)) := by
    ext P
    have hC' : (Cμ.coeff P : ℚ) = m * (M.coeff P - (KW.coeff P + Θ₀.coeff P)) := by
      have := congrArg (fun G : QDivisor W => G.coeff P) hCeq
      simpa [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_add] using this
    have hD' : (Dexc.coeff P : ℚ) = e * Fexc.coeff P := by
      have := congrArg (fun G : QDivisor W => G.coeff P) hDexceq
      simpa [DivisorWithCoeffs.coeff_smul] using this
    have hΘP := hΘc P
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_neg, nsmul_eq_mul, zsmul_eq_mul,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast, smul_eq_mul]
      at hC' hD' hΘP ⊢
    have hNq : (N : ℚ) ≠ 0 := by positivity
    have hmq : (m : ℚ) ≠ 0 := by positivity
    rw [hΘP, hC', hD', hδ, hc]
    push_cast
    field_simp
    ring
  exact MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
    (p ≫ sX) sX hsm p rfl hproj hKW hB0 hBsnc hB1 (hcart M) ⟨c, hc0, _, hLc, heq, hLamp⟩ i hi

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
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety k sX := hX.1
  haveI : MMP.Mori.IsVariety k (p ≫ sX) := hW.1
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

/-! ### Prime divisors of a model -/

section Geometry

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

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
    exact absurd (h2.trans_lt hlt) (lt_irrefl _)
  have hle : v g⁻¹ ≤ 1 := by
    rw [← hab, map_div₀, hb1, div_one]
    exact h1 a
  rw [map_inv₀, hg] at hle
  exact absurd hle (by decide)

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

/-- A prime divisor `P` of a model `p : W ⟶ X` is `p`-exceptional exactly when its image
`p(η_P)` has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety k sX) {p : W ⟶ X}
    (hW : IsNormalVariety k (p ≫ sX)) (hb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) p.toRationalMap P ↔
      2 ≤ Order.coheight (p P.genericPoint) :=
  DivisorOver.isExceptional_iff_two_le_coheight hX ⟨W, p, hW, hb, P⟩

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

end Model

/-- **A prime plt floor is normal.** Let `X` be a `ℚ`-factorial projective variety over an
algebraically closed field `k` of characteristic zero, `K` a canonical divisor and `n = dim X`,
`S` a prime divisor of `X`, and `B` an effective `ℚ`-divisor with `⌊B⌋ = 0` and
`B.coeff S = 0`. If `(X, S + B)` is plt, then the integral closed subscheme
`S.idealSheaf.subscheme` is normal. -/
public theorem IsPltPair.isNormal_subscheme_of_isQFactorial_of_charZero {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} (hQ : Fourfold.IsQFactorial sX)
    (hX : IsProjectiveVariety k sX) {S : PrimeDivisor X} {B : QDivisor X} (hB : B.IsEffective)
    (hB0 : B.roundDown = 0) (hBS : B.coeff S = 0) {n : ℕ} {K : Divisor X}
    (h : IsPltPair sX n K (Finsupp.single S 1 + B)) :
    IsNormal S.idealSheaf.subscheme := by
  classical
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔdef
  have hPW : IsPairWith sX n K Δ := h.1
  have hXn : IsNormalVariety k sX := hPW.1
  have hP : MMP.Mori.IsPair sX Δ := h.isPair
  haveI : MMP.Mori.IsVariety k sX := hXn.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : CompactSpace X := haveI := hXn.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  -- the coefficients of the boundary `Δ = S + B`
  have hBlt : ∀ Q, B.coeff Q < 1 := fun Q => by
    have h1 := congrArg (fun D : Divisor X => D.coeff Q) hB0
    simp only [DivisorWithCoeffs.coeff_roundDown] at h1
    exact (Int.floor_eq_zero_iff.1 h1).2
  have hΔc : ∀ Q, Δ.coeff Q = (Finsupp.single S (1 : ℚ)) Q + B.coeff Q := fun Q => by
    rw [hΔdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_apply (Finsupp.single S 1)]
  have hΔS : Δ.coeff S = 1 := by
    rw [hΔc, hBS, add_zero, Finsupp.single_eq_same]
  have hΔ0 : ∀ Q, 0 ≤ Δ.coeff Q := fun Q => by
    rw [hΔc, Finsupp.single_apply]
    split_ifs <;> linarith [hB Q]
  have hΔ1 : ∀ Q, Q ≠ S → Δ.coeff Q < 1 := fun Q hQ => by
    rw [hΔc, Finsupp.single_eq_of_ne hQ, zero_add]
    exact hBlt Q
  -- the log resolution
  obtain ⟨W, p, hres, -, hsncW, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hXn Δ.support
  haveI : MMP.Mori.IsVariety k (p ≫ sX) := hres.isVariety_source
  haveI : LocallyOfFiniteType (p ≫ sX) := hres.isVariety_source.toLocallyOfFiniteType
  haveI : IsProper p := hres.isProjective.isProper
  have hsr : IsSmoothResolution sX p :=
    ⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  haveI : IsIntegral W := hsr.isIntegral
  haveI : IsNormal W := hsr.isNormal
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := haveI := hres.isVariety_source.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  have hWn : IsNormalVariety k (p ≫ sX) := (hsr.isNormalVariety hXn).1
  have hb : IsBirationalMorphism p := hres.isBirationalMorphism
  haveI : IsDominant p := hb.isDominant
  have hbij := hb.functionFieldMap_bijective
  have hsm : IsSmoothScheme (p ≫ sX) := hres.isSmoothScheme
  haveI : Smooth (p ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hproj : IsProjectiveMorphism p := by
    obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
    obtain ⟨H, hH, hHa⟩ :=
      AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism sX M hMa hX.isProjective
    exact AlgebraicGeometry.isProjectiveMorphism_of_isProjective p H hHa hres.isProjective
  have hcart : ∀ G : Divisor W, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  -- the strict transform `T` of `S`
  haveI hV : IsIso (p ∣_ biregularLocus p) := isBiregular_biregularLocus p
  have hSV : S.genericPoint ∈ biregularLocus p :=
    MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb S
  obtain ⟨T, hT, hTI⟩ := exists_primeDivisor_map_genericPoint_eq p hV S hSV
  have hTP : ∀ P : MMP.Mori.PrimeDivisor W, p P.genericPoint = S.genericPoint → P = T :=
    fun P hP => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.Oai4C1.eq_of_map_eq_genericPoint hb hP hT)
  -- the crepant boundary `Δ_W`, with `K_W + Δ_W = p^*(K_X + S + B)`
  obtain ⟨ω, hω0, hωK, hKW⟩ := exists_divisorOfForm_pullback_isCanonicalDivisor sX hXn hWn hsm hb
    hPW.2.1
  set KW := divisorOfForm (pullbackRationalPluriForms sX p ω) with hKWdef
  obtain ⟨ΔW, hΔW, -⟩ := (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP hPW.2.1 p hWn hb).1
  have hexc := isExceptional_iff_two_le_coheight hXn hWn hb
  have hΔWc : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → ΔW.coeff P = Δ.coeff Q := fun P Q h =>
    coeff_crepantBoundary_of_map_genericPoint hP hΔW h
  have hΔWex : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      ΔW.coeff P < 1 := by
    intro P h2
    have hE : (⟨W, p, hWn, hb, P⟩ : DivisorOver k sX).IsExceptional := (hexc P).2 h2
    have h1 : (-1 : ℝ) < ((-ΔW.coeff P : ℚ) : ℝ) := EReal.coe_lt_coe_iff.mp
      (by simpa using h.2.trans_le (discrep_le hE (hΔW P)))
    have h2 : (-1 : ℚ) < -ΔW.coeff P := by exact_mod_cast h1
    linarith
  have hΔWT : ΔW.coeff T = 1 := (hΔWc T S hT).trans hΔS
  have hΔWlt : ∀ P, P ≠ T → ΔW.coeff P < 1 := by
    intro P hPT
    rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, hQ⟩ | h2
    · rw [hΔWc P Q hQ]
      refine hΔ1 Q fun hQS => hPT (hTP P ?_)
      rw [hQ, hQS]
    · exact hΔWex P h2
  -- `E = -⌊Δ_W - T⌋` and the fractional boundary `Θ₀ = Δ_W - T + E`
  set Tw : Divisor W := Finsupp.single T 1 with hTw
  have hTwc : ∀ P, (Tw.coeff P : ℚ) = if P = T then 1 else 0 := fun P => by
    rw [hTw, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    by_cases h1 : T = P
    · rw [if_pos h1, if_pos h1.symm]; simp
    · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
  set E : Divisor W := -(ΔW - Divisor.toQDivisor Tw).roundDown with hEdef
  have hEc : ∀ P, E.coeff P = -⌊ΔW.coeff P - Tw.coeff P⌋ := fun P => by
    simp [hEdef, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
  have hET : E.coeff T = 0 := by
    rw [hEc, hΔWT, hTwc, if_pos rfl]; simp
  have hEnex : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → E.coeff P = 0 := by
    intro P Q hQ
    by_cases hPT : P = T
    · rw [hPT, hET]
    · rw [hEc, hTwc, if_neg hPT, hΔWc P Q hQ]
      have h0 := hΔ0 Q
      have h1 : Δ.coeff Q < 1 := by rw [← hΔWc P Q hQ]; exact hΔWlt P hPT
      simp only [Nat.cast_zero, sub_zero, neg_eq_zero]
      exact Int.floor_eq_zero_iff.2 ⟨h0, h1⟩
  have hE0 : ∀ P, 0 ≤ E.coeff P := by
    intro P
    by_cases hPT : P = T
    · rw [hPT, hET]
    · rw [hEc, hTwc, if_neg hPT]
      have h1 := hΔWlt P hPT
      have : ⌊ΔW.coeff P - ((0 : ℤ) : ℚ)⌋ < 1 := Int.floor_lt.2 (by push_cast; linarith)
      push_cast at this ⊢
      omega
  set Θ₀ : QDivisor W := ΔW - Divisor.toQDivisor Tw + Divisor.toQDivisor E with hΘ₀
  have hΘc : ∀ P, Θ₀.coeff P = Int.fract (ΔW.coeff P - Tw.coeff P) := by
    intro P
    rw [hΘ₀, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
      Divisor.coeff_toQDivisor, hEc P, Int.fract]
    push_cast
    ring
  have hΘ0 : ∀ P, 0 ≤ Θ₀.coeff P := fun P => by rw [hΘc]; exact Int.fract_nonneg _
  have hΘ1 : ∀ P, Θ₀.coeff P < 1 := fun P => by rw [hΘc]; exact Int.fract_lt_one _
  -- the snc divisor `Ex(p) ∪ p⁻¹(Supp Δ)` and its components
  set Z : Closeds W := ⟨_, hsncW.1⟩ with hZ
  have hmemZ : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Q.genericPoint → Δ.coeff Q ≠ 0 → P.genericPoint ∈ (Z : Set W) := by
    intro P Q hQ hΔQ
    right
    change p P.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X))
    rw [Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨Q, Finsupp.mem_support_iff.2 hΔQ, ?_⟩
    rw [hQ]
    change Q.genericPoint ∈ (Q.support : Set X)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hmemZex : ∀ P : MMP.Mori.PrimeDivisor W, 2 ≤ Order.coheight (p P.genericPoint) →
      P.genericPoint ∈ (Z : Set W) := by
    intro P h2
    left
    intro hP
    rw [coheight_map_eq_of_isIso_restrict p (biregularLocus p) _
      (show p P.genericPoint ∈ _ from hP),
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  have hTZ : T.genericPoint ∈ (Z : Set W) := hmemZ T S hT (by rw [hΔS]; exact one_ne_zero)
  obtain ⟨s, hs, hsncs⟩ : ∃ s : Finset (MMP.Mori.PrimeDivisor W),
      (⋃ E ∈ s, (E.support : Set W)) = (Z : Set W) ∧
        DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
    rcases MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hsm (S := Z) hsncW with
      hbot | h'
    · exfalso
      have h' := hTZ
      rw [hbot] at h'
      exact h'
    · exact h'
  have hmems : ∀ P : MMP.Mori.PrimeDivisor W, P.genericPoint ∈ (Z : Set W) →
      P ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor W).support := by
    intro P hP
    rw [← hs] at hP
    obtain ⟨F, hFs, hF⟩ := Set.mem_iUnion₂.1 hP
    rw [← MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hF]
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hFs]
  -- every `ℚ`-divisor supported on `Θ₀ + Ex(p)` is snc
  have hsnc : ∀ G : QDivisor W, (∀ P, G.coeff P ≠ 0 → Θ₀.coeff P ≠ 0 ∨
      RationalMap.IsExceptional (X := W) p.toRationalMap P) →
        DivisorWithCoeffs.IsSNC (p ≫ sX) G := by
    intro G hG
    refine hsncs.of_support_subset fun P hP => hmems P ?_
    have hGP : G.coeff P ≠ 0 := Finsupp.mem_support_iff.1 hP
    rcases exists_map_genericPoint_eq_or_two_le_coheight p hbij.2 P with ⟨Q, hQ⟩ | h2
    · refine hmemZ P Q hQ fun hz => ?_
      rcases hG P hGP with hΘ | hE
      · apply hΘ
        by_cases hPT : P = T
        · subst hPT
          rw [hT] at hQ
          have hQS := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hQ
          subst hQS
          rw [hΔS] at hz
          exact absurd hz one_ne_zero
        · rw [hΘc, hΔWc P Q hQ, hz, hTwc, if_neg hPT]
          simp
      · rw [hexc, hQ, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hE
        exact absurd hE (by decide)
    · exact hmemZex P h2
  -- the vanishing `R¹p_* 𝒪_W(E - T) = 0`
  obtain ⟨hpb, -, -⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP p hWn hb hPW.2.1 hKW
    (Or.inl ⟨ω, hω0, hωK, rfl⟩) hΔW
  obtain ⟨m, hm, D, hD, hDc⟩ := hPW.2.2.exists_pos
  obtain ⟨DY, hDY, -, hB', hDYpb⟩ := hpb m hm D hD hDc
  have hCs := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp p ((-1 : ℤ) • D)
  have hCμ := hDYpb.zsmul hDc (-1) hCs
  have h1 : IsZero (((Scheme.Modules.pushforward p).rightDerived 1).obj
      (E - Finsupp.single T 1).divisorialSheaf) := by
    refine isZero_rightDerived_of_fractionalBoundary sX hQ p hWn hsm hproj hb hKW
      (E - Finsupp.single T 1) Θ₀ hΘ0 hΘ1 hsnc m hm _ (hDc.zsmul (-1)) hCs _ hCμ ?_ 1 one_pos
    rw [map_zsmul, hDY, hΘ₀, map_sub, ← hTw, neg_smul, one_smul, ← smul_neg]
    congr 1
    abel
  -- the strict transform as a scheme
  haveI := S.integral
  haveI := T.integral
  set μT := Scheme.IdealSheafData.subschemeMap T.idealSheaf S.idealSheaf p
    (le_map_idealSheaf p S T hT hTI) with hμTdef
  have hμT : μT ≫ S.idealSheaf.subschemeι = T.idealSheaf.subschemeι ≫ p :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  obtain ⟨-, hμTs⟩ := isProper_surjective_strictTransform p S T hT μT hμT
  haveI := hμTs
  haveI : IsDominant μT := inferInstance
  haveI hTsm : Smooth (T.idealSheaf.subschemeι ≫ p ≫ sX) := by
    have h := MMP.Fourfold.smooth_iSup_idealSheaf_of_isSNC (p ≫ sX) hsncs {T}
      (Finset.singleton_subset_iff.2 (hmems T hTZ))
    rwa [show (⨆ E ∈ ({T} : Finset (MMP.Mori.PrimeDivisor W)), E.idealSheaf) = T.idealSheaf by
      simp] at h
  haveI : LocallyOfFiniteType (T.idealSheaf.subschemeι ≫ p ≫ sX) := inferInstance
  haveI : IsLocallyNoetherian T.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (T.idealSheaf.subschemeι ≫ p ≫ sX)
  haveI : IsNormal T.idealSheaf.subscheme := isNormal_of_isRegular _
    (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme
      ((MMP.Mori.isSmoothScheme_iff _).2 hTsm))
  -- lifting sections from `T`, and normal Hartogs on `X`
  refine isNormal_subscheme_of_forall_exists_isRestrictionAlong S μT (E.restrictPrimeDivisor T)
    ?_ ?_
  · intro Q
    rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor E T hET Q, Finsupp.sum]
    exact Finset.sum_nonneg fun F _ => nsmul_nonneg (hE0 F) _
  · intro U y hy x hx
    obtain ⟨V, hxV, -, g, hg, hgy⟩ := exists_local_lift_of_isZero_rightDerived_one sX p S T μT hμT
      hT hET (hcart E) hV hSV hbij h1 U y hy x hx
    refine ⟨g, fun Γ hΓ => ?_, hgy⟩
    obtain ⟨Γ', hΓ', -⟩ := exists_primeDivisor_map_genericPoint_eq p hV Γ
      (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hb Γ)
    have hΓV : Γ.genericPoint ∈ V := by
      have hsp : Γ.genericPoint ⤳ S.idealSheaf.subschemeι x := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
        exact specializes_iff_mem_closure.mpr hΓ
      exact hsp.mem_open V.isOpen hxV
    have hmeet : (Γ'.support ∩ p ⁻¹ᵁ V).Nonempty := ⟨Γ'.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      show p Γ'.genericPoint ∈ V by rw [hΓ']; exact hΓV⟩
    have := hg.2 Γ' hmeet
    rwa [Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint p hbij.2 Γ' Γ hΓ',
      hEnex Γ' Γ hΓ', WithZero.exp_zero] at this

/-- The case `k = ℂ` (the setting of the source) of
`IsPltPair.isNormal_subscheme_of_isQFactorial_of_charZero`. -/
@[mmp "lem_mmp_projective_qfactorial_plt_floor_normal"]
public theorem IsPltPair.isNormal_subscheme_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hQ : Fourfold.IsQFactorial sX) (hX : IsProjectiveVariety ℂ sX)
    {S : PrimeDivisor X} {B : QDivisor X} (hB : B.IsEffective) (hB0 : B.roundDown = 0)
    (hBS : B.coeff S = 0) {n : ℕ} {K : Divisor X}
    (h : IsPltPair sX n K (Finsupp.single S 1 + B)) :
    IsNormal S.idealSheaf.subscheme := by
  apply IsPltPair.isNormal_subscheme_of_isQFactorial_of_charZero (k := ℂ) <;> assumption

end MMP.Mori

end
