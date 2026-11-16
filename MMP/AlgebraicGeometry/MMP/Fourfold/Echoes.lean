module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.SncResolution
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence
import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
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
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoWeightedMonomialValuation
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.SNCAffineLineExample
import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.MMP.Fourfold.SurfaceEchoLogDiscrepancy

/-!
# Echoes below log discrepancy two

Let `(Y, Θ)` be a terminal pair on a projective `ℚ`-factorial fourfold `Y`, and let
`S_1, …, S_m` be distinct prime divisors of `Y` (the labels) whose union contains the support of
`Θ`, so that `Θ = ∑_h b_h S_h` with `b_h ≥ 0`. Let `Y°` be the one-label smooth locus. Then all
but finitely many exceptional normalized divisorial valuations `ξ` over `Y` with
`a(ξ; Y, Θ) < 2` are echoes: of some order `j ≥ 1` of some label `S_h` at some irreducible
closed surface `V ⊆ S_h` whose generic point lies in `Y°`.

The argument splits according to the generic point `η` of the centre `c_Y(ξ)`.

* `η ∉ Y°`. Every point of `A = Y ∖ Y°` has coheight at least two. A resolution `π : W ⟶ Y`
  which principalizes the ideal of `A ∪ Supp Θ` carries the reduced snc divisor `T` with
  components those of `Ex(π) ∪ π⁻¹(A ∪ Supp Θ)`, and `(π, T)` is a log-smooth datum. The centre
  of `ξ` on `W` lies on a component of `π⁻¹(A)`, which is exceptional over `Y` and therefore has
  log discrepancy `> 1`. The log-smooth formula `a(ξ) = ∑ ξ(Tⱼ) aⱼ + e_T(ξ)` then forces
  `e_T(ξ) = 0` and bounds every `ξ(Tⱼ)`, and only finitely many valuations satisfy both.
* `η ∈ Y°`. On a smooth open neighbourhood `U ⊆ Y°` of `η` meeting at most one label `S`,
  `(𝟙_U, T)` is a log-smooth datum for `(U, Θ|_U)` whenever `T` is a reduced snc divisor
  containing `Supp Θ|_U`, and log discrepancies are local at the centre, so
  `a(ξ; Y, Θ) = a(ξ; U, Θ|_U)`. For `T = 0` or `T = S ∩ U`, the formula together with
  `e_T(ξ) ≥ codim c_Y(ξ) - |J(ξ)|` shows that a label passes through `η` and that the centre is
  a surface `V`. For `T = (S ∩ U) + {t = 0}`, where `(x, t)` is a regular system of parameters
  at `η_V` and `x` a local equation of `S`, the formula gives `ξ(t) = 1` and `e_T(ξ) = 0`. So `ξ`
  is monomial of weight `(j, 1)`, that is, the echo of order `j = ξ(x)` of `S` at `V`.

Three consequences follow. An echo has a surface as centre, of codimension two, so the
valuations with centre of codimension at least three are among the finitely many non-echoes. An
echo of order `j` of `S_h` at a surface `V` is unique and has log discrepancy `1 + j (1 - b_h)`,
where `b_h < 1` since the pair is klt; so at a fixed surface only finitely many valuations have
log discrepancy `< 2`. Finally, the surface centres of the non-echoes form a finite set `𝒮`, and
at every surface `V ∉ 𝒮` log discrepancy `< 2` forces an echo.

## Main results

* `MMP.Fourfold.IsKltTerminalPair.finite_setOf_not_isSurfaceEcho`: the exceptional valuations
  with log discrepancy `< 2` that are not echoes form a finite set.
* `MMP.Fourfold.IsKltTerminalPair.finite_setOf_three_le_codimension_centre`: the exceptional
  valuations with log discrepancy `< 2` and centre of codimension `≥ 3` form a finite set.
* `MMP.Fourfold.IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two`: the
  exceptional valuations with centre a fixed surface `V` and log discrepancy `< 2` form a finite
  set.
* `MMP.Fourfold.IsKltTerminalPair.exists_finset_forall_isSurfaceEcho`: outside a finite set of
  surfaces, every valuation with surface centre and log discrepancy `a < 2` is an echo of some
  order `j` of some label `S_h`, and `a = 1 + j (1 - b_h)`.

## Implementation notes

* The labels are a finite set `L` of prime divisors, so they are distinct, and
  `Supp Θ ⊆ ⋃_h S_h` reads `Θ.support ⊆ L`. Effectivity of `Θ` is part of
  `MMP.Fourfold.IsPair`, which `MMP.Fourfold.IsKltTerminalPair` contains; the coefficients
  `b_h` are `Θ.coeff S_h`, zero allowed.
* Valuations are Mathlib's multiplicative `Valuation k(Y) ℤᵐ⁰`. An exceptional normalized
  divisorial valuation is `MMP.Intersection.IsExceptionalValuation`, the centre is
  `MMP.Intersection.IsCentre`, and `a(ξ; Y, Θ) < 2` says that `ξ` has some log discrepancy
  `a < 2` (`MMP.Fourfold.HasLogDiscrepancy`). Echoes at a surface are
  `MMP.Fourfold.IsSurfaceEcho`, which carries `S_h ∈ L`, `V ⊆ S_h`, `dim V = 2`, `η_V ∈ Y°` and
  `j ≥ 1`. A surface is an irreducible closed subset of topological Krull dimension `2`.
* The base field is any field `k`; a pair (`MMP.Fourfold.IsPair`) forces `k` algebraically
  closed of characteristic zero, the source's `k = ℂ` being the case of interest.
* The source first deduces from `ℚ`-factoriality that `Y` is terminal and smooth in codimension
  two. The argument above needs neither: `Y ∖ Y°` has codimension at least two because `Y` is
  normal, and the exceptional components over it have log discrepancy `> 1` because the pair is
  terminal. Projectivity is not needed either, since resolutions with principalization exist
  over any variety in characteristic zero.
* The local datum `(𝟙_U, T)` requires `(U, Θ|_U)` to be klt. A divisor over `U` is a divisor
  over `Y`, which has a proper model (Nagata compactification followed by normalization), and its
  log discrepancy over `(U, Θ|_U)` is its log discrepancy over `(Y, Θ)`.
* The resolution with principalization is Kollár's: strong resolution, followed by marked
  order-one reduction of the inverse image of the ideal and then of the ideal of the
  exceptional locus.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [J. Kollár, *Lectures on resolution of singularities*], 3.26, 3.36
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori
open scoped WithZero

/-! ### Resolution with principalization of an ideal -/

section Principalization

open MMP.Resolution

/-! ### Varieties and blow-up sequences -/

/-- A variety is a disjoint union of varieties, with one component. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    IsDisjointUnionOfVarieties sX := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro C hC C' hC' hne
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
private theorem isVariety_toBase {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sX → Nonempty B.target →
        AlgebraicGeometry.IsVariety k (B.toBase ≫ sX)
  | X, .nil _, sX, hX, _ => by
    change AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | X, .cons Z B, sX, hX, hne => by
    haveI := hX
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      haveI := isEmpty_blowUp_bot X
      obtain ⟨y⟩ := hne
      exact isEmptyElim (B.toBase y)
    have h := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      sX Z hZ).1
    have := isVariety_toBase B _ h hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-! ### Isomorphisms over opens -/

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨((inv (g ∣_ V)) ⟨x, hx⟩).1, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- The biregular locus of a morphism from a smooth scheme lies in the smooth locus. -/
private theorem biregularLocus_le_smoothLocus {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hY : IsSmoothScheme (f ≫ sX)) : biregularLocus f ≤ smoothLocus sX := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hY
  haveI h : Smooth ((f ∣_ V) ≫ V.ι ≫ sX) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have e : V.ι ≫ sX = inv (f ∣_ V) ≫ ((f ∣_ V) ≫ V.ι ≫ sX) := by simp
  refine le_smoothLocus _ ?_
  rw [e]
  infer_instance

/-- In an irreducible scheme, an open `O` of `U` containing every point of `U` lying in a
nonempty open `V` has dense inclusion. -/
theorem isDominant_ι_of_forall_mem {Y : Scheme.{u}} [IrreducibleSpace Y] {U V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (O : U.toScheme.Opens) (hO : ∀ z, U.ι z ∈ V → z ∈ O) :
    IsDominant O.ι := by
  constructor
  have hpre : IsPreirreducible (U : Set Y) :=
    (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen
      (Set.subset_univ _)
  haveI : PreirreducibleSpace U.toScheme := Subtype.preirreducibleSpace hpre
  rcases isEmpty_or_nonempty U.toScheme with hE | hN
  · exact isEmptyElim
  obtain ⟨z₀⟩ := hN
  rw [DenseRange, Scheme.Opens.range_ι]
  refine O.isOpen.dense ?_
  obtain ⟨y₁, hy₁⟩ := hV
  obtain ⟨y, -, hyU, hyV⟩ := (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible _ _
    U.isOpen V.isOpen ⟨z₀.1, trivial, z₀.2⟩ ⟨y₁, trivial, hy₁⟩
  exact ⟨⟨y, hyU⟩, hO _ hyV⟩

/-- **Composing on the source does not enlarge the biregular locus.** Let `g : Y₂ ⟶ X` be
separated, with `Y₂` reduced and irreducible and `g` an isomorphism over an open with nonempty
inverse image. If `h ≫ g` is an isomorphism over `W`, so is `g`. -/
private theorem biregularLocus_comp_le {X Y Y₂ : Scheme.{u}} (h : Y ⟶ Y₂) (g : Y₂ ⟶ X)
    [IsSeparated g] [IsReduced Y₂] [IrreducibleSpace Y₂]
    (hne : ((g ⁻¹ᵁ biregularLocus g : Y₂.Opens) : Set Y₂).Nonempty) :
    biregularLocus (h ≫ g) ≤ biregularLocus g := by
  set W := biregularLocus (h ≫ g) with hWdef
  have hW : IsIso ((h ≫ g) ∣_ W) := isBiregular_biregularLocus _
  refine le_biregularLocus (show IsIso (g ∣_ W) from ?_)
  rw [morphismRestrict_comp] at hW
  set a := h ∣_ g ⁻¹ᵁ W with ha
  set b := g ∣_ W with hb
  haveI : IsIso (a ≫ b) := hW
  set s := inv (a ≫ b) ≫ a with hs
  have hsb : s ≫ b = 𝟙 _ := by rw [hs, Category.assoc, IsIso.inv_hom_id]
  set W' : W.toScheme.Opens := W.ι ⁻¹ᵁ biregularLocus g with hW'
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  haveI : IsIso (g ∣_ W.ι ''ᵁ W') := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g
    (V := biregularLocus g) (by rintro _ ⟨y, hy, rfl⟩; exact hy)
  haveI hc : IsIso (b ∣_ W') := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W W')).2 (inferInstanceAs (IsIso (g ∣_ W.ι ''ᵁ W')))
  haveI : IsSeparated b := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› W
  set ι := (b ⁻¹ᵁ W').ι with hι
  have hbase : ∀ z : (g ⁻¹ᵁ W).toScheme, W.ι (b z) = g ((g ⁻¹ᵁ W).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hb, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : IsDominant ι := isDominant_ι_of_forall_mem hne _ fun z hz => by
    change W.ι (b z) ∈ biregularLocus g
    rwa [hbase z]
  have hbs : b ≫ s = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated b
      (by rw [Category.assoc, hsb, Category.comp_id, Category.id_comp]) ι ?_
    have hrange : Set.range (ι ≫ b ≫ s) ⊆ Set.range ι := by
      rintro _ ⟨z, rfl⟩
      rw [hι, Scheme.Opens.range_ι]
      show b ((ι ≫ b ≫ s) z) ∈ W'
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hsb, Category.comp_id]
      exact z.2
    set m := IsOpenImmersion.lift ι (ι ≫ b ≫ s) hrange with hmdef
    have hm : m ≫ ι = ι ≫ b ≫ s := IsOpenImmersion.lift_fac _ _ _
    have key : ι ≫ b = (b ∣_ W') ≫ W'.ι := (morphismRestrict_ι b W').symm
    have h1 : m ≫ (b ∣_ W') = b ∣_ W' := by
      rw [← cancel_mono W'.ι, Category.assoc, ← key, ← Category.assoc, hm, Category.assoc,
        Category.assoc, hsb, Category.comp_id]
    have h2 : m = 𝟙 _ := by rw [← cancel_mono (b ∣_ W'), h1, Category.id_comp]
    rw [← hm, h2, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hbs, hsb⟩⟩

/-! ### Marked order-one reduction -/

/-- The cosupport of a marked ideal of marking one lies in the support of the ideal. -/
private theorem cosupport_one_subset {X : Scheme.{u}} (I : X.IdealSheafData) :
    MarkedIdeal.cosupport ⟨I, 1⟩ ⊆ (I.support : Set X) := by
  intro x hx
  change ((1 : ℕ) : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I x) at hx
  by_contra h
  rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 h] at hx
  have h0 : idealOrder (⊤ : Ideal (X.presheaf.stalk x)) ≤ 0 := by
    unfold idealOrder
    refine iSup₂_le fun j hj => ?_
    rcases j with _ | j
    · simp
    · exact absurd (top_le_iff.1 (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j))))
        (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  exact absurd (hx.trans h0) (by norm_num)

/-- The centre of a blow-up along which `ord I ≥ m` lies in the cosupport of `(I, m)`. -/
private theorem support_subset_cosupport' {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (I : X.IdealSheafData) (m : ℕ)
    (ha : OrderAlongGE I (Z.support : Set X) m) :
    (Z.support : Set X) ⊆ MarkedIdeal.cosupport ⟨I, m⟩ := by
  intro x hx
  change (m : ℕ∞) ≤ idealOrder (IdealSheafData.stalk I x)
  refine (natCast_le_idealOrder_iff' _ _).2 <|
    (stalk_le_pow_of_orderAlongGE s hX Z hZ I m ha _).trans (Ideal.pow_right_mono ?_ _)
  exact IsLocalRing.le_maximalIdeal ((IdealSheafData.stalk_eq_top_iff_notMem_support _ _).not.2
    (not_not.2 hx))

/-- The cosupport of the first birational transform along a smooth blow-up sequence of order
`≥ m` lies over the cosupport of the marked ideal. -/
private theorem cosupport_birationalTransform_subset' {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z))
    (hB : (ClosedBlowupSequence.cons Z B).IsOrderGeMarkedTripleSeq s a E) :
    (a.birationalTransform Z).cosupport ⊆ blowUpToBase Z ⁻¹' a.cosupport := by
  have h := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E
    (.cons Z B) hB 1
  cases B <;> exact fun y hy => by
    have h' := h hy
    simp only [ClosedBlowupSequence.toBase, Set.mem_preimage, Scheme.Hom.comp_apply] at h'
    exact h'

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, the final
boundary lies over `Supp E ∪ cosupp(I, m)`. -/
private theorem support_orderedTotalTransform_subset {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      (B.orderedTotalTransform E).support ⊆ B.toBase ⁻¹' (E.support ∪ a.cosupport) := by
  intro X B
  induction B with
  | nil X =>
    intro s a E _ x hx
    exact Or.inl hx
  | @cons X Z B ih =>
    intro s a E hB x hx
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := id hB
    have hcos := cosupport_birationalTransform_subset' s a E Z B hB
    have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
    rcases ih _ _ _ hB'' hx with h | h
    · rw [OrderedDivisor.support_totalTransform E (fun i => (hT.2.2.2.2.2.2.2.1 i).2.1) Z] at h
      rcases h with h | h
      · have h' : closure (blowUpToBase Z ⁻¹' (E.support \ (Z.support : Set X))) ⊆
            blowUpToBase Z ⁻¹' E.support := closure_minimal
          (Set.preimage_mono Set.diff_subset) (hEc.preimage (blowUpToBase Z).continuous)
        exact Or.inl (h' h)
      · exact Or.inr (support_subset_cosupport' s hT.2.1 Z hZ a.I a.m hord h)
    · exact Or.inr (hcos h)

/-- A smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)` is an isomorphism over
every open missing `cosupp(I, m)`. -/
private theorem isIso_restrict_of_disjoint_cosupport {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E → ∀ W : X.Opens,
      Disjoint a.cosupport (W : Set X) → IsIso (B.toBase ∣_ W) := by
  intro X B
  induction B with
  | nil X =>
    intro s a E _ W _
    change IsIso (𝟙 X ∣_ W)
    infer_instance
  | @cons X Z B ih =>
    intro s a E hB W hW
    obtain ⟨hT, hZ, -, -, hord, hB''⟩ := id hB
    have hZW : (W : Set X) ⊆ (Z.support : Set X)ᶜ := fun x hxW hxZ =>
      hW.notMem_of_mem_right hxW (support_subset_cosupport' s hT.2.1 Z hZ a.I a.m hord hxZ)
    haveI : IsIso (blowUpToBase Z ∣_ W) :=
      isIso_blowUpToBase_restrict_of_subset_compl_support Z W hZW
    have hcos := cosupport_birationalTransform_subset' s a E Z B hB
    haveI : IsIso (B.toBase ∣_ blowUpToBase Z ⁻¹ᵁ W) := ih _ _ _ hB'' _
      (Set.disjoint_left.2 fun y hy hyW => hW.notMem_of_mem_right hyW (hcos hy))
    exact isIso_restrict_comp B.toBase (blowUpToBase Z) W

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

/-- On a smooth scheme with an snc divisor `F`, an ideal sheaf whose support lies in `Supp F`
has no zero stalk. -/
private theorem stalk_ne_bot_of_support_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (F : OrderedDivisor X) (hF : F.IsSNC sX) (K : X.IdealSheafData)
    (hK : (K.support : Set X) ⊆ F.support) (x : X) : IdealSheafData.stalk K x ≠ ⊥ := by
  have := Aux.smooth_of_isSmoothScheme' sX h
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  intro h0
  let p₀ : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : X.fromSpecStalk x p₀ ∈ (K.support : Set X) :=
    (fromSpecStalk_mem_support_iff_stalk_le K x p₀).2 h0.le
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hK hξ)
  have hxj : x ∈ ((F.E j).support : Set X) :=
    (fromSpecStalk_specializes_self x p₀).mem_closed (F.E j).support.isClosed hj
  have hle := (fromSpecStalk_mem_support_iff_stalk_le _ x p₀).1 hj
  obtain ⟨n, z, c, hz, hc, -⟩ := hF.2 x
  rw [hc ⟨j, hxj⟩] at hle
  exact (prime_of_isRegularSystemOfParameters hz (c ⟨j, hxj⟩)).ne_zero
    (Ideal.mem_bot.1 (hle (Ideal.mem_span_singleton_self _)))

/-- On a smooth scheme with an snc divisor `F`, an ideal sheaf with principal stalks whose
support lies in `Supp F` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_of_support_subset {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (h : MMP.Mori.IsSmoothScheme sX) (F : OrderedDivisor X) (hF : F.IsSNC sX)
    (K : X.IdealSheafData) (hK : (K.support : Set X) ⊆ F.support)
    (hprin : ∀ x, ∃ g, IdealSheafData.stalk K x = Ideal.span {g}) :
    Stacks.Divisors.IsEffectiveCartierDivisor K := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := Aux.smooth_of_isSmoothScheme' sX h
  refine isEffectiveCartierDivisor_of_stalk_regular_principal K fun x _ => ?_
  obtain ⟨g, hg⟩ := hprin x
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hne := stalk_ne_bot_of_support_subset sX h F hF K hK x
  have hg0 : g ≠ 0 := fun h0 => hne (by rw [hg, h0, Ideal.span_singleton_eq_bot])
  exact ⟨g, IsRegular.of_ne_zero hg0, hg⟩

/-! ### Ordered snc divisors from snc closed subsets -/

/-- An empty family on a smooth scheme over a field is an snc family. -/
private theorem isSNCFamily_of_isEmpty {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hsm : IsSmoothScheme sX) {ι : Type*}
    [IsEmpty ι] (E : ι → X.IdealSheafData) : IsSNCFamily sX E := by
  have := Aux.smooth_of_isSmoothScheme' sX hsm
  refine ⟨isEmptyElim, fun x => ?_⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field sX x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  exact ⟨n, z, fun i => isEmptyElim i.1, hz, fun i => isEmptyElim i.1,
    fun i => isEmptyElim i.1⟩

/-- The irreducible components of a divisor with simple normal crossings, in some order, form an
ordered snc divisor with support the divisor. -/
private theorem exists_isOrderedSNC_support_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [CompactSpace X]
    (hsm : IsSmoothScheme sX) {D : Set X} (hD : IsSNCClosedSubset sX D) :
    ∃ E : OrderedDivisor X, E.IsOrderedSNC sX ∧ E.support = D := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : AlgebraicGeometry.IsNoetherian X := {}
  obtain ⟨hcl, hD⟩ := hD
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hcl
  have hfam : IsSNCFamily sX (componentsFamily D) := by
    rcases hD with rfl | ⟨-, -, h⟩
    · have : IsEmpty (componentsOf (∅ : Set X)) :=
        ⟨fun W => W.2.1.1.nonempty.ne_empty (Set.subset_empty_iff.1 W.2.1.2)⟩
      exact isSNCFamily_of_isEmpty sX hsm _
    · exact h
  have : Fintype (componentsOf D) := hfin.fintype
  let e := Fintype.equivFin (componentsOf D)
  have hfam' : IsSNCFamily sX (componentsFamily D ∘ e.symm) :=
    MMP.Resolution.Internal.TupleRestrictionLift.isSNCFamily_comp hfam _ e.symm.injective
  refine ⟨⟨Fintype.card (componentsOf D), componentsFamily D ∘ e.symm⟩, ⟨fun i => ⟨(hfam'.1 i).1,
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ fun y hy => ?_⟩, hfam'⟩, ?_⟩
  · obtain ⟨n, z, c, hz, hc, -⟩ := hfam'.2 y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      change ((componentsFamily D (e.symm i)).support : Set X) ⊆ D
      rw [coe_support_componentsFamily hcl]
      exact (e.symm i).2.1.2
    · intro x hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
      refine Set.mem_iUnion.2 ⟨e ⟨W, hW⟩, ?_⟩
      change x ∈ ((componentsFamily D (e.symm (e ⟨W, hW⟩))).support : Set X)
      rw [Equiv.symm_apply_apply, coe_support_componentsFamily hcl]
      exact hxW

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Marked triples -/

/-- A nonempty scheme of finite type over a field has finite dimension. -/
private theorem hasDimensionIn_univ {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY] [Nonempty Y] :
    HasDimensionIn Y Set.univ := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
  obtain ⟨x⟩ : Nonempty Y := inferInstance
  have : Nonempty (TopologicalSpace.IrreducibleCloseds Y) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim Y ≠ ⊥ := Order.krullDim_ne_bot_iff.2 inferInstance
  generalize hd : topologicalKrullDim Y = d at htop hbot
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => exact ⟨n, trivial, hd⟩

/-- On an integral scheme, an ideal sheaf whose support misses the generic point is nonzero at
the generic points. -/
private theorem isNonzeroAtGenericPoints_of_genericPoint_notMem {Y : Scheme.{u}} [IsIntegral Y]
    (K : Y.IdealSheafData) (h : genericPoint Y ∉ K.support) : IsNonzeroAtGenericPoints K := by
  intro η hη
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hη
  have hηgen : η = genericPoint Y := (show IsGenericPoint η ⊤ from hη).eq (genericPoint_spec _)
  rw [hηgen, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 h]
  exact top_ne_bot

/-- On an irreducible scheme, the generic point lies over every open over which a morphism is
an isomorphism, when that open is nonempty. -/
private theorem genericPoint_mem_preimage {X Y : Scheme.{u}} [IrreducibleSpace Y] (g : Y ⟶ X)
    (V : X.Opens) [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) :
    genericPoint Y ∈ g ⁻¹ᵁ V :=
  ((genericPoint_spec Y).mem_open_set_iff (g ⁻¹ᵁ V).isOpen).2
    (by simpa using nonempty_preimage_of_isIso_restrict g V hV)

/-- **Resolution and principalization.** Let `X` be a variety over a field `k` of characteristic
zero and `I ≠ 0` an ideal sheaf on `X`. There is a resolution `f : Y ⟶ X` (projective
in the sense of EGA, birational, `Y` a smooth variety) which is an isomorphism over
`X_sm ∖ V(I)`, such that `I 𝒪_Y` is an effective Cartier divisor, `Ex(f) ∪ Supp(I 𝒪_Y)` is an
snc divisor, and `Ex(f)` is empty
or of pure codimension one. -/
private theorem exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : AlgebraicGeometry.IsVariety k sX) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧
      AlgebraicGeometry.IsProjective f ∧ IsBirationalMorphism f ∧ IsSmoothScheme (f ≫ sX) ∧
      IsIso (f ∣_ (smoothLocus sX ⊓ I.support.compl)) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) ∧
      IsSNCSubset (f ≫ sX) (exceptionalSet f ⊔ (I.comap f).support) ∧
      IsPureCodimOne (exceptionalSet f) := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  /- Step 1: strong resolution `p : X₁ ⟶ X`. -/
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety sX hX
  obtain ⟨hsm₁, hiso₁, hsnc₁⟩ := hBR sX hDU
  set B₁ := BR sX hDU with hB₁
  set p := B₁.toBase with hp
  haveI := hiso₁
  have hsmne : ((smoothLocus sX : X.Opens) : Set X).Nonempty := by
    rw [smoothLocus_eq_smoothLocus]
    exact (Scheme.Hom.dense_smoothLocus_of_perfectField sX).nonempty
  set U₀ : X.Opens := smoothLocus sX ⊓ I.support.compl with hU₀
  have hgenI : genericPoint X ∉ (I.support : Set X) := by
    intro h
    refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (eq_top_iff.mpr fun x _ => ?_))
    exact ((genericPoint_spec X).mem_closed_set_iff I.support.isClosed).mp h (Set.mem_univ x)
  have hU₀ne : (U₀ : Set X).Nonempty := ⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff (smoothLocus sX).isOpen).2 (by simpa using hsmne),
    hgenI⟩
  haveI : IsIso (p ∣_ U₀) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le p inf_le_left
  have hX₁ : AlgebraicGeometry.IsVariety k (p ≫ sX) := isVariety_toBase B₁ sX hX
    (let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict p U₀ hU₀ne; ⟨y⟩)
  haveI := hX₁
  haveI : IsIntegral B₁.target := hX₁.toIsIntegral
  haveI : IsLocallyNoetherian B₁.target := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace B₁.target := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₁.target := {}
  /- Step 2: the components of `p⁻¹(Sing X)`, and order-one reduction of `I 𝒪_{X₁}`. -/
  obtain ⟨E, hE, hEsupp⟩ := exists_isOrderedSNC_support_eq (p ≫ sX) hsm₁ hsnc₁
  set J : B₁.target.IdealSheafData := I.comap p with hJ
  have hJsupp : (J.support : Set B₁.target) = p ⁻¹' (I.support : Set X) := by
    rw [hJ, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hgenJ : genericPoint B₁.target ∉ J.support := by
    intro h
    have h' : genericPoint B₁.target ∈ (J.support : Set B₁.target) := h
    rw [hJsupp] at h'
    exact (genericPoint_mem_preimage p U₀ hU₀ne).2 h'
  obtain ⟨F, -, hFR⟩ := exists_isOrderReductionFunctorMarked_bmoFamily.{u} 1 le_rfl
  let t₁ : MarkedTriple.{u} := ⟨⟨⟨B₁.target, J, E⟩, k, p ≫ sX⟩, 1⟩
  have ht₁ : t₁ ∈ markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hsm₁, (inferInstance : LocallyOfFiniteType (p ≫ sX)),
      (inferInstance : QuasiCompact (p ≫ sX)),
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      isNonzeroAtGenericPoints_of_genericPoint_notMem J hgenJ, hE⟩, rfl,
      hasDimensionIn_univ (p ≫ sX)⟩
  set B₂ : ClosedBlowupSequence B₁.target := F.toFun t₁ ht₁ with hB₂def
  have hB₂ : B₂.IsOrderGeMarkedTripleSeq (p ≫ sX) ⟨J, 1⟩ E := F.isOrderGeMarkedTripleSeq t₁ ht₁
  have hmax₂ : maxOrder (B₂.markedTransform ⟨J, 1⟩).I < 1 := hFR.1 t₁ ht₁
  have hexc₂ : J.comap B₂.toBase = B₂.exceptionalIdeal := by
    rw [ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal B₂ _
      ⟨J, 1⟩ E rfl hB₂, eq_top_of_maxOrder_lt_one hmax₂,
      ← Scheme.IdealSheafData.one_eq_top, one_mul]
  haveI : IsIso (B₂.toBase ∣_ p ⁻¹ᵁ U₀) :=
    isIso_restrict_of_disjoint_cosupport B₂ _ _ _ hB₂ _ (Set.disjoint_left.2 fun y hy hyU => by
      have h := cosupport_one_subset J hy
      rw [hJsupp] at h
      exact hyU.2 h)
  set g : B₂.target ⟶ X := B₂.toBase ≫ p with hg
  haveI hgU₀ : IsIso (g ∣_ U₀) := isIso_restrict_comp B₂.toBase p U₀
  obtain ⟨-, hsm₂, -, -, -, -, hE₂⟩ :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B₂ _ _ _ hB₂
  have hgs : g ≫ sX = B₂.toBase ≫ p ≫ sX := Category.assoc _ _ _
  have hX₂ : AlgebraicGeometry.IsVariety k (g ≫ sX) := by
    rw [hgs]
    exact isVariety_toBase B₂ _ hX₁
      (let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict g U₀ hU₀ne; ⟨y⟩)
  haveI := hX₂
  haveI : IsIntegral B₂.target := hX₂.toIsIntegral
  haveI : IsLocallyNoetherian B₂.target := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : CompactSpace B₂.target := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₂.target := {}
  have hgproj : AlgebraicGeometry.IsProjective g :=
    (ClosedBlowupSequence.isProjective_toBase B₂).comp
      (ClosedBlowupSequence.isProjective_toBase B₁)
  haveI : IsProper g := hgproj.isProper
  /- Step 3: order-one reduction of the ideal of the non-biregular locus of `g`. -/
  set V : X.Opens := biregularLocus g with hV
  haveI : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  have hU₀V : U₀ ≤ V := le_biregularLocus hgU₀
  have hVne : (V : Set X).Nonempty := hU₀ne.mono hU₀V
  set Z' : Closeds X := V.compl with hZ'
  set I₃ : B₂.target.IdealSheafData := (Scheme.IdealSheafData.vanishingIdeal Z').comap g with hI₃
  have hI₃supp : (I₃.support : Set B₂.target) = g ⁻¹' (Z' : Set X) := by
    rw [hI₃, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hgenI₃ : genericPoint B₂.target ∉ I₃.support := by
    intro h
    have h' : genericPoint B₂.target ∈ (I₃.support : Set B₂.target) := h
    rw [hI₃supp] at h'
    exact h' (genericPoint_mem_preimage g V hVne)
  set E₂ := B₂.orderedTotalTransform E with hE₂def
  let t₂ : MarkedTriple.{u} := ⟨⟨⟨B₂.target, I₃, E₂⟩, k, B₂.toBase ≫ p ≫ sX⟩, 1⟩
  have ht₂ : t₂ ∈ markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hsm₂, (hgs ▸ inferInstance : LocallyOfFiniteType (B₂.toBase ≫ p ≫ sX)),
      (hgs ▸ inferInstance : QuasiCompact (B₂.toBase ≫ p ≫ sX)),
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      isNonzeroAtGenericPoints_of_genericPoint_notMem I₃ hgenI₃, hE₂⟩, rfl,
      hasDimensionIn_univ (g ≫ sX)⟩
  set B₃ : ClosedBlowupSequence B₂.target := F.toFun t₂ ht₂ with hB₃def
  have hB₃ : B₃.IsOrderGeMarkedTripleSeq (B₂.toBase ≫ p ≫ sX) ⟨I₃, 1⟩ E₂ :=
    F.isOrderGeMarkedTripleSeq t₂ ht₂
  have hmax₃ : maxOrder (B₃.markedTransform ⟨I₃, 1⟩).I < 1 := hFR.1 t₂ ht₂
  have hexc₃ : I₃.comap B₃.toBase = B₃.exceptionalIdeal := by
    rw [ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal B₃ _
      ⟨I₃, 1⟩ E₂ rfl hB₃, eq_top_of_maxOrder_lt_one hmax₃,
      ← Scheme.IdealSheafData.one_eq_top, one_mul]
  haveI : IsIso (B₃.toBase ∣_ g ⁻¹ᵁ V) :=
    isIso_restrict_of_disjoint_cosupport B₃ _ _ _ hB₃ _ (Set.disjoint_left.2 fun y hy hyV => by
      have h := cosupport_one_subset I₃ hy
      rw [hI₃supp] at h
      exact h hyV)
  set f : B₃.target ⟶ X := B₃.toBase ≫ g with hf
  haveI hfV : IsIso (f ∣_ V) := isIso_restrict_comp B₃.toBase g V
  haveI : IsIso (f ∣_ U₀) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le f hU₀V
  obtain ⟨-, hsm₃, -, -, -, -, hE₃⟩ :=
    ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq B₃ _ _ _ hB₃
  have hfs : f ≫ sX = B₃.toBase ≫ B₂.toBase ≫ p ≫ sX := by
    rw [hf, hg]; simp only [Category.assoc]
  rw [← hfs] at hsm₃ hE₃
  have hY : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rw [hf, Category.assoc]
    exact isVariety_toBase B₃ _ hX₂
      (let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict f U₀ hU₀ne; ⟨y⟩)
  haveI := hY
  haveI : IsIntegral B₃.target := hY.toIsIntegral
  haveI : IsLocallyNoetherian B₃.target := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : CompactSpace B₃.target := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₃.target := {}
  /- The biregular loci of `f` and `g` agree, so `Ex(f) = f⁻¹(Z')`. -/
  have hVf : biregularLocus f = V := le_antisymm
    (biregularLocus_comp_le B₃.toBase g (nonempty_preimage_of_isIso_restrict g V hVne))
    (le_biregularLocus hfV)
  have hEx : (exceptionalSet f : Set B₃.target) = f ⁻¹' (Z' : Set X) := by
    ext y
    change f y ∉ biregularLocus f ↔ f y ∉ V
    rw [hVf]
  have hexcsupp : (B₃.exceptionalIdeal.support : Set B₃.target) = f ⁻¹' (Z' : Set X) := by
    rw [← hexc₃, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI₃supp]
    rfl
  set E₃ := B₃.orderedTotalTransform E₂ with hE₃def
  have hIf : I.comap f = B₂.exceptionalIdeal.comap B₃.toBase := by
    rw [hf, hg, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hJ, hexc₂]
  have hIfsupp : ((I.comap f).support : Set B₃.target) = f ⁻¹' (I.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hsing : f ⁻¹' (singularLocus sX : Set X) ⊆ exceptionalSet f := fun y hy hyV =>
    hy (biregularLocus_le_smoothLocus sX f hsm₃ hyV)
  /- `Ex(f) ∪ Supp(I 𝒪_Y)` is the support of the final boundary. -/
  have hS : (exceptionalSet f : Set B₃.target) ∪ ((I.comap f).support : Set B₃.target) =
      E₃.support := by
    apply Set.Subset.antisymm
    · rintro y (hy | hy)
      · rw [hEx, ← hexcsupp] at hy
        exact ClosedBlowupSequence.support_exceptionalIdeal_subset B₃ _ _ _ hB₃ hy
      · rw [hIf, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at hy
        exact ClosedBlowupSequence.preimage_support_subset_support_orderedTotalTransform
          B₃ _ _ _ hB₃ (ClosedBlowupSequence.support_exceptionalIdeal_subset B₂ _ _ _ hB₂ hy)
    · intro y hy
      rcases support_orderedTotalTransform_subset B₃ _ _ _ hB₃ hy with h | h
      · rcases support_orderedTotalTransform_subset B₂ _ _ _ hB₂ h with h' | h'
        · left
          rw [hEsupp] at h'
          exact hsing h'
        · right
          have h'' := cosupport_one_subset J h'
          rw [hJsupp] at h''
          rw [hIfsupp]
          exact h''
      · left
        have h' := cosupport_one_subset I₃ h
        rw [hI₃supp] at h'
        rw [hEx]
        exact h'
  have hcart : ∀ K : B₃.target.IdealSheafData, (K.support : Set B₃.target) ⊆ E₃.support →
      (∀ y, ∃ a, IdealSheafData.stalk K y = Ideal.span {a}) →
      Stacks.Divisors.IsEffectiveCartierDivisor K := fun K hK hprin =>
    isEffectiveCartierDivisor_of_support_subset (f ≫ sX) hsm₃ E₃ hE₃.2 K hK hprin
  refine ⟨B₃.target, f, hY, (ClosedBlowupSequence.isProjective_toBase B₃).comp hgproj,
    isBirationalMorphism_of_isIso_restrict f U₀ hU₀ne, hsm₃, inferInstance, ?_, ?_, ?_⟩
  · -- `I 𝒪_Y` is an effective Cartier divisor
    refine hcart _ (fun y hy => hS ▸ Or.inr hy) fun y => ?_
    rw [hIf]
    obtain ⟨a, ha⟩ := ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B₂ (B₃.toBase y)
    refine ⟨(B₃.toBase.stalkMap y).hom a, ?_⟩
    rw [IdealSheafData.stalk_comap, ha, Ideal.map_span, Set.image_singleton]
  · -- simple normal crossings
    refine isSNCSubset_of_isSNCClosedSubset (f ≫ sX) ?_
    rw [Closeds.coe_sup, hS]
    exact hE₃.2.isSNCClosedSubset_iUnion
  · -- pure codimension one
    have hexcart := hcart B₃.exceptionalIdeal
      (ClosedBlowupSequence.support_exceptionalIdeal_subset B₃ _ _ _ hB₃)
      (ClosedBlowupSequence.exists_stalk_exceptionalIdeal_eq_span B₃)
    rw [show exceptionalSet f = B₃.exceptionalIdeal.support from
      Closeds.ext (hEx.trans hexcsupp.symm)]
    exact isPureCodimOne_support_of_isEffectiveCartierDivisor (f ≫ sX) hexcart

end Principalization

/-! ### Prime divisors and closed sets of pure codimension one -/

/-- The support of a prime divisor, as an irreducible closed subset. -/
private def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]
  rfl

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{u}} {P Q : MMP.Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- An irreducible closed subset of codimension one contained in the union of the supports of
finitely many prime divisors is the support of one of them. -/
private theorem exists_mem_support_eq {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)} (W : IrreducibleCloseds X)
    (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) (hW1 : codimension W = 1) :
    ∃ E ∈ s, (E.support : Set X) = W := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]
      exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  have hWE : W ≤ primeIrr E := fun x hx ↦ by
    change x ∈ (primeIrr E : Set X)
    rw [coe_primeIrr]
    exact hWz hx
  have hWE' : W = primeIrr E := by
    by_contra hne
    have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
    have := Order.coheight_add_one_le hlt
    rw [← codimension_eq_coheight, ← codimension_eq_coheight,
      show codimension (primeIrr E) = 1 from E.codimension_one, hW1] at this
    exact absurd this (by decide)
  exact ⟨E, hE, by rw [← coe_primeIrr, ← hWE']⟩

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by
    rwa [← this]
  exact subset_closure ⟨_, this, rfl⟩

/-- **Points of an effective Cartier divisor inside an snc subset lie on its components.** -/
private theorem exists_primeDivisor_subset_support_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] {S : Closeds Y} (hS : IsSNCSubset sY S)
    {D : Y.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDS : (D.support : Set Y) ⊆ S) {y : Y} (hy : y ∈ (D.support : Set Y)) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ D.support ∧ y ∈ P.support := by
  obtain ⟨W, hWmax, hyW⟩ := exists_maximal_ge D.support.isClosed
    (IrreducibleCloseds.closureSingleton y)
    (closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed)
  have hyW' : y ∈ (W : Set Y) := hyW (subset_closure rfl)
  rcases hS with rfl | ⟨s, hs, -⟩
  · exact absurd (hDS (hWmax.1 hyW')) (by simp)
  · obtain ⟨E, -, hEW⟩ := exists_mem_support_eq W (hs ▸ hWmax.1.trans hDS)
      (isPureCodimOne_support_of_isEffectiveCartierDivisor sY hD W hWmax)
    exact ⟨E, hEW ▸ hWmax.1, hEW ▸ hyW'⟩

/-- A prime divisor whose support lies in a finite union of supports of prime divisors is one
of them. -/
private theorem mem_of_support_subset {X : Scheme.{u}} {s : Finset (MMP.Mori.PrimeDivisor X)}
    {P : MMP.Mori.PrimeDivisor X} (hP : (P.support : Set X) ⊆ ⋃ E ∈ s, E.support) : P ∈ s := by
  obtain ⟨E, hE, hEP⟩ := exists_mem_support_eq (s := s) (primeIrr P)
    (by rw [coe_primeIrr]; exact hP) P.codimension_one
  rw [coe_primeIrr] at hEP
  rwa [← primeDivisor_eq_of_support_eq hEP]

/-! ### The support of the crepant boundary -/

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The strict-transform part of the crepant boundary.** -/
private theorem exists_coeff_eq_of_not_isExceptional (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨P, neg_injective ((hΔY G).eq hd), hη⟩

/-- **The support of the crepant boundary.** Every prime divisor in the support of the crepant
boundary `Δ_Y` is `f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f G.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hη⟩ := exists_coeff_eq_of_not_isExceptional hP hY hf hΔY hGe
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc,
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-! ### The one-label smooth locus -/

section OneLabel

variable {Y : Scheme.{u}}

/-- The one-label smooth locus is open. -/
private theorem isOpen_oneLabelSmoothLocus {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (L : Finset (MMP.Mori.PrimeDivisor Y)) : IsOpen (oneLabelSmoothLocus L) := by
  refine (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType sY).sdiff
    (IsClosed.union ?_ ?_)
  · refine isClosed_biUnion_finset fun S _ => ?_
    refine S.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ ?_
    exact (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType
      (S.idealSheaf.subschemeι ≫ sY)).isClosed_compl
  · refine isClosed_biUnion_finset fun S _ => isClosed_biUnion_finset fun S' _ => ?_
    exact isClosed_iUnion_of_finite fun _ => S.idealSheaf.support.isClosed.inter
      S'.idealSheaf.support.isClosed

/-- A point of coheight at most one on the support of a prime divisor is its generic point. -/
private theorem eq_genericPoint_of_coheight_le_one (P : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : Order.coheight y ≤ 1) (hyP : y ∈ P.support) : y = P.genericPoint := by
  have h := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hyP
  by_contra hne
  have hlt : y < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.2 h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.1 h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at this
  exact absurd (this.trans hy) (by decide)

/-- **Points of coheight at most one lie in the one-label smooth locus** of a normal locally
Noetherian scheme: the local ring is a field or a discrete valuation ring, and such a point lies
on at most one label, as its generic point. -/
private theorem mem_oneLabelSmoothLocus_of_coheight_le_one [IsLocallyNoetherian Y] [IsNormal Y]
    (L : Finset (MMP.Mori.PrimeDivisor Y)) {y : Y} (hy : Order.coheight y ≤ 1) :
    y ∈ oneLabelSmoothLocus L := by
  refine mem_oneLabelSmoothLocus_iff.2 ⟨?_, fun S _ hS => ?_,
    fun S _ S' _ hne ⟨hS, hS'⟩ => hne ?_⟩
  · rcases (show Order.coheight y = 0 ∨ Order.coheight y = 1 by
      obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (hy.trans_lt (by decide)).ne
      rw [← hc] at hy ⊢
      have : c ≤ 1 := by exact_mod_cast hy
      interval_cases c <;> simp) with h0 | h1
    · exact MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero h0
    · have hPg := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1
      have hP : IsDiscreteValuationRing (Y.presheaf.stalk
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1).genericPoint) :=
        MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing _
      rw [hPg] at hP
      infer_instance
  · obtain ⟨z, hzs, rfl⟩ := hS
    have hyS : S.idealSheaf.subschemeι z ∈ S.support := by
      show _ ∈ (S.idealSheaf.support : Set Y)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have hgen := eq_genericPoint_of_coheight_le_one S hy hyS
    apply hzs
    change IsRegularLocalRing _
    have hq : IdealSheafData.stalk S.idealSheaf (S.idealSheaf.subschemeι z) =
        IsLocalRing.maximalIdeal _ := by
      rw [hgen]
      exact MMP.Resolution.Aux.stalk_idealSheaf_genericPoint S
    have hfield : IsField (Y.presheaf.stalk (S.idealSheaf.subschemeι z) ⧸
        IdealSheafData.stalk S.idealSheaf (S.idealSheaf.subschemeι z)) := by
      rw [hq]
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance
    let e := IdealSheafData.subschemeStalkQuotEquiv S.idealSheaf z
    haveI : IsNoetherianRing (S.idealSheaf.subscheme.presheaf.stalk z) :=
      isNoetherianRing_of_ringEquiv _ e
    exact MMP.Flips.isRegularLocalRing_of_isField (MulEquiv.isField hfield e.symm.toMulEquiv)
  · exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((eq_genericPoint_of_coheight_le_one S hy hS).symm.trans
        (eq_genericPoint_of_coheight_le_one S' hy hS'))

/-- Off the one-label smooth locus the coheight is at least two. -/
private theorem two_le_coheight_of_notMem_oneLabelSmoothLocus [IsLocallyNoetherian Y]
    [IsNormal Y] {L : Finset (MMP.Mori.PrimeDivisor Y)} {y : Y}
    (hy : y ∉ oneLabelSmoothLocus L) : 2 ≤ Order.coheight y := by
  by_contra h
  exact hy (mem_oneLabelSmoothLocus_of_coheight_le_one L
    (Order.le_of_lt_add_one (not_le.1 h)))

end OneLabel

/-! ### Exceptional divisors -/

section Exceptional

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor `(Y, f, E)` over a normal variety `X` is exceptional exactly when its center has
codimension at least two. -/
private theorem isExceptional_iff_two_le_codimension_center (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

/-- A divisor over `X` whose generic point maps to a point of coheight at least two is
exceptional. -/
private theorem isExceptional_of_two_le_coheight (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) (h : 2 ≤ Order.coheight (D.f D.E.genericPoint)) :
    D.IsExceptional := by
  rw [isExceptional_iff_two_le_codimension_center hX,
    MMP.Positivity.DivisorOver.codimension_center]
  exact h

end Exceptional

/-! ### Valuations along a birational morphism -/

/-- **The centre maps to the centre.** If `π : W ⟶ X` is dominant and `D'`, `D₀` are divisors
over `W` and `X` with `π_* v_{D'} = v_{D₀}`, then `π` maps the generic point of the centre of
`D'` to that of `D₀`. -/
private theorem map_genericPoint_eq_of_comap_eq {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral W] [IsSeparated sX]
    {π : W ⟶ X} [IsDominant π] (D' : DivisorOver k (π ≫ sX)) (D₀ : DivisorOver k sX)
    (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation) :
    π (D'.f D'.E.genericPoint) = D₀.f D₀.E.genericPoint := by
  open MMP.Positivity.DivisorOver in
  refine eq_of_dominates sX D₀.valuation (fun x => ?_) (fun x hx => ?_)
    (valuation_algebraMap_le_one D₀ _ rfl) (valuation_algebraMap_lt_one D₀ _ rfl)
  · rw [← hξ]
    change D'.valuation (functionFieldMap π _) ≤ 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact valuation_algebraMap_le_one D' _ rfl _
  · rw [← hξ]
    change D'.valuation (functionFieldMap π _) < 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact valuation_algebraMap_lt_one D' _ rfl _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit _ _ hu))

/-- The generic point of the centre of a divisor `(Y, f, E)` is `f(η_E)`. -/
private theorem genericPoint_center {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) :
    D.center.isIrreducible.genericPoint = D.f D.E.genericPoint :=
  (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).eq
    D.center_eq_closure_genericPoint.symm

/-- The centre of a divisorial valuation on a variety is unique. -/
private theorem isCentre_unique {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (hX : MMP.Mori.IsVariety k sX) {ξ : Valuation X.functionField ℤᵐ⁰}
    {Z Z' : IrreducibleCloseds X} (h : MMP.Intersection.IsCentre k sX ξ Z)
    (h' : MMP.Intersection.IsCentre k sX ξ Z') : Z = Z' := by
  obtain ⟨D, -, rfl, rfl⟩ := h
  obtain ⟨D', -, hv, rfl⟩ := h'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX hv

/-- **Centres map to centres.** If `π : W ⟶ X` is dominant and `ξ_W` is a valuation of `k(W)`
restricting to `ξ`, then `π` maps the generic point of `c_W(ξ_W)` to that of `c_X(ξ)`. -/
private theorem map_genericPoint_of_isCentre {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral W] [IsSeparated sX]
    {π : W ⟶ X} [IsDominant π] {ξW : Valuation W.functionField ℤᵐ⁰}
    {ξ : Valuation X.functionField ℤᵐ⁰} {Z' : IrreducibleCloseds W} {Z : IrreducibleCloseds X}
    (hZ' : MMP.Intersection.IsCentre k (π ≫ sX) ξW Z') (hZ : MMP.Intersection.IsCentre k sX ξ Z)
    (h : ξW.comap (functionFieldMap π) = ξ) :
    π Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint := by
  obtain ⟨D', -, rfl, rfl⟩ := hZ'
  obtain ⟨D, -, rfl, rfl⟩ := hZ
  rw [genericPoint_center, genericPoint_center]
  exact map_genericPoint_eq_of_comap_eq D' D h

/-- Along a bijective ring map every valuation of the source is the restriction of one of the
target. -/
private theorem exists_comap_eq_of_bijective {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {f : K →+* L} (hf : Function.Bijective f)
    (ξ : Valuation K Γ) : ∃ ξ' : Valuation L Γ, ξ'.comap f = ξ := by
  let e := RingEquiv.ofBijective f hf
  exact ⟨ξ.comap e.symm.toRingHom, Valuation.ext fun x => congrArg ξ (e.symm_apply_apply x)⟩

/-- A nonzero element of the maximal ideal of the local ring at the centre of a divisor `D` has
`v_D`-order a positive integer. -/
private theorem exists_valuation_eq_exp_neg {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] (D : DivisorOver k sW) {η : W}
    (hη : η = D.f D.E.genericPoint) {z : W.presheaf.stalk η} (hz0 : z ≠ 0)
    (hz : z ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk η)) :
    ∃ m : ℤ, 1 ≤ m ∧ D.valuation (algebraMap _ W.functionField z) = WithZero.exp (-m) := by
  have hne : D.valuation (algebraMap _ W.functionField z) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0))
  refine ⟨-WithZero.log (D.valuation (algebraMap _ W.functionField z)), ?_, by
    rw [neg_neg, WithZero.exp_log hne]⟩
  have h := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D η hη z hz
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

/-- Local equations of the components through the centre, with positive orders. -/
private theorem exists_localEquations {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W]
    [LocallyOfFiniteType sW] (hsm : IsSmoothScheme sW) {ξ : Valuation W.functionField ℤᵐ⁰}
    {Z : IrreducibleCloseds W} (hZ : MMP.Intersection.IsCentre k sW ξ Z)
    (J : Finset (MMP.Mori.PrimeDivisor W)) (hJ : ∀ j ∈ J, (Z : Set W) ⊆ j.support) :
    ∃ (z : J → W.presheaf.stalk Z.isIrreducible.genericPoint) (m : J → ℤ),
      (∀ j, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
        Ideal.span {z j}) ∧
      (∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) ∧ ∀ j, 1 ≤ m j := by
  obtain ⟨D', -, rfl, rfl⟩ := hZ
  have hηj : ∀ j : J, D'.center.isIrreducible.genericPoint ∈ (j.1.support : Set W) := fun j =>
    hJ j.1 j.2 (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  choose z hzp hz using fun j : J =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sW hsm j.1 (hηj j)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D' (genericPoint_center D')
    (hzp j).ne_zero ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  exact ⟨z, m, hz, hm, hm1⟩

/-- **The arithmetic of the bad centres.** If positive integers `mⱼ` and positive reals `aⱼ`
satisfy `∑ⱼ mⱼ aⱼ + e < 2` with `e ∈ ℕ` and some `a_{j₀} > 1`, then `e = 0` and
`mⱼ ≤ 2 / aⱼ` for every `j`. -/
private theorem eq_zero_and_le_two_div {ι : Type*} [Fintype ι] {m : ι → ℤ}
    {a : ι → ℝ} (hm : ∀ i, 1 ≤ m i) (ha : ∀ i, 0 < a i) {e : ℕ}
    (h : ∑ i, (m i : ℝ) * a i + e < 2) {i₀ : ι} (hi₀ : 1 < a i₀) (j : ι) :
    e = 0 ∧ (m j : ℝ) ≤ 2 / a j := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (m i : ℝ) * a i := fun i _ =>
    mul_nonneg (Int.cast_nonneg (zero_le_one.trans (hm i))) (ha i).le
  have hi := Finset.single_le_sum hnn (Finset.mem_univ i₀)
  have hj := Finset.single_le_sum hnn (Finset.mem_univ j)
  have h1 : (1 : ℝ) ≤ m i₀ := by exact_mod_cast hm i₀
  have hi' : a i₀ ≤ m i₀ * a i₀ := by nlinarith [ha i₀]
  refine ⟨Nat.lt_one_iff.1 (by exact_mod_cast (show (e : ℝ) < 1 by linarith)), ?_⟩
  rw [le_div_iff₀ (ha j)]
  linarith [e.cast_nonneg (α := ℝ)]

/-! ### The log-smooth datum over the bad set -/

/-- An snc closed subset of a smooth scheme is the union of the components of a reduced snc
divisor. -/
private theorem exists_finset_of_isSNCSubset {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW] (hsm : IsSmoothScheme sW) {S : Closeds W}
    (hS : IsSNCSubset sW S) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor W), (⋃ E ∈ s, (E.support : Set W)) = S ∧
      DivisorWithCoeffs.IsSNC sW (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
  haveI : LocallyOfFinitePresentation sW :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sW)).mpr inferInstance
  rcases hS with rfl | h
  · refine ⟨∅, by simp, ?_⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
  · exact h

/-- **A log-smooth datum principalizing a closed set of codimension two.** Let `(Y, Θ)` be a klt
pair and `A ⊆ Y` a closed set all of whose points have coheight at least two. There is a
log-smooth datum `(π, T)` such that every point of `π⁻¹(A)` lies on a component `Tⱼ` of `T`
whose generic point maps to a point of coheight at least two. -/
private theorem exists_isLogSmoothDatum_forall_mem_preimage {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ) (A : Closeds Y)
    (hA : ∀ y ∈ (A : Set Y), 2 ≤ Order.coheight y) :
    ∃ (W : Scheme.{u}) (π : W ⟶ Y) (T : Divisor W), IsLogSmoothDatum sY Θ π T ∧
      ∀ w : W, π w ∈ (A : Set Y) → ∃ E ∈ T.support, w ∈ E.support ∧
        2 ≤ Order.coheight (π E.genericPoint) := by
  classical
  haveI : IsAlgClosed k := hΘ.1.isAlgClosed
  haveI : CharZero k := hΘ.1.charZero
  obtain ⟨hY, n, K, hK, hq⟩ := hΘ.1.isPair
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  set IA := Scheme.IdealSheafData.vanishingIdeal A with hIA
  set IΘ := Scheme.IdealSheafData.vanishingIdeal Θ.supp with hIΘ
  have hgA : genericPoint Y ∉ (A : Set Y) := fun h => by
    have := hA _ h
    rw [show Order.coheight (genericPoint Y) = 0 from Order.coheight_top Y] at this
    exact absurd this (by decide)
  have hsuppI : ((IA * IΘ).support : Set Y) = (A : Set Y) ∪ (Θ.supp : Set Y) := by
    rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, hIA, hIΘ,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hI : IA * IΘ ≠ ⊥ := by
    intro h
    have h' : genericPoint Y ∈ ((IA * IΘ).support : Set Y) := by rw [h]; simp
    rw [hsuppI] at h'
    rcases h' with h1 | h2
    · exact hgA h1
    · exact MMP.Fourfold.genericPoint_notMem_supp Θ h2
  obtain ⟨W, π, -, hproj, hbir, hsm, -, hcart, hsnc, -⟩ :=
    exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap sY hY.1 (IA * IΘ) hI
  haveI : IsProper π := hproj.isProper
  have hfres : IsSmoothResolution sY π := ⟨inferInstance, hbir, hsm⟩
  obtain ⟨hW, -, -⟩ := hfres.isNormalVariety hY
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hW.2
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hΘ.1.isPair hK π hW hbir
  set S := exceptionalSet π ⊔ ((IA * IΘ).comap π).support with hS
  obtain ⟨s, hs, hsncs⟩ := exists_finset_of_isSNCSubset hsm hsnc
  have hsupp : (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor W).support = s :=
    MMP.Intersection.support_reducedDivisorOf s
  have hmem : ∀ G : MMP.Mori.PrimeDivisor W, G.genericPoint ∈ (S : Set W) → G ∈ s :=
    fun G hG => by
    rw [← hs] at hG
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  have hpre : ∀ w : W, π w ∈ ((IA * IΘ).support : Set Y) → w ∈ (S : Set W) := fun w hw =>
    Or.inr (by rwa [Scheme.IdealSheafData.support_comap])
  refine ⟨W, π, ∑ E ∈ s, Finsupp.single E (1 : ℤ), ⟨hΘ, hproj, hbir, hW, hsm,
    MMP.Intersection.isReducedEffective_reducedDivisorOf s, hsncs, fun w hw => ?_, n, K, BW, hBW, fun G hG => ?_⟩,
    fun w hw => ?_⟩
  · rw [hsupp, hs]
    exact Or.inl hw
  · rw [hsupp]
    apply hmem
    rcases genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hY, hK, hq⟩ hW hbir hBW hG
      with h | h
    · exact Or.inl h
    · refine hpre _ ?_
      rw [hsuppI]
      rw [Finset.sup_set_eq_biUnion] at h
      obtain ⟨E, hE, hx⟩ := Set.mem_iUnion₂.1 h
      exact Or.inr (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hE) hx)
  · have hcartA : Stacks.Divisors.IsEffectiveCartierDivisor (IA.comap π) := by
      have h := hcart
      rw [Stacks.IdealSheaf.comap_mul] at h
      exact AlgebraicGeometry.isEffectiveCartierDivisor_left_of_mul _ _ h
    have hcomapA : ∀ x : W, x ∈ ((IA.comap π).support : Set W) ↔ π x ∈ (A : Set Y) := by
      intro x
      rw [Scheme.IdealSheafData.support_comap]
      change π x ∈ (IA.support : Set Y) ↔ _
      rw [hIA, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have hAS : ((IA.comap π).support : Set W) ⊆ S := fun x hx =>
      hpre x (by rw [hsuppI]; exact Or.inl ((hcomapA x).1 hx))
    obtain ⟨P, hPA, hwP⟩ :=
      exists_primeDivisor_subset_support_mem hsnc hcartA hAS ((hcomapA w).2 hw)
    refine ⟨P, ?_, hwP, hA _ ((hcomapA _).1
      (hPA (MMP.Flips.primeDivisor_genericPoint_mem_support P)))⟩
    rw [hsupp]
    exact mem_of_support_subset (hs ▸ hPA.trans hAS)

/-! ### Centres off the one-label smooth locus -/

section Global

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Centres off `Y°`.** For a terminal pair `(Y, Θ)` with labels `L`, the exceptional
valuations `ξ` with `a(ξ; Y, Θ) < 2` whose centre has its generic point off the one-label smooth
locus lie in a finite set: on a log-smooth datum principalizing `Y ∖ Y°`, the centre of `ξ` lies on
an exceptional component of `T`, of log discrepancy `> 1`, so `e_T(ξ) = 0` and the orders of
`ξ` along the components of `T` are bounded. -/
private theorem exists_finite_of_genericPoint_notMem {Θ : QDivisor Y}
    (hΘ : IsKltTerminalPair sY Θ) (L : Finset (MMP.Mori.PrimeDivisor Y)) :
    ∃ F : Set (Valuation Y.functionField ℤᵐ⁰), F.Finite ∧
      ∀ ξ, MMP.Intersection.IsExceptionalValuation k sY ξ →
        (∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sY Θ ξ a) →
        ∀ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre k sY ξ Z →
          Z.isIrreducible.genericPoint ∉ oneLabelSmoothLocus L → ξ ∈ F := by
  classical
  have hklt := hΘ.1
  haveI : IsAlgClosed k := hklt.1.isAlgClosed
  haveI : CharZero k := hklt.1.charZero
  obtain ⟨hY, n, K, hK, -⟩ := hklt.1.isPair
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  let A : Closeds Y := ⟨(oneLabelSmoothLocus L)ᶜ, (isOpen_oneLabelSmoothLocus sY L).isClosed_compl⟩
  obtain ⟨W, π, T, hπ, hPA⟩ := exists_isLogSmoothDatum_forall_mem_preimage hklt A
    (fun y hy => two_le_coheight_of_notMem_oneLabelSmoothLocus hy)
  have hW : IsNormalVariety k (π ≫ sY) := hπ.isNormalVariety
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hW.2
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  -- the log discrepancies `aⱼ > 0` of the prime divisors of `W`
  let DT : MMP.Mori.PrimeDivisor W → DivisorOver k sY :=
    fun j => ⟨W, π, hW, hπ.isBirationalMorphism, j⟩
  have hex : ∀ j, ∃ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) (DT j) a := fun j => by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hklt.1.isPair hK (DT j)
    exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstance : IsProper π)⟩
  choose aT haT using hex
  have haT0 : ∀ j, 0 < aT j := fun j => hklt.2 n (DT j) (aT j) (haT j)
  set M : ℕ := ⌈∑ j ∈ T.support, 2 / aT j⌉₊ + 1 with hM
  refine ⟨_, (finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sY) T (M := M)
    (Nat.le_add_left 1 _)).image fun ξ => ξ.comap (functionFieldMap π), ?_⟩
  rintro ξ - ⟨a, ha2, n', D, hDξ, ha⟩ Z hZ hηZ
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  -- lift `ξ` to a valuation `ξ_W` of `k(W)`
  obtain ⟨ξW, hΦ⟩ :=
    exists_comap_eq_of_bijective hπ.isBirationalMorphism.functionFieldMap_bijective ξ
  refine ⟨ξW, ?_, hΦ⟩
  obtain ⟨Z', hZ', eT, heT, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sY hπ aT
      (fun j _ => haT j) D ha.2.1 ha ξW (hΦ.trans hDξ.symm)
  -- `π` maps the generic point of `c_W(ξ)` to that of `c_Y(ξ) = Z`, which lies off `Y°`
  obtain ⟨E, hET, hηE, hE2⟩ := hPA _ (by
    change π _ ∉ oneLabelSmoothLocus L
    rwa [map_genericPoint_of_isCentre hZ' hZ hΦ])
  have hEJ : E ∈ sncIndexSet T (Z' : Set W) := Finset.mem_filter.2 ⟨hET, by
    rw [← (Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed).def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηE) E.idealSheaf.support.isClosed⟩
  have haE : 1 < aT E :=
    hΘ.2 _ (DT E) (aT E) (isExceptional_of_two_le_coheight hY (DT E) hE2) (haT E)
  -- local equations `zⱼ` of the components `Tⱼ` through the centre, and `ξ(Tⱼ) = mⱼ ≥ 1`
  obtain ⟨z, m, hz, hm, hm1⟩ := exists_localEquations hπ.isSmoothScheme hZ' _
    (fun j hj => (Finset.mem_filter.1 hj).2)
  have hform' := hform z m hz hm
  obtain ⟨e0, rfl⟩ := heT.exists_eq_natCast
  push_cast at hform'
  have hsum : ∑ j, (m j : ℝ) * aT j + e0 < 2 := hform' ▸ ha2
  obtain rfl := (eq_zero_and_le_two_div hm1 (fun j => haT0 j) hsum (i₀ := ⟨E, hEJ⟩) haE
    ⟨E, hEJ⟩).1
  refine ⟨by exact_mod_cast heT, fun Z'' hZ'' j hj z' hz' => ?_⟩
  obtain rfl : Z'' = Z' := isCentre_unique hW.1 hZ'' hZ'
  have hval : ξW (algebraMap _ W.functionField z') = WithZero.exp (-m ⟨j, hj⟩) := by
    obtain ⟨D', -, rfl, rfl⟩ := hZ'
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz'.symm.trans (hz ⟨j, hj⟩))
    rw [← hm, ← hu, map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
      _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ (genericPoint_center D')) u,
      mul_one]
  rw [hval, WithZero.exp_le_exp, neg_le_neg_iff]
  have h1 := (eq_zero_and_le_two_div hm1 (fun j => haT0 j) hsum (i₀ := ⟨E, hEJ⟩) haE
    ⟨j, hj⟩).2
  have h2 : 2 / aT j ≤ ∑ i ∈ T.support, 2 / aT i :=
    Finset.single_le_sum (fun i _ => (div_pos two_pos (haT0 i)).le) (Finset.mem_filter.1 hj).1
  have h3 := Nat.le_ceil (∑ i ∈ T.support, 2 / aT i)
  exact_mod_cast (show (m ⟨j, hj⟩ : ℝ) ≤ M by rw [hM]; push_cast; linarith)

end Global

section Port

open IsLocalRing

/-- An open subset of the regular locus is smooth over a perfect field. -/
private theorem isSmoothScheme_ι_comp {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY)
    (U : Y.Opens) (hU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u)) :
    IsSmoothScheme (U.ι ≫ sY) := by
  have := hY
  have hs : Smooth (U.ι ≫ sY) := by
    rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    intro u
    have hr : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hU _ u.2
    exact @IsRegularLocalRing.of_ringEquiv _ _ hr _ _
      (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
  refine eq_top_iff.2 (le_sSup ?_)
  show Smooth ((⊤ : U.toScheme.Opens).ι ≫ U.ι ≫ sY)
  infer_instance

/-- **The pointwise snc condition suffices on a smooth scheme.** On a smooth scheme over a
perfect field, a divisor satisfying the pointwise condition of `DivisorWithCoeffs.IsSNC` (a
regular system of parameters containing local equations of the components through each point)
is snc: each component is locally cut out by a parameter, hence smooth. -/
private theorem isSNC_of_forall_exists {k : Type u} [Field k] [PerfectField k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW] (hW : IsSmoothScheme sW) {R : Type*}
    [Zero R] {D : DivisorWithCoeffs R W}
    (h : ∀ x : W, ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk x)
      (j : {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ x ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (j E)}) :
    D.IsSNC sW := by
  refine ⟨fun E hE => MMP.Resolution.isSmoothScheme_subscheme_of_forall_stalk_eq_span sW hW
    E.idealSheaf fun x hx => ?_, h⟩
  obtain ⟨n, z, j, hz, -, hzE⟩ := h x
  exact ⟨n, z, j ⟨E, hE, hx⟩, hz, hzE ⟨E, hE, hx⟩⟩

/-! ### The pair on an open subset -/

private lemma span_pair_eq {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (hxy : IsRegularSystemOfParameters ![x, y]) :
    Ideal.span {x, y} = IsLocalRing.maximalIdeal A := by
  rw [← hxy.1]; congr 1; ext; simp [Matrix.range_cons, Set.pair_comm]

/-- A variety over a field is a Noetherian scheme. -/
private lemma isNoetherian_of_isVariety {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k sY) : IsNoetherian Y := by
  have := hY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := by
    rw [← isCompact_univ_iff, ← Set.preimage_univ (f := sY.base)]
    exact QuasiCompact.isCompact_preimage _ isOpen_univ isCompact_univ
  exact ⟨⟩

/-- A ring equivalence of local rings carries a regular system of parameters to one. -/
private theorem isRegularSystemOfParameters_map_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {n : ℕ} {w : Fin n → A}
    (hw : IsRegularSystemOfParameters w) : IsRegularSystemOfParameters fun j => e (w j) := by
  refine ⟨?_, (ringKrullDim_eq_of_ringEquiv e).symm.trans hw.2⟩
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← hw.1, Ideal.map_span, ← Set.range_comp]
  rfl

section Neighbourhood

/-- The stalk of a sum of ideal sheaves. -/
private theorem stalk_add {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I + J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hx,
    show (I + J).ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ from rfl, Ideal.map_sup]

/-- A section on `W ⊇ U`, as a global section of the open subscheme `U`. -/
private def sectionOn {Y : Scheme.{u}} {W U : Y.Opens} (h : U ≤ W)
    (f : Γ(Y, W)) : Γ(U.toScheme, ⊤) :=
  U.toScheme.presheaf.map (homOfLE (show ⊤ ≤ U.ι ⁻¹ᵁ W from fun u _ => h u.2)).op
    ((U.ι.app W).hom f)

private theorem germ_sectionOn {Y : Scheme.{u}} {W U : Y.Opens} (h : U ≤ W)
    (f : Γ(Y, W)) (u : U.toScheme) :
    U.toScheme.presheaf.germ ⊤ u trivial (sectionOn h f) =
      (U.ι.stalkMap u).hom (Y.presheaf.germ W (U.ι u) (h u.2) f) := by
  have h1 := Scheme.Hom.germ_stalkMap U.ι W u (h u.2)
  have h2 := congrArg (fun φ => φ.hom f) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2, sectionOn]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Near a point where the quotient of the local ring by an ideal sheaf is regular, it stays
regular. -/
private theorem exists_isOpen_forall_isRegularLocalRing_quotient {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (I : Y.IdealSheafData) {y : Y} (hy : y ∈ I.support)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk I y)) :
    ∃ W : Y.Opens, y ∈ W ∧ ∀ u ∈ W, u ∈ I.support →
      IsRegularLocalRing (Y.presheaf.stalk u ⧸ IdealSheafData.stalk I u) := by
  have hopen := MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (I.subschemeι ≫ sY)
  obtain ⟨W, hW, hWeq⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp hopen
  have hrange : ∀ u, u ∈ I.support → ∃ z : I.subscheme, I.subschemeι z = u := fun u hu => by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι] at hu
    exact hu
  obtain ⟨z, rfl⟩ := hrange y hy
  have hz : z ∈ regularLocus I.subscheme :=
    IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z)
  refine ⟨⟨W, hW⟩, (hWeq ▸ hz : z ∈ I.subschemeι ⁻¹' W), fun u hu hus => ?_⟩
  obtain ⟨z', rfl⟩ := hrange u hus
  have hz' : z' ∈ regularLocus I.subscheme := hWeq ▸ (hu : z' ∈ I.subschemeι ⁻¹' W)
  have : IsRegularLocalRing (I.subscheme.presheaf.stalk z') := hz'
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z').symm

private theorem exists_mul_mem_of_map_eq_span {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsNoetherianRing R]
    (J : Ideal R) (g : R) (h : J.map (algebraMap R S) = Ideal.span {algebraMap R S g}) :
    ∃ s ∉ p, s * g ∈ J ∧ ∀ j ∈ J, s * j ∈ Ideal.span {g} := by
  classical
  have hmem : ∀ (I : Ideal R) (a : R), algebraMap R S a ∈ I.map (algebraMap R S) →
      ∃ s ∈ p.primeCompl, s * a ∈ I := by
    intro I a ha
    obtain ⟨⟨⟨j, hj⟩, ⟨s', hs'⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).1 ha
    rw [← map_mul] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 e
    refine ⟨c * s', p.primeCompl.mul_mem hc hs', ?_⟩
    have : c * s' * a = c * j := by simp only at hc'; rw [← hc']; ring
    rw [this]
    exact I.mul_mem_left _ hj
  obtain ⟨s0, hs0, hs0g⟩ := hmem J g (h ▸ Ideal.mem_span_singleton_self _)
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian J : J.FG)
  have hgen : ∀ j ∈ G, ∃ s ∈ p.primeCompl, s * j ∈ Ideal.span {g} := by
    intro j hj
    refine hmem _ j ?_
    rw [Ideal.map_span, Set.image_singleton, ← h]
    exact Ideal.mem_map_of_mem _ (hG ▸ Submodule.subset_span hj)
  choose s_ hs_ hs_j using hgen
  set s1 : R := ∏ j ∈ G.attach, s_ j.1 j.2
  have hs1 : s1 ∈ p.primeCompl := Submonoid.prod_mem _ fun j _ => hs_ j.1 j.2
  have hs1J : ∀ j ∈ J, s1 * j ∈ Ideal.span {g} := by
    intro j hj
    rw [← hG] at hj
    induction hj using Submodule.span_induction with
    | mem j hj =>
      have : s1 = s_ j hj * ∏ i ∈ G.attach.erase ⟨j, hj⟩, s_ i.1 i.2 :=
        (Finset.mul_prod_erase _ (fun i : G => s_ i.1 i.2) (Finset.mem_attach G ⟨j, hj⟩)).symm
      rw [this, mul_comm (s_ j hj), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hs_j j hj)
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
  refine ⟨s0 * s1, p.primeCompl.mul_mem hs0 hs1, ?_, fun j hj => ?_⟩
  · rw [mul_comm s0, mul_assoc]; exact J.mul_mem_left _ hs0g
  · rw [mul_comm s0, mul_assoc, mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hs1J j hj)

/-- **Spreading out a principal stalk.** If the stalk at `y` of an ideal sheaf on a locally
Noetherian scheme is generated by the germ of a section `f`, then so is its stalk at every point
of a neighbourhood of `y`. -/
private theorem exists_forall_stalk_eq_span {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) {W : Y.Opens} (f : Γ(Y, W)) {y : Y} (hyW : y ∈ W)
    (h : IdealSheafData.stalk I y = Ideal.span {Y.presheaf.germ W y hyW f}) :
    ∃ W' : Y.Opens, y ∈ W' ∧ ∃ hW' : W' ≤ W, ∀ u (hu : u ∈ W'),
      IdealSheafData.stalk I u = Ideal.span {Y.presheaf.germ W u (hW' hu) f} := by
  obtain ⟨A, hA, hyA, hAW⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := W) hyW
  have := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  set g : Γ(Y, A) := Y.presheaf.map (homOfLE hAW).op f
  have hg : ∀ u (hu : u ∈ A), Y.presheaf.germ A u hu g = Y.presheaf.germ W u (hAW hu) f :=
    fun u hu => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  letI : Algebra Γ(Y, A) (Y.presheaf.stalk y) := (Y.presheaf.germ A y hyA).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (hA.primeIdealOf ⟨y, hyA⟩).asIdeal :=
    hA.isLocalization_stalk ⟨y, hyA⟩
  have hmap : (I.ideal ⟨A, hA⟩).map (algebraMap Γ(Y, A) (Y.presheaf.stalk y)) =
      Ideal.span {algebraMap Γ(Y, A) (Y.presheaf.stalk y) g} := by
    have := IdealSheafData.stalk_eq_map_germ I y ⟨A, hA⟩ hyA
    rw [h, ← hg y hyA] at this
    exact this.symm
  obtain ⟨s, hsp, hsg, hsJ⟩ := exists_mul_mem_of_map_eq_span (S := Y.presheaf.stalk y)
    (hA.primeIdealOf ⟨y, hyA⟩).asIdeal _ _ hmap
  refine ⟨Y.basicOpen s, ?_, (Y.basicOpen_le s).trans hAW, fun u hu => ?_⟩
  · rw [Scheme.mem_basicOpen _ _ _ hyA]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ _ s).2 hsp
  have huA : u ∈ A := Y.basicOpen_le s hu
  have hunit : IsUnit (Y.presheaf.germ A u huA s) := (Scheme.mem_basicOpen _ _ _ huA).1 hu
  rw [IdealSheafData.stalk_eq_map_germ I u ⟨A, hA⟩ huA, ← hg u huA]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun j hj => ?_) ?_
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hsJ j hj)
    have := congrArg (Y.presheaf.germ A u huA).hom hc
    rw [map_mul, map_mul] at this
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨hunit.unit⁻¹ * (Y.presheaf.germ A u huA).hom c, ?_⟩
    rw [mul_assoc, this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm : (Y.presheaf.germ A u huA).hom (s * g) ∈ (I.ideal ⟨A, hA⟩).map
        (Y.presheaf.germ A u huA).hom := Ideal.mem_map_of_mem _ hsg
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (hunit.unit⁻¹ : (Y.presheaf.stalk u)ˣ).1 hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

/-- A lift of an element of the maximal ideal of a quotient lies in the maximal ideal. -/
private theorem mem_maximalIdeal_of_mk_mem {A : Type*} [CommRing A] [IsLocalRing A]
    (K : Ideal A) [IsLocalRing (A ⧸ K)] {a : A}
    (ha : Ideal.Quotient.mk K a ∈ maximalIdeal (A ⧸ K)) : a ∈ maximalIdeal A :=
  (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (hu.map _)

/-- **Lifting a regular system of parameters of a quotient.** If `A ⧸ K` has a regular system of
parameters `w`, and `z` is a family in `𝔪_A` of length `dim A` whose span contains `K` and
which contains lifts of all the `wᵢ`, then `z` is a regular system of parameters of `A`. -/
private theorem isRegularSystemOfParameters_of_lift {A : Type*} [CommRing A] [IsLocalRing A]
    (K : Ideal A) [IsLocalRing (A ⧸ K)] {n N : ℕ} {w : Fin n → A ⧸ K}
    (hw : IsRegularSystemOfParameters w) (z : Fin N → A) (hzm : ∀ i, z i ∈ maximalIdeal A)
    (hzK : K ≤ Ideal.span (Set.range z)) (hlift : ∀ i, ∃ j, Ideal.Quotient.mk K (z j) = w i)
    (hN : ringKrullDim A = N) : IsRegularSystemOfParameters z := by
  refine ⟨le_antisymm (Ideal.span_le.2 (Set.range_subset_iff.2 hzm)) ?_, hN⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  haveI : IsLocalHom (Ideal.Quotient.mk K) := IsLocalHom.of_surjective _ hsurj
  have hm : maximalIdeal A = (maximalIdeal (A ⧸ K)).comap (Ideal.Quotient.mk K) := by
    ext a
    exact ⟨fun ha => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha
      (isUnit_of_map_unit _ _ hu), fun ha => mem_maximalIdeal_of_mk_mem K ha⟩
  rw [hm, ← hw.1]
  calc Ideal.comap (Ideal.Quotient.mk K) (Ideal.span (Set.range w))
      ≤ Ideal.comap (Ideal.Quotient.mk K) ((Ideal.span (Set.range z)).map (Ideal.Quotient.mk K)) :=
        Ideal.comap_mono (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => by
          obtain ⟨j, hj⟩ := hlift i
          rw [← hj]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)))
    _ = Ideal.span (Set.range z) := by
        rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.2 hzK]

/-- In a regular local ring, a nonzero `a ∈ 𝔪` with `A ⧸ (a)` regular is the first member of a
regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_cons {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {a : A} (ham : a ∈ maximalIdeal A) (ha0 : a ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {a})) :
    ∃ (n : ℕ) (z : Fin (n + 1) → A), IsRegularSystemOfParameters z ∧ z 0 = a := by
  have := IsRegularLocalRing.isDomain A
  obtain ⟨n, w, hw⟩ := exists_isRegularSystemOfParameters (A ⧸ Ideal.span {a})
  have hdim : ringKrullDim (A ⧸ Ideal.span {a}) + 1 = ringKrullDim A :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
      (p := maximalIdeal A) (maximalIdeal_height_eq_ringKrullDim) ham
  choose w' hw' using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span {a}) (w i)
  have hw'm : ∀ i, w' i ∈ maximalIdeal A := fun i => mem_maximalIdeal_of_mk_mem _ (by
    rw [hw' i, ← hw.1]; exact Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨n, Fin.cons a w', isRegularSystemOfParameters_of_lift _ hw _ ?_ ?_ ?_ ?_, rfl⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ham
    · simpa using hw'm i
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨0, rfl⟩
  · exact fun i => ⟨i.succ, by simpa using hw' i⟩
  · rw [← hdim, hw.2]; rfl

/-- In a regular local ring, if `a, b ∈ 𝔪`, `a ≠ 0`, `b ∉ (a)`, and `A ⧸ (a)` and
`A ⧸ (a, b)` are regular, then `a, b` are the first two members of a regular system of
parameters. -/
private theorem exists_isRegularSystemOfParameters_cons_cons {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {a b : A} (ham : a ∈ maximalIdeal A) (hbm : b ∈ maximalIdeal A)
    (ha0 : a ≠ 0) (hba : b ∉ Ideal.span {a})
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {a}))
    (hreg2 : IsRegularLocalRing (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))) :
    ∃ (n : ℕ) (z : Fin (n + 2) → A), IsRegularSystemOfParameters z ∧ z 0 = a ∧ z 1 = b := by
  have := IsRegularLocalRing.isDomain A
  have := IsRegularLocalRing.isDomain (A ⧸ Ideal.span {a})
  obtain ⟨n, w, hw⟩ := exists_isRegularSystemOfParameters (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))
  have hdim1 : ringKrullDim (A ⧸ Ideal.span {a}) + 1 = ringKrullDim A :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
      (p := maximalIdeal A) (maximalIdeal_height_eq_ringKrullDim) ham
  set b' := Ideal.Quotient.mk (Ideal.span {a}) b
  have hb'0 : b' ≠ 0 := fun h => hba (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hb'm : b' ∈ maximalIdeal (A ⧸ Ideal.span {a}) := (mem_maximalIdeal _).2 fun hu =>
    (mem_maximalIdeal _).1 hbm (isUnit_of_map_unit _ _ hu)
  have hdim2 : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {b'}) + 1 =
      ringKrullDim (A ⧸ Ideal.span {a}) :=
    Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hb'0)
      (p := maximalIdeal _) (maximalIdeal_height_eq_ringKrullDim) hb'm
  have he : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {b'}) =
      ringKrullDim (A ⧸ (Ideal.span {a} ⊔ Ideal.span {b})) := by
    have : Ideal.span {b'} = (Ideal.span {b}).map (Ideal.Quotient.mk (Ideal.span {a})) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup _ _)
  choose w' hw' using fun i =>
    Ideal.Quotient.mk_surjective (I := Ideal.span {a} ⊔ Ideal.span {b}) (w i)
  have hw'm : ∀ i, w' i ∈ maximalIdeal A := fun i => mem_maximalIdeal_of_mk_mem _ (by
    rw [hw' i, ← hw.1]; exact Ideal.subset_span ⟨i, rfl⟩)
  refine ⟨n, Fin.cons a (Fin.cons b w'),
    isRegularSystemOfParameters_of_lift _ hw _ ?_ ?_ ?_ ?_, rfl, rfl⟩
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact ham
    · exact hbm
    · simpa using hw'm i
  · refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff]
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩
  · exact fun i => ⟨i.succ.succ, by simpa using hw' i⟩
  · rw [← hdim1, ← hdim2, he, hw.2]; push_cast; ring_nf

/-- A member of a regular system of parameters of `𝒪_{Y,y}` cuts out a prime divisor through
`y`: the closure of the generization of `y` at the prime it generates. -/
private theorem exists_primeDivisor_stalk_eq_span {Y : Scheme.{u}} {y : Y}
    [IsRegularLocalRing (Y.presheaf.stalk y)] {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : IsRegularSystemOfParameters z) (m : Fin n) :
    ∃ E : MMP.Mori.PrimeDivisor Y, y ∈ E.support ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {z m} := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  have hP := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz m
  set q : PrimeSpectrum (Y.presheaf.stalk y) := ⟨Ideal.span {z m}, hP⟩
  have hz0 : z m ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m
  have hzu : ¬ IsUnit (z m) := fun hu => hP.ne_top (Ideal.span_singleton_eq_top.2 hu)
  have h1 : Order.coheight (Y.fromSpecStalk y q) = 1 := by
    refine (Stacks.Chow.coheight_fromSpecStalk_eq_height (W := Y) y q).trans ?_
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) hzu
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hsupp : (E.support : Set Y) = closure {Y.fromSpecStalk y q} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨E, ?_, ?_⟩
  · rw [hsupp]
    exact specializes_iff_mem_closure.1 (MMP.Resolution.specializes_fromSpecStalk y q)
  · have hcl : E.idealSheaf.support = Closeds.closure {Y.fromSpecStalk y q} :=
      Closeds.ext (by rwa [Closeds.coe_closure])
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E, hcl]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q

/-- A local equation of a prime divisor at a point of it is a nonzero element of the maximal
ideal. -/
private theorem mem_maximalIdeal_and_ne_zero_of_stalk_eq_span {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hy : y ∈ E.support) {a : Y.presheaf.stalk y}
    (ha : IdealSheafData.stalk E.idealSheaf y = Ideal.span {a}) :
    a ∈ maximalIdeal (Y.presheaf.stalk y) ∧ a ≠ 0 := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  refine ⟨(mem_maximalIdeal _).2 fun hu => ?_, ?_⟩
  · exact (IdealSheafData.stalk_eq_top_iff_notMem_support E.idealSheaf y).1
      (by rwa [ha, Ideal.span_singleton_eq_top]) hy
  · rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hqh (by rw [← hq, ha, Ideal.span_singleton_eq_bot])

/-- At a point of a prime divisor `E` where `E` is regular, `𝒪_{Y,y} ⧸ I_{E,y}` is regular. -/
private theorem isRegularLocalRing_quotient_of_notMem_image_singularLocus {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ E.support)
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk E.idealSheaf y) := by
  obtain ⟨z, rfl⟩ : y ∈ Set.range E.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hz : IsRegularLocalRing (E.idealSheaf.subscheme.presheaf.stalk z) := by
    by_contra h
    exact hsm ⟨z, h, rfl⟩
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z).symm

/-- A local equation `a` of a prime divisor `E` at a point `y` where `Y` and `E` are regular is
a nonzero element of `𝔪_y` with `𝒪_{Y,y} ⧸ (a)` regular. -/
private theorem localEquation_spec {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y) {y : Y}
    [IsRegularLocalRing (Y.presheaf.stalk y)] (hy : y ∈ E.support)
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme)
    {a : Y.presheaf.stalk y} (ha : IdealSheafData.stalk E.idealSheaf y = Ideal.span {a}) :
    a ∈ maximalIdeal (Y.presheaf.stalk y) ∧ a ≠ 0 ∧
      IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {a}) :=
  ⟨(mem_maximalIdeal_and_ne_zero_of_stalk_eq_span E hy ha).1,
    (mem_maximalIdeal_and_ne_zero_of_stalk_eq_span E hy ha).2,
    ha ▸ isRegularLocalRing_quotient_of_notMem_image_singularLocus E hy hsm⟩

/-- If `x` is the only generization of itself in a closed subset `D` of a Noetherian sober
space, then near `x` the set `D` lies in `closure {x}`. -/
private theorem exists_isOpen_inter_subset_closure {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {D : Set T} (hD : IsClosed D) {x : T}
    (hgen : ∀ ξ ∈ D, ξ ⤳ x → ξ = x) :
    ∃ W : Set T, IsOpen W ∧ x ∈ W ∧ W ∩ D ⊆ closure {x} := by
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hD
  set C := {W ∈ MMP.Resolution.componentsOf D | x ∉ W}
  have hcl : IsClosed (⋃₀ C) := (hfin.subset fun W hW => hW.1).isClosed_sUnion
    fun W hW => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hD hW.1
  refine ⟨(⋃₀ C)ᶜ, hcl.isOpen_compl, fun ⟨W, hW, hxW⟩ => hW.2 hxW, ?_⟩
  rintro y ⟨hyC, hyD⟩
  obtain ⟨W, hW, hyW⟩ := hcov hyD
  have hxW : x ∈ W := by
    by_contra h
    exact hyC ⟨W, ⟨hW, h⟩, hyW⟩
  have hWc := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hD hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWc
  have hξx : ξ ⤳ x := by
    rwa [specializes_iff_mem_closure, hξ.def]
  have hξD : ξ ∈ D := hW.1.2 hξ.mem
  rw [← hgen ξ hξD hξx, hξ.def]
  exact hyW

/-- A local equation `x` of a prime divisor `E` at a point `y` where `E` is regular lies in
`𝔪_y ∖ 𝔪_y²`. -/
private theorem mem_maximalIdeal_notMem_sq_of_regular {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ E.support) [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme)
    {x : Y.presheaf.stalk y} (hx : IdealSheafData.stalk E.idealSheaf y = Ideal.span {x}) :
    x ∈ IsLocalRing.maximalIdeal _ ∧ x ∉ IsLocalRing.maximalIdeal _ ^ 2 := by
  obtain ⟨hxm, hx0⟩ := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span E hy hx
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  refine ⟨hxm, fun hx2 => ?_⟩
  have hquot := isRegularLocalRing_quotient_of_notMem_image_singularLocus E hy hsm
  rw [hx] at hquot
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero hx0) hx2 hquot

/-- In a two-dimensional regular local ring, an element of `𝔪 ∖ 𝔪²` is part of a regular system
of parameters. -/
private theorem exists_isRegularSystemOfParameters_pair {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ∃ t : R, MMP.Mori.IsRegularSystemOfParameters ![x, t] := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have h2 : (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by
    have := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
    exact_mod_cast this
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = IsLocalRing.maximalIdeal R := by simpa using hspan
  have key : ∀ {p q : R}, Ideal.span {p, q} = IsLocalRing.maximalIdeal R → ∀ c₀ c₁ : R,
      x = c₀ * p + c₁ * q → IsUnit c₀ → Ideal.span {x, q} = IsLocalRing.maximalIdeal R := by
    intro p q hpq c₀ c₁ hx hu
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rintro _ (rfl | rfl)
      exacts [hxm, hpq ▸ Ideal.subset_span (by simp)]
    · have hp : p = ↑hu.unit⁻¹ * x - ↑hu.unit⁻¹ * c₁ * q := by
        rw [hx, mul_add, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
        ring
      rw [← hpq]
      refine Ideal.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [hp]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · exact Ideal.subset_span (by simp)
  have ha : a ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  have hb : b ∈ IsLocalRing.maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hx⟩ := Ideal.mem_span_pair.mp (hab ▸ hxm : x ∈ Ideal.span {a, b})
  have hunit : IsUnit c₀ ∨ IsUnit c₁ := by
    by_contra! h
    apply hx2
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.2) hb)
  obtain ⟨t, ht⟩ : ∃ t, Ideal.span {x, t} = IsLocalRing.maximalIdeal R := by
    rcases hunit with hu | hu
    · exact ⟨b, key hab c₀ c₁ hx.symm hu⟩
    · exact ⟨a, key (by rwa [Set.pair_comm]) c₁ c₀ (by rw [← hx]; ring) hu⟩
  exact ⟨t, by rw [← ht]; congr 1; ext; simp [Matrix.range_cons, or_comm],
    by exact_mod_cast hdim⟩

open MMP.Threefold.Mori.OpenRestriction in
/-- A prime divisor of `Y` meeting an open `U` is the image of a prime divisor of `U`, whose
support is the preimage and whose stalks are those of the given one. -/
private theorem exists_primeDivisor_restrict {Y : Scheme.{u}} (U : Y.Opens)
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hyU : y ∈ U) (hy : y ∈ E.support) :
    ∃ EU : MMP.Mori.PrimeDivisor U.toScheme,
      OpenWeilRestriction.primeDivisorMap U.ι EU = E ∧ EU.support = U.ι ⁻¹' E.support ∧
      ∀ u, IdealSheafData.stalk EU.idealSheaf u =
        Ideal.map (U.ι.stalkMap u).hom (IdealSheafData.stalk E.idealSheaf (U.ι u)) := by
  obtain ⟨EU, hEU⟩ := exists_primeDivisorMap_eq_of_mem_support U.ι E ⟨y, hyU⟩ hy
  refine ⟨EU, hEU, ?_, fun u => ?_⟩
  · ext v
    rw [Set.mem_preimage, ← hEU]
    exact (mem_support_primeDivisorMap_iff U.ι EU v).symm
  · rw [← idealSheaf_comap_primeDivisorMap U.ι EU, hEU]
    exact stalk_comap_eq_map U.ι E.idealSheaf u

open Classical in
/-- The index set of the snc condition at `u` for `S_U + L_U` consists of `S_U` and `L_U`. -/
private theorem eq_or_eq_of_mem_support_reducedDivisorOf {W : Scheme.{u}}
    {SU LU : MMP.Mori.PrimeDivisor W}
    (E : MMP.Mori.PrimeDivisor W)
    (hE : E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support) : E = SU ∨ E = LU := by
  rw [MMP.Intersection.support_reducedDivisorOf] at hE
  simpa using hE

open Classical in
/-- The snc condition at a point for `S_U + L_U`, from a regular system of parameters containing
local equations of the components through the point. -/
private theorem exists_sncData {W : Scheme.{u}} {SU LU : MMP.Mori.PrimeDivisor W}
    (hne : SU ≠ LU) (u : W) {n : ℕ} (z : Fin n → W.presheaf.stalk u)
    (hz : IsRegularSystemOfParameters z) (iS iL : Fin n)
    (hS : u ∈ SU.support → IdealSheafData.stalk SU.idealSheaf u = Ideal.span {z iS})
    (hL : u ∈ LU.support → IdealSheafData.stalk LU.idealSheaf u = Ideal.span {z iL})
    (hSL : u ∈ SU.support → u ∈ LU.support → iS ≠ iL) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk u)
      (j : {E : MMP.Mori.PrimeDivisor W //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (j E)} := by
  refine ⟨n, z, fun E => if E.1 = SU then iS else iL, hz, ?_, fun E => ?_⟩
  · rintro ⟨E, hE, huE⟩ ⟨E', hE', huE'⟩ h
    apply Subtype.ext
    simp only at h ⊢
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl <;>
      rcases eq_or_eq_of_mem_support_reducedDivisorOf E' hE' with rfl | rfl
    · rfl
    · simp only [if_neg hne.symm, ↓reduceIte] at h
      exact absurd h (hSL huE huE')
    · simp only [if_neg hne.symm, ↓reduceIte] at h
      exact absurd h.symm (hSL huE' huE)
    · rfl
  · obtain ⟨E, hE, huE⟩ := E
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl
    · simp only [↓reduceIte]
      exact hS huE
    · simp only [if_neg hne.symm]
      exact hL huE

open Classical in
/-- The snc condition at a point outside `S_U` and `L_U`. -/
private theorem exists_sncData_of_notMem {W : Scheme.{u}} {SU LU : MMP.Mori.PrimeDivisor W}
    (u : W) [IsRegularLocalRing (W.presheaf.stalk u)] (hS : u ∉ SU.support)
    (hL : u ∉ LU.support) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk u)
      (j : {E : MMP.Mori.PrimeDivisor W //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (j E)} := by
  have hempty : ∀ E : {E : MMP.Mori.PrimeDivisor W //
      E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support}, False := by
    rintro ⟨E, hE, huE⟩
    rcases eq_or_eq_of_mem_support_reducedDivisorOf E hE with rfl | rfl
    exacts [hS huE, hL huE]
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (W.presheaf.stalk u)
  exact ⟨n, z, fun E => (hempty E).elim, hz, fun E => (hempty E).elim,
    fun E => (hempty E).elim⟩

/-! ### The neighbourhood `U` -/

open Classical in
/-- The existence of a completion `t` of `x` to a regular system of parameters of `𝒪_{Y,η_V}` and
of an open neighbourhood `U ⊆ Y°` of `η_V` on which `x`, `t` cut out an snc divisor
`(S ∩ U) + {t = 0}` with `V ∩ U` a component of `S ∩ {t = 0}`. -/
private theorem exists_regularSystemOfParameters_isSNC
    {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y]
    (L : Finset (MMP.Mori.PrimeDivisor Y)) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y)
    (hY : IsNormalVariety k sY) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support)
    (hdim2 : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L)
    (x : Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    (∃ t : Y.presheaf.stalk V.isIrreducible.genericPoint, IsRegularSystemOfParameters ![x, t] ∧
      ∃ (U : Y.Opens) (hηU : V.isIrreducible.genericPoint ∈ U),
        (U : Set Y) ⊆ oneLabelSmoothLocus L ∧
        (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) ∧
        ∃ (xU tU : Γ(U.toScheme, ⊤)),
          U.ι.stalkMap ⟨_, hηU⟩ x = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial xU ∧
          U.ι.stalkMap ⟨_, hηU⟩ t = U.toScheme.presheaf.germ ⊤ ⟨_, hηU⟩ trivial tU ∧
          ∃ (SU LU : MMP.Mori.PrimeDivisor U.toScheme) (Z : IrreducibleCloseds U.toScheme),
            OpenWeilRestriction.primeDivisorMap U.ι SU = S ∧
            SU.support = U.ι ⁻¹' S.support ∧
            (∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU}) ∧
            (∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
              Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU}) ∧
            SU ≠ LU ∧
            (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) ∧
            (Z : Set U.toScheme) = U.ι ⁻¹' V ∧
            Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
              (Z : Set U.toScheme)) := by
  have hYv : MMP.Mori.IsVariety k sY := hY.1
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI := isNoetherian_of_isVariety hYv
  have hdim2' := hdim2
  have hηgen' := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  revert x hx hη hdim2' hηgen'
  generalize V.isIrreducible.genericPoint = η
  intro hη x hx hdim2 hηgen
  have hηY := mem_oneLabelSmoothLocus_iff.1 hη
  haveI : IsRegularLocalRing (Y.presheaf.stalk η) := hηY.1
  have hηV : η ∈ (V : Set Y) := hηgen.mem
  have hηS : η ∈ S.support := hVS hηV
  obtain ⟨hxm, hx2⟩ := mem_maximalIdeal_notMem_sq_of_regular S hηS (hηY.2.1 S hS) hx
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair hdim2 hxm hx2
  refine ⟨t, ht, ?_⟩
  -- the prime divisor `L' = {t = 0}` of `Y`
  obtain ⟨L', hηL', hL'⟩ := exists_primeDivisor_stalk_eq_span ht 1
  have ht1 : (![x, t] : Fin 2 → _) 1 = t := rfl
  have ht0 : (![x, t] : Fin 2 → _) 0 = x := rfl
  rw [ht1] at hL'
  -- sections representing `x` and `t`
  obtain ⟨Wx, hηWx, x', hx'⟩ := Y.presheaf.germ_exist (x := η) x
  obtain ⟨Wt, hηWt, t', ht'⟩ := Y.presheaf.germ_exist (x := η) t
  set W0 : Y.Opens := Wx ⊓ Wt
  have hηW0 : η ∈ W0 := ⟨hηWx, hηWt⟩
  set x0 : Γ(Y, W0) := Y.presheaf.map (homOfLE inf_le_left).op x'
  set t0 : Γ(Y, W0) := Y.presheaf.map (homOfLE inf_le_right).op t'
  have hxη : Y.presheaf.germ W0 η hηW0 x0 = x :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans hx'
  have htη : Y.presheaf.germ W0 η hηW0 t0 = t :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ht'
  -- the local equations spread out
  obtain ⟨W1, hηW1, hW1, hS1⟩ :=
    exists_forall_stalk_eq_span S.idealSheaf x0 hηW0 (by rwa [hxη])
  obtain ⟨W2, hηW2, hW2, hL1⟩ :=
    exists_forall_stalk_eq_span L'.idealSheaf t0 hηW0 (by rwa [htη])
  -- `L'` is regular near `η`
  obtain ⟨W3, hηW3, hW3⟩ := exists_isOpen_forall_isRegularLocalRing_quotient sY L'.idealSheaf
    hηL' (by
      rw [hL', ← ht1]
      exact MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters
        ht 1)
  -- `S ∩ L'` is regular near `η`
  have hm : Ideal.span {x} ⊔ Ideal.span {t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [← Ideal.span_insert]; exact span_pair_eq ht
  have hTη : IdealSheafData.stalk (S.idealSheaf + L'.idealSheaf) η =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [stalk_add, hx, hL', hm]
  have hmemT : ∀ y : Y, IdealSheafData.stalk (S.idealSheaf + L'.idealSheaf) y ≠ ⊤ →
      y ∈ (S.idealSheaf + L'.idealSheaf).support := fun y hy => by
    by_contra h
    exact hy ((IdealSheafData.stalk_eq_top_iff_notMem_support _ y).2 h)
  obtain ⟨W4, hηW4, hW4⟩ := exists_isOpen_forall_isRegularLocalRing_quotient sY
    (S.idealSheaf + L'.idealSheaf) (hmemT η (by rw [hTη]; exact Ideal.IsPrime.ne_top'))
    (by
      rw [hTη]
      exact MMP.Flips.isRegularLocalRing_of_isField (A := IsLocalRing.ResidueField _)
        (Field.toIsField _))
  -- near `η`, `S ∩ L'` lies in `V`
  have hgen : ∀ ξ ∈ (S.support ∩ L'.support : Set Y), ξ ⤳ η → ξ = η := by
    rintro ξ ⟨hξS, hξL⟩ h
    have h1 := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes S.idealSheaf h).1 hξS
    have h2 := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes L'.idealSheaf h).1 hξL
    rw [hx] at h1
    rw [hL'] at h2
    have hP : MMP.Intersection.primeOfSpecializes h =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk η) :=
      le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        (hm ▸ sup_le h1 h2)
    have hηξ : η ⤳ ξ := MMP.Intersection.specializes_of_primeOfSpecializes_le
      (specializes_refl η) h
      (by rw [hP]; exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
    exact (h.antisymm hηξ).eq
  obtain ⟨W5, hW5o, hηW5, hW5⟩ :=
    exists_isOpen_inter_subset_closure
      (S.idealSheaf.support.isClosed.inter L'.idealSheaf.support.isClosed) hgen
  -- the other labels
  set C : Set Y := ⋃ S' ∈ L, ⋃ (_ : S' ≠ S), (S'.support : Set Y)
  have hC : IsClosed C := isClosed_biUnion_finset fun S' _ =>
    isClosed_iUnion_of_finite fun _ => S'.idealSheaf.support.isClosed
  have hηC : η ∉ C := by
    simp only [C, Set.mem_iUnion]
    rintro ⟨S', hS'L, hne, hηS'⟩
    exact hηY.2.2 S hS S' hS'L hne.symm ⟨hηS, hηS'⟩
  -- the neighbourhood `U`
  set U : Y.Opens := W1 ⊓ W2 ⊓ W3 ⊓ W4 ⊓ ⟨W5, hW5o⟩ ⊓
    ⟨oneLabelSmoothLocus L, isOpen_oneLabelSmoothLocus sY L⟩ ⊓ ⟨Cᶜ, hC.isOpen_compl⟩ with hU_def
  have hUmem : ∀ y ∈ U, y ∈ W1 ∧ y ∈ W2 ∧ y ∈ W3 ∧ y ∈ W4 ∧ y ∈ W5 ∧
      y ∈ oneLabelSmoothLocus L ∧ y ∉ C := fun y hy =>
    ⟨hy.1.1.1.1.1.1, hy.1.1.1.1.1.2, hy.1.1.1.1.2, hy.1.1.1.2, hy.1.1.2, hy.1.2, hy.2⟩
  have hηU : η ∈ U := ⟨⟨⟨⟨⟨⟨hηW1, hηW2⟩, hηW3⟩, hηW4⟩, hηW5⟩, hη⟩, hηC⟩
  have hUW0 : U ≤ W0 := fun y hy => hW1 (hUmem y hy).1
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  -- pointwise facts on `U`
  have hregU : ∀ y ∈ U, IsRegularLocalRing (Y.presheaf.stalk y) := fun y hy =>
    (mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.2.2.2.2.1).1
  have hSfact : ∀ y (hy : y ∈ U), y ∈ S.support →
      Y.presheaf.germ W0 y (hUW0 hy) x0 ∈ IsLocalRing.maximalIdeal _ ∧
        Y.presheaf.germ W0 y (hUW0 hy) x0 ≠ 0 ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0}) :=
    fun y hy hyS =>
    haveI := hregU y hy
    localEquation_spec S hyS ((mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.2.2.2.2.1).2.1 S hS)
      (hS1 y (hUmem y hy).1)
  have hLfact : ∀ y (hy : y ∈ U), y ∈ L'.support →
      Y.presheaf.germ W0 y (hUW0 hy) t0 ∈ IsLocalRing.maximalIdeal _ ∧
        Y.presheaf.germ W0 y (hUW0 hy) t0 ≠ 0 ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0}) :=
    fun y hy hyL => by
    haveI := hregU y hy
    have hst := hL1 y (hUmem y hy).2.1
    have h1 := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span L' hyL hst
    have h2 := hW3 y (hUmem y hy).2.2.1 hyL
    rw [hst] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hSLfact : ∀ y (hy : y ∈ U), y ∈ S.support → y ∈ L'.support →
      Y.presheaf.germ W0 y (hUW0 hy) t0 ∉ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0} ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ (Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0} ⊔
          Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0})) := fun y hy hyS hyL => by
    have hstS := hS1 y (hUmem y hy).1
    have hstL := hL1 y (hUmem y hy).2.1
    refine ⟨fun hba => ?_, ?_⟩
    · have hs : S.genericPoint ⤳ y :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support S hyS
      have hsU : S.genericPoint ∈ U := hs.mem_open U.isOpen hy
      have hsS : S.genericPoint ∈ S.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have hsL : S.genericPoint ∈ L'.support := by
        by_contra hn
        have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support L'.idealSheaf _).2 hn
        rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes L'.idealSheaf hs, hstL] at htop
        have hle : Ideal.map (Y.presheaf.stalkSpecializes hs).hom
            (Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) t0}) ≤
            Ideal.map (Y.presheaf.stalkSpecializes hs).hom
              (IdealSheafData.stalk S.idealSheaf y) :=
          Ideal.map_mono (by rw [hstS, Ideal.span_le, Set.singleton_subset_iff]; exact hba)
        rw [← MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes S.idealSheaf hs,
          MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, htop] at hle
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
      have hsV : S.genericPoint ∈ closure {η} := hW5 ⟨(hUmem _ hsU).2.2.2.2.1, hsS, hsL⟩
      have hηs : η ⤳ S.genericPoint := specializes_iff_mem_closure.2 hsV
      have hsη : S.genericPoint ⤳ η :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support S hηS
      have heq : S.genericPoint = η := (hsη.antisymm hηs).eq
      have h2 : ((Order.coheight η : ℕ∞) : WithBot ℕ∞) = 2 := by
        rwa [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      rw [← heq, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
      exact absurd h2 (by decide)
    · have hT := hW4 y (hUmem y hy).2.2.2.1
      rw [stalk_add, hstS, hstL] at hT
      haveI := hregU y hy
      refine hT (hmemT y ?_)
      rw [stalk_add, hstS, hstL]
      exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 (hSfact y hy hyS).1))
          (Ideal.span_le.2 (Set.singleton_subset_iff.2 (hLfact y hy hyL).1)))
  -- the data on `U`
  set xU := sectionOn hUW0 x0
  set tU := sectionOn hUW0 t0
  obtain ⟨SU, hSUmap, hSUsupp, hSUstalk⟩ := exists_primeDivisor_restrict U S hηU hηS
  obtain ⟨LU, hLUmap, hLUsupp, hLUstalk⟩ := exists_primeDivisor_restrict U L' hηU hηL'
  have hSUx : ∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
      Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU} := fun u => by
    rw [hSUstalk, hS1 (U.ι u) (hUmem _ u.2).1, Ideal.map_span, Set.image_singleton, germ_sectionOn]
  have hLUt : ∀ u : U.toScheme, IdealSheafData.stalk LU.idealSheaf u =
      Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial tU} := fun u => by
    rw [hLUstalk, hL1 (U.ι u) (hUmem _ u.2).2.1, Ideal.map_span, Set.image_singleton,
      germ_sectionOn]
  have hne : SU ≠ LU := by
    intro h
    have hSL : S = L' := by rw [← hSUmap, ← hLUmap, h]
    apply MMP.Resolution.notMem_span_singleton_of_isRegularSystemOfParameters ht
      (m := 0) (m' := 1) (by decide)
    rw [ht1, ht0, ← hx, hSL, hL']
    exact Ideal.mem_span_singleton_self t
  have hpt : ∀ u : U.toScheme, ∃ (n : ℕ) (z : Fin n → U.toScheme.presheaf.stalk u)
      (jj : {E : MMP.Mori.PrimeDivisor U.toScheme //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (jj E)} := by
    intro u
    haveI : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hregU _ u.2
    haveI : IsRegularLocalRing (Y.presheaf.stalk u.1) := hregU _ u.2
    let e := (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
    have hex : e (Y.presheaf.germ W0 (U.ι u) (hUW0 u.2) x0) =
        U.toScheme.presheaf.germ ⊤ u trivial xU := (germ_sectionOn hUW0 x0 u).symm
    have het : e (Y.presheaf.germ W0 (U.ι u) (hUW0 u.2) t0) =
        U.toScheme.presheaf.germ ⊤ u trivial tU := (germ_sectionOn hUW0 t0 u).symm
    have hSu : u ∈ SU.support ↔ U.ι u ∈ S.support := by rw [hSUsupp]; rfl
    have hLu : u ∈ LU.support ↔ U.ι u ∈ L'.support := by rw [hLUsupp]; rfl
    by_cases hyS : U.ι u ∈ S.support <;> by_cases hyL : U.ι u ∈ L'.support
    · obtain ⟨hxm', hx0', hxr⟩ := hSfact _ u.2 hyS
      obtain ⟨htm', -, -⟩ := hLfact _ u.2 hyL
      obtain ⟨hba, hr2⟩ := hSLfact _ u.2 hyS hyL
      obtain ⟨n, z, hz, hz0, hz1⟩ :=
        exists_isRegularSystemOfParameters_cons_cons hxm' htm' hx0' hba hxr hr2
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 1
        (fun _ => ?_) (fun _ => ?_)
        (fun _ _ => show (0 : Fin (n + 2)) ≠ 1 by simp)
      · rw [hSUx, ← hex, hz0]; rfl
      · rw [hLUt, ← het, hz1]; rfl
    · obtain ⟨hxm', hx0', hxr⟩ := hSfact _ u.2 hyS
      obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_cons hxm' hx0' hxr
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 0
        (fun _ => ?_)
        (fun h => absurd (hLu.1 h) hyL) (fun _ h => absurd (hLu.1 h) hyL)
      rw [hSUx, ← hex, hz0]; rfl
    · obtain ⟨htm', ht0', htr⟩ := hLfact _ u.2 hyL
      obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_cons htm' ht0' htr
      refine exists_sncData hne u _ (isRegularSystemOfParameters_map_ringEquiv e hz) 0 0
        (fun h => absurd (hSu.1 h) hyS) (fun _ => ?_) (fun h => absurd (hSu.1 h) hyS)
      rw [hLUt, ← het, hz0]; rfl
    · haveI : IsRegularLocalRing (U.toScheme.presheaf.stalk u) := IsRegularLocalRing.of_ringEquiv e
      exact exists_sncData_of_notMem u (fun h => hyS (hSu.1 h)) (fun h => hyL (hLu.1 h))
  have hsnc : (MMP.Intersection.reducedDivisorOf {SU, LU}).IsSNC (U.ι ≫ sY) :=
    isSNC_of_forall_exists (isSmoothScheme_ι_comp hYv U hregU) hpt
  -- the component `Z = V ∩ U`
  let Z : IrreducibleCloseds U.toScheme :=
    ⟨U.ι ⁻¹' V, ⟨⟨⟨η, hηU⟩, hηV⟩, V.isIrreducible.2.preimage U.ι.isOpenEmbedding⟩,
      V.isClosed.preimage U.ι.continuous⟩
  have hVL : (V : Set Y) ⊆ L'.support := by
    rw [← hηgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηL') L'.idealSheaf.support.isClosed
  have hZmax : Maximal (fun T : Set U.toScheme => IsIrreducible T ∧ T ⊆ SU.support ∩ LU.support)
      (Z : Set U.toScheme) := by
    refine ⟨⟨Z.isIrreducible, fun v hv => ⟨?_, ?_⟩⟩, fun T hT _ v hv => ?_⟩
    · rw [hSUsupp]; exact hVS hv
    · rw [hLUsupp]; exact hVL hv
    · obtain ⟨h1, h2⟩ := hT.2 hv
      rw [hSUsupp] at h1
      rw [hLUsupp] at h2
      have := hW5 ⟨(hUmem _ v.2).2.2.2.2.1, h1, h2⟩
      rwa [hηgen.def] at this
  refine ⟨U, hηU, fun y hy => (hUmem y hy).2.2.2.2.2.1,
    fun S' hS'L hne' => Set.disjoint_left.2 fun y hyU hyS' => (hUmem y hyU).2.2.2.2.2.2 ?_,
    xU, tU, ?_, ?_, SU, LU, Z, hSUmap, hSUsupp, hSUx, hLUt, hne, hsnc, rfl, hZmax⟩
  · simp only [C, Set.mem_iUnion]
    exact ⟨S', hS'L, hne', hyS'⟩
  · exact (congrArg _ hxη.symm).trans (germ_sectionOn hUW0 x0 ⟨η, hηU⟩).symm
  · exact (congrArg _ htη.symm).trans (germ_sectionOn hUW0 t0 ⟨η, hηU⟩).symm

end Neighbourhood

end Port

section Local

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-! ### Open immersions and birational morphisms -/

/-- An open immersion restricted to its image is an isomorphism. -/
private theorem isIso_ι_restrict_self {X : Scheme.{u}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    refine ⟨fun y => ?_⟩
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inclusion of a nonempty open subscheme of an integral scheme is birational. -/
private theorem isBirationalMorphism_ι {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] : IsBirationalMorphism U.ι := by
  haveI := isIso_ι_restrict_self U
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨x⟩ := ‹Nonempty U›
  exact isBirationalMorphism_of_isIso_restrict U.ι U ⟨x.1, x.2⟩

omit [IsIntegral Y] in
/-- The extension of function fields of a composite is the composite of the extensions. -/
private theorem functionFieldMap_comp_apply {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] (c : Z.functionField) :
    functionFieldMap (a ≫ b) c = functionFieldMap a (functionFieldMap b c) := by
  obtain ⟨s, rfl⟩ := MMP.Positivity.DivisorOver.algebraMap_stalk_surjective_of_eq_genericPoint
    ((a ≫ b) (genericPoint X)) (map_genericPoint_of_isDominant (a ≫ b)) c
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk (a ≫ b) (genericPoint X) s]
  erw [MMP.Mori.functionFieldMap_algebraMap_stalk b (a (genericPoint X)) s,
    MMP.Mori.functionFieldMap_algebraMap_stalk a (genericPoint X)]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- A divisor over an open subscheme `U ⊆ Y` is a divisor over `Y`, with the corresponding
valuation. -/
private theorem exists_divisorOver_comp_ι (U : Y.Opens) [Nonempty U] [IsDominant U.ι]
    (D : DivisorOver k (U.ι ≫ sY)) :
    ∃ D' : DivisorOver k sY, D'.valuation = D.valuation.comap (functionFieldMap U.ι) := by
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hnv : IsNormalVariety k ((D.f ≫ U.ι) ≫ sY) := by
    simpa only [Category.assoc] using D.isNormalVariety
  let D' : DivisorOver k sY :=
    ⟨D.Y, D.f ≫ U.ι, hnv, MMP.Mori.IsPair.isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_ι U), D.E⟩
  refine ⟨D', ?_⟩
  haveI := D'.isDominant
  ext c
  rw [Valuation.comap_apply]
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ U.ι) c) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap U.ι c))
  rw [functionFieldMap_comp_apply]

/-! ### Proper models of divisors (Nagata compactification) -/

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {Y P : Scheme.{u}}
    {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact NoetherianSpace.finite_irreducibleComponents

/-- If `t ≫ g` is birational and `t` is an open immersion of integral schemes, `g` is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, hW, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by
    rw [hc]
    infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  obtain ⟨w, hw⟩ := hW
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ⟨t w, w, hw, rfl⟩
    ⟨_, ⟨w, hw⟩, rfl⟩ hUV ?_
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(t.isoImage W).hom w, ?_⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

/-- **Proper models.** Every divisor `(Y', f, E)` over a normal variety `X` has the valuation of
a divisor over `X` with `f` proper: compactify `f` by Nagata's theorem, `Y' ⊆ P → X`, and
replace `P` by the normalization of `P` in `Y'`. -/
private theorem exists_properDivisorOver_valuation_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    ∃ E : MMP.Flips.ProperDivisorOver k sX, E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  obtain ⟨c, hjq⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace D.f
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ : ∃ (P : Scheme.{u}) (j : D.Y ⟶ P) (p : P ⟶ X),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsProper p ∧ j ≫ p = D.f :=
    ⟨c.space, c.immersion, c.toBase, inferInstance, hjq, inferInstance, Over.w c.obj.hom⟩
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p ≫ sX) j
  set t := j.toNormalization
  let g := j.fromNormalization ≫ p
  have htg : t ≫ g = D.f := by
    simp only [g, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hgv : IsNormalVariety k (g ≫ sX) :=
    ⟨(isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm⟩
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism)
  let D' : DivisorOver k sX :=
    ⟨_, g, hgv, hgb, OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨⟨D', inferInstance⟩, (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι (h : IsNormalVariety k sY) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ sY) := by
  have := h.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The coefficients of the restriction of a divisor to an open subscheme. -/
private theorem coeff_inverseTransformDivisor_ι {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor U) :
    (inverseTransformDivisor U.ι B).coeff P =
      B.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) := by
  rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen, DivisorWithCoeffs.coeff_restrictOpen]

/-- On a smooth open subscheme the restriction of a pair is a pair. -/
private theorem isPair_restrict {Θ : QDivisor Y} (hP : MMP.Fourfold.IsPair sY Θ) (U : Y.Opens)
    [Nonempty U] (hsm : IsSmoothScheme (U.ι ≫ sY)) {d : ℕ}
    (hd : topologicalKrullDim U.toScheme = d) :
    MMP.Fourfold.IsPair (U.ι ≫ sY) (inverseTransformDivisor U.ι Θ) := by
  have hUv : IsNormalVariety k (U.ι ≫ sY) := isNormalVariety_ι hP.isPair.1 U
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sY) := hUv.1
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sY)
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (U.ι ≫ sY) hsm hd
  refine ⟨hP.isAlgClosed, hP.charZero,
    ⟨hUv, d, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩, fun P => ?_⟩
  rw [coeff_inverseTransformDivisor_ι]
  exact hP.nonneg _

/-- **The klt condition is local**: the restriction of a klt pair to an open subscheme on which
it is a pair is klt. A divisor over `U` is a divisor over `Y`, which has a proper model; its log
discrepancy over `(U, Θ|_U)` is its log discrepancy over `(Y, Θ)`. -/
private theorem isKltPair_restrict {Θ : QDivisor Y} (hklt : IsKltPair sY Θ) (U : Y.Opens)
    [Nonempty U] [IsDominant U.ι]
    (hP : MMP.Fourfold.IsPair (U.ι ≫ sY) (inverseTransformDivisor U.ι Θ)) :
    IsKltPair (U.ι ≫ sY) (inverseTransformDivisor U.ι Θ) := by
  have hY : IsNormalVariety k sY := hklt.1.isPair.1
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  refine ⟨hP, fun n D a ha => ?_⟩
  obtain ⟨DY, hDY⟩ := exists_divisorOver_comp_ι U D
  obtain ⟨E, hE⟩ := exists_properDivisorOver_valuation_eq hY DY
  have hmap := map_genericPoint_eq_of_comap_eq (π := U.ι) D E.toDivisorOver
    (by rw [← hDY]; exact hE.symm)
  have hZ : MMP.Intersection.IsCentre k sY E.toDivisorOver.valuation E.toDivisorOver.center :=
    ⟨E.toDivisorOver, E.isProper, rfl, rfl⟩
  have hUZ : ((U : Set Y) ∩ E.toDivisorOver.center).Nonempty := by
    refine ⟨E.toDivisorOver.f E.toDivisorOver.E.genericPoint, ?_, ?_⟩
    · rw [← hmap]
      exact (D.f D.E.genericPoint).2
    · rw [E.toDivisorOver.center_eq_closure_genericPoint]
      exact subset_closure rfl
  obtain ⟨n', D', -, -, hl⟩ := (isValuationLogDiscrepancy_restrict_iff sY hklt.1
    ⟨E.toDivisorOver, E.isProper, rfl⟩ hZ U hUZ (ξU := D.valuation)
    (by rw [← hDY]; exact hE.symm.trans rfl) a).1 ⟨n, D, ha.2.1, rfl, ha⟩
  exact hklt.2 n' D' a hl

/-- **The identity log-smooth datum on a smooth open subset.** If `U ⊆ Y` is smooth and `T` is a
reduced snc divisor on `U` containing the support of `Θ|_U`, then `(𝟙_U, T)` is a log-smooth
datum for `(U, Θ|_U)`. -/
private theorem isLogSmoothDatum_id {Θ : QDivisor Y} (hklt : IsKltPair sY Θ) (U : Y.Opens)
    [Nonempty U] [IsDominant U.ι] (hsm : IsSmoothScheme (U.ι ≫ sY)) {d : ℕ}
    (hd : topologicalKrullDim U.toScheme = d) {T : Divisor U.toScheme}
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC (U.ι ≫ sY))
    (hTΘ : (inverseTransformDivisor U.ι Θ).support ⊆ T.support) :
    IsLogSmoothDatum (U.ι ≫ sY) (inverseTransformDivisor U.ι Θ) (𝟙 U.toScheme) T := by
  classical
  haveI : CharZero k := hklt.1.charZero
  have hPU := isPair_restrict hklt.1 U hsm hd
  have hkltU := isKltPair_restrict hklt U hPU
  have hUv : IsNormalVariety k (U.ι ≫ sY) := hPU.isPair.1
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI : LocallyOfFiniteType (U.ι ≫ sY) := hUv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sY)
  haveI : IsNormal U.toScheme := hUv.2
  have hnv : IsNormalVariety k (𝟙 U.toScheme ≫ U.ι ≫ sY) := by rwa [Category.id_comp]
  have hbir : IsBirationalMorphism (𝟙 U.toScheme) := isBirationalMorphism_of_isIso _
  obtain ⟨-, n, K, hK, hq⟩ := hPU.isPair
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hPU.isPair hK
    (𝟙 U.toScheme) hnv hbir
  have hreg (x : U.toScheme) : x ∈ (𝟙 U.toScheme) ⁻¹ᵁ biregularLocus (𝟙 U.toScheme) :=
    le_biregularLocus (V := ⊤) (show IsIso ((𝟙 U.toScheme) ∣_ ⊤) from inferInstance) trivial
  refine ⟨hkltU, AlgebraicGeometry.isProjective_id _, hbir, hnv, by rwa [Category.id_comp], hT,
    by rwa [Category.id_comp], fun w hw => (hw (hreg w)).elim, n, K, BW, hBW, fun G hG => ?_⟩
  rcases genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hUv, hK, hq⟩ hnv hbir hBW hG
    with h | h
  · exact (h (hreg _)).elim
  · rw [Finset.sup_set_eq_biUnion] at h
    obtain ⟨E, hE, hx⟩ := Set.mem_iUnion₂.1 h
    have hx' : G.genericPoint ∈ (E.support : Set U.toScheme) := by simpa using hx
    have hGE : E = G := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hx'
    exact hTΘ (hGE ▸ hE)

/-- The log discrepancy of a prime divisor of `X` itself, regarded as the divisor `(X, 𝟙, P)`
over `X`, is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_id_primeDivisor [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hnv : IsNormalVariety k (𝟙 X ≫ sX))
    (hbir : IsBirationalMorphism (𝟙 X)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨X, 𝟙 X, hnv, hbir, P⟩
      (1 - (B.coeff P : ℝ)) := by
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK ⟨X, 𝟙 X, hnv, hbir, P⟩
  have hc' : c = -B.coeff P := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (inferInstance : IsProper (𝟙 X))
  rw [hc'] at h
  convert h using 1
  push_cast
  ring

/-- **The log-smooth formula on an open subset.** -/
private theorem exists_logSmoothFormula_restrict {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (U : Y.Opens) [Nonempty U] [IsDominant U.ι]
    (hU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u))
    {T : Divisor U.toScheme} (hT : MMP.Intersection.IsReducedEffective T)
    (hTs : T.IsSNC (U.ι ≫ sY))
    (hTΘ : (inverseTransformDivisor U.ι Θ).support ⊆ T.support)
    {ξ : Valuation Y.functionField ℤᵐ⁰} {a : ℝ} (ha : HasLogDiscrepancy sY Θ ξ a)
    {Z : IrreducibleCloseds Y} (hZ : MMP.Intersection.IsCentre k sY ξ Z)
    (hηU : Z.isIrreducible.genericPoint ∈ U) :
    ∃ ξU : Valuation U.toScheme.functionField ℤᵐ⁰, ξU.comap (functionFieldMap U.ι) = ξ ∧
      ∃ Z' : IrreducibleCloseds U.toScheme, MMP.Intersection.IsCentre k (U.ι ≫ sY) ξU Z' ∧
        U.ι Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint ∧
        ∃ e : ℕ, IsReducedSNCDiscrepancy (U.ι ≫ sY) T ξU e ∧
          (∀ c : ℕ, codimension Z = c →
            (c : ℝ) - (sncIndexSet T (Z' : Set U.toScheme)).card ≤ e) ∧
          (∀ j ∈ T.support, 0 < 1 - ((inverseTransformDivisor U.ι Θ).coeff j : ℝ)) ∧
          ∃ (z : sncIndexSet T (Z' : Set U.toScheme) →
              U.toScheme.presheaf.stalk Z'.isIrreducible.genericPoint)
            (m : sncIndexSet T (Z' : Set U.toScheme) → ℤ),
            (∀ j, IdealSheafData.stalk j.1.idealSheaf Z'.isIrreducible.genericPoint =
              Ideal.span {z j}) ∧
            (∀ j, ξU (algebraMap _ U.toScheme.functionField (z j)) = WithZero.exp (-m j)) ∧
            (∀ j, 1 ≤ m j) ∧ (e : ℝ) ≤ a ∧
            a = ∑ j, (m j : ℝ) * (1 - ((inverseTransformDivisor U.ι Θ).coeff j.1 : ℝ)) + e := by
  classical
  haveI : IsAlgClosed k := hΘ.1.isAlgClosed
  haveI : CharZero k := hΘ.1.charZero
  have hY : IsNormalVariety k sY := hΘ.1.isPair.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hsm := isSmoothScheme_ι_comp hY.1 U hU
  have hUv := isNormalVariety_ι hY U
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sY) := hUv.1
  haveI : LocallyOfFiniteType (U.ι ≫ sY) := hUv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sY)
  haveI : IsNormal U.toScheme := hUv.2
  obtain ⟨-, n, K, hK, -⟩ := hΘ.1.isPair
  have hdU : topologicalKrullDim U.toScheme = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (U.ι ≫ sY)
      (isBirationalMorphism_ι U)).symm.trans hK.topologicalKrullDim_eq
  have hπ := isLogSmoothDatum_id hΘ U hsm hdU hT hTs hTΘ
  obtain ⟨-, nU, KU, hKU, -⟩ := hπ.isKltPair.1.isPair
  -- the log discrepancies `aⱼ = 1 - coeff_{Tⱼ}(Θ|_U)`
  let aT : MMP.Mori.PrimeDivisor U.toScheme → ℝ :=
    fun j => 1 - ((inverseTransformDivisor U.ι Θ).coeff j : ℝ)
  have haT : ∀ j ∈ T.support, MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sY) nU
      (QDivisor.toRDivisor (inverseTransformDivisor U.ι Θ))
      ⟨U.toScheme, 𝟙 U.toScheme, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j) :=
    fun j _ => isLogDiscrepancy_id_primeDivisor hπ.isKltPair.1.isPair hKU hπ.isNormalVariety
      hπ.isBirationalMorphism j
  have haT0 : ∀ j ∈ T.support, 0 < aT j := fun j hj => hπ.isKltPair.2 _ _ _ (haT j hj)
  -- the valuation `ξ_U` and its log discrepancy over `(U, Θ|_U)`
  obtain ⟨n', D, hDξ, ha'⟩ := ha
  obtain ⟨ξU, hξU⟩ := exists_comap_eq_of_bijective
    (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
      (by simpa using (Set.univ_nonempty : (Set.univ : Set U.toScheme).Nonempty))) ξ
  have hηZ : Z.isIrreducible.genericPoint ∈ (Z : Set Y) :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  obtain ⟨n'', DU, hDUp, hDUv, hla⟩ := (isValuationLogDiscrepancy_restrict_iff sY hΘ.1
    ⟨D, ha'.2.1, hDξ.symm⟩ hZ U ⟨_, hηU, hηZ⟩ hξU a).2 ⟨n', D, ha'.2.1, hDξ, ha'⟩
  obtain rfl : n'' = nU := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hla).symm.trans
      hKU.topologicalKrullDim_eq
  -- the log-smooth formula
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨Z', hZ', e, he, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy (U.ι ≫ sY) hπ aT haT DU
      hDUp hla ξU (by
        ext c
        rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply, hDUv])
  rw [Category.id_comp] at he hZ'
  obtain ⟨e0, rfl⟩ := he.exists_eq_natCast
  -- the generic point of the centre on `U` maps to that on `Y`
  have hgen : U.ι Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint :=
    map_genericPoint_of_isCentre hZ' hZ hξU
  obtain ⟨z, m, hz, hm, hm1⟩ := exists_localEquations hsm hZ' _
    (fun j hj => (Finset.mem_filter.1 hj).2)
  have hf := hform z m hz hm
  refine ⟨ξU, hξU, Z', hZ', hgen, e0, he, fun c hc => ?_, haT0, z, m, hz, hm, hm1, ?_, hf⟩
  · refine he.sub_card_sncIndexSet_le hZ' ?_
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, ← coheight_eq_of_isOpenImmersion U.ι,
      hgen, ← MMP.Flips.codimension_eq_coheight_genericPoint, hc]
  · rw [hf]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => mul_nonneg
      (by exact_mod_cast zero_le_one.trans (hm1 j)) (haT0 _ (Finset.mem_filter.1 j.2).1).le)

/-- The restriction of the boundary to an open set: its components are restrictions of
components of `Θ`, hence of labels meeting the open set. -/
private theorem primeDivisorMap_mem_of_mem_support {Θ : QDivisor Y}
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) (U : Y.Opens)
    {P : MMP.Mori.PrimeDivisor U.toScheme} (hP : P ∈ (inverseTransformDivisor U.ι Θ).support) :
    OpenWeilRestriction.primeDivisorMap U.ι P ∈ L ∧
      ¬ Disjoint (U : Set Y) (OpenWeilRestriction.primeDivisorMap U.ι P).support := by
  have hc : Θ.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) ≠ 0 := by
    rw [← coeff_inverseTransformDivisor_ι, DivisorWithCoeffs.coeff_apply]
    exact Finsupp.mem_support_iff.1 hP
  refine ⟨hsupp (Finsupp.mem_support_iff.2 (by rwa [DivisorWithCoeffs.coeff_apply] at hc)),
    Set.not_disjoint_iff.2 ⟨U.ι P.genericPoint, P.genericPoint.2, ?_⟩⟩
  rw [← OpenWeilRestriction.genericPoint_primeDivisorMap]
  exact MMP.Flips.primeDivisor_genericPoint_mem_support _

/-- A local equation of a label at a point of `Y°`: restrict to the smooth open `Y°`. -/
private theorem exists_stalk_eq_span_of_mem_oneLabelSmoothLocus [PerfectField k]
    (hY : IsNormalVariety k sY) {L : Finset (MMP.Mori.PrimeDivisor Y)}
    (S : MMP.Mori.PrimeDivisor Y) {η : Y} (hηS : η ∈ S.support)
    (hη : η ∈ oneLabelSmoothLocus L) :
    ∃ x : Y.presheaf.stalk η, IdealSheafData.stalk S.idealSheaf η = Ideal.span {x} := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  let U : Y.Opens := ⟨oneLabelSmoothLocus L, isOpen_oneLabelSmoothLocus sY L⟩
  have hηU : η ∈ U := hη
  have hsm := isSmoothScheme_ι_comp hY.1 U (fun u hu => (mem_oneLabelSmoothLocus_iff.1 hu).1)
  obtain ⟨SU, -, hSUsupp, hSUstalk⟩ := exists_primeDivisor_restrict U S hηU hηS
  let u : U.toScheme := ⟨η, hηU⟩
  have huS : u ∈ SU.support := by rwa [hSUsupp]
  obtain ⟨π, -, hπ⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (U.ι ≫ sY) hsm SU huS
  let e := (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
  refine ⟨e.symm π, ?_⟩
  have h1 : Ideal.map e (IdealSheafData.stalk S.idealSheaf (U.ι u)) = Ideal.span {π} := by
    rw [← hπ, hSUstalk u]
    rfl
  calc IdealSheafData.stalk S.idealSheaf (U.ι u)
      = Ideal.map e.symm (Ideal.map e (IdealSheafData.stalk S.idealSheaf (U.ι u))) :=
        (Ideal.map_of_equiv e).symm
    _ = Ideal.map e.symm (Ideal.span {π}) := by rw [h1]
    _ = Ideal.span {e.symm π} := by rw [Ideal.map_span, Set.image_singleton]

/-- A neighbourhood of a point of `Y°` on exactly one label `S`, on which `S` is snc. -/
private theorem exists_singleLabel_neighbourhood {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {S : MMP.Mori.PrimeDivisor Y} (hY : IsNormalVariety k sY) [PerfectField k]
    (hS : S ∈ L) {η : Y} (hηS : η ∈ S.support) (hη : η ∈ oneLabelSmoothLocus L) :
    ∃ (U : Y.Opens), η ∈ U ∧ (U : Set Y) ⊆ oneLabelSmoothLocus L ∧
      (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) ∧
      ∃ SU : MMP.Mori.PrimeDivisor U.toScheme,
        OpenWeilRestriction.primeDivisorMap U.ι SU = S ∧ SU.support = U.ι ⁻¹' S.support ∧
        (MMP.Intersection.reducedDivisorOf {SU}).IsSNC (U.ι ≫ sY) := by
  classical
  have hYv : MMP.Mori.IsVariety k sY := hY.1
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI := isNoetherian_of_isVariety hYv
  obtain ⟨x, hx⟩ := exists_stalk_eq_span_of_mem_oneLabelSmoothLocus hY S hηS hη
  obtain ⟨W0, hηW0, x0, hx0⟩ := Y.presheaf.germ_exist (x := η) x
  obtain ⟨W1, hηW1, hW1, hS1⟩ :=
    exists_forall_stalk_eq_span S.idealSheaf x0 hηW0 (by rwa [hx0])
  set C : Set Y := ⋃ S' ∈ L, ⋃ (_ : S' ≠ S), (S'.support : Set Y)
  have hC : IsClosed C := isClosed_biUnion_finset fun S' _ =>
    isClosed_iUnion_of_finite fun _ => S'.idealSheaf.support.isClosed
  have hηY := mem_oneLabelSmoothLocus_iff.1 hη
  have hηC : η ∉ C := by
    simp only [C, Set.mem_iUnion]
    rintro ⟨S', hS'L, hne, hηS'⟩
    exact hηY.2.2 S hS S' hS'L hne.symm ⟨hηS, hηS'⟩
  set U : Y.Opens := W1 ⊓ ⟨oneLabelSmoothLocus L, isOpen_oneLabelSmoothLocus sY L⟩ ⊓
    ⟨Cᶜ, hC.isOpen_compl⟩ with hU_def
  have hUmem : ∀ y ∈ U, y ∈ W1 ∧ y ∈ oneLabelSmoothLocus L ∧ y ∉ C := fun y hy =>
    ⟨hy.1.1, hy.1.2, hy.2⟩
  have hηU : η ∈ U := ⟨⟨hηW1, hη⟩, hηC⟩
  have hUW0 : U ≤ W0 := fun y hy => hW1 (hUmem y hy).1
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hregU : ∀ y ∈ U, IsRegularLocalRing (Y.presheaf.stalk y) := fun y hy =>
    (mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.1).1
  have hSfact : ∀ y (hy : y ∈ U), y ∈ S.support →
      Y.presheaf.germ W0 y (hUW0 hy) x0 ∈ IsLocalRing.maximalIdeal _ ∧
        Y.presheaf.germ W0 y (hUW0 hy) x0 ≠ 0 ∧
        IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {Y.presheaf.germ W0 y (hUW0 hy) x0}) :=
    fun y hy hyS =>
    haveI := hregU y hy
    localEquation_spec S hyS ((mem_oneLabelSmoothLocus_iff.1 (hUmem y hy).2.1).2.1 S hS)
      (hS1 y (hUmem y hy).1)
  set xU := sectionOn hUW0 x0
  obtain ⟨SU, hSUmap, hSUsupp, hSUstalk⟩ := exists_primeDivisor_restrict U S hηU hηS
  have hSUx : ∀ u : U.toScheme, IdealSheafData.stalk SU.idealSheaf u =
      Ideal.span {U.toScheme.presheaf.germ ⊤ u trivial xU} := fun u => by
    rw [hSUstalk, hS1 (U.ι u) (hUmem _ u.2).1, Ideal.map_span, Set.image_singleton, germ_sectionOn]
  have hmemS : ∀ E, E ∈ (MMP.Intersection.reducedDivisorOf {SU}).support → E = SU := fun E hE => by
    rw [MMP.Intersection.support_reducedDivisorOf] at hE
    exact Finset.mem_singleton.1 hE
  have hpt : ∀ u : U.toScheme, ∃ (n : ℕ) (z : Fin n → U.toScheme.presheaf.stalk u)
      (jj : {E : MMP.Mori.PrimeDivisor U.toScheme //
        E ∈ (MMP.Intersection.reducedDivisorOf {SU}).support ∧ u ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf u = Ideal.span {z (jj E)} := by
    intro u
    haveI : IsRegularLocalRing (Y.presheaf.stalk (U.ι u)) := hregU _ u.2
    haveI : IsRegularLocalRing (Y.presheaf.stalk u.1) := hregU _ u.2
    let e := (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv
    have hex : e (Y.presheaf.germ W0 (U.ι u) (hUW0 u.2) x0) =
        U.toScheme.presheaf.germ ⊤ u trivial xU := (germ_sectionOn hUW0 x0 u).symm
    by_cases hyS : U.ι u ∈ S.support
    · obtain ⟨hxm', hx0', hxr⟩ := hSfact _ u.2 hyS
      obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_cons hxm' hx0' hxr
      refine ⟨n + 1, fun i => e (z i), fun _ => 0, isRegularSystemOfParameters_map_ringEquiv e hz,
        fun E E' _ => Subtype.ext ((hmemS _ E.2.1).trans (hmemS _ E'.2.1).symm), fun E => ?_⟩
      obtain ⟨E, hE, huE⟩ := E
      obtain rfl := hmemS E hE
      show IdealSheafData.stalk E.idealSheaf u = Ideal.span {e (z 0)}
      rw [hSUx, ← hex, hz0]
      rfl
    · haveI : IsRegularLocalRing (U.toScheme.presheaf.stalk u) := IsRegularLocalRing.of_ringEquiv e
      have hempty : ∀ E : {E : MMP.Mori.PrimeDivisor U.toScheme //
          E ∈ (MMP.Intersection.reducedDivisorOf {SU}).support ∧ u ∈ E.support}, False := by
        rintro ⟨E, hE, huE⟩
        rw [hmemS E hE, hSUsupp] at huE
        exact hyS huE
      obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (U.toScheme.presheaf.stalk u)
      exact ⟨n, z, fun E => (hempty E).elim, hz, fun E => (hempty E).elim,
        fun E => (hempty E).elim⟩
  have hsnc : (MMP.Intersection.reducedDivisorOf {SU}).IsSNC (U.ι ≫ sY) :=
    isSNC_of_forall_exists (isSmoothScheme_ι_comp hYv U hregU) hpt
  refine ⟨U, hηU, fun y hy => (hUmem y hy).2.1,
    fun S' hS'L hne' => Set.disjoint_left.2 fun y hyU hyS' => (hUmem y hyU).2.2 ?_,
    SU, hSUmap, hSUsupp, hsnc⟩
  simp only [C, Set.mem_iUnion]
  exact ⟨S', hS'L, hne', hyS'⟩

/-- Monomiality of weight `α` depends on the divisor and the index set only up to equality. -/
private theorem isMonomialValuationOfWeight_congr {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    [IsIntegral W] {T T' : Divisor W} (hT : T = T') {J J' : Finset (MMP.Mori.PrimeDivisor W)}
    (h : J = J')
    {Z : IrreducibleCloseds W} {z : J → W.presheaf.stalk Z.isIrreducible.genericPoint}
    {α : J → ℕ} {ξ : Valuation W.functionField ℤᵐ⁰}
    (hm : IsMonomialValuationOfWeight sW T J Z z α ξ) :
    IsMonomialValuationOfWeight sW T' J' Z (fun j => z ⟨j.1, h ▸ j.2⟩)
      (fun j => α ⟨j.1, h ▸ j.2⟩) ξ := by
  subst h hT
  exact hm

/-- `d + 2 = 4` in `WithBot ℕ∞` forces `d = 2`. -/
private theorem eq_two_of_add_two_eq_four {x : WithBot ℕ∞} (h : x + ((2 : ℕ) : ℕ∞) = 4) :
    x = 2 := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    have h2 : d + 2 = 4 := by
      have h' : ((d + 2 : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        convert h using 2 <;> norm_cast
      exact WithBot.coe_injective h'
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe d' =>
      have h3 : d' + 2 = 4 := by exact_mod_cast h2
      have : d' = 2 := by omega
      subst this
      rfl

/-- A reduced divisor with two components is the sum of the two. -/
private theorem reducedDivisorOf_pair {W : Scheme.{u}} {P Q : MMP.Mori.PrimeDivisor W}
    (h : P ≠ Q) [DecidableEq (MMP.Mori.PrimeDivisor W)] :
    MMP.Intersection.reducedDivisorOf {P, Q} =
      (Finsupp.single P 1 + Finsupp.single Q 1 : Divisor W) := by
  rw [MMP.Intersection.reducedDivisorOf, Finset.sum_pair h]

/-- An irreducible closed subset of an open subscheme whose generic point maps to that of `Z`
is the preimage of `Z`. -/
private theorem coe_eq_preimage_of_ι_genericPoint {U : Y.Opens} {Z : IrreducibleCloseds Y}
    {Z' : IrreducibleCloseds U.toScheme}
    (h : U.ι Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint) :
    (Z' : Set U.toScheme) = U.ι ⁻¹' Z := by
  have h1 := (Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed).def
  have h2 := U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
    {Z'.isIrreducible.genericPoint}
  rw [Set.image_singleton, h, (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def] at h2
  rw [← h1, h2]

/-- Valuations whose centre has its generic point in the one-label smooth locus are echoes. -/
private theorem exists_isSurfaceEcho_of_genericPoint_mem (hdim : topologicalKrullDim Y = 4)
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    {ξ : Valuation Y.functionField ℤᵐ⁰}
    (hξ : MMP.Intersection.IsExceptionalValuation k sY ξ)
    (ha : ∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sY Θ ξ a)
    {Z : IrreducibleCloseds Y} (hZ : MMP.Intersection.IsCentre k sY ξ Z)
    (hη : Z.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) :
    ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
      IsSurfaceEcho sY L S V j ξ := by
  classical
  have hklt := hΘ.1
  haveI : IsAlgClosed k := hklt.1.isAlgClosed
  haveI : CharZero k := hklt.1.charZero
  have hY : IsNormalVariety k sY := hklt.1.isPair.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  obtain ⟨a, ha2, ha⟩ := ha
  set η := Z.isIrreducible.genericPoint with hηdef
  -- the codimension `c ≥ 2` of the centre
  have hc2 : 2 ≤ codimension Z := by
    obtain ⟨D₀, hD₀p, rfl, hD₀⟩ := hξ
    rwa [isCentre_unique hY.1 hZ ⟨D₀, hD₀p, rfl, rfl⟩]
  have hcfin : codimension Z ≠ ⊤ := by
    intro htop
    have h1 : ((Order.coheight Z : ℕ∞) : WithBot ℕ∞) ≤
        Order.krullDim (IrreducibleCloseds Y) := Order.coheight_le_krullDim _
    rw [← codimension_eq_coheight, htop] at h1
    change _ ≤ topologicalKrullDim Y at h1
    rw [hdim] at h1
    exact absurd h1 (by decide)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hcfin
  replace hc := hc.symm
  have hc2' : 2 ≤ c := by exact_mod_cast hc ▸ hc2
  have hregY : ∀ u ∈ oneLabelSmoothLocus L, IsRegularLocalRing (Y.presheaf.stalk u) :=
    fun u hu => (mem_oneLabelSmoothLocus_iff.1 hu).1
  by_cases hS : ∃ S ∈ L, η ∈ S.support
  swap
  · -- no label passes through `η`: then `a(ξ) = e(ξ) ≥ c ≥ 2`
    exfalso
    simp only [not_exists, not_and] at hS
    let C : Set Y := ⋃ S ∈ L, (S.support : Set Y)
    have hC : IsClosed C := isClosed_biUnion_finset fun S _ => S.idealSheaf.support.isClosed
    let U : Y.Opens := ⟨oneLabelSmoothLocus L ∩ Cᶜ,
      (isOpen_oneLabelSmoothLocus sY L).inter hC.isOpen_compl⟩
    have hηU : η ∈ U := ⟨hη, fun h => by
      obtain ⟨S, hSL, hηS⟩ := Set.mem_iUnion₂.1 h
      exact hS S hSL hηS⟩
    haveI : Nonempty U := ⟨⟨η, hηU⟩⟩
    haveI := isDominant_ι_of_nonempty U
    have hTΘ : (inverseTransformDivisor U.ι Θ).support ⊆
        (MMP.Intersection.reducedDivisorOf
          (∅ : Finset (MMP.Mori.PrimeDivisor U.toScheme))).support := by
      intro P hP
      obtain ⟨hPL, hPU⟩ := primeDivisorMap_mem_of_mem_support hsupp U hP
      exact absurd (Set.disjoint_left.2 fun y hyU hyS => hyU.2 (Set.mem_iUnion₂.2 ⟨_, hPL, hyS⟩))
        hPU
    have hregU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u) := fun u hu => hregY u hu.1
    have hsm := isSmoothScheme_ι_comp hY.1 U hregU
    haveI : LocallyOfFinitePresentation (U.ι ≫ sY) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sY)).mpr inferInstance
    have hsnc : (MMP.Intersection.reducedDivisorOf
        (∅ : Finset (MMP.Mori.PrimeDivisor U.toScheme))).IsSNC (U.ι ≫ sY) := by
      rw [MMP.Intersection.reducedDivisorOf, Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
    obtain ⟨ξU, -, Z', -, -, e, -, hec, -, -, -, -, -, -, hea, -⟩ :=
      exists_logSmoothFormula_restrict hklt U hregU
        (MMP.Intersection.isReducedEffective_reducedDivisorOf _) hsnc hTΘ ha hZ hηU
    have hJ : sncIndexSet (MMP.Intersection.reducedDivisorOf
        (∅ : Finset (MMP.Mori.PrimeDivisor U.toScheme))) (Z' : Set U.toScheme) = ∅ :=
      Finset.subset_empty.1 ((Finset.filter_subset _ _).trans
        (by rw [MMP.Intersection.support_reducedDivisorOf]))
    have h1 := hec c hc
    rw [hJ, Finset.card_empty] at h1
    have : (2 : ℝ) ≤ c := by exact_mod_cast hc2'
    push_cast at h1
    linarith
  obtain ⟨S, hSL, hηS⟩ := hS
  -- the restriction of `Θ` to a neighbourhood meeting no other label is supported on `S`
  have hΘU : ∀ (U : Y.Opens), (∀ S' ∈ L, S' ≠ S → Disjoint (U : Set Y) S'.support) →
      ∀ (SU : MMP.Mori.PrimeDivisor U.toScheme), OpenWeilRestriction.primeDivisorMap U.ι SU = S →
        (inverseTransformDivisor U.ι Θ).support ⊆ {SU} := by
    intro U hUL SU hSUmap P hP
    obtain ⟨hPL, hPU⟩ := primeDivisorMap_mem_of_mem_support hsupp U hP
    have hPS : OpenWeilRestriction.primeDivisorMap U.ι P = S := by
      by_contra hne
      exact hPU (hUL _ hPL hne)
    rw [Finset.mem_singleton]
    exact OpenWeilRestriction.primeDivisorMap_injective U.ι (hPS.trans hSUmap.symm)
  -- Step 1: the centre is a surface, `c = 2`
  have hc_le : c ≤ 2 := by
    obtain ⟨U, hηU, hUY, hUL, SU, hSUmap, -, hsnc1⟩ :=
      exists_singleLabel_neighbourhood hY hSL hηS hη
    haveI : Nonempty U := ⟨⟨η, hηU⟩⟩
    haveI := isDominant_ι_of_nonempty U
    have hregU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u) := fun u hu => hregY u (hUY hu)
    have hTΘ : (inverseTransformDivisor U.ι Θ).support ⊆
        (MMP.Intersection.reducedDivisorOf {SU}).support := by
      rw [MMP.Intersection.support_reducedDivisorOf]
      exact hΘU U hUL SU hSUmap
    obtain ⟨ξU, -, Z', -, -, e, -, hec, -, -, -, -, -, -, hea, -⟩ :=
      exists_logSmoothFormula_restrict hklt U hregU
        (MMP.Intersection.isReducedEffective_reducedDivisorOf _) hsnc1 hTΘ ha hZ hηU
    have hcard : (sncIndexSet (MMP.Intersection.reducedDivisorOf {SU})
        (Z' : Set U.toScheme)).card ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (by rw [MMP.Intersection.support_reducedDivisorOf]; simp)
    have h1 := sub_le_iff_le_add'.1 (hec c hc)
    norm_cast at h1
    have he : e < 2 := by exact_mod_cast hea.trans_lt ha2
    omega
  have hc2'' : c = 2 := le_antisymm hc_le hc2'
  -- Step 2: the monomial valuation of weight `(j, 1)` for `S + {t = 0}`
  have hdim2 : ringKrullDim (Y.presheaf.stalk η) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, ← MMP.Flips.codimension_eq_coheight_genericPoint, hc,
      hc2'']
    rfl
  obtain ⟨x, hx⟩ := exists_stalk_eq_span_of_mem_oneLabelSmoothLocus hY S hηS hη
  have hVS : (Z : Set Y) ⊆ S.support := by
    rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηS) S.idealSheaf.support.isClosed
  obtain ⟨-, -, U, hηU, hUY, hUL, -, -, -, -, SU, LU, ZU, hSUmap, hSUsupp, -, -, hne, hsnc₂, hZU,
    hZUmax⟩ := exists_regularSystemOfParameters_isSNC sY L S Z hY hSL hVS hdim2 hη x hx
  haveI : Nonempty U := ⟨⟨η, hηU⟩⟩
  haveI := isDominant_ι_of_nonempty U
  have hregU : ∀ u ∈ U, IsRegularLocalRing (Y.presheaf.stalk u) := fun u hu => hregY u (hUY hu)
  have hsm := isSmoothScheme_ι_comp hY.1 U hregU
  have hΘS := hΘU U hUL SU hSUmap
  have hTΘ : (inverseTransformDivisor U.ι Θ).support ⊆
      (MMP.Intersection.reducedDivisorOf {SU, LU}).support := by
    rw [MMP.Intersection.support_reducedDivisorOf]
    exact hΘS.trans (by simp)
  obtain ⟨ξU, hξU, Z', hZ', hZ'η, e, he, -, haT, z, m, hz, hm, hm1, -, hf⟩ :=
    exists_logSmoothFormula_restrict hklt U hregU
      (MMP.Intersection.isReducedEffective_reducedDivisorOf _) hsnc₂ hTΘ ha hZ hηU
  have hZ'U : Z' = ZU :=
    IrreducibleCloseds.ext (by rw [coe_eq_preimage_of_ι_genericPoint hZ'η, hZU])
  subst hZ'U
  have hJ : sncIndexSet (MMP.Intersection.reducedDivisorOf {SU, LU}) (Z' : Set U.toScheme) =
      {SU, LU} := by
    unfold sncIndexSet
    rw [MMP.Intersection.support_reducedDivisorOf]
    refine Finset.filter_true_of_mem fun E hE => ?_
    rcases Finset.mem_insert.1 hE with rfl | hE
    · exact fun z hz => (hZUmax.1.2 hz).1
    · rw [Finset.mem_singleton.1 hE]
      exact fun z hz => (hZUmax.1.2 hz).2
  set jS : sncIndexSet (MMP.Intersection.reducedDivisorOf {SU, LU}) (Z' : Set U.toScheme) :=
    ⟨SU, by rw [hJ]; simp⟩
  set jL : sncIndexSet (MMP.Intersection.reducedDivisorOf {SU, LU}) (Z' : Set U.toScheme) :=
    ⟨LU, by rw [hJ]; simp⟩
  have hjSL : jS ≠ jL := fun h => hne (congrArg Subtype.val h)
  have hLcoeff : ((inverseTransformDivisor U.ι Θ).coeff LU : ℝ) = 0 := by
    have : LU ∉ (inverseTransformDivisor U.ι Θ).support := fun h =>
      hne (Finset.mem_singleton.1 (hΘS h)).symm
    rw [Finsupp.notMem_support_iff] at this
    rw [DivisorWithCoeffs.coeff_apply, this]
    simp
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (m j : ℝ) *
      (1 - ((inverseTransformDivisor U.ι Θ).coeff j.1 : ℝ)) := fun j _ =>
    mul_nonneg (by exact_mod_cast (zero_le_one.trans (hm1 j)))
      (haT j.1 (Finset.mem_filter.1 j.2).1).le
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {jS, jL})
    fun j h _ => hnn j h
  rw [Finset.sum_pair hjSL] at hpair
  have hS0 : 0 < (m jS : ℝ) * (1 - ((inverseTransformDivisor U.ι Θ).coeff jS.1 : ℝ)) :=
    mul_pos (by exact_mod_cast (zero_lt_one.trans_le (hm1 jS))) (haT SU (by
      rw [MMP.Intersection.support_reducedDivisorOf]; simp))
  have hL1 : (m jL : ℝ) * (1 - ((inverseTransformDivisor U.ι Θ).coeff jL.1 : ℝ)) = m jL := by
    change (m jL : ℝ) * (1 - ((inverseTransformDivisor U.ι Θ).coeff LU : ℝ)) = _
    rw [hLcoeff]; ring
  rw [hL1] at hpair
  have hlt : (m jL : ℝ) + e < 2 := by linarith
  have hmL : m jL = 1 := by
    have := hm1 jL
    have : m jL + e < 2 := by exact_mod_cast hlt
    omega
  have he0 : e = 0 := by
    have : m jL + e < 2 := by exact_mod_cast hlt
    omega
  subst he0
  rw [Nat.cast_zero] at he
  -- the monomial valuation
  obtain ⟨Z'', hZ'', -, α, -, hα⟩ := he.isMonomialValuationOfWeight_of_eq_zero
  obtain rfl : Z'' = Z' := isCentre_unique he.1 hZ'' hZ'
  have hmono := hα z hz
  have hαL : α jL = 1 := by
    have h1 := hmono.1 jL
    rw [hm jL, hmL] at h1
    have h2 := WithZero.exp_injective h1
    omega
  have hαpos : ∀ j, 0 < α j := hmono.2.2.2.2.2.2.2.2.2.1
  have hmono' := isMonomialValuationOfWeight_congr (reducedDivisorOf_pair hne) hJ hmono.2
  have hweight : (fun j : ({SU, LU} : Finset (MMP.Mori.PrimeDivisor U.toScheme)) =>
      α ⟨j.1, by rw [hJ]; exact j.2⟩) = fun E => if E.1 = SU then α jS else 1 := by
    funext E
    obtain ⟨E, hE⟩ := E
    rcases Finset.mem_insert.1 hE with rfl | hE
    · simp only [if_true]
      rfl
    · obtain rfl := Finset.mem_singleton.1 hE
      rw [if_neg hne.symm, ← hαL]
  rw [hweight] at hmono'
  -- the dimension of the surface
  have hVdim : topologicalKrullDim (Z : Set Y) = 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY η
    rw [(Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def, hdim,
      ← MMP.Flips.codimension_eq_coheight_genericPoint, hc, hc2''] at h
    exact eq_two_of_add_two_eq_four h
  refine ⟨S, Z, α jS, (isSurfaceEcho_iff_isMonomialValuationOfWeight sY hY hdim hSL hVS hVdim
    hη (hαpos jS) hηU hUY hUL hsm hSUsupp hne (by rwa [← reducedDivisorOf_pair hne])
    hZU hZUmax hξU.symm ⟨Z, hZ⟩).2 ⟨_, hmono'⟩⟩

end Local

/-- **Echoes below log discrepancy two.** Let `(Y, Θ)` be a terminal pair on a projective
`ℚ`-factorial fourfold `Y` over `k`, and let `L` be a finite set of prime divisors (the labels)
containing the support of `Θ`. Then the exceptional normalized divisorial valuations `ξ` of `k(Y)`
with log discrepancy `a(ξ; Y, Θ) < 2` which are not an echo of any order `j` of any label `S ∈ L`
at any surface `V` (`MMP.Fourfold.IsSurfaceEcho`) form a finite set. -/
@[mmp "lem_oai4_echoes"]
public theorem IsKltTerminalPair.finite_setOf_not_isSurfaceEcho
    {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hproj : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 4) {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField ℤᵐ⁰ |
      MMP.Intersection.IsExceptionalValuation k sY ξ ∧
        (∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          IsSurfaceEcho sY L S V j ξ}.Finite := by
  obtain ⟨F, hF, hFmem⟩ := exists_finite_of_genericPoint_notMem hΘ L
  refine hF.subset fun ξ ⟨hξ, ha, hne⟩ => ?_
  obtain ⟨D, hDp, rfl, -⟩ := id hξ
  have hZ : MMP.Intersection.IsCentre k sY D.valuation D.center := ⟨D, hDp, rfl, rfl⟩
  by_cases hη : D.center.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L
  · exact absurd (exists_isSurfaceEcho_of_genericPoint_mem hdim hΘ hsupp hξ ha hZ hη) hne
  · exact hFmem _ hξ ha _ hZ hη

/-! ### Consequences: centres of higher codimension, fixed and generic surfaces -/

/-- On an integral scheme locally of finite type over a field, the dimension of an irreducible
closed subset plus its codimension is the dimension of the scheme. -/
private lemma topologicalKrullDim_add_codimension {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (V : IrreducibleCloseds Y) :
    topologicalKrullDim (V : Set Y) + codimension V = topologicalKrullDim Y := by
  obtain ⟨η, hη⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  obtain rfl : IrreducibleCloseds.closureSingleton η = V := SetLike.coe_injective hη
  rw [MMP.Flips.codimension_closureSingleton]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY η

/-- On a fourfold, an irreducible surface has codimension two. -/
private lemma codimension_eq_two {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2) : codimension V = 2 := by
  have h := topologicalKrullDim_add_codimension sY V
  rw [hV, hdim] at h
  generalize codimension V = c at h ⊢
  induction c with
  | top => exact absurd h (by decide)
  | coe n =>
    have : ((2 + n : ℕ) : WithBot ℕ∞) = ((4 : ℕ) : WithBot ℕ∞) := by simpa using h
    have : 2 + n = 4 := by exact_mod_cast this
    exact_mod_cast (by omega : n = 2)

/-- **Echoes: higher-codimension centres.** Let `(Y, Θ)` be a terminal pair on a projective
`ℚ`-factorial fourfold `Y` over `k`, and let `L` be a finite set of prime divisors containing the
support of `Θ`. Then the exceptional normalized divisorial valuations `ξ` of `k(Y)` with log
discrepancy `a(ξ; Y, Θ) < 2` whose centre has codimension at least three form a finite set. -/
@[mmp "lem_oai4_echoes_i"]
public theorem IsKltTerminalPair.finite_setOf_three_le_codimension_centre
    {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hproj : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 4) {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField ℤᵐ⁰ |
      MMP.Intersection.IsExceptionalValuation k sY ξ ∧
        (∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sY Θ ξ a) ∧
        ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre k sY ξ Z ∧
          3 ≤ codimension Z}.Finite := by
  refine (IsKltTerminalPair.finite_setOf_not_isSurfaceEcho hproj hQ hdim hΘ hsupp).subset ?_
  rintro ξ ⟨hexc, hlog, Z, hZ, hcod⟩
  refine ⟨hexc, hlog, ?_⟩
  rintro ⟨S, V, j, hecho⟩
  obtain ⟨hnorm, -, -, -, hV2, -, -, hV, -⟩ := hecho
  obtain ⟨D, -, hD, rfl⟩ := hZ
  obtain ⟨D', -, hD', rfl⟩ := hV
  rw [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hnorm.1 (hD.symm.trans hD')] at hcod
  haveI : LocallyOfFiniteType sY := hnorm.1.toLocallyOfFiniteType
  rw [codimension_eq_two sY hdim hV2] at hcod
  exact absurd hcod (by decide)

/-- The coefficients of the boundary of a klt pair are `< 1`: the log discrepancy of a prime
divisor `P` of `X` is `1 - Θ_P`, which is positive. -/
private theorem coeff_lt_one_of_isKltPair {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Θ : QDivisor X} (hΘ : IsKltPair sX Θ) (P : MMP.Mori.PrimeDivisor X) :
    Θ.coeff P < 1 := by
  haveI : CharZero k := hΘ.1.charZero
  obtain ⟨hX, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor k hX P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor k hX P).f := by
    change IsProper (𝟙 X); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The log discrepancy of a valuation with respect to a pair is unique. -/
private theorem hasLogDiscrepancy_unique {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hP : MMP.Mori.IsPair sY Θ)
    {ξ : Valuation Y.functionField ℤᵐ⁰} {a a' : ℝ}
    (h : HasLogDiscrepancy sY Θ ξ a) (h' : HasLogDiscrepancy sY Θ ξ a') : a = a' := by
  obtain ⟨n, E, hEv, hE⟩ := h
  obtain ⟨n', E', hEv', hE'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hP hE hE'
    (hEv.trans hEv'.symm)

/-- **Order bound for echoes.** On a klt pair, an echo of order `j` of the label `S` whose log
discrepancy is `< 2` satisfies `j (1 - b_S) < 1`, since its log discrepancy is
`1 + j (1 - b_S)`. -/
private theorem mul_lt_one_of_isSurfaceEcho {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ} {ξ : Valuation Y.functionField ℤᵐ⁰}
    (hξ : IsSurfaceEcho sY L S V j ξ) {a : ℝ} (ha : HasLogDiscrepancy sY Θ ξ a) (ha2 : a < 2) :
    (j : ℝ) * (1 - Θ.coeff S) < 1 := by
  haveI : CharZero k := hΘ.1.charZero
  have := hasLogDiscrepancy_unique hΘ.1.isPair ha
    (hξ.hasLogDiscrepancy hΘ.1 hsupp fun S _ => coeff_lt_one_of_isKltPair hΘ S)
  linarith

/-- For `b < 1`, only finitely many natural numbers `j` satisfy `j (1 - b) < 1`. -/
private theorem finite_setOf_mul_lt_one {b : ℝ} (hb : b < 1) :
    {j : ℕ | (j : ℝ) * (1 - b) < 1}.Finite :=
  (Set.finite_Iio ⌈1 / (1 - b)⌉₊).subset fun _ hj =>
    Nat.lt_ceil.2 ((lt_div_iff₀ (sub_pos.2 hb)).2 hj)

/-- **Echoes at a fixed surface centre.** Let `(Y, Θ)` be a terminal pair on a projective
`ℚ`-factorial fourfold `Y` over `k`, and let `L` be a finite set of prime divisors containing the
support of `Θ`. Then for every irreducible closed surface `V ⊆ Y`, the exceptional normalized
divisorial valuations `ξ` of `k(Y)` with centre `V` (`MMP.Intersection.IsCentre`) and log
discrepancy `a(ξ; Y, Θ) < 2` form a finite set. -/
@[mmp "lem_oai4_echoes_ii"]
public theorem IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two
    {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hproj : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 4) {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    (V : IrreducibleCloseds Y) (hV : topologicalKrullDim (V : Set Y) = 2) :
    {ξ : Valuation Y.functionField ℤᵐ⁰ |
      MMP.Intersection.IsExceptionalValuation k sY ξ ∧ MMP.Intersection.IsCentre k sY ξ V ∧
        ∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have hE : (⋃ S ∈ (L : Set (MMP.Mori.PrimeDivisor Y)),
      ⋃ j ∈ {j : ℕ | (j : ℝ) * (1 - (Θ.coeff S : ℝ)) < 1},
        {ξ : Valuation Y.functionField ℤᵐ⁰ |
          IsSurfaceEcho sY L S V j ξ}).Finite :=
    L.finite_toSet.biUnion fun S _ =>
      (finite_setOf_mul_lt_one (by exact_mod_cast coeff_lt_one_of_isKltPair hΘ.1 S)).biUnion
        fun _ _ => Set.Subsingleton.finite fun _ hξ _ hξ' => IsSurfaceEcho.eq hξ hξ'
  refine ((IsKltTerminalPair.finite_setOf_not_isSurfaceEcho hproj hQ hdim hΘ hsupp).union
    hE).subset ?_
  rintro ξ ⟨hexc, hcen, a, ha2, hla⟩
  by_cases hecho : ∃ (S : MMP.Mori.PrimeDivisor Y) (V' : IrreducibleCloseds Y) (j : ℕ),
      IsSurfaceEcho sY L S V' j ξ
  · obtain ⟨S, V', j, h⟩ := hecho
    obtain ⟨hY, -, hS, -, -, -, -, hcen', -⟩ := id h
    obtain rfl := isCentre_unique hY.1 hcen' hcen
    exact Or.inr (Set.mem_biUnion hS
      (Set.mem_biUnion (mul_lt_one_of_isSurfaceEcho hΘ.1 hsupp h hla ha2) h))
  · exact Or.inl ⟨hexc, ⟨a, ha2, hla⟩, hecho⟩

/-- On a fourfold, a valuation whose centre is a surface is exceptional. -/
private theorem isExceptionalValuation_of_isCentre {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : MMP.Mori.IsVariety k sY)
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2) {ξ : Valuation Y.functionField ℤᵐ⁰}
    (h : MMP.Intersection.IsCentre k sY ξ V) : MMP.Intersection.IsExceptionalValuation k sY ξ := by
  obtain ⟨D, hD, rfl, rfl⟩ := h
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  exact ⟨D, hD, rfl, (codimension_eq_two sY hdim hV).ge⟩

/-- The centres of a finite set of valuations form a finite set. -/
private theorem finite_setOf_isCentre {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : MMP.Mori.IsVariety k sY)
    {F : Set (Valuation Y.functionField ℤᵐ⁰)} (hF : F.Finite) :
    {V : IrreducibleCloseds Y | ∃ ξ ∈ F, MMP.Intersection.IsCentre k sY ξ V}.Finite :=
  (hF.biUnion fun ξ _ => Set.Subsingleton.finite
    (s := {V | MMP.Intersection.IsCentre k sY ξ V}) fun _ hV _ hV' =>
      isCentre_unique hY hV hV').subset fun _ ⟨_, hξ, hc⟩ => Set.mem_biUnion hξ hc

/-- **Echoes at generic surface centres.** Let `(Y, Θ)` be a terminal pair on a projective
`ℚ`-factorial fourfold `Y` over `k`, and let `L` be a finite set of prime divisors (the labels)
containing the support of `Θ`. Then there is a finite set `𝒮` of irreducible closed surfaces of
`Y` such that for every irreducible closed surface `V ∉ 𝒮`, every normalized divisorial valuation
`ξ` with centre `V` and every value `a < 2` of its log discrepancy `a(ξ; Y, Θ)`, the valuation `ξ`
is an echo of some order `j` of some label `S ∈ L` containing `V`
(`MMP.Fourfold.IsSurfaceEcho`), and `a = 1 + j (1 - Θ(S))`. -/
@[mmp "lem_oai4_echoes_iii"]
public theorem IsKltTerminalPair.exists_finset_forall_isSurfaceEcho
    {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hproj : MMP.Mori.IsProjectiveVariety k sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 4) {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    ∃ 𝒮 : Finset (IrreducibleCloseds Y),
      (∀ V ∈ 𝒮, topologicalKrullDim (V : Set Y) = 2) ∧
      ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 2 → V ∉ 𝒮 →
        ∀ (ξ : Valuation Y.functionField ℤᵐ⁰),
          MMP.Intersection.IsCentre k sY ξ V →
          ∀ a : ℝ, a < 2 → HasLogDiscrepancy sY Θ ξ a →
            ∃ (S : MMP.Mori.PrimeDivisor Y) (j : ℕ),
              IsSurfaceEcho sY L S V j ξ ∧ a = 1 + j * (1 - (Θ.coeff S : ℝ)) := by
  haveI : CharZero k := hΘ.1.1.charZero
  have hY : MMP.Mori.IsVariety k sY := hΘ.1.1.isPair.1.1
  have hF := IsKltTerminalPair.finite_setOf_not_isSurfaceEcho hproj hQ hdim hΘ hsupp
  have hfin : {V : IrreducibleCloseds Y | topologicalKrullDim (V : Set Y) = 2 ∧
      ∃ ξ ∈ _, MMP.Intersection.IsCentre k sY ξ V}.Finite :=
    (finite_setOf_isCentre hY hF).subset fun _ h => h.2
  refine ⟨hfin.toFinset, fun V hV => (hfin.mem_toFinset.mp hV).1, ?_⟩
  intro V hV hV𝒮 ξ hcen a ha2 hla
  have hexc := isExceptionalValuation_of_isCentre hY hdim hV hcen
  by_contra hne
  refine hV𝒮 (hfin.mem_toFinset.mpr ⟨hV, ξ, ⟨hexc, ⟨a, ha2, hla⟩, ?_⟩, hcen⟩)
  rintro ⟨S, V', j, h⟩
  obtain rfl : V' = V := isCentre_unique hY h.2.2.2.2.2.2.2.1 hcen
  exact hne ⟨S, j, h, hasLogDiscrepancy_unique hΘ.1.1.isPair hla
    (h.hasLogDiscrepancy hΘ.1.1 hsupp fun S _ => coeff_lt_one_of_isKltPair hΘ.1 S)⟩

end MMP.Fourfold

end
