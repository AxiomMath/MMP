module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
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
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicTopology.PoincareDuality.AlexanderCocycleDuality
import MMP.AlgebraicTopology.CapProduct.SupportRetraction
import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicTopology.CapProduct.SupportLemmas
import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import StacksFrontier.AlgebraicGeometry.RegularImmersion.StalkDimension
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
import MMP.AlgebraicGeometry.Variety.StalkDimensionClosedPoint
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.Analytic.SupportedDuality
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.SubschemeOver
import MMP.AlgebraicGeometry.Chow.CycleClassDegree
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Surface and divisor classes in `H_4(-, ℚ)` for the conductor calculations

Two facts about classes in rational degree-four homology used by the conductor calculations on
a dominating smooth fourfold.

* For a smooth projective complex fourfold `Z`, a smooth connected closed centre `C = V(I)` of
  codimension at least two and the exceptional divisor `J` of `Bl_C Z ⟶ Z`, the push-forward
  `H_4(J, ℚ) ⟶ H_4(Bl_C Z, ℚ)` is injective. The proof compares the Borel–Moore localization
  sequences of `J ⊆ Bl_C Z` and `C ⊆ Z`, uses Poincaré duality on `Z` and the projection formula;
  for a surface centre it uses `[C] ≠ 0` (`MMP.Chow.pointCycleClass_ne_zero`: the degree of
  `c₁(A)² ∩ [C]` is positive for an ample `A`, Stacks 0BEV, and Fulton's Theorem 19.2 on Stacks
  cycles).
* On a smooth projective complex threefold `W`, a `ℚ`-divisor `F` with smooth Cartier components
  whose class vanishes in `H_4(W, ℚ)` is numerically trivial. By the Cartier divisor dictionary
  (`MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback`) `[F] = 0` forces
  `c₁(𝒪_W(N F)) = 0`, and the degree of a line bundle with vanishing `c₁ᵗᵒᵖ` on a curve is zero
  (`MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero`).

## Main results

* `MMP.Fourfold.eq_zero_of_componentHomologyMap_exceptional_eq_zero`: a class `u ∈ H_4(J, ℚ)`
  with `ι_* u = 0` in `H_4(Bl_C Z, ℚ)` is zero.
* `MMP.Threefold.isNumericallyTrivial_of_divisorClass_eq_zero`: vanishing of `[F]` in
  `H_4(W, ℚ)` implies `F ≡ 0`.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result. `H_n(-, ℚ)` is `MMP.Fourfold.RationalHomology`, the Borel–Moore
homology of the complex points; the push-forward along the exceptional divisor is
`MMP.Fourfold.componentHomologyMap`, and the class of a `ℚ`-divisor is
`MMP.Chow.divisorClass`. The source's projective-bundle decomposition of `H²(J)` is replaced
by the localization sequences, and its normalization of the curve by Fulton's Theorem 19.2 on
Stacks cycles and the Stacks project's Riemann–Roch for invertible modules on a proper curve.

## References

* [P. Griffiths, J. Harris, *Principles of algebraic geometry*, §4.6]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, §19.2, Theorem 19.2, Corollary 19.2
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Proof_lem_mmp_conductor_blowup_exceptional_surface_kernel

open TopologicalSpace MMP
open scoped MMP.SubschemeOver

open borelMooreHomology

section Ladder

variable {R : Type} [CommRing R] (M : ModuleCat.{0} R)

/-- **The ladder argument.** Let `q : Y' → Y` be proper and `U ⊆ Y` open with `U' = q⁻¹ U`, and
let `A → Y`, `A' → Y'` be proper maps fitting into localization sequences
`H_{k+1}(U) → H_k(A) → H_k(Y)` and `H_{k+1}(U') → H_k(A') → H_k(Y')`. Suppose `H_k(A) → H_k(Y)`
is injective, `q_* : H_{k+1}(Y') → H_{k+1}(Y)` is surjective and `q : U' → U` is injective on
`H_{k+1}`. Then `H_k(A') → H_k(Y')` is injective. -/
private theorem injective_pushforward_of_ladder {Y Y' A A' : TopCat.{0}} [T2Space Y] [T2Space Y']
    (q : Y' ⟶ Y) (hq : IsProperMap q) (i : A ⟶ Y) (hi : IsProperMap i) (ι : A' ⟶ Y')
    (hι : IsProperMap ι) (U : Opens Y) (U' : Opens Y') (hU' : U' = Opens.comap q.hom U) (k : ℤ)
    (δ : borelMooreHomology R M (TopCat.of U) (k + 1) ⟶ borelMooreHomology R M A k)
    (hδ₁ : Function.Exact (restrict R M U (k + 1)).hom δ.hom)
    (hδ₂ : Function.Exact δ.hom (pushforward R M i hi k).hom)
    (δ' : borelMooreHomology R M (TopCat.of U') (k + 1) ⟶ borelMooreHomology R M A' k)
    (hδ'₁ : Function.Exact (restrict R M U' (k + 1)).hom δ'.hom)
    (hδ'₂ : Function.Exact δ'.hom (pushforward R M ι hι k).hom)
    (hinj : Function.Injective (pushforward R M i hi k).hom)
    (hsurj : Function.Surjective (pushforward R M q hq (k + 1)).hom)
    (hφ : Function.Injective (pushforward R M (restrictPreimage q U)
      (isProperMap_restrictPreimage q U hq) (k + 1)).hom) :
    Function.Injective (pushforward R M ι hι k).hom := by
  subst hU'
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := (hδ'₂ u).1 hu
  set y := (pushforward R M (restrictPreimage q U) (isProperMap_restrictPreimage q U hq)
    (k + 1)).hom x
  have hy : δ.hom y = 0 := hinj (by rw [map_zero]; exact (hδ₂ _).2 ⟨y, rfl⟩)
  obtain ⟨z, hz⟩ := (hδ₁ y).1 hy
  obtain ⟨z', rfl⟩ := hsurj z
  have hx : (restrict R M (Opens.comap q.hom U) (k + 1)).hom z' = x :=
    hφ (by rwa [← restrict_pushforward_apply])
  rw [← hx]
  exact (hδ'₁ _).2 ⟨z', rfl⟩

/-- A class of `Y` whose restriction to `U` comes from `U' = q⁻¹ U` comes from `Y'`, when the
restriction to `U` is injective and every class of `U'` extends to `Y'`. -/
private theorem exists_pushforward_eq_of_ladder {Y Y' : TopCat.{0}} [T2Space Y] [T2Space Y']
    (q : Y' ⟶ Y) (hq : IsProperMap q) (U : Opens Y) (U' : Opens Y')
    (hU' : U' = Opens.comap q.hom U) (m : ℤ)
    (hres : Function.Injective (restrict R M U m).hom)
    (hext : Function.Surjective (restrict R M U' m).hom)
    (hφ : Function.Surjective (pushforward R M (restrictPreimage q U)
      (isProperMap_restrictPreimage q U hq) m).hom)
    (μ : borelMooreHomology R M Y m) :
    ∃ μ', (pushforward R M q hq m).hom μ' = μ := by
  subst hU'
  obtain ⟨x, hx⟩ := hφ ((restrict R M U m).hom μ)
  obtain ⟨μ', rfl⟩ := hext x
  refine ⟨μ', hres ?_⟩
  rw [restrict_pushforward_apply, hx]

end Ladder

section Dimension

/-- If every irreducible closed subset of the closed set `S` has codimension at least `c` in a
space of dimension at most `n`, then `S` has dimension at most `n - c`. -/
private lemma topologicalKrullDim_le_sub_of_le_codimension {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsClosed S) {c n : ℕ} (hX : topologicalKrullDim X ≤ n)
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ S → (c : ℕ∞) ≤ codimension W) :
    topologicalKrullDim S ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
  let e : IrreducibleCloseds S → IrreducibleCloseds X := fun W ↦
    ⟨(↑) '' (W : Set S), W.2.image _ continuous_subtype_val.continuousOn,
      hS.isClosedMap_subtype_val _ W.3⟩
  have he : StrictMono e := by
    intro a b hab
    have hab' : (a : Set S) ⊂ b := hab
    change Subtype.val '' (a : Set S) ⊂ Subtype.val '' (b : Set S)
    exact ⟨Set.image_mono hab'.1, fun h ↦ hab'.2 ((Set.image_subset_image_iff
      Subtype.val_injective).1 h)⟩
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun W ↦ ?_
  have h1 : Order.height W ≤ Order.height (e W) :=
    Order.height_le_height_apply_of_strictMono _ he _
  have h2 : (c : ℕ∞) ≤ Order.coheight (e W) := by
    rw [← codimension_eq_coheight]
    exact hc _ (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  have h3 : ((Order.height (e W) + Order.coheight (e W) : ℕ∞) : WithBot ℕ∞) ≤ n := by
    haveI : Nonempty (IrreducibleCloseds X) := ⟨e W⟩
    refine le_trans ?_ hX
    rw [topologicalKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.2 (le_iSup (fun a ↦ Order.height a + Order.coheight a) (e W))
  have h4 : Order.height W + c ≤ n := (add_le_add h1 h2).trans (WithBot.coe_le_coe.1 h3)
  have hne : Order.height W ≠ ⊤ := fun h ↦ by simp [h] at h4
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hm] at h4 ⊢
  have h6 : m + c ≤ n := by exact_mod_cast h4
  exact WithBot.coe_le_coe.2 (Nat.cast_le.2 (show m ≤ n - c by omega))

/-- A closed subscheme of a scheme of dimension at most `n`, all of whose irreducible closed
subsets have codimension at least `c`, has dimension at most `n - c`. -/
private lemma dimension_subscheme_le {X : Scheme.{0}} (I : X.IdealSheafData) {c n : ℕ}
    (hX : topologicalKrullDim X ≤ n)
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ I.support → (c : ℕ∞) ≤ codimension W) :
    topologicalKrullDim I.subscheme ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
  have hmem : ∀ z, I.subschemeι z ∈ (I.support : Set X) := fun z ↦ by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
  exact ((I.subschemeι.isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le).trans
    (topologicalKrullDim_le_sub_of_le_codimension I.support.isClosed hX hc)

end Dimension

section Points

open UnderlyingSpace

/-- Push-forward along a proper continuous bijection is bijective. -/
private lemma bijective_pushforward_of_bijective {R : Type} [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (hb : Function.Bijective f) (j : ℤ) :
    Function.Bijective (pushforward R (ModuleCat.of R R) f hf j).hom :=
  bijective_pushforward_homeomorph R
    ((Equiv.ofBijective f hb).toHomeomorphOfContinuousClosed f.hom.continuous
      hf.isClosedMap) j

/-- If `f ∣_ W` is an isomorphism, `f` is bijective on `ℂ`-points over `W`. -/
private lemma bijective_restrictPreimage_map_of_isIso {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    (W : Y.Opens) [IsIso (f ∣_ W)] (U : Opens (TopCat.of (UnderlyingSpace ℂ Y)))
    (hU : ∀ p : UnderlyingSpace ℂ Y, p ∈ U ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ W) :
    Function.Bijective (restrictPreimage (TopCat.ofHom (map (K := ℂ) f)) U) := by
  have hpt : ∀ x : Spec (.of ℂ), x = IsLocalRing.closedPoint ℂ := fun x ↦ Subsingleton.elim _ _
  have hX : ∀ a : Opens.comap (TopCat.ofHom (map (K := ℂ) f)).hom U,
      Set.range a.1.toHom ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rintro a _ ⟨x, rfl⟩
    rw [hpt x, Scheme.Opens.range_ι]
    exact (hU _).1 a.2
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · have hab' : a.1.toHom ≫ f = b.1.toHom ≫ f :=
      congrArg UnderlyingSpace.toHom (congrArg Subtype.val hab)
    have key : IsOpenImmersion.lift (f ⁻¹ᵁ W).ι a.1.toHom (hX a) =
        IsOpenImmersion.lift (f ⁻¹ᵁ W).ι b.1.toHom (hX b) := by
      rw [← cancel_mono (f ∣_ W), ← cancel_mono W.ι, Category.assoc, Category.assoc,
        morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab']
    apply Subtype.ext
    apply UnderlyingSpace.ext
    rw [← IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι a.1.toHom (hX a),
      ← IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι b.1.toHom (hX b), key]
  · have hb : Set.range b.1.toHom ⊆ Set.range W.ι := by
      rintro _ ⟨x, rfl⟩
      rw [hpt x, Scheme.Opens.range_ι]
      exact (hU _).1 b.2
    set x := IsOpenImmersion.lift W.ι b.1.toHom hb ≫ inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι with hxdef
    have hxf : x ≫ f = b.1.toHom := by
      rw [hxdef, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
        IsOpenImmersion.lift_fac]
    have hxo : x ≫ X ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [← comp_over f (Spec (.of ℂ)), ← Category.assoc, hxf, b.1.toHom_comp_over]
    let x' : UnderlyingSpace ℂ X := ⟨x, hxo⟩
    have hx' : map (K := ℂ) f x' = b.1 := UnderlyingSpace.ext hxf
    refine ⟨⟨x', ?_⟩, Subtype.ext hx'⟩
    change map (K := ℂ) f x' ∈ U
    rw [hx']
    exact b.2

end Points

section Duality

open BorelMooreCap BorelMooreCross

/-- If capping with `μ` maps `H^{n-k}(Y)` onto `H_k(Y)` and `μ = q_* μ'`, then
`q_* : H_k(Y') → H_k(Y)` is onto, by the projection formula. -/
private lemma surjective_pushforward_of_surjective_dualityMap {R : Type} [CommRing R]
    {Y' Y : TopCat.{0}} [T2Space Y] [T2Space Y'] (q : Y' ⟶ Y) (hq : IsProperMap q) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) Y n)
    (μ' : borelMooreHomology R (ModuleCat.of R R) Y' n)
    (hμ : (pushforward R (ModuleCat.of R R) q hq n).hom μ' = μ)
    {A : Set Y} (hA : IsClosed A) (hAu : A = Set.univ) (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (q ⁻¹' A)) (k : ℤ)
    (hdual : Function.Surjective (dualityMap R hA hAd μ k)) :
    Function.Surjective (pushforward R (ModuleCat.of R R) q hq k).hom := by
  subst hAu
  intro z
  have hb := bijective_pushforward_of_bijective (R := R) (subsetInclusion (Set.univ : Set Y))
    (isProperMap_subsetInclusion hA)
    ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, trivial⟩, rfl⟩⟩ k
  obtain ⟨w, rfl⟩ := hb.2 z
  obtain ⟨c, rfl⟩ := hdual w
  refine ⟨congrDegree R Y' (by omega : (n : ℤ) - (n - k) = k)
    (capProduct R Y' (q ⁻¹' Set.univ) (n - k) n
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) q Set.univ (n - k)).hom c) μ'), ?_⟩
  rw [pushforward_congrDegree_apply, pushforward_capProduct_pullback R q hq hA hAd hA'd, hμ,
    dualityMap_apply, pushforward_congrDegree_apply, pushforward_subsetInclusion_capProductSupport]

end Duality

section Centre

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme {Y Z : Scheme.{0}} {f : Y ⟶ Z}
    (h : MMP.Mori.IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : Y.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- A connected closed subscheme smooth over a field is integral. -/
private theorem isIntegral_subscheme_of_isConnected {X : Scheme.{0}} {k : Type} [Field k]
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (hI : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ sX))
    (hc : _root_.IsConnected (I.support : Set X)) :
    IsIntegral I.subscheme := by
  have := smooth_of_isSmoothScheme hI
  have hc' : _root_.IsConnected (I.subschemeι.base ⁻¹' (I.support : Set X)) :=
    hc.preimage_of_isClosedMap I.subschemeι.isClosedEmbedding.injective
      I.subschemeι.isClosedEmbedding.isClosedMap (by rw [I.range_subschemeι])
  have : ConnectedSpace I.subscheme := by
    rw [connectedSpace_iff_univ]
    convert hc'
    ext z
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (I.subschemeι ≫ sX)

open UnderlyingSpace in
/-- **A smooth connected centre of dimension at most `d` carries no class in `H_{2d}` dying in
the ambient space.** Let `X` be a projective non-singular complex variety and `C = V(I)` a smooth
connected closed subscheme of dimension at most `d ≥ 1`. Then
`i_* : H_{2d}(C, ℚ) → H_{2d}(X, ℚ)` is injective: if `dim C < d` the source vanishes, and if
`dim C = d` it is spanned by the fundamental class of `C`, whose image is nonzero by
`isCycleClass_ne_zero`. -/
private theorem injective_pushforward_subschemeι_of_dimension_le {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (hX : IsProjective (X ↘ Spec (.of ℂ)))
    (I : X.IdealSheafData) (hC : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (X ↘ Spec (.of ℂ))))
    (hconn : _root_.IsConnected (I.support : Set X)) {d : ℕ} (hd : 1 ≤ d)
    (hdim : topologicalKrullDim I.subscheme ≤ (d : WithBot ℕ∞)) [IsComplexScheme I.subscheme] :
    Function.Injective (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) I.subschemeι))
      (isClosedEmbedding_map_of_isClosedImmersion I.subschemeι).isProperMap (2 * d : ℕ)).hom := by
  by_cases h1 : topologicalKrullDim I.subscheme ≤ ((d - 1 : ℕ) : WithBot ℕ∞)
  · have h4 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le I.subscheme ℚ h1
      (i := (2 * d : ℕ)) (by omega)
    rw [ModuleCat.isZero_iff_subsingleton] at h4
    exact fun a b _ ↦ Subsingleton.elim a b
  have hd' : ((d : ℕ) : WithBot ℕ∞) = topologicalKrullDim I.subscheme := by
    generalize topologicalKrullDim I.subscheme = e at hdim h1 ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact absurd bot_le h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_le_coe.1 hdim) (not_le.2 (ENat.coe_lt_top d))
      | coe m =>
        have h2 : m ≤ d := by exact_mod_cast hdim
        have h3 : ¬ m ≤ d - 1 := fun h ↦ h1 (WithBot.coe_le_coe.2 (Nat.cast_le.2 h))
        obtain rfl : m = d := by omega
        rfl
  have hI : IsIntegral I.subscheme := isIntegral_subscheme_of_isConnected _ I hC hconn
  have : IsProper (X ↘ Spec (.of ℂ)) := hX.isProper
  have hη : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (I.subscheme ↘ Spec (.of ℂ)) (genericPoint I.subscheme) = d :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ (I.subscheme ↘ Spec (.of ℂ)) hd'.symm
  let cC := MMP.Chow.pointCycleClass ℚ (genericPoint I.subscheme) hη
  have hcongr : ∀ {p q : I.subscheme} (_ : p = q) hp hq,
      MMP.Chow.pointCycleClass ℚ (k := d) p hp = MMP.Chow.pointCycleClass ℚ q hq := by
    rintro p q rfl hp hq; rfl
  have hgen : ∀ y, ∃ r : ℚ, r • cC = y := by
    intro y
    have hspan :=
      (MMP.Chow.linearIndependent_and_span_eq_top_pointCycleClass ℚ (X := I.subscheme) hdim).2
    have hy : y ∈ Submodule.span ℚ {cC} := by
      refine Submodule.span_le.2 ?_ (hspan.symm ▸ Submodule.mem_top)
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span (Set.mem_singleton_iff.2 (hcongr ?_ _ _))
      have hu : (j.1 : Set I.subscheme) = Set.univ := Set.eq_univ_of_univ_subset
        (j.1.2.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
      have hg : IsGenericPoint (MMP.Chow.componentGenericPoint j.1) Set.univ :=
        (MMP.Chow.closure_componentGenericPoint j.1).trans hu
      exact hg.eq (genericPoint_spec I.subscheme)
    exact Submodule.mem_span_singleton.1 hy
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨A, hAi, hA⟩ := AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism
    (X ↘ Spec (.of ℂ)) M hMa (isProjectiveMorphism_of_isProjective_of_isAffine _ hX)
  have hpush : pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) I.subschemeι))
      (isClosedEmbedding_map_of_isClosedImmersion I.subschemeι).isProperMap (2 * d : ℕ) cC ≠ 0 := by
    have hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (I.subschemeι.base (genericPoint I.subscheme)) = d := by
      refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
        ℂ _ _ d ?_
      have hemb := I.subschemeι.isClosedEmbedding
      rw [← Set.image_singleton, hemb.closure_image_eq, (genericPoint_spec I.subscheme).def,
        Set.image_univ, ← hemb.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
      exact hd'.symm
    have hne := MMP.Chow.pointCycleClass_ne_zero A hA _ hx
    have e := MMP.Chow.pushforward_pointCycleClass ℚ I.subschemeι (genericPoint I.subscheme) hη
    rw [Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul,
      MMP.Chow.pointCycleClassOrZero] at e
    simp only [dif_pos hx] at e
    rwa [← e] at hne
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨r, rfl⟩ := hgen y
  rw [map_smul] at hy
  rcases smul_eq_zero.1 hy with h | h
  · simp [h]
  · exact absurd h hpush

end Centre

end Proof_lem_mmp_conductor_blowup_exceptional_surface_kernel

namespace MMP.Fourfold

open TopologicalSpace
open scoped MMP.SubschemeOver
open MMP.borelMooreHomology MMP.UnderlyingSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open Proof_lem_mmp_conductor_blowup_exceptional_surface_kernel

/-- An ideal sheaf on an irreducible scheme whose support has codimension at least two
everywhere is nonzero. -/
private lemma ne_bot_of_two_le_codimension {X : Scheme.{0}} [IrreducibleSpace X]
    (I : X.IdealSheafData)
    (hcodim : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ I.support → 2 ≤ codimension W) :
    I ≠ ⊥ := by
  rintro rfl
  have h := hcodim ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    (by rw [Scheme.IdealSheafData.support_bot]; exact subset_rfl)
  rw [codimension_eq_coheight, Order.coheight_eq_zero.mpr fun W _ ↦ by
    change (W : Set X) ≤ Set.univ; exact Set.subset_univ _] at h
  exact absurd h (by decide)

/-- An irreducible blow-up of a scheme locally of finite type over a field has dimension at most
that of the base. -/
private lemma topologicalKrullDim_blowUp_le {X : Scheme.{0}} {k : Type} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    [IrreducibleSpace (blowUp I)] :
    topologicalKrullDim (blowUp I) ≤ topologicalKrullDim X := by
  obtain ⟨D, -, hD⟩ :=
    MMP.Resolution.exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp sX I
      (C := Set.univ) ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ ↦ Set.subset_univ _⟩
  calc topologicalKrullDim (blowUp I) ≤ topologicalKrullDim (Set.univ : Set (blowUp I)) :=
        (Homeomorph.Set.univ _).symm.isInducing.topologicalKrullDim_le
    _ = topologicalKrullDim D := hD
    _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le _ _

/-- A prime divisor of a scheme of dimension at most `n` has dimension at most `n - 1`. -/
private lemma topologicalKrullDim_primeDivisor_subscheme_le {X : Scheme.{0}}
    (J : MMP.Mori.PrimeDivisor X) {n : ℕ} (hX : topologicalKrullDim X ≤ n) :
    topologicalKrullDim J.idealSheaf.subscheme ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  refine dimension_subscheme_le J.idealSheaf hX fun W hW ↦ ?_
  have h1 := J.codimension_one
  have hle : W ≤ IrreducibleCloseds.closureSingleton
      (Stacks.Chow.genericPointOf J.idealSheaf J.integral) := by
    change (W : Set X) ⊆ closure {_}
    rw [← Stacks.Chow.support_eq_closure_genericPointOf]
    exact hW
  rw [codimension_eq_coheight] at h1 ⊢
  rw [Nat.cast_one]
  exact h1.symm.le.trans (Order.coheight_anti hle)

/-- The complex points off the exceptional divisor `J` of `Bl_I Z` are the preimage of the
complex points off `V(I)`. -/
private lemma complOpens_exceptional_eq_comap {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (I : Z.IdealSheafData) [(blowUp I).Over (Spec (.of ℂ))]
    [(blowUpToBase I).IsOver (Spec (.of ℂ))] (J : MMP.Mori.PrimeDivisor (blowUp I))
    (hJ : J.idealSheaf = exceptionalIdeal I) :
    complOpens (Y := TopCat.of (UnderlyingSpace ℂ (blowUp I)))
        (isClosed_range_map_of_isClosedImmersion J.idealSheaf.subschemeι) =
      Opens.comap (TopCat.ofHom (map (K := ℂ) (blowUpToBase I))).hom
        (complOpens (Y := TopCat.of (UnderlyingSpace ℂ Z))
          (isClosed_range_map_of_isClosedImmersion I.subschemeι)) := by
  have hrange : Set.range (map (K := ℂ) J.idealSheaf.subschemeι) =
      map (K := ℂ) (blowUpToBase I) ⁻¹' Set.range (map (K := ℂ) I.subschemeι) := by
    rw [range_map_of_isClosedImmersion, range_map_of_isClosedImmersion]
    ext p
    simp only [mem_pointsOver, Set.mem_preimage, toHom_map,
      Scheme.IdealSheafData.range_subschemeι, hJ]
    rw [exceptionalIdeal, Scheme.IdealSheafData.support_comap]
    rfl
  ext p
  change p ∈ (Set.range (map (K := ℂ) J.idealSheaf.subschemeι))ᶜ ↔
    map (K := ℂ) (blowUpToBase I) p ∈ (Set.range (map (K := ℂ) I.subschemeι))ᶜ
  rw [hrange]
  rfl

/-- Over the complement of the centre, the blow-up induces a bijection on Borel–Moore
homology. -/
private lemma bijective_pushforward_restrictPreimage_blowUp {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (I : Z.IdealSheafData)
    [(blowUp I).Over (Spec (.of ℂ))]
    [(blowUpToBase I).IsOver (Spec (.of ℂ))] [IsProper (blowUpToBase I)] (j : ℤ) :
    Function.Bijective (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (restrictPreimage (TopCat.ofHom (map (K := ℂ) (blowUpToBase I)))
        (complOpens (Y := TopCat.of (UnderlyingSpace ℂ Z))
          (isClosed_range_map_of_isClosedImmersion I.subschemeι)))
      (isProperMap_restrictPreimage _ _ (isProperMap_map (K := ℂ) (blowUpToBase I))) j).hom := by
  have := isIso_blowUp_restrict_compl_support I
  refine bijective_pushforward_of_bijective _ _ ?_ _
  refine bijective_restrictPreimage_map_of_isIso _ ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    _ fun p ↦ ?_
  change p ∈ (Set.range (map (K := ℂ) I.subschemeι))ᶜ ↔ _
  rw [range_map_of_isClosedImmersion, Set.mem_compl_iff, mem_pointsOver,
    Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- Push-forward onto a smooth projective complex variety `X` of dimension `d` is surjective in
every degree once the fundamental class of `X` lies in its image, by Poincaré duality on `X`. -/
private lemma surjective_pushforward_map_of_isProjective {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y]
    [IsIntegral X] [AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ))] {d : ℕ}
    [SmoothOfRelativeDimension d (X ↘ Spec (.of ℂ))] (hX : IsProjective (X ↘ Spec (.of ℂ)))
    (f : Y ⟶ X) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (μ' : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y)) (2 * d : ℕ))
    (hμ' : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) f))
      (isProperMap_map (K := ℂ) f) (2 * d : ℕ)).hom μ' =
      MMP.Chow.pointCycleClass ℚ (genericPoint X) (MMP.Chow.relativeDimension_genericPoint_eq ℂ
        (X ↘ Spec (.of ℂ))
        (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) X d).symm))
    (k : ℤ) :
    Function.Surjective (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) f))
      (isProperMap_map (K := ℂ) f) k).hom := by
  have hqp : IsQuasiProjectiveVariety ℂ (X ↘ Spec (.of ℂ)) :=
    (isQuasiProjectiveVariety_iff_isQuasiProjective ℂ _).2 (isQuasiProjective_of_isProjective hX)
  have : IsProper (X ↘ Spec (.of ℂ)) := hX.isProper
  have hD : IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫
      (X ↘ Spec (.of ℂ))) := inferInstance
  have hpre : map (K := ℂ) f ⁻¹' pointsOver ((⊤ : Closeds X) : Set X) =
      pointsOver ((⊤ : Closeds Y) : Set Y) := by
    ext p; simp [mem_pointsOver]
  exact surjective_pushforward_of_surjective_dualityMap _ _ _ μ' hμ'
    (isClosed_pointsOver (⊤ : Closeds X).isClosed) (by ext p; simp [mem_pointsOver]) _
    (hpre ▸ hasProperNeighbourhoodDeformations_pointsOver Y ⊤) _
    (MMP.Analytic.bijective_dualityMap_of_isQuasiProjectiveVariety hqp rfl ⊤ hD k).1.2

/-- **Surface classes on the exceptional divisor of a smooth blow-up of a fourfold.** Let `Z`
be a smooth projective complex fourfold, `I` the ideal sheaf of a smooth connected closed
subscheme `C = V(I)` of codimension at least two, and `J` the exceptional divisor of the blow-up
`blowUpToBase I : blowUp I ⟶ Z`. If `u ∈ H_4(J, ℚ)` has zero push-forward in
`H_4(blowUp I, ℚ)`, then `u = 0`. -/
@[mmp "lem_mmp_conductor_blowup_exceptional_surface_kernel"]
public theorem eq_zero_of_componentHomologyMap_exceptional_eq_zero
    {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsIntegral Z]
    [SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ))] (hZ : IsProjective (Z ↘ Spec (.of ℂ)))
    (I : Z.IdealSheafData)
    (hC : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hconn : _root_.IsConnected (I.support : Set Z))
    (hcodim : ∀ W : IrreducibleCloseds Z, (W : Set Z) ⊆ I.support → 2 ≤ codimension W)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    [IsComplexScheme (blowUp I)]
    (J : MMP.Mori.PrimeDivisor (blowUp I)) (hJ : J.idealSheaf = exceptionalIdeal I)
    (u : RationalHomology J.idealSheaf.subscheme 4) (hu : componentHomologyMap J 4 u = 0) :
    u = 0 := by
  have hI : I ≠ ⊥ := ne_bot_of_two_le_codimension I hcodim
  have : IsProper (Z ↘ Spec (.of ℂ)) := hZ.isProper
  have : Nonempty Z := IsIntegral.nonempty
  have : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := { }
  have : Smooth (Z ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 4 _
  have : IsSmoothVariety ℂ (Z ↘ Spec (.of ℂ)) := { }
  have : IsComplexScheme Z := IsComplexScheme.of_isSmoothVariety Z
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  set q := blowUpToBase I
  set i := I.subschemeι
  set ι := J.idealSheaf.subschemeι
  obtain ⟨δ, hδ₂, hmid, hδ₁⟩ := IsComplexScheme.exists_borelMooreHomology_longExact ℚ
    (ModuleCat.of ℚ ℚ) Z i
  obtain ⟨δ', hδ'₂, -, hδ'₁⟩ := IsComplexScheme.exists_borelMooreHomology_longExact ℚ
    (ModuleCat.of ℚ ℚ) (blowUp I) ι
  let U := complOpens (Y := TopCat.of (UnderlyingSpace ℂ Z))
    (isClosed_range_map_of_isClosedImmersion i)
  have hU' := complOpens_exceptional_eq_comap I J hJ
  have hφb := bijective_pushforward_restrictPreimage_blowUp I
  have hZdim : topologicalKrullDim Z = (4 : ℕ) :=
    MMP.UnderlyingSpace.topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) 4
  have hdimC : topologicalKrullDim I.subscheme ≤ ((4 - 2 : ℕ) : WithBot ℕ∞) :=
    dimension_subscheme_le I hZdim.le fun W hW ↦ by simpa using hcodim W hW
  have hdimJ := topologicalKrullDim_primeDivisor_subscheme_le J
    ((topologicalKrullDim_blowUp_le (Z ↘ Spec (.of ℂ)) I).trans hZdim.le)
  have : IsComplexScheme I.subscheme := IsComplexScheme.of_isClosedImmersion i
  have : IsComplexScheme J.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion ι
  have hC8 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le I.subscheme ℚ hdimC
    (i := ((2 * 4 : ℕ) : ℤ)) (by norm_num)
  have hJ7 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le J.idealSheaf.subscheme ℚ
    hdimJ (i := 7) (by norm_num)
  rw [ModuleCat.isZero_iff_subsingleton] at hC8 hJ7
  have hres := (injective_iff_map_eq_zero (restrict ℚ (ModuleCat.of ℚ ℚ) U ((2 * 4 : ℕ) : ℤ)).hom).2
    fun x hx ↦ by
      obtain ⟨a, rfl⟩ := (hmid _ x).1 hx
      rw [Subsingleton.elim a 0, map_zero]
  obtain ⟨μ', hμ'⟩ := exists_pushforward_eq_of_ladder (ModuleCat.of ℚ ℚ) _
    (isProperMap_map (K := ℂ) q) U _ hU' _ hres (fun x ↦ (hδ'₁ 7 x).1 (Subsingleton.elim _ _))
    (hφb _).2 (MMP.Chow.pointCycleClass ℚ (genericPoint Z)
      (MMP.Chow.relativeDimension_genericPoint_eq ℂ (Z ↘ Spec (.of ℂ)) hZdim))
  exact injective_pushforward_of_ladder (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) q))
    (isProperMap_map (K := ℂ) q) _ _ (TopCat.ofHom (map (K := ℂ) ι))
    (isClosedEmbedding_map_of_isClosedImmersion ι).isProperMap U _ hU' 4 (δ 4) (hδ₁ 4) (hδ₂ 4)
    (δ' 4) (hδ'₁ 4) (hδ'₂ 4)
    (injective_pushforward_subschemeι_of_dimension_le hZ I hC hconn (d := 2) (by norm_num) hdimC)
    (surjective_pushforward_map_of_isProjective hZ q μ' hμ' (4 + 1)) (hφb _).1
    (by rw [map_zero]; exact hu)

end MMP.Fourfold

namespace MMP.Threefold

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **A divisor with vanishing homology class is numerically trivial.** Let `W` be a smooth
projective complex threefold and `F` a `ℚ`-divisor on `W` whose components are smooth over `ℂ`
and Cartier. If the class of `F` in `H_4(W, ℚ)` is zero, then `F` is `ℚ`-Cartier and
`(F · C) = 0` for every integral closed curve `C ⊆ W`. -/
@[mmp "lem_mmp_conductor_snc_divisor_class_degree"]
public theorem isNumericallyTrivial_of_divisorClass_eq_zero
    {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [MMP.IsComplexScheme W] [IsLocallyNoetherian W]
    [IsNormal W]
    (hW : MMP.Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (F : QDivisor W)
    (hFsm : ∀ S ∈ F.support, IsSmoothScheme (S.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    (hFc : ∀ S ∈ F.support, Divisor.IsCartier (Finsupp.single S 1 : Divisor W))
    (hF : MMP.Chow.divisorClass W F = 0) :
    F.IsNumericallyTrivial ℂ (W ↘ Spec (.of ℂ)) := by
  classical
  have hv := ((MMP.Mori.isProjectiveVariety_iff _ _).1 hW).1
  haveI : IsIntegral W := hv.toIsIntegral
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  -- an integral multiple `G = N F`, Cartier since `W` is smooth
  obtain ⟨N, hN, G, hG⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor F
  have hGC : G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm G
  have hQ : F.IsQCartier := ⟨N, by exact_mod_cast hN.ne', G, hG, hGC⟩
  rw [QDivisor.isNumericallyTrivial_iff]
  refine ⟨hQ, fun C i _ _ _ hC ↦ ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ _ i hC.le F hQ hN G hGC hG]
  suffices h0 : G.degreeOn ℂ (W ↘ Spec (.of ℂ)) i hC.le hGC = 0 by rw [h0]; simp
  haveI hGi : Stacks.Ample.IsInvertibleModule W G.divisorialSheaf :=
    hGC.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 G.divisorialSheaf := hGi
  -- the dictionary: `[F] = 0` iff `c₁(𝒪_W(G)) = 0`
  have hdimX : topologicalKrullDim W = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  have hgen : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ))
      (_root_.genericPoint W) = ((2 + 1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ (2 + 1) ?_
    rw [(genericPoint_spec W).def, ← hdimX]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ W).isHomeomorph
  have hc := ((MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hW hsm hdimX F hN G hG
    (_root_.genericPoint W) hgen).2).1 hF
  have hL := MMP.Chow.firstChernClassTop_eq_zero_of_mapCoeff_eq_zero G.divisorialSheaf hc
  -- the degree along `C` of a line bundle with vanishing `c₁ᵗᵒᵖ`
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hW
  haveI : Stacks.Ample.IsInvertibleModule W H := hH
  exact MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple W H).mpr hHa) _ hL i hC.le

end MMP.Threefold
