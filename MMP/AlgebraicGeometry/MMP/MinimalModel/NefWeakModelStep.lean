module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.ArbitraryModule
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# A nef weak model survives each negative step of the program

Let `φ : Y ⤏ Z` be a nef weak model (`MMP.Fourfold.IsNefWeakModel`) over `S` of a pair `(Y, C)`
with real boundary, `Y` and `Z` being `ℚ`-factorial. Let `g : Y ⤏ Y⁺` be a step over `S`, with `Y⁺`
`ℚ`-factorial, of the `(K_Y + C)`-minimal model program: either a `(K_Y + C)`-negative extremal
divisorial contraction `f : Y ⟶ Y⁺`, or the flip `f⁺ : Y⁺ ⟶ V` of a `(K_Y + C)`-negative
extremal small contraction `f : Y ⟶ V`. Then

1. `Z` is still a nef weak model of `(Y⁺, C⁺)`, `C⁺ = g_* C`, through the map `φ⁺ : Y⁺ ⤏ Z`
   with `φ⁺ ∘ g = φ`;
2. no prime divisor `G` of `Y` whose coefficient in the comparison
   `p^*(K_Y + C) - q^*(K_Z + C_Z)` vanishes is contracted by `g`;
3. `(K_Y + C)` admits no negative extremal contraction of fibre type over `S`.

On a common resolution of `Y`, `Z`, `Y⁺` every non-exceptional coefficient of the new
comparison is an old one, so the new comparison is effective by negativity; a contracted prime
of comparison coefficient zero would have its discrepancy strictly raised, making its new
coefficient negative. A curve through a general point of a general fibre of a fibre-type
contraction has negative degree for `K_Y + C`, but nonnegative degree for the sum of the nef
`q^*(K_Z + C_Z)` and the effective comparison.

## Main results

* `MMP.Fourfold.IsNefWeakModel.isNefWeakModel_of_negativeStep`.
* `MMP.Fourfold.IsNefWeakModel.isNefWeakModel_and_exists_model_of_negativeStep`: the nef weak
  model `φ⁺` of conclusion 1 comes with a smooth common model of `Y⁺` and `Z` on which every
  comparison coefficient of a prime `G` of `Y` with `g_* G` a prime is unchanged, so that the
  steps of a program can be chained.
* `MMP.Fourfold.IsNefWeakModel.isNefWeakModel_of_step_over`: the same for any step `g : Y ⤏ Y⁺`
  over a normal base `B` (`f : Y ⟶ B`, `u : Y⁺ ⟶ B` proper birational, `u ∘ g = f`) contracting
  no prime of comparison coefficient zero, together with `φ⁺_* g_* N = φ_* N` and
  `g_* N = (u⁻¹)_* f_* N` (`MMP.Mori.flipTransform`) for every divisor `N` of `Y`.
* `MMP.Fourfold.not_isExceptional_of_coeff_eq_zero` and
  `MMP.Fourfold.not_isExceptional_of_isFlip`: the two kinds of steps contract no prime of
  comparison coefficient zero.
* `MMP.Fourfold.coeff_eq_coeff_of_isRCartierPullback`: comparison coefficients do not depend on
  the common model; and the rational-map algebra of `MMP.Fourfold.Crepant`
  (`comp_eq_id_of_isInverse`, `eq_of_compHom_eq_id`, `isBirationalMorphism_comp`, ...).
* `MMP.Flips.IsRCartierPullback.comp`: pull-backs of `ℝ`-Cartier divisors compose,
  `(g ≫ f)^*D = g^*(f^*D)`.
* `MMP.Flips.isCartierIntersectionNumber_degreeOn`: the intersection number `L · C` of a Cartier
  divisor with a proper curve is the degree `L.degreeOn` of `𝒪_X(L)` along `C`.
* `MMP.Flips.isRIntersectionNumber_sum_degreeOn` and
  `MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber`: for a presentation `D = ∑ r_j L_j` by
  Cartier divisors, `D · C = ∑ r_j (L_j · C)` computed from degrees, and every value of `D · C`
  is this sum.
* `MMP.Fourfold.degreeOn_eq_mul_of_isPullback`: the projection formula
  `f^*L · C' = [k(C') : k(f(C'))] (L · f(C'))` for a Cartier divisor `L`.
* `MMP.Fourfold.exists_properCurve_map_eq`: a proper curve on the target of a proper surjection
  is the image of a proper curve, with a finite extension of function fields.
* `MMP.Fourfold.isRelativelyNef_of_isRCartierPullback`: if `M` is nef over `S` and
  `q : W ⟶ Z` is proper with `p ≫ πY = q ≫ πZ`, then `q^*M` is `p`-nef.
* `MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective`: nefness over `S` descends
  along a proper surjection.
* `MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse`: the transform of a prime divisor
  along `q ∘ p⁻¹`, for a proper birational `p : W ⟶ X`, is read at the prime of `W` over it;
  `MMP.Fourfold.exists_rep_apply_eq_of_isInverse` gives the representative of `p⁻¹` doing so.
* `MMP.Fourfold.exists_common_model_over` and `MMP.Fourfold.exists_isInverse_of_common_model`:
  a smooth common model of a step of the program, and the composites of the maps on it;
  `MMP.Fourfold.comp_eq_comp_of_isOver`: a model of a map over `S` commutes over `S`.
* `MMP.Fourfold.mapPrimeDivisors_mapPrimeDivisors`: push-forwards along partial maps of prime
  divisors compose.
* `MMP.Fourfold.Crepant.compHom_eq_of_isInverse`,
  `MMP.Fourfold.Crepant.eq_of_apply_eq_of_coheight_le_one` and
  `MMP.Fourfold.Crepant.coheight_genericPoint_le_one`: generalities on inverses of birational
  morphisms and points of coheight at most one.

## Implementation notes

The step is recorded as a birational map `g : Y ⤏ Y⁺` with the morphisms realizing it, all over
`S`; the canonical divisor and boundary of `Y⁺` are `g_* K_Y` and `g_* C`, so that the adjoints
of `Y`, `Y⁺` and `Z` are cut out by one rational top form, as in `MMP.Fourfold.IsNefWeakModel`.
A divisorial contraction is a `(K_Y + C)`-negative extremal contraction
(`MMP.Flips.IsNegativeExtremalContraction`) that is a birational morphism whose exceptional set
is a prime divisor; a flip is `MMP.Flips.IsFlip` of a `(K_Y + C)`-negative extremal
contraction. The models are projective varieties over `S`, so `Y⁺` is assumed projective. The
comparison coefficient of a prime `G` of `Y` is read on any common projective birational model
`p : W ⟶ Y`, `q : W ⟶ Z` at the strict transform of `G`; it does not depend on the model.
Fibre type means `dim V < dim Y`. The base field has characteristic zero, where the smooth
common resolutions that `MMP.Fourfold.IsNefWeakModel` asks for exist.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

universe u

namespace MMP.Fourfold

namespace Crepant

/-! ### Generalities on points and partial maps -/

section Generalities

/-- A morphism of irreducible schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_apply_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) :
    IsDominant f := by
  rw [isDominant_iff]
  intro y
  have hy : y ∈ closure ({genericPoint Y} : Set Y) := by
    rw [(genericPoint_spec Y).def]; trivial
  have hmem : genericPoint Y ∈ Set.range (f : X → Y) := ⟨genericPoint X, h⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hy

/-- **The point over a codimension-one point.** Let `f : X ⟶ Y` be a separated dominant morphism
of normal integral schemes inducing an isomorphism of function fields, and `y ∈ Y` a point of
coheight at most one. Then `f` induces an isomorphism of local rings at every point over `y`, and
two points over `y` coincide. -/
private theorem isIso_stalkMap_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : Order.coheight (f x) ≤ 1) :
    IsIso (f.stalkMap x) := by
  have := valuationRing_stalk_of_coheight_le_one hx
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

/-- Two points of `X` over the same point of coheight at most one coincide, along a separated
dominant morphism of integral schemes, to a normal scheme, inducing an isomorphism of function
fields. -/
theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  have : IsIso (f.stalkMap x₂) :=
    isIso_stalkMap_of_coheight_le_one f hf (by rw [h]; exact hx)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- The coheight of the generic point of a prime divisor is at most one. -/
theorem coheight_genericPoint_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight P.genericPoint ≤ 1 :=
  P.coheight_genericPoint.le

/-- The coheight of the generic point is zero, hence at most one. -/
private theorem coheight_genericPoint_scheme_le_one (X : Scheme.{u}) [IrreducibleSpace X] :
    Order.coheight (genericPoint X) ≤ 1 := by
  have : IsMax (genericPoint X) := fun y _ =>
    (genericPoint_spec X).specializes (Set.mem_univ y)
  rw [Order.coheight_eq_zero.mpr this]
  exact zero_le_one

/-- Two partial maps with the same domain representing the same rational map to a separated
scheme are equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

/-- The partial map given by the restriction of `g` to `U`, composed with `q`, represents
`g ∘ q`. -/
private theorem toRationalMap_restrict_comp {X Y Z : Scheme.{u}} (g : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hle : U ≤ g.domain) (q : Y ⟶ Z) :
    (⟨U, hU, (g.restrict U hU hle).hom ≫ q⟩ : X.PartialMap Z).toRationalMap =
      g.toRationalMap.compHom q := by
  rw [← Scheme.PartialMap.restrict_toRationalMap g U hU hle,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-- The partial map given by the inclusion of a dense open `U`, composed with `q`, represents
`q`. -/
private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- Two representatives, restricted to a common dense open `U` and composed with morphisms to a
separated scheme, agree on `U` when the composite rational maps agree. -/
private theorem comp_eq_comp_of_compHom_eq {X Y₁ Y₂ Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g₁ : X.PartialMap Y₁)
    (g₂ : X.PartialMap Y₂) (h₁ : U ≤ g₁.domain) (h₂ : U ≤ g₂.domain) (q₁ : Y₁ ⟶ Z)
    (q₂ : Y₂ ⟶ Z) (h : g₁.toRationalMap.compHom q₁ = g₂.toRationalMap.compHom q₂) :
    (X.homOfLE h₁ ≫ g₁.hom) ≫ q₁ = (X.homOfLE h₂ ≫ g₂.hom) ≫ q₂ :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g₁ hU h₁ q₁).trans
    (h.trans (toRationalMap_restrict_comp g₂ hU h₂ q₂).symm))

/-- A representative restricted to a dense open `U` and composed with a morphism agrees on `U`
with a morphism `r` when the composite rational map is `r`. -/
private theorem comp_eq_ι_comp_of_compHom_eq {X Y Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g : X.PartialMap Y)
    (h₁ : U ≤ g.domain) (q : Y ⟶ Z) (r : X ⟶ Z)
    (h : g.toRationalMap.compHom q = r.toRationalMap) :
    (X.homOfLE h₁ ≫ g.hom) ≫ q = U.ι ≫ r :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g hU h₁ q).trans
    (h.trans (toRationalMap_ι_comp hU r).symm))

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
theorem compHom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]

/-- A morphism whose composite with `s` is a given separated morphism is separated. -/
private theorem isSeparated_of_comp_eq {X Y T : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ T}
    {t : X ⟶ T} (h : f ≫ s = t) [IsSeparated t] : IsSeparated f := by
  subst h
  exact IsSeparated.of_comp f s

/-- **Cancelling a local isomorphism at a codimension-one point.** If `f ≫ g` induces an
isomorphism of local rings at `x`, and `g` is a separated dominant morphism of normal integral
schemes inducing an isomorphism of function fields with `f x` over a point of coheight at most
one, then `f` induces an isomorphism of local rings at `x`. -/
private theorem isIso_stalkMap_of_isIso_comp {X Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (x : X) [h : IsIso ((f ≫ g).stalkMap x)]
    (hx : Order.coheight (g (f x)) ≤ 1) : IsIso (f.stalkMap x) := by
  have := isIso_stalkMap_of_coheight_le_one g hg hx
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap (f x)) (f.stalkMap x) this h

end Generalities

/-! ### Pull-backs along composites -/

section Pullback

/-- **Pull-backs of `ℝ`-Cartier divisors along a composite**: for `Z` quasi-compact, if `G = f^*D`
and `G' = g^*G`, then `G' = (g ≫ f)^*D`. -/
theorem _root_.MMP.Flips.IsRCartierPullback.comp {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {f : Y ⟶ X} {g : Z ⟶ Y}
    [IsDominant f] [IsDominant g] {D : RDivisor X} {G : RDivisor Y} {G' : RDivisor Z}
    (h : IsRCartierPullback f D G) (h' : IsRCartierPullback g G G') :
    IsRCartierPullback (g ≫ f) D G' := by
  obtain ⟨m, r, L, L', hLc, hD, hpb, rfl⟩ := h
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  have hL'' : ∀ j, (L' j).IsPullback g (map_componentGenericPoint_notMem_supp_of_isDominant g _)
      ((L' j).pullback (hL'c j) (map_componentGenericPoint_notMem_supp_of_isDominant g _)) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  obtain rfl := IsRCartierPullback.eq g h' ⟨m, r, L', _, hL'c, rfl, fun j => ⟨_, hL'' j⟩, rfl⟩
  exact ⟨m, r, L, _, hLc, hD, fun j =>
    ⟨map_componentGenericPoint_notMem_supp_of_isDominant (g ≫ f) _,
      MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hpb j).2 (hL'' j) _⟩, rfl⟩

/-- **Pulling a pull-back back once more.** Let `g^*M = D` be an `ℝ`-Cartier pull-back and
`f : V ⟶ W` dominant from a quasi-compact normal integral scheme. Then `M` has a pull-back `G`
along `f ≫ g` (`MMP.Flips.IsRCartierPullback.comp`, with `G = f^*D`) whose coefficient along a
prime divisor `E` of `V` dominating a prime divisor `P` of `W` with an isomorphism of local rings
is the coefficient of `D` along `P`. -/
private theorem exists_isRCartierPullback_comp {V W Z : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      ∀ (E : MMP.Mori.PrimeDivisor V) (P : MMP.Mori.PrimeDivisor W),
        f E.genericPoint = P.genericPoint → IsIso (f.stalkMap E.genericPoint) →
          G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, -, hpb, rfl⟩ := id hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  have hL'' : ∀ j, (L' j).IsPullback f (map_componentGenericPoint_notMem_supp_of_isDominant f _)
      ((L' j).pullback (hL'c j) (map_componentGenericPoint_notMem_supp_of_isDominant f _)) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  refine ⟨_, hD.comp ⟨m, r, L', _, hL'c, rfl, fun j => ⟨_, hL'' j⟩, rfl⟩, fun E P heq hiso => ?_⟩
  rw [coeff_sum_smul_toRDivisor, coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E P heq (hL'c j) (hL'' j)

end Pullback

/-! ### Dominance -/

section Dominance

/-- The partial map underlying a partial isomorphism is dominant. -/
private theorem isDominant_toPartialMap_hom {X Y : Scheme.{u}} (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

/-- If `a ≫ p` is dominant, with `p` a separated dominant morphism of integral schemes inducing
an isomorphism of function fields onto a normal scheme, then `a` is dominant. -/
private theorem isDominant_of_comp_eq {V W T : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (a : V ⟶ W) (p : W ⟶ T) [IsSeparated p]
    [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) [IsDominant (a ≫ p)] :
    IsDominant a := by
  refine isDominant_of_apply_genericPoint a ?_
  have h1 : p (a (genericPoint V)) = genericPoint T := by
    rw [← Scheme.Hom.comp_apply]; exact MMP.Positivity.map_genericPoint_eq_of_isDominant (a ≫ p)
  have h2 : p (genericPoint W) = genericPoint T :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant p
  refine (eq_of_apply_eq_of_coheight_le_one p hp (h1.trans h2.symm) ?_).symm
  rw [h2]; exact coheight_genericPoint_scheme_le_one T

end Dominance

/-! ### Composites of rational maps -/

section Composition

/-- **A representative of a composite.** If `f` maps a dense open `O ⊆ dom f` into `dom g`
through `β`, then `g ∘ f` is represented on `O` by `β` followed by `g`. -/
private theorem comp_toRationalMap_eq {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

/-- A birational map is dominant. -/
theorem isDominant_of_isBirational {X Y : Scheme.{u}} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsBirational φ) : φ.IsDominant := by
  obtain ⟨e, rfl⟩ := hφ
  have := isDominant_toPartialMap_hom e
  infer_instance

/-- A birational map followed by its inverse is the identity. -/
theorem comp_eq_id_of_isInverse {X Y : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {h : Y.RationalMap X}
    (H : RationalMap.IsInverse f h) : f.comp h = Scheme.RationalMap.id X := by
  obtain ⟨e, rfl, rfl⟩ := H
  have := isDominant_toPartialMap_hom e
  rw [comp_toRationalMap_eq e.toPartialMap e.symm.toPartialMap (O := e.source) e.dense_source le_rfl
    e.iso.hom (by
      change e.iso.hom ≫ e.target.ι = X.homOfLE le_rfl ≫ e.iso.hom ≫ e.target.ι
      rw [Scheme.homOfLE_rfl, Category.id_comp])]
  have : (⟨e.source, e.dense_source, e.iso.hom ≫ e.symm.toPartialMap.hom⟩ : X.PartialMap X) =
      ⟨e.source, e.dense_source, e.source.ι ≫ 𝟙 X⟩ := by
    congr 1
    change e.iso.hom ≫ e.iso.inv ≫ e.source.ι = _
    simp
  exact (congrArg Scheme.PartialMap.toRationalMap this).trans (toRationalMap_ι_comp _ (𝟙 X))

/-- A partial map which is an open immersion represents a birational map. -/
private theorem isBirational_of_isOpenImmersion {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (c : X.PartialMap Y) [IsOpenImmersion c.hom] [Nonempty c.domain] :
    RationalMap.IsBirational c.toRationalMap := by
  have hd : Dense (c.hom.opensRange : Set Y) :=
    c.hom.opensRange.2.dense ⟨_, Classical.arbitrary c.domain, rfl⟩
  refine ⟨⟨c.domain, c.dense_domain, c.hom.opensRange, hd, c.hom.isoOpensRange⟩, ?_⟩
  change Scheme.PartialMap.toRationalMap
    ⟨c.domain, c.dense_domain, c.hom.isoOpensRange.hom ≫ c.hom.opensRange.ι⟩ = _
  rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.homOfLE_ι X (inf_le_left : U ≤ U₁), Category.assoc]
    infer_instance
  have := IsOpenImmersion.of_comp (f.resLE U₂ U hle) U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U (U.2.dense hne)

/-- Composition on the left respects equality of the first map. -/
theorem comp_eq_comp_of_eq {X Y Z : Scheme.{u}} [IrreducibleSpace X] [Nonempty Y]
    {f f' : X ⤏ Y} [f.IsDominant] [f'.IsDominant] (h : f = f') (g : Y ⤏ Z) :
    f.comp g = f'.comp g := by
  subst h; rfl

/-- **Uniqueness of a section of a birational morphism.** If `p : W ⟶ Z` is a dominant morphism
with inverse `ψ`, a dominant rational map `χ : Z ⤏ W` with `p ∘ χ = id` is `ψ`. -/
theorem eq_of_compHom_eq_id {Z W : Scheme.{u}} [IsIntegral Z] [IsIntegral W]
    {p : W ⟶ Z} [IsDominant p] {ψ χ : Z.RationalMap W} [χ.IsDominant]
    (hψ : RationalMap.IsInverse p.toRationalMap ψ)
    (hχ : χ.compHom p = Scheme.Hom.toRationalMap (𝟙 Z)) : χ = ψ := by
  calc χ = χ.comp (Scheme.RationalMap.id W) := (Scheme.RationalMap.comp_id χ).symm
    _ = χ.comp (p.toRationalMap.comp ψ) := by rw [comp_eq_id_of_isInverse hψ]
    _ = (χ.comp p.toRationalMap).comp ψ := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id Z).comp ψ :=
        comp_eq_comp_of_eq (by rw [Scheme.RationalMap.comp_toRationalMap, hχ]) ψ
    _ = ψ := Scheme.RationalMap.id_comp ψ

end Composition

/-! ### Pull-backs of rational forms along birational morphisms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k]

/-- Along a dominant morphism inducing an isomorphism of function fields, the pull-back of a
nonzero rational form is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  have h1 : pullbackRationalPluriForms sX f τ =
      pullbackFormsAlong (K' := V.functionField) hω m τ := pullbackForms_eq hω m τ
  rw [h1]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- Along a dominant morphism inducing an isomorphism of function fields, every rational form is
a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (σ : RationalPluriForms (f ≫ sX) d m) :
    ∃ τ : RationalPluriForms sX d m, pullbackRationalPluriForms sX f τ = σ ∧ (σ ≠ 0 → τ ≠ 0) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let B' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  let B := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (B'.repr σ ())
  refine ⟨c • B (), ?_, fun hσ => smul_ne_zero ?_ (B.ne_zero ())⟩
  swap
  · rintro rfl
    rw [map_zero] at hc
    apply hσ
    have h2 := (B'.sum_repr σ).symm
    simp only [← hc, Finset.univ_unique, Finset.sum_singleton, zero_smul] at h2
    exact h2
  change pullbackForms (K := X.functionField) (K' := V.functionField) m (c • B ()) = σ
  rw [pullbackForms_eq hω, pullbackFormsAlong, show B.repr (c • B ()) () = c by simp]
  change functionFieldMap f c • B' () = σ
  rw [hc]
  simpa using B'.sum_repr σ

/-- The order of a rational form does not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s s' : V ⟶ Spec (.of k)}
    (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m) (E : MMP.Mori.PrimeDivisor V) :
    E.ordForm (cast (congrArg (fun t => RationalPluriForms t d m) h) τ) = E.ordForm τ := by
  subst h; rfl

private theorem cast_ne_zero {V : Scheme.{u}} [IsIntegral V] {s s' : V ⟶ Spec (.of k)}
    (h : s = s') {d : ℕ} {m : ℤ} {τ : RationalPluriForms s d m} (hτ : τ ≠ 0) :
    cast (congrArg (fun t => RationalPluriForms t d m) h) τ ≠ 0 := by
  subst h; exact hτ

end Forms

/-! ### The comparison of two nef weak models -/

section Comparison

variable {k : Type u} [Field k] {Y Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    {sY : Y ⟶ Spec (.of k)} {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}
    [QuasiCompact s₁] [QuasiCompact s₂] {sS : S ⟶ Spec (.of k)}
    {πY : Y ⟶ S} {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ₁ : Y.RationalMap Z₁} {φ₂ : Y.RationalMap Z₂}

/-- A rational map `Y ⤏ V` inverse to a proper morphism `p : V ⟶ Y` is defined at the generic
point of every prime divisor of `Y`. -/
private theorem exists_rep_mem_domain {V : Scheme.{u}} [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p] {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ g : Y.PartialMap V, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
  have hhp := compHom_eq_of_isInverse hinv
  obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Y) p h hhp
      (coheight_genericPoint_le_one Q))
  exact ⟨g, hg', hg⟩

/-- The adjoint `K_Z + C_Z` of a nef weak model is a real combination of Cartier divisors. -/
private theorem isCartierCombination_logCanonicalDivisor {πZ : Z₁ ⟶ S}
    (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) :
    MMP.Flips.IsCartierCombination
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)) := by
    obtain ⟨m, r, L, hLc, heq, -⟩ := h₁.isRelativelyNef
    exact ⟨m, r, L, hLc, by rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

end Comparison

end Crepant

namespace SamePrimes

open CategoryTheory.Limits

/-- A prime divisor with a divisorial transform is not exceptional. -/
private theorem not_isExceptional_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    ¬ MMP.Mori.RationalMap.IsExceptional φ P := by
  rw [MMP.Mori.RationalMap.isExceptional_iff]
  intro hex
  have h2 := hex (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    ← MMP.Mori.RationalMap.support_transformPrimeDivisor h] at h2
  have h3 := h2 F.genericPoint (by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl)
  rw [F.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

/-- If `P` is not exceptional for `φ = q ∘ g`, then `q(g(η_P))` has coheight at most one. -/
theorem coheight_apply_le_one_of_not_isExceptional {X W Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    (g : X.PartialMap W) (hg : (g.compHom q).toRationalMap = φ) (hP : P.genericPoint ∈ g.domain)
    (hnex : ¬ MMP.Mori.RationalMap.IsExceptional φ P) :
    Order.coheight (q (g.hom ⟨P.genericPoint, hP⟩)) ≤ 1 := by
  by_contra h2
  refine hnex (Or.inr ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨_, hP, hg⟩, ?_⟩)
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  have hx' : x ∈ (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) := hx
  rw [MMP.Flips.coe_transform_eq_closure_singleton (g.compHom q) hg P hP] at hx'
  have h2' : 2 ≤ Order.coheight (q (g.hom ⟨P.genericPoint, hP⟩)) := by
    simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h2)
  exact h2'.trans (Order.coheight_anti
    (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hx')))

end SamePrimes

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
theorem _root_.MMP.Flips.isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
theorem _root_.MMP.Flips.isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

/-- Every value of `D · C` is `∑ r_j (L_j · C)`, for any presentation `D = ∑ r_j L_j`. -/
theorem _root_.MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber (C : ProperCurve sX)
    {D : RDivisor X} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber k sX D r' L' C x) :
    x = ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) := by
  subst hD
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r' L' r L _ _ hx
    (isRIntersectionNumber_sum_degreeOn k sX C r L hL)

end Intersection

section Geometry

/-- A combination of Cartier divisors, written with `Divisor.toRDivisor`, is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_eq_sum {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] {D : RDivisor Y} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsCartierCombination D :=
  ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor `P` has a
Cartier multiple `m_P P`, and `D = ∑ (D_P / m_P) (m_P P)`. -/
private theorem isCartierCombination_of_isQFactorial {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Fourfold.IsQFactorial sY) (D : RDivisor Y) : IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine isCartierCombination_of_eq_sum (fun j => D (e.symm j) / m (e.symm j))
    (fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1)
    (fun j => hc _) ?_
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- A prime divisor of `W` that is not exceptional over `Y` lies over a prime divisor `P` of `Y`,
`q` is a local isomorphism at its generic point, and the coefficient of `P` in a push-forward
`q_* D` is the coefficient of `E` in `D`. -/
theorem exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
    {k : Type u} [Field k] {W Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    (q : W ⟶ Y) (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hqb : IsBirationalMorphism q)
    (E : MMP.Mori.PrimeDivisor W) (hE : ¬ IsExceptionalPrimeDivisor sY q E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, q E.genericPoint = P.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) ∧
      ∀ D : RDivisor W, MMP.Mori.RationalMap.transformDivisor q.toRationalMap D P = D E := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated q := IsSeparated.of_comp q sY
  haveI : IsDominant q := hqb.isDominant
  set DE : ProperDivisorOver k sY := ProperDivisorOver.mk ⟨W, q, hW, hqb, E⟩ inferInstance
  have hnot : ¬ DE.IsExceptional := fun h => hE ⟨hW, hqb, inferInstance, h⟩
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    intro h2
    refine hnot ?_
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (DE.toDivisorOver.f DE.toDivisorOver.E.genericPoint)
    rw [← hd]
    gcongr
    rw [← WithBot.coe_ofNat]
    exact WithBot.coe_le_coe.mpr h2
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  have hEP : q E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv
  obtain ⟨E', hE'P, hiso', htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hqb P
  have hbij := hqb.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hEP]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (q E'.genericPoint)) := by rw [hE'P]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij E.genericPoint
  have hEE' : E'.genericPoint = E.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hEP.trans hE'P.symm)
  have hEE : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEE'
  subst hEE
  exact ⟨P, hEP, hiso, htr⟩

/-- **The projection formula for the pull-back of a Cartier divisor.** If `L'` is the pull-back of
the Cartier divisor `L` along `f` and `f(C') = C` is a proper curve, then
`(L' · C') = [k(C') : k(C)] (L · C)`. -/
theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {L : Divisor Y} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : Divisor X} (h : L.IsPullback f hB L') (hc : L'.IsCartier) (C' : ProperCurve sX)
    (C : ProperCurve sY) (hC : f C'.point = C.point) :
    (L'.degreeOn k sX C'.ι C'.dim_le hc : ℝ) =
      (residueFieldDegree f C'.point : ℝ) * (L.degreeOn k sY C.ι C.dim_le hL : ℝ) := by
  obtain rfl := Divisor.IsPullback.pullback_eq hL h
  obtain ⟨c, hcC⟩ := C
  dsimp only at hC
  subst hC
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hL hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos hcC]
  simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul]
  push_cast
  rfl

end Geometry

section CurveLifting

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [TopologicalSpace.NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

variable {k : Type u} [Field k]

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over `k`: it factors through its scheme-theoretic image, which is `C'`. -/
private lemma isProper_comp_of_closure_range {X B : Scheme.{u}}
    {sB : B ⟶ Spec (.of k)} (C' : ProperCurve sB) (φ : X ⟶ B) [IsReduced X] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {C'.point}) : IsProper (φ ≫ sB) := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {C'.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB); rw [hker]; exact C'.isProper_ι_comp
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting proper curves.** Let `h : A ⟶ B` be a proper surjective morphism of schemes of
finite type over `k`. Every proper curve `C'` on `B` is `h(C)` for a proper curve `C` on `A`
whose function field is a finite extension of that of `C'`. -/
theorem exists_properCurve_map_eq {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k))
    (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] [QuasiCompact sB] (h : A ⟶ B) [IsProper h] [Surjective h]
    (hh : h ≫ sB = sA) (C' : ProperCurve sB) :
    ∃ C : ProperCurve sA, h C.point = C'.point ∧ residueFieldDegree h C.point ≠ 0 := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base (h.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = C'.point → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  refine ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range C' φ hclr⟩, haξ, ?_⟩
  -- `a` is a closed point of its fibre, so `κ(a)` is finite over `κ(h(a))`
  have : LocallyOfFiniteType h := by
    have : LocallyOfFiniteType (h ≫ sB) := hh ▸ inferInstance
    exact locallyOfFiniteType_of_comp h sB
  have hcl : IsClosed ({h.asFiber a} : Set (h.fiber (h a))) := by
    have hsub : IsClosed ({⟨a, rfl⟩} : Set (h.base ⁻¹' {h a})) := by
      refine isClosed_of_closure_subset fun b hb => ?_
      have hab : (⟨a, rfl⟩ : h.base ⁻¹' {h a}) ⤳ b := specializes_iff_mem_closure.mpr hb
      exact Subtype.ext (hamax b.1 ((Set.mem_singleton_iff.mp b.2).trans haξ)
        (hab.map continuous_subtype_val))
    have hpre : ({h.asFiber a} : Set (h.fiber (h a))) = h.fiberHomeo (h a) ⁻¹' {⟨a, rfl⟩} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        simp [Scheme.Hom.asFiber]
      · intro hz
        rw [Scheme.Hom.asFiber, ← hz, Homeomorph.symm_apply_apply]
    rw [hpre]
    exact (h.fiberHomeo (h a)).isClosed_preimage.mpr hsub
  have hfin := (isClosed_asFiber_iff_finite_residueField h a).mp hcl
  letI := (h.residueFieldMap a).hom.toAlgebra
  exact Module.finrank_pos.ne'

end CurveLifting

section Nef

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- **Pull-backs of divisors nef over a base are nef along morphisms over it.** Let
`p : W ⟶ Y` and `q : W ⟶ Z` be morphisms with `p ≫ πY = q ≫ πZ` for `πY : Y ⟶ S`,
`πZ : Z ⟶ S`, and `q` proper. If `M` is an `ℝ`-Cartier divisor on `Z` nef over `S`, its pull-back
`q^*M` is `p`-nef. -/
theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z S : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
    [LocallyOfFiniteType sZ] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y)
    (q : W ⟶ Z) [IsProper q] [QuasiCompact (q ≫ sZ)] (hpq : p ≫ πY = q ≫ πZ)
    {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsRelativelyNef k (q ≫ sZ) p M' := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  obtain ⟨m, r, L₀, L₁, hL₀, hMeq, hpb, hM'eq⟩ := hM'
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  refine ⟨m, r, _, hL₁c, hM'eq, fun C hC x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) C r _ hL₁c
  rw [← hM'eq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) C).1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sZ (q C.point)
  · obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ProperCurve sZ, C₀.point = q C.point := ⟨⟨_, hc⟩, rfl⟩
    have hC₀c : C₀.IsContractedBy πZ := by
      intro z hz
      rw [hC₀] at hz ⊢
      have hsub : closure ({q C.point} : Set Z) ⊆ q '' closure ({C.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨w, hw, rfl⟩ := hsub hz
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, hC w hw]
    have hdeg : ∀ j, ((((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) : ℤ) : ℝ) =
        (residueFieldDegree q C.point : ℝ) * (L₀ j).degreeOn k sZ C₀.ι C₀.dim_le (hL₀ j) := by
      intro j
      rw [degreeOn_pullback_eq_mul q (hL₀ j) (hB j) C C₀ hC₀]
      push_cast; rfl
    obtain ⟨mM, rM, LM, hLM, hMeq', hMall⟩ := hM
    have hMx := isRIntersectionNumber_sum_degreeOn k sZ C₀ rM LM hLM
    rw [← hMeq'] at hMx
    have h0 := isRIntersectionNumber_sum_degreeOn k sZ C₀ r L₀ hL₀
    rw [← hMeq] at h0
    have hnn := hMall C₀ hC₀c _ hMx
    rw [(IsRIntersectionNumber.eq_and_linear k sZ C₀).1 _ _ _ _ _ _ _ hMx h0] at hnn
    simp only [hdeg, mul_left_comm (r _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) hnn
  · have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) = 0 := fun j => degreeOn_pullback_eq_zero q (hL₀ j) (hB j) C hc
    simp [hdeg]

/-- **Nef descent along a proper surjection.** Let `q : V ⟶ Y` be a proper surjective morphism of
schemes of finite type over `k`, `π : Y ⟶ S`, and `G` a pull-back of the `ℝ`-Cartier divisor `D`
along `q`. If `G` is nef over `S`, so is `D`. -/
theorem IsRelativelyNef.of_isRCartierPullback_of_surjective {k : Type u} [Field k]
    {V Y S : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian Y] [IsNormal Y] {sV : V ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sV] [QuasiCompact sV] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsSeparated sY] (q : V ⟶ Y) [IsProper q] [Surjective q] (hq : q ≫ sY = sV) (π : Y ⟶ S)
    {D : RDivisor Y} {G : RDivisor V} (hG : IsRCartierPullback q D G)
    (hnef : IsRelativelyNef k sV (q ≫ π) G) : IsRelativelyNef k sY π D := by
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨m, r, L, L', hL, hD, hpb, hGeq⟩ := hG
  choose hB hpbj using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL j) (hpbj j)]
    exact (hL j).isCartier_pullback q (hB j)
  refine ⟨m, r, L, hL, hD, fun C hC x hx => ?_⟩
  obtain ⟨C', hC'q, hd⟩ := exists_properCurve_map_eq sV sY q hq C
  have hcon : C'.IsContractedBy (q ≫ π) := by
    intro v hv
    have hqv : q v ∈ closure {C.point} := by
      rw [← hC'q]
      exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hv).map q.continuous)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC (q v) hqv, hC'q]
  obtain ⟨mG, rG, LG, hLG, hGeq', hGall⟩ := hnef
  have hxG' := isRIntersectionNumber_sum_degreeOn k sV C' rG LG hLG
  rw [← hGeq'] at hxG'
  have hxG := isRIntersectionNumber_sum_degreeOn k sV C' r L' hL'c
  rw [← hGeq] at hxG
  have hnn := hGall C' hcon _ hxG'
  rw [(IsRIntersectionNumber.eq_and_linear k sV C').1 _ _ _ _ _ _ _ hxG' hxG] at hnn
  have hxD := isRIntersectionNumber_sum_degreeOn k sY C r L hL
  rw [← hD] at hxD
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hxD]
  simp only [fun j => degreeOn_eq_mul_of_isPullback q hq (hL j) (hpbj j) (hL'c j) C' C hC'q,
    mul_left_comm (r _), ← Finset.mul_sum] at hnn
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast Nat.pos_of_ne_zero hd)).mp hnn

end Nef

section RationalMaps

open CategoryTheory.Limits

/-- Composing a rational map with two morphisms in turn is composing it with their composite. -/
private theorem compHom_compHom {X Y Z T : Scheme.{u}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- The rational map of a morphism, composed with a morphism, is the rational map of the
composite. -/
private theorem toRationalMap_compHom {X Z T : Scheme.{u}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-! ### Function fields along a common resolution -/

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p`
and `q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p]
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p e he1]

/-! ### Comparison of the two composites to the base -/

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of a map `φ` over `Z`, the two composites
`W ⟶ Z` agree. -/
theorem comp_eq_comp_of_isOver {X Y Z W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (πX : X ⟶ Z) (πY : Y ⟶ Z) {φ : X.RationalMap Y}
    (hφZ : MMP.Flips.RationalMap.IsOver πX πY φ) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
    [IsDominant p] (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) : p ≫ πX = q ≫ πY := by
  have h1 := specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp
  have h2 : (p ≫ πX).toRationalMap = (q ≫ πY).toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom]
    calc W.fromSpecStalk (genericPoint W) ≫ p ≫ πX
        = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
            X.fromSpecStalk (genericPoint X) ≫ πX := by
          rw [← Category.assoc (Spec.map _), functionFieldMap_fromSpecStalk, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField ≫ πY := by
          rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hφZ,
            MMP.Flips.RationalMap.fromFunctionField_hom]
      _ = W.fromSpecStalk (genericPoint W) ≫ q ≫ πY := by
          rw [← Category.assoc, h1, Category.assoc]
  have H := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h2)
  rw [Scheme.Hom.toPartialMap_hom] at H
  exact (cancel_epi _).mp H

end RationalMaps

section CurveInequality

variable {k : Type u} [Field k]

/-- An effective `ℝ`-divisor on a smooth scheme has nonnegative degree on a proper curve whose
generic point is outside its support. -/
private theorem nonneg_of_isRIntersectionNumber {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (hsm : IsSmoothScheme sX)
    {A : RDivisor X} (hA : ∀ P, 0 ≤ A.coeff P) (C : ProperCurve sX) (hC : C.point ∉ A.supp)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX A r L C x) : 0 ≤ x := by
  classical
  let e := A.support.equivFin
  let P : Fin A.support.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j : _)
  let PD : Fin A.support.card → Divisor X := fun j => Finsupp.single (P j) 1
  have hL : ∀ j, (PD j).IsCartier := fun j =>
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hterm : ∀ Q : MMP.Mori.PrimeDivisor X,
      A Q • Divisor.toRDivisor (Finsupp.single Q (1 : ℤ) : Divisor X) = Finsupp.single Q (A Q) := by
    intro Q
    ext Q'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : Q = Q'
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  have hAeq : A = ∑ j, A (P j) • Divisor.toRDivisor (PD j) := by
    rw [Equiv.sum_comp e.symm (fun Q : A.support => A Q •
      Divisor.toRDivisor (Finsupp.single (Q : MMP.Mori.PrimeDivisor X) (1 : ℤ) : Divisor X))]
    rw [Finset.sum_coe_sort A.support (fun Q => A Q •
      Divisor.toRDivisor (Finsupp.single Q (1 : ℤ) : Divisor X))]
    simp_rw [hterm]
    exact (Finsupp.sum_single A).symm
  rw [eq_sum_degreeOn_of_isRIntersectionNumber k sX C _ _ hL hAeq hx]
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hA _) ?_
  have hne : ∃ c : C.scheme, C.ι c ∉ (PD j).supp := by
    refine ⟨genericPoint C.scheme, ?_⟩
    rw [ProperCurve.ι_genericPoint]
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hEP : P j = E := by
      by_contra h
      exact hE (DivisorWithCoeffs.coeff_single_of_ne h _)
    subst hEP
    have hPA : A (P j) ≠ 0 := Finsupp.mem_support_iff.mp (e.symm j).2
    exact hC (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P j, hPA, hxE⟩)
  have h0 := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX C.ι C.dim_le _ (hL j)
    (Finsupp.single_nonneg.mpr zero_le_one) hne).1
  exact_mod_cast h0

/-- **The curve inequality on a common resolution.** Let `p : W ⟶ Y`, `q : W ⟶ Z` be proper
morphisms over `S`, `p` surjective and `W` smooth, `L` an `ℝ`-Cartier divisor on `Y` and `M` an
`ℝ`-Cartier divisor on `Z` nef over `S`, with `p^*L - q^*M ≥ 0`. A proper curve `Γ ⊆ Y` over a
point of `S` whose generic point is not the image of a point of `Supp (p^*L - q^*M)` has
`L · Γ ≥ 0`. -/
private theorem nonneg_of_isRIntersectionNumber_of_resolution {Y Z S W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    [LocallyOfFiniteType sW] [QuasiCompact sW] (hWs : IsSmoothScheme sW)
    {πY : Y ⟶ S} {πZ : Z ⟶ S} (p : W ⟶ Y) (q : W ⟶ Z) [IsProper p] [IsProper q] [Surjective p]
    (hpY : p ≫ sY = sW) (hqZ : q ≫ sZ = sW) (hpq : p ≫ πY = q ≫ πZ)
    {L : RDivisor Y} {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M)
    {GY GZ : RDivisor W} (hGY : IsRCartierPullback p L GY) (hGZ : IsRCartierPullback q M GZ)
    (hA : ∀ P, 0 ≤ (GY - GZ).coeff P)
    (Γ : ProperCurve sY) (hΓ : Γ.IsContractedBy πY)
    (hΓB : Γ.point ∉ p '' ((GY - GZ).supp : Set W))
    {m : ℕ} {r : Fin m → ℝ} {Ls : Fin m → Divisor Y} {x : ℝ}
    (hx : IsRIntersectionNumber k sY L r Ls Γ x) : 0 ≤ x := by
  subst hqZ
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨Γ', hΓ'p, hd⟩ := exists_properCurve_map_eq (q ≫ sZ) sY p hpY Γ
  -- `q^*M` is nef over `S`
  have hnef : IsRelativelyNef k (q ≫ sZ) (p ≫ πY) GZ :=
    isRelativelyNef_of_isRCartierPullback (𝟙 S) πZ (p ≫ πY) q (by rw [Category.comp_id, hpq])
      hM hGZ
  have hcon : Γ'.IsContractedBy (p ≫ πY) := by
    intro w hw
    have hpw : p w ∈ closure {Γ.point} := by
      rw [← hΓ'p]
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hw).map p.continuous)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ (p w) hpw, hΓ'p]
  -- `p^*L · Γ' = [k(Γ') : k(Γ)] (L · Γ)`
  obtain ⟨mY, rY, LY, LY', hLY, hLeq, hpb, hGYeq⟩ := hGY
  choose hB hpbj using hpb
  have hLY'c : ∀ j, (LY' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hLY j) (hpbj j)]
    exact (hLY j).isCartier_pullback p (hB j)
  have hxY := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) Γ' rY LY' hLY'c
  rw [← hGYeq] at hxY
  have hxL := isRIntersectionNumber_sum_degreeOn k sY Γ rY LY hLY
  rw [← hLeq] at hxL
  have hxx := (IsRIntersectionNumber.eq_and_linear k sY Γ).1 _ _ _ _ _ _ _ hx hxL
  have hdeg : ∀ j, ((LY' j).degreeOn k (q ≫ sZ) Γ'.ι Γ'.dim_le (hLY'c j) : ℝ) =
      (residueFieldDegree p Γ'.point : ℝ) * ((LY j).degreeOn k sY Γ.ι Γ.dim_le (hLY j) : ℝ) :=
    fun j => degreeOn_eq_mul_of_isPullback p hpY (hLY j) (hpbj j) (hLY'c j) Γ' Γ hΓ'p
  -- `q^*M · Γ' ≥ 0`
  obtain ⟨mZ, rZ, LZ, hLZ, hGZeq, hnefall⟩ := hnef
  have hxZ := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) Γ' rZ LZ hLZ
  rw [← hGZeq] at hxZ
  have hZ0 := hnefall Γ' hcon _ hxZ
  -- `(p^*L - q^*M) · Γ' ≥ 0`
  have hA' := (IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) Γ').2 _ _ _ _ _ _ _ _ 1 (-1) hxY hxZ
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hA'
  have hA0 := nonneg_of_isRIntersectionNumber hWs hA Γ' (fun h => hΓB ⟨_, h, hΓ'p⟩) hA'
  have hdpos : (0 : ℝ) < residueFieldDegree p Γ'.point := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  simp only [hdeg, mul_left_comm (rY _), ← Finset.mul_sum] at hA0
  rw [← hxx] at hA0
  nlinarith

end CurveInequality

section FibreType

variable {k : Type u} [Field k]

/-- A divisor whose negative is `f`-ample is negative on every proper curve contracted by `f`. -/
private theorem exists_isRIntersectionNumber_neg {X V : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ V)
    {L : RDivisor X} (hL : IsRelativelyAntiAmple f L) (Γ : ProperCurve sX)
    (hΓ : Γ.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (Ls : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX L r Ls Γ x ∧ x < 0 := by
  obtain ⟨m, r, A, hm, hr, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hLeq' : L = ∑ j, (-r j) • Divisor.toRDivisor (A j) := by
    have hL' : L = -(-L) := (neg_neg L).symm
    rw [hL', hLeq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hx := isRIntersectionNumber_sum_degreeOn k sX Γ (fun j => -r j) A hAc
  rw [← hLeq'] at hx
  refine ⟨m, _, A, _, hx, ?_⟩
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j => by
    exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) Γ hΓ
  have hsum : 0 < ∑ j, r j * ((A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- A contraction is dominant: an open set missing its image has no sections upstairs. -/
private theorem isDominant_of_isContraction {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X} (hf : MMP.Flips.IsContraction k sX sY f) :
    IsDominant f := by
  have hfX := hf.isIso_app
  refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let V' : X.Opens := ⟨V, hV⟩
  have hbot : f ⁻¹ᵁ V' = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
  have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(X, V') :=
    (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
  obtain ⟨x, hx⟩ := hVne
  have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- **Curves in the fibres of a morphism of fibre type.** Let `f : Y ⟶ V` be a dominant proper
morphism of varieties with `dim V < dim Y`, `Y` proper over `k`. For every closed set `B ∌ η_Y`
there is a proper curve contracted by `f` whose generic point is outside `B`. -/
theorem exists_properCurve_isContractedBy_of_lt {Y V : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (hY : AlgebraicGeometry.IsVariety k sY)
    [IsProper sY] (hV : AlgebraicGeometry.IsVariety k sV) (f : Y ⟶ V) (hf : f ≫ sV = sY)
    [IsDominant f] [IsProper f] (hdim : topologicalKrullDim V < topologicalKrullDim Y)
    {B : Set Y} (hB : IsClosed B) (hηB : genericPoint Y ∉ B) :
    ∃ Γ : ProperCurve sY, Γ.IsContractedBy f ∧ Γ.point ∉ B := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsIntegral V := hV.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨U, hUo, hUd, -, hfib⟩ :=
    MMP.Foundations.exists_dense_isOpen_forall_irreducibleComponents_fiber_dim sY sV hY hV f hf
  have hηU : f (genericPoint Y) ∈ U := by
    rw [map_genericPoint_of_isDominant]
    obtain ⟨v, hv⟩ := hUd.nonempty
    exact ((genericPoint_spec V).mem_open_set_iff hUo).mpr ⟨v, trivial, hv⟩
  obtain ⟨y, ⟨hyU, hyB⟩, hyc⟩ := nonempty_inter_closedPoints (Z := f ⁻¹' U ∩ Bᶜ)
    ⟨genericPoint Y, hηU, hηB⟩
    ((hUo.preimage f.continuous).inter hB.isOpen_compl).isLocallyClosed
  have hyc' : IsClosed ({y} : Set Y) := mem_closedPoints_iff.mp hyc
  have hfyc : IsClosed ({f y} : Set V) := by
    rw [← Set.image_singleton]; exact f.isClosedMap _ hyc'
  set F : Set Y := f ⁻¹' {f y} with hF
  have hFc : IsClosed F := hfyc.preimage f.continuous
  let yF : F := ⟨y, rfl⟩
  set C := irreducibleComponent yF with hCdef
  have hCmem : C ∈ irreducibleComponents F := irreducibleComponent_mem_irreducibleComponents yF
  have hdC := hfib (f y) hyU C hCmem
  set C' : Set Y := Subtype.val '' C with hC'def
  have hC'irr : IsIrreducible C' :=
    isIrreducible_irreducibleComponent.image _ continuous_subtype_val.continuousOn
  have hC'cl : IsClosed C' :=
    hFc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hCmem)
  have hgen := hC'irr.isGenericPoint_genericPoint_closure
  rw [hC'cl.closure_eq] at hgen
  set η := hC'irr.genericPoint
  have hyC' : y ∈ C' := ⟨yF, mem_irreducibleComponent, rfl⟩
  have hηy : η ⤳ y := hgen.specializes hyC'
  have hηne : η ≠ y := by
    intro hη
    have hC'y : C' = {y} := by rw [← hgen.def, hη, hyc'.closure_eq]
    have : Subsingleton C := ⟨fun a b => by
      have ha : a.1.1 ∈ C' := ⟨a.1, a.2, rfl⟩
      have hb : b.1.1 ∈ C' := ⟨b.1, b.2, rfl⟩
      rw [hC'y] at ha hb
      exact Subtype.ext (Subtype.ext (ha.trans hb.symm))⟩
    have : Nonempty C := ⟨⟨yF, mem_irreducibleComponent⟩⟩
    rw [topologicalKrullDim_eq_zero_of_subsingleton, zero_add] at hdC
    exact hdim.ne hdC
  have hηB' : η ∉ B := fun h => hyB (hηy.mem_closed hB h)
  obtain ⟨y', hηy', -, hy'Z, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sY hηy hyc'
    (hB.union hyc') (Or.inr rfl) (by
      rintro (h | h)
      · exact hηB' h
      · exact hηne h)
  refine ⟨⟨y', hy'⟩, ?_, fun h => hy'Z (Or.inl h)⟩
  have hsubF : closure {y'} ⊆ F := by
    have h1 : closure ({y'} : Set Y) ⊆ C' := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hηy'))
        isClosed_closure
    exact h1.trans (Set.image_subset_iff.mpr fun c _ => c.2)
  intro x hx
  have h1 : f x = f y := hsubF hx
  have h2 : f y' = f y := hsubF (subset_closure rfl)
  exact h1.trans h2.symm

end FibreType

section PartThree

variable {k : Type u} [Field k]

open CategoryTheory.Limits in
/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
theorem isSeparated_terminal {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSeparated sX] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The image of the support of a divisor under a birational morphism of varieties misses the
generic point. -/
private theorem genericPoint_notMem_image_supp {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : AlgebraicGeometry.IsVariety k sY) (p : W ⟶ Y)
    (hW : AlgebraicGeometry.IsVariety k (p ≫ sY)) (hpb : IsBirationalMorphism p)
    (D : RDivisor W) : genericPoint Y ∉ p '' (D.supp : Set W) := by
  rintro ⟨w, hw, hpw⟩
  obtain ⟨E, -, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb
  have h1 := coheight_le_coheight_map sY (p ≫ sY) hY hW p rfl hdim.symm w
  rw [hpw] at h1
  have h0 : Order.coheight (genericPoint Y) = 0 :=
    Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
  have hs : E.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hwE
  have h2 : Order.coheight E.genericPoint ≤ Order.coheight w := Order.coheight_anti hs
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
  rw [h0] at h1
  have := h2.trans h1
  norm_num at this

/-- **No negative contraction of fibre type.** If `(Y, C)` has a nef weak model over a separated
base `S`, then `K_Y + C` admits no negative extremal contraction `f : Y ⟶ V` over `S` with
`dim V < dim Y`. -/
private theorem false_of_isNefWeakModel_of_lt {Y Z S V : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS] {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ : Y.RationalMap Z} (hφ : MMP.Fourfold.IsNefWeakModel sY sZ sS πY πZ KY C φ)
    {sV : V ⟶ Spec (.of k)} (πV : V ⟶ S) (f : Y ⟶ V)
    (hf : IsNegativeExtremalContraction k sY sV (logCanonicalDivisor KY C) f)
    (hfV : f ≫ πV = πY) (hdim : topologicalKrullDim V < topologicalKrullDim Y) : False := by
  obtain ⟨W, _, _, _, sW, p, q, h, hW, hWs, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, GY, GZ, hGY,
    hGZ, hA, -⟩ := hφ.exists_resolution
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hYv.1.toQuasiCompact
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsProper sY :=
    isProper_of_isProjectiveMorphism sY hφ.isProjectiveVariety_source.isProjective
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have : QuasiCompact sW := hW.toQuasiCompact
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsDominant p := hpb.isDominant
  have := isSeparated_terminal sS
  have hpq : p ≫ πY = q ≫ πZ := comp_eq_comp_of_isOver πY πZ hφ.isOver p q h hinv hhq
  have hBc : IsClosed (p '' ((GY - GZ).supp : Set W)) :=
    p.isClosedMap _ (DivisorWithCoeffs.isClosed_supp _)
  have hηB := genericPoint_notMem_image_supp hYv.1 p (by rw [hpY]; exact hW) hpb (GY - GZ)
  have := isDominant_of_isContraction hf.isContraction
  have : IsProper f := hf.isContraction.isProper
  obtain ⟨Γ, hΓ, hΓB⟩ := exists_properCurve_isContractedBy_of_lt hYv.1
    hf.isNormalVariety_target.1 f hf.isContraction.comp_eq hdim hBc hηB
  obtain ⟨m, r, Ls, x, hx, hxneg⟩ :=
    exists_isRIntersectionNumber_neg f hf.isRelativelyAntiAmple Γ hΓ
  have hΓS : Γ.IsContractedBy πY := fun y hy => by
    rw [← hfV, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ y hy]
  have := nonneg_of_isRIntersectionNumber_of_resolution hWs p q hpY hqZ hpq hφ.isRelativelyNef
    hGY hGZ hA Γ hΓS hΓB hx
  linarith

end PartThree

section PartTwo

variable {k : Type u} [Field k]

open CategoryTheory.Limits

/-- The exceptional set `Ex(f)` (points with no neighbourhood on which `f` is an open immersion)
is contained in the complement of the preimage of the biregular locus of `f`. -/
private theorem exceptionalSet_subset {X Y : Scheme.{u}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- **Comparison coefficients do not depend on the model.** Let `p : W ⟶ Y`, `q : W ⟶ Z` and
`p₀ : W₀ ⟶ Y`, `q₀ : W₀ ⟶ Z` be two models of `φ : Y ⤏ Z`: `p`, `p₀` proper birational with
inverses `h`, `h₀` and `q ∘ h = φ = q₀ ∘ h₀`. The pull-backs `q^*M` and `q₀^*M` of an
`ℝ`-Cartier divisor `M` on `Z` have the same coefficient along prime divisors `P ⊆ W`,
`P₀ ⊆ W₀` lying over the same prime divisor `G` of `Y`. -/
theorem coeff_eq_coeff_of_isRCartierPullback {Y Z W W₀ : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral W₀] [IsLocallyNoetherian W₀] [IsNormal W₀]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)] {φ : Y.RationalMap Z}
    (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W) [IsProper p] [IsSeparated p] [IsDominant q]
    (hpb : IsBirationalMorphism p) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (hh : h.compHom q = φ)
    (p₀ : W₀ ⟶ Y) (q₀ : W₀ ⟶ Z) (h₀ : Y.RationalMap W₀) [IsProper p₀] [IsSeparated p₀]
    [IsDominant q₀] (hp₀b : IsBirationalMorphism p₀)
    (hinv₀ : RationalMap.IsInverse p₀.toRationalMap h₀) (hh₀ : h₀.compHom q₀ = φ)
    {M : RDivisor Z} {GZ : RDivisor W} {GZ₀ : RDivisor W₀}
    (hGZ : IsRCartierPullback q M GZ) (hGZ₀ : IsRCartierPullback q₀ M GZ₀)
    (G : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor W) (P₀ : MMP.Mori.PrimeDivisor W₀)
    (hP : p P.genericPoint = G.genericPoint) (hP₀ : p₀ P₀.genericPoint = G.genericPoint) :
    GZ.coeff P = GZ₀.coeff P₀ := by
  have : IsDominant p := hpb.isDominant
  have : IsDominant p₀ := hp₀b.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hp₀bij := hp₀b.functionFieldMap_bijective
  obtain ⟨g, hg, hGg⟩ := Crepant.exists_rep_mem_domain hinv G
  obtain ⟨g₀, hg₀, hGg₀⟩ := Crepant.exists_rep_mem_domain hinv₀ G
  let U : Y.Opens := g.domain ⊓ g₀.domain
  have hU : Dense (U : Set Y) := by
    simp only [U, TopologicalSpace.Opens.coe_inf]
    exact g.dense_domain.inter_of_isOpen_left g₀.dense_domain g.domain.isOpen
  have hGU : G.genericPoint ∈ U := ⟨hGg, hGg₀⟩
  haveI : Nonempty U := ⟨⟨_, hGU⟩⟩
  haveI : IsNoetherian Y := {}
  haveI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set Y))
  have hle : U ≤ g.domain := inf_le_left
  have hle₀ : U ≤ g₀.domain := inf_le_right
  let a : U.toScheme ⟶ W := Y.homOfLE hle ≫ g.hom
  let b : U.toScheme ⟶ W₀ := Y.homOfLE hle₀ ≫ g₀.hom
  have hab : a ≫ q = b ≫ q₀ := Crepant.comp_eq_comp_of_compHom_eq hU g g₀ hle hle₀ q q₀
    (by rw [hg, hg₀, hh, hh₀])
  have hap : a ≫ p = U.ι := by
    have := Crepant.comp_eq_ι_comp_of_compHom_eq hU g hle p (𝟙 Y)
      (by rw [hg, Crepant.compHom_eq_of_isInverse hinv])
    rwa [Category.comp_id] at this
  have hbp : b ≫ p₀ = U.ι := by
    have := Crepant.comp_eq_ι_comp_of_compHom_eq hU g₀ hle₀ p₀ (𝟙 Y)
      (by rw [hg₀, Crepant.compHom_eq_of_isInverse hinv₀])
    rwa [Category.comp_id] at this
  obtain ⟨GU, hGU'⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq U G hGU
  have hx : U.ι GU.genericPoint = G.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hGU']
  have hpax : p (a GU.genericPoint) = G.genericPoint := by
    calc p (a GU.genericPoint) = (a ≫ p) GU.genericPoint := (Scheme.Hom.comp_apply _ _ _).symm
      _ = G.genericPoint := by rwa [hap]
  have hpbx : p₀ (b GU.genericPoint) = G.genericPoint := by
    calc p₀ (b GU.genericPoint) = (b ≫ p₀) GU.genericPoint := (Scheme.Hom.comp_apply _ _ _).symm
      _ = G.genericPoint := by rwa [hbp]
  have hax : a GU.genericPoint = P.genericPoint :=
    (Crepant.eq_of_apply_eq_of_coheight_le_one p hpbij (hpax.trans hP.symm)
      (by rw [hP]; exact Crepant.coheight_genericPoint_le_one G)).symm
  have hbx : b GU.genericPoint = P₀.genericPoint :=
    (Crepant.eq_of_apply_eq_of_coheight_le_one p₀ hp₀bij (hpbx.trans hP₀.symm)
      (by rw [hP₀]; exact Crepant.coheight_genericPoint_le_one G)).symm
  have haiso : IsIso (a.stalkMap GU.genericPoint) := by
    have : IsIso ((a ≫ p).stalkMap GU.genericPoint) := by rw [hap]; infer_instance
    exact Crepant.isIso_stalkMap_of_isIso_comp a p hpbij _
      (by rw [hpax]; exact Crepant.coheight_genericPoint_le_one G)
  have hbiso : IsIso (b.stalkMap GU.genericPoint) := by
    have : IsIso ((b ≫ p₀).stalkMap GU.genericPoint) := by rw [hbp]; infer_instance
    exact Crepant.isIso_stalkMap_of_isIso_comp b p₀ hp₀bij _
      (by rw [hpbx]; exact Crepant.coheight_genericPoint_le_one G)
  haveI : IsDominant U.ι := Opens.isDominant_ι hU
  have : IsDominant (a ≫ p) := by rw [hap]; infer_instance
  have : IsDominant a := Crepant.isDominant_of_comp_eq a p hpbij
  have : IsDominant (b ≫ p₀) := by rw [hbp]; infer_instance
  have : IsDominant b := Crepant.isDominant_of_comp_eq b p₀ hp₀bij
  obtain ⟨G₁, hG₁, hG₁c⟩ := Crepant.exists_isRCartierPullback_comp a q hGZ
  obtain ⟨G₂, hG₂, hG₂c⟩ := Crepant.exists_isRCartierPullback_comp b q₀ hGZ₀
  rw [hab] at hG₁
  have hG : G₁ = G₂ := MMP.Flips.IsRCartierPullback.eq (b ≫ q₀) hG₁ hG₂
  rw [← hG₁c GU P hax haiso, ← hG₂c GU P₀ hbx hbiso, hG]

/-- A prime divisor of `Y` whose generic point is outside `Ex(f)` is not `f`-exceptional. -/
private theorem not_isExceptional_of_notMem_exceptionalSet {Y Y' : Scheme.{u}} [IsReduced Y]
    [IsSeparated (Y' ↘ ⊤_ Scheme)] (f : Y ⟶ Y') (G : MMP.Mori.PrimeDivisor Y)
    (hG : G.genericPoint ∉ MMP.Flips.exceptionalSet f) :
    ¬ MMP.Mori.RationalMap.IsExceptional f.toRationalMap G := by
  have hco : Order.coheight (f G.genericPoint) = 1 := by
    rw [coheight_map_of_notMem_exceptionalSet hG,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact SamePrimes.not_isExceptional_of_transformPrimeDivisor_eq_some
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f G
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco)).mpr
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm)

/-- **A flip contracts no prime divisor.** Only the smallness of `f` and
`f⁺` and `f⁺ ∘ g = f` are used, so this applies to any `MMP.Flips.IsFlip`. -/
theorem not_isExceptional_of_isFlip {Y Y' V : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] [IsSeparated (Y' ↘ ⊤_ Scheme)] [IsSeparated (V ↘ ⊤_ Scheme)]
    {sY : Y ⟶ Spec (.of k)} {sY' : Y' ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {f : Y ⟶ V} {fp : Y' ⟶ V} {g : Y.RationalMap Y'} (hf : IsSmall k sV sY f)
    (hfp : IsSmall k sV sY' fp) (hcomp : g.compHom fp = f.toRationalMap)
    (G : MMP.Mori.PrimeDivisor Y) : ¬ MMP.Mori.RationalMap.IsExceptional g G := by
  have : IsProper fp := hfp.isProper
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hf G
  obtain ⟨W', hW'iso, -, hW'Q⟩ := exists_isIso_morphismRestrict_of_isSmall hfp
  obtain ⟨g', hGg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f fp g hcomp
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint G).le)
  have hfy' : fp (g'.hom ⟨G.genericPoint, hGg⟩) = f G.genericPoint := by
    have h1 : g'.hom ≫ fp = g'.domain.ι ≫ f :=
      Crepant.hom_eq_of_toRationalMap_eq g'.dense_domain <| by
        rw [Crepant.toRationalMap_ι_comp]
        change (g'.compHom fp).toRationalMap = _
        rw [Scheme.RationalMap.compHom_toRationalMap, hg', hcomp]
    calc fp (g'.hom ⟨G.genericPoint, hGg⟩) = (g'.hom ≫ fp) ⟨G.genericPoint, hGg⟩ :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = (g'.domain.ι ≫ f) ⟨G.genericPoint, hGg⟩ := by rw [h1]
      _ = f G.genericPoint := Scheme.Hom.comp_apply _ _ _
  have hy'W : fp (g'.hom ⟨G.genericPoint, hGg⟩) ∈ W' := by rw [hfy', hQ]; exact hW'Q Q
  have hco : Order.coheight (g'.hom ⟨G.genericPoint, hGg⟩) = 1 := by
    rw [← coheight_map_eq_of_isIso_morphismRestrict fp W' hy'W, hfy', hQ,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact SamePrimes.not_isExceptional_of_transformPrimeDivisor_eq_some
    (MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hGg
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco))

/-- The generic point of a prime divisor `G` of `Y` is not the image of a point of the support of
a divisor `A` on `W` along a birational morphism `p : W ⟶ Y`, if `A` vanishes along the prime
divisor `P₀` of `W` over `G`: a point of `W` over `η_G` has coheight at most one, so it is the
generic point of a prime divisor, which is `P₀`. -/
private theorem genericPoint_notMem_image_supp_of_coeff_eq_zero {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : AlgebraicGeometry.IsVariety k sY) (p : W ⟶ Y)
    (hW : AlgebraicGeometry.IsVariety k (p ≫ sY)) [IsSeparated p] (hpb : IsBirationalMorphism p)
    {A : RDivisor W} (G : MMP.Mori.PrimeDivisor Y) (P₀ : MMP.Mori.PrimeDivisor W)
    (hP₀ : p P₀.genericPoint = G.genericPoint) (hA : A.coeff P₀ = 0) :
    G.genericPoint ∉ p '' (A.supp : Set W) := by
  rintro ⟨w, hw, hpw⟩
  obtain ⟨Q, hQ, hwQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
  have : IsDominant p := hpb.isDominant
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb
  have h1 := coheight_le_coheight_map sY (p ≫ sY) hY hW p rfl hdim.symm w
  rw [hpw, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwQ
  have hs : Q.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hwQ
  have hQw : Q.genericPoint = w := by
    by_contra hne
    have hle : w ≤ Q.genericPoint := Scheme.le_iff_specializes.mpr hs
    have hlt : w < Q.genericPoint := lt_of_le_not_ge hle fun h' =>
      hne (hs.antisymm (Scheme.le_iff_specializes.mp h')).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    have h3 := h2.trans h1
    norm_num at h3
  have hQP : P₀.genericPoint = Q.genericPoint :=
    Crepant.eq_of_apply_eq_of_coheight_le_one p hpb.functionFieldMap_bijective
      (by rw [hQw, hpw, hP₀]) (by rw [hP₀]; exact Crepant.coheight_genericPoint_le_one G)
  obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hQP
  exact hQ hA

/-- **A birational negative contraction contracts no prime of comparison coefficient zero.** Let
`φ` be a nef weak model of `(Y, C)` over a separated base and `f : Y ⟶ Y⁺` a `(K_Y + C)`-negative
extremal contraction over the base which is a birational morphism (a divisorial contraction, for
instance). A prime divisor `G` of `Y` along which the
comparison `p^*(K_Y + C) - q^*(K_Z + C_Z)` vanishes on some common model is not contracted by
`f`. -/
theorem not_isExceptional_of_coeff_eq_zero {Y Z S Y' W : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS] {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ : Y.RationalMap Z} (hφ : MMP.Fourfold.IsNefWeakModel sY sZ sS πY πZ KY C φ)
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    {sY' : Y' ⟶ Spec (.of k)} {πY' : Y' ⟶ S} (f : Y ⟶ Y') (hfY : f ≫ πY' = πY)
    (hf : IsNegativeExtremalContraction k sY sY' (logCanonicalDivisor KY C) f)
    (hfb : IsBirationalMorphism f)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)}
    (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W) {GY GZ : RDivisor W}
    (hW : MMP.Mori.IsVariety k sW) (hpY : p ≫ sY = sW) (hqZ : q ≫ sZ = sW)
    (hp : IsProjectiveMorphism p) (hq : IsProjectiveMorphism q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hhq : h.compHom q = φ)
    (hGY : IsRCartierPullback p (logCanonicalDivisor KY C) GY)
    (hGZ : IsRCartierPullback q
      (logCanonicalDivisor (RationalMap.transformDivisor φ KY)
        (RationalMap.transformDivisor φ C)) GZ)
    (G : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor W)
    (hPG : RationalMap.transformPrimeDivisor p.toRationalMap P = some G)
    (h0 : (GY - GZ).coeff P = 0) : ¬ RationalMap.IsExceptional f.toRationalMap G := by
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have hY'v := hf.isNormalVariety_target
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hYv.1.toQuasiCompact
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsProper sY :=
    isProper_of_isProjectiveMorphism sY hφ.isProjectiveVariety_source.isProjective
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : IsSeparated sY' := hY'v.1.toIsSeparated
  have := isSeparated_terminal sY
  have := isSeparated_terminal sZ
  have := isSeparated_terminal sY'
  by_cases hGE : G.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set Y)
  swap
  · exact not_isExceptional_of_notMem_exceptionalSet f G fun h => hGE (exceptionalSet_subset f h)
  intro _
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
    GY₀, GZ₀, hGY₀, hGZ₀, hA₀, -⟩ := hφ.exists_resolution
  have : LocallyOfFiniteType sW₀ := hW₀.toLocallyOfFiniteType
  have : QuasiCompact sW₀ := hW₀.toQuasiCompact
  have : IsSeparated sW₀ := hW₀.toIsSeparated
  have : IsSeparated sW := hW.toIsSeparated
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀
  have : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀
  have : IsSeparated p := Crepant.isSeparated_of_comp_eq hpY
  have : IsSeparated p₀ := Crepant.isSeparated_of_comp_eq hp₀Y
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : IsDominant p₀ := hp₀b.isDominant
  have : IsDominant q₀ := hq₀b.isDominant
  have := isSeparated_terminal sS
  have hpq₀ : p₀ ≫ πY = q₀ ≫ πZ := comp_eq_comp_of_isOver πY πZ hφ.isOver p₀ q₀ h₀ hinv₀ hhq₀
  -- the comparison vanishes along the prime divisor of `W₀` over `G`
  have hpP : p P.genericPoint = G.genericPoint :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P G).mp hPG
  obtain ⟨P₀, hP₀, hP₀iso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYv (f := p₀)
      (by rw [hp₀Y]; exact ⟨hW₀, inferInstance⟩) hp₀b G
  have : IsIso (p.stalkMap P.genericPoint) :=
    Crepant.isIso_stalkMap_of_coheight_le_one p hpb.functionFieldMap_bijective
      (by rw [hpP]; exact Crepant.coheight_genericPoint_le_one G)
  have e1 : GY.coeff P = (logCanonicalDivisor KY C).coeff G :=
    MMP.Fourfold.coeff_eq_of_isRCartierPullback P G hpP hGY
  have e2 : GY₀.coeff P₀ = (logCanonicalDivisor KY C).coeff G :=
    MMP.Fourfold.coeff_eq_of_isRCartierPullback P₀ G hP₀ hGY₀
  have e3 : GZ.coeff P = GZ₀.coeff P₀ := coeff_eq_coeff_of_isRCartierPullback p q h hpb hinv hhq
    p₀ q₀ h₀ hp₀b hinv₀ hhq₀ hGZ hGZ₀ G P P₀ hpP hP₀
  have hA₀P₀ : (GY₀ - GZ₀).coeff P₀ = 0 := by
    rw [DivisorWithCoeffs.coeff_sub] at h0 ⊢
    linarith
  -- a closed point of `G` outside the image of the comparison
  set B := p₀ '' ((GY₀ - GZ₀).supp : Set W₀) with hB
  have hBc : IsClosed B := p₀.isClosedMap _ (DivisorWithCoeffs.isClosed_supp _)
  have hGB : G.genericPoint ∉ B := genericPoint_notMem_image_supp_of_coeff_eq_zero hYv.1 p₀
    (by rw [hp₀Y]; exact hW₀) hp₀b G P₀ hP₀ hA₀P₀
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hGmem : G.genericPoint ∈ G.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨y, ⟨hyG, hyB⟩, hyc⟩ := nonempty_inter_closedPoints (Z := G.support ∩ Bᶜ)
    ⟨G.genericPoint, hGmem, hGB⟩
    (G.idealSheaf.support.isClosed.isLocallyClosed.inter hBc.isOpen_compl.isLocallyClosed)
  have hyE : y ∈ (MMP.Mori.exceptionalSet f : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyG
    exact closure_minimal (Set.singleton_subset_iff.mpr hGE) (MMP.Mori.exceptionalSet f).isClosed
      hyG
  -- a curve through `y` contracted by `f`
  have : IsProper f := hf.isContraction.isProper
  obtain ⟨Cs, hCc, hCi, hCd, hyC, w, hw⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hYv.1 hY'v.1 f
      hf.isContraction.comp_eq hfb hf.isContraction.isIso_app (mem_closedPoints_iff.mp hyc) hyE
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη1 : topologicalKrullDim (curveSubschemeAt hCi.genericPoint) = 1 := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hgen.def, hCd]
  let Γ : ProperCurve sY := ⟨hCi.genericPoint, isProperCurve_of_isProper sY hη1⟩
  have hΓf : Γ.IsContractedBy f := by
    intro x hx
    change x ∈ closure {hCi.genericPoint} at hx
    rw [hgen.def] at hx
    have h1 : f x ∈ ({w} : Set Y') := hw ▸ ⟨x, hx, rfl⟩
    have h2 : f hCi.genericPoint ∈ ({w} : Set Y') := hw ▸ ⟨_, hgen.mem, rfl⟩
    exact h1.trans h2.symm
  have hΓB : Γ.point ∉ B := fun hm => hyB ((hgen.specializes hyC).mem_closed hBc hm)
  obtain ⟨m, r, Ls, x, hx, hxneg⟩ :=
    exists_isRIntersectionNumber_neg f hf.isRelativelyAntiAmple Γ hΓf
  have hΓS : Γ.IsContractedBy πY := fun z hz => by
    rw [← hfY, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓf z hz]
  have := nonneg_of_isRIntersectionNumber_of_resolution hW₀s p₀ q₀ hp₀Y hq₀Z hpq₀
    hφ.isRelativelyNef hGY₀ hGZ₀ hA₀ Γ hΓS hΓB hx
  linarith

end PartTwo

section RationalMapAlgebra

/-- **Cancelling a birational map on the right.** If `g` has an inverse, two dominant rational
maps `χ₁`, `χ₂` with `g ∘ χ₁ = g ∘ χ₂` are equal. -/
private theorem eq_of_comp_eq_comp_right {X A B : Scheme.{u}} [IsIntegral X] [IsIntegral A]
    [IsIntegral B] {g : A.RationalMap B} [g.IsDominant] {gi : B.RationalMap A}
    (hg : RationalMap.IsInverse g gi) {χ₁ χ₂ : X.RationalMap A} [χ₁.IsDominant] [χ₂.IsDominant]
    (h : χ₁.comp g = χ₂.comp g) : χ₁ = χ₂ := by
  have h1 : g.comp gi = Scheme.RationalMap.id A := Crepant.comp_eq_id_of_isInverse hg
  calc χ₁ = χ₁.comp (Scheme.RationalMap.id A) := (Scheme.RationalMap.comp_id χ₁).symm
    _ = χ₁.comp (g.comp gi) := by rw [h1]
    _ = (χ₁.comp g).comp gi := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (χ₂.comp g).comp gi := Crepant.comp_eq_comp_of_eq h gi
    _ = χ₂.comp (g.comp gi) := Scheme.RationalMap.comp_assoc _ _ _
    _ = χ₂ := by rw [h1, Scheme.RationalMap.comp_id]

/-- **Cancelling a birational map on the left.** If `g` has a dominant inverse, two rational maps
`ψ₁`, `ψ₂` with `ψ₁ ∘ g = ψ₂ ∘ g` are equal. -/
private theorem eq_of_comp_eq_comp_left {A B T : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    {g : A.RationalMap B} [g.IsDominant] {gi : B.RationalMap A} [gi.IsDominant]
    (hg : RationalMap.IsInverse g gi) {ψ₁ ψ₂ : B.RationalMap T} (h : g.comp ψ₁ = g.comp ψ₂) :
    ψ₁ = ψ₂ := by
  have h1 : gi.comp g = Scheme.RationalMap.id B := Crepant.comp_eq_id_of_isInverse hg.symm
  calc ψ₁ = (Scheme.RationalMap.id B).comp ψ₁ := (Scheme.RationalMap.id_comp ψ₁).symm
    _ = (gi.comp g).comp ψ₁ := Crepant.comp_eq_comp_of_eq h1.symm ψ₁
    _ = gi.comp (g.comp ψ₁) := Scheme.RationalMap.comp_assoc _ _ _
    _ = gi.comp (g.comp ψ₂) := by rw [h]
    _ = (gi.comp g).comp ψ₂ := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id B).comp ψ₂ := Crepant.comp_eq_comp_of_eq h1 ψ₂
    _ = ψ₂ := Scheme.RationalMap.id_comp ψ₂

/-- A morphism inducing a birational map is dominant as a rational map. -/
private theorem isDominant_toRationalMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] :
    f.toRationalMap.IsDominant := by
  change f.toPartialMap.toRationalMap.IsDominant
  infer_instance

end RationalMapAlgebra

section CommonModelOver

variable {k : Type u} [Field k]

/-- **A smooth common model over a base.** Two proper birational morphisms `a : W₀ ⟶ B`,
`u : Y' ⟶ B` from normal varieties to a normal variety have a common smooth model `W'` with
projective birational morphisms `r : W' ⟶ W₀`, `p' : W' ⟶ Y'` and `r ≫ a = p' ≫ u`. -/
theorem exists_common_model_over [CharZero k] {B W₀ Y' : Scheme.{u}}
    (sB : B ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sB] [IsNormal B]
    (a : W₀ ⟶ B) (u : Y' ⟶ B) [IsProper a] [IsProper u] (ha : IsBirationalMorphism a)
    (hu : IsBirationalMorphism u) (hW₀ : IsNormalVariety k (a ≫ sB))
    (hY' : IsNormalVariety k (u ≫ sB)) :
    ∃ (W' : Scheme.{u}) (r : W' ⟶ W₀) (p' : W' ⟶ Y'),
      IsNormalVariety k (p' ≫ u ≫ sB) ∧ IsSmoothScheme (p' ≫ u ≫ sB) ∧ r ≫ a = p' ≫ u ∧
        IsProjectiveMorphism r ∧ IsBirationalMorphism r ∧ IsProjectiveMorphism p' ∧
        IsBirationalMorphism p' := by
  let X : Bool → Scheme.{u} := fun b => cond b W₀ Y'
  let F : ∀ b, X b ⟶ B := fun b => Bool.rec (motive := fun b => X b ⟶ B) u a b
  haveI hFp : ∀ b, IsProper (F b) := fun b => by cases b <;> (dsimp [F, X]; infer_instance)
  obtain ⟨W', w, hW', hwb, g, hsm, -, hg, -, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sB (X := X) F
      (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption)
      (κ := Empty) Empty.elim (fun j => j.elim)
  obtain ⟨h1, h1p, h1b⟩ := hg true
  obtain ⟨h0, h0p, h0b⟩ := hg false
  refine ⟨W', g true, g false, ?_, ?_, h1.trans h0.symm, h1p, h1b, h0p, h0b⟩
  · rw [← Category.assoc]; change IsNormalVariety k ((g false ≫ F false) ≫ sB); rw [h0]; exact hW'
  · rw [← Category.assoc]; change IsSmoothScheme ((g false ≫ F false) ≫ sB); rw [h0]; exact hsm

end CommonModelOver

section StepModel

open CategoryTheory.Limits

/-- **The inverses on a common model of a step.** Let `g : Y ⤏ Y⁺` be birational with
`u ∘ g = f` for `f : Y ⟶ B`, `u : Y⁺ ⟶ B`, let `φ = φ⁺ ∘ g`, and let `p₀ : W₀ ⟶ Y`,
`q₀ : W₀ ⟶ Z` resolve `φ` (`q₀ = φ ∘ p₀`). If `r : W' ⟶ W₀` and `p' : W' ⟶ Y⁺` are birational
with `r ≫ p₀ ≫ f = p' ≫ u`, then inverses `h''` of `r ≫ p₀` and `h'` of `p'` satisfy
`(r ≫ q₀) ∘ h'' = φ`, `p' ∘ h'' = g` and `(r ≫ q₀) ∘ h' = φ⁺`. -/
theorem exists_isInverse_of_common_model {Y Z Y' B W₀ W' : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsIntegral Y'] [IsIntegral B] [IsIntegral W₀] [IsIntegral W']
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (B ↘ ⊤_ Scheme)]
    {φ : Y.RationalMap Z} {φ' : Y'.RationalMap Z} {g : Y.RationalMap Y'} [g.IsDominant]
    (hg : RationalMap.IsBirational g) (hcomp : g.comp φ' = φ)
    {p₀ : W₀ ⟶ Y} {q₀ : W₀ ⟶ Z} {h₀ : Y.RationalMap W₀} [IsDominant p₀]
    (hinv₀ : RationalMap.IsInverse p₀.toRationalMap h₀) (hhq₀ : h₀.compHom q₀ = φ)
    {f : Y ⟶ B} {u : Y' ⟶ B} [IsDominant u] (hub : IsBirationalMorphism u)
    (hgu : g.compHom u = f.toRationalMap)
    {r : W' ⟶ W₀} {p' : W' ⟶ Y'} [IsDominant r] [IsDominant p'] (hp'b : IsBirationalMorphism p')
    (hrp : r ≫ p₀ ≫ f = p' ≫ u) (hp''b : IsBirationalMorphism (r ≫ p₀)) :
    ∃ (h' : Y'.RationalMap W') (h'' : Y.RationalMap W'),
      RationalMap.IsInverse p'.toRationalMap h' ∧
      RationalMap.IsInverse (r ≫ p₀).toRationalMap h'' ∧
      h''.compHom (r ≫ q₀) = φ ∧ h''.compHom p' = g ∧ h'.compHom (r ≫ q₀) = φ' := by
  obtain ⟨h', hh'⟩ := hp'b.exists_isInverse
  obtain ⟨h'', hh''⟩ := hp''b.exists_isInverse
  obtain ⟨gi, hgi⟩ := hg.exists_isInverse
  obtain ⟨ui, hui⟩ := hub.exists_isInverse
  haveI : h'.IsDominant := Crepant.isDominant_of_isBirational hh'.isBirational_inverse
  haveI : h''.IsDominant := Crepant.isDominant_of_isBirational hh''.isBirational_inverse
  haveI : gi.IsDominant := Crepant.isDominant_of_isBirational hgi.isBirational_inverse
  haveI := isDominant_toRationalMap r
  haveI := isDominant_toRationalMap p'
  haveI := isDominant_toRationalMap u
  have hh''p : h''.compHom (r ≫ p₀) = Scheme.Hom.toRationalMap (𝟙 Y) :=
    Crepant.compHom_eq_of_isInverse hh''
  -- `(r ≫ q₀) ∘ h'' = φ`
  have hr : h''.compHom r = h₀ := by
    haveI : (h''.compHom r).IsDominant := by
      rw [← Scheme.RationalMap.comp_toRationalMap]; infer_instance
    refine Crepant.eq_of_compHom_eq_id hinv₀ ?_
    rw [compHom_compHom, hh''p]
  have h1 : h''.compHom (r ≫ q₀) = φ := by rw [← compHom_compHom, hr, hhq₀]
  -- `p' ∘ h'' = g`
  have h2 : h''.compHom p' = g := by
    haveI : (h''.compHom p').IsDominant := by
      rw [← Scheme.RationalMap.comp_toRationalMap]; infer_instance
    refine eq_of_comp_eq_comp_right hui ?_
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_toRationalMap, hgu,
      compHom_compHom, ← hrp, ← Category.assoc, ← compHom_compHom, hh''p, toRationalMap_compHom,
      Category.id_comp]
  refine ⟨h', h'', hh', hh'', h1, h2, ?_⟩
  -- `(r ≫ q₀) ∘ h' = φ⁺`
  have h3 : g.comp h' = h'' := by
    calc g.comp h' = (h''.comp p'.toRationalMap).comp h' :=
        Crepant.comp_eq_comp_of_eq (by rw [Scheme.RationalMap.comp_toRationalMap, h2]) h'
      _ = h''.comp (p'.toRationalMap.comp h') := Scheme.RationalMap.comp_assoc _ _ _
      _ = h'' := by rw [Crepant.comp_eq_id_of_isInverse hh', Scheme.RationalMap.comp_id]
  refine eq_of_comp_eq_comp_left hgi ?_
  rw [hcomp, ← Scheme.RationalMap.comp_toRationalMap, ← Scheme.RationalMap.comp_assoc,
    Scheme.RationalMap.comp_toRationalMap, h3, h1]

end StepModel

section ExceptionalPrime

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := by
  rintro ⟨hY, hg, hp, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

end ExceptionalPrime

section PartOne

variable {k : Type u} [Field k]

open CategoryTheory.Limits

/-- An inverse `h` of a proper birational morphism `p` has a representative defined at the
generic point of every prime divisor `R`, sending it to the generic point of the prime divisor of
`W` over `R`. -/
theorem exists_rep_apply_eq_of_isInverse {X W : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsSeparated (X ↘ ⊤_ Scheme)]
    (p : W ⟶ X) [IsProper p] [IsSeparated p] (hpb : IsBirationalMorphism p)
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    (R : MMP.Mori.PrimeDivisor X) (RW : MMP.Mori.PrimeDivisor W)
    (hRW : p RW.genericPoint = R.genericPoint) :
    ∃ (g₀ : X.PartialMap W) (_ : g₀.toRationalMap = h) (hR : R.genericPoint ∈ g₀.domain),
      g₀.hom ⟨R.genericPoint, hR⟩ = RW.genericPoint := by
  have : IsDominant p := hpb.isDominant
  obtain ⟨g₀, hg₀, hRg⟩ := Crepant.exists_rep_mem_domain hinv R
  have he : g₀.hom ≫ p = g₀.domain.ι ≫ 𝟙 X :=
    Crepant.hom_eq_of_toRationalMap_eq g₀.dense_domain <| by
      rw [Crepant.toRationalMap_ι_comp]
      change (g₀.compHom p).toRationalMap = _
      rw [Scheme.RationalMap.compHom_toRationalMap, hg₀, Crepant.compHom_eq_of_isInverse hinv]
  have hw : p (g₀.hom ⟨R.genericPoint, hRg⟩) = R.genericPoint := by
    calc p (g₀.hom ⟨R.genericPoint, hRg⟩) = (g₀.hom ≫ p) ⟨R.genericPoint, hRg⟩ :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = R.genericPoint := by rw [he]; simp
  exact ⟨g₀, hg₀, hRg, (Crepant.eq_of_apply_eq_of_coheight_le_one p hpb.functionFieldMap_bijective
    (hw.trans hRW.symm) (by rw [hRW]; exact Crepant.coheight_genericPoint_le_one R)).symm⟩

/-- **Transforms of prime divisors through a model.** Let `p : W ⟶ X` be a proper birational
morphism with inverse `h`, and `ψ = q ∘ h` for a morphism `q : W ⟶ T`. If `R_W ⊆ W` lies over
the prime divisor `R` of `X`, then `ψ_* R = F` exactly when `q(η_{R_W}) = η_F`. -/
theorem transformPrimeDivisor_eq_some_iff_of_isInverse {X W T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)]
    (p : W ⟶ X) [IsProper p] [IsSeparated p] (hpb : IsBirationalMorphism p)
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h) (q : W ⟶ T)
    {ψ : X.RationalMap T} (hψ : h.compHom q = ψ) (R : MMP.Mori.PrimeDivisor X)
    (RW : MMP.Mori.PrimeDivisor W) (hRW : p RW.genericPoint = R.genericPoint)
    (F : MMP.Mori.PrimeDivisor T) :
    RationalMap.transformPrimeDivisor ψ R = some F ↔ q RW.genericPoint = F.genericPoint := by
  obtain ⟨g₀, hg₀, hRg, hwRW⟩ := exists_rep_apply_eq_of_isInverse p hpb hinv R RW hRW
  have hgq : (g₀.compHom q).toRationalMap = ψ := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg₀, hψ]
  constructor
  · intro hRF
    have h1 :=
      MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hRF (g₀.compHom q) hgq hRg
    rw [h1, ← hwRW]
    rfl
  · intro hq
    refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (g₀.compHom q) hgq hRg ?_
    change F.genericPoint = q (g₀.hom ⟨R.genericPoint, hRg⟩)
    rw [hwRW, hq]

/-- The linear extensions of two partial maps on prime divisors compose to the linear extension
of their composite. -/
theorem mapPrimeDivisors_mapPrimeDivisors {X Y T : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (χ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (ψ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor T))
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors ψ (DivisorWithCoeffs.mapPrimeDivisors χ D) =
      DivisorWithCoeffs.mapPrimeDivisors (fun G => (χ G).bind ψ) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, map_add, hD, hD']
  | single G r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases χ G with _ | D'
    · simp
    · simp [DivisorWithCoeffs.mapPrimeDivisors_single]

end PartOne

section PartOneMain

variable {k : Type u} [Field k]

open CategoryTheory.Limits

/-- **The nef weak model descends along a negative step.** Let `φ : Y ⤏ Z` be a nef weak model of
`(Y, C)` over a separated base `S`, with resolution `p₀ : W₀ ⟶ Y`, `q₀ : W₀ ⟶ Z`, and let
`g : Y ⤏ Y⁺` be a birational map over a normal variety `B` (`u ∘ g = f`, `f : Y ⟶ B`,
`u : Y⁺ ⟶ B` proper birational over `S`, `u` sending generic points of prime divisors to points of
coheight one) to a `ℚ`-factorial projective `Y⁺`, contracting no prime divisor along which the
comparison on `W₀` vanishes. Then `φ⁺ = φ ∘ g⁻¹` is a nef weak model of `(Y⁺, g_* C)` with
canonical divisor `g_* K_Y`, realised on a smooth common model `W'` of `Y`, `Y⁺` and `Z` on which
the comparison coefficient along the strict transform of a prime `G` with `g_* G` a prime is the
comparison coefficient of `G` on any common projective model of `φ`. Along the way, every
divisor `N` of `Y` has `φ⁺_* g_* N = φ_* N`, and `g_* N` is the strict transform
`(u⁻¹)_* f_* N` through `B`. -/
public theorem IsNefWeakModel.isNefWeakModel_of_step_over [CharZero k] {Y Z S Y' B W₀ : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS] {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ : Y.RationalMap Z} (hφ : MMP.Fourfold.IsNefWeakModel sY sZ sS πY πZ KY C φ)
    [IsIntegral W₀] [IsLocallyNoetherian W₀] [IsNormal W₀] {sW₀ : W₀ ⟶ Spec (.of k)}
    {p₀ : W₀ ⟶ Y} {q₀ : W₀ ⟶ Z} {h₀ : Y.RationalMap W₀} (hW₀ : MMP.Mori.IsVariety k sW₀)
    (hp₀Y : p₀ ≫ sY = sW₀) (hq₀Z : q₀ ≫ sZ = sW₀) (hp₀ : IsProjectiveMorphism p₀)
    (hq₀ : IsProjectiveMorphism q₀) (hp₀b : IsBirationalMorphism p₀)
    (hq₀b : IsBirationalMorphism q₀)
    (hinv₀ : RationalMap.IsInverse p₀.toRationalMap h₀) (hhq₀ : h₀.compHom q₀ = φ)
    {GY₀ GZ₀ : RDivisor W₀} (hGY₀ : IsRCartierPullback p₀ (logCanonicalDivisor KY C) GY₀)
    (hGZ₀ : IsRCartierPullback q₀
      (logCanonicalDivisor (RationalMap.transformDivisor φ KY)
        (RationalMap.transformDivisor φ C)) GZ₀)
    (hA₀ : ∀ P, 0 ≤ (GY₀ - GZ₀).coeff P)
    (hA₀q : ∀ P, (GY₀ - GZ₀).coeff P ≠ 0 → IsExceptionalPrimeDivisor sZ q₀ P)
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    {sY' : Y' ⟶ Spec (.of k)} {πY' : Y' ⟶ S} {g : Y.RationalMap Y'} [g.IsDominant]
    {φ' : Y'.RationalMap Z} (hY'p : MMP.Mori.IsProjectiveVariety k sY')
    (hY'q : MMP.Fourfold.IsQFactorial sY') (hπY' : πY' ≫ sS = sY') (hcomp : g.comp φ' = φ)
    (hg : RationalMap.IsBirational g)
    {sB : B ⟶ Spec (.of k)} (hB : IsNormalVariety k sB) {πB : B ⟶ S} (f : Y ⟶ B) (u : Y' ⟶ B)
    [IsProper f] [IsProper u] (hfb : IsBirationalMorphism f) (hub : IsBirationalMorphism u)
    (hfB : f ≫ sB = sY) (huB : u ≫ sB = sY') (hfS : f ≫ πB = πY) (huS : u ≫ πB = πY')
    (hgu : g.compHom u = f.toRationalMap)
    (hu1 : ∀ D : MMP.Mori.PrimeDivisor Y', Order.coheight (u D.genericPoint) ≤ 1)
    (hnex : ∀ (G : MMP.Mori.PrimeDivisor Y) (P₀ : MMP.Mori.PrimeDivisor W₀),
      p₀ P₀.genericPoint = G.genericPoint → (GY₀ - GZ₀).coeff P₀ = 0 →
        ¬ RationalMap.IsExceptional g G) :
    MMP.Fourfold.IsNefWeakModel sY' sZ sS πY' πZ (RationalMap.transformDivisor g KY)
      (RationalMap.transformDivisor g C) φ' ∧
      (∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
        RationalMap.transformDivisor φ' (RationalMap.transformDivisor g N) =
          RationalMap.transformDivisor φ N) ∧
      (∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
        RationalMap.transformDivisor g N = flipTransform f u N) ∧
      ∃ (W' : Scheme.{u}) (_ : IsIntegral W') (_ : IsLocallyNoetherian W') (_ : IsNormal W')
        (sW' : W' ⟶ Spec (.of k)) (p' : W' ⟶ Y') (q' : W' ⟶ Z) (h' : Y'.RationalMap W'),
        MMP.Mori.IsVariety k sW' ∧ MMP.Mori.IsSmoothScheme sW' ∧ p' ≫ sY' = sW' ∧
        q' ≫ sZ = sW' ∧ IsProjectiveMorphism p' ∧ IsProjectiveMorphism q' ∧
        IsBirationalMorphism p' ∧ IsBirationalMorphism q' ∧
        MMP.Mori.RationalMap.IsInverse p'.toRationalMap h' ∧ h'.compHom q' = φ' ∧
        ∃ GY' GZ' : RDivisor W',
          MMP.Flips.IsRCartierPullback p' (MMP.Flips.logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor g KY)
            (MMP.Mori.RationalMap.transformDivisor g C)) GY' ∧
          MMP.Flips.IsRCartierPullback q' (MMP.Flips.logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor φ' (MMP.Mori.RationalMap.transformDivisor g KY))
            (MMP.Mori.RationalMap.transformDivisor φ' (MMP.Mori.RationalMap.transformDivisor g C)))
            GZ' ∧
          ∀ {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
            (sW : W ⟶ Spec (.of k)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W)
            {GY GZ : RDivisor W},
            MMP.Mori.IsVariety k sW → p ≫ sY = sW → q ≫ sZ = sW →
            IsProjectiveMorphism p → IsProjectiveMorphism q →
            IsBirationalMorphism p → IsBirationalMorphism q →
            MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
            MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY →
            MMP.Flips.IsRCartierPullback q
              (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
                (MMP.Mori.RationalMap.transformDivisor φ C)) GZ →
            ∀ (G : MMP.Mori.PrimeDivisor Y) (D : MMP.Mori.PrimeDivisor Y')
              (P : MMP.Mori.PrimeDivisor W) (P' : MMP.Mori.PrimeDivisor W'),
              MMP.Mori.RationalMap.transformPrimeDivisor g G = some D →
              p P.genericPoint = G.genericPoint → p' P'.genericPoint = D.genericPoint →
              (GY' - GZ').coeff P' = (GY - GZ).coeff P := by
  classical
  -- instances
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have hY'v : IsNormalVariety k sY' := hY'q.1
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hYv.1.toQuasiCompact
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : LocallyOfFiniteType sY' := hY'v.1.toLocallyOfFiniteType
  have : QuasiCompact sY' := hY'v.1.toQuasiCompact
  have : IsSeparated sY' := hY'v.1.toIsSeparated
  have : AlgebraicGeometry.IsVariety k sB := hB.1
  have : IsIntegral B := hB.1.toIsIntegral
  have : IsNormal B := hB.2
  have : LocallyOfFiniteType sB := hB.1.toLocallyOfFiniteType
  have : IsSeparated sB := hB.1.toIsSeparated
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  have : LocallyOfFiniteType sW₀ := hW₀.toLocallyOfFiniteType
  have : QuasiCompact sW₀ := hW₀.toQuasiCompact
  have : IsSeparated sW₀ := hW₀.toIsSeparated
  have := isSeparated_terminal sY
  have := isSeparated_terminal sZ
  have := isSeparated_terminal sY'
  have := isSeparated_terminal sB
  have := isSeparated_terminal sS
  have : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀
  have : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀
  have : IsSeparated p₀ := Crepant.isSeparated_of_comp_eq hp₀Y
  have : IsDominant p₀ := hp₀b.isDominant
  have : IsDominant q₀ := hq₀b.isDominant
  have : IsDominant f := hfb.isDominant
  have : IsDominant u := hub.isDominant
  have hpq₀ : p₀ ≫ πY = q₀ ≫ πZ := comp_eq_comp_of_isOver πY πZ hφ.isOver p₀ q₀ h₀ hinv₀ hhq₀
  -- the common model `W'` of `Y`, `Y⁺` and `Z`
  obtain ⟨W', r, p', hW'v, hW'sm, hrp, hrproj, hrb, hp'proj, hp'b⟩ :=
    exists_common_model_over sB (p₀ ≫ f) u (Crepant.isBirationalMorphism_comp hp₀b hfb) hub
      (by rw [Category.assoc, hfB, hp₀Y]; exact ⟨hW₀, inferInstance⟩) (by rw [huB]; exact hY'v)
  rw [huB] at hW'v hW'sm
  have : IsIntegral W' := hW'v.1.toIsIntegral
  have : IsNormal W' := hW'v.2
  have : LocallyOfFiniteType (p' ≫ sY') := hW'v.1.toLocallyOfFiniteType
  have : QuasiCompact (p' ≫ sY') := hW'v.1.toQuasiCompact
  have : IsSeparated (p' ≫ sY') := hW'v.1.toIsSeparated
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ sY')
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (p' ≫ sY')
  have : IsProper r := isProper_of_isProjectiveMorphism r hrproj
  have : IsProper p' := isProper_of_isProjectiveMorphism p' hp'proj
  have : IsDominant r := hrb.isDominant
  have : IsDominant p' := hp'b.isDominant
  have : IsSeparated p' := IsSeparated.of_comp p' sY'
  have hp''b : IsBirationalMorphism (r ≫ p₀) := Crepant.isBirationalMorphism_comp hrb hp₀b
  have hq'b : IsBirationalMorphism (r ≫ q₀) := Crepant.isBirationalMorphism_comp hrb hq₀b
  have : IsDominant (r ≫ p₀) := hp''b.isDominant
  have : IsDominant (r ≫ q₀) := hq'b.isDominant
  have hp''Y : (r ≫ p₀) ≫ sY = p' ≫ sY' := by
    rw [Category.assoc, ← hfB, ← huB, ← Category.assoc p', ← hrp]; simp only [Category.assoc]
  have hq'Z : (r ≫ q₀) ≫ sZ = p' ≫ sY' := by
    rw [Category.assoc, hq₀Z, ← hp₀Y, ← Category.assoc, hp''Y]
  have hq'S : (r ≫ q₀) ≫ πZ = p' ≫ πY' := by
    rw [Category.assoc, ← hpq₀, ← hfS, ← huS, ← Category.assoc p', ← hrp]
    simp only [Category.assoc]
  have : IsSeparated (r ≫ p₀) := Crepant.isSeparated_of_comp_eq hp''Y
  have : IsProper (r ≫ p₀) := inferInstance
  have : IsSeparated (r ≫ q₀) := Crepant.isSeparated_of_comp_eq hq'Z
  have : IsProper (r ≫ q₀) := inferInstance
  -- the inverses
  obtain ⟨h', h'', hh', hh'', hφW, hgW, hφ'W⟩ :=
    exists_isInverse_of_common_model hg hcomp hinv₀ hhq₀ hub hgu hp'b hrp hp''b
  -- strict transforms
  have hW'n : IsNormalVariety k ((r ≫ p₀) ≫ sY) := by rw [hp''Y]; exact hW'v
  have hW'nq : IsNormalVariety k ((r ≫ q₀) ≫ sZ) := by rw [hq'Z]; exact hW'v
  have hW₀n : IsNormalVariety k (p₀ ≫ sY) := by rw [hp₀Y]; exact ⟨hW₀, inferInstance⟩
  choose GW hGW hGWiso hGWtr using fun G : MMP.Mori.PrimeDivisor Y =>
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYv
      (f := r ≫ p₀) hW'n hp''b G
  choose G0 hG0 hG0iso hG0tr using fun G : MMP.Mori.PrimeDivisor Y =>
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYv
      (f := p₀) hW₀n hp₀b G
  choose DW hDW hDWiso hDWtr using fun D : MMP.Mori.PrimeDivisor Y' =>
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY'v
      (f := p') hW'v hp'b D
  have : MMP.Mori.IsVariety k (p' ≫ sY') := hW'v.1
  have : MMP.Mori.IsVariety k sY := hYv.1
  have : MMP.Mori.IsVariety k sY' := hY'v.1
  have : MMP.Mori.IsVariety k ((r ≫ p₀) ≫ sY) := hW'n.1
  have : MMP.Mori.IsVariety k (f ≫ sB) := by rw [hfB]; exact hYv.1
  have : MMP.Mori.IsVariety k sB := hB.1
  have hdimY' := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY' (p' ≫ sY') hp'b
  have hdimY := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY
    ((r ≫ p₀) ≫ sY) hp''b
  have hdimB := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sB (f ≫ sB) hfb
  -- transforms through `W'` and `W₀`
  have hTφ : ∀ G F, RationalMap.transformPrimeDivisor φ G = some F ↔
      (r ≫ q₀) (GW G).genericPoint = F.genericPoint := fun G F =>
    transformPrimeDivisor_eq_some_iff_of_isInverse (r ≫ p₀) hp''b hh'' (r ≫ q₀) hφW G (GW G)
      (hGW G) F
  have hTg : ∀ G D, RationalMap.transformPrimeDivisor g G = some D ↔
      p' (GW G).genericPoint = D.genericPoint := fun G D =>
    transformPrimeDivisor_eq_some_iff_of_isInverse (r ≫ p₀) hp''b hh'' p' hgW G (GW G) (hGW G) D
  have hTφ' : ∀ D (RW : MMP.Mori.PrimeDivisor W'), p' RW.genericPoint = D.genericPoint →
      ∀ F, RationalMap.transformPrimeDivisor φ' D = some F ↔
        (r ≫ q₀) RW.genericPoint = F.genericPoint := fun D RW hRW F =>
    transformPrimeDivisor_eq_some_iff_of_isInverse p' hp'b hh' (r ≫ q₀) hφ'W D RW hRW F
  have hTφ₀ : ∀ G F, RationalMap.transformPrimeDivisor φ G = some F ↔
      q₀ (G0 G).genericPoint = F.genericPoint := fun G F =>
    transformPrimeDivisor_eq_some_iff_of_isInverse p₀ hp₀b hinv₀ q₀ hhq₀ G (G0 G) (hG0 G) F
  -- (1) `φ⁺_* g_* G = φ_* G`
  have hC1 : ∀ G D, RationalMap.transformPrimeDivisor g G = some D →
      RationalMap.transformPrimeDivisor φ' D = RationalMap.transformPrimeDivisor φ G := by
    intro G D hGD
    have hp'G := (hTg G D).mp hGD
    exact Option.ext fun F => (hTφ' D (GW G) hp'G F).trans (hTφ G F).symm
  have hA0zero : ∀ G F, RationalMap.transformPrimeDivisor φ G = some F →
      (GY₀ - GZ₀).coeff (G0 G) = 0 := by
    intro G F hGF
    have hq₀G := (hTφ₀ G F).mp hGF
    by_contra hne
    exact not_isExceptionalPrimeDivisor hZv q₀ (G0 G)
      (by rw [hq₀G]; exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint F) (hA₀q _ hne)
  -- (2) a prime of `Y` not contracted by `φ` is not contracted by `g`
  have hC2 : ∀ G F, RationalMap.transformPrimeDivisor φ G = some F →
      ∃ D, RationalMap.transformPrimeDivisor g G = some D := by
    intro G F hGF
    have hnex' := hnex G (G0 G) (hG0 G) (hA0zero G F hGF)
    obtain ⟨g₀, hg₀, hGg, hg₀G⟩ := exists_rep_apply_eq_of_isInverse (r ≫ p₀) hp''b hh'' G (GW G)
      (hGW G)
    have hle := SamePrimes.coheight_apply_le_one_of_not_isExceptional p' g₀
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg₀, hgW]) hGg hnex'
    rw [hg₀G] at hle
    have hge := coheight_le_coheight_map sY' (p' ≫ sY') hY'v.1 hW'v.1 p' rfl hdimY'.symm
      (GW G).genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hge
    have hco : Order.coheight (p' (GW G).genericPoint) = 1 := le_antisymm hle hge
    exact ⟨_, (hTg G _).mpr (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
  -- (3) every prime of `Y⁺` is the transform of a prime of `Y`
  have hC3 : ∀ D, ∃ G, RationalMap.transformPrimeDivisor g G = some D ∧ GW G = DW D ∧
      f G.genericPoint = u D.genericPoint ∧ Order.coheight (u D.genericPoint) = 1 := by
    intro D
    set y := (r ≫ p₀) (DW D).genericPoint with hy
    have h1 := coheight_le_coheight_map sY ((r ≫ p₀) ≫ sY) hYv.1 hW'n.1 (r ≫ p₀) rfl
      hdimY.symm (DW D).genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    have hfy : f y = u D.genericPoint := by
      rw [← hDW D, hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hrp]
    have h2 := coheight_le_coheight_map sB sY hB.1 hYv.1 f hfB
      (by rw [← hfB] at *; exact hdimB.symm) y
    rw [hfy] at h2
    have hco : Order.coheight y = 1 := le_antisymm (h2.trans (hu1 D)) h1
    set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco
    have hGy : G.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have hGWD : GW G = DW D := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      exact Crepant.eq_of_apply_eq_of_coheight_le_one (r ≫ p₀) hp''b.functionFieldMap_bijective
        ((hGW G).trans hGy).symm (by rw [hGW G]; exact Crepant.coheight_genericPoint_le_one G)
    exact ⟨G, (hTg G D).mpr (by rw [hGWD, hDW D]), hGWD, (congrArg f hGy).trans hfy,
      le_antisymm (hu1 D) (by rw [← hco]; exact h2)⟩
  -- (4) `g_*` is injective on prime divisors
  have hC4 : ∀ G₁ G₂ D, RationalMap.transformPrimeDivisor g G₁ = some D →
      RationalMap.transformPrimeDivisor g G₂ = some D → G₁ = G₂ := by
    intro G₁ G₂ D h₁ h₂
    have e₁ := (hTg G₁ D).mp h₁
    have e₂ := (hTg G₂ D).mp h₂
    have hWW : (GW G₂).genericPoint = (GW G₁).genericPoint :=
      Crepant.eq_of_apply_eq_of_coheight_le_one p' hp'b.functionFieldMap_bijective
        (e₁.trans e₂.symm) (by rw [e₂]; exact Crepant.coheight_genericPoint_le_one D)
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    exact (hGW G₁).symm.trans ((congrArg (fun x => (r ≫ p₀) x) hWW).symm.trans (hGW G₂))
  -- the composite transform
  have hTT : ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
      RationalMap.transformDivisor φ' (RationalMap.transformDivisor g N) =
        RationalMap.transformDivisor φ N := by
    intro R _ N
    change DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ N) =
      DivisorWithCoeffs.mapPrimeDivisors _ N
    rw [mapPrimeDivisors_mapPrimeDivisors]
    have hfun : (fun G => (RationalMap.transformPrimeDivisor g G).bind
        (RationalMap.transformPrimeDivisor φ')) = RationalMap.transformPrimeDivisor φ := by
      funext G
      rcases hG : RationalMap.transformPrimeDivisor g G with _ | D
      · rcases hφG : RationalMap.transformPrimeDivisor φ G with _ | F
        · rfl
        · obtain ⟨D, hD⟩ := hC2 G F hφG
          rw [hG] at hD
          cases hD
      · exact hC1 G D hG
    rw [hfun]
  have hgcoeff : ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y) G D,
      RationalMap.transformPrimeDivisor g G = some D →
        RationalMap.transformDivisor g N D = N G := fun N G D hGD =>
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hGD (fun G' hG' => hC4 G' G D hG' hGD) N
  -- `g_*` is the strict transform `(u⁻¹)_* f_*` through `B`
  have hflip : ∀ {R : Type} [AddCommMonoid R] (N : DivisorWithCoeffs R Y),
      RationalMap.transformDivisor g N = flipTransform f u N := by
    intro R _ N
    refine Finsupp.ext fun D => ?_
    obtain ⟨G, hGD, -, hfG, hco⟩ := hC3 D
    set Q : MMP.Mori.PrimeDivisor B := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hQ : Q.genericPoint = u D.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have := Q.isDiscreteValuationRing_localRing
    have : IsSeparated (f ≫ sB) := by rw [hfB]; infer_instance
    have : IsSeparated f := IsSeparated.of_comp f sB
    have hus : Function.Surjective u := fun y => by
      rw [← Set.mem_range, ← u.isClosedMap.isClosed_range.closure_eq, u.denseRange.closure_range]
      trivial
    rw [hgcoeff N G D hGD, flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
      hus (hfG.trans hQ.symm) hQ.symm
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal u hub (hQ ▸ hco.le))]
  have hcanon : ∃ m : ℕ, Divisor.IsCanonicalDivisor sY' m (RationalMap.transformDivisor g KY) := by
    obtain ⟨n, hKY⟩ := hφ.isCanonicalDivisor
    refine ⟨n, ?_⟩
    have hqs : p' ≫ sY' = (r ≫ p₀) ≫ sY := hp''Y.symm
    have hpbij := hp''b.functionFieldMap_bijective
    have hqbij := hp'b.functionFieldMap_bijective
    have hdY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
      hKY.topologicalKrullDim_eq
    have htr : (letI := functionFieldAlgebra sY'; Algebra.trdeg k Y'.functionField) =
        (letI := functionFieldAlgebra sY; Algebra.trdeg k Y.functionField) := by
      rw [trdeg_functionField_eq_of_bijective sY' p' hqbij,
        trdeg_functionField_eq_of_bijective sY (r ≫ p₀) hpbij]
      exact congrArg (fun t => (letI := functionFieldAlgebra t; Algebra.trdeg k W'.functionField))
        hqs
    have hdZ : (letI := functionFieldAlgebra sY'; Algebra.trdeg k Y'.functionField).toNat = n := by
      rwa [htr]
    have hnZ : topologicalKrullDim Y' = n := by
      rw [← toENat_trdeg_functionField (sX := sY'), htr, toENat_trdeg_functionField (sX := sY)]
      exact hKY.topologicalKrullDim_eq
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sY' hY'v hnZ
    obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYv hKY
    have hω'0 := Crepant.pullbackRationalPluriForms_ne_zero sY (r ≫ p₀) hpbij hdY hω0
    obtain ⟨τ, hτ, hτ0'⟩ := Crepant.exists_pullbackRationalPluriForms_eq sY' p' hqbij hdZ
      (cast (congrArg (fun t => RationalPluriForms t n 1) hqs.symm)
        (pullbackRationalPluriForms sY (r ≫ p₀) ω))
    have hτ0 : τ ≠ 0 := hτ0' (Crepant.cast_ne_zero hqs.symm hω'0)
    have hdiv : RationalMap.transformDivisor g KY = divisorOfForm τ := by
      refine Finsupp.ext fun D => ?_
      obtain ⟨G, hGD, hGWD, -⟩ := hC3 D
      have hpE : (r ≫ p₀) (DW D).genericPoint = G.genericPoint := by rw [← hGWD]; exact hGW G
      have : IsIso ((r ≫ p₀).stalkMap (DW D).genericPoint) := by rw [← hGWD]; exact hGWiso G
      have : IsIso (p'.stalkMap (DW D).genericPoint) := hDWiso D
      change (RationalMap.transformDivisor g KY).coeff D = (divisorOfForm τ).coeff D
      rw [DivisorWithCoeffs.coeff_apply, hgcoeff KY G D hGD, coeff_divisorOfForm,
        ← DivisorWithCoeffs.coeff_apply KY G, ← hω G,
        ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso (r ≫ p₀) hpbij hdY (DW D) G
          hpE ω,
        ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p' hqbij hdZ (DW D) D
          (hDW D) τ, hτ, Crepant.ordForm_cast hqs.symm]
    rw [hdiv]
    exact hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY'v hK₀ hτ0)
  have hbir : RationalMap.IsBirational φ' := by
    obtain ⟨Up, hUp, hUpi⟩ := Crepant.exists_isOpenImmersion_of_isBirationalMorphism hp'b
    obtain ⟨Uq, hUq, hUqi⟩ := Crepant.exists_isOpenImmersion_of_isBirationalMorphism hq'b
    let U : W'.Opens := Up ⊓ Uq
    have hU : Dense (U : Set W') := by
      simp only [U, TopologicalSpace.Opens.coe_inf]
      exact hUp.inter_of_isOpen_left hUq Up.isOpen
    obtain ⟨w₀, hw₀⟩ := hU.nonempty
    haveI : IsOpenImmersion (U.ι ≫ p') := by
      rw [← W'.homOfLE_ι (inf_le_left : U ≤ Up), Category.assoc]; infer_instance
    haveI : IsOpenImmersion (U.ι ≫ (r ≫ q₀)) := by
      rw [← W'.homOfLE_ι (inf_le_right : U ≤ Uq), Category.assoc]; infer_instance
    set j := U.ι ≫ p' with hj
    have hjw : j ⟨w₀, hw₀⟩ ∈ j.opensRange := ⟨_, rfl⟩
    have hO : Dense (j.opensRange : Set Y') := j.opensRange.isOpen.dense ⟨_, hjw⟩
    haveI : IsDominant U.ι := Opens.isDominant_ι hU
    let χ : Y'.PartialMap W' := ⟨j.opensRange, hO, j.isoOpensRange.inv ≫ U.ι⟩
    haveI : IsDominant χ.hom := by change IsDominant (j.isoOpensRange.inv ≫ U.ι); infer_instance
    have hχ : χ.toRationalMap = h' := by
      refine Crepant.eq_of_compHom_eq_id hh' ?_
      rw [← Scheme.RationalMap.compHom_toRationalMap, ← Crepant.toRationalMap_ι_comp hO (𝟙 Y')]
      congr 1
      change (⟨j.opensRange, hO, (j.isoOpensRange.inv ≫ U.ι) ≫ p'⟩ : Y'.PartialMap Y') =
        ⟨j.opensRange, hO, j.opensRange.ι ≫ 𝟙 Y'⟩
      congr 1
      rw [Category.comp_id, Category.assoc]
      exact (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι j).symm
    let c : Y'.PartialMap Z := ⟨j.opensRange, hO, j.isoOpensRange.inv ≫ U.ι ≫ (r ≫ q₀)⟩
    haveI : IsOpenImmersion c.hom := by
      change IsOpenImmersion (j.isoOpensRange.inv ≫ U.ι ≫ (r ≫ q₀)); infer_instance
    haveI : Nonempty c.domain := ⟨⟨_, hjw⟩⟩
    have hc : c.toRationalMap = φ' := by
      rw [← hφ'W, ← hχ, ← Scheme.RationalMap.compHom_toRationalMap]
      congr 1
    rw [← hc]
    exact Crepant.isBirational_of_isOpenImmersion c
  -- the comparison on `W'`
  have hq'proj : IsProjectiveMorphism (r ≫ q₀) := hrproj.comp hq₀
  have hL'c : IsCartierCombination (logCanonicalDivisor (RationalMap.transformDivisor g KY)
      (RationalMap.transformDivisor g C)) := isCartierCombination_of_isQFactorial hY'q _
  obtain ⟨GY', hGY', -⟩ := MMP.Flips.existsUnique_isRCartierPullback p' hL'c
  obtain ⟨GZ', hGZ', -⟩ := MMP.Flips.existsUnique_isRCartierPullback (r ≫ q₀)
    (Crepant.isCartierCombination_logCanonicalDivisor hφ)
  obtain ⟨GY'', hGY'', -⟩ := MMP.Flips.existsUnique_isRCartierPullback (r ≫ p₀)
    hφ.isCartierCombination
  -- along a prime not contracted by `g`, the two pull-backs of the adjoints to `W'` agree
  have hK : ∀ G D, RationalMap.transformPrimeDivisor g G = some D →
      GY'.coeff (GW G) = GY''.coeff (GW G) := by
    intro G D hGD
    have hp'G := (hTg G D).mp hGD
    haveI : IsIso (p'.stalkMap (GW G).genericPoint) :=
      Crepant.isIso_stalkMap_of_coheight_le_one p' hp'b.functionFieldMap_bijective
        (by rw [hp'G]; exact Crepant.coheight_genericPoint_le_one D)
    haveI := hGWiso G
    rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback (GW G) D hp'G hGY',
      MMP.Fourfold.coeff_eq_of_isRCartierPullback (GW G) G (hGW G) hGY'']
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
    change ((RationalMap.transformDivisor g KY D : ℤ) : ℝ) + RationalMap.transformDivisor g C D =
      ((KY G : ℤ) : ℝ) + C G
    rw [hgcoeff KY G D hGD, hgcoeff C G D hGD]
  -- the comparison coefficient along the strict transform of `G` is the one on any model
  have htr : ∀ {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
      (sW : W ⟶ Spec (.of k)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W)
      {GY GZ : RDivisor W},
      MMP.Mori.IsVariety k sW → p ≫ sY = sW → q ≫ sZ = sW →
      IsProjectiveMorphism p → IsProjectiveMorphism q →
      IsBirationalMorphism p → IsBirationalMorphism q →
      MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
      IsRCartierPullback p (logCanonicalDivisor KY C) GY →
      IsRCartierPullback q
        (logCanonicalDivisor (RationalMap.transformDivisor φ KY)
          (RationalMap.transformDivisor φ C)) GZ →
      ∀ (G : MMP.Mori.PrimeDivisor Y) (D : MMP.Mori.PrimeDivisor Y')
        (P : MMP.Mori.PrimeDivisor W) (P' : MMP.Mori.PrimeDivisor W'),
        RationalMap.transformPrimeDivisor g G = some D →
        p P.genericPoint = G.genericPoint → p' P'.genericPoint = D.genericPoint →
        (GY' - GZ').coeff P' = (GY - GZ).coeff P := by
    intro W _ _ _ sW p q h GY GZ hW hpY _ hp hq hpb hqb hinv hhq hGY hGZ G D P P' hGD hP hP'
    have hp'G := (hTg G D).mp hGD
    obtain rfl : GW G = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Crepant.eq_of_apply_eq_of_coheight_le_one p' hp'b.functionFieldMap_bijective
        (hP'.trans hp'G.symm) (by rw [hp'G]; exact Crepant.coheight_genericPoint_le_one D))
    have : IsSeparated sW := hW.toIsSeparated
    have : IsProper p := isProper_of_isProjectiveMorphism p hp
    have : IsSeparated p := Crepant.isSeparated_of_comp_eq hpY
    have : IsDominant p := hpb.isDominant
    have : IsDominant q := hqb.isDominant
    haveI : IsIso (p.stalkMap P.genericPoint) :=
      Crepant.isIso_stalkMap_of_coheight_le_one p hpb.functionFieldMap_bijective
        (by rw [hP]; exact Crepant.coheight_genericPoint_le_one G)
    haveI := hGWiso G
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub, hK G D hGD,
      MMP.Fourfold.coeff_eq_of_isRCartierPullback (GW G) G (hGW G) hGY'',
      MMP.Fourfold.coeff_eq_of_isRCartierPullback P G hP hGY,
      coeff_eq_coeff_of_isRCartierPullback (r ≫ p₀) (r ≫ q₀) h'' hp''b hh'' hφW p q h hpb
        hinv hhq hGZ' hGZ G (GW G) P (hGW G) hP]
  have hK₀ : ∀ G D, RationalMap.transformPrimeDivisor g G = some D →
      (GY' - GZ').coeff (GW G) = (GY₀ - GZ₀).coeff (G0 G) := fun G D hGD =>
    htr sW₀ p₀ q₀ h₀ hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ G D (G0 G) (GW G) hGD
      (hG0 G) ((hTg G D).mp hGD)
  have hW'p : MMP.Mori.IsProjectiveVariety k (p' ≫ sY') :=
    (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
      ⟨hW'v.1, hp'proj.comp hY'p.isProjective⟩
  have hpush : 0 ≤ RationalMap.transformDivisor p'.toRationalMap (GY' - GZ') := by
    rw [← DivisorWithCoeffs.isEffective_iff_nonneg]
    intro D
    obtain ⟨G, hGD, hGWD, -⟩ := hC3 D
    rw [DivisorWithCoeffs.coeff_apply, hDWtr D, ← hGWD, ← DivisorWithCoeffs.coeff_apply,
      hK₀ G D hGD]
    exact hA₀ _
  have hnn := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (p' ≫ sY') sY' sZ hW'v hW'p
    hY'v hY'p hZv hφ.isProjectiveVariety_target πY' πZ p' (r ≫ q₀) rfl hq'Z hq'S.symm hp'proj
    hp'b hq'proj hq'b hL'c hφ.isRelativelyNef hGY' hGZ' hpush
  have hexc : ∀ P, (GY' - GZ').coeff P ≠ 0 → IsExceptionalPrimeDivisor sZ (r ≫ q₀) P := by
    intro P hP
    by_contra hPq
    obtain ⟨F, hqF, -, -⟩ := exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hZv
      (r ≫ q₀) hW'nq hq'b P hPq
    obtain ⟨G, hG⟩ : ∃ G, RationalMap.transformPrimeDivisor φ G = some F := by
      simpa [MMP.Flips.RationalMap.IsInverseExceptional] using hφ.not_isInverseExceptional F
    have hPG : GW G = P := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      exact Crepant.eq_of_apply_eq_of_coheight_le_one (r ≫ q₀) hq'b.functionFieldMap_bijective
        (hqF.trans ((hTφ G F).mp hG).symm)
        (by rw [(hTφ G F).mp hG]; exact Crepant.coheight_genericPoint_le_one F)
    obtain ⟨D, hD⟩ := hC2 G F hG
    exact hP (by rw [← hPG, hK₀ G D hD]; exact hA0zero G F hG)
  have hGZ'' : IsRCartierPullback (r ≫ q₀) (logCanonicalDivisor
      (RationalMap.transformDivisor φ' (RationalMap.transformDivisor g KY))
      (RationalMap.transformDivisor φ' (RationalMap.transformDivisor g C))) GZ' := by
    rwa [hTT, hTT]
  refine ⟨
    { isNormalVariety_source := hY'v
      isProjectiveVariety_source := hY'p
      comp_eq_source := hπY'
      isCanonicalDivisor := hcanon
      isCartierCombination := hL'c
      isNormalVariety_target := hZv
      isProjectiveVariety_target := hφ.isProjectiveVariety_target
      comp_eq_target := hφ.comp_eq_target
      isBirational := hbir
      isOver := by
        change φ'.compHom πZ = πY'.toRationalMap
        rw [← hφ'W, compHom_compHom, hq'S, ← compHom_compHom, Crepant.compHom_eq_of_isInverse hh',
          toRationalMap_compHom, Category.id_comp]
      not_isInverseExceptional := fun F hF => by
        obtain ⟨G, hG⟩ : ∃ G, RationalMap.transformPrimeDivisor φ G = some F := by
          have := hφ.not_isInverseExceptional F
          simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
        obtain ⟨D, hD⟩ := hC2 G F hG
        exact hF D (by rw [hC1 G D hD, hG])
      isRelativelyNef := by rw [hTT, hTT]; exact hφ.isRelativelyNef
      exists_resolution := ⟨W', inferInstance, inferInstance, inferInstance, p' ≫ sY', p',
        r ≫ q₀, h', hW'v.1, hW'sm, rfl, hq'Z, hp'proj, hq'proj, hp'b, hq'b, hh', hφ'W, GY', GZ',
        hGY', hGZ'', DivisorWithCoeffs.isEffective_iff_nonneg.mpr hnn, hexc⟩ }, hTT, hflip,
    W', inferInstance, inferInstance, inferInstance, p' ≫ sY', p', r ≫ q₀, h', hW'v.1, hW'sm, rfl,
    hq'Z, hp'proj, hq'proj, hp'b, hq'b, hh', hφ'W, GY', GZ', hGY', hGZ'', htr⟩

end PartOneMain

/-- **A nef weak model survives a negative step, with its comparison.** Let `φ : Y ⤏ Z` be a nef
weak model over `S` of `(Y, C)`, over a field of characteristic zero, and `g : Y ⤏ Y⁺` a
`(K_Y + C)`-negative step over `S` (a divisorial contraction or a flip) with `Y⁺` `ℚ`-factorial
and projective, and `φ⁺ ∘ g = φ`. Then `φ⁺` is a nef weak model of `(Y⁺, g_* C)` with canonical
divisor `g_* K_Y`, and it has a smooth common projective model `p' : W' ⟶ Y⁺`, `q' : W' ⟶ Z`
on which the comparison coefficients are the old ones: if `g_* G = D`, the coefficient of
`p'^*(K_{Y⁺} + C⁺) - q'^*(K_Z + C_Z)` at a prime of `W'` over `D` is that of
`p^*(K_Y + C) - q^*(K_Z + C_Z)` at a prime over `G`, on every common projective model
`p : W ⟶ Y`, `q : W ⟶ Z` of `φ`. -/
public theorem IsNefWeakModel.isNefWeakModel_and_exists_model_of_negativeStep
    {k : Type u} [Field k] [CharZero k] {Y Z S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS]
    {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ KY C φ)
    {Y' : Scheme.{u}} [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    (sY' : Y' ⟶ Spec (.of k)) (πY' : Y' ⟶ S) (g : Y.RationalMap Y') [g.IsDominant]
    (φ' : Y'.RationalMap Z) (hY'p : MMP.Mori.IsProjectiveVariety k sY')
    (hY'q : IsQFactorial sY') (hπY' : πY' ≫ sS = sY')
    (hstep : (∃ f : Y ⟶ Y', f.toRationalMap = g ∧ f ≫ πY' = πY ∧
          MMP.Flips.IsNegativeExtremalContraction k sY sY'
            (MMP.Flips.logCanonicalDivisor KY C) f ∧
          IsBirationalMorphism f ∧
          ∃ E : MMP.Mori.PrimeDivisor Y, MMP.Flips.exceptionalSet f = E.support) ∨
        (∃ (V : Scheme.{u}) (sV : V ⟶ Spec (.of k)) (πV : V ⟶ S) (f : Y ⟶ V) (fp : Y' ⟶ V),
          f ≫ πV = πY ∧ fp ≫ πV = πY' ∧
          MMP.Flips.IsNegativeExtremalContraction k sY sV
            (MMP.Flips.logCanonicalDivisor KY C) f ∧
          MMP.Flips.IsFlip k sY sV sY' (MMP.Flips.logCanonicalDivisor KY C) f fp g))
    (hcomp : g.comp φ' = φ) :
    IsNefWeakModel sY' sZ sS πY' πZ (MMP.Mori.RationalMap.transformDivisor g KY)
        (MMP.Mori.RationalMap.transformDivisor g C) φ' ∧
      ∃ (W' : Scheme.{u}) (_ : IsIntegral W') (_ : IsLocallyNoetherian W') (_ : IsNormal W')
        (sW' : W' ⟶ Spec (.of k)) (p' : W' ⟶ Y') (q' : W' ⟶ Z) (h' : Y'.RationalMap W'),
        MMP.Mori.IsVariety k sW' ∧ MMP.Mori.IsSmoothScheme sW' ∧ p' ≫ sY' = sW' ∧
        q' ≫ sZ = sW' ∧ IsProjectiveMorphism p' ∧ IsProjectiveMorphism q' ∧
        IsBirationalMorphism p' ∧ IsBirationalMorphism q' ∧
        MMP.Mori.RationalMap.IsInverse p'.toRationalMap h' ∧ h'.compHom q' = φ' ∧
        ∃ GY' GZ' : RDivisor W',
          MMP.Flips.IsRCartierPullback p' (MMP.Flips.logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor g KY)
            (MMP.Mori.RationalMap.transformDivisor g C)) GY' ∧
          MMP.Flips.IsRCartierPullback q' (MMP.Flips.logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor φ' (MMP.Mori.RationalMap.transformDivisor g KY))
            (MMP.Mori.RationalMap.transformDivisor φ' (MMP.Mori.RationalMap.transformDivisor g C)))
            GZ' ∧
          ∀ {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
            (sW : W ⟶ Spec (.of k)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W)
            {GY GZ : RDivisor W},
            MMP.Mori.IsVariety k sW → p ≫ sY = sW → q ≫ sZ = sW →
            IsProjectiveMorphism p → IsProjectiveMorphism q →
            IsBirationalMorphism p → IsBirationalMorphism q →
            MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
            MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY →
            MMP.Flips.IsRCartierPullback q
              (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
                (MMP.Mori.RationalMap.transformDivisor φ C)) GZ →
            ∀ (G : MMP.Mori.PrimeDivisor Y) (D : MMP.Mori.PrimeDivisor Y')
              (P : MMP.Mori.PrimeDivisor W) (P' : MMP.Mori.PrimeDivisor W'),
              MMP.Mori.RationalMap.transformPrimeDivisor g G = some D →
              p P.genericPoint = G.genericPoint → p' P'.genericPoint = D.genericPoint →
              (GY' - GZ').coeff P' = (GY - GZ).coeff P := by
  have hYv := hφ.isNormalVariety_source
  have : IsSeparated sY := hYv.1.toIsSeparated
  have := isSeparated_terminal sY
  have : IsSeparated sY' := hY'q.1.1.toIsSeparated
  have := isSeparated_terminal sY'
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀,
    hhq₀, GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hφ.exists_resolution
  have : IsSeparated sW₀ := hW₀.toIsSeparated
  have : IsSeparated p₀ := Crepant.isSeparated_of_comp_eq hp₀Y
  rcases hstep with ⟨f, rfl, hfY, hf, hfb, -⟩ | ⟨V, sV, πV, f, fp, hfV, hfpV, hf, hfl⟩
  · have : IsProper f := hf.isContraction.isProper
    refine (fun h => ⟨h.1, h.2.2.2⟩) (hφ.isNefWeakModel_of_step_over hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b
      hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ hA₀ hA₀q hY'p hY'q hπY' hcomp hfb hY'q.1 f (𝟙 Y') hfb
      (isBirationalMorphism_of_isIso _) hf.isContraction.comp_eq (Category.id_comp _) hfY
      (Category.id_comp _)
      (by rw [toRationalMap_compHom, Category.comp_id])
      (fun D => (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D).le) ?_)
    intro G P₀ hP₀ h0
    exact not_isExceptional_of_coeff_eq_zero hφ f hfY hf hfb p₀ q₀ h₀ hW₀ hp₀Y hq₀Z hp₀ hq₀
      hp₀b hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ G P₀
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p₀ P₀ G).mpr hP₀) h0
  · have : IsProper f := hf.isContraction.isProper
    have : IsProper fp := hfl.isProper
    have : IsSeparated sV := hf.isNormalVariety_target.1.toIsSeparated
    have := isSeparated_terminal sV
    refine (fun h => ⟨h.1, h.2.2.2⟩) (hφ.isNefWeakModel_of_step_over hW₀ hp₀Y hq₀Z hp₀ hq₀ hp₀b
      hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ hA₀ hA₀q hY'p hY'q hπY' hcomp hfl.isModificationOf.1
      hf.isNormalVariety_target f fp
      hfl.isSmall_source.isBirationalMorphism hfl.isSmall.isBirationalMorphism
      hf.isContraction.comp_eq hfl.isSmall.comp_eq hfV hfpV hfl.isModificationOf.2 ?_
      (fun G _ _ _ => not_isExceptional_of_isFlip hfl.isSmall_source hfl.isSmall
        hfl.isModificationOf.2 G))
    intro D
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hfl.isSmall D
    rw [hQ]
    exact (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le

/-- **A nef weak model survives each negative step.** Let `φ : Y ⤏ Z` be a nef weak model over
`S` of `(Y, C)`, with `Y`, `Z` `ℚ`-factorial, over a field of characteristic zero. Then

1. for every `(K_Y + C)`-negative step `g : Y ⤏ Y⁺` over `S` (a divisorial contraction or a
   flip) with `Y⁺` `ℚ`-factorial and `φ⁺ : Y⁺ ⤏ Z` with `φ⁺ ∘ g = φ`, `φ⁺` is a nef weak model of
   `(Y⁺, g_* C)` with canonical divisor `g_* K_Y`, and no prime divisor `G` of `Y` with comparison
   coefficient `0` (on any common model `W` of `Y` and `Z`) is `g`-exceptional;
2. there is no `(K_Y + C)`-negative extremal contraction `f : Y ⟶ V` over `S` with
   `dim V < dim Y`. -/
@[mmp "lem_fourfold_weak_model_survives_step"]
public theorem IsNefWeakModel.isNefWeakModel_of_negativeStep
    {k : Type u} [Field k] [CharZero k] {Y Z S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS]
    {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ KY C φ)
    (hQY : IsQFactorial sY) (hQZ : IsQFactorial sZ) :
    (∀ {Y' : Scheme.{u}} [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
      (sY' : Y' ⟶ Spec (.of k)) (πY' : Y' ⟶ S) (g : Y.RationalMap Y') [g.IsDominant]
      (φ' : Y'.RationalMap Z),
      MMP.Mori.IsProjectiveVariety k sY' → IsQFactorial sY' → πY' ≫ sS = sY' →
      ((∃ f : Y ⟶ Y', f.toRationalMap = g ∧ f ≫ πY' = πY ∧
          MMP.Flips.IsNegativeExtremalContraction k sY sY'
            (MMP.Flips.logCanonicalDivisor KY C) f ∧
          IsBirationalMorphism f ∧
          ∃ E : MMP.Mori.PrimeDivisor Y, MMP.Flips.exceptionalSet f = E.support) ∨
        (∃ (V : Scheme.{u}) (sV : V ⟶ Spec (.of k)) (πV : V ⟶ S) (f : Y ⟶ V) (fp : Y' ⟶ V),
          f ≫ πV = πY ∧ fp ≫ πV = πY' ∧
          MMP.Flips.IsNegativeExtremalContraction k sY sV
            (MMP.Flips.logCanonicalDivisor KY C) f ∧
          MMP.Flips.IsFlip k sY sV sY' (MMP.Flips.logCanonicalDivisor KY C) f fp g)) →
      g.comp φ' = φ →
      IsNefWeakModel sY' sZ sS πY' πZ (MMP.Mori.RationalMap.transformDivisor g KY)
          (MMP.Mori.RationalMap.transformDivisor g C) φ' ∧
        ∀ {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
          (sW : W ⟶ Spec (.of k)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W)
          {GY GZ : RDivisor W},
          MMP.Mori.IsVariety k sW → p ≫ sY = sW → q ≫ sZ = sW →
          IsProjectiveMorphism p → IsProjectiveMorphism q →
          IsBirationalMorphism p → IsBirationalMorphism q →
          MMP.Mori.RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
          MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY →
          MMP.Flips.IsRCartierPullback q
            (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
              (MMP.Mori.RationalMap.transformDivisor φ C)) GZ →
          ∀ (G : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor W),
            MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P = some G →
            (GY - GZ).coeff P = 0 → ¬ MMP.Mori.RationalMap.IsExceptional g G) ∧
    ∀ {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (πV : V ⟶ S) (f : Y ⟶ V),
      MMP.Flips.IsNegativeExtremalContraction k sY sV (MMP.Flips.logCanonicalDivisor KY C) f →
      f ≫ πV = πY → topologicalKrullDim V < topologicalKrullDim Y → False := by
  refine ⟨?_, fun {V} sV πV f hf hfV hdim => false_of_isNefWeakModel_of_lt hφ πV f hf hfV hdim⟩
  intro Y' _ _ _ _ sY' πY' g _ φ' hY'p hY'q hπY' hstep hcomp
  refine ⟨?_, ?_⟩
  · exact (hφ.isNefWeakModel_and_exists_model_of_negativeStep sY' πY' g φ' hY'p hY'q hπY' hstep
      hcomp).1
  · intro W _ _ _ sW p q h GY GZ hW hpY hqZ hp hq hpb hqb hinv hhq hGY hGZ G P hPG h0
    have : IsSeparated sY' := hY'q.1.1.toIsSeparated
    have := isSeparated_terminal sY'
    rcases hstep with ⟨f, rfl, hfY, hf, hfb, -⟩ | ⟨V, sV, πV, f, fp, hfV, hfpV, hf, hfl⟩
    · exact not_isExceptional_of_coeff_eq_zero hφ f hfY hf hfb p q h hW hpY hqZ hp hq hpb hqb
        hinv hhq hGY hGZ G P hPG h0
    · have : IsSeparated sV := hf.isNormalVariety_target.1.toIsSeparated
      have := isSeparated_terminal sV
      exact not_isExceptional_of_isFlip hfl.isSmall_source hfl.isSmall hfl.isModificationOf.2 G

end MMP.Fourfold

end
