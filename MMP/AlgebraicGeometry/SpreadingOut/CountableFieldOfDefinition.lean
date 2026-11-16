module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Positivity.BigNefCartier
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsMaps
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
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
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
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
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Nef and big pull-backs, point blowups of surfaces, and countable fields of definition

This file collects three independent results used in the construction of flips.

**Birational pull-backs of ample divisors are nef and big.** Let `g : Y ⟶ T` be a projective
birational morphism of projective varieties over a field `k`, with `Y` smooth, and let `A` be an
ample `ℚ`-Cartier divisor on `T`: some positive multiple `mA` is a Cartier divisor whose
invertible sheaf `L = 𝒪_T(mA)` is ample. Then the pull-back `g^*A` is nef (it has nonnegative
degree on every proper curve of `Y`) and big (`h⁰(Y, 𝒪_Y(m' g^*A))` grows like `m'^{dim Y}` for
a Cartier multiple). For nefness, the degree of `g^*L` on a proper curve `C ⊆ Y` is the degree of
`L` along `C → T`: zero if `g(C)` is a point, and otherwise `[k(C) : k(g(C))]` times the degree
of the ample restriction `L|_{g(C)}`, which is positive. For bigness, write `L ≅ 𝒪_T(A)` for a
Cartier divisor `A`; ampleness gives `h⁰(T, 𝒪_T(jA)) > c jⁿ` for `j ≫ 0` with
`n = dim T = dim Y`, and pulling back sections along the dominant morphism `g` is injective, so
`h⁰(T, 𝒪_T(jA)) ≤ h⁰(Y, 𝒪_Y(jD))`.

**Resolving a rational map from a smooth projective surface by point blowups.** Let `X` be a
smooth projective surface over an algebraically closed field `k` and `f : X ⇢ Y` a rational map
over `k` to a projective `k`-scheme `Y`. Then there is a finite sequence of blowups at closed
points `X = S₀ ← S₁ ← ⋯ ← Sₙ`, `S_{j+1} = Bl_{p_j} S_j`, such that `f` composed with
`π : Sₙ ⟶ X` extends to a morphism `g : Sₙ ⟶ Y` ([Stacks, Tag 0C5H]). Moreover the total
transforms `E_j` on `Sₙ` of the exceptional curves satisfy `E_i · E_j = -δ_{ij}`. Each
exceptional curve `F ≅ ℙ¹` has `F² = -1` and `(π^* D · F) = 0`, computed by cutting the
intersection number down to a degree on `F` ([Stacks, Tag 0BEU]); the total transform of `F` is
its Cartier pull-back, and the projection formula along the birational composite
([Stacks, Tag 0BET]) carries the intersection numbers from `Sₙ` back to the blowup where `F`
appears.

**Countable diagrams are defined over a countable algebraically closed field.** Let `k` be an
algebraically closed field of characteristic zero. A countable diagram of schemes of finite type
over `k`, together with countably many coherent sheaves on its members and countably many
homomorphisms between pullbacks of these sheaves along the morphisms of the diagram, has a model
over a countable algebraically closed subfield `k₀ ⊆ k`. The field `k₀` may be taken to contain
any prescribed countable subfield `k₁`, and any part of the data that already has a model over
`k₁` keeps that model: over `k₀` it is the base change of the prescribed `k₁`-model. A model over
`k₀` is a diagram `F₀` of `k₀`-schemes, a natural transformation `π : F ⟶ F₀` over
`Spec k → Spec k₀` all of whose squares are cartesian, sheaves `M₀` with `M ≅ π^* M₀`, and
homomorphisms `φ₀` whose pullbacks along `π` are the given ones. The countable algebraically
closed subfields of `k` containing `k₁` form a directed set in which every countable family has
an upper bound, and `k` is their union, so `Spec k` is the limit of the cofiltered system of
their spectra, with affine transition maps. Schemes of finite presentation and morphisms between
them descend to a stage ([Stacks, Tag 01ZM]), and so do modules of finite presentation and
morphisms between them ([Stacks, Tag 01ZR]); countably many pieces of data descend to a common
stage because countable families of stages have lower bounds.

## Main results

* `MMP.Mori.QDivisor.isNef_and_isBig_of_isBirationalMorphism`: nefness and bigness of the
  pull-back of an ample `ℚ`-Cartier divisor along a projective birational morphism.
* `MMP.Fourfold.exists_pointBlowups_comp_eq_of_partialMap`: the resolution of indeterminacy of a
  rational map from a smooth projective surface by point blowups, together with the
  intersection matrix of the total exceptional transforms.
* `MMP.FieldOfDefinition.exists_countable_isAlgClosed_model`: a countable diagram of finite
  type schemes, coherent sheaves and homomorphisms has a model over a countable algebraically
  closed subfield.

## Implementation notes

The ample `ℚ`-Cartier divisor `A` on `T` is given by an ample invertible sheaf `L` on `T` and a
positive integer `m`, standing for `A = (1/m) L`, so that `T` need not be normal. The pull-back
`g^*A` is any `ℚ`-divisor `B` on the normal scheme `Y` such that `mB` is a Cartier divisor `D`
with `𝒪_Y(D) ≅ g^*L`. This determines `B` up to `ℚ`-linear equivalence, and the statement is
made for every such `B`.

The tower of point blowups is a sequence `S : ℕ → Scheme` with morphisms
`σ i : S (i + 1) ⟶ S i`, of which the first `n` are blowups at closed points `p i` (up to
isomorphism over `S i`); the composites `Sₙ ⟶ S_j` are the maps of
`CategoryTheory.Functor.ofOpSequence σ`, and the terms beyond `n` are irrelevant. The rational
map is given by a representative `f : X.PartialMap Y`. The total transform of the `j`-th
exceptional curve is the Weil divisor `MMP.Resolution.divisorialPart` of the inverse image on
`Sₙ` of the ideal sheaf of the point `p j`, whose inverse image on `S_{j+1}` is the exceptional
divisor of the `j`-th blowup. Intersection numbers are `MMP.Mori.Divisor.intersectionNumberOn`
on `Sₙ`.

In the field-of-definition statement, closed subschemes, open subschemes, Cartier divisors,
projective embeddings and morphisms to fixed schemes are members and morphisms of the diagram.
Rational sections are homomorphisms from structure sheaves of open subschemes, and isomorphisms
of sheaves are pairs of mutually inverse homomorphisms. A canonical object such as `ℙⁿ_k` or
`𝒪_X` is pinned by putting its model over the prime field into the retained part. Equalities
among the data do not have to be listed: base change along `k₀ → k` is faithful, so they
descend. "Coherent" is quasicoherent of finite type, which is the same thing over a scheme of
finite type over a field.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.60, 2.61
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 0BET](https://stacks.math.columbia.edu/tag/0BET)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

universe u

namespace MMP.Mori.QDivisor

open CategoryTheory AlgebraicGeometry Opposite

/-- An ample invertible sheaf has nonnegative degree along every curve mapping to `T`. -/
private theorem degreeOn_nonneg_of_isAmple {k : Type u} [Field k] {C T : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] [LocallyOfFiniteType sT] (φ : C ⟶ T)
    [AlgebraicGeometry.IsCurve k (φ ≫ sT)] [IsProper (φ ≫ sT)] (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple T L) :
    0 ≤ degreeOn k sT φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sT)).le L := by
  by_cases hpt : ∃ x : T, Set.range φ = {x}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sT φ L hpt]
  · rw [degreeOn_eq_degreeOver_mul sT φ L hpt]
    have : IsProper φ := IsProper.of_comp φ sT
    have : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    have : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hpt
    have h1 := isAmple_pullback_of_isFinite φ.imageι L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T L).mpr hL)
    have := MMP.Mori.isInvertible_pullback_obj φ.imageι L
    have h2 := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (φ.imageι ≫ sT)
      (topologicalKrullDim_image_le_one sT φ) _ h1
    exact mul_nonneg (by positivity) h2.le

/-- The `ℚ`-divisor `B` with `mB = D`, `𝒪_Y(D) ≅ g^*L` and `L` ample is nef. -/
private theorem isNef_of_pullback {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] (hT : MMP.Mori.IsVariety k sT)
    (g : Y ⟶ T) (hg : g ≫ sT = sY)
    (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] (hL : Stacks.Ample.IsAmple T L)
    (m : ℕ) (hm : 0 < m) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L)
    (B : QDivisor Y) (hB : Divisor.toQDivisor D = (m : ℚ) • B) :
    B.IsNef k sY := by
  have hB' : Divisor.toQDivisor D = (m : ℤ) • B := by
    rw [hB, Nat.cast_smul_eq_nsmul ℚ, ← natCast_zsmul]
  have hBq : B.IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', ⟨D, hB', hD⟩⟩
  refine (QDivisor.isNef_iff B hBq).mpr fun C i _ _ _ hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul k sY i hC.le B hBq hm D hD hB']
  refine div_nonneg ?_ (by positivity)
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hD.isInvertibleModule_divisorialSheaf
  have := hT.toIsSeparated
  have := hT.toLocallyOfFiniteType
  have hc : (i ≫ g) ≫ sT = i ≫ sY := by rw [Category.assoc, hg]
  have : IsProper ((i ≫ g) ≫ sT) := hc ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ g) ≫ sT) := by
    rw [hc]
    exact { topologicalKrullDim_eq_one := hC }
  have h1 : D.degreeOn k sY i hC.le hD = degreeOn k sT (i ≫ g)
      (IsCurve.topologicalKrullDim_eq_one (f := (i ≫ g) ≫ sT)).le L := by
    rw [← degreeOn_pullback_eq_degreeOn_comp sY sT g i hg]
    exact degreeOn_eq_of_iso k sY i hC.le e
  rw [h1]
  exact_mod_cast degreeOn_nonneg_of_isAmple sT (i ≫ g) L hL

/-- Restricting a section of a module twice is restricting it once. -/
private theorem map_map_homOfLE {X : Scheme.{u}} (L : X.Modules) {P Q R : X.Opens} (h₁ : Q ≤ P)
    (h₂ : P ≤ R) (σ : Γ(L, R)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op σ) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of a module to its own open does nothing. -/
private theorem map_homOfLE_refl {X : Scheme.{u}} (L : X.Modules) {W : X.Opens} (σ : Γ(L, W)) :
    L.presheaf.map (homOfLE (le_refl W)).op σ = σ := by
  rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A generator of an invertible module over every open inside `K` pulls back, along the unit of
`b^* ⊣ b_*`, to a generator over every open inside `b⁻¹ K`. -/
private theorem bijective_smul_unit_app {X Y : Scheme.{u}} (b : X ⟶ Y) (A : Y.Modules)
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

/-- A global section of an invertible module on an integral scheme vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_map_eq_zero {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens} (hV : (V : Set X).Nonempty)
    (s : Γ(L, ⊤)) (hs : L.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s = 0) : s = 0 := by
  have hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
  have key : ∀ x : X, ∃ (K : X.Opens) (_ : x ∈ K),
      L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s = 0 := by
    intro x
    obtain ⟨K, hx, a, ha⟩ : ∃ (K : X.Opens) (_ : x ∈ K) (a : Γ(L, K)), ∀ (W : X.Opens)
        (hW : W ≤ K), Function.Bijective
          (fun c : Γ(X, W) => c • L.presheaf.map (homOfLE hW).op a) :=
      @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible X.toRingedSpace _ L hL x
    refine ⟨K, hx, ?_⟩
    obtain ⟨g, hg⟩ := (ha K le_rfl).2 (L.presheaf.map (homOfLE le_top : K ⟶ ⊤).op s)
    simp only [map_homOfLE_refl] at hg
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter K.2 V.2 ⟨x, hx⟩ hV
    have : Nonempty (K ⊓ V : X.Opens) := ⟨⟨z, hz⟩⟩
    -- `g` vanishes on `K ⊓ V`, hence on `K` since `X` is integral
    have hg0 : g = 0 := by
      refine map_injective_of_isIntegral X (homOfLE inf_le_left : K ⊓ V ⟶ K) ?_
      rw [map_zero]
      refine (ha (K ⊓ V) inf_le_left).1 ?_
      dsimp only
      rw [zero_smul, ← Scheme.Modules.map_smul, hg, map_map_homOfLE,
        ← map_map_homOfLE L (inf_le_right : K ⊓ V ≤ V) (le_top : V ≤ ⊤), hs, map_zero]
    rw [← hg, hg0, zero_smul]
  choose K hxK hK using key
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ K ⊤
    (fun x => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxK x⟩) s 0
    fun x => ?_
  change L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op s =
    L.presheaf.map (homOfLE le_top : K x ⟶ ⊤).op 0
  rw [hK x, map_zero]

/-- Pull-back of sections of an invertible sheaf along a dominant quasi-compact morphism of
integral schemes is injective on global sections. -/
private theorem unit_app_top_injective {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] (g : Y ⟶ T)
    [IsDominant g] [QuasiCompact g] (M : T.Modules) [Stacks.Ample.IsInvertibleModule T M] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤) := by
  have hMinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (structureSheafRing T.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  set L := (Scheme.Modules.pullback g).obj M
  set η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨y0⟩ : Nonempty Y := inferInstance
  obtain ⟨K, hyK, a, ha⟩ : ∃ (K : T.Opens) (_ : g y0 ∈ K) (a : Γ(M, K)), ∀ (W : T.Opens)
      (hW : W ≤ K), Function.Bijective
        (fun c : Γ(T, W) => c • M.presheaf.map (homOfLE hW).op a) :=
    @Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible T.toRingedSpace _ M hMinv (g y0)
  obtain ⟨U, hUaff, hyU, hUK⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyK
  set e : Γ(L, g ⁻¹ᵁ U) := η.app U (M.presheaf.map (homOfLE hUK).op a)
  have hgen := bijective_smul_unit_app g M (M.presheaf.map (homOfLE hUK).op a)
    (fun W hW => by simpa only [map_map_homOfLE] using ha W (hW.trans hUK)) (g ⁻¹ᵁ U) le_rfl
  set t := M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  obtain ⟨f, hf⟩ := (ha U hUK).2 t
  have hηt : η.app U t = 0 := by
    refine (PresheafOfModules.naturality_apply η.val (homOfLE le_top : U ⟶ ⊤).op s).trans ?_
    change _ = (0 : _)
    erw [hs, map_zero]
    rfl
  have hgf : g.app U f = 0 := by
    refine hgen.1 ?_
    change g.app U f • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e =
      (0 : Γ(Y, g ⁻¹ᵁ U)) • L.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ U))).op e
    rw [map_homOfLE_refl, zero_smul]
    refine Eq.trans ?_ hηt
    rw [← hf, Scheme.Modules.Hom.app_smul]
    rfl
  have : IsSchemeTheoreticallyDominant g := .of_isDominant _
  have hf0 : f = 0 := g.app_injective U (by rw [hgf, map_zero])
  have ht0 : t = 0 := by rw [← hf, hf0]; exact zero_smul _ _
  exact eq_zero_of_map_eq_zero M ⟨g y0, hyU⟩ s ht0

/-- For Cartier `D` with `𝒪_Y(D) ≅ g^*𝒪_T(A)`, the iterated isomorphism
`𝒪_Y((n+1)D) ≅ g^*𝒪_T((n+1)A)`, built from `𝒪(D) ⊗ 𝒪(D') ≅ 𝒪(D + D')` on both sides and
`g^*(F ⊗ G) ≅ g^*F ⊗ g^*G`. -/
private noncomputable def isoPullbackSucc {Y T : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (g : Y ⟶ T) (A : T.CartierDivisor) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf A)) :
    ∀ n : ℕ, ((n + 1) • D).divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf ((n + 1) • A))
  | 0 => eqToIso (by rw [zero_add, one_smul]) ≪≫ e ≪≫
      (Scheme.Modules.pullback g).mapIso (eqToIso (by rw [zero_add, one_smul]))
  | n + 1 =>
      eqToIso (by rw [succ_nsmul]) ≪≫ ((hD.nsmul (n + 1)).divisorialSheafTensorIso hD).symm ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso Y (isoPullbackSucc g A D hD e n) e ≪≫
        (Stacks.RelativeVeryAmple.pullbackTensorModulesIso g _ _).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          (MMP.CartierDivisorSheaf.sheafMulIso ((n + 1) • A) A ≪≫
            eqToIso (by rw [← succ_nsmul]))

/-- `scalarsToGlobalSections` through `appLE`. -/
private theorem scalarsToGlobalSections_eq_appLE {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) :
    scalarsToGlobalSections k sX =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ ⊤ (by simp)).hom := by
  have : sX.appLE ⊤ ⊤ (by simp) = sX.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [this]
  rfl

/-- The global sections of `𝒪_Y(D)`, `D` Cartier on a proper `k`-scheme, are finite over `k`. -/
private theorem finite_divisorialSubmodule_top {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsProper sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {D : Divisor Y} (hD : D.IsCartier) :
    letI := Module.compHom (D.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY);
    Module.Finite k (D.divisorialSubmodule ⊤) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k sY
    D.divisorialSheaf 1
  have := finiteDimensional_cohomologyOverField_of_isProper k sY D.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sY D.divisorialSheaf).toLinearEquiv
  have key : ∀ ψ : k →+* Γ(Y, ⊤),
      ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom (D.divisorialSubmodule ⊤) ψ;
          Module.Finite k (D.divisorialSubmodule ⊤)) := by
    rintro ψ rfl
    have := Module.Finite.equiv e
    exact this
  exact key _ (scalarsToGlobalSections_eq_appLE sY)

/-- Pull-back of sections along a dominant morphism of varieties: for a Cartier divisor `A` on
`T` and a Cartier divisor `D` on `Y` with `𝒪_Y(D) ≅ g^*𝒪_T(A)`, and every integer `j > 0`,
`h⁰(T, 𝒪_T(jA)) ≤ h⁰(Y, 𝒪_Y(jD))`. -/
private theorem cartierH0_le_h0_of_iso_pullback {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y] (hYp : IsProjectiveMorphism sY)
    (hT : MMP.Mori.IsVariety k sT) (g : Y ⟶ T) (hg : g ≫ sT = sY)
    (hgb : IsBirationalMorphism g) (A : T.CartierDivisor) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf A))
    (j : ℤ) (hj : 0 < j) :
    cartierH0 k sT (j • A) ≤ Divisor.h0 k sY (j • D) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = ((n + 1 : ℕ) : ℤ) := ⟨j.toNat - 1, by omega⟩
  rw [natCast_zsmul, natCast_zsmul]
  have := hY.toIsIntegral
  have := hT.toIsIntegral
  have : IsProper sY := isProper_of_isProjectiveMorphism _ hYp
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsDominant g := hgb.isDominant
  have := hT.toIsSeparated
  have : QuasiCompact (g ≫ sT) := hg ▸ inferInstance
  have : QuasiCompact g := QuasiCompact.of_comp g sT
  have hsc : ∀ c, g.appTop (scalarsToGlobalSections k sT c) = scalarsToGlobalSections k sY c := by
    intro c
    subst hg
    simp only [scalarsToGlobalSections, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  set M := MMP.CartierDivisor.sheaf ((n + 1) • A)
  have : Stacks.Ample.IsInvertibleModule T M := inferInstance
  set D' := (n + 1) • D
  have hD' : D'.IsCartier := hD.nsmul _
  let E := isoPullbackSucc g A D hD e n
  let η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M
  letI := Module.compHom Γ(M, ⊤) (scalarsToGlobalSections k sT)
  letI := Module.compHom (D'.divisorialSubmodule ⊤) (scalarsToGlobalSections k sY)
  have : Module.Finite k (D'.divisorialSubmodule ⊤) := finite_divisorialSubmodule_top sY hD'
  let φ : Γ(M, ⊤) →ₗ[k] D'.divisorialSubmodule ⊤ :=
    { toFun s := E.inv.app ⊤ (η.app ⊤ s)
      map_add' s t := by
        rw [map_add]
        exact map_add _ _ _
      map_smul' c s := by
        change E.inv.app ⊤ (η.app ⊤ (scalarsToGlobalSections k sT c • s)) =
          (scalarsToGlobalSections k sY c • (E.inv.app ⊤ (η.app ⊤ s) : D'.divisorialSubmodule ⊤))
        rw [Scheme.Modules.Hom.app_smul, ← hsc c]
        exact Scheme.Modules.Hom.app_smul E.inv _ _ }
  have h2 : ∀ x, E.hom.app ⊤ (E.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.inv_hom_id]
    rfl
  have hφ : Function.Injective φ := fun s t hst => by
    refine unit_app_top_injective g M ?_
    have := congrArg (E.hom.app ⊤) hst
    change E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ s)) = E.hom.app ⊤ (E.inv.app ⊤ (η.app ⊤ t)) at this
    exact (h2 _).symm.trans (this.trans (h2 _))
  exact LinearMap.finrank_le_finrank_of_injective hφ

/-- The `ℚ`-divisor `B` with `mB = D`, `𝒪_Y(D) ≅ g^*L` and `L` ample is big. -/
private theorem isBig_of_pullback {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    [IsLocallyNoetherian Y] [IsNormal Y] (hYp : IsProjectiveMorphism sY)
    (hT : MMP.Mori.IsVariety k sT) (hTp : IsProjectiveMorphism sT) (g : Y ⟶ T)
    (hg : g ≫ sT = sY) (hgb : IsBirationalMorphism g)
    (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] (hL : Stacks.Ample.IsAmple T L)
    (m : ℕ) (hm : 0 < m) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L)
    (B : QDivisor Y) (hB : Divisor.toQDivisor D = (m : ℚ) • B) :
    B.IsBig k sY := by
  have := hT.toIsIntegral
  have := hY.toIsIntegral
  obtain ⟨A, ⟨eA⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have hA : Stacks.Ample.IsAmple T (MMP.CartierDivisor.sheaf A) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T _).mp
      (Scheme.Modules.isAmple_of_iso eA
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T L).mpr hL))
  have hbig : IsBigCartier k sT A :=
    isBigCartier_of_linearlyEquivalent_add (E := 0) (m := 1) ⟨hTp⟩ one_pos hA
      MMP.Intersection.isEffective_zero
      (by simpa using MMP.Intersection.LinearlyEquivalent.refl _)
  obtain ⟨n, hn, c, hc, k₀, hk⟩ := hbig
  have hdim : topologicalKrullDim T = topologicalKrullDim Y :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sY hgb
  refine ⟨m, hm, D, hB, hD, n, hdim ▸ hn, c, hc, max k₀ 1, fun j hj => ?_⟩
  refine (hk j (le_of_max_le_left hj)).trans_le ?_
  exact_mod_cast cartierH0_le_h0_of_iso_pullback sY sT hY hYp hT g hg hgb A D hD
    (e ≪≫ (Scheme.Modules.pullback g).mapIso eA) j (lt_of_lt_of_le one_pos (le_of_max_le_right hj))

/-- **Ample pull-backs along birational morphisms are nef and big.** Let `g : Y ⟶ T` be a
projective birational morphism of projective varieties over `k`, with `Y` smooth, `L` an ample
invertible sheaf on `T` and `m > 0`. If `B` is a `ℚ`-divisor on `Y` such that `mB` is a Cartier
divisor `D` with `𝒪_Y(D) ≅ g^*L` (that is, `B = g^*A` for the ample `ℚ`-Cartier divisor
`A = (1/m) L`), then `B` is nef and big. -/
@[mmp "lem_mmp_ample_birational_pullback_nef_big"]
public theorem isNef_and_isBig_of_isBirationalMorphism {k : Type u} [Field k] {Y T : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) (hY : IsVariety k sY) [Smooth sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] (hYp : IsProjectiveMorphism sY)
    (hT : IsVariety k sT) (hTp : IsProjectiveMorphism sT) (g : Y ⟶ T) (hg : g ≫ sT = sY)
    (hgp : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L] (hL : Stacks.Ample.IsAmple T L)
    (m : ℕ) (hm : 0 < m) (D : Divisor Y) (hD : D.IsCartier)
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj L)
    (B : QDivisor Y) (hB : Divisor.toQDivisor D = (m : ℚ) • B) :
    B.IsNef k sY ∧ B.IsBig k sY :=
  ⟨isNef_of_pullback sY sT hT g hg L hL m hm D hD e B hB,
    isBig_of_pullback sY sT hY hYp hT hTp g hg hgb L hL m hm D hD e B hB⟩

end MMP.Mori.QDivisor

/-! ### Resolving a rational map from a surface by point blowups -/

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry

/-- A sequence of `n` blowups at closed points of `X`, with composite `Z ⟶ X`. -/
private inductive ChainLen (X : Scheme.{u}) : ℕ → ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop
  | refl : ChainLen X 0 X (𝟙 X)
  | step {n : ℕ} {W : Scheme.{u}} {h : W ⟶ X} (hh : ChainLen X n W h) (w : W)
      (hw : IsClosed ({w} : Set W)) :
      ChainLen X (n + 1) (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)

/-- Every point blowup chain has a length. -/
private theorem exists_chainLen {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X}
    (h : Stacks.ResolutionOfSurfaces.PointBlowupChain X T Z p) : ∃ n, ChainLen X n Z p := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step _ w hw _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, hn.step w hw⟩

/-- A chain of positive length begins with the blowup of a closed point of its base. -/
private theorem ChainLen.head {X Z : Scheme.{u}} {m : ℕ} {p : Z ⟶ X} (h : ChainLen X m Z p) :
    (m = 0 ∧ Z = X ∧ HEq p (𝟙 X)) ∨ ∃ n, m = n + 1 ∧ ∃ (x : X) (hx : IsClosed ({x} : Set X))
      (q : Z ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)),
      ChainLen (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) n Z q ∧
        p = q ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) := by
  induction h with
  | refl => exact .inl ⟨rfl, rfl, HEq.rfl⟩
  | step hh w hw ih =>
    rcases ih with ⟨hm, hZ, hp⟩ | ⟨n', hm, x, hx, q, hq, hpq⟩
    · subst hm hZ
      obtain rfl := eq_of_heq hp
      exact .inr ⟨0, rfl, w, hw, 𝟙 _, .refl, by rw [Category.comp_id, Category.id_comp]⟩
    · subst hm hpq
      exact .inr ⟨n' + 1, rfl, x, hx, _, hq.step w hw, (Category.assoc _ _ _).symm⟩

/-- Prepend an object to a sequence. -/
private def consSeq {C : Type*} (X : C) (S : ℕ → C) : ℕ → C
  | 0 => X
  | i + 1 => S i

/-- Prepend a morphism to a sequence of morphisms. -/
private def consHom {C : Type*} [Category C] {X : C} {S : ℕ → C} (f : S 0 ⟶ X)
    (σ : ∀ i, S (i + 1) ⟶ S i) : ∀ i, consSeq X S (i + 1) ⟶ consSeq X S i
  | 0 => f
  | i + 1 => σ i

/-- The composite of a sequence with a prepended morphism. -/
private theorem ofOpSequence_consHom {C : Type*} [Category C] {X : C} {S : ℕ → C}
    (f : S 0 ⟶ X) (σ : ∀ i, S (i + 1) ⟶ S i) (m : ℕ) :
    (Functor.ofOpSequence (consHom f σ)).map (homOfLE (Nat.zero_le (m + 1))).op =
      (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le m)).op ≫ f := by
  induction m with
  | zero =>
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rw [show (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    exact (Category.id_comp f).symm
  | succ m ih =>
    have h1 : (homOfLE (Nat.zero_le (m + 1 + 1)) : (0 : ℕ) ⟶ m + 1 + 1) =
        homOfLE (Nat.zero_le (m + 1)) ≫ homOfLE (Nat.le_succ (m + 1)) := rfl
    have h2 : (homOfLE (Nat.zero_le (m + 1)) : (0 : ℕ) ⟶ m + 1) =
        homOfLE (Nat.zero_le m) ≫ homOfLE (Nat.le_succ m) := rfl
    rw [h1, op_comp, Functor.map_comp, ih, Functor.ofOpSequence_map_homOfLE_succ, h2, op_comp,
      Functor.map_comp, Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.assoc _ _ _).symm

/-- A chain of `n` point blowups is, up to isomorphism of its source, a tower indexed by `ℕ`. -/
private theorem exists_tower_of_chainLen (n : ℕ) : ∀ {X Z : Scheme.{u}} {p : Z ⟶ X},
    ChainLen X n Z p →
    ∃ (S : ℕ → Scheme.{u}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ X)
      (pts : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({pts j} : Set (S j))),
      (∀ j : Fin n, ∃ φ : S (j + 1) ≅
          blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{pts j}, hp j⟩),
        σ j = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{pts j}, hp j⟩)) ∧
      ∃ ψ : S n ≅ Z,
        ψ.hom ≫ p = (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom := by
  induction n with
  | zero =>
    intro X Z p h
    rcases h.head with ⟨-, rfl, hp⟩ | ⟨n, hn, -⟩
    · obtain rfl := eq_of_heq hp
      refine ⟨fun _ => Z, fun _ => 𝟙 Z, Iso.refl Z, fun j => j.elim0, fun j => j.elim0,
        fun j => j.elim0, Iso.refl Z, ?_⟩
      have : (homOfLE (Nat.zero_le 0) : (0 : ℕ) ⟶ 0) = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).symm
    · omega
  | succ n ih =>
    intro X Z p h
    rcases h.head with ⟨h0, -⟩ | ⟨n', hn, x, hx, q, hq, rfl⟩
    · omega
    obtain rfl : n = n' := by omega
    obtain ⟨S, σ, e, pts, hp, hσ, ψ, hψ⟩ := ih hq
    let b := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)
    let pts' : ∀ j : Fin (n + 1), consSeq (C := Scheme.{u}) X S j := fun j =>
      match j with
      | ⟨0, _⟩ => x
      | ⟨i + 1, hi⟩ => pts ⟨i, by omega⟩
    let hp' : ∀ j : Fin (n + 1),
        IsClosed ({pts' j} : Set (consSeq (C := Scheme.{u}) X S j)) := fun j =>
      match j with
      | ⟨0, _⟩ => hx
      | ⟨i + 1, hi⟩ => hp ⟨i, by omega⟩
    refine ⟨consSeq (C := Scheme.{u}) X S, consHom (e.hom ≫ b) σ, Iso.refl X, pts', hp', ?_, ψ, ?_⟩
    · rintro ⟨_ | i, hi⟩
      · exact ⟨e, rfl⟩
      · exact hσ ⟨i, by omega⟩
    · rw [ofOpSequence_consHom]
      exact (Category.assoc ψ.hom q b).symm.trans ((congrArg (· ≫ b) hψ).trans
        ((Category.assoc _ _ _).trans (Category.comp_id _).symm))

/-- The resolution half: a tower of blowups at closed points over which `f` extends to a
`k`-morphism ([Stacks, Tag 0C5H]). -/
private theorem exists_pointBlowupTower_resolving (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2) (hY : IsProjectiveMorphism sY)
    (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) :
    ∃ (n : ℕ) (S : ℕ → Scheme.{u}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ X)
      (p : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j))),
      (∀ j : Fin n, ∃ φ : S (j + 1) ≅
          blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩),
        σ j = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩)) ∧
      let π : S n ⟶ X := (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom
      (∃ g : S n ⟶ Y, g ≫ sY = π ≫ sX ∧
        (π ⁻¹ᵁ f.domain).ι ≫ g = (π ∣_ f.domain) ≫ f.hom) := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  have hreg := (isRegular_iff_regular_stalks X).1
    (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sX hXs)
  haveI : IsLocallyNoetherian X := hreg.1
  haveI : QuasiCompact sX := hX.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : IsProper (Y ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism sY hY
  haveI : f.IsOver (Spec (.of k)) := Scheme.PartialMap.isOver_iff.mpr hf
  obtain ⟨Z, q, h, hchain, hS, hagree⟩ :=
    Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two
      (S := Spec (.of k)) hreg.2 hXd f
  obtain ⟨n, hn⟩ := exists_chainLen hchain
  obtain ⟨S, σ, e, pts, hp, hσ, ψ, hψ⟩ := exists_tower_of_chainLen n hn
  refine ⟨n, S, σ, e, pts, hp, hσ, ?_⟩
  intro π
  have hψ' : ψ.hom ≫ q = π := hψ
  refine ⟨ψ.hom ≫ h, ?_, ?_⟩
  · rw [← hψ', Category.assoc, Category.assoc]
    exact congrArg (ψ.hom ≫ ·) hS
  · have hcond : ((π ⁻¹ᵁ f.domain).ι ≫ ψ.hom) ≫ q = (π ∣_ f.domain) ≫ f.domain.ι := by
      rw [Category.assoc, hψ', morphismRestrict_ι]
    calc _ = Limits.pullback.lift (f := q) (g := f.domain.ι) _ _ hcond ≫
          Limits.pullback.fst q f.domain.ι ≫ h := by
          rw [Limits.pullback.lift_fst_assoc, Category.assoc]
      _ = _ := by rw [hagree, Limits.pullback.lift_snd_assoc]

section IntersectionMatrix

open MMP.Mori MMP.Threefold.Resolution

local notation "𝓘[" y ", " hy "]" =>
  Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : TopologicalSpace.Closeds _)

variable {k : Type u} [Field k]

/-- A smooth proper surface over `k`. -/
private structure IsSmoothSurface {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) : Prop where
  variety : MMP.Mori.IsVariety k s
  smooth : MMP.Mori.IsSmoothScheme s
  dim : topologicalKrullDim Y = 2
  proper : IsProper s

/-- Being a smooth proper surface is invariant under isomorphism of the source. -/
private theorem IsSmoothSurface.of_iso {Y Y' : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsSmoothSurface s) (e : Y' ≅ Y) : IsSmoothSurface (e.hom ≫ s) := by
  have := h.variety
  have := h.proper
  have : LocallyOfFiniteType s := h.variety.toLocallyOfFiniteType
  have : IsIntegral Y := h.variety.toIsIntegral
  have : Nonempty Y' := ⟨e.inv (Classical.arbitrary Y)⟩
  have : IsIntegral Y' := isIntegral_of_isOpenImmersion e.hom
  refine ⟨(isVariety_iff _ _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ?_, ?_, inferInstance⟩
  · have : Smooth s := (isSmoothScheme_iff s).1 h.smooth
    exact (isSmoothScheme_iff _).2 inferInstance
  · rw [← h.dim]
    exact e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

variable [IsAlgClosed k]

/-- The blowup of a closed point of a smooth proper surface is a smooth proper surface. -/
private theorem IsSmoothSurface.blowUpToBase_comp {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsSmoothSurface s) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsSmoothSurface (blowUpToBase 𝓘[y, hy] ≫ s) := by
  obtain ⟨-, hprop, hbir, -⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection h.variety h.smooth
      h.dim hy
  have := h.proper
  have hv := isVariety_blowUp_singleton h.variety h.dim hy
  refine ⟨hv, isSmoothScheme_blowUp_singleton h.variety h.smooth h.dim hy, ?_, inferInstance⟩
  have := h.variety
  rw [← h.dim]
  exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s
    (blowUpToBase 𝓘[y, hy] ≫ s) hbir).symm

open Stacks.Divisors in
/-- On a proper surface, cutting by an effective Cartier prime divisor `P` whose invertible sheaf
is the first entry computes the intersection number as a degree on the curve `P`. -/
private theorem intersectionNumber_two_eq_degree {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (f : X ⟶ Spec (.of k)) [IsProper f] (hd : topologicalKrullDim X ≤ (2 : ℕ))
    (L : Fin 2 → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (P : MMP.Mori.PrimeDivisor X) [IsEffectiveCartierDivisor P.idealSheaf]
    (C : ProperCurve f) (hC : C.point = P.genericPoint)
    (e : L 0 ≅ (invertibleSheaf P.idealSheaf : X.Modules)) :
    intersectionNumber k f (𝟙 X) 2 hd L = C.degree k (L 1) := by
  have hdim := topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f
    (𝟙 X) 1 hd P.idealSheaf
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k f (𝟙 X) 1 hd L P.idealSheaf
    ((Scheme.Modules.pullbackId X).app _ ≪≫ e)]
  rw [intersectionNumber_congr_family k f _ 1 _ (M := fun _ => L 1)
    (funext fun t => by rw [Subsingleton.elim t 0]; rfl)]
  have hdim1 : topologicalKrullDim P.idealSheaf.subscheme ≤ 1 := by exact_mod_cast hdim
  refine (intersectionNumber_one_eq_invertibleCurveDegree k f _ hdim1 (L 1)).trans ?_
  change degreeOn k f (P.idealSheaf.subschemeι ≫ 𝟙 X) _ (L 1) = degreeOn k f C.ι C.dim_le (L 1)
  have hCI : Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set X)) = P.idealSheaf := by
    rw [hC, vanishingIdeal_closure_genericPoint_eq_idealSheaf]
  obtain ⟨a, ha⟩ := exists_subscheme_iso_of_eq hCI
  exact degreeOn_eq_of_iso_comp k f _ C.ι _ C.dim_le a.symm
    (by rw [Iso.symm_hom, Category.comp_id]; exact (Iso.inv_comp_eq a).2 ha.symm) (L 1)

/-- The intersection number of two invertible sheaves depends only on their isomorphism
classes. -/
private theorem intersectionNumber_two_eq_of_iso {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i] (hd : topologicalKrullDim Z ≤ (2 : ℕ))
    (L M : Fin 2 → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)]
    (e : ∀ q, Nonempty (L q ≅ M q)) :
    intersectionNumber k f i 2 hd L = intersectionNumber k f i 2 hd M := by
  let N : Fin 2 → X.Modules := ![M 0, L 1]
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
    Fin.forall_fin_two.2
      ⟨(inferInstance : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M 0)),
        (inferInstance : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L 1))⟩
  refine (intersectionNumber_eq_of_iso_at k f i 2 hd L N 0 (fun q hq => ?_) (e 0).some).trans
    (intersectionNumber_eq_of_iso_at k f i 2 hd N M 1 (fun q hq => ?_) (e 1).some)
  · obtain rfl : q = 1 := by omega
    rfl
  · obtain rfl : q = 0 := by omega
    rfl

open Stacks.Divisors in
/-- The exceptional curve `F` of the blowup `b` of a closed point of a smooth surface: its
invertible sheaf `N` has `(N · N) = -1`, and `(b^* M · N) = 0` for every invertible `M`. -/
private theorem exists_exceptional {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (h : IsSmoothSurface sY) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ∃ F : MMP.Mori.PrimeDivisor (AlgebraicGeometry.blowUp 𝓘[y, hy]),
      F.idealSheaf = exceptionalIdeal 𝓘[y, hy] ∧
      ∃ (_ : IsEffectiveCartierDivisor F.idealSheaf),
      ∀ (_ : IsProper (blowUpToBase 𝓘[y, hy] ≫ sY))
        (hd : topologicalKrullDim (AlgebraicGeometry.blowUp 𝓘[y, hy]) ≤ (2 : ℕ)),
        (∀ (L : Fin 2 → (AlgebraicGeometry.blowUp 𝓘[y, hy]).Modules)
            [∀ t, SheafOfModules.IsInvertible (AlgebraicGeometry.blowUp 𝓘[y, hy]).presheaf
              (AlgebraicGeometry.blowUp 𝓘[y, hy]).ringCatSheaf.2 (L t)],
          (∀ t, Nonempty (L t ≅ invertibleSheaf' F.idealSheaf)) →
          intersectionNumber k (blowUpToBase 𝓘[y, hy] ≫ sY) (𝟙 _) 2 hd L = -1) ∧
        ∀ (L : Fin 2 → (AlgebraicGeometry.blowUp 𝓘[y, hy]).Modules)
            [∀ t, SheafOfModules.IsInvertible (AlgebraicGeometry.blowUp 𝓘[y, hy]).presheaf
              (AlgebraicGeometry.blowUp 𝓘[y, hy]).ringCatSheaf.2 (L t)]
          (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M],
          Nonempty (L 0 ≅ (Scheme.Modules.pullback (blowUpToBase 𝓘[y, hy])).obj M) →
          Nonempty (L 1 ≅ invertibleSheaf' F.idealSheaf) →
          intersectionNumber k (blowUpToBase 𝓘[y, hy] ≫ sY) (𝟙 _) 2 hd L = 0 := by
  obtain ⟨-, -, -, -, F, hF, -, hpc, hself⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection h.variety h.smooth
      h.dim hy
  have hsm := isSmoothScheme_blowUp_singleton h.variety h.smooth h.dim hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm).2
  have : LocallyOfFiniteType sY := h.variety.toLocallyOfFiniteType
  have : IsSeparated sY := h.variety.toIsSeparated
  have := (isVariety_blowUp_singleton h.variety h.dim hy).toQuasiCompact
  have hEC := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
  refine ⟨F, hF, hEC, fun _ hd => ?_⟩
  let C : ProperCurve (blowUpToBase 𝓘[y, hy] ≫ sY) := ⟨F.genericPoint, hpc⟩
  have hCc : C.IsContractedBy (blowUpToBase 𝓘[y, hy]) := by
    intro x hx
    have hxF : x ∈ F.support := by
      rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hηF : F.genericPoint ∈ F.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    rw [(mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF x).1 hxF,
      (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF _).1 hηF]
  refine ⟨fun L _ hL => ?_, fun L _ M _ h0 h1 => ?_⟩
  · rw [intersectionNumber_two_eq_degree _ hd L F C rfl (hL 0).some]
    have h1 := intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsm F C
    rw [hself C rfl] at h1
    have h2 : ((C.degree k (invertibleSheaf' F.idealSheaf :
        (AlgebraicGeometry.blowUp 𝓘[y, hy]).Modules) : ℤ) : ℚ) = -1 := h1.symm
    have h3 : C.degree k (L 1) = C.degree k (invertibleSheaf' F.idealSheaf :
        (AlgebraicGeometry.blowUp 𝓘[y, hy]).Modules) :=
      degreeOn_eq_of_iso k _ C.ι C.dim_le (hL 1).some
    rw [h3]
    exact_mod_cast h2
  · rw [← intersectionNumber_comp_perm k _ _ 2 hd L (Equiv.swap 0 1)]
    have e0 : L (Equiv.swap (0 : Fin 2) 1 0) ≅ invertibleSheaf F.idealSheaf :=
      eqToIso (congrArg L (Equiv.swap_apply_left 0 1)) ≪≫ h1.some
    rw [intersectionNumber_two_eq_degree _ hd _ F C rfl e0]
    have h3 : C.degree k (L (Equiv.swap (0 : Fin 2) 1 1)) =
        C.degree k ((Scheme.Modules.pullback (blowUpToBase 𝓘[y, hy])).obj M) :=
      degreeOn_eq_of_iso k _ C.ι C.dim_le
        (eqToIso (congrArg L (Equiv.swap_apply_right 0 1)) ≪≫ h0.some)
    rw [h3]
    exact C.degree_pullback_eq_zero_of_isContractedBy (blowUpToBase 𝓘[y, hy]) rfl hCc M

/-- A dominant morphism inducing an isomorphism of function fields has degree one. -/
private theorem degreeOver_eq_one_of_bijective {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (g : T ⟶ B) [LocallyOfFiniteType g] [IsDominant g]
    (hbij : Function.Bijective (dominantFunctionFieldMap g)) : degreeOver g = 1 := by
  letI : Algebra B.functionField T.functionField := (dominantFunctionFieldMap g).toAlgebra
  rw [degreeOver_eq_finrank g rfl,
    ← (AlgEquiv.ofBijective (Algebra.ofId B.functionField T.functionField)
      hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **Projection formula along a birational morphism of surfaces.** For a proper dominant
morphism `g : T ⟶ B` of integral proper `k`-schemes of dimension two inducing an isomorphism of
function fields, `(M₁ · M₂) = (L₁ · L₂)` whenever `M_j ≅ g^* L_j`. -/
private theorem intersectionNumber_pullback_of_bijective {T B : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) (sB : B ⟶ Spec (.of k)) [IsProper sT] [IsProper sB] [IsIntegral T]
    [IsIntegral B] (g : T ⟶ B) (hg : g ≫ sB = sT) [IsDominant g]
    (hbij : Function.Bijective (dominantFunctionFieldMap g))
    (hT : topologicalKrullDim T = (2 : ℕ)) (hB : topologicalKrullDim B = (2 : ℕ))
    (L : Fin 2 → B.Modules) [∀ j, SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 (L j)]
    (M : Fin 2 → T.Modules) [∀ j, SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 (M j)]
    (hM : ∀ j, Nonempty (M j ≅ (Scheme.Modules.pullback g).obj (L j))) :
    intersectionNumber k sT (𝟙 T) 2 hT.le M = intersectionNumber k sB (𝟙 B) 2 hB.le L := by
  rw [intersectionNumber_two_eq_of_iso sT (𝟙 T) hT.le M _ hM]
  haveI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  subst hg
  haveI : IsProper g := IsProper.of_comp g sB
  haveI : Surjective g := ⟨by
    rw [← Set.range_eq_univ, ← g.isClosedMap.isClosed_range.closure_eq]
    exact g.denseRange.closure_range⟩
  haveI : Surjective (𝟙 T ≫ g) := by rw [Category.id_comp]; infer_instance
  haveI : Surjective (𝟙 T ≫ g).imageι := surjective_imageι (𝟙 T ≫ g)
  haveI : IsIso (𝟙 T ≫ g).imageι :=
    isIso_of_isClosedImmersion_of_surjective (𝟙 T ≫ g).imageι
  haveI : IsIntegral (𝟙 T ≫ g).image := Stacks.Chow.isIntegral_image (𝟙 T ≫ g)
  haveI : IsProper (𝟙 T ≫ g).toImage := Stacks.Chow.isProper_toImage (𝟙 T ≫ g)
  have hIm : topologicalKrullDim (𝟙 T ≫ g).image = (2 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq (𝟙 T ≫ g).imageι
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(𝟙 T ≫ g).imageι.isEmbedding, (𝟙 T ≫ g).imageι.surjective⟩)).trans hB
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k (g ≫ sB) sB g rfl (𝟙 T) 2 hT
    L hIm
  have hdeg : degreeOver g = degreeOver (𝟙 T ≫ g).toImage :=
    degreeOver_eq_degreeOver_of_isIso g (𝟙 T ≫ g).toImage (𝟙 T ≫ g).imageι
      ((𝟙 T ≫ g).toImage_imageι.trans (Category.id_comp g))
  have hint : intersectionNumber k sB (𝟙 T ≫ g).imageι 2 hIm.le L =
      intersectionNumber k sB (𝟙 B) 2 hB.le L :=
    intersectionNumber_eq_intersectionNumber_id k sB (𝟙 T ≫ g).imageι 2 hIm.le hB.le _
  rw [hpull, ← hdeg, degreeOver_eq_one_of_bijective g hbij, hint]
  simp

open Stacks.Divisors in
/-- **The total transform is the pull-back.** For a dominant morphism `g : T ⟶ B` of normal
locally Noetherian schemes, `T` integral and quasi-compact, and a prime divisor `F` of `B` with
invertible ideal sheaf, the divisorial part of the inverse image ideal `g^{-1} I_F · 𝒪_T` is the
pull-back `g^* F` of the Cartier divisor `F`. -/
private theorem divisorialPart_comap_eq_pullback {T B : Scheme.{u}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] (g : T ⟶ B) [IsDominant g] (F : MMP.Mori.PrimeDivisor B)
    (hF : IsEffectiveCartierDivisor F.idealSheaf)
    (hFc : MMP.Mori.Divisor.IsCartier (Finsupp.single F 1 : MMP.Mori.Divisor B)) :
    MMP.Resolution.divisorialPart (F.idealSheaf.comap g) =
      MMP.Mori.Divisor.pullback (Finsupp.single F 1 : MMP.Mori.Divisor B) hFc
        (map_componentGenericPoint_notMem_supp_of_isDominant' g _) := by
  classical
  haveI : IsNoetherian T := ⟨⟩
  set J := F.idealSheaf.comap g
  have hη : genericPoint T ∉ (J.support : Set T) := by
    rw [Scheme.IdealSheafData.support_comap]
    intro h
    change g (genericPoint T) ∈ (F.support : Set B) at h
    rw [map_genericPoint_of_isDominant] at h
    exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support F h
  symm
  ext E
  obtain ⟨n, hn, hc⟩ := coeff_isPullback_single_eq_idealOrder F hF
    (MMP.Mori.Divisor.isPullback_pullback hFc
      (map_componentGenericPoint_notMem_supp_of_isDominant' g _)) E
  refine hc.trans ?_
  change (n : ℤ) = MMP.Resolution.divisorialPart J E
  rw [MMP.Resolution.divisorialPart_apply]
  unfold MMP.Resolution.divisorialPartCoeff
  split_ifs with hcomp
  · simp [MMP.Resolution.multAt, J, hn]
  · by_contra hn0
    have hn0' : n ≠ 0 := by exact_mod_cast fun h => hn0 (by simp [h])
    apply hcomp
    have hEJ : E.genericPoint ∈ (J.support : Set T) := by
      by_contra hnot
      rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hnot,
        idealOrder_top] at hn
      exact hn0' (by exact_mod_cast hn.symm)
    have hsupp : (E.support : Set T) = closure {E.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    refine ⟨⟨?_, ?_⟩, fun W hW hEW => ?_⟩
    · rw [hsupp]
      exact isIrreducible_singleton.closure
    · rw [hsupp]
      exact J.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hEJ)
    · obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (closure W) :=
        ⟨_, hW.1.isGenericPoint_genericPoint_closure⟩
      have hWcl : closure W ⊆ (J.support : Set T) := J.support.isClosed.closure_subset_iff.2 hW.2
      have hηE : E.genericPoint ∈ closure W := subset_closure (hEW (by
        rw [hsupp]; exact subset_closure rfl))
      rw [← hξ.def] at hηE
      have hle : E.genericPoint ≤ ξ := specializes_iff_mem_closure.mpr hηE
      by_cases heq : ξ = E.genericPoint
      · intro w hw
        have : w ∈ closure W := subset_closure hw
        rwa [← hξ.def, heq, ← hsupp] at this
      · exfalso
        have hlt : E.genericPoint < ξ := lt_of_le_not_ge hle fun h =>
          heq (Specializes.antisymm (show ξ ⤳ E.genericPoint from hle)
            (show E.genericPoint ⤳ ξ from h)).eq
        have h2 := Order.coheight_add_one_le hlt
        rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
        have h0 : Order.coheight ξ = 0 := by
          by_contra hne
          have : 1 ≤ Order.coheight ξ := ENat.one_le_iff_ne_zero.2 hne
          have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
          norm_num at h3
        have hmax := Order.coheight_eq_zero.1 h0
        have hgT : genericPoint T ≤ ξ :=
          hmax ((genericPoint_spec T).specializes (Set.mem_univ ξ))
        refine hη (hWcl ?_)
        rw [← hξ.def]
        exact specializes_iff_mem_closure.mp hgT

section Tower

/-- The composite `S b ⟶ S a` of a tower of morphisms, for `a ≤ b`. -/
private def tw {S : ℕ → Scheme.{u}} (σ : ∀ i, S (i + 1) ⟶ S i) {a b : ℕ} (h : a ≤ b) :
    S b ⟶ S a :=
  (Functor.ofOpSequence σ).map (homOfLE h).op

variable {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {n : ℕ} {S : ℕ → Scheme.{u}}
  {σ : ∀ i, S (i + 1) ⟶ S i} {e : S 0 ≅ X} {p : ∀ j : Fin n, S j}
  {hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j))}

/-- The composite over an empty stretch of the tower is the identity. -/
private theorem tw_refl (a : ℕ) : tw σ (le_refl a) = 𝟙 (S a) :=
  (Functor.ofOpSequence σ).map_id (Opposite.op a)

/-- Composites along the tower compose. -/
private theorem tw_trans {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (h : a ≤ c) :
    tw σ h = tw σ h₂ ≫ tw σ h₁ :=
  (Functor.ofOpSequence σ).map_comp (homOfLE h₂).op (homOfLE h₁).op

/-- Peeling off the last step of a composite along the tower. -/
private theorem tw_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) :
    tw σ h' = σ b ≫ tw σ h := by
  rw [tw_trans h (Nat.le_succ b) h']
  congr 1
  exact Functor.ofOpSequence_map_homOfLE_succ σ b

/-- Peeling off the first step of a composite along the tower. -/
private theorem tw_succ_left {a b : ℕ} (h : a + 1 ≤ b) (h' : a ≤ b) :
    tw σ h' = tw σ h ≫ σ a := by
  rw [tw_trans (Nat.le_succ a) h h']
  congr 1
  exact Functor.ofOpSequence_map_homOfLE_succ σ a

variable (hσ : ∀ j : Fin n, ∃ φ : S (j + 1) ≅ AlgebraicGeometry.blowUp 𝓘[p j, hp j],
  σ j = φ.hom ≫ blowUpToBase 𝓘[p j, hp j])

include hσ

/-- Every surface of a tower of point blowups of a smooth proper surface is a smooth proper
surface. -/
private theorem isSmoothSurface_tower (hX0 : IsSmoothSurface sX) :
    ∀ m ≤ n, IsSmoothSurface ((tw σ (Nat.zero_le m) ≫ e.hom) ≫ sX) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [tw_refl, Category.id_comp]
    exact hX0.of_iso e
  | succ m ih =>
    intro hm
    obtain ⟨φ, hφ⟩ := hσ ⟨m, hm⟩
    have hφ' : σ m = φ.hom ≫ blowUpToBase 𝓘[p ⟨m, hm⟩, hp ⟨m, hm⟩] := hφ
    have h := ((ih (by omega)).blowUpToBase_comp (hp ⟨m, hm⟩)).of_iso φ
    rw [tw_succ (Nat.zero_le m), hφ']
    simpa only [Category.assoc] using h

/-- The composites along a tower of point blowups of smooth surfaces are dominant and induce
isomorphisms of function fields. -/
private theorem bijective_tower
    (hS : ∀ m ≤ n, ∃ s : S m ⟶ Spec (.of k), IsSmoothSurface s) (a : ℕ) :
    ∀ b (h : a ≤ b), b ≤ n →
      ∃ (_ : IsIntegral (S b)) (_ : IsIntegral (S a)) (_ : IsDominant (tw σ h)),
        Function.Bijective (dominantFunctionFieldMap (tw σ h)) := by
  have hint : ∀ m ≤ n, IsIntegral (S m) := fun m hm =>
    (hS m hm).choose_spec.variety.toIsIntegral
  intro b h
  induction b, h using Nat.le_induction with
  | base =>
    intro ha
    have := hint a ha
    have : IsIso (tw σ (le_refl a)) := by rw [tw_refl]; infer_instance
    exact ⟨inferInstance, inferInstance, inferInstance,
      bijective_dominantFunctionFieldMap_of_isIso _⟩
  | succ b hab ih =>
    intro hb
    obtain ⟨_, _, _, hbij⟩ := ih (by omega)
    obtain ⟨φ, hφ⟩ := hσ ⟨b, hb⟩
    have hφ' : σ b = φ.hom ≫ blowUpToBase 𝓘[p ⟨b, hb⟩, hp ⟨b, hb⟩] := hφ
    have hS := (hS b (by omega)).choose_spec
    have hB := hS.blowUpToBase_comp (hp ⟨b, hb⟩)
    have : IsIntegral (S (b + 1)) := hint (b + 1) hb
    have : IsIntegral (AlgebraicGeometry.blowUp 𝓘[p ⟨b, hb⟩, hp ⟨b, hb⟩]) :=
      hB.variety.toIsIntegral
    have := isDominant_blowUpToBase_singleton hS.dim (hp ⟨b, hb⟩)
    have hbb : Function.Bijective (dominantFunctionFieldMap
        (blowUpToBase 𝓘[p ⟨b, hb⟩, hp ⟨b, hb⟩])) :=
      Stacks.Chow.bijective_dominantFunctionFieldMap_of_isBirational _
        (isBirational_blowUpToBase _
          (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hS.dim _ _))
    rw [tw_succ hab, hφ', Category.assoc]
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [Stacks.Chow.dominantFunctionFieldMap_comp, Stacks.Chow.dominantFunctionFieldMap_comp]
    exact (bijective_dominantFunctionFieldMap_of_isIso φ.hom).comp (hbb.comp hbij)

end Tower

open Stacks.Divisors in
/-- **The intersection half.** For a tower of point blowups of a smooth projective surface, the
last surface is proper, locally Noetherian, normal and of dimension at most two, the total
transforms `E_j` of the exceptional curves are Cartier, and `E_i · E_j = -δ_{ij}`.

On `B_j`, the blowup of the `j`-th point, the exceptional curve `F_j` has `F_j² = -1` and meets
every pulled-back invertible sheaf in degree zero (`exists_exceptional`). The total transform `E_j`
is the pull-back of `F_j` along `q_j : S_n ⟶ B_j` (`divisorialPart_comap_eq_pullback`), and for
`i < j` the pull-back of `F_i` to `B_j` is pulled back from `S_j`. The projection formula along the
birational `q_j` (`intersectionNumber_pullback_of_bijective`) moves both numbers to `B_j`. -/
private theorem pointBlowupTower_intersectionMatrix (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2)
    (n : ℕ) (S : ℕ → Scheme.{u}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ X)
    (p : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j)))
    (hσ : ∀ j : Fin n, ∃ φ : S (j + 1) ≅
          AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩),
        σ j = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩)) :
      let π : S n ⟶ X := (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom
      let E : Fin n → MMP.Mori.Divisor (S n) := fun j =>
        MMP.Resolution.divisorialPart
          ((Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩).comap
            ((Functor.ofOpSequence σ).map (homOfLE j.is_le').op))
      ∃ (_ : IsProper (π ≫ sX)) (_ : IsLocallyNoetherian (S n)) (_ : IsNormal (S n))
        (hd : topologicalKrullDim (S n) ≤ (2 : ℕ)) (hE : ∀ j, (E j).IsCartier),
        ∀ i j : Fin n,
          MMP.Mori.Divisor.intersectionNumberOn k (π ≫ sX) (𝟙 (S n)) 2 hd ![E i, E j]
              (Fin.forall_fin_two.2 ⟨hE i, hE j⟩) = if i = j then -1 else 0 := by
  intro π E
  obtain ⟨hXv, hXp⟩ := (MMP.Mori.isProjectiveVariety_iff k sX).1 hX
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hXp
  have hX0 : IsSmoothSurface sX := ⟨hXv, hXs, hXd, inferInstance⟩
  have hT := isSmoothSurface_tower (e := e) hσ hX0
  have hπ : π = tw σ (Nat.zero_le n) ≫ e.hom := rfl
  have hSn := hT n le_rfl
  rw [← hπ] at hSn
  have := hSn.proper
  have : IsIntegral (S n) := hSn.variety.toIsIntegral
  have := hSn.variety.toQuasiCompact
  have : CompactSpace (S n) := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hSn.smooth).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hSn.smooth).2
  have hdn : topologicalKrullDim (S n) = (2 : ℕ) := by rw [hSn.dim]; rfl
  -- the blowups `B_j` and the maps `q_j : S n ⟶ B_j`
  have hσ₀ := hσ
  choose φ hφ using hσ
  have hSj : ∀ j : Fin n, IsSmoothSurface ((tw σ (Nat.zero_le j) ≫ e.hom) ≫ sX) :=
    fun j => hT j j.is_le'
  have hBj := fun j : Fin n => (hSj j).blowUpToBase_comp (hp j)
  choose F hF hEC hnum using fun j : Fin n => exists_exceptional (hSj j) (hp j)
  let q : ∀ j : Fin n, S n ⟶ AlgebraicGeometry.blowUp 𝓘[p j, hp j] := fun j =>
    tw σ (Nat.succ_le_of_lt j.is_lt) ≫ (φ j).hom
  have hqb : ∀ j : Fin n, q j ≫ blowUpToBase 𝓘[p j, hp j] = tw σ j.is_le' := fun j => by
    simp only [q, Category.assoc, ← hφ j]
    exact (tw_succ_left _ _).symm
  have hqs : ∀ j : Fin n, q j ≫ blowUpToBase 𝓘[p j, hp j] ≫
      ((tw σ (Nat.zero_le j) ≫ e.hom) ≫ sX) = π ≫ sX := fun j => by
    rw [reassoc_of% (hqb j), hπ, ← Category.assoc, ← Category.assoc,
      ← tw_trans (Nat.zero_le j) j.is_le' (Nat.zero_le n)]
  have hSall : ∀ m ≤ n, ∃ s : S m ⟶ Spec (.of k), IsSmoothSurface s := fun m hm => ⟨_, hT m hm⟩
  have hqd : ∀ j : Fin n, ∃ (_ : IsIntegral (AlgebraicGeometry.blowUp 𝓘[p j, hp j]))
      (_ : IsDominant (q j)), Function.Bijective (dominantFunctionFieldMap (q j)) := fun j => by
    obtain ⟨_, _, _, hbij⟩ := bijective_tower hσ₀ hSall (j + 1) n (Nat.succ_le_of_lt j.is_lt) le_rfl
    have : IsIntegral (AlgebraicGeometry.blowUp 𝓘[p j, hp j]) := (hBj j).variety.toIsIntegral
    have : IsDominant (q j) := by simp only [q]; infer_instance
    refine ⟨inferInstance, inferInstance, ?_⟩
    simp only [q]
    rw [Stacks.Chow.dominantFunctionFieldMap_comp]
    exact hbij.comp (bijective_dominantFunctionFieldMap_of_isIso _)
  have hBinst := fun j : Fin n => isLocallyNoetherian_and_isNormal_of_isSmoothScheme (hBj j).smooth
  have _instLN := fun j : Fin n => (hBinst j).1
  have _instN := fun j : Fin n => (hBinst j).2
  have hFc : ∀ j : Fin n, MMP.Mori.Divisor.IsCartier
      (Finsupp.single (F j) 1 : MMP.Mori.Divisor (AlgebraicGeometry.blowUp 𝓘[p j, hp j])) :=
    fun j => MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme (hBj j).smooth (F j)
  -- the total transform `E j` is the pull-back of `F j` along `q j`
  have hEj : ∀ j : Fin n, (E j).IsCartier ∧ Nonempty ((E j).divisorialSheaf ≅
      (Scheme.Modules.pullback (q j)).obj
        (invertibleSheaf' (F j).idealSheaf : (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).Modules)) := by
    intro j
    obtain ⟨_, _, -⟩ := hqd j
    have := (hBj j).variety.toQuasiCompact
    have : CompactSpace (AlgebraicGeometry.blowUp 𝓘[p j, hp j]) :=
      QuasiCompact.compactSpace_of_compactSpace
        (blowUpToBase 𝓘[p j, hp j] ≫ (tw σ (Nat.zero_le j) ≫ e.hom) ≫ sX)
    have hc : E j = MMP.Resolution.divisorialPart ((F j).idealSheaf.comap (q j)) := by
      change MMP.Resolution.divisorialPart (𝓘[p j, hp j].comap (tw σ j.is_le')) = _
      rw [← hqb j, Scheme.IdealSheafData.comap_comp]
      change MMP.Resolution.divisorialPart ((exceptionalIdeal 𝓘[p j, hp j]).comap (q j)) = _
      rw [hF j]
    rw [hc, divisorialPart_comap_eq_pullback (q j) (F j) (hEC j) (hFc j)]
    refine ⟨(hFc j).isCartier_pullback (q j) _, ?_⟩
    obtain ⟨a⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso (hFc j) (q j)
      (map_componentGenericPoint_notMem_supp_of_isDominant' (q j) _)
    obtain ⟨b⟩ := nonempty_divisorialSheaf_single_iso_invertibleSheaf' (F j) (hEC j) (hFc j)
    exact ⟨a ≪≫ (Scheme.Modules.pullback (q j)).mapIso b⟩
  choose hE hiso using hEj
  have _instEC : ∀ j : Fin n, IsEffectiveCartierDivisor (F j).idealSheaf := hEC
  have hdB : ∀ j : Fin n,
      topologicalKrullDim (AlgebraicGeometry.blowUp 𝓘[p j, hp j]) = (2 : ℕ) := fun j => by
    rw [(hBj j).dim]; rfl
  have _instPB := fun j : Fin n => (hBj j).proper
  -- the diagonal
  have hdiag : ∀ j : Fin n,
      ∀ [∀ t, SheafOfModules.IsInvertible (S n).presheaf (S n).ringCatSheaf.2
        ((![E j, E j] t).divisorialSheaf)],
      intersectionNumber k (π ≫ sX) (𝟙 (S n)) 2 hdn.le
        (fun t => (![E j, E j] t).divisorialSheaf) = -1 := by
    intro j _
    obtain ⟨_, _, hbij⟩ := hqd j
    rw [intersectionNumber_pullback_of_bijective (π ≫ sX) _ (q j) (hqs j) hbij hdn (hdB j)
      (fun _ => (invertibleSheaf' (F j).idealSheaf :
        (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).Modules)) _
      (fun t => by fin_cases t <;> exact hiso j)]
    exact (hnum j inferInstance (hdB j).le).1 _ fun _ => ⟨Iso.refl _⟩
  -- off the diagonal
  have hoff : ∀ i j : Fin n, i < j →
      ∀ [∀ t, SheafOfModules.IsInvertible (S n).presheaf (S n).ringCatSheaf.2
        ((![E i, E j] t).divisorialSheaf)],
      intersectionNumber k (π ≫ sX) (𝟙 (S n)) 2 hdn.le
        (fun t => (![E i, E j] t).divisorialSheaf) = 0 := by
    intro i j hij _
    obtain ⟨_, _, hbij⟩ := hqd j
    have hij' : (i : ℕ) + 1 ≤ j := hij
    let r : S j ⟶ AlgebraicGeometry.blowUp 𝓘[p i, hp i] := tw σ hij' ≫ (φ i).hom
    let M : (S j).Modules := (Scheme.Modules.pullback r).obj (invertibleSheaf' (F i).idealSheaf)
    let L : Fin 2 → (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).Modules :=
      ![(Scheme.Modules.pullback (blowUpToBase 𝓘[p j, hp j])).obj M,
        invertibleSheaf' (F j).idealSheaf]
    haveI : ∀ t, SheafOfModules.IsInvertible (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).presheaf
        (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).ringCatSheaf.2 (L t) :=
      Fin.forall_fin_two.2
        ⟨(inferInstance : SheafOfModules.IsInvertible
            (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).presheaf
            (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).ringCatSheaf.2
          ((Scheme.Modules.pullback (blowUpToBase 𝓘[p j, hp j])).obj M)),
        (inferInstance : SheafOfModules.IsInvertible
            (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).presheaf
            (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).ringCatSheaf.2
          (invertibleSheaf' (F j).idealSheaf : (AlgebraicGeometry.blowUp 𝓘[p j, hp j]).Modules))⟩
    have hqi : q i = q j ≫ blowUpToBase 𝓘[p j, hp j] ≫ r := by
      rw [reassoc_of% (hqb j)]
      simp only [q, r]
      rw [← Category.assoc, ← tw_trans hij' j.is_le']
    have e0 : (E i).divisorialSheaf ≅ (Scheme.Modules.pullback (q j)).obj (L 0) :=
      (hiso i).some ≪≫ eqToIso (by rw [hqi]) ≪≫
        ((Scheme.Modules.pullbackComp (q j) (blowUpToBase 𝓘[p j, hp j] ≫ r)).app _).symm ≪≫
        (Scheme.Modules.pullback (q j)).mapIso
          ((Scheme.Modules.pullbackComp (blowUpToBase 𝓘[p j, hp j]) r).app _).symm
    rw [intersectionNumber_pullback_of_bijective (π ≫ sX) _ (q j) (hqs j) hbij hdn (hdB j) L _
      (fun t => by fin_cases t; exacts [⟨e0⟩, hiso j])]
    exact (hnum j inferInstance (hdB j).le).2 L M ⟨Iso.refl _⟩ ⟨Iso.refl _⟩
  have _instE : ∀ a b : Fin n, ∀ t, SheafOfModules.IsInvertible (S n).presheaf
      (S n).ringCatSheaf.2 ((![E a, E b] t).divisorialSheaf) := fun a b t => by
    fin_cases t
    exacts [(hE a).isInvertibleModule_divisorialSheaf, (hE b).isInvertibleModule_divisorialSheaf]
  refine ⟨inferInstance, inferInstance, inferInstance, hdn.le, hE, fun i j => ?_⟩
  unfold MMP.Mori.Divisor.intersectionNumberOn
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg hij.ne]
    exact hoff i j hij
  · rw [if_pos rfl]
    exact hdiag i
  · rw [if_neg hij.ne', ← intersectionNumber_comp_perm k _ _ 2 _ _ (Equiv.swap 0 1)]
    rw [intersectionNumber_congr_family k _ _ 2 _
      (L := fun t => (![E i, E j] (Equiv.swap 0 1 t)).divisorialSheaf)
      (M := fun t => (![E j, E i] t).divisorialSheaf) (funext fun t => by fin_cases t <;> rfl)]
    exact hoff j i hij

end IntersectionMatrix

/-- **Resolution of a rational map from a smooth projective surface by point blowups.** Let `X`
be a smooth projective surface over an algebraically closed field `k`, `Y` a projective
`k`-scheme and `f : X ⇢ Y` a rational map over `k`. There are finitely many blowups at closed
points `S_{j+1} = Bl_{p_j} S_j`, `S₀ ≅ X`, `j < n`, such that `f ∘ π` extends to a morphism
`g : Sₙ ⟶ Y` over `k`, where `π : Sₙ ⟶ X` is the composite; and the total transforms `E_j` on
`Sₙ` of the exceptional curves satisfy `E_i · E_j = -δ_{ij}`. -/
@[mmp "lem_fourfold_surface_rational_map_point_blowups"]
public theorem exists_pointBlowups_comp_eq_of_partialMap (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    (hXd : topologicalKrullDim X = 2) (hY : IsProjectiveMorphism sY)
    (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX) :
    ∃ (n : ℕ) (S : ℕ → Scheme.{u}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ X)
      (p : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j))),
      (∀ j : Fin n, ∃ φ : S (j + 1) ≅
          blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩),
        σ j = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩)) ∧
      let π : S n ⟶ X := (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom
      let E : Fin n → MMP.Mori.Divisor (S n) := fun j =>
        MMP.Resolution.divisorialPart
          ((Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩).comap
            ((Functor.ofOpSequence σ).map (homOfLE j.is_le').op))
      (∃ g : S n ⟶ Y, g ≫ sY = π ≫ sX ∧
        (π ⁻¹ᵁ f.domain).ι ≫ g = (π ∣_ f.domain) ≫ f.hom) ∧
      ∃ (_ : IsProper (π ≫ sX)) (_ : IsLocallyNoetherian (S n)) (_ : IsNormal (S n))
        (hd : topologicalKrullDim (S n) ≤ (2 : ℕ)) (hE : ∀ j, (E j).IsCartier),
        ∀ i j : Fin n,
          MMP.Mori.Divisor.intersectionNumberOn k (π ≫ sX) (𝟙 (S n)) 2 hd ![E i, E j]
              (Fin.forall_fin_two.2 ⟨hE i, hE j⟩) = if i = j then -1 else 0 := by
  obtain ⟨n, S, σ, e, p, hp, hσ, hg⟩ :=
    exists_pointBlowupTower_resolving k sX sY hX hXs hXd hY f hf
  exact ⟨n, S, σ, e, p, hp, hσ, hg,
    pointBlowupTower_intersectionMatrix k sX hX hXs hXd n S σ e p hp hσ⟩

end MMP.Fourfold

/-! ### Fields of definition of countable diagrams -/

namespace MMP.FieldOfDefinition

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

/-! ### The index of countable algebraically closed subfields -/

section Index

variable (k : Type u) [Field k] (k₁ : Subfield k)

/-- The countable algebraically closed subfields of `k` containing `k₁`, ordered by inclusion. -/
private abbrev Idx := {K : Subfield k // Countable K ∧ IsAlgClosed K ∧ k₁ ≤ K}

variable [IsAlgClosed k] [CharZero k] [Countable k₁]

variable {k k₁} in
/-- A countable family of stages, together with countably many elements of `k`, lies below a
single stage. -/
private theorem exists_le_and_mem {ι : Type*} [Countable ι] (f : ι → Idx k k₁) (T : Set k)
    (hT : T.Countable) : ∃ K : Idx k k₁, (∀ x, f x ≤ K) ∧ T ⊆ K.1 := by
  have hc : ((k₁ : Set k) ∪ (⋃ x, ((f x).1 : Set k)) ∪ T).Countable :=
    ((Set.countable_coe_iff.mp inferInstance).union
      (Set.countable_iUnion fun x => Set.countable_coe_iff.mp (f x).2.1)).union hT
  obtain ⟨K, hK, hKc, hKa⟩ := MMP.exists_countable_isAlgClosed_subfield_superset k _ hc
  refine ⟨⟨K, Set.countable_coe_iff.mpr hKc, hKa, fun y hy => hK (Or.inl (Or.inl hy))⟩,
    fun x y hy => hK (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨x, hy⟩))), fun y hy => hK (Or.inr hy)⟩

variable {k k₁} in
private theorem exists_le {ι : Type*} [Countable ι] (f : ι → Idx k k₁) :
    ∃ K : Idx k k₁, ∀ x, f x ≤ K :=
  (exists_le_and_mem f ∅ Set.countable_empty).imp fun _ h => h.1

private theorem nonempty_idx : Nonempty (Idx k k₁) :=
  ⟨(exists_le (Empty.elim : Empty → Idx k k₁)).choose⟩

variable {k k₁} in
private theorem exists_le₂ (K L : Idx k k₁) : ∃ M : Idx k k₁, K ≤ M ∧ L ≤ M := by
  obtain ⟨M, hM⟩ := exists_le (fun b : Bool => if b then K else L)
  exact ⟨M, hM true, hM false⟩

private theorem isDirected_idx : IsDirected (Idx k k₁) (· ≤ ·) :=
  ⟨exists_le₂⟩

attribute [local instance] nonempty_idx isDirected_idx

/-- The diagram of stages in `CommRingCat`. -/
private def ringDiagram : Idx k k₁ ⥤ CommRingCat.{u} where
  obj K := CommRingCat.of K.1
  map f := CommRingCat.ofHom (Subfield.inclusion (leOfHom f))

/-- The cocone on `ringDiagram` with apex `k`. -/
private def ringCocone : Cocone (ringDiagram k k₁) where
  pt := CommRingCat.of k
  ι :=
    { app K := CommRingCat.ofHom K.1.subtype
      naturality _ _ _ := rfl }

variable {k k₁}

private theorem exists_mem (x : k) : ∃ K : Idx k k₁, x ∈ K.1 :=
  (exists_le_and_mem (Empty.elim : Empty → Idx k k₁) {x} (Set.countable_singleton x)).imp
    fun _ h => h.2 rfl

/-- The value of the universal map at an element, through some stage containing it. -/
private def liftFun (s : Cocone (ringDiagram k k₁)) (x : k) : s.pt :=
  s.ι.app (exists_mem (k₁ := k₁) x).choose ⟨x, (exists_mem x).choose_spec⟩

private theorem liftFun_eq (s : Cocone (ringDiagram k k₁)) {K : Idx k k₁} {x : k}
    (hx : x ∈ K.1) : liftFun s x = s.ι.app K ⟨x, hx⟩ := by
  obtain ⟨M, hKM, hLM⟩ := exists_le₂ (exists_mem (k₁ := k₁) x).choose K
  exact (ConcreteCategory.congr_hom (s.w (homOfLE hKM)) _).symm.trans
    (ConcreteCategory.congr_hom (s.w (homOfLE hLM)) ⟨x, hx⟩)

private theorem exists_mem₂ (x y : k) : ∃ K : Idx k k₁, x ∈ K.1 ∧ y ∈ K.1 := by
  obtain ⟨K, hK⟩ := exists_mem (k₁ := k₁) x
  obtain ⟨L, hL⟩ := exists_mem (k₁ := k₁) y
  obtain ⟨M, hKM, hLM⟩ := exists_le₂ K L
  exact ⟨M, hKM hK, hLM hL⟩

/-- The universal ring map out of `k`. -/
private def liftHom (s : Cocone (ringDiagram k k₁)) : k →+* s.pt where
  toFun := liftFun s
  map_one' := by
    obtain ⟨K⟩ := nonempty_idx k k₁
    rw [liftFun_eq s (K := K) (one_mem _)]
    exact (s.ι.app K).hom.map_one
  map_mul' x y := by
    obtain ⟨K, hx, hy⟩ := exists_mem₂ (k₁ := k₁) x y
    rw [liftFun_eq s (mul_mem hx hy), liftFun_eq s hx, liftFun_eq s hy]
    exact (s.ι.app K).hom.map_mul ⟨x, hx⟩ ⟨y, hy⟩
  map_zero' := by
    obtain ⟨K⟩ := nonempty_idx k k₁
    rw [liftFun_eq s (K := K) (zero_mem _)]
    exact (s.ι.app K).hom.map_zero
  map_add' x y := by
    obtain ⟨K, hx, hy⟩ := exists_mem₂ (k₁ := k₁) x y
    rw [liftFun_eq s (add_mem hx hy), liftFun_eq s hx, liftFun_eq s hy]
    exact (s.ι.app K).hom.map_add ⟨x, hx⟩ ⟨y, hy⟩

variable (k k₁)

/-- `k` is the filtered colimit of the stages. -/
private def isColimitRingCocone : IsColimit (ringCocone k k₁) where
  desc s := CommRingCat.ofHom (liftHom s)
  fac s K := by
    ext x
    exact liftFun_eq s x.2
  uniq s m hm := by
    ext (x : k)
    obtain ⟨K, hx⟩ := exists_mem (k₁ := k₁) x
    have h := ConcreteCategory.congr_hom (hm K) ⟨x, hx⟩
    exact h.trans (liftFun_eq s hx).symm

/-- The cofiltered diagram of the spectra of the stages. -/
private def specDiagram : (Idx k k₁)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram k k₁).op ⋙ Scheme.Spec

/-- The cone on `specDiagram` with apex `Spec k`. -/
private def specCone : Cone (specDiagram k k₁) :=
  Scheme.Spec.mapCone (ringCocone k k₁).op

/-- `Spec k` is the limit of the spectra of the stages. -/
private def isLimitSpecCone : IsLimit (specCone k k₁) :=
  isLimitOfPreserves Scheme.Spec (isColimitRingCocone k k₁).op

private theorem specDiagram_obj (K : (Idx k k₁)ᵒᵖ) :
    (specDiagram k k₁).obj K = Spec (CommRingCat.of K.unop.1) := rfl

private theorem isAffine_specDiagram_obj (K : (Idx k k₁)ᵒᵖ) :
    IsAffine ((specDiagram k k₁).obj K) := by
  rw [specDiagram_obj]; infer_instance

end Index

/-! ### Schemes of finite type over a field -/

section Fields

/-- Being quasi-compact and locally of finite type descends along an extension of fields. -/
private theorem locallyOfFiniteType_quasiCompact_of_isPullback {K L : Type u} [Field K] [Field L]
    (σ : L →+* K) {X Y : Scheme.{u}} {p : X ⟶ Y} {x : X ⟶ Spec (.of K)} {y : Y ⟶ Spec (.of L)}
    (h : IsPullback p x y (Spec.map (CommRingCat.ofHom σ))) [LocallyOfFiniteType x]
    [QuasiCompact x] : LocallyOfFiniteType y ∧ QuasiCompact y := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Spec.map (CommRingCat.ofHom σ)) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  refine ⟨MorphismProperty.of_isPullback_of_descendsAlong h.flip hQ inferInstance, ?_⟩
  have : Surjective p := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  have : CompactSpace Y := by
    have := isCompact_univ.image p.continuous
    rw [Set.image_univ_of_surjective p.surjective] at this
    exact ⟨this⟩
  exact (quasiCompact_iff_compactSpace y).mpr this

/-- A quasicoherent module of finite type on a locally Noetherian scheme is of finite
presentation. -/
private theorem isFinitePresentation_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    M.IsFinitePresentation := by
  have h := (Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X M).out 2 3
  exact h.mp ⟨inferInstance, inferInstance⟩

/-- A module of finite presentation on a locally Noetherian scheme is quasicoherent of finite
type. -/
private theorem isQuasicoherent_isFiniteType_of_isFinitePresentation {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation] :
    M.IsQuasicoherent ∧ M.IsFiniteType := by
  have h := (Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X M).out 2 3
  exact h.mpr inferInstance

/-- Finite presentation is stable under base change. -/
private theorem finitePresentation_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hf : FinitePresentation f) : FinitePresentation snd :=
  ⟨MorphismProperty.of_isPullback h hf.1, MorphismProperty.of_isPullback h hf.2.1,
    MorphismProperty.of_isPullback h hf.2.2⟩

/-- The first projection of a pullback along a morphism of finite presentation is of finite
presentation. -/
private theorem finitePresentation_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) {g : Y ⟶ Z}
    (hg : FinitePresentation g) : FinitePresentation (pullback.fst f g) :=
  finitePresentation_of_isPullback (IsPullback.of_hasPullback f g).flip hg

end Fields

/-! ### Countable families of stages of a cofiltered limit -/

section Stages

open MMP.CoefficientModels

variable {I : Type u} [SmallCategory I] [∀ i j : I, Subsingleton (i ⟶ j)]

/-- In an index category with countable lower bounds, a countable family of objects over `i₀`
has a lower bound over `i₀`. -/
private theorem exists_over_lowerBound
    (hσ : ∀ (ι : Type u) [Countable ι] (f : ι → I), ∃ i, ∀ x, Nonempty (i ⟶ f x)) {i₀ : I}
    {ι : Type u} [Countable ι] (f : ι → Over i₀) : ∃ m : Over i₀, ∀ x, Nonempty (m ⟶ f x) := by
  obtain ⟨i, hi⟩ := hσ (Option ι) (fun o => o.elim i₀ fun x => (f x).left)
  exact ⟨Over.mk (hi none).some,
    fun x => ⟨Over.homMk (hi (some x)).some (Subsingleton.elim _ _)⟩⟩

variable (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- A scheme of finite presentation over the limit has a model at some stage, recorded by a
cartesian square. -/
private theorem exists_objModel [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c)
    (X : Over c.pt) (hX : FinitePresentation X.hom) :
    ∃ (i : I) (W : Over (D.obj i)) (g : X.left ⟶ W.left),
      FinitePresentation W.hom ∧ IsPullback g X.hom W.hom (c.π.app i) := by
  have : EssentiallySmall.{u} I := essentiallySmallSelf I
  obtain ⟨i, W, hW, ⟨e⟩⟩ := LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  refine ⟨i, W, e.hom.left ≫ pullback.fst _ _, hW, ?_⟩
  have h2 : e.hom.left ≫ pullback.snd W.hom (c.π.app i) = X.hom := Over.w e.hom
  exact IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h2]⟩
    ((Over.forget _).mapIso e) rfl h2

variable {J : Type u} [SmallCategory J] (X : J ⥤ Over c.pt) {i₀ : I} (W : J → Over (D.obj i₀))
  (g : ∀ j, (X.obj j).left ⟶ (W j).left)
  (hpb : ∀ j, IsPullback (g j) (X.obj j).hom (W j).hom (c.π.app i₀))

/-- Models of the arrows of a diagram whose objects have models `W j` at the stage `i₀`: models
`H φ` of the arrows over a later stage `m₁`, recorded by their second components, and a still
later stage `m₂` from which on they respect identities and composition. -/
private structure ArrowData where
  /-- The stage over which the arrows are modelled. -/
  m₁ : Over i₀
  /-- The models of the arrows. -/
  H {j j' : J} (φ : j ⟶ j') : stageObj D (W j) m₁ ⟶ (W j').left
  H_w {j j' : J} (φ : j ⟶ j') : H φ ≫ (W j').hom = pullback.snd _ _ ≫ (W j).hom
  leg_H {j j' : J} (φ : j ⟶ j') :
    leg D (W j) c (X.obj j) (g j) (hpb j) m₁ ≫ H φ = (X.map φ).left ≫ g j'
  /-- The stage from which on the models of the arrows form a diagram. -/
  m₂ : Over i₀
  /-- The transition from `m₂` to `m₁`. -/
  b₂ : m₂ ⟶ m₁
  H_id (j : J) : stageMap D (W j) b₂ ≫ H (𝟙 j) = stageMap D (W j) b₂ ≫ pullback.snd _ _
  H_comp {j j' j'' : J} (φ : j ⟶ j') (ψ : j' ⟶ j'') :
    stageMap D (W j) b₂ ≫ stageLift (H φ) (H_w φ) (𝟙 m₁) ≫ H ψ =
      stageMap D (W j) b₂ ≫ H (φ ≫ ψ)

namespace ArrowData

variable {D c X W g hpb} (d : ArrowData D c X W g hpb)

/-- The model of the diagram at a stage `m` later than `d.m₂`. -/
private def diagram {m : Over i₀} (bm : m ⟶ d.m₂) : J ⥤ Over (D.obj m.left) where
  obj j := Over.mk (pullback.fst (D.map m.hom) (W j).hom)
  map {j j'} φ := Over.homMk (stageLift (d.H φ) (d.H_w φ) (bm ≫ d.b₂)) (stageLift_fst _ _ _)
  map_id j := by
    ext1
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [Over.homMk_left, Over.id_left, stageLift_snd, Category.id_comp, stageMap_comp,
        Category.assoc, d.H_id, stageMap_snd]
  map_comp {j j' j''} φ ψ := by
    ext1
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [Over.homMk_left, Over.comp_left, Category.assoc, stageLift_snd]
      rw [← Category.assoc (stageLift _ _ (bm ≫ d.b₂)),
        stageLift_stageMap (d.H φ) (d.H_w φ) (bm ≫ d.b₂) (𝟙 d.m₁) (bm ≫ d.b₂)
          (Category.comp_id _)]
      simp only [stageMap_comp, Category.assoc, d.H_comp]

private theorem proj_map {m : Over i₀} (bm : m ⟶ d.m₂) {j j' : J} (φ : j ⟶ j') :
    (X.map φ).left ≫ leg D (W j') c (X.obj j') (g j') (hpb j') m =
      leg D (W j) c (X.obj j) (g j) (hpb j) m ≫ ((d.diagram bm).map φ).left :=
  (leg_stageLift D (W j) c (X.obj j) (g j) (hpb j) (hpb j') (X.map φ)
    (d.H φ) (d.H_w φ) (bm ≫ d.b₂) (d.leg_H φ)).symm

end ArrowData

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **The arrows of a countable diagram with models of its objects at a stage have models**
(Stacks 01ZM (2), (3)). Arrows for which a model `ℓ x` at the stage `i₀` is prescribed are, from
the stage `m₂` on, the base changes of the prescribed models. -/
private theorem exists_arrowData (hc : IsLimit c)
    (hσ : ∀ (ι : Type u) [Countable ι] (f : ι → I), ∃ i, ∀ x, Nonempty (i ⟶ f x))
    [Countable J] [∀ j j' : J, Countable (j ⟶ j')] (hfp : ∀ j, FinitePresentation (W j).hom)
    {A : Type u} [Countable A] (a : A → Σ (j : J) (j' : J), (j ⟶ j'))
    (ℓ : ∀ x, (W (a x).1).left ⟶ (W (a x).2.1).left)
    (hℓw : ∀ x, ℓ x ≫ (W (a x).2.1).hom = (W (a x).1).hom)
    (hℓ : ∀ x, g (a x).1 ≫ ℓ x = (X.map (a x).2.2).left ≫ g (a x).2.1) :
    ∃ d : ArrowData D c X W g hpb, ∀ x, stageMap D (W (a x).1) d.b₂ ≫ d.H (a x).2.2 =
      stageMap D (W (a x).1) d.b₂ ≫ pullback.snd _ _ ≫ ℓ x := by
  classical
  -- the arrows of the diagram, and a stage at which each of them is defined
  let Arr := Σ (j : J) (j' : J), (j ⟶ j')
  have hfac : ∀ x : Arr, ∃ (m : Over i₀) (h : stageObj D (W x.1) m ⟶ (W x.2.1).left),
      leg D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) m ≫ h = (X.map x.2.2).left ≫ g x.2.1 ∧
      h ≫ (W x.2.1).hom = pullback.snd _ _ ≫ (W x.1).hom := fun x => by
    have : LocallyOfFinitePresentation (W x.2.1).hom := (hfp _).1
    refine exists_stage_hom D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) hc (hfp _) (W x.2.1) _ ?_
    rw [Category.assoc, (hpb x.2.1).w, ← Category.assoc, Over.w]
  choose mx hx hx1 hx2 using hfac
  obtain ⟨m₁, hm₁⟩ := exists_over_lowerBound hσ mx
  have b₁ : ∀ x, m₁ ⟶ mx x := fun x => (hm₁ x).some
  let H : ∀ x : Arr, stageObj D (W x.1) m₁ ⟶ (W x.2.1).left :=
    fun x => stageMap D _ (b₁ x) ≫ hx x
  have hHleg : ∀ x : Arr, leg D (W x.1) c (X.obj x.1) (g x.1) (hpb x.1) m₁ ≫ H x =
      (X.map x.2.2).left ≫ g x.2.1 := fun x => by
    simp only [H, leg_stageMap_assoc, hx1]
  have hHw : ∀ x : Arr, H x ≫ (W x.2.1).hom = pullback.snd _ _ ≫ (W x.1).hom := fun x => by
    simp only [H, Category.assoc, hx2, stageMap_snd_assoc]
  let L : ∀ (x : Arr) {m : Over i₀} (_ : m ⟶ m₁), stageObj D (W x.1) m ⟶ stageObj D (W x.2.1) m :=
    fun x _ b => stageLift (H x) (hHw x) b
  -- the identities of the diagram hold at a later stage
  have hid : ∀ j : J, ∃ (m : Over i₀) (e : m ⟶ m₁),
      stageMap D (W j) e ≫ H ⟨j, j, 𝟙 j⟩ = stageMap D (W j) e ≫ pullback.snd _ _ := fun j => by
    have : LocallyOfFinitePresentation (W j).hom := (hfp j).1
    exact exists_stage_eq D (W j) c (X.obj j) (g j) (hpb j) hc (hfp j) (W j) _ _ (hHw ⟨j, j, 𝟙 j⟩)
      rfl (by rw [hHleg ⟨j, j, 𝟙 j⟩, leg_snd]; simp)
  -- the compositions of the diagram hold at a later stage
  let Comp := Σ (j : J) (j' : J) (j'' : J), (j ⟶ j') × (j' ⟶ j'')
  have hcomp : ∀ y : Comp, ∃ (m : Over i₀) (e : m ⟶ m₁),
      stageMap D (W y.1) e ≫ L ⟨y.1, y.2.1, y.2.2.2.1⟩ (𝟙 m₁) ≫
          H ⟨y.2.1, y.2.2.1, y.2.2.2.2⟩ =
        stageMap D (W y.1) e ≫ H ⟨y.1, y.2.2.1, y.2.2.2.1 ≫ y.2.2.2.2⟩ := fun y => by
    obtain ⟨j, j', j'', φ, ψ⟩ := y
    have : LocallyOfFinitePresentation (W j'').hom := (hfp j'').1
    refine exists_stage_eq D (W j) c (X.obj j) (g j) (hpb j) hc (hfp j) (W j'') _ _ ?_
      (hHw ⟨j, j'', φ ≫ ψ⟩) ?_
    · simp only [L, Category.assoc, hHw, stageLift_snd_assoc, stageMap_id, Category.id_comp]
    · rw [← Category.assoc, leg_stageLift D (W j) c (X.obj j) (g j) (hpb j) (hpb j') (X.map φ)
        (H ⟨j, j', φ⟩) (hHw _) (𝟙 m₁) (hHleg ⟨j, j', φ⟩), Category.assoc]
      dsimp only
      rw [hHleg ⟨j', j'', ψ⟩, hHleg ⟨j, j'', φ ≫ ψ⟩]
      simp
  -- the prescribed models hold at a later stage
  have hret : ∀ x : A, ∃ (m : Over i₀) (e : m ⟶ m₁),
      stageMap D (W (a x).1) e ≫ H (a x) =
        stageMap D (W (a x).1) e ≫ pullback.snd _ _ ≫ ℓ x := fun x => by
    have : LocallyOfFinitePresentation (W (a x).2.1).hom := (hfp _).1
    refine exists_stage_eq D (W (a x).1) c (X.obj (a x).1) (g (a x).1) (hpb (a x).1) hc
      (hfp _) (W (a x).2.1) _ _ (hHw (a x)) (by rw [Category.assoc, hℓw]) ?_
    rw [hHleg, leg_snd_assoc, hℓ]
  choose mj ej hej using hid
  choose my ey hey using hcomp
  choose mr er her using hret
  obtain ⟨m₂, hm₂⟩ := exists_over_lowerBound hσ
    (fun o : Option (J ⊕ Comp ⊕ A) => o.elim m₁ fun z => z.elim mj fun z' => z'.elim my mr)
  have b₂ : m₂ ⟶ m₁ := (hm₂ none).some
  have dj : ∀ j, m₂ ⟶ mj j := fun j => (hm₂ (some (Sum.inl j))).some
  have dy : ∀ y, m₂ ⟶ my y := fun y => (hm₂ (some (Sum.inr (Sum.inl y)))).some
  have dr : ∀ x, m₂ ⟶ mr x := fun x => (hm₂ (some (Sum.inr (Sum.inr x)))).some
  let d : ArrowData D c X W g hpb :=
    { m₁ := m₁, H := fun {j j'} φ => H ⟨j, j', φ⟩, H_w := fun {j j'} φ => hHw ⟨j, j', φ⟩,
      leg_H := fun {j j'} φ => hHleg ⟨j, j', φ⟩, m₂ := m₂, b₂ := b₂,
      H_id := fun j => by
        rw [show b₂ = dj j ≫ ej j from Subsingleton.elim _ _, stageMap_comp, Category.assoc,
          Category.assoc, hej]
      H_comp := fun {j j' j''} φ ψ => by
        have := hey ⟨j, j', j'', φ, ψ⟩
        simp only [L] at this
        rw [show b₂ = dy ⟨j, j', j'', φ, ψ⟩ ≫ ey ⟨j, j', j'', φ, ψ⟩ from Subsingleton.elim _ _,
          stageMap_comp, Category.assoc, Category.assoc, this] }
  refine ⟨d, fun x => ?_⟩
  change stageMap D (W (a x).1) b₂ ≫ H (a x) =
    stageMap D (W (a x).1) b₂ ≫ pullback.snd (D.map m₁.hom) _ ≫ ℓ x
  rw [show b₂ = dr x ≫ er x from Subsingleton.elim _ _, stageMap_comp]
  simp only [Category.assoc]
  rw [her]

end Stages

/-! ### Coherence of the identifications of iterated pullbacks of modules -/

section Coherence

open MMP.CoefficientModels
open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso canHom_comp canHom_naturality canIso_hom)

/-- A morphism `φ : f^* M_t ⟶ M_s` whose canonical form, read through identifications
`M_s ≅ l_s^* N_s` and `M_t ≅ l_t^* N_t`, is the transport of `Ψ` along `p_s` is the pullback
along `p_s` of the morphism `g^* a_t^* N_t ⟶ a_s^* N_s` built from `Ψ`. -/
private theorem comp_eq_of_transport_eq {Xs Xt Ys Yt Ts Tt : Scheme.{u}} (f : Xs ⟶ Xt)
    (ps : Xs ⟶ Ys) (pt : Xt ⟶ Yt) (g : Ys ⟶ Yt) (hnat : f ≫ pt = ps ≫ g) (as : Ys ⟶ Ts)
    (at' : Yt ⟶ Tt) {ls : Xs ⟶ Ts} {lt : Xt ⟶ Tt} (hls : ps ≫ as = ls) (hlt : pt ≫ at' = lt)
    {Ms : Xs.Modules} {Mt : Xt.Modules} {Ns : Ts.Modules} {Nt : Tt.Modules}
    (θs : Ms ≅ (Scheme.Modules.pullback ls).obj Ns)
    (θt : Mt ≅ (Scheme.Modules.pullback lt).obj Nt)
    (φ : (Scheme.Modules.pullback f).obj Mt ⟶ Ms)
    (Ψ : (Scheme.Modules.pullback (g ≫ at')).obj Nt ⟶ (Scheme.Modules.pullback as).obj Ns)
    (h₁ : ps ≫ g ≫ at' = f ≫ lt)
    (hΨ : transport ps h₁ hls Ψ = (canIso f lt (f ≫ lt) rfl Nt).inv ≫
      (Scheme.Modules.pullback f).map θt.inv ≫ φ ≫ θs.hom) :
    φ ≫ (θs ≪≫ (canIso ps as ls hls Ns).symm).hom =
      (Scheme.Modules.pullback f).map (θt ≪≫ (canIso pt at' lt hlt Nt).symm).hom ≫
        ((Scheme.Modules.pullbackComp f pt).hom.app _ ≫
          (Scheme.Modules.pullbackCongr hnat).hom.app _ ≫
          (Scheme.Modules.pullbackComp ps g).inv.app _) ≫
        (Scheme.Modules.pullback ps).map (canHom g at' (g ≫ at') rfl Nt ≫ Ψ) := by
  have ht : (ps ≫ g) ≫ at' = f ≫ lt := by rw [Category.assoc, h₁]
  -- `φ` in terms of `Ψ`
  have hφ : φ ≫ θs.hom = (Scheme.Modules.pullback f).map θt.hom ≫
      canHom f lt (f ≫ lt) rfl Nt ≫ transport ps h₁ hls Ψ := by
    rw [hΨ]
    simp [← canIso_hom]
  have htr : transport ps h₁ hls Ψ ≫ (canIso ps as ls hls Ns).inv =
      (canIso ps (g ≫ at') (f ≫ lt) h₁ Nt).inv ≫ (Scheme.Modules.pullback ps).map Ψ := by
    simp [transport, ← canIso_hom]
  -- the coherence of the canonical identifications
  have c₁ := canHom_comp f pt at' (ps ≫ g) lt (f ≫ lt) hnat hlt ht rfl Nt
  have c₂ := canHom_comp ps g at' (ps ≫ g) (g ≫ at') (f ≫ lt) rfl rfl ht h₁ Nt
  have hcoh : canHom f lt (f ≫ lt) rfl Nt ≫ (canIso ps (g ≫ at') (f ≫ lt) h₁ Nt).inv =
      (Scheme.Modules.pullback f).map (canIso pt at' lt hlt Nt).inv ≫
        canHom f pt (ps ≫ g) hnat _ ≫ (canIso ps g (ps ≫ g) rfl _).inv ≫
        (Scheme.Modules.pullback ps).map (canHom g at' (g ≫ at') rfl Nt) := by
    haveI : Epi ((Scheme.Modules.pullback f).map (canHom pt at' lt hlt Nt)) := IsIso.epi_of_iso _
    haveI : Mono (canHom ps (g ≫ at') (f ≫ lt) h₁ Nt) := IsIso.mono_of_iso _
    rw [← cancel_epi ((Scheme.Modules.pullback f).map (canHom pt at' lt hlt Nt)),
      ← cancel_mono (canHom ps (g ≫ at') (f ≫ lt) h₁ Nt)]
    simp only [Category.assoc, ← canIso_hom, Iso.inv_hom_id, Category.comp_id]
    simp only [canIso_hom]
    rw [c₁, c₂, ← Functor.map_comp_assoc]
    simp [← canIso_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hφ, htr]
  have e₁ : (Scheme.Modules.pullbackComp f pt).hom.app ((Scheme.Modules.pullback at').obj Nt) ≫
      (Scheme.Modules.pullbackCongr hnat).hom.app _ = canHom f pt (ps ≫ g) hnat _ := rfl
  have e₂ : (Scheme.Modules.pullbackComp ps g).inv.app ((Scheme.Modules.pullback at').obj Nt) =
      (canIso ps g (ps ≫ g) rfl _).inv := by
    simp [canIso, Scheme.Modules.pullbackCongr]
  rw [reassoc_of% e₁, e₂, ← reassoc_of% hcoh]

/-- The identification `M ≅ l^* N` together with `N ≅ r^* M₁`, pulled back along a stage
change `a`, gives back the identification `M ≅ ρ^* M₁`. -/
private theorem retain_eq {X Y T Z : Scheme.{u}} (p : X ⟶ Y) (a : Y ⟶ T) {l : X ⟶ T}
    (hl : p ≫ a = l) (r : T ⟶ Z) {ρY : Y ⟶ Z} (hρY : a ≫ r = ρY) {ρX : X ⟶ Z}
    (hρX : l ≫ r = ρX) (hρ : p ≫ ρY = ρX) {M : X.Modules} {N : T.Modules} {M₁ : Z.Modules}
    (θ : M ≅ (Scheme.Modules.pullback l).obj N) (γ : N ≅ (Scheme.Modules.pullback r).obj M₁)
    (α₁ : M ≅ (Scheme.Modules.pullback ρX).obj M₁)
    (hγ : θ.hom ≫ (Scheme.Modules.pullback l).map γ.hom ≫ canHom l r ρX hρX M₁ = α₁.hom) :
    (θ ≪≫ (canIso p a l hl N).symm).hom ≫
        (Scheme.Modules.pullback p).map
          (((Scheme.Modules.pullback a).mapIso γ ≪≫ canIso a r ρY hρY M₁).hom) ≫
        (Scheme.Modules.pullbackComp p ρY).hom.app M₁ ≫
        (Scheme.Modules.pullbackCongr hρ).hom.app M₁ = α₁.hom := by
  rw [← hγ]
  have hn := canHom_naturality p a l hl γ.hom
  have c := canHom_comp p a r l ρY ρX hl hρY hρX hρ M₁
  have e : (Scheme.Modules.pullbackComp p ρY).hom.app M₁ ≫
      (Scheme.Modules.pullbackCongr hρ).hom.app M₁ = canHom p ρY ρX hρ M₁ := rfl
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    canIso_hom]
  rw [e, c, ← Category.assoc ((Scheme.Modules.pullback p).map
    ((Scheme.Modules.pullback a).map γ.hom)), hn]
  simp [← canIso_hom]

end Coherence

/-! ### Models of modules and of morphisms of modules -/

section ModuleModels

open MMP.CoefficientModels

variable {I : Type u} [SmallCategory I] [∀ i j : I, Subsingleton (i ⟶ j)] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i₀ : I}

/-- **A module of finite presentation on a scheme with a model at a stage is the pullback of a
module of finite presentation on a later base change of the model** (Stacks 01ZR (1)). -/
private theorem exists_moduleModel (hc : IsLimit c) (X : Over c.pt) (W : Over (D.obj i₀))
    (g : X.left ⟶ W.left) (hpb : IsPullback g X.hom W.hom (c.π.app i₀))
    (hW : FinitePresentation W.hom) (M : X.left.Modules) [M.IsFinitePresentation] :
    ∃ (m : Over i₀) (N : (stageObj D W m).Modules), N.IsFinitePresentation ∧
      Nonempty (M ≅ (Scheme.Modules.pullback (leg D W c X g hpb m)).obj N) := by
  have {j k : Over i₀} (e : j ⟶ k) : IsAffineHom ((stageDiagram D W).map e) :=
    isAffineHom_stageMap D W e
  have (m : Over i₀) : CompactSpace ((stageDiagram D W).obj m) := compactSpace_stageObj D W hW m
  have (m : Over i₀) : QuasiSeparatedSpace ((stageDiagram D W).obj m) :=
    quasiSeparatedSpace_stageObj D W hW m
  exact @Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs
    _ _ _ (stageDiagram D W) _ (legCone D W c X g hpb) (isLimitLegCone D W c X g hpb hc) _ _ M
    ‹_›

variable {Xs Xt : Over c.pt} {Ws Wt : Over (D.obj i₀)} {gs : Xs.left ⟶ Ws.left}
  {gt : Xt.left ⟶ Wt.left} (hpbs : IsPullback gs Xs.hom Ws.hom (c.π.app i₀))
  (hpbt : IsPullback gt Xt.hom Wt.hom (c.π.app i₀)) (f : Xs ⟶ Xt) {m₁ : Over i₀}
  {H : stageObj D Ws m₁ ⟶ Wt.left} (hHw : H ≫ Wt.hom = pullback.snd _ _ ≫ Ws.hom)
  (hHleg : leg D Ws c Xs gs hpbs m₁ ≫ H = f.left ≫ gt)

include hHleg in
private theorem leg_stageLift_stageMap {m mt : Over i₀} (b : m ⟶ m₁) (bt : m ⟶ mt) :
    leg D Ws c Xs gs hpbs m ≫ stageLift H hHw b ≫ stageMap D Wt bt =
      f.left ≫ leg D Wt c Xt gt hpbt mt := by
  rw [← Category.assoc, leg_stageLift D Ws c Xs gs hpbs hpbt f H hHw b hHleg, Category.assoc,
    leg_stageMap]

/-- **A morphism between pullbacks of modules of finite presentation on stages, at the limit, is
the transport of a morphism at every sufficiently late stage** (Stacks 01ZR (2)). -/
private theorem exists_mapModel (hc : IsLimit c) (hWs : FinitePresentation Ws.hom)
    {ms mt : Over i₀} (Ns : (stageObj D Ws ms).Modules) (Nt : (stageObj D Wt mt).Modules)
    [Ns.IsFinitePresentation] [Nt.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (f.left ≫ leg D Wt c Xt gt hpbt mt)).obj Nt ⟶
      (Scheme.Modules.pullback (leg D Ws c Xs gs hpbs ms)).obj Ns) :
    ∃ k : Over i₀, ∀ (m : Over i₀) (_ : m ⟶ k) (b : m ⟶ m₁) (bs : m ⟶ ms) (bt : m ⟶ mt),
      ∃ Ψ : (Scheme.Modules.pullback (stageLift H hHw b ≫ stageMap D Wt bt)).obj Nt ⟶
          (Scheme.Modules.pullback (stageMap D Ws bs)).obj Ns,
        transport (leg D Ws c Xs gs hpbs m)
          (leg_stageLift_stageMap D c hpbs hpbt f hHw hHleg b bt)
          (leg_stageMap D Ws c Xs gs hpbs bs) Ψ = φ := by
  have {j k : Over i₀} (e : j ⟶ k) : IsAffineHom ((stageDiagram D Ws).map e) :=
    isAffineHom_stageMap D Ws e
  have (m : Over i₀) : CompactSpace ((stageDiagram D Ws).obj m) :=
    compactSpace_stageObj D Ws hWs m
  have (m : Over i₀) : QuasiSeparatedSpace ((stageDiagram D Ws).obj m) :=
    quasiSeparatedSpace_stageObj D Ws hWs m
  classical
  -- a common stage below `m₁`, `ms` and `mt`
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists ({m₁, ms, mt} : Finset (Over i₀))
  have b₀ : i ⟶ m₁ := (hi (by simp)).some
  have bs₀ : i ⟶ ms := (hi (by simp)).some
  have bt₀ : i ⟶ mt := (hi (by simp)).some
  have hA := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageLift H hHw b₀ ≫ stageMap D Wt bt₀) Nt
  have hB := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageMap D Ws bs₀) Ns
  have key : ∃ (k : Over i₀) (e : k ⟶ i)
      (Ψ : (Scheme.Modules.pullback (stageMap D Ws e ≫ stageLift H hHw b₀ ≫
          stageMap D Wt bt₀)).obj Nt ⟶
        (Scheme.Modules.pullback (stageMap D Ws e ≫ stageMap D Ws bs₀)).obj Ns),
      transport (leg D Ws c Xs gs hpbs k)
        (by rw [leg_stageMap_assoc]; exact leg_stageLift_stageMap D c hpbs hpbt f hHw hHleg b₀ bt₀)
        (by rw [leg_stageMap_assoc]; exact leg_stageMap D Ws c Xs gs hpbs bs₀) Ψ = φ := by
    obtain ⟨k, e, Ψ, hΨ⟩ := exists_transport_eq_of_isLimit (stageDiagram D Ws)
      (legCone D Ws c Xs gs hpbs) (isLimitLegCone D Ws c Xs gs hpbs hc) i
      (stageLift H hHw b₀ ≫ stageMap D Wt bt₀) (stageMap D Ws bs₀) (hA := hA) (hB := hB)
      (leg_stageLift_stageMap D c hpbs hpbt f hHw hHleg b₀ bt₀)
      (leg_stageMap D Ws c Xs gs hpbs bs₀) φ
    exact ⟨k, e, Ψ, hΨ⟩
  obtain ⟨k, e, Ψ, hΨ⟩ := key
  refine ⟨k, fun m ek b bs bt => ?_⟩
  have h₁ : stageMap D Ws ek ≫ stageMap D Ws e ≫ stageLift H hHw b₀ ≫ stageMap D Wt bt₀ =
      stageLift H hHw b ≫ stageMap D Wt bt := by
    rw [← Category.assoc, ← stageMap_comp, ← Category.assoc,
      ← stageLift_stageMap H hHw (ek ≫ e) b₀ b (Subsingleton.elim _ _), Category.assoc,
      ← stageMap_comp]
    exact congrArg (_ ≫ ·) (congrArg _ (Subsingleton.elim _ _))
  have h₂ : stageMap D Ws ek ≫ stageMap D Ws e ≫ stageMap D Ws bs₀ = stageMap D Ws bs := by
    rw [← stageMap_comp, ← stageMap_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  refine ⟨transport (stageMap D Ws ek) h₁ h₂ Ψ, ?_⟩
  rw [transport_transport, ← hΨ]
  · exact transport_congr (leg_stageMap D Ws c Xs gs hpbs ek) _ _ _ _ _
  · rw [leg_stageMap, leg_stageMap_assoc]
    exact leg_stageLift_stageMap D c hpbs hpbt f hHw hHleg b₀ bt₀
  · rw [leg_stageMap, leg_stageMap_assoc]
    exact leg_stageMap D Ws c Xs gs hpbs bs₀

end ModuleModels

/-! ### Models of a countable diagram over a cofiltered limit -/

section Assembly

open MMP.CoefficientModels
open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso)

variable {I : Type u} [SmallCategory I] [∀ i j : I, Subsingleton (i ⟶ j)] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **A countable diagram of schemes of finite presentation over the limit of a cofiltered system
with countable lower bounds, with countably many modules of finite presentation and morphisms
between their pullbacks, has a model at some stage.** On a part of the diagram prescribed as the
base change of a diagram `G` along maps `r i` of the stages to a scheme `B`, and on a part of the
modules prescribed as pullbacks of modules on `G`, the model is the base change of the
prescribed one. -/
private theorem exists_stage_model [∀ i, IsLocallyNoetherian (D.obj i)] (hc : IsLimit c)
    (hσ : ∀ (ι : Type u) [Countable ι] (f : ι → I), ∃ i, ∀ x, Nonempty (i ⟶ f x))
    {B : Scheme.{u}} (r : ∀ i, D.obj i ⟶ B) (hr : ∀ {i j : I} (e : i ⟶ j), D.map e ≫ r j = r i)
    (ι₁ : c.pt ⟶ B) (hι₁ : ∀ i, c.π.app i ≫ r i = ι₁)
    {J : Type u} [SmallCategory J] [Countable J] [∀ j j' : J, Countable (j ⟶ j')]
    (F : J ⥤ Over c.pt) (hF : ∀ j, FinitePresentation (F.obj j).hom)
    {S : Type u} [Countable S] (σ : S → J) (M : ∀ s, (F.obj (σ s)).left.Modules)
    [∀ s, (M s).IsFinitePresentation]
    {H : Type u} [Countable H] (src tgt : H → S) (u : ∀ h, σ (src h) ⟶ σ (tgt h))
    (φ : ∀ h, (Scheme.Modules.pullback (F.map (u h)).left).obj (M (tgt h)) ⟶ M (src h))
    (P : ObjectProperty J) (G : P.FullSubcategory ⥤ Over B)
    (hG : ∀ j, FinitePresentation (G.obj j).hom)
    (ρ₁ : P.ι ⋙ F ⋙ Over.map ι₁ ⟶ G)
    (hρ₁ : ∀ j, IsPullback (ρ₁.app j).left (F.obj j.obj).hom (G.obj j).hom ι₁)
    (Q : S → Prop) (hQ : ∀ s, Q s → P (σ s))
    (M₁ : ∀ s (hs : Q s), (G.obj ⟨σ s, hQ s hs⟩).left.Modules)
    [∀ s (hs : Q s), (M₁ s hs).IsFinitePresentation]
    (α₁ : ∀ s (hs : Q s),
      M s ≅ (Scheme.Modules.pullback (ρ₁.app ⟨σ s, hQ s hs⟩).left).obj (M₁ s hs)) :
    ∃ (i : I) (F₀ : J ⥤ Over (D.obj i)) (π : F ⋙ Over.map (c.π.app i) ⟶ F₀)
      (M₀ : ∀ s, (F₀.obj (σ s)).left.Modules)
      (α : ∀ s, M s ≅ (Scheme.Modules.pullback (π.app (σ s)).left).obj (M₀ s))
      (φ₀ : ∀ h, (Scheme.Modules.pullback (F₀.map (u h)).left).obj (M₀ (tgt h)) ⟶ M₀ (src h))
      (ρ₀ : P.ι ⋙ F₀ ⋙ Over.map (r i) ⟶ G)
      (hρ : ∀ j, (π.app j.obj).left ≫ (ρ₀.app j).left = (ρ₁.app j).left)
      (β : ∀ s (hs : Q s),
        M₀ s ≅ (Scheme.Modules.pullback (ρ₀.app ⟨σ s, hQ s hs⟩).left).obj (M₁ s hs)),
      (∀ j, LocallyOfFiniteType (F₀.obj j).hom ∧ QuasiCompact (F₀.obj j).hom) ∧
      (∀ j, IsPullback (π.app j).left (F.obj j).hom (F₀.obj j).hom (c.π.app i)) ∧
      (∀ s, (M₀ s).IsQuasicoherent ∧ (M₀ s).IsFiniteType) ∧
      (∀ h, φ h ≫ (α (src h)).hom =
        (Scheme.Modules.pullback (F.map (u h)).left).map (α (tgt h)).hom ≫
          ((Scheme.Modules.pullbackComp (F.map (u h)).left (π.app (σ (tgt h))).left).hom.app
              (M₀ (tgt h)) ≫
            (Scheme.Modules.pullbackCongr
                (congrArg CommaMorphism.left (π.naturality (u h)))).hom.app (M₀ (tgt h)) ≫
            (Scheme.Modules.pullbackComp (π.app (σ (src h))).left
                (F₀.map (u h)).left).inv.app (M₀ (tgt h))) ≫
          (Scheme.Modules.pullback (π.app (σ (src h))).left).map (φ₀ h)) ∧
      (∀ j, IsPullback (ρ₀.app j).left (F₀.obj j.obj).hom (G.obj j).hom (r i)) ∧
      (∀ s (hs : Q s), (α s).hom ≫
        (Scheme.Modules.pullback (π.app (σ s)).left).map (β s hs).hom ≫
          (Scheme.Modules.pullbackComp (π.app (σ s)).left
              (ρ₀.app ⟨σ s, hQ s hs⟩).left).hom.app (M₁ s hs) ≫
          (Scheme.Modules.pullbackCongr (hρ ⟨σ s, hQ s hs⟩)).hom.app (M₁ s hs) =
        (α₁ s hs).hom) := by
  classical
  -- Step 1: models of the objects, the prescribed ones on `P`
  have hobj : ∀ j, ∃ (i : I) (W : Over (D.obj i)) (g : (F.obj j).left ⟶ W.left),
      FinitePresentation W.hom ∧ IsPullback g (F.obj j).hom W.hom (c.π.app i) ∧
      ∀ hj : P j, ∃ ψ : W.left ⟶ (G.obj ⟨j, hj⟩).left,
        IsPullback ψ W.hom (G.obj ⟨j, hj⟩).hom (r i) ∧ g ≫ ψ = (ρ₁.app ⟨j, hj⟩).left := by
    intro j
    by_cases hj : P j
    · obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      let Gj := G.obj ⟨j, hj⟩
      have hw : (ρ₁.app ⟨j, hj⟩).left ≫ Gj.hom = ((F.obj j).hom ≫ c.π.app i) ≫ r i := by
        rw [Over.w (ρ₁.app ⟨j, hj⟩), Category.assoc, hι₁]
        rfl
      refine ⟨i, Over.mk (pullback.snd Gj.hom (r i)), pullback.lift _ _ hw,
        finitePresentation_of_isPullback (IsPullback.of_hasPullback Gj.hom (r i)) (hG _), ?_,
        fun hj' =>
          ⟨pullback.fst _ _, IsPullback.of_hasPullback Gj.hom (r i), pullback.lift_fst _ _ _⟩⟩
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback Gj.hom (r i))
      rw [pullback.lift_fst, hι₁]
      exact hρ₁ ⟨j, hj⟩
    · obtain ⟨i, W, g, hW, hpb⟩ := exists_objModel D c hc (F.obj j) (hF j)
      exact ⟨i, W, g, hW, hpb, fun hj' => absurd hj' hj⟩
  choose i' W' g' hW' hpb' hret' using hobj
  -- Step 2: a common stage for the objects
  obtain ⟨i₀, hi₀⟩ := hσ J i'
  have e : ∀ j, i₀ ⟶ i' j := fun j => (hi₀ j).some
  let W : J → Over (D.obj i₀) := fun j => Over.mk (pullback.fst (D.map (e j)) (W' j).hom)
  let g : ∀ j, (F.obj j).left ⟶ (W j).left := fun j =>
    leg D (W' j) c (F.obj j) (g' j) (hpb' j) (Over.mk (e j))
  have hpb : ∀ j, IsPullback (g j) (F.obj j).hom (W j).hom (c.π.app i₀) := fun j =>
    isPullback_leg D (W' j) c (F.obj j) (g' j) (hpb' j) (Over.mk (e j))
  have hfp : ∀ j, FinitePresentation (W j).hom := fun j =>
    finitePresentation_pullback_fst _ (hW' j)
  have hret : ∀ j (hj : P j), ∃ ψ : (W j).left ⟶ (G.obj ⟨j, hj⟩).left,
      IsPullback ψ (W j).hom (G.obj ⟨j, hj⟩).hom (r i₀) ∧ g j ≫ ψ = (ρ₁.app ⟨j, hj⟩).left := by
    intro j hj
    obtain ⟨ψ, hψ, hgψ⟩ := hret' j hj
    refine ⟨pullback.snd _ _ ≫ ψ, ?_, ?_⟩
    · have := (IsPullback.of_hasPullback (D.map (e j)) (W' j).hom).flip.paste_horiz hψ
      rwa [hr] at this
    · exact (leg_snd_assoc D (W' j) c (F.obj j) (g' j) (hpb' j) (Over.mk (e j)) ψ).trans hgψ
  choose ψ hψpb hψ using hret
  -- Step 3: models of the arrows; on `P` they are the base changes of the arrows of `G`
  let A := {x : Σ (j : J) (j' : J), (j ⟶ j') // P x.1 ∧ P x.2.1}
  let a : A → Σ (j : J) (j' : J), (j ⟶ j') := Subtype.val
  have hℓ' : ∀ x : A, (ψ (a x).1 x.2.1 ≫
      (G.map (ObjectProperty.homMk (a x).2.2 :
        (⟨_, x.2.1⟩ : P.FullSubcategory) ⟶ ⟨_, x.2.2⟩)).left) ≫
        (G.obj ⟨_, x.2.2⟩).hom = (W (a x).1).hom ≫ r i₀ := fun x => by
    rw [Category.assoc, Over.w, (hψpb _ _).w]
  let ℓ : ∀ x : A, (W (a x).1).left ⟶ (W (a x).2.1).left := fun x =>
    (hψpb _ x.2.2).lift (ψ (a x).1 x.2.1 ≫
      (G.map (ObjectProperty.homMk (a x).2.2 :
        (⟨_, x.2.1⟩ : P.FullSubcategory) ⟶ ⟨_, x.2.2⟩)).left)
      (W (a x).1).hom (hℓ' x)
  have hℓw : ∀ x : A, ℓ x ≫ (W (a x).2.1).hom = (W (a x).1).hom := fun x =>
    (hψpb _ x.2.2).lift_snd _ _ _
  have hℓψ : ∀ x : A, ℓ x ≫ ψ (a x).2.1 x.2.2 = ψ (a x).1 x.2.1 ≫
      (G.map (ObjectProperty.homMk (a x).2.2 :
        (⟨_, x.2.1⟩ : P.FullSubcategory) ⟶ ⟨_, x.2.2⟩)).left :=
    fun x => (hψpb _ x.2.2).lift_fst _ _ _
  have hℓ : ∀ x : A, g (a x).1 ≫ ℓ x = (F.map (a x).2.2).left ≫ g (a x).2.1 := fun x => by
    refine (hψpb _ x.2.2).hom_ext ?_ ?_
    · rw [Category.assoc, hℓψ, ← Category.assoc, hψ, Category.assoc, hψ]
      exact (congrArg CommaMorphism.left (ρ₁.naturality
        (ObjectProperty.homMk (a x).2.2 : (⟨_, x.2.1⟩ : P.FullSubcategory) ⟶ ⟨_, x.2.2⟩))).symm
    · rw [Category.assoc, hℓw, Category.assoc, (hpb _).w, (hpb _).w, ← Category.assoc,
        Over.w (F.map (a x).2.2)]
  obtain ⟨d, hd⟩ := exists_arrowData D c F W g hpb hc hσ hfp a ℓ hℓw hℓ
  -- Step 4: models of the modules, the prescribed ones on `Q`
  have hlegψ : ∀ s (hs : Q s), leg D (W (σ s)) c (F.obj (σ s)) (g _) (hpb _) d.m₂ ≫
      pullback.snd _ _ ≫ ψ (σ s) (hQ s hs) = (ρ₁.app ⟨σ s, hQ s hs⟩).left := fun s hs => by
    rw [leg_snd_assoc, hψ]
  have hmod : ∀ s, ∃ (m : Over i₀) (N : (stageObj D (W (σ s)) m).Modules)
      (θ : M s ≅ (Scheme.Modules.pullback
        (leg D (W (σ s)) c (F.obj (σ s)) (g _) (hpb _) m)).obj N),
      N.IsFinitePresentation ∧ ∀ hs : Q s, ∃ (r' : stageObj D (W (σ s)) m ⟶
          (G.obj ⟨σ s, hQ s hs⟩).left)
        (hr' : leg D (W (σ s)) c (F.obj (σ s)) (g _) (hpb _) m ≫ r' =
          (ρ₁.app ⟨σ s, hQ s hs⟩).left)
        (γ : N ≅ (Scheme.Modules.pullback r').obj (M₁ s hs)),
        r' = pullback.snd _ _ ≫ ψ (σ s) (hQ s hs) ∧
        θ.hom ≫ (Scheme.Modules.pullback _).map γ.hom ≫ canHom _ r' _ hr' (M₁ s hs) =
          (α₁ s hs).hom := by
    intro s
    by_cases hs : Q s
    · refine ⟨d.m₂, (Scheme.Modules.pullback (pullback.snd _ _ ≫ ψ (σ s) (hQ s hs))).obj
        (M₁ s hs), α₁ s hs ≪≫ (canIso _ _ _ (hlegψ s hs) (M₁ s hs)).symm,
        Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ _,
        fun hs' => ⟨_, hlegψ s hs', Iso.refl _, rfl, ?_⟩⟩
      simp [← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]
    · obtain ⟨m, N, hN, ⟨θ⟩⟩ := exists_moduleModel D c hc (F.obj (σ s)) (W (σ s)) (g _) (hpb _)
        (hfp _) (M s)
      exact ⟨m, N, θ, hN, fun hs' => absurd hs' hs⟩
  choose ms N θ hNfp hNret using hmod
  -- Step 5: models of the morphisms of modules
  have hmap : ∀ h : H, ∃ k : Over i₀, ∀ (m : Over i₀) (_ : m ⟶ k) (b : m ⟶ d.m₁)
      (bs : m ⟶ ms (src h)) (bt : m ⟶ ms (tgt h)),
      ∃ Ψ : (Scheme.Modules.pullback (stageLift (d.H (u h)) (d.H_w (u h)) b ≫
          stageMap D (W (σ (tgt h))) bt)).obj (N (tgt h)) ⟶
          (Scheme.Modules.pullback (stageMap D (W (σ (src h))) bs)).obj (N (src h)),
        transport (leg D (W (σ (src h))) c (F.obj _) (g _) (hpb _) m)
          (leg_stageLift_stageMap D c (hpb _) (hpb _) (F.map (u h)) (d.H_w (u h))
            (d.leg_H (u h)) b bt)
          (leg_stageMap D _ c _ _ (hpb _) bs) Ψ =
          (canIso (F.map (u h)).left (leg D (W (σ (tgt h))) c (F.obj _) (g _) (hpb _)
            (ms (tgt h))) _ rfl (N (tgt h))).inv ≫
            (Scheme.Modules.pullback (F.map (u h)).left).map (θ (tgt h)).inv ≫ φ h ≫
            (θ (src h)).hom := fun h => by
    have := hNfp (src h)
    have := hNfp (tgt h)
    exact exists_mapModel D c (hpb _) (hpb _) (F.map (u h)) (d.H_w (u h)) (d.leg_H (u h)) hc
      (hfp _) (N (src h)) (N (tgt h)) _
  choose kh hkh using hmap
  -- Step 6: the final stage
  obtain ⟨m, hm⟩ := exists_over_lowerBound hσ
    (fun o : Option (H ⊕ S) => o.elim d.m₂ fun z => z.elim kh ms)
  have bm : m ⟶ d.m₂ := (hm none).some
  have bk : ∀ h, m ⟶ kh h := fun h => (hm (some (Sum.inl h))).some
  have bs : ∀ s, m ⟶ ms s := fun s => (hm (some (Sum.inr s))).some
  choose Ψ hΨ using fun h => hkh h m (bk h) (bm ≫ d.b₂) (bs (src h)) (bs (tgt h))
  choose r' hr' γ hr'eq hγ using hNret
  let F₀ := d.diagram bm
  let π : F ⋙ Over.map (c.π.app m.left) ⟶ F₀ :=
    { app j := Over.homMk (leg D (W j) c (F.obj j) (g j) (hpb j) m) (leg_fst _ _ _ _ _ _ _)
      naturality j j' f := by
        ext
        exact d.proj_map bm f }
  let M₀ : ∀ s, (F₀.obj (σ s)).left.Modules := fun s =>
    (Scheme.Modules.pullback (stageMap D (W (σ s)) (bs s))).obj (N s)
  let α : ∀ s, M s ≅ (Scheme.Modules.pullback (π.app (σ s)).left).obj (M₀ s) := fun s =>
    θ s ≪≫ (canIso (leg D (W (σ s)) c (F.obj _) (g _) (hpb _) m) (stageMap D _ (bs s)) _
      (leg_stageMap D _ c _ _ (hpb _) (bs s)) (N s)).symm
  let φ₀ : ∀ h, (Scheme.Modules.pullback (F₀.map (u h)).left).obj (M₀ (tgt h)) ⟶ M₀ (src h) :=
    fun h => canHom (F₀.map (u h)).left (stageMap D _ (bs (tgt h))) _ rfl (N (tgt h)) ≫ Ψ h
  have hρw : ∀ j (hj : P j), (pullback.snd (D.map m.hom) (W j).hom ≫ ψ j hj) ≫
      (G.obj ⟨j, hj⟩).hom = pullback.fst (D.map m.hom) (W j).hom ≫ r m.left := by
    intro j hj
    rw [Category.assoc, (hψpb j hj).w, ← Category.assoc, ← pullback.condition, Category.assoc,
      hr]
  have hρnat : ∀ x : A, stageLift (d.H (a x).2.2) (d.H_w (a x).2.2) (bm ≫ d.b₂) ≫
      pullback.snd (D.map m.hom) _ ≫ ψ (a x).2.1 x.2.2 =
      (pullback.snd _ _ ≫ ψ (a x).1 x.2.1) ≫
        (G.map (ObjectProperty.homMk (a x).2.2 :
          (⟨_, x.2.1⟩ : P.FullSubcategory) ⟶ ⟨_, x.2.2⟩)).left := fun x => by
    rw [stageLift_snd_assoc, stageMap_comp, Category.assoc,
      reassoc_of% (hd x), stageMap_snd_assoc, hℓψ, stageMap_snd_assoc, Category.assoc]
  let ρ₀ : P.ι ⋙ F₀ ⋙ Over.map (r m.left) ⟶ G :=
    { app j := Over.homMk (pullback.snd _ _ ≫ ψ j.obj j.property) (hρw j.obj j.property)
      naturality j j' f := by
        ext
        exact hρnat ⟨⟨j.obj, j'.obj, f.hom⟩, j.property, j'.property⟩ }
  have hρ : ∀ j, (π.app j.obj).left ≫ (ρ₀.app j).left = (ρ₁.app j).left := fun j =>
    (leg_snd_assoc D (W j.obj) c (F.obj j.obj) (g _) (hpb _) m _).trans (hψ j.obj j.property)
  have hβ : ∀ s (hs : Q s), stageMap D (W (σ s)) (bs s) ≫ r' s hs =
      pullback.snd _ _ ≫ ψ (σ s) (hQ s hs) := fun s hs => by
    rw [hr'eq, stageMap_snd_assoc]
  let β : ∀ s (hs : Q s),
      M₀ s ≅ (Scheme.Modules.pullback (ρ₀.app ⟨σ s, hQ s hs⟩).left).obj (M₁ s hs) :=
    fun s hs => (Scheme.Modules.pullback (stageMap D _ (bs s))).mapIso (γ s hs) ≪≫
      canIso (stageMap D _ (bs s)) (r' s hs) _ (hβ s hs) (M₁ s hs)
  refine ⟨m.left, F₀, π, M₀, α, φ₀, ρ₀, hρ, β, fun j => ?_, fun j => ?_, fun s => ?_,
    fun h => ?_, fun j => ?_, fun s hs => ?_⟩
  · have h := finitePresentation_pullback_fst (D.map m.hom) (hfp j)
    have := h.1
    have hlft : LocallyOfFiniteType (pullback.fst (D.map m.hom) (W j).hom) := inferInstance
    exact ⟨hlft, h.2.1⟩
  · exact isPullback_leg D (W j) c (F.obj j) (g j) (hpb j) m
  · have := hNfp s
    have := (finitePresentation_pullback_fst (D.map m.hom) (hfp (σ s))).1
    have hln : IsLocallyNoetherian (stageObj D (W (σ s)) m) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (D.map m.hom) (W (σ s)).hom)
    have hM₀ := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
      (stageMap D (W (σ s)) (bs s)) (N s)
    exact @isQuasicoherent_isFiniteType_of_isFinitePresentation (stageObj D (W (σ s)) m) hln
      ((Scheme.Modules.pullback (stageMap D (W (σ s)) (bs s))).obj (N s)) hM₀
  · exact comp_eq_of_transport_eq (F.map (u h)).left
      (leg D (W (σ (src h))) c (F.obj _) (g _) (hpb _) m)
      (leg D (W (σ (tgt h))) c (F.obj _) (g _) (hpb _) m) (F₀.map (u h)).left
      (d.proj_map bm (u h)) (stageMap D _ (bs (src h))) (stageMap D _ (bs (tgt h)))
      (leg_stageMap D _ c _ _ (hpb _) (bs (src h))) (leg_stageMap D _ c _ _ (hpb _) (bs (tgt h)))
      (θ (src h)) (θ (tgt h)) (φ h) (Ψ h) _ (hΨ h)
  · have := (IsPullback.of_hasPullback (D.map m.hom) (W j.obj).hom).flip.paste_horiz
      (hψpb j.obj j.property)
    rwa [hr] at this
  · exact retain_eq (leg D (W (σ s)) c (F.obj _) (g _) (hpb _) m) (stageMap D _ (bs s))
      (leg_stageMap D _ c _ _ (hpb _) (bs s)) (r' s hs) (hβ s hs) (hr' s hs)
      (hρ ⟨σ s, hQ s hs⟩) (θ s) (γ s hs) (α₁ s hs) (hγ s hs)

end Assembly

end

/-- A countable diagram of finite type `k`-schemes, coherent sheaves on them and homomorphisms
between pullbacks of these sheaves has a model over a countable algebraically closed subfield
`k₀` of `k`. Here `k₀` contains a prescribed countable subfield `k₁`, and on the part of the
data already modelled over `k₁` the model over `k₀` is the base change of the given one. -/
@[mmp "lem_mmp_countable_diagram_field_of_definition"]
public theorem exists_countable_isAlgClosed_model
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {J : Type u} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ Over (Spec (.of k)))
    [∀ j, LocallyOfFiniteType (F.obj j).hom] [∀ j, QuasiCompact (F.obj j).hom]
    {S : Type u} [Countable S] (σ : S → J) (M : ∀ s, (F.obj (σ s)).left.Modules)
    [∀ s, (M s).IsQuasicoherent] [∀ s, (M s).IsFiniteType]
    {H : Type u} [Countable H] (src tgt : H → S) (u : ∀ h, σ (src h) ⟶ σ (tgt h))
    (φ : ∀ h, (Scheme.Modules.pullback (F.map (u h)).left).obj (M (tgt h)) ⟶ M (src h))
    (k₁ : Subfield k) [Countable k₁]
    (P : ObjectProperty J) (G : P.FullSubcategory ⥤ Over (Spec (.of k₁)))
    (ρ₁ : P.ι ⋙ F ⋙ Over.map (Spec.map (CommRingCat.ofHom k₁.subtype)) ⟶ G)
    (hρ₁ : ∀ j, IsPullback (ρ₁.app j).left (F.obj j.obj).hom (G.obj j).hom
      (Spec.map (CommRingCat.ofHom k₁.subtype)))
    (Q : S → Prop) (hQ : ∀ s, Q s → P (σ s))
    (M₁ : ∀ s (hs : Q s), (G.obj ⟨σ s, hQ s hs⟩).left.Modules)
    [∀ s (hs : Q s), (M₁ s hs).IsQuasicoherent] [∀ s (hs : Q s), (M₁ s hs).IsFiniteType]
    (α₁ : ∀ s (hs : Q s),
      M s ≅ (Scheme.Modules.pullback (ρ₁.app ⟨σ s, hQ s hs⟩).left).obj (M₁ s hs)) :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀) (hk : k₁ ≤ k₀)
      (F₀ : J ⥤ Over (Spec (.of k₀)))
      (π : F ⋙ Over.map (Spec.map (CommRingCat.ofHom k₀.subtype)) ⟶ F₀)
      (M₀ : ∀ s, (F₀.obj (σ s)).left.Modules)
      (α : ∀ s, M s ≅ (Scheme.Modules.pullback (π.app (σ s)).left).obj (M₀ s))
      (φ₀ : ∀ h, (Scheme.Modules.pullback (F₀.map (u h)).left).obj (M₀ (tgt h)) ⟶ M₀ (src h))
      (ρ₀ : P.ι ⋙ F₀ ⋙ Over.map (Spec.map (CommRingCat.ofHom (Subfield.inclusion hk))) ⟶ G)
      (hρ : ∀ j, (π.app j.obj).left ≫ (ρ₀.app j).left = (ρ₁.app j).left)
      (β : ∀ s (hs : Q s),
        M₀ s ≅ (Scheme.Modules.pullback (ρ₀.app ⟨σ s, hQ s hs⟩).left).obj (M₁ s hs)),
      (∀ j, LocallyOfFiniteType (F₀.obj j).hom ∧ QuasiCompact (F₀.obj j).hom) ∧
      (∀ j, IsPullback (π.app j).left (F.obj j).hom (F₀.obj j).hom
        (Spec.map (CommRingCat.ofHom k₀.subtype))) ∧
      (∀ s, (M₀ s).IsQuasicoherent ∧ (M₀ s).IsFiniteType) ∧
      (∀ h, φ h ≫ (α (src h)).hom =
        (Scheme.Modules.pullback (F.map (u h)).left).map (α (tgt h)).hom ≫
          ((Scheme.Modules.pullbackComp (F.map (u h)).left (π.app (σ (tgt h))).left).hom.app
              (M₀ (tgt h)) ≫
            (Scheme.Modules.pullbackCongr
                (congrArg CommaMorphism.left (π.naturality (u h)))).hom.app (M₀ (tgt h)) ≫
            (Scheme.Modules.pullbackComp (π.app (σ (src h))).left
                (F₀.map (u h)).left).inv.app (M₀ (tgt h))) ≫
          (Scheme.Modules.pullback (π.app (σ (src h))).left).map (φ₀ h)) ∧
      (∀ j, IsPullback (ρ₀.app j).left (F₀.obj j.obj).hom (G.obj j).hom
        (Spec.map (CommRingCat.ofHom (Subfield.inclusion hk)))) ∧
      (∀ s (hs : Q s), (α s).hom ≫
        (Scheme.Modules.pullback (π.app (σ s)).left).map (β s hs).hom ≫
          (Scheme.Modules.pullbackComp (π.app (σ s)).left
              (ρ₀.app ⟨σ s, hQ s hs⟩).left).hom.app (M₁ s hs) ≫
          (Scheme.Modules.pullbackCongr (hρ ⟨σ s, hQ s hs⟩)).hom.app (M₁ s hs) =
        (α₁ s hs).hom) := by
  haveI := nonempty_idx k k₁
  haveI := isDirected_idx k k₁
  haveI := isAffine_specDiagram_obj k k₁
  haveI : ∀ {K L : (Idx k k₁)ᵒᵖ} (f : K ⟶ L), IsAffineHom ((specDiagram k k₁).map f) :=
    fun _ => isAffineHom_of_isAffine _
  haveI : ∀ K, CompactSpace ((specDiagram k k₁).obj K) := fun _ => inferInstance
  haveI : ∀ K, QuasiSeparatedSpace ((specDiagram k k₁).obj K) := fun _ => inferInstance
  haveI : ∀ K : (Idx k k₁)ᵒᵖ, IsLocallyNoetherian ((specDiagram k k₁).obj K) := fun K => by
    rw [specDiagram_obj]; infer_instance
  have hσ : ∀ (ι : Type u) [Countable ι] (f : ι → (Idx k k₁)ᵒᵖ), ∃ i, ∀ x, Nonempty (i ⟶ f x) := by
    intro ι _ f
    obtain ⟨K, hK⟩ := exists_le (fun x => (f x).unop)
    exact ⟨op K, fun x => ⟨(homOfLE (hK x)).op⟩⟩
  let r : ∀ K : (Idx k k₁)ᵒᵖ, (specDiagram k k₁).obj K ⟶ Spec (.of k₁) := fun K =>
    Spec.map (CommRingCat.ofHom (Subfield.inclusion K.unop.2.2.2))
  have hr : ∀ {K L : (Idx k k₁)ᵒᵖ} (e : K ⟶ L), (specDiagram k k₁).map e ≫ r L = r K :=
    fun _ => (Spec.map_comp _ _).symm
  have hι₁ : ∀ K, (specCone k k₁).π.app K ≫ r K = Spec.map (CommRingCat.ofHom k₁.subtype) :=
    fun _ => (Spec.map_comp _ _).symm
  have hF : ∀ j, FinitePresentation (F.obj j).hom := fun j => finitePresentation_of_finiteType _
  have hX : ∀ j, IsLocallyNoetherian (F.obj j).left := fun j =>
    LocallyOfFiniteType.isLocallyNoetherian (F.obj j).hom
  haveI : ∀ s, (M s).IsFinitePresentation := fun s => isFinitePresentation_of_isLocallyNoetherian _
  have hG' : ∀ j, LocallyOfFiniteType (G.obj j).hom ∧ QuasiCompact (G.obj j).hom := fun j =>
    locallyOfFiniteType_quasiCompact_of_isPullback k₁.subtype (hρ₁ j)
  have hG : ∀ j, FinitePresentation (G.obj j).hom := fun j => by
    have := (hG' j).1
    have := (hG' j).2
    exact finitePresentation_of_finiteType _
  haveI : ∀ s (hs : Q s), (M₁ s hs).IsFinitePresentation := fun s hs => by
    have := (hG' ⟨σ s, hQ s hs⟩).1
    have : IsLocallyNoetherian (G.obj ⟨σ s, hQ s hs⟩).left :=
      LocallyOfFiniteType.isLocallyNoetherian (G.obj ⟨σ s, hQ s hs⟩).hom
    exact isFinitePresentation_of_isLocallyNoetherian _
  obtain ⟨i, F₀, π, M₀, α, φ₀, ρ₀, hρ, β, h1, h2, h3, h4, h5, h6⟩ :=
    exists_stage_model (specDiagram k k₁) (specCone k k₁) (isLimitSpecCone k k₁) hσ r hr
      (Spec.map (CommRingCat.ofHom k₁.subtype)) hι₁ F hF σ M src tgt u φ P G hG ρ₁ hρ₁ Q hQ M₁ α₁
  exact ⟨i.unop.1, i.unop.2.1, i.unop.2.2.1, i.unop.2.2.2, F₀, π, M₀, α, φ₀, ρ₀, hρ, β,
    h1, h2, h3, h4, h5, h6⟩

end MMP.FieldOfDefinition
