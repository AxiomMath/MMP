module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.ContractedBadBranches
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.LabelNormalizationModel
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.ProjectiveSpace.ProductProjectiveLine
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicTopology.BorelMoore.CycleSpanRestriction
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Action
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.ZariskiSequenceBasic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.Semismooth.BranchLocus
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceCurves
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Curves.DegreeEuler
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.Chow.CycleClassDegree
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeAffineHom
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.RationalCycleClass
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ConductorKernel

/-!
# The rank difference across a step diagram

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold step diagram in which both morphisms are small, with
bad loci `W^±`, let `S⁻` be a prime divisor of `Y⁻` and `S⁺ = (f⁺)⁻¹_* f⁻_* S⁻` its strict
transform. The boxed divisor cycle ranks of the normalizations differ by the difference of the
bad branch counts:
`ρ^□((S⁻)^ν) - ρ^□((S⁺)^ν) = e⁻(S⁻) - e⁺(S⁻)`.

Let `σ^± : (S^±)^ν ⟶ T` be the morphisms to the normalization `T` of `f⁻(S⁻)`, isomorphisms from
`O^± = (S^±)^ν ∖ (ν^±)⁻¹(W^±)` onto a common open of `T`. For each sign,
`ρ^□((S^±)^ν) = ρ_2(O^± × ℙ¹) + e^±(S⁻)`: restriction of cycle spans from `(S^±)^ν × ℙ¹` to
`O^± × ℙ¹` is onto, with kernel spanned by the classes of the surfaces `P × ℙ¹` over the bad
branches `P`, which are independent since `σ^± × id` contracts them. The isomorphism `O⁻ ≅ O⁺`
makes the two ranks `ρ_2(O^± × ℙ¹)` equal, and subtracting gives the identity.

## Main results

* `MMP.Fourfold.boxedSurfaceRank_sub_boxedSurfaceRank_eq_badBranchCount_sub_badBranchCount`:
  the rank difference.

## Implementation notes

* The normalizations `(S^±)^ν` are `MMP.Fourfold.primeDivisorNormalizationScheme`, over `ℂ`
  through `(S^±)^ν ⟶ Y^±`, and complex schemes since `Y^±` are projective
  (`MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`). The bad branch counts are
  `MMP.Fourfold.badBranchCount` on the bad loci `MMP.Fourfold.badLocusMinus` and
  `MMP.Fourfold.badLocusPlus`, `e⁺` being taken on the strict transform `S⁺`, as in
  `MMP.Fourfold.IsBadBranchCountPlus`. The identity is an identity of integers.
* The independence of the classes of contracted divisors is proved for a birational morphism of
  normal projective threefolds, through a strong resolution, the localization sequence, the
  Cartier divisor dictionary (`MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback`), the
  vanishing of curve degrees of a line bundle with zero topological first Chern class
  (`MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero`) and the negativity lemma; it is then
  applied to `σ^± × id`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open MMP (IsComplexScheme)

namespace MMP.Fourfold

/-! ### Contracted divisors have independent classes

Suppose `∑ c_P [P] = 0` in `H_4(S, ℚ)` for prime divisors `P` of a normal projective threefold
`S` contracted by a birational morphism `q : S ⟶ T`. On a strong resolution `r : W ⟶ S`, an
isomorphism over the smooth locus `U` of `S`, the class of `∑ c_P P̃` restricts to zero over
`r⁻¹(U)`; the localization sequence of `W ∖ r⁻¹(U)` gives a `ℚ`-divisor `G` over the singular
locus with `F = ∑ c_P P̃ - G` of class zero. A class zero divisor on the smooth projective
threefold `W` has degree zero on every curve (its line bundle has zero topological `c₁`),
every component of `F` is exceptional for `r ≫ q`, and the negativity lemma gives `F = 0`. -/

section Independence

open MMP MMP.Fourfold
open MMP.Chow (divisorClass)
open scoped MMP.SubschemeOver

universe u

/-- If `a + c = 3` in `WithBot ℕ∞` with `a` a natural number, then `c` is a natural number. -/
private theorem exists_coheight_eq_of_add_eq_three {a : ℕ} {c : ℕ∞}
    (h : ((a : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : ∃ n : ℕ, c = n ∧ a + n = 3 := by
  have h' : (a : ℕ∞) + c = 3 := by
    apply WithBot.coe_injective
    rwa [WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_ofNat]
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n => exact ⟨n, rfl, by exact_mod_cast h'⟩

/-- On an integral threefold over `ℂ`, the generic point of a prime divisor has
delta-dimension `2`. -/
private theorem relativeDimension_primeDivisor_genericPoint {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    (hX : topologicalKrullDim X = 3) (P : MMP.Mori.PrimeDivisor X) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = (2 : ℕ) := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (X ↘ Spec (.of ℂ))
    P.genericPoint
  rw [hX, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ))] at h1
  obtain ⟨n, hn, hsum⟩ := exists_coheight_eq_of_add_eq_three h1
  have h0 := Stacks.Chow.relativeDimension_fieldChowSituation_nonneg ℂ (X ↘ Spec (.of ℂ))
    P.genericPoint
  have h0' := Int.toNat_of_nonneg h0
  have hn1 : n = 1 := by
    have := P.coheight_genericPoint
    rw [hn] at this
    exact_mod_cast this
  omega

open Stacks.Intersection.ExteriorProductProjections in
/-- The generic point of a threefold has delta-dimension three. -/
private theorem relativeDimension_genericPoint {W : Scheme.{0}} [IsIntegral W]
    [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
    (hW3 : topologicalKrullDim W = 3) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (W ↘ Spec (.of ℂ)) (genericPoint W) = ((2 + 1 : ℕ) : ℤ) := by
  refine relativeDimension_eq_of_topologicalKrullDim_closure ℂ _ _ (2 + 1) ?_
  rw [(genericPoint_spec W).def, (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq, hW3]
  rfl

/-- **Numerical triviality of a divisor with zero class.** On a smooth projective complex
threefold `W`, a divisor `D` whose class vanishes in `H_4(W, ℚ)` has degree zero on every curve:
by the Cartier divisor dictionary `c₁(𝒪_W(D)) = 0` in `H²(W^an, ℚ)`, and a line bundle with
vanishing topological first Chern class has degree zero on every curve. -/
private theorem degreeOn_eq_zero_of_divisorClass_eq_zero {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [W.Over (Spec (.of ℂ))] [IsComplexScheme W]
    (hWp : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (hW3 : topologicalKrullDim W = 3)
    (D : MMP.Mori.Divisor W) (hD : divisorClass W (MMP.Mori.Divisor.toQDivisor D) = 0)
    (C : MMP.Mori.ProperCurve (W ↘ Spec (.of ℂ))) :
    MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le D
      (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D) = 0 := by
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  have hinv : Stacks.Ample.IsInvertibleModule W D.divisorialSheaf :=
    hcart.isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 D.divisorialSheaf := hinv
  have h := (MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hWp hsm (d := 2)
    (by rw [hW3]; rfl) (MMP.Mori.Divisor.toQDivisor D) one_pos D (by rw [Nat.cast_one, one_smul])
    (genericPoint W) (relativeDimension_genericPoint hW3)).2.1 hD
  have hc := MMP.Chow.firstChernClassTop_eq_zero_of_mapCoeff_eq_zero D.divisorialSheaf h
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hWp
  have : Stacks.Ample.IsInvertibleModule W H := hH
  unfold MMP.Mori.Divisor.degreeOn
  exact MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple W H).mpr hHa) D.divisorialSheaf hc C.ι C.dim_le

section Topo

variable {W S : Scheme.{0}} [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]

/-- The `ℂ`-points of `S` lying over an open `V`, as an open subset of `S(ℂ)`. -/
private def pointsOverOpens (V : S.Opens) :
    TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ S)) :=
  ⟨UnderlyingSpace.pointsOver (V : Set S), by
    have := UnderlyingSpace.isOpen_setOf_le_preimage (K := ℂ) (X := S) V
    convert this using 1
    ext p
    simp only [UnderlyingSpace.pointsOver, Set.mem_setOf_eq]
    constructor
    · intro h x _
      rwa [Subsingleton.elim x (IsLocalRing.closedPoint ℂ)]
    · exact fun h => h trivial⟩

/-- A `ℂ`-point whose closed point lies in an open `U` factors through `U`. -/
private theorem exists_lift_of_mem {X : Scheme.{0}} (U : X.Opens) (a : Spec (.of ℂ) ⟶ X)
    (h : a (IsLocalRing.closedPoint ℂ) ∈ U) : ∃ a' : Spec (.of ℂ) ⟶ U, a' ≫ U.ι = a := by
  refine ⟨IsOpenImmersion.lift U.ι a ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨y, rfl⟩
  rwa [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint ℂ)]

/-- A morphism which is an isomorphism over `V` is bijective on `ℂ`-points over `V`. -/
private theorem bijective_restrictPreimage (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))] (V : S.Opens)
    [IsIso (r ∣_ V)] :
    Function.Bijective (borelMooreHomology.restrictPreimage
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) (pointsOverOpens V)) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : a.toHom ≫ r = b.toHom ≫ r := congrArg (fun z => (Subtype.val z).toHom) hab
    obtain ⟨a', ha'⟩ := exists_lift_of_mem (r ⁻¹ᵁ V) a.toHom ha
    obtain ⟨b', hb'⟩ := exists_lift_of_mem (r ⁻¹ᵁ V) b.toHom hb
    have key : a' ≫ (r ∣_ V) ≫ V.ι = b' ≫ (r ∣_ V) ≫ V.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, ha', ← Category.assoc, hb', hab']
    have : a' = b' := by
      rwa [← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at key
    apply Subtype.ext
    apply UnderlyingSpace.ext
    rw [← ha', ← hb', this]
  · rintro ⟨q, hq⟩
    obtain ⟨q', hq'⟩ := exists_lift_of_mem V q.toHom hq
    let p : Spec (.of ℂ) ⟶ W := q' ≫ inv (r ∣_ V) ≫ (r ⁻¹ᵁ V).ι
    have hpr : p ≫ r = q.toHom := by
      simp only [p, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hq']
    have hpo : p ≫ W ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [← comp_over r (Spec (.of ℂ)), ← Category.assoc, hpr, q.toHom_comp_over]
    refine ⟨⟨⟨p, hpo⟩, ?_⟩, ?_⟩
    · change (p ≫ r) (IsLocalRing.closedPoint ℂ) ∈ V
      rwa [hpr]
    · exact Subtype.ext (UnderlyingSpace.ext hpr)

/-- Push-forward along a bijective closed embedding is injective. -/
private theorem injective_pushforward_of_isClosedEmbedding_of_surjective {A B : TopCat.{0}}
    (f : A ⟶ B) (hf : IsProperMap f) (hemb : Topology.IsClosedEmbedding f)
    (hsurj : Function.Surjective f) (k : ℤ) :
    Function.Injective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom := by
  let Φ := hemb.isEmbedding.toHomeomorphOfSurjective hsurj
  have hcomp : f ≫ TopCat.ofHom ⟨Φ.symm, Φ.symm.continuous⟩ = 𝟙 A := by
    ext a
    exact Φ.symm_apply_apply a
  intro a b hab
  have := congrArg (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom ⟨Φ.symm, Φ.symm.continuous⟩) Φ.symm.isProperMap k).hom hab
  rw [← borelMooreHomology.pushforward_comp_apply', ← borelMooreHomology.pushforward_comp_apply',
    borelMooreHomology.pushforward_congr hcomp _ isProperMap_id,
    borelMooreHomology.pushforward_id] at this
  exact this

/-- If `r` is an isomorphism over `V` and `r_* x = 0`, then `x` restricts to zero over
`r⁻¹(V)(ℂ)`. -/
private theorem restrict_eq_zero_of_pushforward_eq_zero [IsComplexScheme W] [IsComplexScheme S]
    (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))] [IsProper r] (V : S.Opens) [IsIso (r ∣_ V)] (k : ℤ)
    (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) k)
    (hx : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r))
      (UnderlyingSpace.isProperMap_map (K := ℂ) r) k).hom x = 0) :
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (TopologicalSpace.Opens.comap (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)).hom
        (pointsOverOpens V)) k).hom x = 0 := by
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) r
  have h := borelMooreHomology.restrict_pushforward_apply ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) hp (pointsOverOpens V) k x
  rw [hx, map_zero] at h
  have hb := bijective_restrictPreimage r V
  have hpp := borelMooreHomology.isProperMap_restrictPreimage
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) (pointsOverOpens V) hp
  have hemb : Topology.IsClosedEmbedding (borelMooreHomology.restrictPreimage
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) (pointsOverOpens V)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (borelMooreHomology.restrictPreimage _ _).hom.continuous hb.1 hpp.isClosedMap
  exact injective_pushforward_of_isClosedEmbedding_of_surjective _ hpp hemb hb.2 k
    (h.symm.trans (map_zero _).symm)

/-- **Localization.** A class in `H_4(W, ℚ)` which restricts to zero off a closed set `Q` of
dimension at most two is the class of a `ℚ`-divisor supported on prime divisors in `Q`. -/
private theorem exists_divisorClass_eq_of_restrict_eq_zero {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] (Q : Closeds W)
    (hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Q).subscheme ≤ (2 : ℕ))
    (hdiv : ∀ w : W, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ)) w = 2 →
        ∃ E : MMP.Mori.PrimeDivisor W, E.genericPoint = w)
    (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) ((4 : ℕ) : ℤ))
    (hx : ∀ O : Opens (TopCat.of (UnderlyingSpace ℂ W)),
      (O : Set (UnderlyingSpace ℂ W)) = (UnderlyingSpace.pointsOver (Q : Set W))ᶜ →
      (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) O ((4 : ℕ) : ℤ)).hom x = 0) :
    ∃ G : MMP.Mori.QDivisor W, (∀ P ∈ G.support, P.genericPoint ∈ (Q : Set W)) ∧
      x = divisorClass W G := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal Q with hI
  obtain ⟨δ, -, h2, -⟩ := IsComplexScheme.exists_borelMooreHomology_longExact ℚ
    (ModuleCat.of ℚ ℚ) W I.subschemeι
  have hrange : Set.range I.subschemeι = (Q : Set W) := by
    rw [I.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hres := hx (borelMooreHomology.complOpens (Y := TopCat.of (UnderlyingSpace ℂ W))
    (UnderlyingSpace.isClosed_range_map_of_isClosedImmersion I.subschemeι)) (by
      change (Set.range (UnderlyingSpace.map (K := ℂ) I.subschemeι))ᶜ = _
      rw [UnderlyingSpace.range_map_of_isClosedImmersion, hrange])
  obtain ⟨z, hz⟩ := ((h2 ((4 : ℕ) : ℤ)) x).1 hres
  obtain ⟨β, rfl⟩ := (MMP.Fourfold.bijective_rationalCycleClass (X := I.subscheme) (k := 2) hdim).2 z
  -- the classes of the prime divisors in `Q`
  let N : Submodule ℚ (Chow.BMHomology ℚ W (2 * 2)) := Submodule.span ℚ
    (Set.range fun P : {P : MMP.Mori.PrimeDivisor W // P.genericPoint ∈ (Q : Set W)} =>
      divisorClass W (Finsupp.single P.1 1))
  have hpt : ∀ (w : W) (hw : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ)) w = (2 : ℕ)),
      w ∈ (Q : Set W) → Chow.pointCycleClass ℚ w hw ∈ N := by
    intro w hw hwQ
    obtain ⟨E, rfl⟩ := hdiv w hw
    rw [← Chow.divisorClass_single hw]
    exact Submodule.subset_span ⟨⟨E, hwQ⟩, rfl⟩
  have hmem : ∀ γ, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) I.subschemeι))
      (UnderlyingSpace.isProperMap_map (K := ℂ) I.subschemeι) ((2 * 2 : ℕ) : ℤ)).hom
        (Chow.rationalCycleClass I.subscheme 2 γ) ∈ N := by
    intro γ
    induction γ using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact N.zero_mem
    | add a b ha hb =>
      rw [map_add, map_add]
      exact N.add_mem ha hb
    | tmul q c =>
      rw [Chow.rationalCycleClass_tmul, map_smul, Chow.cycleClass_eq_sum, map_sum]
      refine N.smul_mem _ (N.sum_mem fun y _ => ?_)
      rw [map_zsmul]
      refine zsmul_mem ?_ _
      unfold Chow.pointCycleClassOrZero
      split_ifs with hy
      · rw [Chow.pushforward_pointCycleClass]
        refine zsmul_mem ?_ _
        unfold Chow.pointCycleClassOrZero
        split_ifs with hd
        · exact hpt _ hd (by rw [← hrange]; exact ⟨y, rfl⟩)
        · exact N.zero_mem
      · rw [map_zero]
        exact N.zero_mem
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hmem β)
  refine ⟨Finsupp.mapDomain Subtype.val c, fun P hP => ?_, ?_⟩
  · obtain ⟨V, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
    exact V.2
  · rw [← hz]
    refine (hc.symm.trans ?_)
    rw [Finsupp.mapDomain, map_finsuppSum]
    refine Finsupp.sum_congr fun P _ => ?_
    rw [← Finsupp.smul_single_one (P : MMP.Mori.PrimeDivisor W) (c P), map_smul]

/-- A morphism which is an isomorphism over `U` has residue degree one at the points over `U`. -/
private theorem residueDegree_eq_one_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)]
    (x : X) (hx : f x ∈ U) : f.residueDegree x = 1 := by
  obtain ⟨x', rfl⟩ : ∃ x' : (f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι x' = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : IsIso (((f ⁻¹ᵁ U).ι ≫ f).residueFieldMap x') := by
    rw [← morphismRestrict_ι, Scheme.residueFieldMap_comp]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_ <;>
      exact Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _
  rw [Scheme.residueFieldMap_comp] at h1
  have h3 : IsIso ((f ⁻¹ᵁ U).ι.residueFieldMap x') :=
    Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _
  have h2 : IsIso (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (f.residueFieldMap ((f ⁻¹ᵁ U).ι x'))
      ((f ⁻¹ᵁ U).ι.residueFieldMap x') h3 h1
  have hb : Function.Bijective (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')).hom :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap ((f ⁻¹ᵁ U).ι x'))
  unfold Scheme.Hom.residueDegree
  letI := (f.residueFieldMap ((f ⁻¹ᵁ U).ι x')).hom.toAlgebra
  let e := AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f ((f ⁻¹ᵁ U).ι x')))
    (X.residueField ((f ⁻¹ᵁ U).ι x'))) hb
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- Push-forward of the class of the strict transform `∑ c_P P̃` along a morphism which is an
isomorphism over the generic points of the `P`. -/
private theorem pushforward_divisorClass_mapDomain {W S : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [S.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsComplexScheme S] (r : W ⟶ S)
    [r.IsOver (Spec (.of ℂ))] [IsProper r] (U : S.Opens)
    [IsIso (r ∣_ U)] (lift : MMP.Mori.PrimeDivisor S → MMP.Mori.PrimeDivisor W)
    (hlift : ∀ P, r (lift P).genericPoint = P.genericPoint)
    (hU : ∀ P : MMP.Mori.PrimeDivisor S, P.genericPoint ∈ U)
    (hxS : ∀ P : MMP.Mori.PrimeDivisor S, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (S ↘ Spec (.of ℂ)) P.genericPoint =
        (2 : ℕ))
    (hxW : ∀ E : MMP.Mori.PrimeDivisor W, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ)) E.genericPoint =
        (2 : ℕ))
    (D : MMP.Mori.QDivisor S) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r))
      (UnderlyingSpace.isProperMap_map (K := ℂ) r) ((2 * 2 : ℕ) : ℤ)).hom
        (divisorClass W (Finsupp.mapDomain lift D)) = divisorClass S D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg, map_add]
  | single P c =>
    rw [Finsupp.mapDomain_single, ← Finsupp.smul_single_one (lift P) c,
      ← Finsupp.smul_single_one P c, map_smul, map_smul, map_smul, Chow.divisorClass_single (hxW _), Chow.divisorClass_single (hxS _)]
    congr 1
    rw [Chow.pushforward_pointCycleClass,
      residueDegree_eq_one_of_isIso r U _ (by rw [hlift]; exact hU P), Nat.cast_one, one_smul,
      Chow.pointCycleClassOrZero, dif_pos (by rw [hlift]; exact hxS P)]
    generalize_proofs h
    revert h
    rw [hlift]
    intro h
    rfl

end Topo

section Normalization

open MMP.Mori MMP.Flips

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
    (hf : MMP.Mori.IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] :
    degreeOver f = 1 := by
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

/-- `L · C` is the degree of `𝒪(L)` along `C`, whichever normalization computes it. -/
private theorem IsCartierIntersectionNumber.eq_degreeOn [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

end Normalization

section Neg

open MMP.Mori MMP.Flips

/-- **Negativity in both signs.** A divisor on the source of a projective birational morphism
of normal varieties which has degree zero on every curve and whose components are all
exceptional is zero. -/
private theorem eq_zero_of_degreeOn_eq_zero {W T : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    (sT : T ⟶ Spec (.of ℂ)) [QuasiCompact sW] [IsLocallyNoetherian T] [IsNormal T]
    [IsLocallyNoetherian W] [IsNormal W] (hW : IsNormalVariety ℂ sW) (hT : IsNormalVariety ℂ sT)
    (f : W ⟶ T) (hf : f ≫ sT = sW) (hfp : IsProjectiveMorphism f)
    (hfb : MMP.Mori.IsBirationalMorphism f) (D : Divisor W) (hD : D.IsCartier)
    (hdeg : ∀ C : ProperCurve sW, D.degreeOn ℂ sW C.ι C.dim_le hD = 0)
    (hexc : ∀ P ∈ D.support, RationalMap.transformPrimeDivisor f.toRationalMap P = none) :
    D = 0 := by
  classical
  set B : RDivisor W := Divisor.toRDivisor D with hBdef
  have hpres : ∀ c : ℝ, c • B = ∑ j : Fin 1, (![c] j) • (Divisor.toRDivisor (![D] j)) := by
    intro c; simp [hBdef]
  have hnef : ∀ c : ℝ, IsRelativelyNef ℂ sW f (c • B) := by
    intro c
    refine ⟨1, ![c], ![D], fun j => by fin_cases j; exact hD, hpres c, fun C _ x hx => ?_⟩
    obtain ⟨hL, d, -, hd, rfl⟩ := hx
    have h0 : d 0 = 0 := by
      rw [IsCartierIntersectionNumber.eq_degreeOn (hd 0)]
      exact hdeg C
    simp [h0]
  have hcomb : ∀ c : ℝ, IsCartierCombination (c • B) := by
    intro c
    refine ⟨1, ![c], ![D], fun j => by fin_cases j; exact hD, ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rfl
  have hpush : ∀ c : ℝ,
      (RationalMap.transformDivisor (X := W) f.toRationalMap (c • B)).IsEffective := by
    intro c
    have : RationalMap.transformDivisor (X := W) f.toRationalMap (c • B) = 0 := by
      rw [← Finsupp.sum_single (c • B), Finsupp.sum, map_sum]
      refine Finset.sum_eq_zero fun P hP => ?_
      refine RationalMap.transformDivisor_single_of_eq_none (hexc P ?_) _
      rw [Finsupp.mem_support_iff] at hP ⊢
      intro h0
      apply hP
      change c * (Divisor.toRDivisor D).coeff P = 0
      rw [Divisor.coeff_toRDivisor]
      change c * ((D P : ℤ) : ℝ) = 0
      rw [h0]; simp
    rw [this]
    intro P; simp
  have h1 := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ sT sW hT hW f
    hf hfp hfb (hcomb 1) (by simpa using hnef (-1)) (hpush 1)
  have h2 := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ sT sW hT hW f
    hf hfp hfb (hcomb (-1)) (by simpa using hnef 1) (hpush (-1))
  ext P
  have a := h1 P
  have b := h2 P
  change 0 ≤ (1 : ℝ) * (Divisor.toRDivisor D).coeff P at a
  change 0 ≤ (-1 : ℝ) * (Divisor.toRDivisor D).coeff P at b
  rw [Divisor.coeff_toRDivisor] at a b
  have : (D.coeff P : ℝ) = 0 := by linarith
  exact_mod_cast this

end Neg

/-- The Krull dimension of the specialization order of a scheme is its dimension. -/
private theorem krullDim_eq_of_topologicalKrullDim {X : Scheme.{0}} {n : WithBot ℕ∞}
    (h : topologicalKrullDim X = n) : Order.krullDim X = n := by
  have := MMP.Intersection.Scheme.dimension_eq_krullDim_subvariety X
  rw [Order.krullDim_eq_of_orderIso MMP.Intersection.Scheme.Subvariety.orderIsoPoints] at this
  exact this.symm.trans h

/-- Under a morphism of threefolds, a point of codimension at least two maps to a point of
codimension at least two. -/
private theorem two_le_coheight_map {S T : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [T.Over (Spec (.of ℂ))]
    [IsIntegral S] [IsIntegral T]
    [LocallyOfFiniteType (S ↘ Spec (.of ℂ))] [LocallyOfFiniteType (T ↘ Spec (.of ℂ))]
    (q : S ⟶ T) [q.IsOver (Spec (.of ℂ))]
    (hS : topologicalKrullDim S = 3) (hT : topologicalKrullDim T = 3) (y : S)
    (hy : 2 ≤ Order.coheight y) : 2 ≤ Order.coheight (q y) := by
  have h1 := MMP.height_add_coheight_eq_krullDim ℂ y
  have h2 := MMP.height_add_coheight_eq_krullDim ℂ (q y)
  rw [krullDim_eq_of_topologicalKrullDim hS] at h1
  rw [krullDim_eq_of_topologicalKrullDim hT] at h2
  -- transcendence degrees of residue fields only drop along `q`
  have h3 : topologicalKrullDim (closure {q y} : Set T) ≤
      topologicalKrullDim (closure {y} : Set S) := by
    rw [topologicalKrullDim_closure_singleton_eq_trdeg ℂ T (T ↘ Spec (.of ℂ)),
      topologicalKrullDim_closure_singleton_eq_trdeg ℂ S (S ↘ Spec (.of ℂ)), WithBot.coe_le_coe]
    exact Cardinal.toENat.monotone' (MMP.Flips.trdeg_residueField_add (S ↘ Spec (.of ℂ))
      (T ↘ Spec (.of ℂ)) q ((Scheme.Hom.isOver_iff (Spec (.of ℂ))).1 inferInstance) y ▸ le_self_add)
  rw [MMP.topologicalKrullDim_closure_singleton_eq_height,
    MMP.topologicalKrullDim_closure_singleton_eq_height] at h3
  have h1' : Order.height y + Order.coheight y = 3 :=
    WithBot.coe_injective (h1.trans rfl)
  have h2' : Order.height (q y) + Order.coheight (q y) = 3 :=
    WithBot.coe_injective (h2.trans rfl)
  have h3' : Order.height (q y) ≤ Order.height y := by exact_mod_cast h3
  have hfin : ∀ a b : ℕ∞, a + b = 3 → a ≠ ⊤ ∧ b ≠ ⊤ := fun a b h => by
    constructor <;> intro ha <;> simp [ha] at h
  obtain ⟨ha, hb⟩ := hfin _ _ h1'
  obtain ⟨hc, hd⟩ := hfin _ _ h2'
  lift Order.height y to ℕ using ha with a
  lift Order.coheight y to ℕ using hb with b
  lift Order.height (q y) to ℕ using hc with c
  lift Order.coheight (q y) to ℕ using hd with d
  norm_cast at *
  omega

/-- A prime divisor whose generic point maps to a point of codimension at least two has no
transform. -/
private theorem transformPrimeDivisor_eq_none_of_two_le_coheight {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] (f : X ⟶ Y) (E : MMP.Mori.PrimeDivisor X)
    (h : 2 ≤ Order.coheight (f E.genericPoint)) :
    MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E = none := by
  by_contra hne
  obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hne
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff] at hP
  rw [hP, P.coheight_genericPoint] at h
  exact absurd h (by decide)

/-- The singular points of a normal variety have codimension at least two. -/
private theorem two_le_coheight_of_notMem_smoothLocus {S : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    (hSn : MMP.Mori.IsNormalVariety ℂ sS) (y : S) (hy : y ∉ MMP.Mori.smoothLocus sS) :
    2 ≤ Order.coheight y := by
  haveI : IsIntegral S := hSn.1.toIsIntegral
  haveI : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
  by_contra h
  push Not at h
  have hc : Order.coheight y = 0 ∨ Order.coheight y = 1 := by
    generalize Order.coheight y = c at h ⊢
    induction c using ENat.recTopCoe with
    | top => simp at h
    | coe n => norm_cast at h ⊢; omega
  rcases hc with h0 | h1
  · rw [Order.coheight_eq_zero] at h0
    have hgen : y = genericPoint S := by
      have h1 : y ≤ genericPoint S := by
        rw [Scheme.le_iff_specializes]; exact genericPoint_specializes y
      have h2 := h0 h1
      rw [Scheme.le_iff_specializes] at h2
      exact (h2.antisymm (genericPoint_specializes y)).eq
    apply hy
    rw [hgen, MMP.Mori.smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField sS
  · apply hy
    have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hSn
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)
    have e : MMP.Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)
        = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1
    rwa [e] at this

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A proper closed subset of a threefold has dimension at most two. -/
private theorem dimension_vanishingIdeal_le_two {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsIntegral W] (hW3 : topologicalKrullDim W = 3) (Q : Closeds W)
    (hne : (Q : Set W) ≠ Set.univ) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Q).subscheme ≤ (2 : ℕ) := by
  change topologicalKrullDim _ ≤ _
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq, Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal Q)]
  have hfin : topologicalKrullDim (Q : Set W) ≠ ⊤ := fun h => by
    have h2 := topologicalKrullDim_subspace_le W (Q : Set W)
    rw [h, hW3] at h2
    exact absurd h2 (by decide)
  have hlt := MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ Q.isClosed hne hfin
  rw [hW3] at hlt
  exact Order.le_of_lt_succ hlt

/-- On a threefold, every point of delta-dimension two is the generic point of a prime divisor. -/
private theorem exists_primeDivisor_genericPoint_eq {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] (hW : topologicalKrullDim W = 3)
    (w : W) (hw : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ)) w = 2) :
    ∃ E : MMP.Mori.PrimeDivisor W, E.genericPoint = w := by
  have h1 := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (W ↘ Spec (.of ℂ)) w
  rw [hw, AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height] at h1
  have hh : Order.height w = 2 :=
    WithBot.coe_injective (h1.trans (by first | rfl | simp))
  have h2 := MMP.height_add_coheight_eq_krullDim ℂ w
  rw [krullDim_eq_of_topologicalKrullDim hW, hh] at h2
  have h3 : (2 : ℕ∞) + Order.coheight w = 3 := WithBot.coe_injective (h2.trans rfl)
  have hc : Order.coheight w = 1 := by
    generalize Order.coheight w = c at h3 ⊢
    induction c using ENat.recTopCoe with
    | top => simp at h3
    | coe n => norm_cast at h3 ⊢; omega
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc⟩

/-- **Negativity for homology classes.** On a smooth projective complex threefold `W`, a
`ℚ`-divisor with zero class in `H_4(W, ℚ)` all of whose components are exceptional for a
projective birational morphism `f : W ⟶ T` to a normal variety is zero. -/
private theorem eq_zero_of_divisorClass_eq_zero {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [W.Over (Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
    [IsComplexScheme W] {T : Scheme.{0}} [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of ℂ)} (hWp : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (hW3 : topologicalKrullDim W = 3) (hWn : MMP.Mori.IsNormalVariety ℂ (W ↘ Spec (.of ℂ)))
    (hTn : MMP.Mori.IsNormalVariety ℂ sT) (f : W ⟶ T) (hf : f ≫ sT = W ↘ Spec (.of ℂ))
    (hfp : IsProjectiveMorphism f) (hfb : MMP.Mori.IsBirationalMorphism f)
    (F : MMP.Mori.QDivisor W) (hF : divisorClass W F = 0)
    (hexc : ∀ P ∈ F.support,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := W) f.toRationalMap P = none) :
    F = 0 := by
  have hQC := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm F
  have hC := MMP.Mori.QDivisor.isCartierDivisor_cartierIndex_smul hQC
  have hDF := hC.toQDivisor_toDivisor
  have hm : ((F.cartierIndex hQC : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (MMP.Mori.QDivisor.cartierIndex_pos hQC).ne'
  -- the coefficients of the Cartier multiple `D = m F`
  have hcoeff : ∀ P, (hC.toDivisor.coeff P : ℚ) = (F.cartierIndex hQC : ℕ) * F P := fun P => by
    have := congrArg (fun E : MMP.Mori.QDivisor W => MMP.Mori.DivisorWithCoeffs.coeff E P) hDF
    simp only [MMP.Mori.Divisor.coeff_toQDivisor] at this
    rw [this]
    change ((F.cartierIndex hQC : ℕ) : ℤ) • F P = _
    rw [zsmul_eq_mul, Int.cast_natCast]
  have hD0 := eq_zero_of_degreeOn_eq_zero (W ↘ Spec (.of ℂ)) sT hWn hTn f hf hfp hfb
    hC.toDivisor _
    (degreeOn_eq_zero_of_divisorClass_eq_zero hWp hsm hW3 _
      (by rw [hDF, map_zsmul, hF, smul_zero]))
    fun P hP => hexc P <| Finsupp.mem_support_iff.mpr fun h0 =>
      Finsupp.mem_support_iff.mp hP <| by
        have h1 : (hC.toDivisor.coeff P : ℚ) = 0 := (hcoeff P).trans (by rw [h0, mul_zero])
        exact_mod_cast h1
  ext P
  have h := hcoeff P
  rw [hD0] at h
  change F P = 0
  simpa [hm, eq_comm] using h

/-- A point in the support of `∑_{x ∈ s} g_x • p(x)` is `p(x)` for some `x ∈ s`. -/
private lemma exists_mem_eq_of_mem_support_sum_single {ι α : Type*} {p : ι → α} {s : Finset ι}
    {g : ι → ℚ} {a : α} (ha : a ∈ (∑ x ∈ s, g x • Finsupp.single (p x) (1 : ℚ)).support) :
    ∃ x ∈ s, p x = a := by
  by_contra hcon
  push Not at hcon
  apply Finsupp.mem_support_iff.mp ha
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (hcon x hx).symm, smul_zero]

/-- Along an injective `f`, the coefficient of `f (p i)` in the image of `∑_{x ∈ s} g_x • p(x)`
is `g_i`, for `p` injective and `i ∈ s`. -/
private lemma mapDomain_sum_single_apply {ι α β : Type*} {p : ι → α} (hp : Function.Injective p)
    {f : α → β} (hf : Function.Injective f) (s : Finset ι) (g : ι → ℚ) {i : ι} (hi : i ∈ s) :
    Finsupp.mapDomain f (∑ x ∈ s, g x • Finsupp.single (p x) (1 : ℚ)) (f (p i)) = g i := by
  rw [Finsupp.mapDomain_apply_of_injective hf, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (fun h => hx (hp h.symm)), smul_zero]
  · exact fun h => absurd hi h

/-- A relation `[D] = 0` on a threefold `S` lifts along a proper `r : W ⟶ S` which is an
isomorphism over `U ∋ η_P`: the class of the strict transform of `D` is the class of a divisor
supported over the complement of `U`. -/
private theorem exists_divisorClass_mapDomain_eq_of_divisorClass_eq_zero {W S : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsComplexScheme S]
    [IsIntegral W] [IsIntegral S] (hW3 : topologicalKrullDim W = 3)
    (hS3 : topologicalKrullDim S = 3) (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))] [IsProper r]
    (U : S.Opens) [IsIso (r ∣_ U)] (hw : ((r ⁻¹ᵁ U : W.Opens) : Set W).Nonempty)
    (lift : MMP.Mori.PrimeDivisor S → MMP.Mori.PrimeDivisor W)
    (hlift : ∀ P, r (lift P).genericPoint = P.genericPoint)
    (hU : ∀ P : MMP.Mori.PrimeDivisor S, P.genericPoint ∈ U) (D : MMP.Mori.QDivisor S)
    (hD : divisorClass S D = 0) :
    ∃ G : MMP.Mori.QDivisor W, (∀ P ∈ G.support, r P.genericPoint ∉ U) ∧
      divisorClass W (Finsupp.mapDomain lift D) = divisorClass W G := by
  have hres := restrict_eq_zero_of_pushforward_eq_zero r U _ _
    ((pushforward_divisorClass_mapDomain r U lift hlift hU
      (relativeDimension_primeDivisor_genericPoint hS3)
      (relativeDimension_primeDivisor_genericPoint hW3) D).trans hD)
  let Q : Closeds W := ⟨((r ⁻¹ᵁ U : W.Opens) : Set W)ᶜ, (r ⁻¹ᵁ U).isOpen.isClosed_compl⟩
  have hQx : ∀ O : Opens (TopCat.of (UnderlyingSpace ℂ W)),
      (O : Set (UnderlyingSpace ℂ W)) = (UnderlyingSpace.pointsOver (Q : Set W))ᶜ →
      (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) O ((4 : ℕ) : ℤ)).hom
        (divisorClass W (Finsupp.mapDomain lift D)) = 0 := by
    intro O hO
    have hOe : O = Opens.comap (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)).hom
        (pointsOverOpens U) := by
      apply Opens.ext
      rw [hO]
      ext p
      exact Classical.not_not
    subst hOe
    exact hres
  obtain ⟨w, hw⟩ := hw
  obtain ⟨G, hGsupp, hG⟩ := exists_divisorClass_eq_of_restrict_eq_zero Q
    (dimension_vanishingIdeal_le_two hW3 Q fun h => (show w ∈ (Q : Set W) by rw [h]; trivial) hw)
    (exists_primeDivisor_genericPoint_eq hW3) _ hQx
  exact ⟨G, hGsupp, hG⟩

/-- The independence of the contracted divisor classes, given a resolution `r : W ⟶ S` which
is an isomorphism over the smooth locus of `S`. -/
private theorem linearIndependent_divisorClass_of_resolution {S T W : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
    [IsComplexScheme S] [IsComplexScheme T] [IsComplexScheme W]
    [IsIntegral S] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsSeparated (T ↘ Spec (.of ℂ))]
    [IsSeparated (T ↘ Limits.terminal Scheme)]
    (hSn : MMP.Mori.IsNormalVariety ℂ (S ↘ Spec (.of ℂ)))
    (hTn : MMP.Mori.IsNormalVariety ℂ (T ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3) (hTdim : topologicalKrullDim T = 3)
    (q : S ⟶ T) [q.IsOver (Spec (.of ℂ))] (hqb : MMP.Mori.IsBirationalMorphism q)
    (hWproj : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hWsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (hW3 : topologicalKrullDim W = 3)
    (hWn : MMP.Mori.IsNormalVariety ℂ (W ↘ Spec (.of ℂ)))
    (r : W ⟶ S) [r.IsOver (Spec (.of ℂ))] [IsProper r]
    [IsIso (r ∣_ MMP.Mori.smoothLocus (S ↘ Spec (.of ℂ)))] (hrb : MMP.Mori.IsBirationalMorphism r)
    (hw : ((r ⁻¹ᵁ MMP.Mori.smoothLocus (S ↘ Spec (.of ℂ)) : W.Opens) : Set W).Nonempty) :
    LinearIndependent ℚ fun P : {P : MMP.Mori.PrimeDivisor S //
        2 ≤ Order.coheight (q P.genericPoint)} =>
      divisorClass S (Finsupp.single P.1 1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hηU : ∀ P : MMP.Mori.PrimeDivisor S,
      P.genericPoint ∈ MMP.Mori.smoothLocus (S ↘ Spec (.of ℂ)) :=
    fun P => MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hSn P
  have hUB : MMP.Mori.smoothLocus (S ↘ Spec (.of ℂ)) ≤ MMP.Mori.biregularLocus r :=
    le_sSup (show MMP.Mori.IsBiregular r _ from ‹IsIso (r ∣_ _)›)
  choose lift hlift1 hlift2 using fun P : MMP.Mori.PrimeDivisor S =>
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P (hUB (hηU P))
  set DS : MMP.Mori.QDivisor S := ∑ P ∈ s, g P • Finsupp.single P.1 (1 : ℚ) with hDSdef
  obtain ⟨G, hGsupp, hG⟩ := exists_divisorClass_mapDomain_eq_of_divisorClass_eq_zero hW3 hSdim r
    _ hw lift hlift2 hηU DS (by rw [hDSdef, map_sum]; simpa only [map_smul] using hsum)
  set F : MMP.Mori.QDivisor W := Finsupp.mapDomain lift DS - G with hFdef
  have hexcF : ∀ P ∈ F.support, 2 ≤ Order.coheight ((r ≫ q) P.genericPoint) := by
    intro P hP
    rw [Scheme.Hom.comp_apply]
    rcases Finset.mem_union.mp (Finsupp.support_sub hP) with h1 | h2
    · obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h1)
      rw [hDSdef] at hP₀
      obtain ⟨x, -, rfl⟩ := exists_mem_eq_of_mem_support_sum_single (p := Subtype.val) hP₀
      rw [hlift2]
      exact x.2
    · exact two_le_coheight_map q hSdim hTdim _
        (two_le_coheight_of_notMem_smoothLocus hSn _ (hGsupp P h2))
  have hF0 : F = 0 := eq_zero_of_divisorClass_eq_zero hWproj hWsm hW3 hWn hTn (r ≫ q)
    (by rw [Category.assoc, comp_over q, comp_over r])
    (IsProjectiveMorphism.of_comp (r ≫ q) (T ↘ Spec (.of ℂ))
      (by rw [Category.assoc, comp_over q, comp_over r]; exact hWproj.isProjective))
    (isBirationalMorphism_comp hrb hqb) F (by rw [hFdef, map_sub, hG, sub_self])
    fun P hP => transformPrimeDivisor_eq_none_of_two_le_coheight _ P (hexcF P hP)
  have hlinj : Function.Injective lift := fun P P' h => by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change MMP.Mori.PrimeDivisor.genericPoint P = MMP.Mori.PrimeDivisor.genericPoint P'
    rw [← hlift2 P, ← hlift2 P', h]
  have hG0 : G (lift i.1) = 0 := by
    by_contra h
    exact hGsupp _ (Finsupp.mem_support_iff.mpr h) (by rw [hlift2]; exact hηU i.1)
  have hcoef : F (lift i.1) = g i := by
    rw [hFdef, Finsupp.sub_apply, hG0, sub_zero, hDSdef]
    exact mapDomain_sum_single_apply Subtype.val_injective hlinj s g hi
  rw [hF0] at hcoef
  exact hcoef.symm

/-- **Contracted divisors have independent classes**, indexed by generic points. For a
birational morphism `q : S ⟶ T` over `ℂ` of normal projective threefolds, the classes
`[P] ∈ H_4(S, ℚ)` of the prime divisors `P` of `S` whose generic point maps to a point of
coheight at least two are linearly independent over `ℚ`. -/
private theorem linearIndependent_divisorClass_of_two_le_coheight : ∀ {S T : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hS : AlgebraicGeometry.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)))
    (hT : AlgebraicGeometry.IsProjectiveVariety ℂ (T ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3) (hTdim : topologicalKrullDim T = 3)
    (q : S ⟶ T) [q.IsOver (Spec (.of ℂ))] (hqb : MMP.Mori.IsBirationalMorphism q),
    letI := isComplexScheme_of_isProjectiveVariety S hS
    LinearIndependent ℚ fun P : {P : MMP.Mori.PrimeDivisor S //
        2 ≤ Order.coheight (q P.genericPoint)} =>
      divisorClass S (Finsupp.single P.1 1) := by
  intro S T _ _ _ _ _ _ _ _ hS hT hSdim hTdim q _ hqb
  letI hSc : IsComplexScheme S := isComplexScheme_of_isProjectiveVariety S hS
  -- the varieties `S` and `T`
  have hSv : AlgebraicGeometry.IsVariety ℂ (S ↘ Spec (.of ℂ)) := hS.toIsVariety
  have hTv : AlgebraicGeometry.IsVariety ℂ (T ↘ Spec (.of ℂ)) := hT.toIsVariety
  have hSn : MMP.Mori.IsNormalVariety ℂ (S ↘ Spec (.of ℂ)) := ⟨hSv, inferInstance⟩
  have hTn : MMP.Mori.IsNormalVariety ℂ (T ↘ Spec (.of ℂ)) := ⟨hTv, inferInstance⟩
  letI hTc : IsComplexScheme T := isComplexScheme_of_isProjectiveVariety T hT
  -- a resolution `r : W ⟶ S`, an isomorphism over the smooth locus `U` of `S`
  obtain ⟨W, r, hWv, hrp, hrb, hWsm, hriso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution (S ↘ Spec (.of ℂ)) hSv
  set U : S.Opens := MMP.Mori.smoothLocus (S ↘ Spec (.of ℂ)) with hUdef
  haveI : IsIso (r ∣_ U) := hriso
  letI : W.Over (Spec (.of ℂ)) := ⟨r ≫ S ↘ Spec (.of ℂ)⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI hWv' : AlgebraicGeometry.IsVariety ℂ (W ↘ Spec (.of ℂ)) := hWv
  haveI : IsIntegral W := hWv'.toIsIntegral
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of ℂ))
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  haveI hWsmooth : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hWsm
  haveI : IsNormal (Spec (.of ℂ)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed ℂ)
  haveI : IsNormal W := isNormal_of_smooth (W ↘ Spec (.of ℂ))
  haveI : IsProper r := hrp.isProper
  have hWn : MMP.Mori.IsNormalVariety ℂ (W ↘ Spec (.of ℂ)) := ⟨hWv', inferInstance⟩
  have hWproj : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := by
    refine (isProjectiveVariety_iff_isProjectiveMorphism ℂ _).2 ?_
    exact (isProjective_iff_isProjectiveMorphism_of_isAffine _).1
      (IsProjective.comp hrp hS.isProjective.isProjective)
  letI hWc : IsComplexScheme W := isComplexScheme_of_isProjectiveVariety W hWproj
  haveI : IsSeparated (T ↘ Spec (.of ℂ)) := hTv.toIsSeparated
  haveI : IsSeparated (T ↘ Limits.terminal Scheme) := by
    rw [show (T ↘ Limits.terminal Scheme) = (T ↘ Spec (.of ℂ)) ≫
      (Spec (.of ℂ) ↘ Limits.terminal Scheme) from Limits.terminal.hom_ext _ _]
    infer_instance
  -- dimensions
  have hUne : (U : Set S).Nonempty := ⟨genericPoint S, by
    rw [hUdef, MMP.Mori.smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _⟩
  obtain ⟨w₀, -⟩ := (Scheme.homeoOfIso (asIso (r ∣_ U))).surjective ⟨hUne.choose, hUne.choose_spec⟩
  have hw₀ : ((r ⁻¹ᵁ U : W.Opens) : Set W).Nonempty := ⟨w₀.1, w₀.2⟩
  have hW3 : topologicalKrullDim W = 3 := by
    have e1 := (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ W (_ ↘ Spec (.of ℂ)) _
        (TopologicalSpace.Opens.isOpen (r ⁻¹ᵁ U)) hw₀).symm
    have e2 := (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ S (_ ↘ Spec (.of ℂ)) _
        (TopologicalSpace.Opens.isOpen U) hUne).symm
    have e3 := IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (r ∣_ U))).isHomeomorph
    exact (e1.symm.trans (e3.trans e2)).trans hSdim
  exact linearIndependent_divisorClass_of_resolution hSn hTn hSdim hTdim q hqb hWproj hWsm hW3
    hWn r hrb hw₀

end Independence

/-- `ℙ¹_ℂ = Proj ℂ[x₀, x₁]` over `ℂ` through `projToSpecCoeff ℂ 1`. -/
@[reducible] private noncomputable def projectiveLineOver :
    (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
  ⟨projToSpecCoeff ℂ 1⟩

attribute [local instance high] projectiveLineOver

private theorem projectiveLineOver_hom :
    AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ) = projToSpecCoeff ℂ 1 :=
  rfl

private instance : IsComplexScheme (AlgebraicGeometry.Proj (polyGrading ℂ 1)) :=
  isComplexScheme_projectiveSpace 1 rfl

open MMP.Fourfold MMP.Mori
open MMP.Chow (divisorClass)

/-- The complex-scheme structure on an open `O` of a complex scheme `X`, over `ℂ` through
`O ⟶ X`. -/
private noncomputable abbrev opensOver {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (O : X.Opens) :
    O.toScheme.Over (Spec (.of ℂ)) :=
  ⟨O.ι ≫ X ↘ Spec (.of ℂ)⟩

private lemma isComplexScheme_opens {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (O : X.Opens) :
    letI := opensOver O
    IsComplexScheme O.toScheme := by
  letI := opensOver O
  haveI : O.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  exact MMP.isComplexScheme_opens O

/-- A small morphism onto a normal scheme is biregular over every point of coheight at most
one. -/
private theorem mem_biregularLocus_of_isSmallMorphism {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {g : X ⟶ Z} (hg : IsSmallMorphism sX sZ g) {z : Z}
    (hz : Order.coheight z ≤ 1) : z ∈ MMP.Mori.biregularLocus g := by
  haveI := hg.isProper
  haveI := hg.isBirationalMorphism.isDominant
  exact MMP.Positivity.mem_biregularLocus_of_coheight_le_one g
    hg.isBirationalMorphism.functionFieldMap_bijective hg.two_le_codimension hz

/-- The normalization of a prime divisor maps the generic point to the generic point. -/
private theorem primeDivisorNormalization_genericPoint {Y : Scheme.{0}}
    (S : MMP.Mori.PrimeDivisor Y) :
    letI := S.integral
    letI : IsIntegral (primeDivisorNormalizationScheme S) :=
      AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    primeDivisorNormalization S (genericPoint (primeDivisorNormalizationScheme S)) =
      S.genericPoint := by
  letI := S.integral
  letI : IsIntegral (primeDivisorNormalizationScheme S) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hz : genericPoint (primeDivisorNormalizationScheme S) ∈
      genericPoints (primeDivisorNormalizationScheme S) := by
    rw [genericPoints_eq_singleton]; rfl
  have h := Scheme.normalization_mem_genericPoints S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) hz
  rw [genericPoints_eq_singleton] at h
  change S.idealSheaf.subschemeι _ = S.idealSheaf.subschemeι _
  congr 1

/-- The isomorphism `(O ×_B P) ≅ pr⁻¹(O)` for an open `O ⊆ X` and `pr : X ×_B P ⟶ X`, followed by
the inclusion, is compatible with the second projections. -/
private lemma pullbackRestrictIso_hom_ι_snd {X P B : Scheme.{0}} (g : X ⟶ B) (h : P ⟶ B)
    (O : X.Opens) (U : (pullback g h).Opens) (hU : pullback.fst g h ⁻¹ᵁ O = U) :
    ((pullbackRightPullbackFstIso g h O.ι).symm ≪≫ pullbackSymmetry _ _ ≪≫
        pullbackRestrictIsoRestrict (pullback.fst g h) O ≪≫ Scheme.isoOfEq _ hU).hom ≫
      U.ι ≫ pullback.snd g h = pullback.snd (O.ι ≫ g) h := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Scheme.isoOfEq_hom_ι_assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd]

/-- Over `ℂ`, a point has delta-dimension `k` exactly when its closure has dimension `k`. -/
private theorem relativeDimension_eq_iff_topologicalKrullDim_closure {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p] (x : X) (k : ℕ) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction p x = k ↔
      topologicalKrullDim (closure ({x} : Set X)) = k := by
  have h0 := Stacks.Chow.relativeDimension_fieldChowSituation_nonneg ℂ p x
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ p x]
  constructor
  · intro h
    rw [h, Int.toNat_natCast]
  · intro h
    have : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      p x).toNat = k := by exact_mod_cast h
    omega

/-- Cancelling `2 +` in `WithBot ℕ∞`: `2 + c = 3` forces `c = 1`. -/
private lemma eq_one_of_two_add_eq_three {c : ℕ∞}
    (h : ((2 : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 1 := by
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe c =>
    have h2 : ((2 : ℕ) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    have h3 : (3 : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := rfl
    rw [h2, h3, ← WithBot.coe_add, WithBot.coe_inj] at h
    have : 2 + c = 3 := by exact_mod_cast h
    exact_mod_cast (show c = 1 by omega)

/-- Push-forward along a proper map equal to the identity is the identity. -/
private lemma pushforward_apply_of_eq_id {X : TopCat.{0}} (g : X ⟶ X) (hg : IsProperMap g)
    (h : g = 𝟙 X) (j : ℤ) :
    ∀ a, (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg j).hom a = a := by
  subst h
  rw [MMP.borelMooreHomology.pushforward_id]
  exact fun _ => rfl

/-- Under a proper morphism to a threefold over `ℂ`, a point whose closure has image of dimension
at most one maps to a point of coheight at least two. -/
private theorem two_le_coheight_of_topologicalKrullDim_image_le_one {V T : Scheme.{0}}
    [T.Over (Spec (.of ℂ))] [IsIntegral T] [LocallyOfFiniteType (T ↘ Spec (.of ℂ))]
    (hTdim : topologicalKrullDim T = 3) (q : V ⟶ T) [IsProper q] {x : V}
    (hx : topologicalKrullDim (q '' closure ({x} : Set V)) ≤ 1) : 2 ≤ Order.coheight (q x) := by
  have hsum := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
    (T ↘ Spec (.of ℂ)) (q x)).trans hTdim
  have hcl : closure {q x} ⊆ q '' closure ({x} : Set V) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
      (q.isClosedMap _ isClosed_closure)
  have hd : topologicalKrullDim (closure {q x} : Set T) ≤ 1 :=
    (topologicalKrullDim_le_of_subset hcl).trans hx
  by_contra hlt
  have hc : Order.coheight (q x) ≤ 1 := Order.le_of_lt_add_one (by
    simpa [one_add_one_eq_two] using not_le.mp hlt)
  have h3 : (3 : WithBot ℕ∞) ≤ 1 + 1 := by
    rw [← hsum]
    exact add_le_add hd (by exact_mod_cast hc)
  exact absurd h3 (by decide)

/-- **Contracted divisors have independent classes.** For a projective birational morphism
`q : V ⟶ T` over `ℂ` of normal projective threefolds over `ℂ`, the fundamental classes in
`H_4(V, ℚ)` of the prime divisors of `V` contracted by `q` (those whose image has dimension at
most one) are linearly independent over `ℚ`. -/
private theorem linearIndependent_fundamentalClass_of_contracted {V T : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [T.Over (Spec (.of ℂ))]
    (hV : MMP.Mori.IsNormalVariety ℂ (V ↘ Spec (.of ℂ)) ∧
      AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim V = ((2 + 1 : ℕ) : WithBot ℕ∞))
    (hT : MMP.Mori.IsNormalVariety ℂ (T ↘ Spec (.of ℂ)) ∧
      AlgebraicGeometry.IsProjectiveVariety ℂ (T ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim T = ((2 + 1 : ℕ) : WithBot ℕ∞))
    (q : V ⟶ T) [q.IsOver (Spec (.of ℂ))] (hq : IsProjective q)
    (hqb : MMP.Mori.IsBirationalMorphism q) :
    LinearIndependent ℚ (fun x : {x : V // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) x = 2 ∧
        topologicalKrullDim (q '' closure ({x} : Set V)) ≤ 1} ↦
      MMP.Analytic.fundamentalClass x.1 x.2.1) := by
  haveI : IsIntegral V := hV.1.1.toIsIntegral
  haveI : IsNormal V := hV.1.2
  haveI : LocallyOfFiniteType (V ↘ Spec (.of ℂ)) := hV.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of ℂ))
  haveI : IsIntegral T := hT.1.1.toIsIntegral
  haveI : IsNormal T := hT.1.2
  haveI : LocallyOfFiniteType (T ↘ Spec (.of ℂ)) := hT.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of ℂ))
  haveI : IsProper q := hq.isProper
  haveI : IsSeparated (V ↘ Spec (.of ℂ)) := hV.1.1.toIsSeparated
  have hVdim : topologicalKrullDim V = 3 := hV.2.2
  have hTdim : topologicalKrullDim T = 3 := hT.2.2
  have hL := linearIndependent_divisorClass_of_two_le_coheight hV.2.1 hT.2.1 hVdim hTdim q hqb
  -- a point of delta-dimension `2` of `V` is the generic point of a prime divisor
  let ι := {x : V // Stacks.Chow.relativeDimension
    (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) x = 2 ∧
    topologicalKrullDim (q '' closure ({x} : Set V)) ≤ 1}
  have hcoh : ∀ x : ι, Order.coheight x.1 = 1 := fun x ↦ by
    have h := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (V ↘ Spec (.of ℂ)) x.1).trans hVdim
    rw [(relativeDimension_eq_iff_topologicalKrullDim_closure _ x.1 2).1 x.2.1] at h
    exact eq_one_of_two_add_eq_three h
  -- whose image is a point of coheight at least two when it is contracted
  have hcohq : ∀ x : ι, 2 ≤ Order.coheight (q x.1) := fun x ↦
    two_le_coheight_of_topologicalKrullDim_image_le_one hTdim q x.2.2
  let φ : ι → {P : MMP.Mori.PrimeDivisor V // 2 ≤ Order.coheight (q P.genericPoint)} := fun x ↦
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hcoh x),
      (congrArg (fun y ↦ 2 ≤ Order.coheight (q y))
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _)).mpr (hcohq x)⟩
  have hφg : ∀ x, (φ x).1.genericPoint = x.1 := fun x ↦
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ (hcoh x)
  have hφ : Function.Injective φ := fun x x' h ↦
    Subtype.ext (by rw [← hφg, ← hφg x', h])
  -- the comparison of the two models of `H_4(V, ℚ)`
  let H := (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := V).continuous⟩)
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := V)).isProperMap
    ((2 * 2 : ℕ) : ℤ)).hom
  have key : ∀ x : ι,
      H (MMP.Analytic.fundamentalClass x.1 x.2.1) = divisorClass V (Finsupp.single (φ x).1 1) := by
    intro x
    let e := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := V)
    have h1 : H (MMP.Analytic.fundamentalClass x.1 x.2.1) = Chow.pointCycleClass ℚ x.1 x.2.1 := by
      rw [MMP.Analytic.fundamentalClass_eq]
      change ((MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) _ _ _ ≫
        MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) _ _ _).hom _) = _
      rw [← MMP.borelMooreHomology.pushforward_comp]
      exact pushforward_apply_of_eq_id _ _ (TopCat.ext fun y ↦ e.apply_symm_apply y) _ _
    have hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (V ↘ Spec (.of ℂ)) (φ x).1.genericPoint = (2 : ℕ) := by
      rw [hφg]
      exact x.2.1
    have hpt : ∀ (y : V) (hy : y = x.1) (h : Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) y = (2 : ℕ)),
        Chow.pointCycleClass ℚ y h = Chow.pointCycleClass ℚ x.1 x.2.1 := by
      rintro _ rfl _
      rfl
    rw [h1, Chow.divisorClass_single hx, hpt _ (hφg x)]
  refine LinearIndependent.of_comp H ?_
  convert hL.comp φ hφ using 1
  exact funext key

/-- Cancelling `+ 1` in `WithBot ℕ∞`: `d + 1 = 2` forces `d = 1`. -/
private lemma eq_one_of_add_one_eq_two {d : WithBot ℕ∞}
    (h : d + ((1 : ℕ∞) : WithBot ℕ∞) = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by norm_cast)
    | coe d =>
      have h2 : ((2 : ℕ∞) : WithBot ℕ∞) = 2 := rfl
      rw [← h2, ← WithBot.coe_add, WithBot.coe_inj] at h
      have h' : d + 1 = 2 := by exact_mod_cast h
      exact_mod_cast (show d = 1 by omega)

/-- Cancelling `1 +` in `WithBot ℕ∞`: `1 + c = 2` forces `c = 1`. -/
private lemma eq_one_of_one_add_eq_two {c : ℕ∞} (h : (1 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 2) :
    c = 1 :=
  WithBot.coe_eq_one.mp (eq_one_of_add_one_eq_two (by rwa [add_comm] at h))

/-- The product map `g × id : X × P ⟶ X' × P` of a morphism `g` over `ℂ` is over `ℂ`. -/
private lemma pullbackMap_id_comp_over {X X' P : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] [P.Over (Spec (.of ℂ))] (g : X ⟶ X')
    (hg : g ≫ X' ↘ Spec (.of ℂ) = X ↘ Spec (.of ℂ)) :
    pullback.map _ _ _ _ g (𝟙 P) (𝟙 _) (by simp [hg]) (by simp) ≫
      ((CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ)) (P ↘ Spec (.of ℂ)) : Scheme) ↘
        Spec (.of ℂ)) =
      (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ)) (P ↘ Spec (.of ℂ)) : Scheme) ↘
        Spec (.of ℂ) := by
  change _ ≫ pullback.snd _ _ ≫ _ = pullback.snd _ _ ≫ _
  simp only [pullback.lift_snd_assoc, Category.comp_id]

/-- For a variety `X` over `ℂ`, the preimage under `X × ℙ¹ ⟶ X` of a closed irreducible set `T`
is irreducible, of dimension `dim T + 1`. -/
private theorem isIrreducible_preimage_fst_and_topologicalKrullDim_eq {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [QuasiCompact (X ↘ Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))] {T : Set X}
    (hT : IsClosed T) (hTi : IsIrreducible T) :
    IsIrreducible (pullback.fst (X ↘ Spec (.of ℂ))
        (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' T) ∧
      topologicalKrullDim (pullback.fst (X ↘ Spec (.of ℂ))
        (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' T) =
        topologicalKrullDim T + 1 := by
  have hcomp := isVariety_product_projectiveLine_and_irreducibleComponents_preimage.2 X
  rw [← projectiveLineOver_hom] at hcomp
  have hmax : Maximal (fun T' ↦ IsIrreducible T' ∧ T' ⊆ T) T := ⟨⟨hTi, le_rfl⟩, fun _ h _ ↦ h.2⟩
  obtain ⟨hset, -, hdim⟩ := hcomp T hT
  refine ⟨?_, hdim T hmax⟩
  have hmem : pullback.fst (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' T ∈
        {T' | Maximal (fun T'' ↦ IsIrreducible T'' ∧ T'' ⊆ pullback.fst (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' T) T'} := by
    rw [hset]
    exact ⟨T, hmax, rfl⟩
  exact hmem.1.1

/-- A prime divisor `P` of `X` is determined by the preimage `P × ℙ¹` of its support. -/
private theorem primeDivisor_eq_of_preimage_fst_support_eq {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] {P P' : MMP.Mori.PrimeDivisor X}
    (h : pullback.fst (X ↘ Spec (.of ℂ))
        (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' P.support =
      pullback.fst (X ↘ Spec (.of ℂ)) (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹'
        P'.support) : P = P' := by
  haveI : Surjective (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hs : P.support = P'.support := (Set.preimage_injective.mpr (pullback.fst (X ↘ Spec (.of ℂ))
    (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))).surjective) h
  have hP : IsGenericPoint P.genericPoint P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
  have hP' : IsGenericPoint P'.genericPoint P.support := by
    rw [hs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP.eq hP')

/-- In a noetherian integral scheme, only finitely many prime divisors lie in a proper closed
subset. -/
private theorem finite_setOf_support_subset {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    {P : MMP.Mori.PrimeDivisor X | P.support ⊆ Z}.Finite := by
  haveI : IsNoetherian X := ⟨⟩
  refine (MMP.Mori.finite_setOf_genericPoint_mem hZ fun x hx h0 ↦ hZne ?_).subset fun P hP ↦ ?_
  · have hη : genericPoint X ⤳ x := (genericPoint_spec _).specializes (Set.mem_univ x)
    have hxη : x = genericPoint X :=
      ((Scheme.le_iff_specializes.mp
        (Order.coheight_eq_zero.mp h0 (Scheme.le_iff_specializes.mpr hη))).antisymm hη).eq
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← hxη]
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
  · exact hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)

/-- On a surface `X` over `ℂ`, a surface of `X × ℙ¹` inside `Z × ℙ¹`, for `Z ⊊ X` closed, is
`P × ℙ¹` for a prime divisor `P` of `X` inside `Z`. -/
private theorem exists_primeDivisor_closure_eq_preimage_fst {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [QuasiCompact (X ↘ Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ))]
    (hX : topologicalKrullDim X = 2) {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ)
    {y : (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme)}
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
        (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) y = 2)
    (hyZ : y ∈ pullback.fst (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' Z) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.support ⊆ Z ∧ closure ({y} : Set _) =
      pullback.fst (X ↘ Spec (.of ℂ)) (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹'
        P.support := by
  set pr := pullback.fst (X ↘ Spec (.of ℂ))
    (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
  have hCirr : IsIrreducible (closure ({y} : Set _)) := isIrreducible_singleton.closure
  have hCd : topologicalKrullDim (closure ({y} : Set _)) = 2 :=
    (relativeDimension_eq_iff_topologicalKrullDim_closure _ y 2).1 hy
  have hC : closure ({y} : Set _) ⊆ pr ⁻¹' Z :=
    closure_minimal (Set.singleton_subset_iff.mpr hyZ) (hZ.preimage pr.continuous)
  set T := closure (pr '' closure ({y} : Set _))
  have hTirr : IsIrreducible T := (hCirr.image pr pr.continuous.continuousOn).closure
  have hTcl : IsClosed T := isClosed_closure
  have hTZ : T ⊆ Z := closure_minimal (Set.image_subset_iff.mpr hC) hZ
  have hCT : closure ({y} : Set _) ⊆ pr ⁻¹' T := fun x hx ↦ subset_closure ⟨x, hx, rfl⟩
  have hTle : topologicalKrullDim T ≤ 1 := by
    refine Order.le_of_lt_succ (show _ < (2 : WithBot ℕ∞) from ?_)
    rw [← hX]
    refine MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ hTcl
      (fun h ↦ hZne (Set.eq_univ_of_univ_subset (h ▸ hTZ))) ?_
    exact ne_top_of_le_ne_top (by rw [hX]; exact WithBot.coe_injective.ne (ENat.coe_ne_top 2))
      (topologicalKrullDim_subspace_le _ _)
  obtain ⟨hpirr, hpd⟩ := isIrreducible_preimage_fst_and_topologicalKrullDim_eq hTcl hTirr
  have hTle2 : topologicalKrullDim T + 1 ≤ 2 :=
    calc topologicalKrullDim T + 1 ≤ 1 + 1 := by gcongr
      _ = 2 := one_add_one_eq_two
  have hCeq : closure ({y} : Set _) = pr ⁻¹' T := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hpirr isClosed_closure hCT hne
      (by
        rw [hpd]
        exact ne_top_of_le_ne_top (WithBot.coe_injective.ne (ENat.coe_ne_top 2)) hTle2)
    rw [hCd, hpd] at hlt
    exact absurd (lt_of_lt_of_le hlt hTle2) (lt_irrefl _)
  have hTd : topologicalKrullDim T = 1 := by
    rw [← hCeq, hCd] at hpd
    exact eq_one_of_add_one_eq_two hpd.symm
  have hgen := hTirr.isGenericPoint_genericPoint_closure
  rw [hTcl.closure_eq] at hgen
  have hcoh : Order.coheight hTirr.genericPoint = 1 := by
    have h := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (X ↘ Spec (.of ℂ)) hTirr.genericPoint).trans hX
    rw [hgen.def, hTd] at h
    exact eq_one_of_one_add_eq_two h
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hgen.def]
    exact hTZ
  · rw [hCeq, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hgen.def]

/-- On a surface `X` over `ℂ` and for `Z ⊊ X` closed, the surfaces of `X × ℙ¹` inside `Z × ℙ¹`
are finitely many, as many as the prime divisors of `X` inside `Z`. -/
private theorem finite_and_ncard_eq_ncard_setOf_support_subset {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [QuasiCompact (X ↘ Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ))]
    (hX : topologicalKrullDim X = 2) {Z : Set X} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    {y | Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ))
          y = 2 ∧
        y ∈ pullback.fst (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' Z}.Finite ∧
      {y | Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ))
          y = 2 ∧
        y ∈ pullback.fst (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' Z}.ncard =
        {P : MMP.Mori.PrimeDivisor X | P.support ⊆ Z}.ncard := by
  set pr := pullback.fst (X ↘ Spec (.of ℂ))
    (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have F1 : ∀ P : MMP.Mori.PrimeDivisor X, P.support ⊆ Z →
      ∃ y, (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
          (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ))
          y = 2 ∧
        y ∈ pr ⁻¹' Z) ∧ closure ({y} : Set _) = pr ⁻¹' P.support := by
    intro P hP
    have hZP : IsClosed P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    have hdP : topologicalKrullDim P.support = 1 := by
      have h := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
        (X ↘ Spec (.of ℂ)) P.genericPoint).trans hX
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
      exact eq_one_of_add_one_eq_two h
    obtain ⟨hirr', hd⟩ := isIrreducible_preimage_fst_and_topologicalKrullDim_eq hZP
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact isIrreducible_singleton.closure)
    have hgen := hirr'.isGenericPoint_genericPoint_closure
    rw [(hZP.preimage pr.continuous).closure_eq] at hgen
    refine ⟨hirr'.genericPoint, ⟨?_, Set.preimage_mono hP hgen.mem⟩, hgen.def⟩
    refine (relativeDimension_eq_iff_topologicalKrullDim_closure _ _ 2).2 ?_
    rw [hgen.def, hd, hdP]
    rfl
  have F3 : ∀ y y' : (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) : Scheme),
      closure ({y} : Set _) = closure {y'} → y = y' := fun y y' h ↦
    isGenericPoint_closure.eq (h ▸ isGenericPoint_closure)
  refine ⟨(((finite_setOf_support_subset hZ hZne).image fun P ↦ pr ⁻¹' P.support).preimage
    (f := fun y ↦ closure ({y} : Set _)) (fun y _ y' _ h ↦ F3 y y' h)).subset fun y hy ↦ ?_, ?_⟩
  · obtain ⟨P, hP, hCP⟩ := exists_primeDivisor_closure_eq_preimage_fst hX hZ hZne hy.1 hy.2
    exact ⟨P, hP, hCP.symm⟩
  symm
  refine Set.ncard_congr (fun P hP ↦ (F1 P hP).choose) (fun P hP ↦ (F1 P hP).choose_spec.1)
    (fun P P' hP hP' h ↦ primeDivisor_eq_of_preimage_fst_support_eq ?_) (fun y hy ↦ ?_)
  · rw [← (F1 P hP).choose_spec.2, ← (F1 P' hP').choose_spec.2, h]
  · obtain ⟨P, hP, hCP⟩ := exists_primeDivisor_closure_eq_preimage_fst hX hZ hZne hy.1 hy.2
    exact ⟨P, hP, F3 _ _ ((F1 P hP).choose_spec.2.trans hCP.symm)⟩

/-- **The classes over the bad branches.** For the normalization `ν : S^ν ⟶ S ⊆ Y` of a prime
divisor of a projective variety over `ℂ`, a normal projective surface, and a projective birational
morphism `σ : S^ν ⟶ T` to a normal projective surface contracting exactly the prime divisors `P`
of `S^ν` with `ν(P) ⊆ W`, the classes of the surfaces of `S^ν × ℙ¹` inside `ν⁻¹(W) × ℙ¹` span a
space of dimension the number of these `P`: those surfaces are the `P × ℙ¹`, and they are
contracted by `σ × id`. -/
private theorem finrank_span_fundamentalClass_eq_badBranchCount
    {Y T : Scheme.{0}} {s : Y ⟶ Spec (.of ℂ)} {t : T ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ s)
    (S : MMP.Mori.PrimeDivisor Y) (W : Set Y) (hW : IsClosed W)
    (hSν : MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization S ≫ s) ∧
      MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization S ≫ s) ∧
      topologicalKrullDim (primeDivisorNormalizationScheme S) = 2)
    (hT : MMP.Mori.IsProjectiveVariety ℂ t ∧ MMP.Mori.IsNormalVariety ℂ t ∧
      topologicalKrullDim T = 2)
    (σ : primeDivisorNormalizationScheme S ⟶ T) (hσp : IsProjectiveMorphism σ)
    (hσb : IsBirationalMorphism σ) (hσt : σ ≫ t = primeDivisorNormalization S ≫ s)
    (hWne : primeDivisorNormalization S ⁻¹' W ≠ Set.univ)
    (hcontr : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      (∃ x, σ '' P.support = {x}) ↔ primeDivisorNormalization S '' P.support ⊆ W) :
    letI := primeDivisorNormalizationOver s S
    haveI := isComplexScheme_primeDivisorNormalizationScheme s hY S
    Module.finrank ℚ (Submodule.span ℚ (Set.range fun y : {y : (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) //
        Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) y = 2 ∧
          y ∈ pullback.fst (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ))
            (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) ⁻¹' (primeDivisorNormalization S ⁻¹' W)} ↦
        MMP.Analytic.fundamentalClass y.1 y.2.1)) =
      badBranchCount S W := by
  letI := primeDivisorNormalizationOver s S
  haveI := isComplexScheme_primeDivisorNormalizationScheme s hY S
  set pr := pullback.fst (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ))
    (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
  set Cset : Set (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) := {y |
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) y = 2 ∧ y ∈ pr ⁻¹' (primeDivisorNormalization S ⁻¹' W)}
  haveI : IsIntegral (primeDivisorNormalizationScheme S) := hSν.2.1.1.toIsIntegral
  haveI : LocallyOfFiniteType (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ)) :=
    hSν.2.1.1.toLocallyOfFiniteType
  haveI : IsSeparated (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ)) :=
    hSν.2.1.1.toIsSeparated
  haveI : QuasiCompact (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ)) :=
    hSν.2.1.1.toQuasiCompact
  have hsp := isNormalProjectiveVariety_product_projectiveSpace_one ℂ (n := 2) hSν.2.1 hSν.1
    hSν.2.2
  rw [← projectiveLineOver_hom] at hsp
  haveI : LocallyOfFiniteType ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) :=
    hsp.1.1.1.toLocallyOfFiniteType
  have hW' : IsClosed (primeDivisorNormalization S ⁻¹' W) :=
    hW.preimage (primeDivisorNormalization S).continuous
  obtain ⟨hCfin, hcard⟩ := finite_and_ncard_eq_ncard_setOf_support_subset hSν.2.2 hW' hWne
  have F5 : LinearIndependent ℚ (fun y : Cset ↦ MMP.Analytic.fundamentalClass y.1 y.2.1) := by
    letI : T.Over (Spec (.of ℂ)) := ⟨t⟩
    haveI : σ.IsOver (Spec (.of ℂ)) := ⟨hσt⟩
    haveI : IsIntegral T := hT.2.1.1.toIsIntegral
    haveI : IsSeparated (T ↘ Spec (.of ℂ)) := hT.2.1.1.toIsSeparated
    haveI : LocallyOfFiniteType (T ↘ Spec (.of ℂ)) := hT.2.1.1.toLocallyOfFiniteType
    haveI : QuasiCompact (T ↘ Spec (.of ℂ)) := hT.2.1.1.toQuasiCompact
    haveI : IsProper σ := hσp.isProjective.isProper
    let Q : (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ⟶
        (CategoryTheory.Limits.pullback (T ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) :=
      pullback.map _ _ _ _ σ (𝟙 _) (𝟙 _) (by simp) (by simp)
    obtain ⟨hTP, hQp, hQb, hQim⟩ := hsp.2 σ hT.2.1 hT.1 hT.2.2 hσp.isProjective hσb
    haveI : Q.IsOver (Spec (.of ℂ)) := ⟨pullbackMap_id_comp_over σ hσt⟩
    have hcon : ∀ y ∈ Cset, topologicalKrullDim (Q '' closure ({y} : Set (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme))) ≤ 1 := by
      intro y hy
      obtain ⟨P, hP, hCP⟩ :=
        exists_primeDivisor_closure_eq_preimage_fst hSν.2.2 hW' hWne hy.1 hy.2
      obtain ⟨x, hx⟩ := (hcontr P).mpr (Set.image_subset_iff.mpr hP)
      have hZ : IsClosed P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
      have hirr : IsIrreducible P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have hxcl : IsClosed ({x} : Set T) := hx ▸ σ.isClosedMap _ hZ
      rw [hCP]
      change topologicalKrullDim (Q '' _) ≤ 1
      rw [hQim P.support hZ hirr, hx,
        (isIrreducible_preimage_fst_and_topologicalKrullDim_eq hxcl isIrreducible_singleton).2]
      calc topologicalKrullDim ({x} : Set T) + 1 ≤ 0 + 1 := by
            gcongr; exact topologicalKrullDim_zero_of_discreteTopology _
        _ = 1 := zero_add 1
    let g : Cset → {y : (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) y = 2 ∧
        topologicalKrullDim (Q '' closure ({y} : Set (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme))) ≤ 1} :=
      fun y ↦ ⟨y.1, y.2.1, hcon y.1 y.2⟩
    exact (linearIndependent_fundamentalClass_of_contracted hsp.1 hTP Q hQp hQb).comp g
      fun y y' h ↦ Subtype.ext (congrArg (fun z ↦ z.1) h)
  haveI : Fintype Cset := hCfin.fintype
  change Module.finrank ℚ (Submodule.span ℚ (Set.range fun y : Cset ↦
    MMP.Analytic.fundamentalClass y.1 y.2.1)) = _
  rw [finrank_span_eq_card F5, ← Nat.card_eq_fintype_card]
  refine hcard.trans ?_
  simp only [badBranchCount, Set.image_subset_iff]

/-- **One sign of the rank identity.** For the normalization `S^ν` of a prime divisor `S` of a
projective threefold `Y` over `ℂ`, a projective birational morphism `σ : S^ν ⟶ T` to a normal
projective surface which contracts exactly the prime divisors of `S^ν` lying over `W`, and an
open `V ⊆ T` with `σ⁻¹(V) = O = S^ν ∖ ν⁻¹(W)` nonempty, `ρ^□(S^ν) = ρ_2(O × ℙ¹) + e`, `e` the
number of prime divisors `P` of `S^ν` with `ν(P) ⊆ W`. -/
private theorem boxedSurfaceRank_eq_cycleRank_add_badBranchCount
    {Y T : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {s : Y ⟶ Spec (.of ℂ)} {t : T ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ s) (hYdim : topologicalKrullDim Y = 3)
    (S : MMP.Mori.PrimeDivisor Y) (W : Set Y) (hW : IsClosed W)
    (hSν : MMP.Mori.IsProjectiveVariety ℂ (primeDivisorNormalization S ≫ s) ∧
      MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization S ≫ s) ∧
      topologicalKrullDim (primeDivisorNormalizationScheme S) = 2)
    (hT : MMP.Mori.IsProjectiveVariety ℂ t ∧ MMP.Mori.IsNormalVariety ℂ t ∧
      topologicalKrullDim T = 2)
    (σ : primeDivisorNormalizationScheme S ⟶ T) (hσp : IsProjectiveMorphism σ)
    (hσb : IsBirationalMorphism σ) (hσt : σ ≫ t = primeDivisorNormalization S ≫ s)
    (V : T.Opens) (hV : ((σ ⁻¹ᵁ V : Set _) = (primeDivisorNormalization S ⁻¹' W)ᶜ))
    (hO : (σ ⁻¹ᵁ V : Set (primeDivisorNormalizationScheme S)).Nonempty)
    (hcontr : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      (∃ x, σ '' P.support = {x}) ↔ primeDivisorNormalization S '' P.support ⊆ W) :
    letI := primeDivisorNormalizationOver s S
    haveI := isComplexScheme_primeDivisorNormalizationScheme s hY S
    letI := opensOver (σ ⁻¹ᵁ V)
    haveI := isComplexScheme_opens (σ ⁻¹ᵁ V)
    boxedSurfaceRank (primeDivisorNormalizationScheme S) =
      MMP.Analytic.cycleRank ((CategoryTheory.Limits.pullback ((σ ⁻¹ᵁ V).toScheme ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) 2 +
        badBranchCount S W := by
  letI := primeDivisorNormalizationOver s S
  haveI := isComplexScheme_primeDivisorNormalizationScheme s hY S
  letI := opensOver (σ ⁻¹ᵁ V)
  haveI := isComplexScheme_opens (σ ⁻¹ᵁ V)
  have hprod := (isNormalProjectiveVariety_product_projectiveSpace_one ℂ (n := 2) hSν.2.1 hSν.1
    hSν.2.2).1
  rw [← projectiveLineOver_hom] at hprod
  let pr := pullback.fst (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ))
    (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
  let A : Closeds ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) :=
    ⟨pr ⁻¹' (primeDivisorNormalization S ⁻¹' W),
      (hW.preimage (primeDivisorNormalization S).continuous).preimage pr.continuous⟩
  have hA : topologicalKrullDim A.1 ≤ (2 : ℕ) := by
    haveI := hprod.1.1.toIsIntegral
    haveI : Surjective (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
      ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
    obtain ⟨x, hx⟩ := hO
    obtain ⟨y, hy⟩ := pr.surjective x
    have hne : A.1 ≠ Set.univ := by
      intro h
      have hyA : y ∈ A.1 := h ▸ Set.mem_univ y
      have : x ∈ primeDivisorNormalization S ⁻¹' W := hy ▸ hyA
      rw [hV] at hx
      exact hx this
    have hlt := MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ A.2 hne
      (ne_top_of_le_ne_top (by rw [hprod.2.2]; exact WithBot.coe_injective.ne (ENat.coe_ne_top 3))
        (topologicalKrullDim_subspace_le _ _))
    rw [hprod.2.2] at hlt
    exact Order.le_of_lt_succ hlt
  letI := opensOver A.compl
  haveI : (Scheme.Opens.ι
      (X := (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) A.compl).IsOver
      (Spec (.of ℂ)) := ⟨rfl⟩
  haveI := isComplexScheme_opens A.compl
  have h1 := MMP.Analytic.cycleRank_eq_cycleRank_compl_add_finrank_span _ hprod.2.1 A.2 hA
    A.compl rfl
  have h2 :
      letI := opensOver A.compl
      haveI := isComplexScheme_opens A.compl
      MMP.Analytic.cycleRank (Scheme.Opens.toScheme (X := (CategoryTheory.Limits.pullback (_ ↘ Spec (.of ℂ)) (_ ↘ Spec (.of ℂ)) : Scheme)) A.compl) 2 =
        MMP.Analytic.cycleRank ((CategoryTheory.Limits.pullback ((σ ⁻¹ᵁ V).toScheme ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) 2 := by
    let U : ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)).Opens := A.compl
    letI := opensOver U
    haveI := isComplexScheme_opens U
    have hO' : pr ⁻¹ᵁ (σ ⁻¹ᵁ V) = U := by
      ext y
      change pr y ∈ ((σ ⁻¹ᵁ V : Set _)) ↔ y ∈ (A.1)ᶜ
      rw [hV]
      rfl
    let φ : (CategoryTheory.Limits.pullback ((σ ⁻¹ᵁ V).toScheme ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ≅ U.toScheme :=
      (pullbackRightPullbackFstIso _ _ (σ ⁻¹ᵁ V).ι).symm ≪≫ pullbackSymmetry _ _ ≪≫
        pullbackRestrictIsoRestrict pr (σ ⁻¹ᵁ V) ≪≫ Scheme.isoOfEq _ hO'
    have hφ : φ.hom ≫ (U.toScheme ↘ Spec (.of ℂ)) =
        (CategoryTheory.Limits.pullback ((σ ⁻¹ᵁ V).toScheme ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ) :=
      (reassoc_of% (pullbackRestrictIso_hom_ι_snd
        (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ)) (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
        (σ ⁻¹ᵁ V) U hO')) (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
    exact ((MMP.Analytic.cycleRank_eq_of_iso φ hφ).2.2.2 2).symm
  have h3 : Module.finrank ℚ (Submodule.span ℚ (Set.range fun y : {y : (CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) //
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        ((CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ)) ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme) ↘ Spec (.of ℂ)) y = 2 ∧ y ∈ A.1} ↦
      MMP.Analytic.fundamentalClass y.1 y.2.1)) = badBranchCount S W := by
    refine finrank_span_fundamentalClass_eq_badBranchCount hY S W hW hSν hT σ hσp hσb hσt ?_
      hcontr
    obtain ⟨x, hx⟩ := hO
    intro h
    rw [hV] at hx
    exact hx (h ▸ Set.mem_univ x)
  show MMP.Analytic.cycleRank (CategoryTheory.Limits.pullback
      (primeDivisorNormalizationScheme S ↘ Spec (.of ℂ))
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))) 2 = _
  rw [h1, h2]
  exact congrArg _ h3

/-- Isomorphic schemes over `ℂ` have the same `ρ_2(X × ℙ¹)`. -/
private theorem cycleRank_product_eq_of_iso {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme X'] (e : X ≅ X')
    (he : e.hom ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) :
    MMP.Analytic.cycleRank ((CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
        ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) 2 =
      MMP.Analytic.cycleRank ((CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ))
        ((AlgebraicGeometry.Proj (polyGrading ℂ 1)) ↘ Spec (.of ℂ)) : Scheme)) 2 :=
  (MMP.Analytic.cycleRank_eq_of_iso
    (asIso (pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by simp [he]) (by simp)))
    (pullbackMap_id_comp_over e.hom he)).2.2.2 2

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- In a threefold step diagram with both morphisms small, the normalization of a prime divisor of
the base meets the preimage of the common biregular locus. -/
private theorem nonempty_preimage_commonBiregularLocus
    {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : MMP.Mori.Divisor Xm} {B : MMP.Mori.QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    (D : MMP.Mori.PrimeDivisor Z) :
    (primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp :
      Set (primeDivisorNormalizationScheme D)).Nonempty := by
  have hZ := h.isNormalVariety_target
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := D.integral
  have hcoh : Order.coheight D.genericPoint ≤ 1 :=
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D).le
  have hξ : D.genericPoint ∈ commonBiregularLocus fm fp :=
    ⟨mem_biregularLocus_of_isSmallMorphism hm hcoh,
      mem_biregularLocus_of_isSmallMorphism h.isSmallMorphism_plus hcoh⟩
  letI : IsIntegral (primeDivisorNormalizationScheme D) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme D.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hT : genericPoint (primeDivisorNormalizationScheme D) ∈
      primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp := by
    rw [Scheme.Hom.mem_preimage, primeDivisorNormalization_genericPoint]
    exact hξ
  exact ⟨_, hT⟩

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **Rank difference.** For a threefold step diagram `Y⁻ → Z ← Y⁺` (by `f^±`) in which both
morphisms are small, a prime divisor `S⁻` of `Y⁻` and its strict transform `S⁺` on `Y⁺`,
`ρ^□((S⁻)^ν) - ρ^□((S⁺)^ν) = e⁻(S⁻) - e⁺(S⁻)`, where `ρ^□` is
`MMP.Fourfold.boxedSurfaceRank` and `e^±` are the bad branch counts
`MMP.Fourfold.badBranchCount` of `S^±` on the bad loci `W^±`. -/
@[mmp "lem_mmp_indexd_rank_difference"]
public theorem boxedSurfaceRank_sub_boxedSurfaceRank_eq_badBranchCount_sub_badBranchCount
    {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : MMP.Mori.Divisor Xm} {B : MMP.Mori.QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {Sm : MMP.Mori.PrimeDivisor Xm} {Sp : MMP.Mori.PrimeDivisor Xp}
    (hS : flipTransformPrimeDivisor fm fp Sm = some Sp) :
    letI := primeDivisorNormalizationOver sXm Sm
    letI := primeDivisorNormalizationOver sXp Sp
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus Sm
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus Sp
    (boxedSurfaceRank (primeDivisorNormalizationScheme Sm) : ℤ) -
        boxedSurfaceRank (primeDivisorNormalizationScheme Sp) =
      (badBranchCount Sm (badLocusMinus fm fp) : ℤ) - badBranchCount Sp (badLocusPlus fm fp) := by
  obtain ⟨hSm, hSp, D, hD, hDν, σm, σp, ⟨hσmP, hσmB, hσm, hOm, hσmI⟩, ⟨hσpP, hσpB, hσp, hOp, -⟩,
    e, he⟩ := exists_normalization_hom_isIso_restrict_commonBiregularLocus h hm hS
  have hc := image_eq_singleton_iff_image_subset_badLocus h hm hS hD
  have hOmne : (σm ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp :
      Set (primeDivisorNormalizationScheme Sm)).Nonempty := by
    obtain ⟨y, hy⟩ := nonempty_preimage_commonBiregularLocus h hm D
    haveI := hσmI
    exact ⟨_, ((inv (σm ∣_ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp)) ⟨y, hy⟩).2⟩
  have hOpne : (σp ⁻¹ᵁ primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp :
      Set (primeDivisorNormalizationScheme Sp)).Nonempty := by
    obtain ⟨x, hx⟩ := hOmne
    exact ⟨_, (e.hom.base ⟨x, hx⟩).2⟩
  generalize primeDivisorNormalization D ⁻¹ᵁ commonBiregularLocus fm fp = V
    at hOm hOp e he hOmne hOpne
  have hm' := boxedSurfaceRank_eq_cycleRank_add_badBranchCount h.isProjectiveVariety_minus
    h.dim_minus Sm _ (badLocusMinus fm fp).isClosed hSm hDν σm hσmP hσmB
    (by rw [← Category.assoc, hσm, Category.assoc, h.comp_eq_minus]) V hOm hOmne (hc.1 σm hσm)
  have hp' := boxedSurfaceRank_eq_cycleRank_add_badBranchCount h.isProjectiveVariety_plus
    h.dim_plus Sp _ (badLocusPlus fm fp).isClosed hSp hDν σp hσpP hσpB
    (by rw [← Category.assoc, hσp, Category.assoc, h.comp_eq_plus]) V hOp hOpne (hc.2 σp hσp)
  letI := primeDivisorNormalizationOver sXm Sm
  letI := primeDivisorNormalizationOver sXp Sp
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus Sm
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus Sp
  letI := opensOver (σm ⁻¹ᵁ V)
  letI := opensOver (σp ⁻¹ᵁ V)
  haveI := isComplexScheme_opens (σm ⁻¹ᵁ V)
  haveI := isComplexScheme_opens (σp ⁻¹ᵁ V)
  have heq := cycleRank_product_eq_of_iso e (by
    change e.hom ≫ (σp ⁻¹ᵁ V).ι ≫ primeDivisorNormalization Sp ≫ sXp =
      (σm ⁻¹ᵁ V).ι ≫ primeDivisorNormalization Sm ≫ sXm
    rw [← h.comp_eq_plus, ← h.comp_eq_minus,
      ← Category.assoc (primeDivisorNormalization Sp) fp sZ, ← hσp,
      ← Category.assoc (primeDivisorNormalization Sm) fm sZ, ← hσm, Category.assoc σp,
      Category.assoc σm, ← morphismRestrict_ι_assoc σp V, ← morphismRestrict_ι_assoc σm V,
      ← Category.assoc e.hom, he])
  rw [hm', hp', heq]
  push_cast
  ring

end MMP.Fourfold
