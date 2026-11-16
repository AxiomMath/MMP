module

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicGeometry.CycleMap.Stacks.PushforwardInjective
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreVanishing
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ComplexSchemeAffineHom
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.Semismooth.BranchLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Action
import MMP.AlgebraicGeometry.Intersection.OneCycles
import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.ZariskiSequenceBasic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceCurves
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Curves.DegreeEuler
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
import MMP.AlgebraicTopology.BorelMoore.CycleSpanRestriction
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.Chow.CycleClassDegree
import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Exceptional divisor classes and divisor cycle ranks across a small step diagram

Let `q : S ⟶ T` be a projective birational morphism of normal projective threefolds over `ℂ`.
The classes `[P] ∈ H_4(S, ℚ)` of the prime divisors `P` of `S` contracted by `q` are linearly
independent over `ℚ`. Suppose `∑ c_P [P] = 0`. Lift the relation to a strong resolution
`r : W ⟶ S`, an isomorphism over the smooth locus of `S`: by the Borel–Moore localization
sequence the strict transform `D_W = ∑ c_P P̃` plus a `ℚ`-divisor `G` whose components map to
curves or points has class `[D_W + G] = 0`. A divisor with zero class on the smooth projective
threefold `W` has `c₁ = 0`, hence degree zero on every curve (Fulton, Corollary 19.2), and every
component of `D_W + G` is exceptional for `r ≫ q`, so the negativity lemma gives `D_W + G = 0`,
whence all `c_P = 0`.

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a fourfold step diagram in which both `f⁻` and `f⁺` are small,
with full bad loci `W^± = (f^±)⁻¹(Σ)`. Let `S⁻` be a prime divisor of `Y⁻` and `S⁺` its strict
transform on `Y⁺`, with normalizations `ν^± : (S^±)^ν ⟶ Y^±`, and let `T` be the normalization
of `f⁻(S⁻)`. Away from the bad loci both normalizations are isomorphic to an open of `T`;
restriction maps the cycle span `Cyc_2((S^±)^ν)` onto a common space, with kernel spanned by the
classes of the bad branches, which are linearly independent by the first result since the bad
branches are exceptional over `T`. Hence the divisor cycle ranks satisfy
`ρ_*((S⁻)^ν) - ρ_*((S⁺)^ν) = e⁻(S⁻) - e⁺(S⁻)`, where `e^±(S⁻)` counts the prime divisors of
`(S^±)^ν` lying over `W^±`.

## Main results

* `MMP.Fourfold.linearIndependent_divisorClass_of_isExceptional`: the classes of the
  `q`-exceptional prime divisors are linearly independent.
* `MMP.Fourfold.IsFourfoldStepDiagram.divisorCycleRank_sub_divisorCycleRank_eq`: the rank
  difference formula.

## Implementation notes

* `H_4(S, ℚ)` is `MMP.Fourfold.RationalHomology S 4`, the rational Borel–Moore homology of
  `S(ℂ)`. The class of a prime divisor `P` is `MMP.Chow.divisorClass S (Finsupp.single P 1)`, the
  cycle class of the Stacks cycle of its generic point, and a projective `S` is a complex scheme
  by `MMP.Fourfold.isComplexScheme_of_isProjectiveVariety`.
* "Contracted by `q`" is `MMP.Mori.RationalMap.IsExceptional q.toRationalMap P`: the image of `P`
  has codimension at least two in `T`.
* The localization step is `MMP.Fourfold.exists_divisorClass_inverseTransformDivisor_add_eq_zero`
  (over the complement of the biregular locus of `r`), rather than over an open on which the
  contracted divisors form a simple normal crossing divisor.
* Numerical triviality uses the Cartier divisor dictionary
  `MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback` (`[D] = 0 ↔ c₁(𝒪(D)) = 0` on a
  smooth projective variety) and `MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero`.
* `ρ_r(X)` is computed as the rank of the classes `MMP.Chow.rationalCycleClass` of the rational
  Stacks `r`-cycles in the Borel–Moore homology of `X(ℂ)` (`cycleRank_eq_finrank_range`): the
  complex realization `X^an` is homeomorphic to `X(ℂ)`, by a homeomorphism carrying `[A]` to the
  cycle class of the generic point of `A`.
* The common open of the two normalizations is not built as a scheme: with
  `σ^± : (S^±)^ν ⟶ T`, `τ : T ⟶ Z` and `U` the common biregular locus of `f^±`, each `σ^±` is an
  isomorphism over `τ⁻¹(U)`, and push-forward along `σ^±` followed by restriction to
  `τ⁻¹(U)(ℂ)` maps the surface classes of `(S^±)^ν` onto the restrictions of the surface classes
  of `T`. The rank count is then rank–nullity (`finrank_sub_finrank_eq_of_surjective`).
* The strict transform `S⁺` is a prime divisor `S'` with
  `MMP.Fourfold.flipTransformPrimeDivisor f⁻ f⁺ S = some S'`, and the counts `e^±` are
  `MMP.Fourfold.badBranchCount` along `MMP.Fourfold.badLocusMinus` and
  `MMP.Fourfold.badLocusPlus`. The identity is an identity of integers.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Corollary 19.2.
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP TopologicalSpace
open scoped MMP.SubschemeOver

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori
open MMP.Chow (rationalCycleClass divisorCycle divisorClass)

universe u

/-! ### Cycle classes of surfaces -/

section Topo

variable {W S : Scheme.{0}} [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]

/-- The `ℂ`-points of `S` lying over an open `V`, as an open subset of `S(ℂ)`. -/
private def pointsOverOpens (V : S.Opens) :
    TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ S)) :=
  ⟨{p | p.toHom (IsLocalRing.closedPoint ℂ) ∈ (V : Set S)}, by
    have := UnderlyingSpace.isOpen_setOf_le_preimage (K := ℂ) (X := S) V
    convert this using 1
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h x _
      rw [Subsingleton.elim x (IsLocalRing.closedPoint ℂ)]; exact h
    · intro h; exact h trivial⟩

/-- A `ℂ`-point whose closed point lies in an open `U` factors through `U`. -/
private theorem exists_lift_of_mem {X : Scheme.{0}} (U : X.Opens) (a : Spec (.of ℂ) ⟶ X)
    (h : a (IsLocalRing.closedPoint ℂ) ∈ U) : ∃ a' : Spec (.of ℂ) ⟶ U, a' ≫ U.ι = a := by
  refine ⟨IsOpenImmersion.lift U.ι a ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint ℂ)]
  exact h

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
    · apply Subtype.ext
      apply UnderlyingSpace.ext
      exact hpr

/-- If `r` is an isomorphism over `V` and `r_* x` restricts to zero on `V(ℂ)`, then `x`
restricts to zero on `r⁻¹(V)(ℂ)`. -/
private theorem restrict_eq_zero_of_restrict_pushforward_eq_zero [IsComplexScheme W]
    [IsComplexScheme S] (r : W ⟶ S)
    [r.IsOver (Spec (.of ℂ))] [IsProper r] (V : S.Opens) [IsIso (r ∣_ V)] (k : ℤ)
    (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) k)
    (hx : (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (pointsOverOpens V) k).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r))
        (UnderlyingSpace.isProperMap_map (K := ℂ) r) k).hom x) = 0) :
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (TopologicalSpace.Opens.comap (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)).hom
        (pointsOverOpens V)) k).hom x = 0 := by
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) r
  have h := borelMooreHomology.restrict_pushforward_apply ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) hp (pointsOverOpens V) k x
  have hb := bijective_restrictPreimage r V
  have hpp := borelMooreHomology.isProperMap_restrictPreimage
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) (pointsOverOpens V) hp
  have hemb : Topology.IsClosedEmbedding (borelMooreHomology.restrictPreimage
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) r)) (pointsOverOpens V)) :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      (borelMooreHomology.restrictPreimage _ _).hom.continuous hb.1 hpp.isClosedMap
  apply MMP.Chow.pushforward_injective_of_isClosedEmbedding _ hpp hemb hb.2 k
  rw [map_zero]
  exact h.symm.trans hx

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

end Topo

/-! ### Contracted divisors have independent classes -/

/-- The generic point of a threefold has delta-dimension three. -/
private theorem relativeDimension_genericPoint {W : Scheme.{0}} [IsIntegral W]
    [W.Over (Spec (.of ℂ))] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
    (hW3 : topologicalKrullDim W = 3) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ)) (genericPoint W) =
      ((2 + 1 : ℕ) : ℤ) := by
  refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ _ _ (2 + 1) ?_
  rw [(genericPoint_spec W).def, (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq, hW3]
  rfl

/-- **Numerical triviality of a divisor with zero class.** On a smooth projective complex
threefold `W`, a divisor `D` whose class vanishes in `H_4(W, ℚ)` has degree zero on every curve:
by the Cartier divisor dictionary `c₁(𝒪_W(D)) = 0` in `H²(W^an, ℚ)`, and a line bundle with
vanishing topological first Chern class has degree zero on every curve (Fulton, Corollary
19.2). -/
private theorem degreeOn_eq_zero_of_divisorClass_eq_zero {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [W.Over (Spec (.of ℂ))] [IsComplexScheme W]
    (hWp : AlgebraicGeometry.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (hW3 : topologicalKrullDim W = 3)
    (D : MMP.Mori.Divisor W) (hD : divisorClass W (MMP.Mori.Divisor.toQDivisor D) = 0)
    (C : MMP.Mori.ProperCurve (W ↘ Spec (.of ℂ))) :
    MMP.Mori.Divisor.degreeOn ℂ (W ↘ Spec (.of ℂ)) C.ι C.dim_le D
      (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D) = 0 := by
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  haveI hinv : Stacks.Ample.IsInvertibleModule W D.divisorialSheaf :=
    hcart.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 D.divisorialSheaf := hinv
  have h := (MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hWp hsm (d := 2)
    (by rw [hW3]; rfl) (MMP.Mori.Divisor.toQDivisor D) one_pos D (by rw [Nat.cast_one, one_smul])
    (genericPoint W) (relativeDimension_genericPoint hW3)).2.1 hD
  have hc := MMP.Chow.firstChernClassTop_eq_zero_of_mapCoeff_eq_zero D.divisorialSheaf h
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hWp
  haveI : Stacks.Ample.IsInvertibleModule W H := hH
  unfold MMP.Mori.Divisor.degreeOn
  exact MMP.Chow.degreeOn_eq_zero_of_firstChernClassTop_eq_zero H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple W H).mpr hHa) D.divisorialSheaf hc C.ι C.dim_le

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
    simp [hBdef]
  have hnef : ∀ c : ℝ, IsRelativelyNef ℂ sW f (c • B) := by
    intro c
    refine ⟨1, ![c], ![D], fun j => by fin_cases j; exact hD, hpres c, fun C _ x hx => ?_⟩
    obtain ⟨hL, d, -, hd, rfl⟩ := hx
    have h0 : d 0 = 0 := by
      rw [Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber (hd 0)]
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
      simp [h0]
    rw [this]
    exact fun P => by simp
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

/-- If `a + c = 3` in `WithBot ℕ∞` with `a` a natural number, then `c` is a natural number. -/
private theorem exists_coheight_eq_of_add_eq_three {a : ℕ} {c : ℕ∞}
    (h : ((a : ℕ) : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : ∃ n : ℕ, c = n ∧ a + n = 3 := by
  have h' : (a : ℕ∞) + c = 3 := by
    apply WithBot.coe_injective
    rw [WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_ofNat]
    exact h
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n => exact ⟨n, rfl, by exact_mod_cast h'⟩

/-- Under a proper morphism of threefolds over `ℂ`, a point of codimension at least two maps to a
point of codimension at least two: the dimension of `closure {q y}` is at most that of
`closure {y}`. -/
private theorem two_le_coheight_map {S T : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [T.Over (Spec (.of ℂ))] [IsComplexScheme S] [IsComplexScheme T]
    [IsIntegral S] [IsIntegral T] (q : S ⟶ T) [q.IsOver (Spec (.of ℂ))] [IsProper q]
    (hS : topologicalKrullDim S = 3) (hT : topologicalKrullDim T = 3) (y : S)
    (hy : 2 ≤ Order.coheight y) : 2 ≤ Order.coheight (q y) := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (S ↘ Spec (.of ℂ)) y
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T ↘ Spec (.of ℂ))
    (q y)
  rw [hS, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (S ↘ Spec (.of ℂ))] at h1
  rw [hT, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (T ↘ Spec (.of ℂ))] at h2
  have h3 := MMP.Chow.relativeDimension_map_le q y
  obtain ⟨a, ha, ha3⟩ := exists_coheight_eq_of_add_eq_three h1
  obtain ⟨b, hb, hb3⟩ := exists_coheight_eq_of_add_eq_three h2
  have h4 := Int.toNat_le_toNat h3
  rw [ha] at hy
  rw [hb]
  have hy' : 2 ≤ a := by exact_mod_cast hy
  exact_mod_cast (show 2 ≤ b by omega)

/-- A prime divisor `E` of `W` whose image under a proper `r : W ⟶ S` has dimension at most one
maps to a point of codimension at least two of the threefold `S`. -/
private theorem two_le_coheight_of_topologicalKrullDim_image_le_one {W S : Scheme.{0}}
    [IsIntegral S] (sS : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sS]
    (hS : topologicalKrullDim S = 3) (r : W ⟶ S) [IsProper r] (E : MMP.Mori.PrimeDivisor W)
    (h : topologicalKrullDim (r.base '' E.support) ≤ 1) : 2 ≤ Order.coheight (r E.genericPoint) := by
  have hmem : E.genericPoint ∈ (E.support : Set W) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hcl : closure ({r E.genericPoint} : Set S) ⊆ r.base '' E.support :=
    closure_minimal (Set.singleton_subset_iff.2 ⟨E.genericPoint, hmem, rfl⟩)
      (r.isClosedMap _ (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure))
  have hle : topologicalKrullDim (closure ({r E.genericPoint} : Set S)) ≤ 1 :=
    ((Topology.IsInducing.subtypeVal.codRestrict
      fun z : closure ({r E.genericPoint} : Set S) ↦ hcl z.2).topologicalKrullDim_le).trans h
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS (r E.genericPoint)
  rw [hS, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ sS] at h1
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ sS] at hle
  obtain ⟨n, hn, hsum⟩ := exists_coheight_eq_of_add_eq_three h1
  have h2 : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sS (r E.genericPoint)).toNat ≤ 1 := by
    exact_mod_cast hle
  rw [hn]
  exact_mod_cast (show 2 ≤ n by omega)

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

/-- An exceptional prime divisor of a morphism maps to a point of codimension at least two. -/
private theorem two_le_coheight_of_isExceptional {S T : Scheme.{0}} [IsLocallyNoetherian S]
    [IsNormal S]
    [IsLocallyNoetherian T] [IsNormal T] [IsSeparated (T ↘ Limits.terminal Scheme)]
    (q : S ⟶ T) (P : MMP.Mori.PrimeDivisor S)
    (h : MMP.Mori.RationalMap.IsExceptional (X := S) q.toRationalMap P) :
    2 ≤ Order.coheight (q P.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff, MMP.Mori.le_closedsCodimension_iff] at h
  rw [coheight_eq_codimension_closureSingleton]
  refine h _ ?_
  change closure {q P.genericPoint} ⊆ closure (q '' (P.idealSheaf.support : Set S))
  refine closure_mono (Set.singleton_subset_iff.mpr ⟨P.genericPoint, ?_, rfl⟩)
  change P.genericPoint ∈ (P.support : Set S)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

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

/-- **Contracted divisors have independent classes.** Let `q : S ⟶ T` be a projective
birational morphism over `ℂ` of normal projective threefolds. Then the classes
`[P] ∈ H_4(S, ℚ)` of the prime divisors `P` of `S` that are exceptional for `q` are linearly
independent over `ℚ`. -/
@[mmp "lem_oai4_difficulty_normalization_independence"]
public theorem linearIndependent_divisorClass_of_isExceptional {S T : Scheme.{0}}
    [S.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hS : AlgebraicGeometry.IsProjectiveVariety ℂ (S ↘ Spec (.of ℂ)))
    (hT : AlgebraicGeometry.IsProjectiveVariety ℂ (T ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3) (hTdim : topologicalKrullDim T = 3)
    (q : S ⟶ T) [q.IsOver (Spec (.of ℂ))] (hqp : IsProjectiveMorphism q)
    (hqb : Mori.IsBirationalMorphism q) :
    letI := isComplexScheme_of_isProjectiveVariety S hS
    LinearIndependent ℚ fun P : {P : Mori.PrimeDivisor S //
        RationalMap.IsExceptional q.toRationalMap P} =>
      divisorClass S (Finsupp.single P.1 1) := by
  letI hSc : IsComplexScheme S := isComplexScheme_of_isProjectiveVariety S hS
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- the relation `∑ g_P [P] = 0` on `S`
  set DS : MMP.Mori.QDivisor S := ∑ P ∈ s, g P • Finsupp.single P.1 (1 : ℚ) with hDSdef
  have hDS : divisorClass S DS = 0 := by
    rw [hDSdef, map_sum]
    simpa only [map_smul] using hsum
  -- the varieties `S` and `T`
  have hSv : AlgebraicGeometry.IsVariety ℂ (S ↘ Spec (.of ℂ)) := hS.toIsVariety
  have hTv : AlgebraicGeometry.IsVariety ℂ (T ↘ Spec (.of ℂ)) := hT.toIsVariety
  have hSn : MMP.Mori.IsNormalVariety ℂ (S ↘ Spec (.of ℂ)) := ⟨hSv, inferInstance⟩
  have hTn : MMP.Mori.IsNormalVariety ℂ (T ↘ Spec (.of ℂ)) := ⟨hTv, inferInstance⟩
  letI hTc : IsComplexScheme T := isComplexScheme_of_isProjectiveVariety T hT
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
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
  -- the prime divisors of `S` lie generically in `U`, and lift to `W`
  have hηU : ∀ P : MMP.Mori.PrimeDivisor S, P.genericPoint ∈ U :=
    fun P => MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hSn P
  have hUB : U ≤ MMP.Mori.biregularLocus r := le_sSup (show MMP.Mori.IsBiregular r U from hriso)
  choose lift hlift1 hlift2 using fun P : MMP.Mori.PrimeDivisor S =>
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P (hUB (hηU P))
  have hliftU : ∀ P, (lift P).genericPoint ∈ r ⁻¹ᵁ U := fun P => by
    change r _ ∈ U
    rw [hlift2]; exact hηU P
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
  -- the strict transform `D_W = ∑ g_P P̃` of the relation, corrected over curves and points
  have hrproj : IsProjectiveMorphism r := by
    haveI : IsSeparated (S ↘ Spec (.of ℂ)) := hSv.toIsSeparated
    exact IsProjectiveMorphism.of_comp r (S ↘ Spec (.of ℂ)) hWproj.isProjective
  obtain ⟨c, hc, hcl⟩ :=
    exists_divisorClass_inverseTransformDivisor_add_eq_zero hWproj hWsm hW3 hS r hrproj hrb DS hDS
  set DW : MMP.Mori.QDivisor W := Finsupp.mapDomain lift DS with hDWdef
  have hDW : inverseTransformDivisor r DS = DW := by
    rw [hDWdef, hDSdef, map_sum, Finsupp.mapDomain_finset_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.mapDomain_single,
      inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_single, hlift1]
    rfl
  set F : MMP.Mori.QDivisor W := DW + c with hFdef
  have hF : divisorClass W F = 0 := by rw [hFdef, ← hDW]; exact hcl
  -- every component of `F` is exceptional over `T`
  have hexcF : ∀ P ∈ F.support,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := W) (r ≫ q).toRationalMap P = none := by
    intro P hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h1 | h2
    · obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h1)
      have : ∃ x ∈ s, x.1 = P₀ := by
        by_contra hcon
        push Not at hcon
        apply Finsupp.mem_support_iff.mp hP₀
        rw [hDSdef, Finsupp.finset_sum_apply]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (hcon x hx).symm, smul_zero]
      obtain ⟨x, -, rfl⟩ := this
      apply transformPrimeDivisor_eq_none_of_two_le_coheight
      rw [Scheme.Hom.comp_apply, hlift2]
      exact two_le_coheight_of_isExceptional q x.1 x.2
    · apply transformPrimeDivisor_eq_none_of_two_le_coheight
      rw [Scheme.Hom.comp_apply]
      exact two_le_coheight_map q hSdim hTdim _
        (two_le_coheight_of_topologicalKrullDim_image_le_one (S ↘ Spec (.of ℂ)) hSdim r P (hc P h2))
  -- the negativity lemma
  have hrqp : IsProjectiveMorphism (r ≫ q) := by
    refine IsProjectiveMorphism.of_comp (r ≫ q) (T ↘ Spec (.of ℂ)) ?_
    rw [Category.assoc, comp_over q (Spec (.of ℂ))]
    exact hWproj.isProjective
  have hrqb : MMP.Mori.IsBirationalMorphism (r ≫ q) :=
    Oai4C1.CommonModel.isBirationalMorphism_comp hrb hqb
  have hF0 : F = 0 := eq_zero_of_divisorClass_eq_zero hWproj hWsm hW3 hWn hTn (r ≫ q)
    (by rw [Category.assoc, comp_over q (Spec (.of ℂ))]; rfl) hrqp hrqb F hF hexcF
  -- the coefficient of `F` at `P̃_i` is `g_i`
  have hlinj : Function.Injective lift := fun P P' h => by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change MMP.Mori.PrimeDivisor.genericPoint P = MMP.Mori.PrimeDivisor.genericPoint P'
    rw [← hlift2 P, ← hlift2 P', h]
  have hcoef : F (lift i.1) = g i := by
    have hc0 : c (lift i.1) = 0 := by
      by_contra h
      have h2 := two_le_coheight_of_topologicalKrullDim_image_le_one (S ↘ Spec (.of ℂ)) hSdim r
        (lift i.1) (hc _ (Finsupp.mem_support_iff.mpr h))
      rw [hlift2, i.1.coheight_genericPoint] at h2
      exact absurd h2 (by decide)
    rw [hFdef, Finsupp.add_apply, hc0, add_zero, hDWdef, Finsupp.mapDomain_apply_of_injective hlinj, hDSdef,
      Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro x _ hx
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (fun h => hx (Subtype.ext h.symm)),
        smul_zero]
    · exact absurd hi
  rw [hF0] at hcoef
  exact hcoef.symm

/-! ### Divisor cycle ranks across a small step diagram -/

/-- **Rank–nullity over a common quotient.** If `φ : V →ₗ M` and `φ' : V' →ₗ M` are surjective,
`V` and `V'` are finite dimensional, and the kernels of `φ` and `φ'` are spanned by linearly
independent families `v` and `v'`, then `dim V - dim V' = #ι - #ι'`. -/
private theorem finrank_sub_finrank_eq_of_surjective {K V V' M : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup M] [Module K M]
    [FiniteDimensional K V] [FiniteDimensional K V']
    (φ : V →ₗ[K] M) (φ' : V' →ₗ[K] M) (hφ : Function.Surjective φ)
    (hφ' : Function.Surjective φ') {ι ι' : Type*} {v : ι → V} {v' : ι' → V'}
    (hv : LinearIndependent K v) (hv' : LinearIndependent K v')
    (hker : LinearMap.ker φ = Submodule.span K (Set.range v))
    (hker' : LinearMap.ker φ' = Submodule.span K (Set.range v')) :
    (Module.finrank K V : ℤ) - Module.finrank K V' = (Nat.card ι : ℤ) - Nat.card ι' := by
  have := hv.finite
  have := hv'.finite
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite ι'
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker φ'
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top, hker, finrank_span_eq_card hv] at h1
  rw [LinearMap.range_eq_top.mpr hφ', finrank_top, hker', finrank_span_eq_card hv'] at h2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

/-- The cycle class of a cycle lies in the span of the cycle classes of points. -/
private theorem cycleClass_mem_span_pointCycleClass (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (r : ℕ)
    (c : Stacks.Chow.CycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) r) :
    MMP.Chow.cycleClass ℚ r c ∈ Submodule.span ℚ (Set.range fun x : {x : X //
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = r} ↦
        MMP.Chow.pointCycleClass ℚ x.1 x.2) := by
  have h0 : ∀ x : X, MMP.Chow.pointCycleClassOrZero ℚ r x ∈ Submodule.span ℚ (Set.range
      fun x : {x : X // Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = r} ↦
        MMP.Chow.pointCycleClass ℚ x.1 x.2) := fun x ↦ by
    unfold MMP.Chow.pointCycleClassOrZero
    split_ifs with h
    · exact Submodule.subset_span ⟨⟨x, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  change Finsupp.linearCombination ℤ (MMP.Chow.pointCycleClassOrZero ℚ r)
    (MMP.Chow.cycleToFinsupp c) ∈ _
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun x _ ↦ zsmul_mem (h0 x) _

/-- The classes of the rational `r`-cycles are spanned by the cycle classes of points. -/
private theorem range_rationalCycleClass_eq_span (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (r : ℕ) :
    LinearMap.range (rationalCycleClass X r) = Submodule.span ℚ (Set.range fun x : {x : X //
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = r} ↦
        MMP.Chow.pointCycleClass ℚ x.1 x.2) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨α, rfl⟩
    induction α using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul q c =>
      rw [MMP.Chow.rationalCycleClass_tmul]
      exact Submodule.smul_mem _ q (cycleClass_mem_span_pointCycleClass X r c)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, MMP.Chow.rationalCycleClass_rationalPointCycle x.1 x.2⟩

/-- The cycle span `Cyc_r(X)` is isomorphic to the span of the classes of the `r`-cycles in
`H_{2r}(X(ℂ), ℚ)`: the complex realization `X^an` and the underlying space `X(ℂ)` are
homeomorphic, and this homeomorphism carries `[A]` to the cycle class of `A`. -/
private theorem nonempty_linearEquiv_cycleSpan (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (r : ℕ) :
    Nonempty (LinearMap.range (rationalCycleClass X r) ≃ₗ[ℚ] MMP.Analytic.cycleSpan X r) := by
  let e := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := X)
  let f : RationalHomology X (2 * r) →ₗ[ℚ]
      MMP.Analytic.borelMooreHomology (X ↘ Spec (.of ℂ)) (2 * r) :=
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, e.symm.continuous⟩) e.symm.isProperMap (2 * r : ℕ)).hom
  have hf : Function.Injective f :=
    MMP.Chow.pushforward_injective_of_isClosedEmbedding _ e.symm.isProperMap e.symm.isClosedEmbedding
      e.symm.surjective _
  have hspan : MMP.Analytic.cycleSpan X r = (LinearMap.range (rationalCycleClass X r)).map f := by
    rw [MMP.Analytic.cycleSpan, range_rationalCycleClass_eq_span, Submodule.map_span,
      ← Set.range_comp]
    rfl
  rw [hspan]
  exact ⟨Submodule.equivMapOfInjective f hf _⟩

/-- The cycle rank `ρ_r(X)` is the rank of the classes of the `r`-cycles in `H_{2r}(X(ℂ), ℚ)`. -/
private theorem cycleRank_eq_finrank_range (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (r : ℕ) :
    MMP.Analytic.cycleRank X r = Module.finrank ℚ (LinearMap.range (rationalCycleClass X r)) :=
  (nonempty_linearEquiv_cycleSpan X r).some.finrank_eq.symm

/-- The classes of the `r`-cycles of a projective complex scheme span a finite dimensional
subspace of `H_{2r}(X(ℂ), ℚ)`. -/
private theorem finiteDimensional_range_rationalCycleClass (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (hX : IsProjective (X ↘ Spec (.of ℂ))) (r : ℕ) :
    FiniteDimensional ℚ (LinearMap.range (rationalCycleClass X r)) :=
  haveI := (MMP.Analytic.finiteDimensional_singularHomology_of_isProjective X hX).2.1 r
  (nonempty_linearEquiv_cycleSpan X r).some.symm.finiteDimensional

/-- On an integral threefold over `ℂ`, the points of delta-dimension `2` are the points of
coheight one, the generic points of the prime divisors. -/
private theorem relativeDimension_eq_two_iff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (hX : topologicalKrullDim X = 3)
    (x : X) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = 2 ↔ Order.coheight x = 1 := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (X ↘ Spec (.of ℂ)) x
  rw [hX, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ))] at h1
  obtain ⟨n, hn, hsum⟩ := exists_coheight_eq_of_add_eq_three h1
  have h0 := Stacks.Chow.relativeDimension_fieldChowSituation_nonneg ℂ (X ↘ Spec (.of ℂ)) x
  have h0' := Int.toNat_of_nonneg h0
  rw [hn]
  constructor
  · intro h
    rw [h] at hsum
    have : n = 1 := by simp at hsum; omega
    rw [this]
    rfl
  · intro h
    have hn1 : n = 1 := by exact_mod_cast h
    omega

section Restriction

variable {N T : Scheme.{0}} [N.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
  [IsComplexScheme N] [IsComplexScheme T]

/-- The class of a point not in an open `U` restricts to zero on `U(ℂ)`. -/
private theorem restrict_pointCycleClass_eq_zero_of_notMem (U : T.Opens) {k : ℕ} (y : T)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (T ↘ Spec (.of ℂ)) y = k) (hyU : y ∉ U) :
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (pointsOverOpens U) ((2 * k : ℕ) : ℤ)).hom
      (MMP.Chow.pointCycleClass ℚ y hy) = 0 := by
  refine MMP.Chow.restrict_pointCycleClass_eq_zero ℚ y hy _
    (Set.disjoint_left.2 fun p hp hp' ↦ hyU ?_)
  rw [UnderlyingSpace.range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq,
    Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt] at hp'
  exact (specializes_iff_mem_closure.2 hp').mem_open U.isOpen hp

/-- The class of a point not in `U`, or zero, restricts to zero on `U(ℂ)`. -/
private theorem restrict_pointCycleClassOrZero_eq_zero_of_notMem (U : T.Opens) (k : ℕ) (y : T)
    (hyU : y ∉ U) :
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (pointsOverOpens U) ((2 * k : ℕ) : ℤ)).hom
      (MMP.Chow.pointCycleClassOrZero ℚ k y) = 0 := by
  unfold MMP.Chow.pointCycleClassOrZero
  split_ifs with hy
  · exact restrict_pointCycleClass_eq_zero_of_notMem U y hy hyU
  · exact map_zero _

/-- Push-forward along `σ : N ⟶ T` followed by restriction to `U(ℂ)` for an open `U ⊆ T`. -/
private noncomputable def pushRestrict (σ : N ⟶ T) [σ.IsOver (Spec (.of ℂ))] [IsProper σ]
    (U : T.Opens) :=
  (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (pointsOverOpens U) ((2 * 2 : ℕ) : ℤ)).hom ∘ₗ
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
      (UnderlyingSpace.isProperMap_map (K := ℂ) σ) ((2 * 2 : ℕ) : ℤ)).hom

/-- The restrictions to `U(ℂ)` of the surface classes of `T`. -/
private noncomputable def restrictedCycles (U : T.Opens) :=
  (LinearMap.range (rationalCycleClass T 2)).map
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (pointsOverOpens U) ((2 * 2 : ℕ) : ℤ)).hom

/-- `pushRestrict` of the class of a point `x` is `deg(x / σ x)` times the restriction of the
class of `σ x`. -/
private theorem pushRestrict_pointCycleClass (σ : N ⟶ T) [σ.IsOver (Spec (.of ℂ))]
    [IsProper σ] (U : T.Opens) (x : N)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) x = 2) :
    pushRestrict σ U (MMP.Chow.pointCycleClass ℚ x hx) =
      (σ.residueDegree x : ℤ) • (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
        (pointsOverOpens U) ((2 * 2 : ℕ) : ℤ)).hom (MMP.Chow.pointCycleClassOrZero ℚ 2 (σ.base x)) := by
  rw [pushRestrict, LinearMap.comp_apply, ← map_zsmul]
  congr 1
  exact MMP.Chow.pushforward_pointCycleClass ℚ σ x hx

/-- **Restriction of surface classes over an open where `σ` is an isomorphism.** Let
`σ : N ⟶ T` be a proper morphism of threefolds over `ℂ` which is an isomorphism over an open
`U ⊆ T` meeting its image. Then push-forward followed by restriction to `U(ℂ)` maps the surface
classes of `N` onto the restrictions of the surface classes of `T`, and a surface class of `N`
is killed exactly when it lies in the span of the classes of the prime divisors of `N` whose
generic point is not over `U`. -/
private theorem map_pushRestrict_and_mem_ker (σ : N ⟶ T) [σ.IsOver (Spec (.of ℂ))] [IsProper σ]
    (U : T.Opens) [IsIso (σ ∣_ U)] [IsIntegral N] [IsIntegral T]
    (hN : topologicalKrullDim N = 3)
    (hT : topologicalKrullDim T = 3) (hne : ((σ ⁻¹ᵁ U : N.Opens) : Set N).Nonempty) :
    (LinearMap.range (rationalCycleClass N 2)).map (pushRestrict σ U) = restrictedCycles U ∧
    ∀ x ∈ LinearMap.range (rationalCycleClass N 2), (pushRestrict σ U x = 0 ↔
      x ∈ Submodule.span ℚ (Set.range fun P : {P : MMP.Mori.PrimeDivisor N //
        P.genericPoint ∉ σ ⁻¹ᵁ U} => divisorClass N (Finsupp.single P.1 1))) := by
  classical
  have hUB : U ≤ MMP.Mori.biregularLocus σ :=
    le_sSup (show MMP.Mori.IsBiregular σ U from (inferInstance : IsIso (σ ∣_ U)))
  have hres0 : ∀ y : T, MMP.Chow.pointCycleClassOrZero ℚ 2 y ∈ LinearMap.range
      (rationalCycleClass T 2) := fun y ↦ by
    rw [range_rationalCycleClass_eq_span]
    unfold MMP.Chow.pointCycleClassOrZero
    split_ifs with h
    · exact Submodule.subset_span ⟨⟨y, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  refine ⟨le_antisymm ?_ ?_, fun x hx => ⟨fun h0 => ?_, fun hmem => ?_⟩⟩
  · rw [range_rationalCycleClass_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, pushRestrict_pointCycleClass σ U x.1 x.2]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_map_of_mem (hres0 _))
  · rw [restrictedCycles, range_rationalCycleClass_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    by_cases hyU : y ∈ U
    · have hc := (relativeDimension_eq_two_iff hT y).1 hy
      set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc
      have hE : MMP.Mori.PrimeDivisor.genericPoint E = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hc
      obtain ⟨E', -, hE'⟩ :=
        MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some E (hUB (hE ▸ hyU))
      have hx' : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) E'.genericPoint = 2 :=
        (relativeDimension_eq_two_iff hN _).2 E'.coheight_genericPoint
      have hσx : σ.base E'.genericPoint = y := hE'.trans hE
      refine ⟨MMP.Chow.pointCycleClass ℚ _ hx',
        (range_rationalCycleClass_eq_span N 2).ge (Submodule.subset_span ⟨⟨_, hx'⟩, rfl⟩), ?_⟩
      rw [pushRestrict_pointCycleClass σ U _ hx', residueDegree_eq_one_of_isIso σ U _
        (by rw [hσx]; exact hyU), Nat.cast_one, one_smul, hσx, MMP.Chow.pointCycleClassOrZero,
        dif_pos hy]
    · rw [SetLike.mem_coe, restrict_pointCycleClass_eq_zero_of_notMem U y hy hyU]
      exact Submodule.zero_mem _
  · have hres := restrict_eq_zero_of_restrict_pushforward_eq_zero σ U _ x h0
    have hdimQ : topologicalKrullDim (((σ ⁻¹ᵁ U : N.Opens) : Set N)ᶜ : Set N) ≤ (2 : ℕ) := by
      have hne' : ((σ ⁻¹ᵁ U : N.Opens) : Set N)ᶜ ≠ Set.univ := fun h ↦ by
        obtain ⟨w, hw⟩ := hne
        exact (show w ∈ ((σ ⁻¹ᵁ U : N.Opens) : Set N)ᶜ by rw [h]; trivial) hw
      have hfin : topologicalKrullDim (((σ ⁻¹ᵁ U : N.Opens) : Set N)ᶜ : Set N) ≠ ⊤ := fun h ↦ by
        have h2 := topologicalKrullDim_subspace_le N (((σ ⁻¹ᵁ U : N.Opens) : Set N)ᶜ)
        rw [h, hN] at h2
        exact absurd h2 (by decide)
      have hlt := MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ
        (σ ⁻¹ᵁ U).isOpen.isClosed_compl hne' hfin
      rw [hN] at hlt
      exact Order.le_of_lt_succ hlt
    have hspan := MMP.Analytic.mem_span_pointCycleClassOrZero_of_restrict_eq_zero (n := 2)
      (σ ⁻¹ᵁ U) _ (fun p ↦ by
        change (UnderlyingSpace.map (K := ℂ) σ p).toHom (IsLocalRing.closedPoint ℂ) ∈ U ↔ _
        rw [UnderlyingSpace.toHom_map]
        rfl) hdimQ x hres
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨y, hyU, rfl⟩
    unfold MMP.Chow.pointCycleClassOrZero
    split_ifs with hy
    · have hc := (relativeDimension_eq_two_iff hN y).1 hy
      have hE : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc) = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hc
      refine Submodule.subset_span ⟨⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc,
        by rw [hE]; exact hyU⟩, ?_⟩
      change divisorClass N (Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc) 1) = _
      have hcongr : ∀ (a b : N) (hab : a = b) (ha : Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) a = 2)
          (hb : Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) b = 2),
          MMP.Chow.pointCycleClass ℚ a ha = MMP.Chow.pointCycleClass ℚ b hb := by
        rintro a _ rfl _ _; rfl
      rw [MMP.Chow.divisorClass_single (by rw [hE]; exact hy)]
      exact hcongr _ _ hE _ hy
    · exact Submodule.zero_mem _
  · have hle : Submodule.span ℚ (Set.range fun P : {P : MMP.Mori.PrimeDivisor N //
        P.genericPoint ∉ σ ⁻¹ᵁ U} => divisorClass N (Finsupp.single P.1 1)) ≤
        LinearMap.ker (pushRestrict σ U) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨P, hP⟩, rfl⟩
      have hx' : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (N ↘ Spec (.of ℂ)) P.genericPoint = 2 :=
        (relativeDimension_eq_two_iff hN _).2 P.coheight_genericPoint
      change pushRestrict σ U (divisorClass N (Finsupp.single P 1)) = 0
      rw [MMP.Chow.divisorClass_single hx',
        pushRestrict_pointCycleClass σ U _ hx',
        restrict_pointCycleClassOrZero_eq_zero_of_notMem U 2 _ hP, smul_zero]
    exact hle hmem

/-- The surface classes of `N` surject onto the restrictions to `U(ℂ)` of the surface classes of
`T`, with kernel spanned by the linearly independent classes of the prime divisors of `N` not
over `U`. -/
private theorem exists_surjective_ker_eq_span (σ : N ⟶ T) [σ.IsOver (Spec (.of ℂ))]
    [IsProper σ] (U : T.Opens) [IsIso (σ ∣_ U)] [IsIntegral N] [IsIntegral T]
    (hN : topologicalKrullDim N = 3)
    (hT : topologicalKrullDim T = 3) (hne : ((σ ⁻¹ᵁ U : N.Opens) : Set N).Nonempty)
    (bad : MMP.Mori.PrimeDivisor N → Prop)
    (hbad : ∀ P, bad P ↔ P.genericPoint ∉ σ ⁻¹ᵁ U)
    (hind : LinearIndependent ℚ fun P : {P | bad P} => divisorClass N (Finsupp.single P.1 1)) :
    ∃ (φ : LinearMap.range (rationalCycleClass N 2) →ₗ[ℚ] restrictedCycles U)
      (v : {P | bad P} → LinearMap.range (rationalCycleClass N 2)),
      Function.Surjective φ ∧ LinearIndependent ℚ v ∧
        LinearMap.ker φ = Submodule.span ℚ (Set.range v) := by
  obtain ⟨hmap, hker⟩ := map_pushRestrict_and_mem_ker σ U hN hT hne
  set C := LinearMap.range (rationalCycleClass N 2)
  let φ : C →ₗ[ℚ] restrictedCycles U :=
    LinearMap.codRestrict (restrictedCycles U) ((pushRestrict σ U).comp C.subtype)
      fun x => hmap ▸ Submodule.mem_map_of_mem x.2
  let v : {P | bad P} → C := fun P =>
    ⟨divisorClass N (Finsupp.single P.1 1), ⟨divisorCycle N (Finsupp.single P.1 1), rfl⟩⟩
  have hv : C.subtype ∘ v = fun P : {P | bad P} => divisorClass N (Finsupp.single P.1 1) := rfl
  have hrange : Set.range (fun P : {P : MMP.Mori.PrimeDivisor N // P.genericPoint ∉ σ ⁻¹ᵁ U} =>
      divisorClass N (Finsupp.single P.1 1)) = Set.range (C.subtype ∘ v) := by
    rw [hv]
    ext y
    exact ⟨fun ⟨⟨P, hP⟩, h⟩ => ⟨⟨P, (hbad P).2 hP⟩, h⟩, fun ⟨⟨P, hP⟩, h⟩ => ⟨⟨P, (hbad P).1 hP⟩, h⟩⟩
  refine ⟨φ, v, fun y => ?_, LinearIndependent.of_comp C.subtype (by rw [hv]; exact hind), ?_⟩
  · obtain ⟨x, hx, hxy⟩ := (show y.1 ∈ (C.map (pushRestrict σ U)) by rw [hmap]; exact y.2)
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · ext x
    rw [LinearMap.mem_ker, show φ x = 0 ↔ pushRestrict σ U x.1 = 0 from
      ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩, hker x.1 x.2, hrange,
      Set.range_comp, ← Submodule.map_span, Submodule.mem_map]
    refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
    rwa [show x = y from Subtype.ext hyx.symm]

end Restriction

/-- Two elements of `ℕ∞` with finite sum are finite. -/
private theorem exists_eq_natCast_of_add_eq {a b : ℕ∞} {n : ℕ} (h : a + b = n) :
    ∃ a' b' : ℕ, a = a' ∧ b = b' ∧ a' + b' = n := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe b => exact ⟨a, b, rfl, rfl, by exact_mod_cast h⟩

/-- On an integral scheme locally of finite type over a field, the height and the coheight of a
point add up to the dimension. -/
private theorem height_add_coheight_eq {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (y : Y) :
    ((Order.height y : ℕ∞) : WithBot ℕ∞) + Order.coheight y = topologicalKrullDim Y := by
  rw [← AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y

/-- `height_add_coheight_eq` on a scheme of known finite dimension, as an equation in `ℕ`. -/
private theorem exists_height_coheight_eq {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hn : topologicalKrullDim Y = n) (y : Y) :
    ∃ a b : ℕ, Order.height y = a ∧ Order.coheight y = b ∧ a + b = n := by
  have h := height_add_coheight_eq sY y
  rw [hn] at h
  exact exists_eq_natCast_of_add_eq (by exact_mod_cast h)

section NormalizationFacts

variable {Y : Scheme.{0}}

/-- The normalization `P^ν` of a prime divisor `P` of an `(n+1)`-dimensional projective complex
variety `Y` is a normal projective variety of dimension `n`, the map `ν : P^ν ⟶ Y` is finite and
carries the generic point of `P^ν` to that of `P`. -/
private theorem primeDivisorNormalization_facts (s : Y ⟶ Spec (.of ℂ))
    (hY : AlgebraicGeometry.IsProjectiveVariety ℂ s) {n : ℕ}
    (hYn : topologicalKrullDim Y = (n + 1 : ℕ)) (P : MMP.Mori.PrimeDivisor Y) :
    letI := primeDivisorNormalizationOver s P
    ∃ _ : IsIntegral (primeDivisorNormalizationScheme P),
      IsNormal (primeDivisorNormalizationScheme P) ∧
      AlgebraicGeometry.IsProjectiveVariety ℂ
        (primeDivisorNormalizationScheme P ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim (primeDivisorNormalizationScheme P) = n ∧
      IsFinite (primeDivisorNormalization P) ∧
      primeDivisorNormalization P (genericPoint (primeDivisorNormalizationScheme P)) =
        P.genericPoint := by
  letI := primeDivisorNormalizationOver s P
  haveI := hY.toIsVariety
  haveI := P.integral
  set IP := P.idealSheaf
  haveI hvP : AlgebraicGeometry.IsVariety ℂ (IP.subschemeι ≫ s) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨hvN, hnorm, hfin, hsurj, hbir⟩, -, -, -, hproj⟩ :=
    MMP.Threefold.normalization_spec (IP.subschemeι ≫ s)
  haveI hvN' : AlgebraicGeometry.IsVariety ℂ (primeDivisorNormalizationScheme P ↘ Spec (.of ℂ)) :=
    hvN
  haveI hint : IsIntegral (primeDivisorNormalizationScheme P) := hvN'.toIsIntegral
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  haveI := hfin
  haveI := hsurj
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (IP.subschemeι ≫ s) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨inferInstance, (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp
        hY.isProjective⟩
  refine ⟨hint, hnorm, hproj inferInstance, ?_,
    MorphismProperty.comp_mem @IsFinite _ _ hfin inferInstance, ?_⟩
  · have e1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      (IP.subschemeι ≫ s) (primeDivisorNormalizationScheme P ↘ Spec (.of ℂ)) hbir
    rw [← e1, MMP.Mori.topologicalKrullDim_subscheme_eq]
    change topologicalKrullDim (P.support : Set Y) = n
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine (AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height _).trans ?_
    obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq s hYn P.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hb
    have hb1 : b = 1 := by exact_mod_cast hb.symm
    rw [ha]
    exact_mod_cast (show a = n by omega)
  · set nP := IP.subscheme.normalization
      (MMP.finite_irreducibleComponents_of_isIntegral IP.subscheme)
    have h1 : nP (genericPoint _) = genericPoint IP.subscheme := genericPoint_eq_of_isDominant nP
    change IP.subschemeι (nP (genericPoint _)) = P.genericPoint
    rw [h1]
    have hg := (genericPoint_spec IP.subscheme).image IP.subschemeι.continuous
    rw [Set.image_univ, IP.subschemeι.isClosedEmbedding.isClosed_range.closure_eq,
      IP.range_subschemeι] at hg
    exact hg.eq ((AlgebraicGeometry.PrimeDivisor.support_eq_closure P).symm)

end NormalizationFacts

/-- A prime divisor of `N` whose image under a proper morphism `σ : N ⟶ T` to a threefold has
dimension at most one is exceptional for `σ`. -/
private theorem isExceptional_of_topologicalKrullDim_image_le_one {N T : Scheme.{0}}
    [IsLocallyNoetherian N] [IsNormal N] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ Limits.terminal Scheme)] (σ : N ⟶ T) [IsProper σ]
    (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] (hT : topologicalKrullDim T = (3 : ℕ))
    (Q : MMP.Mori.PrimeDivisor N) (hd : topologicalKrullDim (σ.base '' Q.support) ≤ 1) :
    MMP.Mori.RationalMap.IsExceptional σ.toRationalMap Q := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have himage : σ.base '' Q.support = closure {σ Q.genericPoint} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure Q,
      ← σ.isClosedMap.closure_image_eq_of_continuous σ.continuous, Set.image_singleton]
  rw [himage, show topologicalKrullDim (closure {σ Q.genericPoint} : Set T) =
    Order.height (σ Q.genericPoint) from
      AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height _] at hd
  obtain ⟨a, b, ha, hb, hab⟩ := exists_height_coheight_eq sT hT (σ Q.genericPoint)
  rw [ha] at hd
  have : a ≤ 1 := by exact_mod_cast hd
  intro x hx
  change x ∈ closure (σ.base '' Q.support) at hx
  rw [himage, closure_closure, ← specializes_iff_mem_closure, ← Scheme.le_iff_specializes] at hx
  exact (show (2 : ℕ∞) ≤ b by exact_mod_cast (show 2 ≤ b by omega)).trans
    (hb ▸ Order.coheight_anti hx)

section Side

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **One side of the step diagram.** Let `f : X ⟶ Z` be a morphism of projective complex
fourfolds which is an isomorphism over an open `U ⊆ Z`, `P` a prime divisor of `X` and `V` a
prime divisor of `Z` with `f(η_P) = η_V ∈ U`, and `σ : P^ν ⟶ V^ν` a projective birational
morphism with `τ ∘ σ = f ∘ ν` contracting every prime divisor of `P^ν` lying over `X ∖ f⁻¹(U)`.
Then the surface classes of `P^ν` surject onto the restrictions to `τ⁻¹(U)(ℂ)` of the surface
classes of `V^ν`, with kernel spanned by the linearly independent classes of the prime divisors
of `P^ν` lying over `X ∖ f⁻¹(U)`. -/
private theorem exists_surjective_ker_eq_span_of_comp_eq
    (hX : AlgebraicGeometry.IsProjectiveVariety ℂ sX) (hX4 : topologicalKrullDim X = (3 + 1 : ℕ))
    (hZ : AlgebraicGeometry.IsProjectiveVariety ℂ sZ) (hZ4 : topologicalKrullDim Z = (3 + 1 : ℕ))
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (U : Z.Opens) [IsIso (f ∣_ U)]
    (P : MMP.Mori.PrimeDivisor X) (V : MMP.Mori.PrimeDivisor Z) (hηV : V.genericPoint ∈ U)
    (hPV : f P.genericPoint = V.genericPoint)
    (σ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme V)
    (hσp : IsProjectiveMorphism σ) (hσb : MMP.Mori.IsBirationalMorphism σ)
    (hσ : σ ≫ primeDivisorNormalization V = primeDivisorNormalization P ≫ f)
    (W : Set X) (hW : W = ((f ⁻¹ᵁ U : X.Opens) : Set X)ᶜ)
    (hexc : ∀ Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      primeDivisorNormalization P '' Q.support ⊆ W →
        topologicalKrullDim (σ.base '' Q.support) ≤ 1) :
    letI := primeDivisorNormalizationOver sX P
    letI := primeDivisorNormalizationOver sZ V
    haveI := isComplexScheme_primeDivisorNormalizationScheme sX hX P
    haveI := isComplexScheme_primeDivisorNormalizationScheme sZ hZ V
    ∃ (φ : LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme P) 2) →ₗ[ℚ]
        restrictedCycles (primeDivisorNormalization V ⁻¹ᵁ U))
      (v : {Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
        primeDivisorNormalization P '' Q.support ⊆ W} →
          LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme P) 2)),
      Function.Surjective φ ∧ LinearIndependent ℚ v ∧
        LinearMap.ker φ = Submodule.span ℚ (Set.range v) := by
  letI := primeDivisorNormalizationOver sX P
  letI := primeDivisorNormalizationOver sZ V
  haveI := isComplexScheme_primeDivisorNormalizationScheme sX hX P
  haveI := isComplexScheme_primeDivisorNormalizationScheme sZ hZ V
  set ν := primeDivisorNormalization P
  set τ := primeDivisorNormalization V
  obtain ⟨hNi, hNn, hNp, hN3, hνfin, hνη⟩ := primeDivisorNormalization_facts sX hX hX4 P
  obtain ⟨hTi, hTn, hTp, hT3, hτfin, hτη⟩ := primeDivisorNormalization_facts sZ hZ hZ4 V
  haveI := hNi
  haveI := hTi
  haveI := hNn
  haveI := hTn
  haveI := hνfin
  haveI : IsLocallyNoetherian (primeDivisorNormalizationScheme P) :=
    LocallyOfFiniteType.isLocallyNoetherian (primeDivisorNormalizationScheme P ↘ Spec (.of ℂ))
  haveI : IsLocallyNoetherian (primeDivisorNormalizationScheme V) :=
    LocallyOfFiniteType.isLocallyNoetherian (primeDivisorNormalizationScheme V ↘ Spec (.of ℂ))
  haveI : σ.IsOver (Spec (.of ℂ)) := ⟨by
    change σ ≫ τ ≫ sZ = ν ≫ sX
    rw [← Category.assoc, hσ, Category.assoc, hf]⟩
  haveI : IsProper σ := isProper_of_isProjectiveMorphism σ hσp
  set UT : (primeDivisorNormalizationScheme V).Opens := τ ⁻¹ᵁ U
  have hmem : ∀ x : (primeDivisorNormalizationScheme P), x ∈ σ ⁻¹ᵁ UT ↔ f (ν x) ∈ U := fun x => by
    change τ (σ x) ∈ U ↔ _
    rw [← Scheme.Hom.comp_apply, hσ, Scheme.Hom.comp_apply]
  -- `σ` is an isomorphism over `τ⁻¹(U)`
  haveI : IsIso (σ ∣_ UT) := by
    have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hσb
    obtain ⟨hO, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso σ hb).1
      inferInstance
    have hle : UT ≤ ⟨_, hO⟩ := by
      intro t ht
      change (σ ⁻¹' {t}).Finite
      have hsub : σ ⁻¹' {t} ⊆ ν ⁻¹' (f ⁻¹' {τ t}) := by
        intro x hx
        change f (ν x) = τ t
        rw [← Scheme.Hom.comp_apply, ← hσ, Scheme.Hom.comp_apply]
        exact congrArg τ hx
      refine Set.Finite.subset (Set.Finite.preimage' ?_ fun y _ => ν.finite_preimage_singleton y)
        hsub
      exact (MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict f U ht).finite
    exact MMP.Mori.isBiregular_iff_le_biregularLocus.mpr
      (hle.trans (MMP.Mori.le_biregularLocus hiso))
  have hne : ((σ ⁻¹ᵁ UT : (primeDivisorNormalizationScheme P).Opens) :
      Set (primeDivisorNormalizationScheme P)).Nonempty :=
    ⟨genericPoint (primeDivisorNormalizationScheme P), (hmem _).2 (by rw [hνη, hPV]; exact hηV)⟩
  have hbad : ∀ Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      ν '' Q.support ⊆ W ↔ Q.genericPoint ∉ σ ⁻¹ᵁ UT := by
    intro Q
    have hQsupp :
        (Q.support : Set (primeDivisorNormalizationScheme P)) = closure {Q.genericPoint} :=
      AlgebraicGeometry.PrimeDivisor.support_eq_closure Q
    rw [hmem, hW]
    constructor
    · intro h
      exact h ⟨Q.genericPoint, by rw [hQsupp]; exact subset_closure rfl, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩ hfa
      rw [hQsupp] at ha
      have hsp : Q.genericPoint ⤳ a := specializes_iff_mem_closure.mpr ha
      exact h (((hsp.map ν.continuous).map f.continuous).mem_open U.isOpen hfa)
  -- the bad branches are exceptional for `σ`
  haveI : IsSeparated ((primeDivisorNormalizationScheme V) ↘ Limits.terminal Scheme) := by
    haveI : IsSeparated (primeDivisorNormalizationScheme V ↘ Spec (.of ℂ)) :=
      hTp.toIsVariety.toIsSeparated
    rw [show (primeDivisorNormalizationScheme V ↘ Limits.terminal Scheme) =
      (primeDivisorNormalizationScheme V ↘ Spec (.of ℂ)) ≫
      (Spec (.of ℂ) ↘ Limits.terminal Scheme) from Limits.terminal.hom_ext _ _]
    infer_instance
  have hN3' : topologicalKrullDim (primeDivisorNormalizationScheme P) = 3 := by
    rw [hN3]; rfl
  have hT3' : topologicalKrullDim (primeDivisorNormalizationScheme V) = 3 := by
    rw [hT3]; rfl
  have hind := linearIndependent_divisorClass_of_isExceptional hNp hTp hN3' hT3' σ hσp hσb
  have hexcQ : ∀ Q : {Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
      ν '' Q.support ⊆ W}, MMP.Mori.RationalMap.IsExceptional σ.toRationalMap Q.1 :=
    fun Q => isExceptional_of_topologicalKrullDim_image_le_one σ
      ((primeDivisorNormalizationScheme V) ↘ Spec (.of ℂ)) hT3 Q.1 (hexc Q.1 Q.2)
  have hind2 := hind.comp (fun Q : {Q : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
      ν '' Q.support ⊆ W} => ⟨Q.1, hexcQ Q⟩) fun _ _ h =>
        Subtype.ext (congrArg Subtype.val h :)
  exact exists_surjective_ker_eq_span σ UT hN3' hT3' hne _ hbad hind2

end Side

section Geometry

/-- The generic point of a prime divisor `P` of `X` is the generic point of its support. -/
private theorem isGenericPoint_genericPoint {X : Scheme.{0}} (P : MMP.Mori.PrimeDivisor X) :
    IsGenericPoint P.genericPoint (P.support : Set X) :=
  (AlgebraicGeometry.PrimeDivisor.support_eq_closure P).symm

/-- If the exceptional set of `f` has codimension at least two, the generic point of every prime
divisor lies over the biregular locus of `f`. -/
private theorem genericPoint_mem_preimage_biregularLocus {X Y : Scheme.{0}} {f : X ⟶ Y}
    (h : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ f ⁻¹ᵁ biregularLocus f := by
  by_contra hn
  have hmem : P.genericPoint ∈ (exceptionalSet f : Set X) := hn
  have hsub : ((IrreducibleCloseds.closureSingleton P.genericPoint : IrreducibleCloseds X) :
      Set X) ⊆ exceptionalSet f :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) (exceptionalSet f).isClosed
  have h2 := le_closedsCodimension_iff.mp h _ hsub
  rw [AlgebraicGeometry.PrimeDivisor.codimension_closureSingleton_genericPoint] at h2
  exact absurd h2 (by decide)

/-- A prime divisor whose support lies in the support of another prime divisor has the same
support: both have codimension one. -/
private theorem support_eq_of_support_subset {X : Scheme.{0}} {A B : MMP.Mori.PrimeDivisor X}
    (h : (A.support : Set X) ⊆ B.support) : (A.support : Set X) = B.support := by
  have hle : IrreducibleCloseds.closureSingleton A.genericPoint ≤
      IrreducibleCloseds.closureSingleton B.genericPoint := by
    change closure {A.genericPoint} ⊆ closure {B.genericPoint}
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h
  rcases hle.lt_or_eq with hlt | heq
  · have hA := A.codimension_closureSingleton_genericPoint
    have hB := B.codimension_closureSingleton_genericPoint
    rw [codimension_eq_coheight] at hA hB
    have := Order.coheight_strictAnti hlt (by rw [hB]; decide)
    rw [hA, hB] at this
    exact absurd this (lt_irrefl _)
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun T : IrreducibleCloseds X => (T : Set X)) heq

/-- The strict transform `S⁺` of a prime divisor `S` under `f⁻ : X⁻ ⟶ Z ← X⁺ : f⁺`, with `f⁺`
proper, maps onto the prime divisor `V = f⁻(S)` of `Z`, and its generic point lies over the
biregular locus of `f⁺`. -/
private theorem image_flipTransformPrimeDivisor {Xm Xp Z : Scheme.{0}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} [IsProper fp] {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S')
    {V : MMP.Mori.PrimeDivisor Z} (hV : (V.support : Set Z) = fm '' S.support) :
    (V.support : Set Z) = fp '' S'.support ∧ S'.genericPoint ∈ fp ⁻¹ᵁ biregularLocus fp := by
  unfold flipTransformPrimeDivisor at hS'
  obtain ⟨E, hE, hE'⟩ := Option.bind_eq_some_iff.mp hS'
  -- `V = E`
  have hES : fm '' S.support ⊆ E.support := by
    rw [MMP.Mori.RationalMap.support_transformPrimeDivisor hE]
    refine subset_trans ?_ (MMP.Mori.RationalMap.image_subset_transform fm.toPartialMap rfl
      S.idealSheaf.support)
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, trivial⟩, hx, ?_⟩
    simp only [Scheme.Hom.toPartialMap]
    rfl
  have hVE : (V.support : Set Z) = E.support := support_eq_of_support_subset (hV ▸ hES)
  -- the strict transform on `X⁺`
  obtain ⟨hne, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hE'
  have hS'supp : (S'.support : Set Xp) =
      closure (fp ⁻¹' ((E.support : Set Z) ∩ biregularLocus fp)) := by
    rw [support_inverseTransformPrimeDivisor hE']
    rfl
  have hηE : E.genericPoint ∈ (E.support : Set Z) ∩ biregularLocus fp :=
    ⟨(isGenericPoint_genericPoint E).mem,
      ((isGenericPoint_genericPoint E).mem_open_set_iff (biregularLocus fp).isOpen).mpr hne⟩
  haveI : IsIso (fp ∣_ biregularLocus fp) := isBiregular_biregularLocus fp
  obtain ⟨w, hw⟩ := (fp ∣_ biregularLocus fp).surjective ⟨E.genericPoint, hηE.2⟩
  have hfw : fp w.1 = E.genericPoint := by
    rw [← morphismRestrict_base_coe, hw]
  have hwS' : w.1 ∈ (S'.support : Set Xp) := by
    rw [hS'supp]
    exact subset_closure (show fp w.1 ∈ _ by rw [hfw]; exact hηE)
  refine ⟨?_, ?_⟩
  · rw [hVE]
    refine le_antisymm ?_ ?_
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal ?_ (fp.isClosedMap _ S'.idealSheaf.support.isClosed)
      rw [Set.singleton_subset_iff]
      exact ⟨w.1, hwS', hfw⟩
    · rw [hS'supp]
      refine (image_closure_subset_closure_image fp.continuous).trans
        (closure_minimal ?_ E.idealSheaf.support.isClosed)
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
  · exact ((isGenericPoint_genericPoint S').mem_open_set_iff (fp ⁻¹ᵁ biregularLocus fp).isOpen).mpr
      ⟨w.1, hwS', w.2⟩

/-- The image `f⁻(S)` of a prime divisor `S` with a strict transform is a prime divisor `V` of
`Z`, with generic point `f⁻(η_S)`. -/
private theorem exists_primeDivisor_support_eq_image {Xm Xp Z : Scheme.{0}} [IsReduced Xm]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm]
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') :
    ∃ V : MMP.Mori.PrimeDivisor Z, (V.support : Set Z) = fm '' S.support ∧
      fm S.genericPoint = V.genericPoint := by
  unfold flipTransformPrimeDivisor at hS'
  obtain ⟨E, hE, -⟩ := Option.bind_eq_some_iff.mp hS'
  have hη := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S E).mp hE
  refine ⟨E, ?_, hη⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure S,
    ← fm.isClosedMap.closure_image_eq_of_continuous fm.continuous, Set.image_singleton, hη]

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- The surface classes of the two normalizations have a common quotient, the restrictions of the
surface classes of the normalization of `f⁻(S)` to the locus over the common biregular locus, by
surjections whose kernels are spanned by the linearly independent classes of the bad
branches. -/
private theorem exists_common_quotient
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') :
    letI := primeDivisorNormalizationOver sXm S
    letI := primeDivisorNormalizationOver sXp S'
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus S
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus S'
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℚ M)
      (φ : LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme S) 2) →ₗ[ℚ] M)
      (φ' : LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme S') 2) →ₗ[ℚ] M)
      (v : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
        primeDivisorNormalization S '' P.support ⊆ badLocusMinus fm fp} →
          LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme S) 2))
      (v' : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S') |
        primeDivisorNormalization S' '' P.support ⊆ badLocusPlus fm fp} →
          LinearMap.range (rationalCycleClass (primeDivisorNormalizationScheme S') 2)),
      Function.Surjective φ ∧ Function.Surjective φ' ∧
        LinearIndependent ℚ v ∧ LinearIndependent ℚ v' ∧
        LinearMap.ker φ = Submodule.span ℚ (Set.range v) ∧
        LinearMap.ker φ' = Submodule.span ℚ (Set.range v') := by
  letI := primeDivisorNormalizationOver sXm S
  letI := primeDivisorNormalizationOver sXp S'
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus S
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus S'
  haveI : IsProper fm := hm.isProper
  haveI : IsProper fp := h.isProper_plus
  have hZv : AlgebraicGeometry.IsVariety ℂ sZ := h.isProjectiveVariety_target.toIsVariety
  haveI : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    haveI : IsSeparated sZ := hZv.toIsSeparated
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  obtain ⟨V, hV, hfmη⟩ := exists_primeDivisor_support_eq_image hS'
  obtain ⟨⟨σ, hσp, hσb, hσ⟩, ⟨σ', hσ'p, hσ'b, hσ'⟩⟩ := h.exists_normalization_comp_eq hm hS' hV
  have hexcs := h.topologicalKrullDim_image_le_one_iff hm hS' hV
  have hdimZ : topologicalKrullDim Z = 4 := by
    haveI : MMP.Mori.IsVariety ℂ sZ := hm.isNormalVariety_target.1
    haveI : MMP.Mori.IsVariety ℂ sXm := hm.isNormalVariety_source.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXm
      hm.isBirationalMorphism]
    exact h.dim_minus
  -- the generic point of `V` lies over the common biregular locus
  have hηS := genericPoint_mem_preimage_biregularLocus hm.two_le_codimension S
  obtain ⟨hV', hηS'⟩ := image_flipTransformPrimeDivisor hS' hV
  have hfpη : fp S'.genericPoint = V.genericPoint := by
    have hg : IsGenericPoint (fp S'.genericPoint) (V.support : Set Z) := by
      rw [hV', AlgebraicGeometry.PrimeDivisor.support_eq_closure S',
        ← fp.isClosedMap.closure_image_eq_of_continuous fp.continuous, Set.image_singleton]
      exact isGenericPoint_closure
    exact hg.eq (isGenericPoint_genericPoint V)
  have hU : V.genericPoint ∈ commonBiregularLocus fm fp :=
    ⟨hfmη ▸ hηS, hfpη ▸ hηS'⟩
  haveI : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  have h4m : topologicalKrullDim Xm = (3 + 1 : ℕ) := by rw [h.dim_minus]; rfl
  have h4p : topologicalKrullDim Xp = (3 + 1 : ℕ) := by rw [h.dim_plus]; rfl
  have h4Z : topologicalKrullDim Z = (3 + 1 : ℕ) := by rw [hdimZ]; rfl
  obtain ⟨φ, v, h1, h2, h3⟩ := exists_surjective_ker_eq_span_of_comp_eq
    h.isProjectiveVariety_minus h4m h.isProjectiveVariety_target h4Z fm h.comp_eq_minus _ S V hU
    hfmη σ hσp hσb hσ _ rfl fun Q hQ => ((hexcs.1 σ hσ Q).2 hQ)
  obtain ⟨φ', v', h1', h2', h3'⟩ := exists_surjective_ker_eq_span_of_comp_eq
    h.isProjectiveVariety_plus h4p h.isProjectiveVariety_target h4Z fp h.comp_eq_plus _ S' V hU
    hfpη σ' hσ'p hσ'b hσ' _ rfl fun Q hQ => ((hexcs.2 σ' hσ' Q).2 hQ)
  exact ⟨_, _, _, φ, φ', v, v', h1, h1', h2, h2', h3, h3'⟩

/-- In a fourfold step diagram `Y⁻ → Z ← Y⁺` in which both `f⁻` and `f⁺` are small, let `S` be a
prime divisor of `Y⁻` and `S'` its strict transform on `Y⁺`. Then the divisor cycle ranks of the
normalizations differ by the bad branch counts:
`ρ_*(S^ν) - ρ_*(S'^ν) = e⁻(S) - e⁺(S)`, where `e⁻(S)` (resp. `e⁺(S)`) counts the prime divisors
of `S^ν` (resp. `S'^ν`) whose image lies in the bad locus `W⁻` (resp. `W⁺`). -/
@[mmp "lem_oai4_c3_normalization_rank_difference"]
public theorem IsFourfoldStepDiagram.divisorCycleRank_sub_divisorCycleRank_eq
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm)
    {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (hS' : flipTransformPrimeDivisor fm fp S = some S') :
    letI := primeDivisorNormalizationOver sXm S
    letI := primeDivisorNormalizationOver sXp S'
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus S
    haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus S'
    (MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S) : ℤ) -
        MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme S') =
      (badBranchCount S (badLocusMinus fm fp) : ℤ) - badBranchCount S' (badLocusPlus fm fp) := by
  letI := primeDivisorNormalizationOver sXm S
  letI := primeDivisorNormalizationOver sXp S'
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXm h.isProjectiveVariety_minus S
  haveI := isComplexScheme_primeDivisorNormalizationScheme sXp h.isProjectiveVariety_plus S'
  obtain ⟨M, _, _, φ, φ', v, v', hφ, hφ', hv, hv', hk, hk'⟩ := exists_common_quotient h hm hS'
  have h4m : topologicalKrullDim Xm = (3 + 1 : ℕ) := by rw [h.dim_minus]; rfl
  have h4p : topologicalKrullDim Xp = (3 + 1 : ℕ) := by rw [h.dim_plus]; rfl
  obtain ⟨hNi, hNn, hNp, hN3, -, -⟩ :=
    primeDivisorNormalization_facts sXm h.isProjectiveVariety_minus h4m S
  obtain ⟨hNi', hNn', hNp', hN3', -, -⟩ :=
    primeDivisorNormalization_facts sXp h.isProjectiveVariety_plus h4p S'
  haveI := finiteDimensional_range_rationalCycleClass
    (primeDivisorNormalizationScheme S) hNp.isProjective.isProjective 2
  haveI := finiteDimensional_range_rationalCycleClass
    (primeDivisorNormalizationScheme S') hNp'.isProjective.isProjective 2
  have key := finrank_sub_finrank_eq_of_surjective φ φ' hφ hφ' hv hv' hk hk'
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at key
  rw [MMP.Analytic.divisorCycleRank, MMP.Analytic.divisorCycleRank,
    cycleRank_eq_finrank_range, cycleRank_eq_finrank_range]
  exact key

end Geometry

end MMP.Fourfold
