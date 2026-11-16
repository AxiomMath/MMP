module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.ScalingProgram.ConstantLevelKltPerturbation
import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.RealPltSpecialTermination
import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
import MMP.AlgebraicGeometry.Singularities.AmpleFloorLowering
import MMP.AlgebraicGeometry.MMP.MinimalModel.PltReference
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.MMP.Flip.DivisorNormalizationLift
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Real dlt special termination from an ample source boundary

Let `π : X ⟶ Z` be a morphism of complex projective varieties, `X` a normal `ℚ`-factorial
fourfold, and let `B, C ≥ 0` be real divisors with `(X, B + C)` dlt and `K_X + B + C` nef over
`Z`, such that `B` contains an effective ample `ℚ`-divisor `A` none of whose components lies in
`⌊B + C⌋`. Consider a `(K_X + B)`-program over `Z` with scaling of `C`: a finite or infinite
sequence of divisorial contractions and flips `X_i ⟶ Z_i ⟵ X_{i+1}` of `(K_{X_i} + B_i)`-negative
extremal contractions over `Z`, with `B_i`, `C_i` the birational transforms of `B`, `C`, such
that at every stage the threshold `λ_i`, the least `t ≥ 0` with `K_{X_i} + B_i + t C_i` nef over
`Z`, is attained, and the upper adjoint `K_{X_i} + B_i + λ_i C_i` descends crepantly through the
step: it is the pull-back of an `ℝ`-Cartier divisor `D_i` on `Z_i`, and its birational transform
on `X_{i+1}` is the pull-back of the same `D_i`. Then all sufficiently late flips are disjoint
from the reduced boundary: for `i` large, if the `i`-th step is small, its flipping locus misses
`⌊B_i⌋` and its flipped locus misses `⌊B_{i+1}⌋`. In particular, if every flipping locus of the
program meets the reduced boundary, the program is finite.

## Main results

* `MMP.Fourfold.IsRealDltPair.eventually_disjoint_exceptionalSet_supp_roundDown_of_scaling`.

## Implementation notes

The models are indexed as in `MMP.Fourfold.RealFlipSequence`: `X₀ = X`, `X_{i+1} = Y i`, with
`n ∈ ℕ ∪ {∞}` steps; the `i`-th step is the diagram `X_i ⟶ Z_i ⟵ X_{i+1}` given by `f i`,
`fp i`, lying over `Z` through `g i : Z_i ⟶ Z`. A small step is an `MMP.Fourfold.IsRealFlipStep`
for the lower adjoint `K_{X_i} + B_i`; a divisorial step is a `(K_{X_i} + B_i)`-negative extremal
projective birational contraction `f i` whose exceptional set is a prime divisor, with `fp i` an
isomorphism, so that `X_{i+1}` is the target of `f i`. In both cases `B_{i+1}` and `C_{i+1}` are
the transforms `MMP.Mori.flipTransform` of `B_i` and `C_i`. Crepant descent of the upper adjoint
is stated with `MMP.Flips.IsRCartierPullback`, and the transformed adjoint is the transform of
`K_{X_i} + B_i + λ_i C_i` itself, so that it does not depend on the choice of the canonical
divisors `K_{X_{i+1}}`. The flipping and flipped loci are the exceptional sets
`MMP.Flips.exceptionalSet` of `f i` and `fp i`, and the reduced boundary is the support of the
round-down `⌊B_i⌋`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MMP.Fourfold MMP.Mori

namespace Proof_thm_fourfold_real_dlt_ample_source_special_termination

section ErasedIntegral

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A contraction is surjective: an open subset of the target missing the image would have no
sections upstairs, while `𝒪_X → f_* 𝒪_Y` is an isomorphism and the target is integral. -/
private theorem surjective_of_isContraction {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}
    (hf : MMP.Flips.IsContraction k sX sY f) : Surjective f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isProper
  have hdom : IsDominant f := by
    refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    let V' : X.Opens := ⟨V, hV⟩
    have hbot : f ⁻¹ᵁ V' = ⊥ := by
      refine Opens.ext ?_
      rw [Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
    have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
    have := hf.isIso_app V'
    have : Subsingleton Γ(X, V') :=
      (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
    obtain ⟨x, hx⟩ := hVne
    have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
    rw [map_one, map_zero] at h10
    exact one_ne_zero h10
  have hrange : Set.range f = Set.univ := by
    rw [← (f.isClosedMap.isClosed_range).closure_eq, hdom.denseRange.closure_range]
  exact ⟨Set.range_eq_univ.mp hrange⟩

/-- The next model of a step of a program over a projective variety is projective: if
`f : X ⟶ W` is a contraction from a projective variety onto a quasi-projective variety, then
`W` is projective, and so is any integral `Y` with a proper quasi-projective `fp : Y ⟶ W`. -/
private theorem isProjectiveVariety_of_isContraction {X W Y : Scheme.{0}} [IsIntegral Y]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {f : X ⟶ W} {fp : Y ⟶ W} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hf : MMP.Flips.IsContraction ℂ sW sX f) (hW : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sW)
    (hfp : fp ≫ sW = sY) (hfpq : IsQuasiProjective fp) [IsProper fp] :
    MMP.Mori.IsProjectiveVariety ℂ sY := by
  have hsurj := surjective_of_isContraction hf
  have := hW.toIsVariety
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  have hcomp : f ≫ sW = sX := hf.comp_eq
  have : UniversallyClosed (f ≫ sW) := by rw [hcomp]; infer_instance
  have : UniversallyClosed sW := UniversallyClosed.of_comp_surjective f sW
  have : IsProper sW := ⟨⟩
  subst hfp
  have hq : IsQuasiProjective (fp ≫ sW) := IsQuasiProjective.comp fp sW hfpq hW.isQuasiProjective
  have hproj : IsProjective (fp ≫ sW) :=
    (isProjective_iff_isQuasiProjective_and_isProper _).mpr ⟨hq, inferInstance⟩
  have : AlgebraicGeometry.IsVariety ℂ (fp ≫ sW) := {}
  exact (isProjectiveVariety_iff_isProjective' ℂ _).mpr ⟨inferInstance, hproj⟩

/-- Two morphisms from the target of a contraction to an affine scheme that agree after
composing with the contraction are equal, since a contraction is an isomorphism on global
sections. -/
private theorem eq_of_isContraction_comp_eq {k : Type} [Field k] {X Y T : Scheme.{0}}
    [IsAffine T] {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}
    (hf : MMP.Flips.IsContraction k sX sY f) {u v : X ⟶ T} (h : f ≫ u = f ≫ v) : u = v := by
  apply ext_of_isAffine
  have := hf.isIso_app ⊤
  have h' := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at h'
  exact (cancel_mono (f.app ⊤)).mp h'

private theorem modelMap_comp_eq {X Z : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {π : X ⟶ Z} {πY : ∀ i, Y i ⟶ Z} (hπ : π ≫ sZ = sX) (hπY : ∀ i, πY i ≫ sZ = sY i) :
    ∀ i, modelMap π πY i ≫ sZ = modelStr sX sY i
  | 0 => hπ
  | i + 1 => hπY i

/-- A point of the exceptional set (in the sense of the biregular locus) of a small birational
contraction onto a normal variety has coheight at least two. -/
private theorem two_le_coheight_of_mem_exceptionalSet_of_isSmall {X W : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    {f : X ⟶ W} (hf : MMP.Flips.IsSmall ℂ sW sX f) {x : X}
    (hx : x ∈ (MMP.Mori.exceptionalSet f : Set X)) : 2 ≤ Order.coheight x := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have := hf.isProper
  have hbir := (MMP.Flips.IsBirationalContraction.surjective_and_isBirational
    hf.toIsBirationalContraction).2
  obtain ⟨V, W', hV, -, h, hiso⟩ := hf.exists_isIso
  by_contra hlt
  have hlt : Order.coheight x ≤ 1 := Order.le_of_lt_add_one (not_le.mp hlt)
  have hxV : x ∉ (V : Set X) := fun hxV =>
    absurd ((MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) x hxV)
      (not_le.mpr (hlt.trans_lt (by decide)))
  let V₀ : X.Opens := V.compl
  let W₀ : W.Opens := W'.compl
  let r : V₀.toScheme ⟶ W₀.toScheme := f.resLE W₀ V₀ h
  let p : V₀.toScheme := ⟨x, hxV⟩
  have e1 : Order.coheight ((r ≫ W₀.ι) p) = Order.coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ (r ≫ W₀.ι).isOpenEmbedding
  have e2 : Order.coheight (V₀.ι p) = Order.coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ V₀.ι.isOpenEmbedding
  have e3 : (r ≫ W₀.ι) p = f x := by
    simp only [r]; rw [Scheme.Hom.resLE_comp_ι]; rfl
  have hfx : Order.coheight (f x) ≤ 1 := by
    rw [← e3, e1, ← e2]; exact hlt
  exact hx (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hbir hfx)

/-- The complement of the preimage of the common biregular locus of two small contractions
`f, f' : X, X' ⟶ W` has codimension at least two in `X`. -/
private theorem two_le_closedsCodimension_badLocusMinus {X X' W : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {f : X ⟶ W} {f' : X' ⟶ W} (hf : MMP.Flips.IsSmall ℂ sW sX f)
    (hf' : MMP.Flips.IsSmall ℂ sW sX' f') :
    2 ≤ closedsCodimension (badLocusMinus f f') := by
  have := hf.isVariety_target.toIsIntegral
  have := hf'.isVariety_source.toIsIntegral
  have := hf'.isProper
  have hbir' := (MMP.Flips.IsBirationalContraction.surjective_and_isBirational
    hf'.toIsBirationalContraction).2
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  by_cases hb : f x ∈ biregularLocus f
  · rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f hb]
    have hb' : f x ∉ biregularLocus f' := fun hb' => hx ⟨hb, hb'⟩
    by_contra hlt
    exact hb' (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f' hbir'
      (Order.le_of_lt_add_one (not_le.mp hlt)))
  · exact two_le_coheight_of_mem_exceptionalSet_of_isSmall hf hb

/-- **Flips keep the Picard number.** Two small contractions `f : X ⟶ W ⟵ X' : f'` of projective
`ℚ`-factorial varieties onto a normal variety identify `X` and `X'` outside closed subsets of
codimension two, so `ρ(X) = ρ(X')`. -/
private theorem picardNumber_eq_of_isSmall {X X' W : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X'] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hX'q : IsQFactorial sX')
    {f : X ⟶ W} {f' : X' ⟶ W} (hf : MMP.Flips.IsSmall ℂ sW sX f)
    (hf' : MMP.Flips.IsSmall ℂ sW sX' f') :
    picardNumber sX' = picardNumber sX := by
  set U := commonBiregularLocus f f'
  have : IsIso (f ∣_ U) := isBiregular_commonBiregularLocus_left f f'
  have : IsIso (f' ∣_ U) := isBiregular_commonBiregularLocus_right f f'
  have h1 : ((badLocusMinus f f').compl : X.Opens) = f ⁻¹ᵁ U := by
    ext x; simp [badLocusMinus, U]
  have h2 : ((badLocusMinus f' f).compl : X'.Opens) = f' ⁻¹ᵁ U := by
    ext x
    simp only [badLocusMinus, Closeds.compl, Opens.compl, U, commonBiregularLocus]
    simp [and_comm]
  let e : Scheme.Opens.toScheme (X := X) (badLocusMinus f f').compl ≅
      Scheme.Opens.toScheme (X := X') (badLocusMinus f' f).compl :=
    X.isoOfEq h1 ≪≫ asIso (f ∣_ U) ≪≫ (asIso (f' ∣_ U)).symm ≪≫ X'.isoOfEq h2.symm
  refine (picardNumber_eq_of_isoInCodimOne sX sX' hXq hX hX'q hX' _ _
    (two_le_closedsCodimension_badLocusMinus hf hf')
    (two_le_closedsCodimension_badLocusMinus hf' hf) e ?_).symm
  have hc : f ≫ sW = sX := hf.comp_eq
  have hc' : f' ≫ sW = sX' := hf'.comp_eq
  have k1 : (X'.isoOfEq h2.symm).hom ≫ Scheme.Opens.ι (X := X') (badLocusMinus f' f).compl =
      (f' ⁻¹ᵁ U).ι := Scheme.isoOfEq_hom_ι _ _
  have k2 : (X.isoOfEq h1).hom ≫ (f ⁻¹ᵁ U).ι =
      Scheme.Opens.ι (X := X) (badLocusMinus f f').compl := Scheme.isoOfEq_hom_ι _ _
  simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← hc', ← hc, reassoc_of% k1, ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc,
    morphismRestrict_ι_assoc, reassoc_of% k2]

/-- A point whose closure is the point itself is not the generic point of a proper curve. -/
private theorem not_isProperCurve_of_closure_subset {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)}
    {y : Y} (hcl : closure ({y} : Set Y) ⊆ {y}) : ¬ IsProperCurve sY y := by
  intro hp
  have hr : ∀ t, curveSubschemeAtι y t = y := fun t => by
    have ht : curveSubschemeAtι y t ∈ closure {y} := range_curveSubschemeAtι y ▸ ⟨t, rfl⟩
    exact hcl ht
  have : Subsingleton (curveSubschemeAt y) :=
    ⟨fun a b => (curveSubschemeAtι y).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h1 := hp.dim_eq
  have h0 : topologicalKrullDim (curveSubschemeAt y) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [h1] at h0
  norm_num at h0

/-- The image of a curve contracted by `f` is not a proper curve. -/
private theorem not_isProperCurve_map_of_isContractedBy {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (f : X ⟶ Y) [IsProper f] {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : ¬ IsProperCurve sY (f C.point) := by
  refine not_isProperCurve_of_closure_subset ?_
  have h1 : closure ({f C.point} : Set Y) ⊆ f '' closure {C.point} := by
    refine closure_minimal ?_ (f.isClosedMap _ isClosed_closure)
    rintro _ rfl
    exact ⟨C.point, subset_closure rfl, rfl⟩
  refine h1.trans ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hC v hv

/-- The exceptional set of `f` in the sense of local open immersions lies in the complement of the
preimage of the biregular locus of `f`. -/
private theorem exceptionalSet_subset {X Y : Scheme.{0}} (f : X ⟶ Y) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set X) := by
  intro x hx hb
  apply hx
  refine ⟨f ⁻¹ᵁ biregularLocus f, hb, ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

/-- A proper birational morphism of integral schemes is surjective. -/
private theorem surjective_of_isProper_of_isBirationalMorphism {T W : Scheme.{0}} [IsIntegral T]
    [IsIntegral W] (g : T ⟶ W) [IsProper g] (hg : IsBirationalMorphism g) :
    Function.Surjective g := by
  have := hg.isDominant
  have hr : Set.range g = Set.univ := by
    rw [← (g.isClosedMap.isClosed_range).closure_eq, g.denseRange.closure_range]
  exact Set.range_eq_univ.mp hr

section CurveCopies

open MMP.Mori

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- The residue degree of `f` at the generic point of a proper curve `C` is the degree of
`C ⟶ f(C)`, the corestriction of `C.ι ≫ f` to its scheme-theoretic image. -/
private theorem residueFieldDegree_eq_degreeOver_toImage (f : X ⟶ Y) (C : ProperCurve sX)
    [IsProper (C.ι ≫ f)] [IsIntegral (C.ι ≫ f).image] :
    residueFieldDegree f C.point = degreeOver (C.ι ≫ f).toImage := by
  have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
  rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
    at h1
  have h2 := residueDegree_comp (C.ι ≫ f).toImage (C.ι ≫ f).imageι (genericPoint C.scheme)
  rw [Scheme.Hom.toImage_imageι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (C.ι ≫ f).imageι,
    one_mul, AlgebraicGeometry.residueDegree_genericPoint_eq_degreeOver (C.ι ≫ f).toImage] at h2
  exact h1.symm.trans h2

/-- If the image of a proper curve `C` under `f` is again a proper curve, the degree
`[k(C) : k(f(C))]` is positive. -/
private theorem residueFieldDegree_pos (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (hC' : IsProperCurve sY (f C.point)) : 0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hpt : ¬ ∃ y : Y, Set.range φ = {y} := by
    rintro ⟨y, hy⟩
    have hcl : closure {f C.point} = ({y} : Set Y) := (C.range_comp f hf).symm.trans hy
    have hfy : f C.point ∈ ({y} : Set Y) := hcl ▸ subset_closure rfl
    refine not_isProperCurve_of_closure_subset ?_ hC'
    rw [hcl]
    exact Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mp hfy).symm
  rw [residueFieldDegree_eq_degreeOver_toImage]
  apply degreeOver_pos
  rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
  exact finite_functionField_image sY φ hpt

/-- **Proper surjections lift numerical classes.** If `τ : V ⟶ X` is a proper surjective
morphism of varieties over `k`, the push-forward `τ_* : N₁(V) ⟶ N₁(X)` is surjective: every
proper curve `C' ⊆ X` is the image of a proper curve `C ⊆ V`, and `τ_*[C] = d · [C']` with
`d = [k(C) : k(C')] > 0`. -/
private theorem pushforward_surjective {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    (hV : MMP.Mori.IsVariety k sV) (hX : MMP.Mori.IsVariety k sY) (τ : V ⟶ Y)
    (hτ : τ ≫ sY = sV) [IsProper τ] [Surjective τ] :
    Function.Surjective (NumericalCurveClasses.pushforward τ hτ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro w -
  obtain ⟨z, rfl⟩ := OneCycle.numericalClass_surjective sY w
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add z w hz hw => rw [map_add]; exact add_mem hz hw
  | single C' r =>
    obtain ⟨C, hC⟩ := ProperCurve.exists_image_closure_eq_of_surjective hV hX τ hτ C'
    have hpt : τ C.point = C'.point := by
      have h1 : τ C.point ∈ closure {C'.point} := hC ▸ ⟨C.point, subset_closure rfl, rfl⟩
      have h2 : C'.point ∈ closure {τ C.point} := by
        have : C'.point ∈ τ '' closure {C.point} := hC ▸ subset_closure rfl
        obtain ⟨c, hc, hc'⟩ := this
        rw [← hc']
        have := image_closure_subset_closure_image (s := {C.point}) τ.continuous ⟨c, hc, rfl⟩
        rwa [Set.image_singleton] at this
      exact ((specializes_iff_mem_closure.mpr h2).antisymm
        (specializes_iff_mem_closure.mpr h1)).eq
    have hC' : IsProperCurve sY (τ C.point) := hpt ▸ C'.isProperCurve
    have hd := residueFieldDegree_pos τ hτ C hC'
    refine ⟨OneCycle.numericalClass sV
      (Finsupp.single C (r / (residueFieldDegree τ C.point : ℝ))), ?_⟩
    change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sV sY τ _) = _
    have hd' : (residueFieldDegree τ C.point : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have he : (⟨τ C.point, hC'⟩ : ProperCurve sY) = C' := ProperCurve.ext hpt
    congr 1
    rw [OneCycle.pushforward, Finsupp.linearCombination_single, cyclePushforwardOfPoint,
      dif_pos hC', Finsupp.smul_single, smul_eq_mul, div_mul_cancel₀ r hd', he]

/-- A proper curve lying in a fibre of `f` is contracted by `f`. -/
private theorem isContractedBy_of_closure_subset_preimage {Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {C : ProperCurve sX} {f : X ⟶ Y} {y : Y}
    (h : closure {C.point} ⊆ f.base ⁻¹' {y}) : C.IsContractedBy f :=
  fun _ hz => (h hz).trans (h (subset_closure rfl)).symm

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp (k : Type) [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : IsNormalVariety k sX) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type} [Field k] {W Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hι (by
      have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      simpa using ha.trans hb.symm))⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- **A contracted curve over a point outside the biregular locus.** Let `f : X ⟶ Y` be a proper
birational morphism of varieties onto a normal variety and `y` a closed point of `Y` over which
`f` is not an isomorphism. Then the fibre `f⁻¹(y)` contains a proper curve `C ⊆ X`, which is then
contracted by `f`. -/
private theorem exists_properCurve_isContractedBy_of_notMem_biregularLocus {k : Type}
    [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : AlgebraicGeometry.IsVariety k sX) (hY : IsNormalVariety k sY) (f : X ⟶ Y)
    (hfs : f ≫ sY = sX) [IsProper f] (hf : IsBirationalMorphism f) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hyV : y ∉ biregularLocus f) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ closure {C.point} ⊆ f.base ⁻¹' {y} := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsSeparated sX := hX.toIsSeparated
  have := hX.toIsIntegral
  have := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsDominant f := hf.isDominant
  obtain ⟨-, hEx, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hX
    hY.1 f hfs (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
  obtain ⟨x, hx⟩ := f.surjective y
  have hxE : x ∈ (exceptionalSet f : Set X) := by
    change x ∉ (f ⁻¹ᵁ biregularLocus f : Set X)
    simpa [hx] using hyV
  rw [hEx, Set.mem_setOf_eq, hx] at hxE
  set ι := f.fiberι y
  set sF := ι ≫ sX
  have : IsProper sF := by simpa [sF, ι, hfs] using isProper_fiberι_comp k sY f hY y hy
  have : IsLocallyNoetherian (f.fiber y) := LocallyOfFiniteType.isLocallyNoetherian sF
  have : CompactSpace (f.fiber y) := QuasiCompact.compactSpace_of_compactSpace sF
  have hdim : 0 < topologicalKrullDim (f.fiber y) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph]
    exact hxE
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
  obtain ⟨A, B, hAB⟩ := hdim
  set η := B.isIrreducible.genericPoint
  have hη : closure ({η} : Set (f.fiber y)) = B := by
    rw [B.isIrreducible.isGenericPoint_genericPoint_closure, B.isClosed.closure_eq]
  obtain ⟨x₀, hx₀A, hx₀⟩ := A.isClosed.exists_closed_singleton A.isIrreducible.nonempty
  have hAB' : (A : Set (f.fiber y)) ⊆ B := hAB.le
  have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (by rw [hη]; exact hAB' hx₀A)
  have hηne : η ∉ ({x₀} : Set (f.fiber y)) := by
    intro h
    rw [Set.mem_singleton_iff] at h
    apply hAB.not_ge
    intro z hz
    have hz' : z ∈ closure ({η} : Set (f.fiber y)) := by rw [hη]; exact hz
    rw [h, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hx₀A
  obtain ⟨y', -, -, -, hcurve⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hηx₀ hx₀ hx₀
    (Set.mem_singleton _) hηne
  let C' : ProperCurve sF := ⟨y', hcurve⟩
  let C : ProperCurve sX := ⟨ι y', isProperCurve_of_injective sX ι ι.isEmbedding.injective C'⟩
  have hrι : Set.range ι = f.base ⁻¹' {y} := f.range_fiberι y
  have hcl : closure {C.point} ⊆ f.base ⁻¹' {y} :=
    closure_minimal (by rintro _ rfl; rw [← hrι]; exact ⟨y', rfl⟩) (hy.preimage f.continuous)
  exact ⟨C, isContractedBy_of_closure_subset_preimage hcl, hcl⟩

end CurveCopies

/-- **A divisorial contraction lowers the Picard number.** Let `f : X ⟶ W` be an extremal
contraction of a projective variety with nonempty exceptional set, and `Y ≅ W` over `ℂ`. The
push-forward `N₁(X) ⟶ N₁(Y)` is surjective and kills the class of a curve contracted by `f`, which
is nonzero since a relatively ample divisor has positive degree on it; so `ρ(Y) < ρ(X)`. -/
private theorem picardNumber_lt_of_isNegativeExtremalContraction {X W Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    {E' : RDivisor X} {f : X ⟶ W} {fp : Y ⟶ W}
    (hneg : MMP.Flips.IsNegativeExtremalContraction ℂ sX sW E' f) (hbir : IsBirationalMorphism f)
    (hEx : (MMP.Flips.exceptionalSet f).Nonempty) [IsIso fp] (hfp : fp ≫ sW = sY) :
    picardNumber sY < picardNumber sX := by
  have hc := hneg.isContraction
  have hW := hneg.isNormalVariety_target
  have := hW.1.toIsIntegral
  have := hW.1.toQuasiCompact
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have := hc.isProper
  have hX' := hX.toIsVariety
  have hY' := hY.toIsVariety
  have : Surjective f := surjective_of_isContraction hc
  set g : X ⟶ Y := f ≫ inv fp with hgdef
  have hg : g ≫ sY = sX := by rw [hgdef, Category.assoc, ← hfp, IsIso.inv_hom_id_assoc, hc.comp_eq]
  -- a curve contracted by `f`
  obtain ⟨x, hx⟩ := hEx
  have hfx : f x ∉ biregularLocus f := exceptionalSet_subset f hx
  obtain ⟨y, hy, hycl⟩ :=
    (biregularLocus f).compl.isClosed.exists_closed_singleton ⟨f x, hfx⟩
  obtain ⟨C, hC, -⟩ :=
    exists_properCurve_isContractedBy_of_notMem_biregularLocus hX' hW f hc.comp_eq hbir hycl hy
  have hCg : C.IsContractedBy g := fun v hv => by
    simp only [hgdef, Scheme.Hom.comp_apply, hC v hv]
  set z := OneCycle.numericalClass sX (C.cycle ℝ) with hzdef
  set φ := NumericalCurveClasses.pushforward g hg with hφdef
  -- `g` contracts `C`, so it pushes `[C]` forward to zero
  have hnp : ¬ IsProperCurve sY (g C.point) := not_isProperCurve_map_of_isContractedBy g hCg
  have hz0 : φ z = 0 := by
    change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sX sY g (C.cycle ℝ)) = 0
    rw [ProperCurve.cycle, OneCycle.pushforward, Finsupp.linearCombination_single,
      cyclePushforwardOfPoint, dif_neg hnp, smul_zero, map_zero]
  -- `[C] ≠ 0`: a relatively ample divisor has positive degree on `C`
  have hzne : z ≠ 0 := by
    obtain ⟨m, r, L, hm, -, hL, -⟩ := hneg.isRelativelyAntiAmple
    have hLc := (hL ⟨0, hm⟩).1
    have hpos := MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL ⟨0, hm⟩) hLc C hC
    haveI := hLc.isInvertibleModule_divisorialSheaf
    intro hz
    have h := congrArg (NumericalCurveClasses.degree sX (L ⟨0, hm⟩).divisorialSheaf) hz
    rw [map_zero, hzdef, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
      at h
    have h' : (C.degree ℂ (L ⟨0, hm⟩).divisorialSheaf : ℝ) = 0 := h
    rw [ProperCurve.degree] at h'
    have : (0 : ℝ) < (degreeOn ℂ sX C.ι C.dim_le (L ⟨0, hm⟩).divisorialSheaf : ℝ) := by
      exact_mod_cast hpos
    linarith
  -- dimension count
  have := finiteDimensional_numericalCurveClasses sX
  have := finiteDimensional_numericalCurveClasses sY
  have hrange : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr (pushforward_surjective hX' hY' g hg)
  have hker : 0 < Module.finrank ℝ (LinearMap.ker φ) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨z, hz0⟩, fun h => hzne (congrArg Subtype.val h)⟩
  have key := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top] at key
  rw [picardNumber, picardNumber, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank]
  rw [Cardinal.toENat_nat, Cardinal.toENat_nat]
  exact_mod_cast (by omega)

/-- A sequence of natural numbers that never increases can drop only finitely often: if
`ρ (i + 1) ≤ ρ i` for all `i`, and `ρ (i + 1) < ρ i` whenever `P i`, then `P i` fails for all
large `i`. -/
private theorem exists_forall_ge_not_of_succ_le {ρ : ℕ → ℕ} {P : ℕ → Prop}
    (hle : ∀ i, ρ (i + 1) ≤ ρ i) (hlt : ∀ i, P i → ρ (i + 1) < ρ i) :
    ∃ N, ∀ i, N ≤ i → ¬ P i := by
  have hanti : Antitone ρ := antitone_nat_of_succ_le hle
  obtain ⟨N, hN⟩ : sInf (Set.range ρ) ∈ Set.range ρ := Nat.sInf_mem ⟨ρ 0, 0, rfl⟩
  refine ⟨N, fun i hi hP => ?_⟩
  have h1 : ρ (i + 1) < ρ N := (hlt i hP).trans_le (hanti hi)
  have h2 : sInf (Set.range ρ) ≤ ρ (i + 1) := Nat.sInf_le ⟨i + 1, rfl⟩
  omega

section SmallPrimes

variable {X X' W : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}

/-- A small contraction maps the generic point of a prime divisor into its biregular locus, onto a
point of coheight one. -/
private theorem map_genericPoint_mem_biregularLocus_of_isSmall {f : X ⟶ W}
    (hf : MMP.Flips.IsSmall ℂ sW sX f) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f ∧ Order.coheight (f P.genericPoint) = 1 := by
  have hb : f P.genericPoint ∈ biregularLocus f := by
    by_contra h
    have h2 := two_le_coheight_of_mem_exceptionalSet_of_isSmall hf
      (x := P.genericPoint) (show P.genericPoint ∉ (f ⁻¹ᵁ biregularLocus f : Set X) from h)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  exact ⟨hb, by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]⟩

/-- Across two small contractions `f : X ⟶ W ⟵ X' : f⁺`, every prime divisor `P'` of `X'` lies
over the same point of `W` as a prime divisor `P` of `X`. -/
private theorem exists_primeDivisor_map_eq_of_isSmall [IsIntegral X']
    {f : X ⟶ W} {fp : X' ⟶ W} (hf : MMP.Flips.IsSmall ℂ sW sX f)
    (hfp : MMP.Flips.IsSmall ℂ sW sX' fp) (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  have := hfp.isVariety_target.toIsIntegral
  have := hfp.isProper
  obtain ⟨-, hz⟩ := map_genericPoint_mem_biregularLocus_of_isSmall hf P
  have hfpb := MMP.Flips.IsBirationalContraction.surjective_and_isBirational
    hfp.toIsBirationalContraction
  have hb := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfpb.2 hz.le
  obtain ⟨x', hx'⟩ := hfpb.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

/-- Across two small contractions `f : X ⟶ W ⟵ X' : f⁺` onto a normal variety, a prime divisor
`P'` of `X'` over the same point of `W` as a prime divisor `P` of `X` is the strict transform of
`P`, and every strict transform `(f⁺)⁻¹_* f_* D` has at `P'` the coefficient of `D` at `P`. -/
private theorem flipTransformPrimeDivisor_eq_some_of_isSmall [IsIntegral X] [IsIntegral X']
    (hW : IsNormalVariety ℂ sW) {f : X ⟶ W} {fp : X' ⟶ W}
    (hf : MMP.Flips.IsSmall ℂ sW sX f) (hfp : MMP.Flips.IsSmall ℂ sW sX' fp)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) :
    flipTransformPrimeDivisor f fp P = some P' ∧
      ∀ (D : RDivisor X), flipTransform f fp D P' = D P := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hW
  haveI : IsProper f := hf.isProper
  haveI : IsProper fp := hfp.isProper
  have hfb := MMP.Flips.IsBirationalContraction.surjective_and_isBirational
    hf.toIsBirationalContraction
  have hfpb := MMP.Flips.IsBirationalContraction.surjective_and_isBirational
    hfp.toIsBirationalContraction
  have hfb' : IsBirationalMorphism f := hfb.2
  have hfpb' : IsBirationalMorphism fp := hfpb.2
  haveI := hfb'.isDominant
  obtain ⟨-, hc⟩ := map_genericPoint_mem_biregularLocus_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
  have hbp : Q.genericPoint ∈ biregularLocus fp :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfpb' (hQ ▸ hc).le
  have := Q.isDiscreteValuationRing_localRing
  refine ⟨?_, fun D => ?_⟩
  · unfold flipTransformPrimeDivisor
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hQ,
      Option.bind_some]
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (hPP'.trans hQ) (by rw [hPP'.trans hQ]; exact hbp)
  · exact MMP.Fourfold.flipTransform_apply_of_map_genericPoint hfb'.functionFieldMap_bijective
      hfpb.1.surj hQ (hPP'.trans hQ) hbp D

end SmallPrimes

/-- The strict transforms `S_{N₀ + k}` of a prime divisor `S` of the model `X_{N₀}` along the
diagrams `X_i ⟶ W_i ⟵ X_{i+1}` of a program, `none` once a transform is not a prime divisor. -/
private noncomputable def primeSeq {X : Scheme.{0}} {Y W : ℕ → Scheme.{0}}
    (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i) (N₀ : ℕ)
    (S : MMP.Mori.PrimeDivisor (modelSeq X Y N₀)) :
    ∀ k, Option (MMP.Mori.PrimeDivisor (modelSeq X Y (N₀ + k)))
  | 0 => some S
  | k + 1 => (primeSeq f fp N₀ S k).bind (flipTransformPrimeDivisor (f (N₀ + k)) (fp (N₀ + k)))

/-- The strict transforms `D_{N₀ + k}` of a divisor `D` of the model `X_{N₀}` along the diagrams
`X_i ⟶ W_i ⟵ X_{i+1}` of a program. -/
private noncomputable def tailTransformSeq {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y W : ℕ → Scheme.{0}} (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i) (N₀ : ℕ)
    (D : DivisorWithCoeffs R (modelSeq X Y N₀)) : ∀ k, DivisorWithCoeffs R (modelSeq X Y (N₀ + k))
  | 0 => D
  | k + 1 => flipTransform (f (N₀ + k)) (fp (N₀ + k)) (tailTransformSeq f fp N₀ D k)

section PartialIsoTransform

variable {X Y : Scheme.{0}}

/-- If a partial isomorphism `e : X ⇢ Y` sends the generic point of a prime divisor `P` of `X` to
the generic point of a prime divisor `F` of `Y`, then `F` is the strict transform of `P`. -/
private theorem transformPrimeDivisor_eq_some_of_mem_source [IsReduced X] [IsIntegral Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (e : X.PartialIso Y) {P : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y} (hP : P.genericPoint ∈ e.source)
    (hF : e.toPartialMap.hom ⟨P.genericPoint, hP⟩ = F.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some F := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨e.toPartialMap, hP, rfl⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform e.toRationalMap P.idealSheaf.support =
      F.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton e.toPartialMap rfl P hP, hF]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure F).symm
  have := F.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- `e⁻¹ ∘ e` is the identity of `X`, as a rational map. -/
private theorem toRationalMap_comp_symm [IsIntegral X] [IsIntegral Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (e : X.PartialIso Y) [IsDominant e.toPartialMap.hom] :
    (e.toPartialMap.comp e.symm.toPartialMap).toRationalMap =
      (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
  rw [Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme), Category.comp_id]
  set U := e.toPartialMap.hom ⁻¹ᵁ e.symm.toPartialMap.domain with hU
  have h1 : e.toPartialMap.hom ∣_ e.symm.toPartialMap.domain = U.ι ≫ e.iso.hom := by
    refine (cancel_mono (Scheme.Opens.ι e.symm.toPartialMap.domain)).mp ?_
    exact (morphismRestrict_ι _ _).trans (Category.assoc _ _ _).symm
  refine (cancel_epi (e.toPartialMap.domain.ι.isoImage U).hom).mp ?_
  change (e.toPartialMap.domain.ι.isoImage U).hom ≫ ((e.toPartialMap.domain.ι.isoImage U).inv ≫
      e.toPartialMap.hom ∣_ e.symm.toPartialMap.domain ≫ (e.iso.inv ≫ e.source.ι)) =
    (e.toPartialMap.domain.ι.isoImage U).hom ≫ (e.toPartialMap.domain.ι ''ᵁ U).ι
  rw [Iso.hom_inv_id_assoc, Scheme.Hom.isoImage_hom_ι]
  exact (congrArg (· ≫ e.iso.inv ≫ e.source.ι) h1).trans
    ((Category.assoc _ _ _).trans (congrArg (U.ι ≫ ·) (e.iso.hom_inv_id_assoc e.source.ι)))

/-- If a partial isomorphism `e : X ⇢ Y` transforms the prime divisor `P` into `F` and `η_F` lies
in its target, then `η_P` lies in its source and `e(η_P) = η_F`. -/
private theorem mem_source_of_transformPrimeDivisor_eq_some [IsIntegral X] [IsIntegral Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] (e : X.PartialIso Y)
    {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some F)
    (hF : F.genericPoint ∈ e.target) :
    ∃ hP : P.genericPoint ∈ e.source,
      e.toPartialMap.hom ⟨P.genericPoint, hP⟩ = F.genericPoint := by
  obtain ⟨g', hg'η, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hg'η
  have : IsDominant e.target.ι := AlgebraicGeometry.Opens.isDominant_ι e.dense_target
  have he : IsDominant e.toPartialMap.hom := by
    change IsDominant (e.iso.hom ≫ e.target.ι)
    infer_instance
  have : IsDominant g'.hom := (Scheme.PartialMap.isDominant_hom_iff_of_equiv g' e.toPartialMap
    (Scheme.PartialMap.toRationalMap_eq_iff.mp hg')).mpr he
  have hcomp : (g'.comp e.symm.toPartialMap).toRationalMap =
      (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
    rw [← toRationalMap_comp_symm e, ← Scheme.RationalMap.toRationalMap_comp,
      ← Scheme.RationalMap.toRationalMap_comp]
    have key : ∀ (φ₁ φ₂ : X ⤏ Y) (_ : φ₁ = φ₂) [φ₁.IsDominant] [φ₂.IsDominant],
        φ₁.comp e.symm.toRationalMap = φ₂.comp e.symm.toRationalMap := by
      rintro φ₁ φ₂ rfl _ _
      rfl
    exact key _ _ hg'
  have hmem : P.genericPoint ∈ (g'.comp e.symm.toPartialMap).domain :=
    ⟨⟨P.genericPoint, hg'η⟩, show g'.hom ⟨P.genericPoint, hg'η⟩ ∈ e.target from hη ▸ hF, rfl⟩
  have h1 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hcomp hmem
    (show P.genericPoint ∈ (Scheme.Hom.toPartialMap (𝟙 X)).domain from trivial)
  have hval : (Scheme.Hom.toPartialMap (𝟙 X)).hom ⟨P.genericPoint, trivial⟩ = P.genericPoint := rfl
  have key : ∀ {T U : Scheme.{0}} (a : T ⟶ U) (b : U ⟶ e.target.toScheme)
      (t : T), (a ≫ b ≫ (e.iso.inv ≫ e.source.ι)) t ∈ e.source := fun a b t => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := e.source.ι) (e.iso.inv (b (a t)))
    rwa [Scheme.Opens.range_ι] at this
  have hP : P.genericPoint ∈ e.source := by
    rw [← hval, ← h1]
    exact key _ _ _
  exact ⟨hP, hη ▸ MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hg'.symm hP hg'η⟩

end PartialIsoTransform

section PartialIsoTrans

variable {X Y Z : Scheme.{0}}

/-- Restricting the source of a partial isomorphism to `U` restricts its underlying map. -/
private theorem restrictSource_iso_hom_comp_ι (g : Y.PartialIso Z) (U : Y.Opens)
    (hU : Dense (U : Set Y)) (hU' : U ≤ g.source) :
    (g.restrictSource U hU hU').iso.hom ≫ (g.restrictSource U hU hU').target.ι =
      Y.homOfLE hU' ≫ g.iso.hom ≫ g.target.ι := by
  have h : (Scheme.Opens.isoOfLE hU').inv ≫ (g.source.ι ⁻¹ᵁ U).ι = Y.homOfLE hU' := by
    rw [← cancel_mono g.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  simp [Scheme.PartialIso.restrictSource, reassoc_of% h]

/-- Restricting the target of a partial isomorphism to `U` restricts its inverse map. -/
private theorem restrictTarget_iso_inv_comp_ι (f : X.PartialIso Y) (U : Y.Opens)
    (hU : Dense (U : Set Y)) (hU' : U ≤ f.target) :
    (f.restrictTarget U hU hU').iso.inv ≫ (f.restrictTarget U hU hU').source.ι =
      Y.homOfLE hU' ≫ f.iso.inv ≫ f.source.ι :=
  restrictSource_iso_hom_comp_ι f.symm U hU hU'

/-- A point of the source of `f` that `f` maps into the source of `g` lies in the source of the
composite `f.trans g`. -/
private theorem mem_trans_source (f : X.PartialIso Y) (g : Y.PartialIso Z) {x : X}
    (hx : x ∈ f.source) (hfx : f.toPartialMap.hom ⟨x, hx⟩ ∈ g.source) :
    x ∈ (f.trans g).source := by
  change x ∈ f.source.ι ''ᵁ (f.iso.inv ''ᵁ (f.target.ι ⁻¹ᵁ (f.target ⊓ g.source)))
  rw [← SetLike.mem_coe]
  simp
  exact ⟨⟨x, hx⟩, ⟨(f.iso.hom ⟨x, hx⟩).2, hfx⟩, rfl⟩

/-- A point of the target of `g` whose preimage under `g` lies in the target of `f` lies in the
target of the composite `f.trans g`. -/
private theorem mem_trans_target (f : X.PartialIso Y) (g : Y.PartialIso Z) {z : Z}
    (hz : z ∈ g.target) (hgz : g.symm.toPartialMap.hom ⟨z, hz⟩ ∈ f.target) :
    z ∈ (f.trans g).target := by
  change z ∈ g.target.ι ''ᵁ (g.iso.hom ''ᵁ (g.source.ι ⁻¹ᵁ (f.target ⊓ g.source)))
  rw [← SetLike.mem_coe]
  simp
  refine ⟨g.iso.inv ⟨z, hz⟩, ⟨hgz, (g.iso.inv ⟨z, hz⟩).2⟩, ?_⟩
  show (g.iso.inv ≫ g.iso.hom ≫ g.target.ι) ⟨z, hz⟩ = z
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- On the source of a composite `f.trans g`, the composite is `x ↦ g (f x)`. -/
private theorem exists_trans_apply (f : X.PartialIso Y) (g : Y.PartialIso Z) {x : X}
    (hx : x ∈ (f.trans g).source) : ∃ (hx1 : x ∈ f.source)
      (hx2 : f.toPartialMap.hom ⟨x, hx1⟩ ∈ g.source),
      (f.trans g).toPartialMap.hom ⟨x, hx⟩ = g.toPartialMap.hom ⟨_, hx2⟩ := by
  have hV := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  set f' := f.restrictTarget _ hV inf_le_left
  set g' := g.restrictSource _ hV inf_le_right
  let q : f'.target.toScheme := f'.iso.hom ⟨x, hx⟩
  have hq1 := congrArg (fun φ => φ q) (restrictTarget_iso_inv_comp_ι f _ hV inf_le_left)
  have hq2 := congrArg (fun φ => φ q) (restrictSource_iso_hom_comp_ι g _ hV inf_le_right)
  simp only [Scheme.Hom.comp_apply] at hq1 hq2
  have hinv : f'.iso.inv q = ⟨x, hx⟩ := by
    show (f'.iso.hom ≫ f'.iso.inv) ⟨x, hx⟩ = ⟨x, hx⟩
    rw [Iso.hom_inv_id]
    rfl
  rw [hinv] at hq1
  have hx' : x = f.source.ι (f.iso.inv (Y.homOfLE inf_le_left q)) := hq1
  have hmem : ∀ p : f.source.toScheme, f.source.ι p ∈ f.source := fun p => by
    have := Set.mem_range_self (f := f.source.ι) p
    rwa [Scheme.Opens.range_ι] at this
  have hx1 : x ∈ f.source := hx' ▸ hmem _
  have hpt : (⟨x, hx1⟩ : f.source.toScheme) = f.iso.inv (Y.homOfLE inf_le_left q) :=
    Subtype.ext hx'
  have hfx : f.iso.hom ⟨x, hx1⟩ = Y.homOfLE inf_le_left q := by
    rw [hpt]
    show (f.iso.inv ≫ f.iso.hom) _ = _
    rw [Iso.inv_hom_id]
    rfl
  have hval1 : f.toPartialMap.hom ⟨x, hx1⟩ = q.1 := by
    show f.target.ι (f.iso.hom ⟨x, hx1⟩) = q.1
    rw [hfx]
    exact Scheme.homOfLE_apply _ _
  have hx2 : f.toPartialMap.hom ⟨x, hx1⟩ ∈ g.source := hval1 ▸ q.2.2
  refine ⟨hx1, hx2, ?_⟩
  have hq : Y.homOfLE (inf_le_right : f.target ⊓ g.source ≤ g.source) q = ⟨_, hx2⟩ :=
    Subtype.ext ((Scheme.homOfLE_apply _ _).trans hval1.symm)
  show g'.target.ι (g'.iso.hom ((Y.isoOfEq rfl).hom q)) = g.target.ι (g.iso.hom ⟨_, hx2⟩)
  rw [Scheme.isoOfEq_rfl, Iso.refl_hom]
  refine hq2.trans ?_
  show g.target.ι (g.iso.hom (Y.homOfLE inf_le_right q)) = _
  rw [hq]

end PartialIsoTrans

/-- A partial isomorphism preserves the coheight of points of its source. -/
private theorem coheight_toPartialMap_hom {X Y : Scheme.{0}} (e : X.PartialIso Y) {x : X}
    (hx : x ∈ e.source) : Order.coheight (e.toPartialMap.hom ⟨x, hx⟩) = Order.coheight x := by
  let p : e.source.toScheme := ⟨x, hx⟩
  have h1 : Order.coheight ((e.iso.hom ≫ e.target.ι) p) = Order.coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ (e.iso.hom ≫ e.target.ι).isOpenEmbedding
  have h2 : Order.coheight (e.source.ι p) = Order.coheight p :=
    Topology.IsOpenEmbedding.coheight_eq _ e.source.ι.isOpenEmbedding
  exact h1.trans h2.symm

/-- **A step of a program as a partial isomorphism.** For proper birational morphisms
`f : X ⟶ W ⟵ X' : f⁺` onto a normal variety, where `f⁺` is an isomorphism over the image of every
point of `X'` of coheight at most one, there is a partial isomorphism `X ⇢ X'` over `W`, the
isomorphism over the common biregular locus, whose target contains every point of coheight at most
one; its source contains every point of coheight at most one when `f` is likewise an isomorphism
over their images. -/
private theorem exists_stepPartialIso {X X' W : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (f : X ⟶ W) (fp : X' ⟶ W)
    [IsProper f] [IsProper fp] (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp) :
    ∃ s : X.PartialIso X', s.IsOver f fp ∧
      (∀ y : X', Order.coheight y ≤ 1 → y ∈ s.target) ∧
      ((∀ x : X, Order.coheight x ≤ 1 → f x ∈ biregularLocus f) →
        ∀ x : X, Order.coheight x ≤ 1 → x ∈ s.source) := by
  set U := commonBiregularLocus f fp
  have : IsIso (f ∣_ U) := isBiregular_commonBiregularLocus_left f fp
  have : IsIso (fp ∣_ U) := isBiregular_commonBiregularLocus_right f fp
  have hbf : ∀ w : W, Order.coheight w ≤ 1 → w ∈ biregularLocus f := fun w hw =>
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hf hw
  have hbfp : ∀ w : W, Order.coheight w ≤ 1 → w ∈ biregularLocus fp := fun w hw =>
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfp hw
  have hη : Order.coheight (genericPoint W) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  obtain ⟨x₀, hx₀⟩ := surjective_of_isProper_of_isBirationalMorphism f hf (genericPoint W)
  obtain ⟨y₀, hy₀⟩ := surjective_of_isProper_of_isBirationalMorphism fp hfp (genericPoint W)
  have hU₀ : genericPoint W ∈ U := ⟨hbf _ hη, hbfp _ hη⟩
  refine ⟨⟨f ⁻¹ᵁ U, (f ⁻¹ᵁ U).2.dense ⟨x₀, show f x₀ ∈ U from hx₀ ▸ hU₀⟩, fp ⁻¹ᵁ U,
    (fp ⁻¹ᵁ U).2.dense ⟨y₀, show fp y₀ ∈ U from hy₀ ▸ hU₀⟩,
    asIso (f ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm⟩, ?_, fun y hy => ?_, fun hf1 x hx => ?_⟩
  · change ((f ∣_ U) ≫ inv (fp ∣_ U)) ≫ (fp ⁻¹ᵁ U).ι ≫ fp = (f ⁻¹ᵁ U).ι ≫ f
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  · have hb := hfp1 y hy
    refine ⟨?_, hb⟩
    refine hbf _ ?_
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb]
    exact hy
  · have hb := hf1 x hx
    refine ⟨hb, hbfp _ ?_⟩
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb]
    exact hx

/-- Every prime divisor whose generic point lies in the target of a partial isomorphism `e` is the
strict transform of a prime divisor under `e`. -/
private theorem exists_transformPrimeDivisor_eq_some_of_mem_target {X Y : Scheme.{0}}
    [IsReduced X] [IsIntegral Y] [IsSeparated (Y ↘ ⊤_ Scheme)] (e : X.PartialIso Y)
    (F : MMP.Mori.PrimeDivisor Y) (hF : F.genericPoint ∈ e.target) :
    ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some F := by
  let q : e.target.toScheme := ⟨_, hF⟩
  have hco : Order.coheight (e.source.ι (e.iso.inv q)) = 1 :=
    (coheight_toPartialMap_hom e.symm hF).trans F.coheight_genericPoint
  let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hPη : P.genericPoint = e.source.ι (e.iso.inv q) :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hmem : ∀ p : e.source.toScheme, e.source.ι p ∈ e.source := fun p => by
    have := Set.mem_range_self (f := e.source.ι) p
    rwa [Scheme.Opens.range_ι] at this
  have hP : P.genericPoint ∈ e.source := hPη ▸ hmem _
  refine ⟨P, transformPrimeDivisor_eq_some_of_mem_source e hP ?_⟩
  have hpt : (⟨P.genericPoint, hP⟩ : e.source.toScheme) = e.iso.inv q := Subtype.ext hPη
  have h1 : (e.iso.hom ≫ e.target.ι) (e.iso.inv q) = F.genericPoint := by
    show (e.iso.inv ≫ e.iso.hom ≫ e.target.ι) q = F.genericPoint
    rw [Iso.inv_hom_id_assoc]
    rfl
  exact (congrArg (fun p => (e.iso.hom ≫ e.target.ι) p) hpt).trans h1

/-- The composites `X = X₀ ⇢ X₁ ⇢ ⋯ ⇢ X_i` of partial isomorphisms between the models of a
program. -/
private noncomputable def compositePartialIso {X : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    (step : ∀ i, (modelSeq X Y i).PartialIso (modelSeq X Y (i + 1))) :
    ∀ i, X.PartialIso (modelSeq X Y i)
  | 0 => Scheme.PartialIso.refl X
  | i + 1 => (compositePartialIso step i).trans (step i)

section DltFloor

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)}

/-- Adding a nonnegative multiple of an effective Cartier divisor to the boundary does not raise a
log discrepancy. -/
private theorem exists_isLogDiscrepancy_add_smul_le {n : ℕ} {B : RDivisor X}
    {D : DivisorOver k sX} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a) {t : ℝ}
    (ht : 0 ≤ t) {L : Divisor X} (hL : L.IsCartier) (hL0 : ∀ P, 0 ≤ L.coeff P) :
    ∃ a', MMP.Intersection.IsLogDiscrepancy sX n (B + t • Divisor.toRDivisor L) D a' ∧
      a' ≤ a := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨L', hL'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hL
  have hc : (0 : ℝ) ≤ (L'.coeff D.E : ℝ) := by
    have hnn := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hL (V := ⊤)
      (fun P _ => hL0 P) hL' D.E ((D.E.genericPoint_mem_iff _).mp trivial)
    exact_mod_cast hnn
  obtain ⟨hX, hp, ω, hω, hK, m, r, C, C', hC, hsum, hpb, rfl⟩ := ha
  refine ⟨_, ⟨hX, hp, ω, hω, hK, m + 1, Fin.cons t r, Fin.cons L C, Fin.cons L' C', fun i => ?_,
    fun Γ => ?_, fun i => ?_, rfl⟩, ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hL
    · simpa using hC j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    rw [← hsum Γ]
    ring
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨_, hL'⟩
    · simpa using hpb j
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    nlinarith

/-- On a `ℚ`-factorial variety, adding an effective divisor to the boundary does not raise a log
discrepancy. -/
private theorem exists_isLogDiscrepancy_add_le (hXq : IsQFactorial sX) {n : ℕ}
    {D : DivisorOver k sX} (G : RDivisor X) (hG : ∀ P, 0 ≤ G.coeff P) :
    ∀ (B : RDivisor X) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B D a →
      ∃ a', MMP.Intersection.IsLogDiscrepancy sX n (B + G) D a' ∧ a' ≤ a := by
  classical
  induction G using Finsupp.induction with
  | zero => exact fun B a ha => ⟨a, by simpa using ha, le_rfl⟩
  | single_add P b f hPf hb ih =>
    intro B a ha
    have hf : ∀ Q, 0 ≤ DivisorWithCoeffs.coeff f Q := fun Q => by
      by_cases hQ : Q = P
      · subst hQ
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hPf]
      · have := hG Q
        rwa [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply,
          Finsupp.single_eq_of_ne' (Ne.symm hQ), zero_add] at this
    have hb0 : 0 ≤ b := by
      have := hG P
      rwa [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hPf, add_zero] at this
    obtain ⟨a₁, ha₁, hle₁⟩ := ih hf B a ha
    obtain ⟨m, hm, hmC⟩ := hXq.2 (Finsupp.single P 1)
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    obtain ⟨a₂, ha₂, hle₂⟩ := exists_isLogDiscrepancy_add_smul_le ha₁ (div_nonneg hb0 hm'.le)
      hmC (fun Q => by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs <;> simp)
    refine ⟨a₂, ?_, hle₂.trans hle₁⟩
    have heq : B + f + (b / m) • Divisor.toRDivisor ((m : ℤ) • Finsupp.single P 1) =
        B + (Finsupp.single P b + f) := by
      refine Finsupp.ext fun Q => ?_
      rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul]
      rw [← DivisorWithCoeffs.coeff_apply (Divisor.toRDivisor _), Divisor.coeff_toRDivisor,
        DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
        Finsupp.single_apply]
      split_ifs
      · push_cast
        field_simp
        simp only [Int.ofNat_eq_coe, Int.cast_natCast, zsmul_eq_mul, nsmul_eq_mul, mul_one]
        ring
      · simp
    rwa [heq] at ha₂

/-- On a `ℚ`-factorial variety, raising the boundary does not raise a log discrepancy. -/
private theorem exists_isLogDiscrepancy_le_of_le (hXq : IsQFactorial sX) {n : ℕ}
    {D : DivisorOver k sX} {Γ₁ Γ₂ : RDivisor X} (hle : ∀ P, Γ₁.coeff P ≤ Γ₂.coeff P) {b : ℝ}
    (hb : MMP.Intersection.IsLogDiscrepancy sX n Γ₁ D b) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX n Γ₂ D a ∧ a ≤ b := by
  obtain ⟨a, ha, hab⟩ := exists_isLogDiscrepancy_add_le hXq (Γ₂ - Γ₁)
    (fun P => by rw [DivisorWithCoeffs.coeff_sub]; linarith [hle P]) Γ₁ b hb
  rw [add_sub_cancel] at ha
  exact ⟨a, ha, hab⟩

end DltFloor

/-- **The round down of a real dlt boundary is a dlt boundary.** On a `ℚ`-factorial variety, if
`(X, Γ)` is dlt with real boundary, so is `(X, ⌊Γ⌋)`: the log discrepancies of `⌊Γ⌋` dominate
those of `Γ`, and the support of `⌊Γ⌋` lies in that of `Γ`. -/
private theorem isDltPair_roundDown_of_isRealDltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hXq : IsQFactorial sX)
    {Γ : RDivisor X} (hΓ : IsRealDltPair sX Γ) :
    MMP.Intersection.IsDltPair sX (Divisor.toQDivisor (DivisorWithCoeffs.roundDown Γ)) := by
  classical
  obtain ⟨⟨hX, hΓ0, ⟨n, K, hK, -⟩, hlc⟩, hΓ1, Z, hsm, hsnc, hpos⟩ := hΓ
  set T := DivisorWithCoeffs.roundDown Γ with hTdef
  have hTc : ∀ P, T.coeff P = if Γ.coeff P = 1 then 1 else 0 := fun P => by
    rw [hTdef, DivisorWithCoeffs.coeff_roundDown]
    split_ifs with h
    · rw [h, Int.floor_one]
    · rw [Int.floor_eq_zero_iff]
      exact ⟨hΓ0 P, lt_of_le_of_ne (hΓ1 P) h⟩
  have hTR : ∀ P, (QDivisor.toRDivisor (Divisor.toQDivisor T)).coeff P =
      if Γ.coeff P = 1 then 1 else 0 := fun P => by
    rw [QDivisor.coeff_toRDivisor, Divisor.coeff_toQDivisor, hTc]
    split_ifs <;> simp
  -- the log discrepancies of `⌊Γ⌋` dominate those of `Γ`
  have hTle : ∀ P, (QDivisor.toRDivisor (Divisor.toQDivisor T)).coeff P ≤ Γ.coeff P := fun P => by
    rw [hTR]
    split_ifs with h
    · exact h.ge
    · exact hΓ0 P
  refine ⟨⟨⟨hX, n, K, hK, ?_⟩, fun P => ?_, fun n' D b hb => ?_⟩, fun P => ?_, Z, hsm, ?_,
    fun n' D hDZ b hb => ?_⟩
  · obtain ⟨m, hm, hmC⟩ := hXq.2 (K + T)
    refine ⟨m, by exact_mod_cast hm.ne', (m : ℤ) • (K + T), ?_, hmC⟩
    ext P
    simp [Divisor.coeff_toQDivisor]
  · rw [Divisor.coeff_toQDivisor, hTc]
    split_ifs <;> norm_num
  · obtain ⟨a, ha, hle⟩ := exists_isLogDiscrepancy_le_of_le hXq hTle hb
    exact (hlc n' D a ha).trans hle
  · rw [Divisor.coeff_toQDivisor, hTc]
    split_ifs <;> norm_num
  · refine hsnc.of_support_subset fun E hE => ?_
    rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen] at hE ⊢
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    apply hE
    change (Divisor.toQDivisor T).coeff _ = 0
    change Γ.coeff _ = 0 at h0
    rw [Divisor.coeff_toQDivisor, hTc, h0]
    simp
  · obtain ⟨a, ha, hle⟩ := exists_isLogDiscrepancy_le_of_le hXq hTle hb
    exact (hpos n' D hDZ a ha).trans_le hle

/-- The strict transforms `D_i` of a divisor `D` on the models of a sequence of diagrams
`X_i ⟶ W_i ⟵ X_{i+1}`: `D_0 = D` and `D_{i+1} = (f_i⁺)⁻¹_* (f_i)_* D_i`. -/
private noncomputable def transformSeq {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y W : ℕ → Scheme.{0}} (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i)
    (D : DivisorWithCoeffs R X) : ∀ i, DivisorWithCoeffs R (modelSeq X Y i)
  | 0 => D
  | i + 1 => flipTransform (f i) (fp i) (transformSeq f fp D i)

/-- The linear extension of a partial map `φ` on prime divisors has, at a prime divisor `F` with a
unique preimage `P`, the coefficient at `P`. -/
private theorem mapPrimeDivisors_apply_of_unique {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y} (hP : φ P = some F)
    (hu : ∀ Q, φ Q = some F → Q = P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D F = D P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', Finsupp.add_apply]
  | single Q r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hQ : φ Q with _ | F'
    · have hne : Q ≠ P := fun h => by rw [h, hP] at hQ; cases hQ
      exact (Finsupp.single_eq_of_ne' hne).symm
    · by_cases hF : F' = F
      · subst hF
        obtain rfl := hu Q hQ
        simp
      · have hne : Q ≠ P := fun h => hF (by rw [h, hP] at hQ; exact (Option.some.inj hQ).symm)
        change Finsupp.single F' r F = Finsupp.single Q r P
        rw [Finsupp.single_eq_of_ne' hF, Finsupp.single_eq_of_ne' hne]

/-- The rational map of a partial isomorphism over `S` lies over `S`. -/
private theorem compHom_toRationalMap_eq_of_isOver {X Y S : Scheme.{0}} [IsReduced X]
    [IsSeparated (S ↘ ⊤_ Scheme)] {sX : X ⟶ S} {sY : Y ⟶ S} {e : X.PartialIso Y}
    (he : e.IsOver sX sY) : e.toRationalMap.compHom sY = sX.toRationalMap := by
  show e.toPartialMap.toRationalMap.compHom sY = _
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  simpa only [Scheme.PartialMap.compHom, Scheme.PartialIso.toPartialMap, Category.assoc]
    using he

section Numerical

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The empty presentation computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX 0 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every presentation of an `ℝ`-Cartier divisor computes some value of `D · C`. -/
private theorem exists_isRIntersectionNumber {D : RDivisor X} (hD : IsCartierCombination D)
    (C : ProperCurve sX) : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX D r L C x := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  have h := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL
  refine ⟨m, r, L, ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ), ?_⟩
  rwa [hDeq, show (fun j => r j • DivisorWithCoeffs.mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero (L j))
    = fun j => r j • Divisor.toRDivisor (L j) from by
      funext j; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]]

/-- `ℝ`-Cartier divisors form a real vector space. -/
private theorem isCartierCombination_add_smul {D N : RDivisor X} (hD : IsCartierCombination D)
    (hN : IsCartierCombination N) (c : ℝ) : IsCartierCombination (D + c • N) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  obtain ⟨m', r', L', hL', rfl⟩ := hN
  refine ⟨m + m', Fin.append r (c • r'), Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add, Finset.smul_sum]
    simp [smul_smul]

/-- A numerically trivial divisor computes `0` on every contracted curve. -/
private theorem eq_zero_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) {C : ProperCurve sX} (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX N r L C x) : x = 0 :=
  hN.2.2 C hC m r L x 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)

/-- Adding a multiple of a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyEquivalentOver ℂ sX f (D + c • N) D := by
  refine ⟨isCartierCombination_add_smul hD hN.1 c, hD,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨m₃, r₃, L₃, x₃, h₃⟩ := exists_isRIntersectionNumber hN.1 C
  have h0 := eq_zero_of_isNumericallyTrivialOver hN hC h₃
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D N r₂ L₂ r₃ L₃ x₂ x₃ 1 c h₂ h₃
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum, h0]
  ring

/-- The sum of numerically trivial divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_add_smul {f : X ⟶ Y} {T N : RDivisor X}
    (hT : IsNumericallyTrivialOver ℂ sX f T) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyTrivialOver ℂ sX f (T + c • N) := by
  refine ⟨isCartierCombination_add_smul hT.1 hN.1 c, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0,
    by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨_, rT, LT, xT, hxT⟩ := exists_isRIntersectionNumber hT.1 C
  obtain ⟨_, rN, LN, xN, hxN⟩ := exists_isRIntersectionNumber hN.1 C
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 T N rT LT rN LN xT xN 1 c hxT hxN
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C), eq_zero_of_isNumericallyTrivialOver hT hC hxT,
    eq_zero_of_isNumericallyTrivialOver hN hC hxN]
  ring

/-- A multiple of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_smul {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) (a : ℝ) :
    IsNumericallyTrivialOver ℂ sX f (a • N) := by
  have := isNumericallyTrivialOver_add_smul hN hN (a - 1)
  convert this using 1
  module

/-- An `ℝ`-Cartier divisor numerically equivalent over `Y` to an `f`-nef one is `f`-nef. -/
private theorem isRelativelyNef_of_isNumericallyEquivalentOver {f : X ⟶ Y} {D D' : RDivisor X}
    (h : IsNumericallyEquivalentOver ℂ sX f D' D) (hD : IsRelativelyNef ℂ sX f D) :
    IsRelativelyNef ℂ sX f D' := by
  obtain ⟨m, r, L, hL, hDeq, hnef⟩ := hD
  obtain ⟨m', r', L', hL', hD'eq⟩ := h.1
  refine ⟨m', r', L', hL', by rw [hD'eq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x hx => ?_⟩
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL
  rw [← hDeq] at hy
  rw [h.2.2 C hC m' r' L' x m r L _ hx hy]
  exact hnef C hC _ hy

/-- A relatively nef divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyNef {f : X ⟶ Y} {D : RDivisor X}
    (hD : IsRelativelyNef ℂ sX f D) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hDeq, -⟩ := hD
  exact ⟨m, r, L, hL, by rw [hDeq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- Adding a multiple of a numerically trivial divisor preserves relative nefness. -/
private theorem isRelativelyNef_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsRelativelyNef ℂ sX f D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsRelativelyNef ℂ sX f (D + c • N) :=
  isRelativelyNef_of_isNumericallyEquivalentOver
    (isNumericallyEquivalentOver_add_smul (isCartierCombination_of_isRelativelyNef hD) hN c) hD

/-- A nonnegative multiple of a relatively nef divisor is relatively nef. -/
private theorem isRelativelyNef_smul {f : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef ℂ sX f D) {c : ℝ} (hc : 0 ≤ c) : IsRelativelyNef ℂ sX f (c • D) := by
  obtain ⟨m, r, L, hL, hD, hn⟩ := h
  have hD' : c • D = ∑ j, (c • r) j • Divisor.toRDivisor (L j) := by
    rw [hD, Finset.smul_sum]; simp [smul_smul]
  refine ⟨m, c • r, L, hL, hD', fun C hC x hx => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL
  rw [← hD] at e
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D D r L r L _ _ c 0 e e
  simp only [zero_smul, add_zero, zero_mul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ x _ hx hsum]
  exact mul_nonneg hc (hn C hC _ e)

variable [CompactSpace X]

/-- A Cartier divisor linearly equivalent to `0` is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent
    (f : X ⟶ Y) {D : Divisor X} (hD : D.IsCartier) (h : D.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor D) := by
  have hDc : IsCartierCombination (Divisor.toRDivisor D) :=
    ⟨1, fun _ => 1, fun _ => D, fun _ => hD, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  refine ⟨hDc, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have h₃ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => D) (fun _ => hD)
  have hDD : (∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor D) = Divisor.toRDivisor D := by simp
  rw [hDD] at h₃
  have hdeg : D.degreeOn ℂ sX C.ι C.dim_le hD = 0 :=
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hD h
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ h₃,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C)]
  simp [hdeg]

/-- A principal divisor is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_principalDivisor (g : X ⟶ Y)
    (ψ : (RationalFunctions X)ˣ) :
    IsNumericallyTrivialOver ℂ sX g (Divisor.toRDivisor (principalDivisor ψ)) :=
  isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent g
    (Divisor.isCartier_principalDivisor ψ) (Divisor.linearlyEquivalent_principalDivisor_zero ψ)

/-- A relatively ample divisor is relatively nef: it has positive degree on every contracted
curve. -/
private theorem isRelativelyNef_of_isRelativelyAmple {f : X ⟶ Y} {A : RDivisor X}
    (hA : IsRelativelyAmple f A) : IsRelativelyNef ℂ sX f A := by
  obtain ⟨m, r, L, -, hr, hL, hAeq⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  refine ⟨m, r, L, hLc, hAeq, fun C hC x hx => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hLc
  rw [← hAeq] at e
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ x _ hx e]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le (by
    exact_mod_cast (MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) C hC).le)

end Numerical

section Transforms

open MMP.Flips

/-- The linear extension of a partial map on prime divisors commutes with `Divisor.toRDivisor`. -/
private theorem mapPrimeDivisors_toRDivisor {X Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  have hs : ∀ {Z : Scheme.{0}} (P : MMP.Mori.PrimeDivisor Z) (n : ℤ),
      Divisor.toRDivisor (Finsupp.single P n : Divisor Z) = Finsupp.single P (n : ℝ) :=
    fun P n => Finsupp.mapRange_single (hf := Int.cast_zero)
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, hD, hD', map_add, map_add]
  | single P n =>
    rw [hs, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases φ P with _ | Q
    · simp
    · exact (hs Q n).symm

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with `Divisor.toRDivisor`. -/
private theorem flipTransform_toRDivisor {X X' Y : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toRDivisor D) = Divisor.toRDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply,
    RationalMap.transformDivisor, inverseTransformDivisor, mapPrimeDivisors_toRDivisor]

/-- The strict transform `(f⁺)⁻¹_* f_*` is `ℝ`-linear. -/
private theorem flipTransform_smul {X X' Y : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y) (c : ℝ)
    (D : RDivisor X) : flipTransform f fp (c • D) = c • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply,
    RationalMap.transformDivisor, inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

variable {X X' W : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X]
  [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X] [CompactSpace X']
  [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}

/-- If `f⁺` is an isomorphism over the image of every point of coheight at most one, every prime
divisor `P'` of `X'` lies over a prime divisor `Q` of `W` over which `f⁺` is an isomorphism, and
over the generic point of a prime divisor `P` of `X`. -/
private theorem exists_primeDivisor_of_biregular (hW : IsNormalVariety ℂ sW) {f : X ⟶ W}
    {fp : X' ⟶ W} [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    (P' : MMP.Mori.PrimeDivisor X') :
    ∃ (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor W),
      f P.genericPoint = Q.genericPoint ∧ fp P'.genericPoint = Q.genericPoint ∧
      Q.genericPoint ∈ biregularLocus fp ∧ Q.genericPoint ∈ biregularLocus f := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  have hb := hfp1 _ P'.coheight_genericPoint.le
  have hc : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb, P'.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hQ : fp P'.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
  have hbf : Q.genericPoint ∈ biregularLocus f :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      (by rw [← hQ, hc])
  obtain ⟨x, hx⟩ := surjective_of_isProper_of_isBirationalMorphism f hfb Q.genericPoint
  have hxc : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hx ▸ hbf), hx, ← hQ, hc]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hxc, Q,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hxc)).trans hx, hQ,
    hQ ▸ hb, hbf⟩

/-- The coefficients of a strict transform along `X ⟶ W ⟵ X'`, with `f⁺` an isomorphism over
codimension one, are coefficients of the original divisor at prime divisors over the same point
of `W`. -/
private theorem flipTransform_apply_of_biregular (hW : IsNormalVariety ℂ sW) {f : X ⟶ W}
    {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'} {Q : MMP.Mori.PrimeDivisor W}
    (hPQ : f P.genericPoint = Q.genericPoint) (hP'Q : fp P'.genericPoint = Q.genericPoint)
    (hQb : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hW
  haveI := hfb.isDominant
  have := Q.isDiscreteValuationRing_localRing
  exact MMP.Fourfold.flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    (surjective_of_isProper_of_isBirationalMorphism fp hfpb) hPQ hP'Q hQb D

/-- If `f⁺ : X' ⟶ W` is an isomorphism over the image of every point of coheight at most one,
then `(f⁺)⁻¹_* f⁺_* D = D`. -/
private theorem flipTransform_self (hW : IsNormalVariety ℂ sW) {fp : X' ⟶ W} [IsProper fp]
    (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X') : flipTransform fp fp D = D := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  ext P'
  have hb := hfp1 _ P'.coheight_genericPoint.le
  have hc : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb, P'.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hQ : fp P'.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
  exact flipTransform_apply_of_biregular hW hfpb hfpb hQ hQ (hQ ▸ hb) D

/-- **Strict transforms of principal divisors.** For a rational function `w` on `W`,
`(f⁺)⁻¹_* f_* div(f^* w) = div((f⁺)^* w)`. -/
private theorem flipTransform_principalDivisor_pullback [CompactSpace W] (hW : IsNormalVariety ℂ sW) {f : X ⟶ W}
    {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX) (hfps : fp ≫ sW = sX')
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX')
    (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    (w : (RationalFunctions W)ˣ)
    (hw : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (MMP.Mori.principalDivisor w).supp)
    (hw' : ∀ Z : irreducibleComponents X',
      fp (componentGenericPoint X' Z) ∉ (MMP.Mori.principalDivisor w).supp) :
    flipTransform f fp (MMP.Mori.principalDivisor (pullbackRationalFunction f w hw)) =
      principalDivisor (pullbackRationalFunction fp w hw') := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  have hXn : IsNormalVariety ℂ (f ≫ sW) := by rw [hfs]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sW) := by rw [hfps]; exact hX'
  have h1 := MMP.Positivity.transformDivisor_principalDivisor_pullback hW hXn hfb w hw
  have h2 := MMP.Positivity.transformDivisor_principalDivisor_pullback hW hX'n hfpb w hw'
  have h3 : flipTransform f fp (MMP.Mori.principalDivisor (pullbackRationalFunction f w hw)) =
      flipTransform fp fp (MMP.Mori.principalDivisor (pullbackRationalFunction fp w hw')) := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, h1, h2]
  rw [h3, flipTransform_self hW hfpb hfp1]

/-- **The strict transform of a canonical divisor is canonical**, along `X ⟶ W ⟵ X'` with `f⁺`
an isomorphism over codimension one. -/
private theorem isCanonicalDivisor_flipTransform (hX : IsNormalVariety ℂ sX)
    (hX' : IsNormalVariety ℂ sX') (hW : IsNormalVariety ℂ sW) {f : X ⟶ W} {fp : X' ⟶ W}
    [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX) (hfps : fp ≫ sW = sX')
    (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : QuasiCompact sW := hW.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  haveI hX1 : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI hX'1 : MMP.Mori.IsVariety ℂ sX' := hX'.1
  haveI hW1 : MMP.Mori.IsVariety ℂ sW := hW.1
  have hdimZ : topologicalKrullDim W = n := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX hfb]; exact hK.1
  have hdimX' : topologicalKrullDim X' = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX' hfpb]
    exact hdimZ
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sW hW hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sX' hX' hdimX'
  have hXn : IsNormalVariety ℂ (f ≫ sW) := by rw [hfs]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sW) := by rw [hfps]; exact hX'
  haveI : LocallyOfFiniteType (f ≫ sW) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sW) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sW) n := by rw [hfs]; exact hK
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sW) n := by rw [hfps]; exact hK₀
  have h1 := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hW hXn hfb hKZ hK1
  obtain ⟨KY, hKY, hKYeq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hW hX'n hfpb h1 hK₀'
  have heq : flipTransform f fp K = flipTransform fp fp KY := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, hKYeq]
  rw [heq, flipTransform_self hW hfpb hfp1]
  rw [hfps] at hKY
  exact hKY

end Transforms

open scoped WithZero

section Bridge

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : MMP.Flips.ProperDivisorOver ℂ sX} {b : ℝ}
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : MMP.Flips.IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Flips.coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : MMP.Flips.ProperDivisorOver ℂ sX) : ∃ b, MMP.Flips.IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : MMP.Flips.ProperDivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- A log discrepancy is a discrepancy, computed with the form inside it, plus one. -/
private theorem isDiscrepancyWith_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ (ω : RationalPluriForms sX n 1) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      MMP.Flips.IsDiscrepancyWith sX n B ω r L ⟨D, h.2.1⟩ (a - 1) := by
  obtain ⟨hX, hp, ω, hω, ⟨K, hK, hKc⟩, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  refine ⟨ω, m, r, C, hX, hK.topologicalKrullDim_eq, hω, hC, ?_, C', hpb, ?_⟩
  · refine DivisorWithCoeffs.ext' fun Γ => ?_
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    exact hrel Γ
  · exact (by linear_combination ha :
      a - 1 = (D.ordPullback ω : ℝ) - ∑ j, r j * ((C' j).coeff D.E : ℝ))

/-- A log discrepancy, against a presentation of `div(ω) + B`, gives the discrepancy `a - 1` of
the valuation in the sense of *Flips and abundance*. -/
private theorem isDiscrepancy_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) :
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B D.valuation (a - 1) := by
  obtain ⟨ω', m', r', L', hw'⟩ := isDiscrepancyWith_of_isLogDiscrepancy h
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum' : Divisor.toRDivisor (divisorOfForm ω) + B =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith h.1 hK.topologicalKrullDim_eq hω hLc hsum'
    ⟨D, h.2.1⟩
  have hab := hb.eq hw' rfl
  refine ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation ⟨D, h.2.1⟩, ⟨D, h.2.1⟩, ω, m, r,
    L, rfl, rfl, ?_⟩
  rwa [hab] at hb

/-- Every divisor with proper model has a log discrepancy once `K_X + B` is `ℝ`-Cartier. -/
private theorem exists_isLogDiscrepancy_of_isCartierCombination (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX n B D a := by
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum' : Divisor.toRDivisor (divisorOfForm ω) + B =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hX hK.topologicalKrullDim_eq hω hLc hsum' ⟨D, hD⟩
  exact ⟨_, isLogDiscrepancy_of_isDiscrepancyWith hK hb⟩

end Bridge

section FormDivisors

/-- A canonical divisor of a normal complex variety is the divisor of a nonzero rational top
form. -/
private theorem exists_divisorOfForm_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  exact ⟨ω, hω0, DivisorWithCoeffs.ext' hωK⟩

end FormDivisors

section Forms

open MMP.Flips

/-- The pull-back of rational forms along an isomorphism of function fields is surjective. -/
private theorem pullbackForms_surjective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hbij : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro σ
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
  refine ⟨c • b (), ?_⟩
  have h1 : b.repr (c • b ()) () = c := by
    simp [Module.Basis.repr_self]
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  change algebraMap K K' (b.repr (c • b ()) ()) • b' () = σ
  rw [h1, hc]
  exact basis_unit_repr_smul b' σ

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)}

/-- Every rational top form on a birational model is a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq [LocallyOfFiniteType sX] (g : Y ⟶ X)
    [IsDominant g] (hg : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hn : topologicalKrullDim X = n) (σ : RationalPluriForms (g ≫ sX) n 1) :
    ∃ ω : RationalPluriForms sX n 1, pullbackRationalPluriForms sX g ω = σ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg hd
  exact pullbackForms_surjective hg hω 1 σ

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero (g : Y ⟶ X) [IsDominant g] {n : ℕ} :
    pullbackRationalPluriForms sX g (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have h := pullbackForms_smul (K' := Y.functionField) (k := ℂ) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- On a normal variety with a canonical divisor, the divisor of every nonzero rational top form
is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n :=
  hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

end Forms

section QFactorial

open MMP.Flips

/-- An `ℝ`-divisor is the sum of its prime components with their coefficients. -/
private theorem eq_sum_coeff_smul_single {W : Scheme.{0}} (G : RDivisor W) :
    G = ∑ j : Fin G.support.card, G.coeff (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) •
      Divisor.toRDivisor
        (Finsupp.single (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1) := by
  classical
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor W → ℝ,
      ∑ j, F (G.support.equivFin.symm j) = ∑ Q ∈ G.support, F Q := fun F => by
    rw [← Finset.sum_coe_sort G.support]
    exact Equiv.sum_comp G.support.equivFin.symm (fun Q => F Q)
  refine DivisorWithCoeffs.ext' fun Q => ?_
  simp only [MMP.Flips.coeff_sum_smul_toRDivisor]
  have key : ∀ R : MMP.Mori.PrimeDivisor W,
      ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single R 1) Q : ℤ) : ℝ) =
        if R = Q then 1 else 0 := fun R => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- Dividing the coefficient by `m` undoes the multiple `m D`:
`(c / m) • (m D) = c • D` for `m > 0`. -/
private theorem div_smul_toRDivisor_zsmul {X : Scheme.{0}} (c : ℝ) {m : ℕ} (hm : 0 < m)
    (D : Divisor X) :
    (c / m) • Divisor.toRDivisor ((m : ℤ) • D) = c • Divisor.toRDivisor D := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
    div_mul_cancel₀ c (by exact_mod_cast hm.ne')]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor `G = ∑ g_P P` is the combination
`∑ (g_P / m_P) (m_P P)` of Cartier divisors, where `m_P P` is Cartier. -/
private theorem exists_presentation_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      G = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hq.2 (Finsupp.single P 1)
  set Pj : Fin G.support.card → MMP.Mori.PrimeDivisor X :=
    fun j => (G.support.equivFin.symm j : _)
  refine ⟨G.support.card, fun j => G.coeff (Pj j) / (mq (Pj j) : ℝ),
    fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1, fun j => hmqC _, ?_⟩
  conv_lhs => rw [eq_sum_coeff_smul_single G]
  exact Finset.sum_congr rfl fun j _ => (div_smul_toRDivisor_zsmul _ (hmq _) _).symm

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    IsCartierCombination G := by
  obtain ⟨m, r, L, hL, hG⟩ := exists_presentation_of_isQFactorial hq G
  exact ⟨m, r, L, hL, by rw [hG]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier, in the coefficientwise sense. -/
private theorem isRCartier_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    RDivisor.IsRCartier G := by
  obtain ⟨m, r, L, hL, hG⟩ := exists_presentation_of_isQFactorial hq G
  exact ⟨m, r, L, hL, fun Γ₀ => by rw [hG, MMP.Flips.coeff_sum_smul_toRDivisor]⟩

end QFactorial

section Comparison

open MMP.Flips

/-- Valuations pulled back along a bijection of fields agree only if they agree. -/
private theorem valuation_eq_of_comap_eq {K L : Type*} [Field K] [Field L] {φ : K →+* L}
    (hφ : Function.Bijective φ) {v w : Valuation L ℤᵐ⁰} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hφ.2 t
    exact congrArg (fun u : Valuation K ℤᵐ⁰ => u s) h

/-- For a proper birational `f : X ⟶ W` onto a normal `W` and a prime `P` of `X` over the prime
`Q` of `W`, the coefficient of `f_* D` at `Q` is that of `D` at `P`. -/
private theorem transformDivisor_apply_of_map_genericPoint {X W : Scheme.{0}} [IsIntegral X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsSeparated (W ↘ ⊤_ Scheme)]
    {f : X ⟶ W} [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor W} (h : f P.genericPoint = Q.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr h)
    (fun P₁ hP₁ => (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.Crepant.eq_of_apply_eq_of_coheight_le_one f hf
        (((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P₁ Q).mp hP₁).trans
          h.symm) (by rw [h, Q.coheight_genericPoint]))).symm) D

variable {X X' W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- A prime divisor `P` of `X` lying over the prime divisor `Q` of `W` defines, through `f`, the
valuation of `Q`. -/
private theorem valuation_ofPrimeDivisor_comap (hX : IsNormalVariety ℂ sX)
    (hW : IsNormalVariety ℂ sW) {f : X ⟶ W} (hfs : f ≫ sW = sX) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor W}
    (h : f P.genericPoint = Q.genericPoint) :
    haveI : IsIntegral W := hW.1.toIsIntegral
    haveI := hfb.isDominant
    (DivisorOver.ofPrimeDivisor ℂ hX P).valuation.comap (functionFieldMap f) =
      (DivisorOver.ofPrimeDivisor ℂ hW Q).valuation := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI := hfb.isDominant
  subst hfs
  rw [← MMP.Mori.valuation_compDivisorOver f hX hfb]
  refine MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hW _ Q ?_
  change (𝟙 X ≫ f) P.genericPoint = Q.genericPoint
  rw [Category.id_comp]
  exact h

/-- **Log discrepancies across a step** (FA 2.28 over the base). Let `f : X ⟶ W ⟵ X' : f⁺` be
proper birational morphisms of normal `ℚ`-factorial varieties onto a normal `W`, with `f⁺` an
isomorphism over codimension one. If `-(K + Γ)` is `f`-nef and `K' + Γ'` is `f⁺`-nef, for the
strict transform `Γ'` of `Γ`, then every log discrepancy `a'` over `X'` of `Γ'` is at least the
log discrepancy over `X` of `Γ` of the same valuation of `k(W)`. -/
private theorem exists_isLogDiscrepancy_le_of_isRelativelyNef
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hW : IsNormalVariety ℂ sW)
    {f : X ⟶ W} {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX)
    (hfps : fp ≫ sW = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    {nK nK' : ℕ} {K : Divisor X} {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX nK)
    (hK' : K'.IsCanonicalDivisor sX' nK') {Γ : RDivisor X}
    (hN : IsRelativelyNef ℂ sX f (-logCanonicalDivisor K Γ))
    (hN' : IsRelativelyNef ℂ sX' fp (logCanonicalDivisor K' (flipTransform f fp Γ)))
    {n : ℕ} {E' : DivisorOver ℂ sX'} {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' n (flipTransform f fp Γ) E' a') :
    ∃ (E : DivisorOver ℂ sX) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n Γ E a ∧ a ≤ a' ∧
      (haveI : IsIntegral W := hW.1.toIsIntegral
       haveI := hfb.isDominant
       haveI := hfpb.isDominant
       E.valuation.comap (functionFieldMap f) = E'.valuation.comap (functionFieldMap fp)) := by
  classical
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hW.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'.1.toQuasiCompact
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  haveI hXv : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI hX'v : MMP.Mori.IsVariety ℂ sX' := hX'.1
  haveI hWv : MMP.Mori.IsVariety ℂ sW := hW.1
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hW
  have hdX' : topologicalKrullDim X' = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha'
  have hdZ : topologicalKrullDim W = n := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX' hfpb]; exact hdX'
  have hdX : topologicalKrullDim X = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX hfb]; exact hdZ
  have hKn : K.IsCanonicalDivisor sX n := by
    have hm : nK = n := by
      have := hK.topologicalKrullDim_eq.symm.trans hdX; exact_mod_cast this
    exact hm ▸ hK
  have hK'n : K'.IsCanonicalDivisor sX' n := by
    have hm : nK' = n := by
      have := hK'.topologicalKrullDim_eq.symm.trans hdX'; exact_mod_cast this
    exact hm ▸ hK'
  set D : RDivisor W := RationalMap.transformDivisor (X := X) f.toRationalMap Γ with hD
  have hDX : ∀ (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor W),
      f P.genericPoint = Q.genericPoint → D Q = Γ P := fun P Q h =>
    transformDivisor_apply_of_map_genericPoint hfb.functionFieldMap_bijective h Γ
  have hXn : IsNormalVariety ℂ (f ≫ sW) := by rw [hfs]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sW) := by rw [hfps]; exact hX'
  have hEX : ∀ P : MMP.Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sW f P →
      DivisorWithCoeffs.coeff (Γ - birationalInverseTransform f hfb D) P = 0 := by
    intro P hP
    have hnE : ¬ (ProperDivisorOver.mk ⟨X, f, hXn, hfb, P⟩ inferInstance :
        ProperDivisorOver ℂ sW).IsExceptional := fun h => hP ⟨hXn, hfb, inferInstance, h⟩
    obtain ⟨Q, -, hQ, -⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hW _ hnE
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hW f hXn.1 hfb D hQ,
      hDX P Q hQ, sub_self]
  have hEY : ∀ P' : MMP.Mori.PrimeDivisor X', ¬ IsExceptionalPrimeDivisor sW fp P' →
      DivisorWithCoeffs.coeff (flipTransform f fp Γ - birationalInverseTransform fp hfpb D)
        P' = 0 := by
    intro P' _
    obtain ⟨P, Q, hPQ, hP'Q, hQb, -⟩ := exists_primeDivisor_of_biregular hW hfb hfp1 P'
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
      MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hW fp hX'n.1 hfpb D hP'Q,
      flipTransform_apply_of_biregular hW hfb hfpb hPQ hP'Q hQb Γ, hDX P Q hPQ, sub_self]
  have hBX : birationalInverseTransform f hfb D + (Γ - birationalInverseTransform f hfb D) = Γ :=
    add_sub_cancel _ _
  have hBY : birationalInverseTransform fp hfpb D +
      (flipTransform f fp Γ - birationalInverseTransform fp hfpb D) = flipTransform f fp Γ :=
    add_sub_cancel _ _
  subst hfs hfps
  obtain ⟨ωX, hωX0, hωXK⟩ := exists_divisorOfForm_eq hX hKn
  obtain ⟨ω, hω⟩ := exists_pullbackRationalPluriForms_eq f hfb.functionFieldMap_bijective hdZ ωX
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hωX0 (hω ▸ pullbackRationalPluriForms_zero f)
  have hωY0 : pullbackRationalPluriForms sW fp ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' fp
      hfpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdZ) hω0
  have hKY : (divisorOfForm (pullbackRationalPluriForms sW fp ω)).IsCanonicalDivisor
      (fp ≫ sW) n := isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hX' hK'n hωY0
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (fp ≫ sW) hX'
    hKY hK'n
  have hE'p : IsProper E'.f := ha'.2.1
  have hv : MMP.Flips.HasNonemptyCenter ℂ sW (E'.valuation.comap (functionFieldMap fp)) := by
    haveI := hE'p
    have hp : IsProper (MMP.Mori.compDivisorOver fp hX' hfpb E').f :=
      (inferInstance : IsProper (E'.f ≫ fp))
    have := hasNonemptyCenter_valuation (sX := sW) ⟨MMP.Mori.compDivisorOver fp hX' hfpb E', hp⟩
    rwa [show (⟨MMP.Mori.compDivisorOver fp hX' hfpb E', hp⟩ :
      MMP.Flips.ProperDivisorOver ℂ sW).valuation = E'.valuation.comap (functionFieldMap fp) from
        MMP.Mori.valuation_compDivisorOver fp hX' hfpb E'] at this
  set ef := RingEquiv.ofBijective (functionFieldMap f) hfb.functionFieldMap_bijective with hef
  have hvX : ((E'.valuation.comap (functionFieldMap fp)).comap
      (ef.symm : X.functionField →+* W.functionField)).comap (functionFieldMap f) =
      E'.valuation.comap (functionFieldMap fp) := by
    ext t
    simp only [Valuation.comap_apply]
    exact congrArg (fun x => E'.valuation (functionFieldMap fp x)) (ef.symm_apply_apply t)
  obtain ⟨hcX, -, hcmp⟩ := MMP.Flips.isDiscrepancy_le_of_isRelativelyNef
    (D := D) (E_X := Γ - birationalInverseTransform f hfb D)
    (E_Y := flipTransform f fp Γ - birationalInverseTransform fp hfpb D)
    (K_X := K) (K_Y := divisorOfForm (pullbackRationalPluriForms sW fp ω)) hW hX hX' hfb hfpb
    (by rw [hω, hωXK]) rfl hEX hEY
    (by rw [hBX]; exact hN)
    (by
      rw [hBY]
      have heq : logCanonicalDivisor (divisorOfForm (pullbackRationalPluriForms sW fp ω))
          (flipTransform f fp Γ) = logCanonicalDivisor K' (flipTransform f fp Γ) +
            (1 : ℝ) • Divisor.toRDivisor (MMP.Mori.principalDivisor φ) := by
        rw [logCanonicalDivisor, logCanonicalDivisor, ← hφ, map_sub]
        module
      rw [heq]
      exact isRelativelyNef_add_smul hN' (isNumericallyTrivialOver_principalDivisor fp φ) 1)
    hv hvX rfl
  obtain ⟨-, E, hEv⟩ := hcX
  have hKω : (divisorOfForm ωX).IsCanonicalDivisor (f ≫ sW) n := hωXK ▸ hKn
  have hcart : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + Γ) := by
    rw [hωXK]; exact isCartierCombination_of_isQFactorial hQ _
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy_of_isCartierCombination hX hωX0 hKω hcart
    E.toDivisorOver E.isProper
  refine ⟨E.toDivisorOver, a, ha, ?_, ?_⟩
  · have h1 := isDiscrepancy_of_isLogDiscrepancy ha hωX0 hKω hcart
    rw [hωXK] at h1
    have h2 := isDiscrepancy_of_isLogDiscrepancy ha' hωY0 hKY
      (isCartierCombination_of_isQFactorial hQ' _)
    have := hcmp (a - 1) (a' - 1) (by rw [hBX, ← hEv]; exact h1) (by rw [hBY]; exact h2)
    linarith
  · have hEv' : E.toDivisorOver.valuation = _ := hEv
    rw [hEv', hvX]

/-- **Positivity of exceptional log discrepancies crosses a step.** In the setting of
`exists_isLogDiscrepancy_le_of_isRelativelyNef`, let `Γ` have coefficients at most one, with
positive log discrepancy at every exceptional divisor over `X`, and with every prime of
coefficient one not contracted by `f`. Then `Γ'` has positive log discrepancy at every
exceptional divisor over `X'`. -/
private theorem logDiscrepancy_pos_flipTransform
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hW : IsNormalVariety ℂ sW)
    {f : X ⟶ W} {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX)
    (hfps : fp ≫ sW = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    {nK nK' : ℕ} {K : Divisor X} {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX nK)
    (hK' : K'.IsCanonicalDivisor sX' nK') {Γ : RDivisor X}
    (hN : IsRelativelyNef ℂ sX f (-logCanonicalDivisor K Γ))
    (hN' : IsRelativelyNef ℂ sX' fp (logCanonicalDivisor K' (flipTransform f fp Γ)))
    (hΓ1 : ∀ P, Γ.coeff P ≤ 1)
    (hexc : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Γ E a → 0 < a)
    (hfloor : ∀ P, Γ.coeff P = 1 → Order.coheight (f P.genericPoint) = 1) :
    ∀ (m : ℕ) (E' : DivisorOver ℂ sX') (a' : ℝ), E'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX' m (flipTransform f fp Γ) E' a' → 0 < a' := by
  intro m E' a' hE' ha'
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  obtain ⟨E, a, ha, hle, hv⟩ := exists_isLogDiscrepancy_le_of_isRelativelyNef hX hX' hW hfs hfps
    hfb hfpb hfp1 hQ hQ' hK hK' hN hN' ha'
  refine lt_of_lt_of_le ?_ hle
  by_cases hEx : E.IsExceptional
  · exact hexc m E a hEx ha
  obtain ⟨P, hP⟩ : ∃ Q : MMP.Mori.PrimeDivisor X,
      E.valuation = (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation := by
    rw [isExceptional_iff_two_le_coheight hX, ← MMP.Positivity.DivisorOver.codimension_center,
      MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hEx
    push Not at hEx
    exact hEx
  have hlp := MMP.Fourfold.PltReference.isLogDiscrepancy_ofPrimeDivisor hX hK
    (isRCartier_of_isQFactorial hQ (Divisor.toRDivisor K + Γ)) P
  have hap : a = 1 - Γ.coeff P :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hlp hP
  rw [hap]
  rcases (hΓ1 P).lt_or_eq with hlt | heq
  · linarith
  exfalso
  have hc := hfloor P heq
  set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hQ1 : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
  have hbQ : Q.genericPoint ∈ biregularLocus fp :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hfpb
      (by rw [← hQ1, hc])
  obtain ⟨x', hx'⟩ := surjective_of_isProper_of_isBirationalMorphism fp hfpb Q.genericPoint
  have hx'c : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hbQ), hx', ← hQ1, hc]
  set P' : MMP.Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx'c
  have hP'Q : fp P'.genericPoint = Q.genericPoint :=
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hx'c)).trans hx'
  have h1 := valuation_ofPrimeDivisor_comap hX hW hfs hfb hQ1
  have h2 := valuation_ofPrimeDivisor_comap hX' hW hfps hfpb hP'Q
  have hE'v : E'.valuation = (DivisorOver.ofPrimeDivisor ℂ hX' P').valuation := by
    refine valuation_eq_of_comap_eq hfpb.functionFieldMap_bijective ?_
    rw [← hv, hP, h1, h2]
  have h2c : 2 ≤ codimension E'.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact (isExceptional_iff_two_le_coheight hX' E').mp hE'
  exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX' E').mp h2c P' hE'v

end Comparison

section StepNumerics

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- **Pull-backs are numerically trivial over the base.** A pull-back `f^* D` of an `ℝ`-Cartier
divisor has degree zero on every curve contracted by `f`. -/
private theorem isNumericallyTrivialOver_of_isRCartierPullback [IsIntegral X] [CompactSpace X]
    {W : Scheme.{0}} [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW] (f : X ⟶ W) [IsProper f]
    (hfs : f ≫ sW = sX) {D : RDivisor W} {G : RDivisor X} (h : IsRCartierPullback f D G) :
    IsNumericallyTrivialOver ℂ sX f G := by
  subst hfs
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  choose hB hpbj using hpb
  obtain rfl : L' = fun j => (L j).pullback (hL j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL j) (hpbj j)).symm
  have hL'c : ∀ j, ((L j).pullback (hL j) (hB j)).IsCartier := fun j =>
    (hL j).isCartier_pullback f (hB j)
  refine ⟨⟨m, r, _, hL'c, by simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ (f ≫ sW) C r _ hL'c rfl h₁,
    (IsRIntersectionNumber.eq_and_linear ℂ (f ≫ sW) C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C)]
  have hc := not_isProperCurve_map_of_isContractedBy (sY := sW) f hC
  have hdeg : ∀ j, ((L j).pullback (hL j) (hB j)).degreeOn ℂ (f ≫ sW) C.ι C.dim_le (hL'c j) = 0 :=
    fun j => by
      rw [Divisor.degreeOn_pullback_eq_degree_pushforward f rfl (hL j) (hB j) C,
        OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_neg hc, map_zero]
  simp [hdeg]

/-- Relative nefness of `(1 - s) A + s T + N` for `A` nef, `T`, `N` numerically trivial and
`0 ≤ s ≤ 1`. -/
private theorem isRelativelyNef_combo {f : X ⟶ Y} {A T N : RDivisor X}
    (hA : IsRelativelyNef ℂ sX f A) (hT : IsNumericallyTrivialOver ℂ sX f T)
    (hN : IsNumericallyTrivialOver ℂ sX f N) {s : ℝ} (hs1 : s ≤ 1) :
    IsRelativelyNef ℂ sX f ((1 - s) • A + s • T + N) := by
  have h1 := isRelativelyNef_smul hA (sub_nonneg.mpr hs1)
  have h2 := isRelativelyNef_add_smul h1 hT s
  have h3 := isRelativelyNef_add_smul h2 hN 1
  simpa only [one_smul] using h3

/-- Every `ℝ`-Cartier divisor is nef over an isomorphism, which contracts no curve. -/
private theorem isRelativelyNef_of_isIso {f : X ⟶ Y} [IsIso f] {D : RDivisor X}
    (hD : IsCartierCombination D) : IsRelativelyNef ℂ sX f D := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  refine ⟨m, r, L, hL, by rw [hDeq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x _ => absurd C.isProperCurve (not_isProperCurve_of_closure_subset fun z hz => ?_)⟩
  exact (Scheme.homeoOfIso (asIso f)).injective (hC z hz)

end StepNumerics

section StepAmple

open MMP.Flips

/-- Adding a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) :
    IsNumericallyEquivalentOver ℂ sX f (D + N) D := by
  simpa only [one_smul] using isNumericallyEquivalentOver_add_smul hD hN 1

/-- **Numerically equivalent divisors are ample together** over a projective morphism of normal
varieties (FA 2.16.3). -/
private theorem isRelativelyAmple_of_isNumericallyEquivalentOver {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsProjectiveMorphism f) (hfs : f ≫ sZ = sX) {D A : RDivisor X}
    (hDA : haveI : QuasiCompact sX := hX.1.toQuasiCompact
      MMP.Flips.IsNumericallyEquivalentOver ℂ sX f D A)
    (hA : MMP.Flips.IsRelativelyAmple f A) : MMP.Flips.IsRelativelyAmple f D := by
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf
  exact (MMP.Flips.relativelyAmple_basics sX sZ hX hZ f hfs).2.2.2.2.2
    (IsProjectiveMorphism.isProjective hf) D A hDA hA

/-- A positive multiple of a relatively ample divisor is relatively ample. -/
private theorem isRelativelyAmple_smul {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Z} {A : RDivisor X} (hA : MMP.Flips.IsRelativelyAmple f A) {t : ℝ}
    (ht : 0 < t) : MMP.Flips.IsRelativelyAmple f (t • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  refine ⟨m, t • r, L, hm, fun j => mul_pos ht (hr j), hL, ?_⟩
  rw [Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, smul_smul]

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- **Perturbing the boundary keeps a flip.** Let `X ⟶ Z ⟵ X⁺` be a step of an extremal real flip
sequence for `K + B`, with `K + B + λ C ≡_Z 0` and `K⁺ + B⁺ + λ C⁺ ≡_Z 0`. If `0 ≤ t < λ` and
`K₂ + B₂ ≡_Z K + B + t C`, `K₂⁺ + B₂⁺ ≡_Z K⁺ + B⁺ + t C⁺` with `B₂⁺` the strict transform of `B₂`,
then the same diagram is a step for `K₂ + B₂`: numerically `-(K₂ + B₂) ≡ (1 - t/λ)(-(K + B))`
and `K₂⁺ + B₂⁺ ≡ (1 - t/λ)(K⁺ + B⁺)`. -/
private theorem isRealFlipStep_perturb [QuasiCompact sX] [QuasiCompact sX']
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX') {C : RDivisor X} {C' : RDivisor X'}
    {lam t : ℝ} (ht0 : 0 ≤ t) (htl : t < lam)
    (hT  : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (hT' : IsNumericallyTrivialOver ℂ sX' fp (logCanonicalDivisor K' (B' + lam • C')))
    {K₂ : Divisor X} {B₂ : RDivisor X} {K₂' : Divisor X'} {B₂' : RDivisor X'} {N : RDivisor X}
    {N' : RDivisor X'}
    (hN  : IsNumericallyTrivialOver ℂ sX f N)
    (hN' : IsNumericallyTrivialOver ℂ sX' fp N')
    (hE : logCanonicalDivisor K₂ B₂ = logCanonicalDivisor K (B + t • C) + N)
    (hE' : logCanonicalDivisor K₂' B₂' = logCanonicalDivisor K' (B' + t • C') + N')
    (hK₂' : ∃ m : ℕ, K₂'.IsCanonicalDivisor sX' m) (hB₂' : B₂' = flipTransform f fp B₂) :
    IsRealFlipStep sX sZ sX' K₂ B₂ K₂' B₂' f fp := by
  have hEx := h.isNegativeExtremalContraction
  have hX := hEx.isNormalVariety_source
  have hZ := hEx.isNormalVariety_target
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  have hlam : 0 < lam := ht0.trans_lt htl
  obtain ⟨s, rfl⟩ : ∃ s, t = s * lam := ⟨t / lam, (div_mul_cancel₀ _ hlam.ne').symm⟩
  have hs1 : 0 < 1 - s := by
    have : s * lam < 1 * lam := by linarith
    have := lt_of_mul_lt_mul_right this hlam.le
    linarith
  have hTr := isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_smul hT (-s)) hN (-1)
  have hTr' := isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_smul hT' s) hN' 1
  have hnKB : -logCanonicalDivisor K₂ B₂ = (1 - s) • (-logCanonicalDivisor K B) +
      ((-s) • logCanonicalDivisor K (B + lam • C) + (-1 : ℝ) • N) := by
    rw [hE]; simp only [logCanonicalDivisor]; module
  have hKB' : logCanonicalDivisor K₂' B₂' = (1 - s) • logCanonicalDivisor K' B' +
      (s • logCanonicalDivisor K' (B' + lam • C') + (1 : ℝ) • N') := by
    rw [hE']; simp only [logCanonicalDivisor]; module
  exact
    { isQuasiProjectiveVariety_target := h.isQuasiProjectiveVariety_target
      isNegativeExtremalContraction :=
        { isNormalVariety_source := hX
          isNormalVariety_target := hZ
          isCartierCombination := isCartierCombination_of_isQFactorial hQ _
          isContraction := hEx.isContraction
          isRelativelyAntiAmple := by
            change MMP.Flips.IsRelativelyAmple f _
            rw [hnKB]
            exact isRelativelyAmple_of_isNumericallyEquivalentOver hX hZ h.isProjectiveMorphism
              hEx.isContraction.comp_eq
              (isNumericallyEquivalentOver_add (isCartierCombination_of_isQFactorial hQ _) hTr)
              (isRelativelyAmple_smul hEx.isRelativelyAntiAmple hs1)
          relativePicardNumber_eq_one := hEx.relativePicardNumber_eq_one }
      isSmall := h.isSmall
      isBirationalMorphism := h.isBirationalMorphism
      isProjectiveMorphism := h.isProjectiveMorphism
      not_isIso := h.not_isIso
      isCanonicalDivisor_flip := hK₂'
      isSmall_flip := h.isSmall_flip
      isBirationalMorphism_flip := h.isBirationalMorphism_flip
      isProjectiveMorphism_flip := h.isProjectiveMorphism_flip
      not_isIso_flip := h.not_isIso_flip
      relativePicardNumber_flip := h.relativePicardNumber_flip
      isRelativelyAmple_flip := by
        rw [hKB']
        exact isRelativelyAmple_of_isNumericallyEquivalentOver hX' hZ
          h.isProjectiveMorphism_flip h.isSmall_flip.comp_eq
          (isNumericallyEquivalentOver_add (isCartierCombination_of_isQFactorial hQ' _) hTr')
          (isRelativelyAmple_smul h.isRelativelyAmple_flip hs1)
      eq_flipTransform := hB₂' }

end StepAmple

section Sequences

/-- `D ↦ D_i` is additive. -/
private theorem transformSeq_add {R : Type*} [AddCommMonoid R] {X : Scheme.{0}}
    {Y W : ℕ → Scheme.{0}} (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i)
    (D₁ D₂ : DivisorWithCoeffs R X) :
    ∀ i, transformSeq f fp (D₁ + D₂) i = transformSeq f fp D₁ i + transformSeq f fp D₂ i
  | 0 => rfl
  | i + 1 => by
    change flipTransform (f i) (fp i) (transformSeq f fp (D₁ + D₂) i) =
      flipTransform (f i) (fp i) (transformSeq f fp D₁ i) +
        flipTransform (f i) (fp i) (transformSeq f fp D₂ i)
    rw [transformSeq_add f fp D₁ D₂ i, map_add]

/-- `D ↦ D_i` is `ℝ`-linear. -/
private theorem transformSeq_smul {X : Scheme.{0}} {Y W : ℕ → Scheme.{0}}
    (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i) (c : ℝ) (D : RDivisor X) :
    ∀ i, transformSeq f fp (c • D) i = c • transformSeq f fp D i
  | 0 => rfl
  | i + 1 => by
    change flipTransform (f i) (fp i) (transformSeq f fp (c • D) i) =
      c • flipTransform (f i) (fp i) (transformSeq f fp D i)
    rw [transformSeq_smul f fp c D i, flipTransform_smul]

/-- `D ↦ D_i` commutes with `Divisor.toRDivisor`. -/
private theorem transformSeq_toRDivisor {X : Scheme.{0}} {Y W : ℕ → Scheme.{0}}
    (f : ∀ i, modelSeq X Y i ⟶ W i) (fp : ∀ i, Y i ⟶ W i) (D : Divisor X) :
    ∀ i, transformSeq f fp (Divisor.toRDivisor D) i =
      Divisor.toRDivisor (transformSeq f fp D i)
  | 0 => rfl
  | i + 1 => by
    change flipTransform (f i) (fp i) (transformSeq f fp (Divisor.toRDivisor D) i) =
      Divisor.toRDivisor (flipTransform (f i) (fp i) (transformSeq f fp D i))
    rw [transformSeq_toRDivisor f fp D i, flipTransform_toRDivisor]

end Sequences

section Singularities

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **Lowering the boundary keeps exceptional log discrepancies positive** on a `ℚ`-factorial
variety. -/
private theorem logDiscrepancy_pos_of_le (hXq : IsQFactorial sX) {Γ₁ Γ₂ : RDivisor X}
    (hle : ∀ P, Γ₁.coeff P ≤ Γ₂.coeff P)
    (hpos : ∀ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Γ₂ E a → 0 < a) :
    ∀ (m : ℕ) (E : DivisorOver ℂ sX) (b : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX m Γ₁ E b → 0 < b := by
  intro m E b hE hb
  obtain ⟨a, ha, hab⟩ := exists_isLogDiscrepancy_le_of_le hXq hle hb
  exact (hpos m E a hE ha).trans_le hab

/-- **Lowering a dlt boundary** on a `ℚ`-factorial variety keeps it dlt. -/
private theorem isRealDltPair_of_le (hXq : IsQFactorial sX) {Γ₁ Γ₂ : RDivisor X}
    (hΓ : IsRealDltPair sX Γ₂) (h0 : ∀ P, 0 ≤ Γ₁.coeff P) (hle : ∀ P, Γ₁.coeff P ≤ Γ₂.coeff P) :
    IsRealDltPair sX Γ₁ := by
  classical
  obtain ⟨⟨hX, -, ⟨n, K, hK, -⟩, hlc⟩, hΓ1, Z, hsm, hsnc, hpos⟩ := hΓ
  refine ⟨⟨hX, h0, ⟨n, K, hK, ?_⟩, fun n' D b hb => ?_⟩, fun P => (hle P).trans (hΓ1 P), Z, hsm,
    ?_, fun n' D hDZ b hb => ?_⟩
  · exact isRCartier_of_isQFactorial hXq _
  · obtain ⟨a, ha, hab⟩ := exists_isLogDiscrepancy_le_of_le hXq hle hb
    exact (hlc n' D a ha).trans hab
  · refine hsnc.of_support_subset fun E hE => ?_
    rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen] at hE ⊢
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro hz
    apply hE
    change Γ₁.coeff _ = 0
    change Γ₂.coeff _ = 0 at hz
    exact le_antisymm (hz ▸ hle _) (h0 _)
  · obtain ⟨a, ha, hab⟩ := exists_isLogDiscrepancy_le_of_le hXq hle hb
    exact (hpos n' D hDZ a ha).trans_le hab

end Singularities

section Curves

open MMP.Flips

/-- A morphism that is not an isomorphism is not an isomorphism over its biregular locus
everywhere. -/
private theorem exists_notMem_biregularLocus {X W : Scheme.{0}} (f : X ⟶ W) (h : ¬ IsIso f) :
    ∃ w, w ∉ biregularLocus f := by
  by_contra hc
  push Not at hc
  have htop : biregularLocus f = ⊤ := eq_top_iff.mpr fun w _ => hc w
  have hiso : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  apply h
  have i1 : ∀ {T : Scheme.{0}} (U : T.Opens), U = ⊤ → IsIso U.ι := by
    rintro T U rfl
    exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have key : ∀ U : W.Opens, U = ⊤ → IsIso (f ∣_ U) → IsIso f := by
    rintro U rfl hU
    have : IsIso (f ⁻¹ᵁ (⊤ : W.Opens)).ι := i1 _ (by simp)
    have : IsIso (⊤ : W.Opens).ι := i1 _ rfl
    have h2 : f = inv ((f ⁻¹ᵁ (⊤ : W.Opens)).ι) ≫ (f ∣_ ⊤) ≫ (⊤ : W.Opens).ι := by
      rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [h2]
    infer_instance
  exact key _ htop hiso

variable {X W Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- A divisor whose negative is `f`-ample is not nef over any base through `f` when `f` contracts
a curve. -/
private theorem not_isRelativelyNef_of_isRelativelyAmple_neg {f : X ⟶ W} (g : W ⟶ Z)
    {D : RDivisor X} (hA : IsRelativelyAmple f (-D)) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : ¬ IsRelativelyNef ℂ sX (f ≫ g) D := by
  intro hN
  obtain ⟨m, r, L, hm, hr, hL, hAeq⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  have hCg : C.IsContractedBy (f ≫ g) := fun z hz => by
    simp only [Scheme.Hom.comp_apply, hC z hz]
  obtain ⟨m', r', L', hL', hDeq, hnn⟩ := hN
  have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r' L' hL'
  rw [← hDeq] at e₁
  have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hLc
  rw [← hAeq] at e₂
  have hpos : 0 < ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ) := by
    refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) C hC
  have h0 := hnn C hCg _ e₁
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D (-D) r' L' r L _ _ 1 1 e₁ e₂
  simp only [one_smul, one_mul, add_neg_cancel] at hsum
  have hz := (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hsum
    (isRIntersectionNumber_zero C)
  linarith

end Curves

section StepNef

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- A real number `t ∈ [0, λ]` is `s λ` for some `s ∈ [0, 1]`. -/
private theorem exists_eq_mul_of_le {t lam : ℝ} (ht0 : 0 ≤ t) (htl : t ≤ lam) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ t = s * lam := by
  rcases (ht0.trans htl).lt_or_eq with hl | hl
  · exact ⟨t / lam, div_nonneg ht0 hl.le, (div_le_one hl).mpr htl, (div_mul_cancel₀ _ hl.ne').symm⟩
  · exact ⟨0, le_rfl, zero_le_one, by rw [zero_mul]; linarith⟩

/-- **The source side of a scaled step is nef.** If `-(K + B)` is `f`-ample and
`K + B + λ C ≡_f 0`, then `-(K + B + t C + N)` is `f`-nef for `0 ≤ t ≤ λ` and `N ≡_f 0`. -/
private theorem isRelativelyNef_neg_logCanonicalDivisor_add {f : X ⟶ Y} {K : Divisor X}
    {B C N : RDivisor X} {lam t : ℝ}
    (hA : IsRelativelyAmple f (-logCanonicalDivisor K B))
    (hT : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (hN : IsNumericallyTrivialOver ℂ sX f N) (ht0 : 0 ≤ t) (htl : t ≤ lam) :
    IsRelativelyNef ℂ sX f (-logCanonicalDivisor K (B + t • C + N)) := by
  obtain ⟨s, -, hs1, rfl⟩ := exists_eq_mul_of_le ht0 htl
  have h := isRelativelyNef_combo (isRelativelyNef_of_isRelativelyAmple (sX := sX) hA)
    (isNumericallyTrivialOver_smul hT (-1)) (isNumericallyTrivialOver_smul hN (-1)) hs1
  convert h using 1
  simp only [logCanonicalDivisor]
  module

/-- **The flipped side of a scaled step is nef.** If `K⁺ + B⁺` is `f⁺`-ample and
`K⁺ + B⁺ + λ C⁺ ≡_{f⁺} 0`, then `K⁺ + B⁺ + t C⁺ + N⁺` is `f⁺`-nef for `0 ≤ t ≤ λ` and
`N⁺ ≡_{f⁺} 0`. -/
private theorem isRelativelyNef_logCanonicalDivisor_add {f : X ⟶ Y} {K : Divisor X}
    {B C N : RDivisor X} {lam t : ℝ}
    (hA : IsRelativelyAmple f (logCanonicalDivisor K B))
    (hT : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (hN : IsNumericallyTrivialOver ℂ sX f N) (ht0 : 0 ≤ t) (htl : t ≤ lam) :
    IsRelativelyNef ℂ sX f (logCanonicalDivisor K (B + t • C + N)) := by
  obtain ⟨s, -, hs1, rfl⟩ := exists_eq_mul_of_le ht0 htl
  have h := isRelativelyNef_combo (isRelativelyNef_of_isRelativelyAmple (sX := sX) hA) hT hN hs1
  convert h using 1
  simp only [logCanonicalDivisor]
  module

end StepNef

section Descent

open MMP.Flips

variable {X X' W Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}

/-- The strict transform of `K + Γ` is `(f⁺)⁻¹_* f_* K + Γ⁺`. -/
private theorem flipTransform_logCanonicalDivisor (f : X ⟶ W) (fp : X' ⟶ W) (K : Divisor X)
    (Γ : RDivisor X) :
    flipTransform f fp (logCanonicalDivisor K Γ) =
      logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp Γ) := by
  rw [logCanonicalDivisor, logCanonicalDivisor, map_add, flipTransform_toRDivisor]

/-- **Crepant descent across a step.** Let `f : X ⟶ W ⟵ X' : f⁺` be a step of a program with `f⁺`
an isomorphism over codimension one, and let `D` be an `ℝ`-Cartier divisor on `W` with
`f^* D = K + Γ` and `(f⁺)^* D = (f⁺)⁻¹_* f_* (K + Γ)`. Then for every canonical divisor `K'` of
`X'`, `K' + Γ'` is numerically trivial over `W` and differs from `(f⁺)^* D` by a principal
divisor. -/
private theorem exists_principal_logCanonicalDivisor_flipTransform
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hW : IsNormalVariety ℂ sW)
    {f : X ⟶ W} {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX)
    (hfps : fp ≫ sW = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    {n n' : ℕ} {K : Divisor X} {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX n)
    (hK' : K'.IsCanonicalDivisor sX' n') (Γ : RDivisor X) :
    ∃ φ : (RationalFunctions X')ˣ, logCanonicalDivisor K' (flipTransform f fp Γ) =
      flipTransform f fp (logCanonicalDivisor K Γ) +
        (1 : ℝ) • Divisor.toRDivisor (MMP.Mori.principalDivisor φ) := by
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have hKf := isCanonicalDivisor_flipTransform hX hX' hW hfs hfps hfb hfpb hfp1 hK
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX' hK' hKf
  refine ⟨φ, ?_⟩
  rw [flipTransform_logCanonicalDivisor, logCanonicalDivisor, logCanonicalDivisor, ← hφ, map_sub]
  module

/-- **Nefness crosses a crepant step.** In the setting of
`exists_principal_logCanonicalDivisor_flipTransform`, if `K + Γ` is nef over `Z` (through
`f ≫ g = π`), then so is `K' + Γ'` (through `f⁺ ≫ g = π'`). -/
private theorem isRelativelyNef_logCanonicalDivisor_flipTransform
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hW : IsNormalVariety ℂ sW)
    {f : X ⟶ W} {fp : X' ⟶ W} [IsProper f] [IsProper fp] (hfs : f ≫ sW = sX)
    (hfps : fp ≫ sW = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hfp1 : ∀ y : X', Order.coheight y ≤ 1 → fp y ∈ biregularLocus fp)
    {n n' : ℕ} {K : Divisor X} {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX n)
    (hK' : K'.IsCanonicalDivisor sX' n') {Γ : RDivisor X} {D : RDivisor W} (g : W ⟶ Z)
    {π : X ⟶ Z} {π' : X' ⟶ Z} (hfg : f ≫ g = π) (hfpg : fp ≫ g = π')
    (hD : IsRCartierPullback f D (logCanonicalDivisor K Γ))
    (hD' : IsRCartierPullback fp D (flipTransform f fp (logCanonicalDivisor K Γ)))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K Γ)) :
    IsRelativelyNef ℂ sX' π' (logCanonicalDivisor K' (flipTransform f fp Γ)) := by
  subst hfps
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hW.1.toQuasiCompact
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : LocallyOfFiniteType (fp ≫ sW) := hX'.1.toLocallyOfFiniteType
  haveI : QuasiCompact (fp ≫ sW) := hX'.1.toQuasiCompact
  haveI : Surjective f := ⟨surjective_of_isProper_of_isBirationalMorphism f hfb⟩
  have hDn : IsRelativelyNef ℂ sW g D :=
    MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective f hfs g hD (hfg ▸ hnef)
  have h1 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) g π' fp
    (by rw [Category.comp_id, hfpg]) hDn hD'
  obtain ⟨φ, hφ⟩ := exists_principal_logCanonicalDivisor_flipTransform hX hX' hW hfs rfl hfb
    hfpb hfp1 hK hK' Γ
  rw [hφ]
  exact isRelativelyNef_add_smul h1 (isNumericallyTrivialOver_principalDivisor π' φ) 1

end Descent

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : X ⟶ Z} (hπ : π ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (MMP.Flips.logCanonicalDivisor K (B + C)))
    {A : QDivisor X} (hA0 : ∀ P, 0 ≤ A.coeff P) (hA : A.IsAmple)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the scaling program
    {n : ℕ∞} {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {πY : ∀ i, Y i ⟶ Z} {KY : ∀ i, Divisor (Y i)} {BY CY : ∀ i, RDivisor (Y i)}
    {W : ℕ → Scheme.{0}} [∀ i, IsLocallyNoetherian (W i)] [∀ i, IsNormal (W i)]
    {sW : ∀ i, W i ⟶ Spec (.of ℂ)} {f : ∀ i, modelSeq X Y i ⟶ W i}
    {fp : ∀ i, Y i ⟶ W i} {g : ∀ i, W i ⟶ Z} {lam : ℕ → ℝ}
    (hπY : ∀ i, πY i ≫ sZ = sY i)
    (hfg : ∀ i : ℕ, (i : ℕ∞) < n → f i ≫ g i = modelMap π πY i)
    (hfpg : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ g i = πY i)
    (hYq : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (modelStr sX sY i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
          (KY i) (BY i) (f i) (fp i) ∨
        (AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (sW i) ∧
          MMP.Flips.IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
            (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
          IsBirationalMorphism (f i) ∧ IsProjectiveMorphism (f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
            MMP.Flips.exceptionalSet (f i) = E.support) ∧
          IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sY i) m) ∧
          BY i = flipTransform (f i) (fp i) (divisorSeq B BY i)))
    (hCY : ∀ i : ℕ, (i : ℕ∞) < n → CY i = flipTransform (f i) (fp i) (divisorSeq C CY i))
    (hthr : ∀ i : ℕ, (i : ℕ∞) < n →
      IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B BY i + t • divisorSeq C CY i))} (lam i))
    (hdesc : ∀ i : ℕ, (i : ℕ∞) < n → ∃ D : RDivisor (W i),
      MMP.Flips.IsRCartierPullback (f i) D
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        MMP.Flips.IsRCartierPullback (fp i) D
          (flipTransform (f i) (fp i) (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)))) :
    (∀ᶠ i : ℕ in atTop, ∀ _ : (i : ℕ∞) < n, MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
      Disjoint (MMP.Flips.exceptionalSet (f i))
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i)) ∧
        Disjoint (MMP.Flips.exceptionalSet (fp i))
          ((DivisorWithCoeffs.roundDown (BY i)).supp : Set (Y i))) ∧
      ((∀ i : ℕ, (i : ℕ∞) < n → MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
        (MMP.Flips.exceptionalSet (f i) ∩
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i))).Nonempty)
        → n ≠ ⊤) := by
  -- every step contracts its model, and both sides of it lie over `sW i`
  have hcon : ∀ i : ℕ, (i : ℕ∞) < n →
      MMP.Flips.IsContraction ℂ (sW i) (modelStr sX sY i) (f i) := fun i hi =>
    (hstep i hi).elim (fun hfl => hfl.isNegativeExtremalContraction.isContraction)
      (fun hdv => hdv.2.1.isContraction)
  have hfpW : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ sW i = sY i := fun i hi => by
    have hsW : g i ≫ sZ = sW i := eq_of_isContraction_comp_eq (hcon i hi) (by
      rw [← Category.assoc, hfg i hi, modelMap_comp_eq hπ hπY, (hcon i hi).comp_eq])
    rw [← hsW, ← Category.assoc, hfpg i hi, hπY]
  have hprojT : n = ⊤ → ∀ i, MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) := by
    intro hn i
    have hlt : ∀ i : ℕ, (i : ℕ∞) < n := fun i => by rw [hn]; exact WithTop.coe_lt_top _
    induction i with
    | zero => exact hX
    | succ i ih =>
      have hc := hcon i (hlt i)
      have hfp := hfpW i (hlt i)
      change MMP.Mori.IsProjectiveVariety ℂ (sY i)
      rcases hstep i (hlt i) with hfl | hdv
      · have := isProper_of_isProjectiveMorphism (fp i) hfl.isProjectiveMorphism_flip
        exact isProjectiveVariety_of_isContraction (fp := fp i) ih hc hfl.isQuasiProjectiveVariety_target hfp
          (IsProjectiveMorphism.isQuasiProjective hfl.isProjectiveMorphism_flip)
      · have := hdv.2.2.2.2.2.1
        exact isProjectiveVariety_of_isContraction (fp := fp i) ih hc hdv.1 hfp
          (isQuasiProjective_of_isImmersion (fp i))
  -- the canonical divisors of the models
  have hcan : n = ⊤ → ∀ i, ∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i) := by
    intro hn i
    cases i with
    | zero => exact ⟨4, hK⟩
    | succ i =>
      rcases hstep i (by rw [hn]; exact WithTop.coe_lt_top _) with hfl | hdv
      · exact hfl.isCanonicalDivisor_flip
      · exact hdv.2.2.2.2.2.2.1
  -- Step 1: an infinite program is eventually a sequence of flips (finitely many divisorial
  -- steps, since each drops the Picard number of a projective model).
  have hflipEv : n = ⊤ → ∃ N : ℕ, ∀ i, N ≤ i →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
        (KY i) (BY i) (f i) (fp i) := by
    intro hn
    have hlt : ∀ i : ℕ, (i : ℕ∞) < n := fun i => by rw [hn]; exact WithTop.coe_lt_top _
    -- every model of the program is projective
    have hproj := hprojT hn
    have hfin : ∀ i, picardNumber (modelStr sX sY i) < ⊤ := fun i => by
      have := hproj i
      exact picardNumber_lt_top_of_isProjectiveVariety _
    -- flips keep the Picard number, divisorial contractions lower it
    have hρflip : ∀ i, IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
        (divisorSeq B BY i) (KY i) (BY i) (f i) (fp i) →
        picardNumber (sY i) = picardNumber (modelStr sX sY i) := fun i hfl =>
      picardNumber_eq_of_isSmall (hproj i) (hYq i (by rw [hn]; exact le_top)) (hproj (i + 1))
        (hYq (i + 1) (by rw [hn]; exact le_top)) hfl.isSmall hfl.isSmall_flip
    have hρdiv : ∀ i, ¬ IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
        (divisorSeq B BY i) (KY i) (BY i) (f i) (fp i) →
        picardNumber (sY i) < picardNumber (modelStr sX sY i) := by
      intro i hnf
      rcases hstep i (hlt i) with hfl | ⟨-, hneg, hbir, -, ⟨E, hE⟩, hiso, -, -⟩
      · exact absurd hfl hnf
      · have hEx : (MMP.Flips.exceptionalSet (f i)).Nonempty := by
          rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact ⟨_, subset_closure rfl⟩
        exact picardNumber_lt_of_isNegativeExtremalContraction (hproj i) (hproj (i + 1)) hneg
          hbir hEx (hfpW i (hlt i))
    have hρle : ∀ i, picardNumber (sY i) ≤ picardNumber (modelStr sX sY i) := fun i => by
      by_cases h : IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
        (divisorSeq B BY i) (KY i) (BY i) (f i) (fp i)
      · exact (hρflip i h).le
      · exact (hρdiv i h).le
    have hρlt := hρdiv
    obtain ⟨N, hN⟩ := exists_forall_ge_not_of_succ_le
      (ρ := fun i => (picardNumber (modelStr sX sY i)).toNat)
      (P := fun i => ¬ IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i)
        (divisorSeq B BY i) (KY i) (BY i) (f i) (fp i))
      (fun i => (ENat.toNat_le_toNat (hρle i) (hfin i).ne))
      (fun i hi => by
        have h : picardNumber (modelStr sX sY (i + 1)) < picardNumber (modelStr sX sY i) :=
          hρlt i hi
        rw [← ENat.coe_toNat (hfin (i + 1)).ne, ← ENat.coe_toNat (hfin i).ne] at h
        exact_mod_cast h)
    exact ⟨N, fun i hi => not_not.mp (hN i hi)⟩
  -- Step 2: special termination proper, for an infinite program.
  have hcore : n = ⊤ → ∃ N : ℕ, ∀ i, N ≤ i →
      MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
      Disjoint (MMP.Flips.exceptionalSet (f i))
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i)) ∧
        Disjoint (MMP.Flips.exceptionalSet (fp i))
          ((DivisorWithCoeffs.roundDown (BY i)).supp : Set (Y i)) := by
    intro hn
    -- special termination, component by component of the reduced boundary
    have hcomp : ∃ N : ℕ, ∀ i, N ≤ i →
        (∀ P : MMP.Mori.PrimeDivisor (modelSeq X Y i),
          (DivisorWithCoeffs.roundDown (divisorSeq B BY i)).coeff P ≠ 0 →
          Disjoint (MMP.Flips.exceptionalSet (f i)) (P.support : Set (modelSeq X Y i))) ∧
        (∀ P : MMP.Mori.PrimeDivisor (Y i), (DivisorWithCoeffs.roundDown (BY i)).coeff P ≠ 0 →
          Disjoint (MMP.Flips.exceptionalSet (fp i)) (P.support : Set (Y i))) := by
      obtain ⟨N₀, hN₀⟩ := hflipEv hn
      -- the tail starts at `N₁`: either every later level is one, or the level at `N₁` is `< 1`
      obtain ⟨N₁, hN₀₁, hcase⟩ : ∃ N₁, N₀ ≤ N₁ ∧ ((∀ i, N₁ ≤ i → 1 ≤ lam i) ∨ lam N₁ < 1) := by
        by_cases h : ∃ j, N₀ ≤ j ∧ lam j < 1
        · obtain ⟨j, hj, hlt⟩ := h
          exact ⟨j, hj, Or.inr hlt⟩
        · push Not at h
          exact ⟨N₀, le_rfl, Or.inl h⟩
      -- every floor component of a late model is the transform of one of `X_{N₁}`
      have hlift : ∀ (k : ℕ) (P : MMP.Mori.PrimeDivisor (modelSeq X Y (N₁ + k))),
          (DivisorWithCoeffs.roundDown (divisorSeq B BY (N₁ + k))).coeff P ≠ 0 →
          ∃ S : MMP.Mori.PrimeDivisor (modelSeq X Y N₁),
            (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).coeff S ≠ 0 ∧
            primeSeq f fp N₁ S k = some P := by
        intro k
        induction k with
        | zero => exact fun P hP => ⟨P, hP, rfl⟩
        | succ k ih =>
          change ∀ P : MMP.Mori.PrimeDivisor (Y (N₁ + k)),
            (DivisorWithCoeffs.roundDown (BY (N₁ + k))).coeff P ≠ 0 →
            ∃ S : MMP.Mori.PrimeDivisor (modelSeq X Y N₁),
              (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).coeff S ≠ 0 ∧
              (primeSeq f fp N₁ S k).bind
                (flipTransformPrimeDivisor (f (N₁ + k)) (fp (N₁ + k))) = some P
          intro P hP
          have hfl := hN₀ (N₁ + k) (by omega)
          obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_eq_of_isSmall hfl.isSmall_flip hfl.isSmall P
          obtain ⟨hQP, hcoef⟩ := flipTransformPrimeDivisor_eq_some_of_isSmall
            hfl.isNegativeExtremalContraction.isNormalVariety_target hfl.isSmall
            hfl.isSmall_flip hQ.symm
          have hQf : (DivisorWithCoeffs.roundDown (divisorSeq B BY (N₁ + k))).coeff Q ≠ 0 := by
            have hP' := hP
            rw [hfl.eq_flipTransform, DivisorWithCoeffs.coeff_roundDown,
              DivisorWithCoeffs.coeff_apply, hcoef] at hP'
            rwa [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_apply]
          obtain ⟨S, hS, hSk⟩ := ih Q hQf
          refine ⟨S, hS, ?_⟩
          rw [hSk, Option.bind_some]
          exact hQP
      -- special termination for a single floor component of `X_{N₁}`
      have hcoreS : ∀ S : MMP.Mori.PrimeDivisor (modelSeq X Y N₁),
          (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).coeff S ≠ 0 →
          ∃ M : ℕ, ∀ k, M ≤ k →
            (∀ P, primeSeq f fp N₁ S k = some P →
              Disjoint (MMP.Mori.exceptionalSet (f (N₁ + k)) : Set (modelSeq X Y (N₁ + k)))
                (P.support : Set (modelSeq X Y (N₁ + k)))) ∧
            (∀ P, primeSeq f fp N₁ S (k + 1) = some P →
              Disjoint (MMP.Mori.exceptionalSet (fp (N₁ + k)) : Set (Y (N₁ + k)))
                (P.support : Set (Y (N₁ + k)))) := by
        intro S hS
        have hfl : ∀ k, IsRealFlipStep (modelStr sX sY (N₁ + k)) (sW (N₁ + k)) (sY (N₁ + k))
            (divisorSeq K KY (N₁ + k)) (divisorSeq B BY (N₁ + k)) (KY (N₁ + k)) (BY (N₁ + k))
            (f (N₁ + k)) (fp (N₁ + k)) := fun k => hN₀ _ (by omega)
        -- the transforms of `S` along the tail are prime divisors
        have hsome : ∀ k, (primeSeq f fp N₁ S k).isSome := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
            obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp ih
            obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_eq_of_isSmall (hfl k).isSmall
              (hfl k).isSmall_flip P
            have h := (flipTransformPrimeDivisor_eq_some_of_isSmall
              (hfl k).isNegativeExtremalContraction.isNormalVariety_target (hfl k).isSmall
              (hfl k).isSmall_flip hQ).1
            change ((primeSeq f fp N₁ S k).bind _).isSome
            rw [hP, Option.bind_some]
            exact Option.isSome_iff_exists.mpr ⟨Q, h⟩
        let S' : ∀ k, MMP.Mori.PrimeDivisor (modelSeq X Y (N₁ + k)) := fun k =>
          (primeSeq f fp N₁ S k).get (hsome k)
        have hS'eq : ∀ k, primeSeq f fp N₁ S k = some (S' k) := fun k => (Option.some_get _).symm
        have hS'step : ∀ k, flipTransformPrimeDivisor (f (N₁ + k)) (fp (N₁ + k)) (S' k) =
            some (S' (k + 1)) := by
          intro k
          have h := hS'eq (k + 1)
          change (primeSeq f fp N₁ S k).bind _ = _ at h
          rwa [hS'eq k, Option.bind_some] at h
        have hlt : ∀ i : ℕ, (i : ℕ∞) < n := fun i => by rw [hn]; exact WithTop.coe_lt_top _
        have hdim : ∀ i, topologicalKrullDim (modelSeq X Y i) = 4 := by
          intro i
          induction i with
          | zero => exact_mod_cast hK.topologicalKrullDim_eq
          | succ i ih =>
            change topologicalKrullDim (Y i) = 4
            have hWi : topologicalKrullDim (W i) = 4 := by
              obtain ⟨hneg, hb⟩ : MMP.Flips.IsNegativeExtremalContraction ℂ (modelStr sX sY i)
                  (sW i) (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i))
                  (f i) ∧ IsBirationalMorphism (f i) := by
                rcases hstep i (hlt i) with hfl | hdv
                · exact ⟨hfl.isNegativeExtremalContraction, hfl.isBirationalMorphism⟩
                · exact ⟨hdv.2.1, hdv.2.2.1⟩
              have : MMP.Mori.IsVariety ℂ (modelStr sX sY i) := hneg.isNormalVariety_source.1
              have : MMP.Mori.IsVariety ℂ (sW i) := hneg.isNormalVariety_target.1
              rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sW i)
                (modelStr sX sY i) hb, ih]
            rcases hstep i (hlt i) with hfl | hdv
            · have : MMP.Mori.IsVariety ℂ (sW i) :=
                hfl.isNegativeExtremalContraction.isNormalVariety_target.1
              have : MMP.Mori.IsVariety ℂ (sY i) := hfl.isSmall_flip.isVariety_source
              rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sW i) (sY i)
                hfl.isBirationalMorphism_flip, hWi]
            · have := hdv.2.2.2.2.2.1
              rw [(Scheme.homeoOfIso (asIso (fp i))).isHomeomorph.topologicalKrullDim_eq, hWi]
        have hCnn : ∀ i, 0 ≤ divisorSeq C CY i := by
          intro i
          induction i with
          | zero => exact fun P => hC P
          | succ i ih =>
            change 0 ≤ CY i
            rw [hCY i (hlt i)]
            exact DivisorWithCoeffs.mapPrimeDivisors_nonneg _
              (DivisorWithCoeffs.mapPrimeDivisors_nonneg _ ih)
        -- the plt perturbation of the program along the tail, with the source as reference
        obtain ⟨ε, Kc, Bs, S₀, hS₀, A₀, ψ, ψinv, hKc, hflipB, hpltB, hlamB, hantiB, hnefB, hupperB,
            hcrepB, hSB, hSC, hA₀, hA₀amp, hA₀S, hψ, hψk, hψinvk, hψS, hord, hAB⟩ :
            ∃ (ε : ℝ) (Kc : ∀ k, Divisor (modelSeq X Y (N₁ + k)))
              (Bs : ∀ k, RDivisor (modelSeq X Y (N₁ + k)))
              (S₀ : MMP.Mori.PrimeDivisor X) (_ : IsNormal S₀.idealSheaf.subscheme)
              (A₀ : QDivisor X) (ψ : ∀ k, X.RationalMap (modelSeq X Y (N₁ + k)))
              (ψinv : ∀ k, (modelSeq X Y (N₁ + k)).RationalMap X),
              (∀ k, ∃ m : ℕ, (Kc k).IsCanonicalDivisor (modelStr sX sY (N₁ + k)) m) ∧
              (∀ k, IsRealFlipStep (modelStr sX sY (N₁ + k)) (sW (N₁ + k))
                (modelStr sX sY (N₁ + (k + 1))) (Kc k) (Bs k)
                (Kc (k + 1)) (Bs (k + 1)) (f (N₁ + k)) (fp (N₁ + k))) ∧
              (∀ k, (∀ P, 0 ≤ (Bs k).coeff P ∧ (Bs k).coeff P ≤ 1) ∧
                RDivisor.IsRCartier (Divisor.toRDivisor (Kc k) + Bs k) ∧
                ∀ (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY (N₁ + k))) (a : ℝ), E.IsExceptional →
                  MMP.Intersection.IsLogDiscrepancy (modelStr sX sY (N₁ + k)) m (Bs k) E a →
                    0 < a) ∧
              (∀ k, 0 < lam (N₁ + k) - ε) ∧ Antitone (fun k => lam (N₁ + k) - ε) ∧
              (∀ k, MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY (N₁ + k)) (modelMap π πY (N₁ + k))
                (MMP.Flips.logCanonicalDivisor (Kc k)
                  (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)))) ∧
              (∀ k, (∀ P, 0 ≤ (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)).coeff P ∧
                  (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)).coeff P ≤ 1) ∧
                RDivisor.IsRCartier (Divisor.toRDivisor (Kc k) +
                  (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k))) ∧
                ∀ (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY (N₁ + k))) (a : ℝ), E.IsExceptional →
                  MMP.Intersection.IsLogDiscrepancy (modelStr sX sY (N₁ + k)) m
                    (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)) E a → 0 < a) ∧
              (∀ k, ∃ D : RDivisor (W (N₁ + k)),
                MMP.Flips.IsRCartierPullback (f (N₁ + k)) D
                  (MMP.Flips.logCanonicalDivisor (Kc k)
                    (Bs k + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k))) ∧
                MMP.Flips.IsRCartierPullback (fp (N₁ + k)) D
                  (MMP.Flips.logCanonicalDivisor (Kc (k + 1))
                    (Bs (k + 1) + (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + (k + 1))))) ∧
              (∀ k, (Bs k).coeff (S' k) = 1) ∧
              (∀ k, (divisorSeq C CY (N₁ + k)).coeff (S' k) = 0) ∧
              0 ≤ A₀ ∧ A₀.IsAmple ∧ A₀.coeff S₀ = 0 ∧
              (∀ k, MMP.Mori.RationalMap.IsInverse (ψ k) (ψinv k)) ∧
              (∀ k, MMP.Flips.RationalMap.IsOver sX (modelStr sX sY (N₁ + k)) (ψ k)) ∧
              (∀ k, MMP.Flips.RationalMap.IsOver (modelStr sX sY (N₁ + k)) sX (ψinv k)) ∧
              (∀ k, MMP.Mori.RationalMap.transformPrimeDivisor (ψ k) S₀ = some (S' k)) ∧
              (∀ k, ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y (N₁ + k)),
                MMP.Flips.RationalMap.IsInverseExceptional (ψ k) F →
                ∀ q : (modelSeq X Y (N₁ + k)).PartialMap X, q.toRationalMap = ψinv k →
                  ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X)) ∧
              (∀ k, QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor (ψ k) A₀) ≤
                Bs k - Finsupp.single (S' k) 1) := by
          -- the divisors of the program are the strict transforms of those of the source
          have hBseq : ∀ i, divisorSeq B BY i = transformSeq f fp B i := by
            intro i
            induction i with
            | zero => rfl
            | succ i ih =>
              change BY i = flipTransform (f i) (fp i) (transformSeq f fp B i)
              rw [← ih]
              rcases hstep i (hlt i) with hfl | hdv
              · exact hfl.eq_flipTransform
              · exact hdv.2.2.2.2.2.2.2
          have hCseq : ∀ i, divisorSeq C CY i = transformSeq f fp C i := by
            intro i
            induction i with
            | zero => rfl
            | succ i ih =>
              change CY i = flipTransform (f i) (fp i) (transformSeq f fp C i)
              rw [← ih]
              exact hCY i (hlt i)
          -- the data of each step
          have hdata : ∀ i, IsProper (f i) ∧ IsBirationalMorphism (f i) ∧ IsProper (fp i) ∧
              IsBirationalMorphism (fp i) ∧ IsNormalVariety ℂ (sW i) ∧
              (∀ y : Y i, Order.coheight y ≤ 1 → fp i y ∈ biregularLocus (fp i)) ∧
              f i ≫ sW i = modelStr sX sY i ∧ fp i ≫ sW i = sY i := by
            intro i
            have hc := hcon i (hlt i)
            have hfpW := hfpW i (hlt i)
            rcases hstep i (hlt i) with hfl | hdv
            · refine ⟨hfl.isSmall.isProper, hfl.isBirationalMorphism, hfl.isSmall_flip.isProper,
                hfl.isBirationalMorphism_flip,
                hfl.isNegativeExtremalContraction.isNormalVariety_target, fun y hy => ?_,
                hc.comp_eq, hfpW⟩
              by_contra h
              exact absurd ((two_le_coheight_of_mem_exceptionalSet_of_isSmall hfl.isSmall_flip
                (x := y) (show y ∉ ((fp i) ⁻¹ᵁ biregularLocus (fp i) : Set (Y i)) from h)).trans
                hy) (by decide)
            · have := hdv.2.2.2.2.2.1
              exact ⟨hc.isProper, hdv.2.2.1, inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _,
                hdv.2.1.isNormalVariety_target, fun y _ =>
                  le_biregularLocus (f := fp i) (V := ⊤) (show IsIso (fp i ∣_ ⊤) by infer_instance)
                    (show fp i y ∈ (⊤ : (W i).Opens) from trivial), hc.comp_eq, hfpW⟩
          choose hfP hfB hfpP hfpB hWn hfp1 hfW hfpW using hdata
          -- the partial isomorphisms from the source to the models
          obtain ⟨e, heOver, heCoeff, heSurj, heChain, heStep⟩ :
              ∃ e : ∀ i, X.PartialIso (modelSeq X Y i),
                (∀ i, (e i).IsOver sX (modelStr sX sY i)) ∧
                (∀ i (P : MMP.Mori.PrimeDivisor X) (F : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
                  MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap P = some F →
                  ∀ D : RDivisor X, transformSeq f fp D i F = D P) ∧
                (∀ i (F : MMP.Mori.PrimeDivisor (modelSeq X Y i)), ∃ P,
                  MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap P = some F) ∧
                (∀ k (P : MMP.Mori.PrimeDivisor X)
                  (F : MMP.Mori.PrimeDivisor (modelSeq X Y (N₁ + k))),
                  MMP.Mori.RationalMap.transformPrimeDivisor (e N₁).toRationalMap P = some S →
                  primeSeq f fp N₁ S k = some F →
                  MMP.Mori.RationalMap.transformPrimeDivisor (e (N₁ + k)).toRationalMap P =
                    some F) ∧
                (∀ i (P : MMP.Mori.PrimeDivisor X)
                  (F : MMP.Mori.PrimeDivisor (modelSeq X Y (i + 1))),
                  MMP.Mori.RationalMap.transformPrimeDivisor (e (i + 1)).toRationalMap P = some F →
                  ∃ F₀ : MMP.Mori.PrimeDivisor (modelSeq X Y i),
                    MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap P = some F₀ ∧
                    fp i F.genericPoint = f i F₀.genericPoint) := by
            classical
            have hsteps : ∀ i, ∃ s : (modelSeq X Y i).PartialIso (modelSeq X Y (i + 1)),
                s.IsOver (f i) (fp i) ∧
                (∀ y : modelSeq X Y (i + 1), Order.coheight y ≤ 1 → y ∈ s.target) ∧
                (N₀ ≤ i → ∀ x : modelSeq X Y i, Order.coheight x ≤ 1 → x ∈ s.source) := by
              intro i
              haveI := hfP i
              haveI := hfpP i
              haveI : IsIntegral (W i) := (hWn i).1.toIsIntegral
              obtain ⟨s, h1, h2, h3⟩ := exists_stepPartialIso (f i) (fp i) (hfB i) (hfpB i) (hfp1 i)
              refine ⟨s, h1, h2, fun hi => h3 fun x hx => ?_⟩
              by_contra h
              exact absurd ((two_le_coheight_of_mem_exceptionalSet_of_isSmall (hN₀ i hi).isSmall
                (x := x) (show x ∉ ((f i) ⁻¹ᵁ biregularLocus (f i) : Set (modelSeq X Y i)) from h)).trans
                hx) (by decide)
            choose step hsOver hsTarget hsSource using hsteps
            have hnv : ∀ i, IsNormalVariety ℂ (modelStr sX sY i) := fun i =>
              ⟨(hprojT hn i).toIsVariety, inferInstance⟩
            have hsep : ∀ i, IsSeparated (modelSeq X Y i ↘ ⊤_ Scheme) := fun i =>
              MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety (hnv i)
            haveI : IsSeparated (X ↘ ⊤_ Scheme) := hsep 0
            -- the composite is over `ℂ`
            have hIover : ∀ i, (compositePartialIso step i).IsOver sX (modelStr sX sY i) := by
              intro i
              induction i with
              | zero =>
                show 𝟙 _ ≫ (Scheme.PartialIso.refl X).target.ι ≫ sX =
                  (Scheme.PartialIso.refl X).source.ι ≫ sX
                rw [Category.id_comp]
                rfl
              | succ i ih =>
                refine Scheme.PartialIso.IsOver.trans ih ?_
                have h := congrArg (· ≫ sW i) (hsOver i)
                simp only [Category.assoc] at h
                change (step i).iso.hom ≫ (step i).target.ι ≫ sY i =
                  (step i).source.ι ≫ modelStr sX sY i
                rw [← hfpW i, ← hfW i]
                exact h
            -- its target contains every point of coheight at most one
            have hItarget : ∀ i (y : modelSeq X Y i), Order.coheight y ≤ 1 →
                y ∈ (compositePartialIso step i).target := by
              intro i
              induction i with
              | zero => exact fun y _ => Set.mem_univ y
              | succ i ih =>
                intro y hy
                have hy' := hsTarget i y hy
                show y ∈ ((compositePartialIso step i).trans (step i)).target
                refine mem_trans_target _ _ hy' (ih _ ?_)
                rw [coheight_toPartialMap_hom (step i).symm hy']
                exact hy
            -- generic points of prime divisors correspond, with the coefficients of transforms
            have hIcoeff : ∀ i (P : MMP.Mori.PrimeDivisor X)
                (F : MMP.Mori.PrimeDivisor (modelSeq X Y i))
                (hP : P.genericPoint ∈ (compositePartialIso step i).source),
                (compositePartialIso step i).toPartialMap.hom ⟨_, hP⟩ = F.genericPoint →
                ∀ D : RDivisor X, transformSeq f fp D i F = D P := by
              intro i
              induction i with
              | zero =>
                intro P F hP h D
                obtain rfl : P = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective h
                rfl
              | succ i ih =>
                intro P F hP h D
                obtain ⟨hx1, hx2, hval⟩ := exists_trans_apply (compositePartialIso step i) (step i) hP
                have hco : Order.coheight ((compositePartialIso step i).toPartialMap.hom
                    ⟨_, hx1⟩) = 1 :=
                  (coheight_toPartialMap_hom _ hx1).trans P.coheight_genericPoint
                let P' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
                have hP'η : P'.genericPoint = (compositePartialIso step i).toPartialMap.hom
                    ⟨_, hx1⟩ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
                have hih := ih P P' hx1 hP'η.symm D
                have hstepval : (step i).toPartialMap.hom ⟨_, hx2⟩ = F.genericPoint :=
                  hval.symm.trans h
                have hfpF : fp i F.genericPoint = f i P'.genericPoint := by
                  rw [← hstepval, hP'η]
                  exact congrArg (fun φ => φ (⟨_, hx2⟩ : (step i).source.toScheme)) (hsOver i)
                haveI := hfP i
                haveI := hfpP i
                haveI : IsIntegral (W i) := (hWn i).1.toIsIntegral
                haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety (hWn i)
                haveI := (hfB i).isDominant
                have hbF := hfp1 i F.genericPoint F.coheight_genericPoint.le
                have hcoW : Order.coheight (fp i F.genericPoint) = 1 := by
                  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus (fp i) hbF]
                  exact F.coheight_genericPoint
                let Q : MMP.Mori.PrimeDivisor (W i) :=
                  AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoW
                have hQ : fp i F.genericPoint = Q.genericPoint :=
                  (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoW).symm
                have := Q.isDiscreteValuationRing_localRing
                change flipTransform (f i) (fp i) (transformSeq f fp D i) F = D P
                rw [← hih]
                exact MMP.Fourfold.flipTransform_apply_of_map_genericPoint
                  (hfB i).functionFieldMap_bijective
                  (surjective_of_isProper_of_isBirationalMorphism (fp i) (hfpB i))
                  (hfpF.symm.trans hQ) hQ (hQ ▸ hbF) (transformSeq f fp D i)
            refine ⟨compositePartialIso step, hIover, fun i P F h D => ?_,
              fun i F => exists_transformPrimeDivisor_eq_some_of_mem_target _ F
                (hItarget i _ F.coheight_genericPoint.le), ?_, ?_⟩
            · haveI := hsep i
              obtain ⟨hP, hv⟩ := mem_source_of_transformPrimeDivisor_eq_some _ h
                (hItarget i _ F.coheight_genericPoint.le)
              exact hIcoeff i P F hP hv D
            · intro k
              induction k with
              | zero =>
                intro P F hP hF
                obtain rfl : S = F := Option.some.inj hF
                exact hP
              | succ k ih =>
                intro P F hP hF
                change (primeSeq f fp N₁ S k).bind _ = some F at hF
                obtain ⟨Fk, hFk, hFkF⟩ := Option.bind_eq_some_iff.mp hF
                have hPk := ih P Fk hP hFk
                have hfl := hN₀ (N₁ + k) (by omega)
                haveI := hsep (N₁ + k)
                haveI := hsep (N₁ + (k + 1))
                obtain ⟨hPs, hPv⟩ := mem_source_of_transformPrimeDivisor_eq_some _ hPk
                  (hItarget _ _ Fk.coheight_genericPoint.le)
                have hFks : Fk.genericPoint ∈ (step (N₁ + k)).source :=
                  hsSource (N₁ + k) (by omega) _ Fk.coheight_genericPoint.le
                have hmem : P.genericPoint ∈
                    ((compositePartialIso step (N₁ + k)).trans (step (N₁ + k))).source :=
                  mem_trans_source _ _ hPs (hPv ▸ hFks)
                obtain ⟨hx1, hx2, hval⟩ := exists_trans_apply _ _ hmem
                have hco : Order.coheight ((step (N₁ + k)).toPartialMap.hom
                    ⟨_, hFks⟩) = 1 :=
                  (coheight_toPartialMap_hom _ hFks).trans Fk.coheight_genericPoint
                let F' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
                have hF'η : F'.genericPoint = (step (N₁ + k)).toPartialMap.hom ⟨_, hFks⟩ :=
                  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
                have hfpF' : fp (N₁ + k) F'.genericPoint = f (N₁ + k) Fk.genericPoint := by
                  rw [hF'η]
                  exact congrArg (fun φ => φ (⟨_, hFks⟩ : (step (N₁ + k)).source.toScheme))
                    (hsOver (N₁ + k))
                have hF'F : F' = F := Option.some.inj
                  ((flipTransformPrimeDivisor_eq_some_of_isSmall
                    hfl.isNegativeExtremalContraction.isNormalVariety_target hfl.isSmall
                    hfl.isSmall_flip hfpF').1.symm.trans hFkF)
                show MMP.Mori.RationalMap.transformPrimeDivisor
                  ((compositePartialIso step (N₁ + k)).trans (step (N₁ + k))).toRationalMap P =
                    some F
                refine transformPrimeDivisor_eq_some_of_mem_source _ hmem ?_
                have hpt : (⟨_, hx2⟩ : (step (N₁ + k)).source.toScheme) = ⟨_, hFks⟩ :=
                  Subtype.ext hPv
                rw [hval]
                exact (congrArg (fun p => (step (N₁ + k)).toPartialMap.hom p) hpt).trans
                  (hF'η.symm.trans (congrArg (fun G => G.genericPoint) hF'F))
            · intro i P F h
              haveI := hsep (i + 1)
              haveI := hsep i
              obtain ⟨hP, hv⟩ := mem_source_of_transformPrimeDivisor_eq_some _ h
                (hItarget (i + 1) _ F.coheight_genericPoint.le)
              obtain ⟨hx1, hx2, hval⟩ :=
                exists_trans_apply (compositePartialIso step i) (step i) hP
              have hco : Order.coheight ((compositePartialIso step i).toPartialMap.hom
                  ⟨_, hx1⟩) = 1 :=
                (coheight_toPartialMap_hom _ hx1).trans P.coheight_genericPoint
              let F₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
              have hF₀η : F₀.genericPoint = (compositePartialIso step i).toPartialMap.hom
                  ⟨_, hx1⟩ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
              refine ⟨F₀, transformPrimeDivisor_eq_some_of_mem_source _ hx1 hF₀η.symm, ?_⟩
              have hstepval : (step i).toPartialMap.hom ⟨_, hx2⟩ = F.genericPoint :=
                hval.symm.trans hv
              have hfpF : fp i F.genericPoint = f i F₀.genericPoint := by
                rw [← hstepval, hF₀η]
                exact congrArg (fun φ => φ (⟨_, hx2⟩ : (step i).source.toScheme)) (hsOver i)
              exact hfpF
          -- a transform has a unique source prime divisor
          have heUniq : ∀ i (P Q : MMP.Mori.PrimeDivisor X)
              (F : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
              MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap P = some F →
              MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap Q = some F →
              Q = P := by
            classical
            intro i P Q F hP hQ
            by_contra hne
            have h1 := heCoeff i P F hP (Finsupp.single P 1)
            have h2 := heCoeff i Q F hQ (Finsupp.single P 1)
            rw [h1, Finsupp.single_eq_same, Finsupp.single_eq_of_ne' (Ne.symm hne)] at h2
            exact one_ne_zero h2
          obtain ⟨S₀, hS₀⟩ := heSurj N₁ S
          have hSk : ∀ k, MMP.Mori.RationalMap.transformPrimeDivisor (e (N₁ + k)).toRationalMap S₀ =
              some (S' k) := fun k => heChain k S₀ (S' k) hS₀ (hS'eq k)
          have hBS₀ : B.coeff S₀ = 1 := by
            have h1 := hdlt.2.1 S₀
            have h2 : (B + C).coeff S₀ = B.coeff S₀ + C.coeff S₀ := rfl
            have h4 := heCoeff _ S₀ (S' 0) (hSk 0) B
            have h5 : (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).coeff S ≠ 0 := hS
            rw [DivisorWithCoeffs.coeff_roundDown, hBseq] at h5
            have h6 : (transformSeq f fp B N₁).coeff S = B.coeff S₀ := by
              rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
              exact h4
            rw [h6] at h5
            have h7 : B.coeff S₀ ≤ 1 := by linarith [hC S₀]
            by_contra hne
            exact h5 (Int.floor_eq_zero_iff.mpr ⟨hB S₀, lt_of_le_of_ne h7 hne⟩)
          -- the plt perturbation of the source boundary and its transport along the program
          obtain ⟨ε, Kc, B'X, A₀, hKc, hflipB, hpltB, hlamB, hantiB, hnefB, hupperB, hcrepB, hB'S,
              hA₀, hA₀amp, hA₀S, hB'A⟩ :
              ∃ (ε : ℝ) (Kc : ∀ k, Divisor (modelSeq X Y (N₁ + k))) (B'X : RDivisor X)
                (A₀ : QDivisor X),
                (∀ k, ∃ m : ℕ, (Kc k).IsCanonicalDivisor (modelStr sX sY (N₁ + k)) m) ∧
                (∀ k, IsRealFlipStep (modelStr sX sY (N₁ + k)) (sW (N₁ + k))
                  (modelStr sX sY (N₁ + (k + 1))) (Kc k)
                  (transformSeq f fp B'X (N₁ + k)) (Kc (k + 1))
                  (transformSeq f fp B'X (N₁ + (k + 1))) (f (N₁ + k)) (fp (N₁ + k))) ∧
                (∀ k, (∀ P, 0 ≤ (transformSeq f fp B'X (N₁ + k)).coeff P ∧
                    (transformSeq f fp B'X (N₁ + k)).coeff P ≤ 1) ∧
                  RDivisor.IsRCartier (Divisor.toRDivisor (Kc k) +
                    transformSeq f fp B'X (N₁ + k)) ∧
                  ∀ (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY (N₁ + k))) (a : ℝ),
                    E.IsExceptional → MMP.Intersection.IsLogDiscrepancy (modelStr sX sY (N₁ + k)) m
                      (transformSeq f fp B'X (N₁ + k)) E a → 0 < a) ∧
                (∀ k, 0 < lam (N₁ + k) - ε) ∧ Antitone (fun k => lam (N₁ + k) - ε) ∧
                (∀ k, MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY (N₁ + k))
                  (modelMap π πY (N₁ + k))
                  (MMP.Flips.logCanonicalDivisor (Kc k)
                    (transformSeq f fp B'X (N₁ + k) +
                      (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)))) ∧
                (∀ k, (∀ P, 0 ≤ (transformSeq f fp B'X (N₁ + k) +
                      (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)).coeff P ∧
                    (transformSeq f fp B'X (N₁ + k) +
                      (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)).coeff P ≤ 1) ∧
                  RDivisor.IsRCartier (Divisor.toRDivisor (Kc k) +
                    (transformSeq f fp B'X (N₁ + k) +
                      (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k))) ∧
                  ∀ (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY (N₁ + k))) (a : ℝ),
                    E.IsExceptional → MMP.Intersection.IsLogDiscrepancy (modelStr sX sY (N₁ + k)) m
                      (transformSeq f fp B'X (N₁ + k) +
                        (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k)) E a → 0 < a) ∧
                (∀ k, ∃ D : RDivisor (W (N₁ + k)),
                  MMP.Flips.IsRCartierPullback (f (N₁ + k)) D
                    (MMP.Flips.logCanonicalDivisor (Kc k)
                      (transformSeq f fp B'X (N₁ + k) +
                        (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k))) ∧
                  MMP.Flips.IsRCartierPullback (fp (N₁ + k)) D
                    (MMP.Flips.logCanonicalDivisor (Kc (k + 1))
                      (transformSeq f fp B'X (N₁ + (k + 1)) +
                        (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + (k + 1))))) ∧
                B'X.coeff S₀ = 1 ∧ 0 ≤ A₀ ∧ A₀.IsAmple ∧ A₀.coeff S₀ = 0 ∧
                ∀ P, (A₀.coeff P : ℝ) ≤ B'X.coeff P - (Finsupp.single S₀ (1 : ℝ) : RDivisor X) P := by
            classical
            -- the varieties and morphisms of the program
            have hnv : ∀ i, IsNormalVariety ℂ (modelStr sX sY i) := fun i =>
              ⟨(hprojT hn i).toIsVariety, inferInstance⟩
            have hQi : ∀ i, IsQFactorial (modelStr sX sY i) := fun i =>
              hYq i (by rw [hn]; exact le_top)
            have hnv' : ∀ i, IsNormalVariety ℂ (sY i) := fun i => hnv (i + 1)
            haveI hfPi : ∀ i, IsProper (f i) := hfP
            haveI hfpPi : ∀ i, IsProper (fp i) := hfpP
            haveI hWci : ∀ i, CompactSpace (W i) := fun i => by
              haveI := (hWn i).1.toQuasiCompact
              exact QuasiCompact.compactSpace_of_compactSpace (sW i)
            haveI hWii : ∀ i, IsIntegral (W i) := fun i => (hWn i).1.toIsIntegral
            haveI hWsi : ∀ i, IsSeparated (sW i) := fun i => (hWn i).1.toIsSeparated
            haveI hWli : ∀ i, LocallyOfFiniteType (sW i) := fun i => (hWn i).1.toLocallyOfFiniteType
            haveI hWqi : ∀ i, QuasiCompact (sW i) := fun i => (hWn i).1.toQuasiCompact
            haveI hXqi : ∀ i, QuasiCompact (modelStr sX sY i) := fun i => (hnv i).1.toQuasiCompact
            haveI hYqi : ∀ i, QuasiCompact (sY i) := fun i => (hnv (i + 1)).1.toQuasiCompact
            haveI hfDi : ∀ i, IsDominant (f i) := fun i => (hfB i).isDominant
            haveI hfpDi : ∀ i, IsDominant (fp i) := fun i => (hfpB i).isDominant
            have hBYi : ∀ i, BY i = flipTransform (f i) (fp i) (divisorSeq B BY i) := fun i => by
              rcases hstep i (hlt i) with hfl | hdv
              · exact hfl.eq_flipTransform
              · exact hdv.2.2.2.2.2.2.2
            have hAnti : ∀ i, MMP.Flips.IsRelativelyAmple (f i)
                (-MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) :=
              fun i => by
                rcases hstep i (hlt i) with hfl | hdv
                · exact hfl.isNegativeExtremalContraction.isRelativelyAntiAmple
                · exact hdv.2.1.isRelativelyAntiAmple
            have htrB : ∀ i (t : ℝ), flipTransform (f i) (fp i)
                (divisorSeq B BY i + t • divisorSeq C CY i) =
                  divisorSeq B BY (i + 1) + t • divisorSeq C CY (i + 1) := fun i t => by
              rw [map_add, flipTransform_smul]
              change _ = BY i + t • CY i
              rw [hBYi i, hCY i (hlt i)]
            -- the descent divisors are numerically trivial over the steps
            have hTriv : ∀ i, MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
                (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
                  (divisorSeq B BY i + lam i • divisorSeq C CY i)) := fun i => by
              obtain ⟨D, hD1, -⟩ := hdesc i (hlt i)
              exact isNumericallyTrivialOver_of_isRCartierPullback (f i) (hfW i) hD1
            have hTriv' : ∀ i, MMP.Flips.IsNumericallyTrivialOver ℂ (sY i) (fp i)
                (MMP.Flips.logCanonicalDivisor (divisorSeq K KY (i + 1))
                  (divisorSeq B BY (i + 1) + lam i • divisorSeq C CY (i + 1))) := fun i => by
              obtain ⟨D, -, hD2⟩ := hdesc i (hlt i)
              obtain ⟨m, hm⟩ := hcan hn i
              obtain ⟨m', hm'⟩ := hcan hn (i + 1)
              obtain ⟨φ, hφ⟩ := exists_principal_logCanonicalDivisor_flipTransform (hnv i)
                (hnv' i) (hWn i) (hfW i) (hfpW i) (hfB i) (hfpB i) (hfp1 i) hm hm'
                (divisorSeq B BY i + lam i • divisorSeq C CY i)
              rw [htrB] at hφ
              rw [hφ]
              exact isNumericallyTrivialOver_add_smul
                (isNumericallyTrivialOver_of_isRCartierPullback (fp i) (hfpW i) hD2)
                (isNumericallyTrivialOver_principalDivisor (fp i) φ) 1
            -- the scaling levels are nonincreasing, at most one, and positive on the tail
            have hlev : ∀ i, lam (i + 1) ≤ lam i := fun i => by
              obtain ⟨D, hD1, hD2⟩ := hdesc i (hlt i)
              obtain ⟨m, hm⟩ := hcan hn i
              obtain ⟨m', hm'⟩ := hcan hn (i + 1)
              have h := isRelativelyNef_logCanonicalDivisor_flipTransform (hnv i) (hnv' i)
                (hWn i) (hfW i) (hfpW i) (hfB i) (hfpB i) (hfp1 i) hm hm' (g i) (hfg i (hlt i))
                (hfpg i (hlt i)) hD1 hD2 (hthr i (hlt i)).1.2
              rw [htrB] at h
              exact (hthr (i + 1) (hlt _)).2 ⟨(hthr i (hlt i)).1.1, h⟩
            have hanti : Antitone lam := antitone_nat_of_succ_le hlev
            have hlam0 : lam 0 ≤ 1 := (hthr 0 (hlt 0)).2 ⟨zero_le_one, by
              change MMP.Flips.IsRelativelyNef ℂ sX π (MMP.Flips.logCanonicalDivisor K
                (B + (1 : ℝ) • C))
              rw [one_smul]
              exact hnef⟩
            have hposT : ∀ k, 0 < lam (N₁ + k) := fun k => by
              have hfl := hN₀ (N₁ + k) (by omega)
              by_contra hle
              have h0 : lam (N₁ + k) = 0 :=
                le_antisymm (not_lt.mp hle) (hthr (N₁ + k) (hlt _)).1.1
              have hn0 := (hthr (N₁ + k) (hlt _)).1.2
              rw [h0, zero_smul, add_zero, ← hfg (N₁ + k) (hlt _)] at hn0
              obtain ⟨w, hw⟩ := exists_notMem_biregularLocus _ hfl.not_isIso
              obtain ⟨y, hy, hycl⟩ :=
                (biregularLocus (f (N₁ + k))).compl.isClosed.exists_closed_singleton ⟨w, hw⟩
              obtain ⟨Cv, hCv, -⟩ := exists_properCurve_isContractedBy_of_notMem_biregularLocus
                (hprojT hn _).toIsVariety (hWn _) _ (hfW _) (hfB _) hycl hy
              exact not_isRelativelyNef_of_isRelativelyAmple_neg (g _) (hAnti _) hCv hn0
            obtain ⟨u, hu⟩ : ∃ u, u = lam N₁ := ⟨_, rfl⟩
            have hu1 : u ≤ 1 := by rw [hu]; exact (hanti (Nat.zero_le N₁)).trans hlam0
            have hu0 : 0 < u := by simpa [hu] using hposT 0
            have hlamu : ∀ k, lam (N₁ + k) ≤ u := fun k => by rw [hu]; exact hanti (by omega)
            have hBC1 : ∀ P, B.coeff P + C.coeff P ≤ 1 := fun P => hdlt.2.1 P
            -- the level `ε` of the lower boundary
            obtain ⟨ε, hε0, hεT, hεC⟩ : ∃ ε : ℝ, 0 ≤ ε ∧ (∀ k, ε < lam (N₁ + k)) ∧
                ∀ P, B.coeff P + u * C.coeff P = 1 → (1 : ℝ) / 2 ≤ B.coeff P + ε * C.coeff P := by
              by_cases hu' : u < 1
              · refine ⟨0, le_rfl, hposT, fun P hP => ?_⟩
                have hCz : C.coeff P = 0 := by
                  by_contra hne
                  have hpos' : 0 < C.coeff P := lt_of_le_of_ne (hC P) (Ne.symm hne)
                  have : 0 < C.coeff P * (1 - u) := mul_pos hpos' (by linarith)
                  nlinarith [hBC1 P]
                rw [hCz] at hP ⊢
                simp only [mul_zero, add_zero] at hP ⊢
                linarith
              · have hu1' : u = 1 := le_antisymm hu1 (not_lt.mp hu')
                refine ⟨1 / 2, by norm_num, fun k => ?_, fun P hP => ?_⟩
                · rcases hcase with h | h
                  · linarith [h (N₁ + k) (by omega)]
                  · exact absurd (by rw [hu]; exact h) hu'
                · rw [hu1', one_mul] at hP
                  linarith [hB P]
            have hεu : ε ≤ u := by simpa [hu] using (hεT 0).le
            -- floor lowering on the source keeping `S₀`
            have hΓc : ∀ P, (B + u • C).coeff P = B.coeff P + u * C.coeff P := fun P => by
              simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
            have hΓ0 : ∀ P, 0 ≤ (B + u • C).coeff P := fun P => by
              rw [hΓc]; nlinarith [hB P, hC P]
            have hΓle : ∀ P, (B + u • C).coeff P ≤ (B + C).coeff P := fun P => by
              rw [hΓc]
              change _ ≤ B.coeff P + C.coeff P
              nlinarith [hC P]
            have hΓdlt : IsRealDltPair sX (B + u • C) := isRealDltPair_of_le hXq hdlt hΓ0 hΓle
            obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : QDivisor X, A₀ = (1 / 2 : ℚ) • A := ⟨_, rfl⟩
            have hA₀c : ∀ P, A₀.coeff P = A.coeff P / 2 := fun P => by
              rw [hA₀def, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; ring
            have hA₀amp : A₀.IsAmple := by
              obtain ⟨m, hm, D, hD, hDc⟩ := hA
              refine ⟨2 * m, by omega, D, ?_, hDc⟩
              rw [hD, hA₀def, smul_smul]
              congr 1
              push_cast
              ring
            have hCS₀ : C.coeff S₀ = 0 := by linarith [hBC1 S₀, hC S₀]
            have hA0S : A.coeff S₀ = 0 := by
              by_contra h
              have h1 := hAfloor S₀ h
              have h2 : (B + C).coeff S₀ = B.coeff S₀ + C.coeff S₀ := rfl
              rw [h2, hBS₀, hCS₀] at h1
              norm_num at h1
            have hΓS : (B + u • C).coeff S₀ = 1 := by rw [hΓc, hBS₀, hCS₀]; ring
            obtain ⟨δ₀, hδ₀, hfun⟩ := IsRealDltPair.exists_isRealPltPair_sub_add_of_isAmple hXq hX
              hΓdlt hA₀amp (fun P => by rw [hA₀c]; exact div_nonneg (hA0 P) (by norm_num))
              (fun P => by
                rw [hA₀c, hΓc]
                have h1 : (0 : ℝ) ≤ A.coeff P := by exact_mod_cast hA0 P
                have h2 := hAB P
                have h3 := mul_nonneg hu0.le (hC P)
                push_cast
                linarith)
              (fun P hP => by
                have hAP : A.coeff P ≠ 0 := fun h => hP (by rw [hA₀c, h]; norm_num)
                rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_zero_iff]
                exact ⟨hΓ0 P, (hΓle P).trans_lt (hAfloor P hAP)⟩)
              S₀ hΓS
            obtain ⟨δ, hδ0, hδδ₀, hδh⟩ : ∃ δ : ℚ, 0 < δ ∧ δ < δ₀ ∧ δ < 1 / 2 :=
              ⟨min (δ₀ / 2) (1 / 4), lt_min (by positivity) (by norm_num),
                (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by norm_num)⟩
            obtain ⟨A', hA'0, -, -, hA'S, hA'lin, hΓ'01, hΓ'S, hΓ'lt, -, hΓ'exc⟩ :=
              hfun δ hδ0 hδδ₀ 1 one_pos ∅ Set.finite_empty (by simp)
            obtain ⟨G, hGdef⟩ : ∃ G : RDivisor X, G = QDivisor.toRDivisor A' -
                QDivisor.toRDivisor (A₀ + δ • Divisor.toQDivisor
                  (DivisorWithCoeffs.roundDown (B + u • C) - (Finsupp.single S₀ 1 : Divisor X))) :=
              ⟨_, rfl⟩
            have hΓ'eq : B + u • C - QDivisor.toRDivisor (A₀ + δ • Divisor.toQDivisor
                (DivisorWithCoeffs.roundDown (B + u • C) - (Finsupp.single S₀ 1 : Divisor X))) +
                QDivisor.toRDivisor A' = B + u • C + G := by
              rw [hGdef]; abel
            rw [hΓ'eq] at hΓ'01 hΓ'S hΓ'lt hΓ'exc
            -- the coefficients of `G`
            have hTc : ∀ P, (((DivisorWithCoeffs.roundDown (B + u • C) -
                (Finsupp.single S₀ 1 : Divisor X)).coeff P : ℤ) : ℝ) =
                (if B.coeff P + u * C.coeff P = 1 then 1 else 0) - (if S₀ = P then 1 else 0) :=
              fun P => by
                rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundDown,
                  DivisorWithCoeffs.coeff_apply (Finsupp.single _ _), Finsupp.single_apply, hΓc]
                have h0 := hΓ0 P
                have h1 := (hΓle P).trans (hdlt.2.1 P)
                rw [hΓc] at h0 h1
                by_cases h : B.coeff P + u * C.coeff P = 1
                · rw [if_pos h, h, Int.floor_one]
                  split_ifs <;> simp
                · rw [if_neg h, Int.floor_eq_zero_iff.mpr ⟨h0, lt_of_le_of_ne h1 h⟩]
                  split_ifs <;> simp
            have hGc : ∀ P, G.coeff P = (A'.coeff P : ℝ) - (A.coeff P : ℝ) / 2 - (δ : ℝ) *
                ((if B.coeff P + u * C.coeff P = 1 then 1 else 0) - (if S₀ = P then 1 else 0)) :=
              fun P => by
                rw [← hTc P, hGdef]
                simp only [DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor,
                  DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
                  Divisor.coeff_toQDivisor, hA₀c]
                push_cast
                ring
            obtain ⟨B'X, hB'Xdef⟩ : ∃ B'X : RDivisor X, B'X = B + ε • C + G := ⟨_, rfl⟩
            have hB'Xc : ∀ P, B'X.coeff P = B.coeff P + ε * C.coeff P + G.coeff P := fun P => by
              rw [hB'Xdef]
              simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
            have hΓtc : ∀ (t : ℝ) P, (B + t • C + G).coeff P =
                (B + u • C + G).coeff P - (u - t) * C.coeff P := fun t P => by
              simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
              ring
            have hΓtle : ∀ t, t ≤ u → ∀ P, (B + t • C + G).coeff P ≤ 1 ∧
                ((B + t • C + G).coeff P = 1 → P = S₀) := fun t ht P => by
              have hCt : 0 ≤ (u - t) * C.coeff P := mul_nonneg (by linarith) (hC P)
              rw [hΓtc]
              refine ⟨by linarith [(hΓ'01 P).2], fun h1 => ?_⟩
              by_contra hne
              linarith [hΓ'lt P hne]
            have hB'A : ∀ P, (A₀.coeff P : ℝ) ≤
                B'X.coeff P - (Finsupp.single S₀ (1 : ℝ) : RDivisor X) P := fun P => by
              rw [hB'Xc, hGc, hA₀c, Finsupp.single_apply]
              have hA'P : (0 : ℝ) ≤ A'.coeff P := by exact_mod_cast hA'0 P
              have hAP : (0 : ℝ) ≤ A.coeff P := by exact_mod_cast hA0 P
              have hδ' : (δ : ℝ) < 1 / 2 := by
                rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
                exact_mod_cast hδh
              have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
              push_cast
              by_cases hPS : S₀ = P
              · subst hPS
                norm_num [hBS₀, hCS₀, hA0S, hA'S]
              · simp only [if_neg hPS, sub_zero]
                by_cases h1 : B.coeff P + u * C.coeff P = 1
                · have hA1 : A.coeff P = 0 := by
                    by_contra hA1
                    have h2 := hAfloor P hA1
                    have h3 : (B + C).coeff P = B.coeff P + C.coeff P := rfl
                    rw [h3] at h2
                    have := hΓle P
                    rw [hΓc, h1, h3] at this
                    linarith
                  rw [if_pos h1, hA1]
                  have := hεC P h1
                  push_cast
                  linarith
                · rw [if_neg h1]
                  simp only [sub_self, mul_zero, sub_zero]
                  have := hAB P
                  have := mul_nonneg hε0 (hC P)
                  linarith
            have hB'X01 : ∀ P, 0 ≤ B'X.coeff P ∧ B'X.coeff P ≤ 1 := fun P => by
              have h1 := hB'A P
              have h2 : (0 : ℝ) ≤ (A₀.coeff P : ℝ) := by
                rw [hA₀c]; exact_mod_cast div_nonneg (hA0 P) (by norm_num)
              have h3 : (0 : ℝ) ≤ (Finsupp.single S₀ (1 : ℝ) : RDivisor X) P := by
                rw [Finsupp.single_apply]; split_ifs <;> norm_num
              refine ⟨by linarith, ?_⟩
              have h4 := (hΓtle ε hεu P).1
              rwa [hB'Xdef]
            -- `G` and its strict transforms are rational multiples of principal divisors
            obtain ⟨mG, hmG, φ, hφ⟩ := hA'lin
            have hGφ : G = ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φ) := by
              refine DivisorWithCoeffs.ext' fun P => ?_
              have h := congrArg (fun D : QDivisor X => D.coeff P) hφ
              simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
                Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast] at h
              rw [hGdef]
              simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
                QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul]
              have hm : (mG : ℝ) ≠ 0 := by exact_mod_cast hmG.ne'
              rw [eq_inv_mul_iff_mul_eq₀ hm]
              exact_mod_cast h
            have hGseq : ∀ i, ∃ φi : (RationalFunctions (modelSeq X Y i))ˣ,
                transformSeq f fp G i =
                  ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φi) := by
              intro i
              induction i with
              | zero => exact ⟨φ, hGφ⟩
              | succ i ih =>
                obtain ⟨φi, hφi⟩ := ih
                obtain ⟨w, hw, hwφ⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq (hfB i) φi
                refine ⟨pullbackRationalFunction (fp i) w
                  (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp i) _), ?_⟩
                change flipTransform (f i) (fp i) (transformSeq f fp G i) = _
                rw [hφi, flipTransform_smul, flipTransform_toRDivisor, ← hwφ,
                  flipTransform_principalDivisor_pullback (hWn i) (hfW i) (hfpW i) (hnv i)
                    (hnv' i) (hfB i) (hfpB i) (hfp1 i) w hw
                    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp i) _)]
                rfl
            have hGtriv : ∀ i {Z' : Scheme.{0}} (g' : modelSeq X Y i ⟶ Z'),
                MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY i) g'
                  (transformSeq f fp G i) := fun i Z' g' => by
              obtain ⟨φi, hφi⟩ := hGseq i
              rw [hφi]
              exact isNumericallyTrivialOver_smul (isNumericallyTrivialOver_principalDivisor g' φi) _
            have hseq : ∀ (t : ℝ) i, transformSeq f fp (B + t • C + G) i =
                divisorSeq B BY i + t • divisorSeq C CY i + transformSeq f fp G i := fun t i => by
              rw [transformSeq_add, transformSeq_add, transformSeq_smul, ← hBseq, ← hCseq]
            -- coefficients of strict transforms are coefficients on the source
            have hcoefE : ∀ i (F : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
                ∃ P : MMP.Mori.PrimeDivisor X,
                  MMP.Mori.RationalMap.transformPrimeDivisor (e i).toRationalMap P = some F ∧
                  ∀ D : RDivisor X, (transformSeq f fp D i).coeff F = D.coeff P := fun i F => by
              obtain ⟨P, hP⟩ := heSurj i F
              exact ⟨P, hP, fun D => by
                rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
                exact heCoeff i P F hP D⟩
            have hRC : ∀ i (D : RDivisor (modelSeq X Y i)), RDivisor.IsRCartier D := fun i =>
              isRCartier_of_isQFactorial (hQi i)
            -- the transform of `S₀` exists up to stage `N₁`
            have hSomeS : ∀ j, j ≤ N₁ → ∃ F,
                MMP.Mori.RationalMap.transformPrimeDivisor (e j).toRationalMap S₀ = some F := by
              intro j hj
              refine Nat.decreasingInduction (motive := fun j _ => ∃ F : MMP.Mori.PrimeDivisor
                (modelSeq X Y j), MMP.Mori.RationalMap.transformPrimeDivisor
                  (e j).toRationalMap S₀ = some F) (fun j _ ih => ?_) ⟨S, hS₀⟩ hj
              obtain ⟨F, hF⟩ := ih
              obtain ⟨F₀, hF₀, -⟩ := heStep j S₀ F hF
              exact ⟨F₀, hF₀⟩
            -- the upper boundary is plt up to stage `N₁`, by negativity of the steps
            have hPre : ∀ i, i ≤ N₁ → ∀ (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY i)) (a : ℝ),
                E.IsExceptional → MMP.Intersection.IsLogDiscrepancy (modelStr sX sY i) m
                  (transformSeq f fp (B + u • C + G) i) E a → 0 < a := by
              intro i
              induction i with
              | zero => intro _; exact hΓ'exc
              | succ i ih =>
                intro hi
                have hi' : i ≤ N₁ := by omega
                obtain ⟨m, hm⟩ := hcan hn i
                obtain ⟨m', hm'⟩ := hcan hn (i + 1)
                have hul : u ≤ lam i := by rw [hu]; exact hanti hi'
                refine logDiscrepancy_pos_flipTransform (hnv i) (hnv' i) (hWn i) (hfW i)
                  (hfpW i) (hfB i) (hfpB i) (hfp1 i) (hQi i) (hQi (i + 1)) hm hm' ?_ ?_ ?_
                  (ih hi') ?_
                · rw [hseq u i]
                  exact isRelativelyNef_neg_logCanonicalDivisor_add (hAnti i) (hTriv i)
                    (hGtriv i (f i)) hu0.le hul
                · change MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY (i + 1)) (fp i)
                    (MMP.Flips.logCanonicalDivisor (divisorSeq K KY (i + 1))
                      (transformSeq f fp (B + u • C + G) (i + 1)))
                  rw [hseq u (i + 1)]
                  rcases hstep i (hlt i) with hfl | hdv
                  · exact isRelativelyNef_logCanonicalDivisor_add hfl.isRelativelyAmple_flip
                      (hTriv' i) (hGtriv (i + 1) (fp i)) hu0.le hul
                  · have := hdv.2.2.2.2.2.1
                    haveI := hYqi i
                    exact isRelativelyNef_of_isIso (sX := sY i)
                      (isCartierCombination_of_isQFactorial (hQi (i + 1)) _)
                · intro F
                  obtain ⟨P, -, hPc⟩ := hcoefE i F
                  rw [hPc]
                  exact (hΓtle u le_rfl P).1
                · intro F hF
                  obtain ⟨P, hPF, hPc⟩ := hcoefE i F
                  rw [hPc] at hF
                  obtain rfl := (hΓtle u le_rfl P).2 hF
                  obtain ⟨F', hF'⟩ := hSomeS (i + 1) hi
                  obtain ⟨F₀, hF₀, hfpF⟩ := heStep i P F' hF'
                  obtain rfl : F₀ = F := Option.some.inj (hF₀.symm.trans hPF)
                  rw [← hfpF, MMP.Positivity.coheight_map_of_mem_biregularLocus (fp i)
                    (hfp1 i _ F'.coheight_genericPoint.le)]
                  exact F'.coheight_genericPoint
            -- along the tail the upper boundary stays plt, by crepancy and lowering
            have hTail : ∀ k (m : ℕ) (E : DivisorOver ℂ (modelStr sX sY (N₁ + k))) (a : ℝ),
                E.IsExceptional → MMP.Intersection.IsLogDiscrepancy (modelStr sX sY (N₁ + k)) m
                  (transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k)) E a → 0 < a := by
              intro k
              induction k with
              | zero =>
                intro m E a hE ha
                refine hPre N₁ le_rfl m E a hE ?_
                rw [hu]
                exact ha
              | succ k ih =>
                have hfl := hN₀ (N₁ + k) (by omega)
                obtain ⟨m, hm⟩ := hcan hn (N₁ + k)
                obtain ⟨m', hm'⟩ := hcan hn (N₁ + k + 1)
                have h1 := logDiscrepancy_pos_flipTransform (hnv (N₁ + k)) (hnv' (N₁ + k))
                  (hWn _) (hfW _) (hfpW _) (hfB _) (hfpB _) (hfp1 _) (hQi _) (hQi (N₁ + k + 1)) hm
                  hm' (Γ := transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k)) (by
                    rw [hseq]
                    exact isRelativelyNef_neg_logCanonicalDivisor_add (hAnti _) (hTriv _)
                      (hGtriv _ (f _)) (hposT k).le le_rfl) (by
                    change MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY (N₁ + k + 1)) (fp (N₁ + k))
                      (MMP.Flips.logCanonicalDivisor (divisorSeq K KY (N₁ + k + 1))
                        (transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k + 1)))
                    rw [hseq]
                    exact isRelativelyNef_logCanonicalDivisor_add hfl.isRelativelyAmple_flip
                      (hTriv' _) (hGtriv (N₁ + k + 1) (fp (N₁ + k))) (hposT k).le le_rfl) (fun F => by
                    obtain ⟨P, -, hPc⟩ := hcoefE _ F
                    rw [hPc]
                    exact (hΓtle _ (hlamu k) P).1) ih (fun F _ =>
                    (map_genericPoint_mem_biregularLocus_of_isSmall hfl.isSmall F).2)
                refine logDiscrepancy_pos_of_le (hQi (N₁ + (k + 1))) (fun F => ?_) h1
                change (transformSeq f fp (B + lam (N₁ + k + 1) • C + G) (N₁ + k + 1)).coeff F ≤
                  (transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k + 1)).coeff F
                rw [hseq, hseq]
                simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
                have hCF : 0 ≤ (divisorSeq C CY (N₁ + k + 1)).coeff F := hCnn _ F
                have := hlev (N₁ + k)
                nlinarith
            -- canonical divisors along the tail: strict transforms of `K_{N₁}`
            obtain ⟨Kc, hKc0, hKcS⟩ : ∃ Kc : ∀ k, Divisor (modelSeq X Y (N₁ + k)),
                Kc 0 = divisorSeq K KY N₁ ∧
                ∀ k, Kc (k + 1) = flipTransform (f (N₁ + k)) (fp (N₁ + k)) (Kc k) :=
              ⟨tailTransformSeq f fp N₁ (divisorSeq K KY N₁), rfl, fun k => rfl⟩
            have hKc : ∀ k, ∃ m : ℕ, (Kc k).IsCanonicalDivisor (modelStr sX sY (N₁ + k)) m := by
              intro k
              induction k with
              | zero => rw [hKc0]; exact hcan hn N₁
              | succ k ih =>
                obtain ⟨m, hm⟩ := ih
                rw [hKcS]
                exact ⟨m, isCanonicalDivisor_flipTransform (hnv (N₁ + k)) (hnv' (N₁ + k)) (hWn _)
                  (hfW _) (hfpW _) (hfB _) (hfpB _) (hfp1 _) hm⟩
            -- the adjoints along the tail, up to principal divisors
            have hform : ∀ k, ∃ (χ : (RationalFunctions (modelSeq X Y (N₁ + k)))ˣ)
                (φk : (RationalFunctions (modelSeq X Y (N₁ + k)))ˣ),
                Kc k - divisorSeq K KY (N₁ + k) = MMP.Mori.principalDivisor χ ∧
                transformSeq f fp G (N₁ + k) =
                  ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φk) ∧
                ∀ t : ℝ, MMP.Flips.logCanonicalDivisor (Kc k)
                  (transformSeq f fp B'X (N₁ + k) + t • divisorSeq C CY (N₁ + k)) =
                  MMP.Flips.logCanonicalDivisor (divisorSeq K KY (N₁ + k))
                    (divisorSeq B BY (N₁ + k) + (ε + t) • divisorSeq C CY (N₁ + k)) +
                  (Divisor.toRDivisor (MMP.Mori.principalDivisor χ) +
                    ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φk)) := fun k => by
              obtain ⟨m, hm⟩ := hKc k
              obtain ⟨m', hm'⟩ := hcan hn (N₁ + k)
              obtain ⟨χ, hχ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _
                (hnv (N₁ + k)) hm hm'
              obtain ⟨φk, hφk⟩ := hGseq (N₁ + k)
              refine ⟨χ, φk, hχ, hφk, fun t => ?_⟩
              have hK' : Divisor.toRDivisor (Kc k) = Divisor.toRDivisor (divisorSeq K KY (N₁ + k)) +
                  Divisor.toRDivisor (MMP.Mori.principalDivisor χ) := by
                rw [← hχ, map_sub]; abel
              rw [hB'Xdef, hseq, hφk]
              simp only [MMP.Flips.logCanonicalDivisor]
              rw [hK']
              module
            refine ⟨ε, Kc, B'X, A₀, hKc, fun k => ?_, fun k => ⟨fun P => ?_, hRC _ _, ?_⟩,
              fun k => by linarith [hεT k], fun a b hab => ?_, fun k => ?_,
              fun k => ⟨fun P => ?_, hRC _ _, ?_⟩, fun k => ?_, ?_, ?_, hA₀amp,
              by rw [hA₀c, hA0S]; norm_num, hB'A⟩
            · -- the steps of the tail are flips for the perturbed boundary
              obtain ⟨χ, φk, -, -, hk⟩ := hform k
              obtain ⟨χ', φk', -, -, hk'⟩ := hform (k + 1)
              have hfl := hN₀ (N₁ + k) (by omega)
              have hN : MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY (N₁ + k)) (f (N₁ + k))
                  (Divisor.toRDivisor (MMP.Mori.principalDivisor χ) +
                    ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φk)) :=
                isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_principalDivisor _ χ)
                  (isNumericallyTrivialOver_principalDivisor _ φk) _
              have hN' : MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX sY (N₁ + (k + 1)))
                  (fp (N₁ + k)) (Divisor.toRDivisor (MMP.Mori.principalDivisor χ') +
                    ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor φk')) :=
                isNumericallyTrivialOver_add_smul (isNumericallyTrivialOver_principalDivisor _ χ')
                  (isNumericallyTrivialOver_principalDivisor _ φk') _
              haveI := hYqi (N₁ + k)
              refine isRealFlipStep_perturb hfl (hQi _) (hQi (N₁ + k + 1)) hε0 (hεT k) (hTriv _)
                (hTriv' _) hN hN' ?_ ?_ (hKc (k + 1)) rfl
              · have := hk 0
                rwa [zero_smul, add_zero, add_zero] at this
              · have := hk' 0
                rwa [zero_smul, add_zero, add_zero] at this
            · obtain ⟨Q, -, hQc⟩ := hcoefE (N₁ + k) P
              rw [hQc]
              exact hB'X01 Q
            · refine logDiscrepancy_pos_of_le (hQi (N₁ + k)) (fun F => ?_) (hTail k)
              rw [hB'Xdef, hseq, hseq]
              simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
              have hCF : 0 ≤ (divisorSeq C CY (N₁ + k)).coeff F := hCnn _ F
              have := hεT k
              nlinarith
            · show lam (N₁ + b) - ε ≤ lam (N₁ + a) - ε
              have := hanti (show N₁ + a ≤ N₁ + b by omega)
              linarith
            · obtain ⟨χ, φk, -, -, hk⟩ := hform k
              rw [hk, show ε + (lam (N₁ + k) - ε) = lam (N₁ + k) by ring]
              have h1 := isRelativelyNef_add_smul (isRelativelyNef_add_smul (hthr _ (hlt _)).1.2
                (isNumericallyTrivialOver_principalDivisor _ χ) 1)
                (isNumericallyTrivialOver_principalDivisor _ φk) ((mG : ℝ)⁻¹)
              rw [one_smul, add_assoc] at h1
              exact h1
            · have hEq : transformSeq f fp B'X (N₁ + k) +
                  (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k) =
                  transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k) := by
                rw [hB'Xdef, hseq, hseq]; module
              rw [hEq]
              obtain ⟨Q, -, hQc⟩ := hcoefE (N₁ + k) P
              rw [hQc]
              refine ⟨?_, (hΓtle _ (hlamu k) Q).1⟩
              have h1 := (hB'X01 Q).1
              rw [hB'Xc] at h1
              simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
              have := mul_nonneg (show 0 ≤ lam (N₁ + k) - ε by linarith [hεT k]) (hC Q)
              nlinarith
            · have hEq : transformSeq f fp B'X (N₁ + k) +
                  (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k) =
                  transformSeq f fp (B + lam (N₁ + k) • C + G) (N₁ + k) := by
                rw [hB'Xdef, hseq, hseq]; module
              rw [hEq]
              exact hTail k
            · -- crepant descent of the perturbed upper adjoint
              obtain ⟨D, hD1, hD2⟩ := hdesc (N₁ + k) (hlt _)
              obtain ⟨χ, φk, hχ, hφk, hk⟩ := hform k
              obtain ⟨w₁, hw₁, hwχ⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq (hfB _) χ
              obtain ⟨w₂, hw₂, hwφ⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq (hfB _) φk
              have hP1 := isRCartierPullback_add_sum_principal (f (N₁ + k)) hD1 ![1, (mG : ℝ)⁻¹]
                ![w₁, w₂]
              have hP2 := isRCartierPullback_add_sum_principal (fp (N₁ + k)) hD2 ![1, (mG : ℝ)⁻¹]
                ![w₁, w₂]
              simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.head_cons, one_smul] at hP1 hP2
              refine ⟨D + (Divisor.toRDivisor (MMP.Mori.principalDivisor w₁) +
                ((mG : ℝ)⁻¹) • Divisor.toRDivisor (MMP.Mori.principalDivisor w₂)), ?_, ?_⟩
              · convert hP1 using 1
                rw [hk, show ε + (lam (N₁ + k) - ε) = lam (N₁ + k) by ring, ← hwχ, ← hwφ]
              · change MMP.Flips.IsRCartierPullback (fp (N₁ + k)) _
                  (MMP.Flips.logCanonicalDivisor (Kc (k + 1))
                    (transformSeq f fp B'X (N₁ + k + 1) +
                      (lam (N₁ + k) - ε) • divisorSeq C CY (N₁ + k + 1)))
                convert hP2 using 1
                have hKc1 : Divisor.toRDivisor (X := Y (N₁ + k)) (Kc (k + 1)) =
                    Divisor.toRDivisor (MMP.Mori.principalDivisor
                      (pullbackRationalFunction (fp (N₁ + k)) w₁
                        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant
                          (fp _) _))) +
                    Divisor.toRDivisor (flipTransform (f (N₁ + k)) (fp (N₁ + k))
                      (divisorSeq K KY (N₁ + k))) := by
                  rw [hKcS, eq_add_of_sub_eq hχ, map_add, ← hwχ,
                    flipTransform_principalDivisor_pullback (hWn (N₁ + k)) (hfW _) (hfpW _)
                      (hnv (N₁ + k)) (hnv' (N₁ + k)) (hfB _) (hfpB _) (hfp1 _) w₁ hw₁
                      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp _) _)]
                  exact map_add _ _ _
                have hG1 : transformSeq f fp G (N₁ + k + 1) = ((mG : ℝ)⁻¹) •
                    Divisor.toRDivisor (MMP.Mori.principalDivisor
                      (pullbackRationalFunction (fp (N₁ + k)) w₂
                        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant
                          (fp _) _))) := by
                  change flipTransform (f (N₁ + k)) (fp (N₁ + k))
                    (transformSeq f fp G (N₁ + k)) = _
                  rw [hφk, flipTransform_smul, flipTransform_toRDivisor, ← hwφ,
                    flipTransform_principalDivisor_pullback (hWn (N₁ + k)) (hfW _) (hfpW _)
                      (hnv (N₁ + k)) (hnv' (N₁ + k)) (hfB _) (hfpB _) (hfp1 _) w₂ hw₂
                      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp _) _)]
                rw [flipTransform_logCanonicalDivisor, htrB, hB'Xdef, hseq, hG1]
                simp only [MMP.Flips.logCanonicalDivisor]
                rw [hKc1]
                have key : ∀ (a₁ a₂ k₀ b c₀ : RDivisor (Y (N₁ + k))),
                    a₁ + k₀ + (b + ε • c₀ + ((mG : ℝ)⁻¹) • a₂ + (lam (N₁ + k) - ε) • c₀) =
                      k₀ + (b + lam (N₁ + k) • c₀) + (a₁ + ((mG : ℝ)⁻¹) • a₂) := by
                  intro a₁ a₂ k₀ b c₀
                  module
                exact key _ _ _ _ _
            · -- `B'X` has coefficient one at `S₀`
              norm_num [hB'Xc, hGc, hBS₀, hCS₀, hA0S, hA'S]
            · refine Finsupp.le_def.mpr fun P => ?_
              rw [Finsupp.coe_zero, Pi.zero_apply, ← DivisorWithCoeffs.coeff_apply, hA₀c]
              exact div_nonneg (hA0 P) (by norm_num)
          have hnorm : IsNormal S₀.idealSheaf.subscheme := by
            have hΓ := isDltPair_roundDown_of_isRealDltPair hXq hdlt
            have hM := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK _).mp hΓ
            have hΓS : (B + C).coeff S₀ = 1 := by
              have h1 := hdlt.2.1 S₀
              have h2 : (B + C).coeff S₀ = B.coeff S₀ + C.coeff S₀ := rfl
              linarith [hC S₀]
            refine MMP.Mori.IsDltPair.isNormal_subscheme_of_coeff_roundDown_ne_zero hM
              (by norm_num) (fun P => hΓ.1.2.1 P) S₀ ?_
            rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor,
              DivisorWithCoeffs.coeff_roundDown, hΓS]
            simp
          refine ⟨ε, Kc, fun k => transformSeq f fp B'X (N₁ + k), S₀, hnorm, A₀,
            fun k => (e (N₁ + k)).toRationalMap, fun k => (e (N₁ + k)).symm.toRationalMap,
            hKc, hflipB, hpltB, hlamB, hantiB, hnefB, hupperB, hcrepB, fun k => ?_, fun k => ?_, hA₀,
            hA₀amp, hA₀S, fun k => ⟨e (N₁ + k), rfl, rfl⟩,
            fun k => compHom_toRationalMap_eq_of_isOver (heOver _),
            fun k => compHom_toRationalMap_eq_of_isOver (heOver _).symm, hSk, ?_, fun k => ?_⟩
          · rw [DivisorWithCoeffs.coeff_apply, heCoeff _ S₀ (S' k) (hSk k) B'X,
              ← DivisorWithCoeffs.coeff_apply, hB'S]
          · rw [hCseq, DivisorWithCoeffs.coeff_apply, heCoeff _ S₀ (S' k) (hSk k) C,
              ← DivisorWithCoeffs.coeff_apply]
            have h1 := hdlt.2.1 S₀
            have h2 : (B + C).coeff S₀ = B.coeff S₀ + C.coeff S₀ := rfl
            have h3 : B.coeff S₀ = 1 := hBS₀
            linarith [hC S₀]
          · intro k F hF
            obtain ⟨P, hP⟩ := heSurj _ F
            exact absurd hP (hF P)
          · intro F
            obtain ⟨P, hP⟩ := heSurj _ F
            have hu := heUniq (N₁ + k) P
            have hcoef : (MMP.Mori.RationalMap.transformDivisor (e (N₁ + k)).toRationalMap A₀) F =
                A₀ P := mapPrimeDivisors_apply_of_unique hP (fun Q hQ => hu Q F hP hQ) A₀
            have hsingle : (Finsupp.single (S' k) (1 : ℝ) : RDivisor _) F =
                (Finsupp.single S₀ (1 : ℝ) : RDivisor X) P := by
              by_cases hPS : P = S₀
              · subst hPS
                have : F = S' k := Option.some.inj (hP.symm.trans (hSk k))
                subst this
                simp
              · have hFS : S' k ≠ F := fun h => hPS (hu S₀ F hP (h ▸ hSk k)).symm
                rw [Finsupp.single_eq_of_ne' hFS, Finsupp.single_eq_of_ne' (Ne.symm hPS)]
            change ((MMP.Mori.RationalMap.transformDivisor (e (N₁ + k)).toRationalMap A₀) F : ℝ) ≤
              transformSeq f fp B'X (N₁ + k) F - (Finsupp.single (S' k) (1 : ℝ) : RDivisor _) F
            rw [hcoef, hsingle, heCoeff _ P F hP B'X]
            exact hB'A P
        obtain ⟨N, hN⟩ := MMP.Fourfold.eventually_disjoint_exceptionalSet_of_realPltFlip_scaling
          (fun k => modelSeq X Y (N₁ + k)) (fun k => modelStr sX sY (N₁ + k))
          Kc Bs (fun k => divisorSeq C CY (N₁ + k))
          (fun k => W (N₁ + k)) (fun k => sW (N₁ + k)) (fun k => f (N₁ + k))
          (fun k => fp (N₁ + k)) Z sZ hZ (fun k => modelMap π πY (N₁ + k)) (fun k => g (N₁ + k))
          (fun k => modelMap_comp_eq hπ hπY _) (fun k => hfg _ (hlt _)) (fun k => hfpg _ (hlt _))
          hKc (fun k => hprojT hn _) (fun k => hYq _ (by rw [hn]; exact le_top))
          (fun k => hdim _) hflipB hpltB (fun k => hCnn _) (fun k => hCY _ (hlt _))
          (fun k => lam (N₁ + k) - ε) hlamB hantiB hnefB hupperB hcrepB S' hSB hSC hS'step
          X sX ⟨hX.toIsVariety, inferInstance⟩ hX S₀ A₀ hA₀ hA₀amp hA₀S ψ ψinv hψ hψk hψinvk hψS hord hAB
        refine ⟨N, fun k hk => ⟨fun P hP => ?_, fun P hP => ?_⟩⟩
        · rw [hS'eq] at hP
          cases hP
          exact (hN k hk).1
        · rw [hS'eq] at hP
          cases hP
          exact (hN k hk).2
      classical
      choose! M hM using hcoreS
      set F := (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).support with hF
      refine ⟨N₁ + F.sup M, fun i hi => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right N₁ _) hi)
      have hk : ∀ S ∈ F, M S ≤ k := fun S hS => (Finset.le_sup (f := M) hS).trans (by omega)
      have hmem : ∀ S, (DivisorWithCoeffs.roundDown (divisorSeq B BY N₁)).coeff S ≠ 0 →
          S ∈ F := fun S hS => Finsupp.mem_support_iff.mpr (by
        simpa only [DivisorWithCoeffs.coeff_apply] using hS)
      refine ⟨fun P hP => ?_, fun P hP => ?_⟩
      · obtain ⟨S, hS, hSk⟩ := hlift k P hP
        exact Set.disjoint_of_subset_left (exceptionalSet_subset _)
          ((hM S hS k (hk S (hmem S hS))).1 P hSk)
      · obtain ⟨S, hS, hSk⟩ := hlift (k + 1) P hP
        exact Set.disjoint_of_subset_left (exceptionalSet_subset _)
          ((hM S hS k (hk S (hmem S hS))).2 P hSk)
    obtain ⟨N, hN⟩ := hcomp
    refine ⟨N, fun i hi _ => ⟨?_, ?_⟩⟩
    · refine Set.disjoint_right.mpr fun x hx hEx => ?_
      obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
      exact Set.disjoint_left.mp ((hN i hi).1 E hE) hEx hxE
    · refine Set.disjoint_right.mpr fun x hx hEx => ?_
      obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
      exact Set.disjoint_left.mp ((hN i hi).2 E hE) hEx hxE
  have hP1 : ∀ᶠ i : ℕ in atTop, ∀ _ : (i : ℕ∞) < n,
      MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
      Disjoint (MMP.Flips.exceptionalSet (f i))
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i)) ∧
        Disjoint (MMP.Flips.exceptionalSet (fp i))
          ((DivisorWithCoeffs.roundDown (BY i)).supp : Set (Y i)) := by
    rw [eventually_atTop]
    by_cases hn : n = ⊤
    · obtain ⟨N, hN⟩ := hcore hn
      exact ⟨N, fun i hi _ hs => hN i hi hs⟩
    · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hn
      refine ⟨m, fun i hi hlt => absurd hlt ?_⟩
      exact not_lt.mpr (by exact_mod_cast hi)
  refine ⟨hP1, fun hmeet hn => ?_⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hP1
  obtain ⟨N₂, hN₂⟩ := hflipEv hn
  have hlt : ((max N₁ N₂ : ℕ) : ℕ∞) < n := by rw [hn]; exact WithTop.coe_lt_top _
  have hsmall := (hN₂ (max N₁ N₂) (le_max_right _ _)).isSmall
  obtain ⟨x, hx₁, hx₂⟩ := hmeet _ hlt hsmall
  exact Set.disjoint_left.mp (hN₁ _ (le_max_left _ _) hlt hsmall).1 hx₁ hx₂

end ErasedIntegral

end Proof_thm_fourfold_real_dlt_ample_source_special_termination

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter

namespace MMP.Fourfold

open MMP.Mori

/-- **Real dlt special termination from an ample source boundary.** Let `π : X ⟶ Z` be a
morphism of complex projective varieties with `X` a normal `ℚ`-factorial fourfold with canonical
divisor `K`, and let `B, C ≥ 0` be real divisors with `(X, B + C)` dlt and `K + B + C` nef over
`Z`, such that `B ≥ A` for an effective ample `ℚ`-divisor `A` having no component in `⌊B + C⌋`.
Let `X_i ⟶ Z_i ⟵ X_{i+1}` (`i < n`) be a `(K + B)`-program over `Z` with scaling of `C`, each step
a flip (`IsRealFlipStep`) or a divisorial contraction of a `(K_i + B_i)`-negative extremal
contraction, with ℚ-factorial models, `B_{i+1}`, `C_{i+1}` the transforms of `B_i`, `C_i`,
threshold `λ_i` the least `t ≥ 0` with `K_i + B_i + t C_i` nef over `Z`, and with
`K_i + B_i + λ_i C_i` descending crepantly to `Z_i`. Then for all sufficiently large `i`, if the
`i`-th step is small, `Ex(f_i)` is disjoint from `Supp ⌊B_i⌋` and `Ex(f_i⁺)` from
`Supp ⌊B_{i+1}⌋`; and if every small step has `Ex(f_i)` meeting `Supp ⌊B_i⌋`, then the program is
finite. -/
@[mmp "thm_fourfold_real_dlt_ample_source_special_termination"]
public theorem IsRealDltPair.eventually_disjoint_exceptionalSet_supp_roundDown_of_scaling
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : X ⟶ Z} (hπ : π ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (MMP.Flips.logCanonicalDivisor K (B + C)))
    {A : QDivisor X} (hA0 : ∀ P, 0 ≤ A.coeff P) (hA : A.IsAmple)
    (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) (hAfloor : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the scaling program
    {n : ℕ∞} {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {πY : ∀ i, Y i ⟶ Z} {KY : ∀ i, Divisor (Y i)} {BY CY : ∀ i, RDivisor (Y i)}
    {W : ℕ → Scheme.{0}} [∀ i, IsLocallyNoetherian (W i)] [∀ i, IsNormal (W i)]
    {sW : ∀ i, W i ⟶ Spec (.of ℂ)} {f : ∀ i, modelSeq X Y i ⟶ W i}
    {fp : ∀ i, Y i ⟶ W i} {g : ∀ i, W i ⟶ Z} {lam : ℕ → ℝ}
    (hπY : ∀ i, πY i ≫ sZ = sY i)
    (hfg : ∀ i : ℕ, (i : ℕ∞) < n → f i ≫ g i = modelMap π πY i)
    (hfpg : ∀ i : ℕ, (i : ℕ∞) < n → fp i ≫ g i = πY i)
    (hYq : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (modelStr sX sY i))
    (hstep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsRealFlipStep (modelStr sX sY i) (sW i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
          (KY i) (BY i) (f i) (fp i) ∨
        (AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (sW i) ∧
          MMP.Flips.IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
            (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
          IsBirationalMorphism (f i) ∧ IsProjectiveMorphism (f i) ∧
          (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
            MMP.Flips.exceptionalSet (f i) = E.support) ∧
          IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sY i) m) ∧
          BY i = flipTransform (f i) (fp i) (divisorSeq B BY i)))
    (hCY : ∀ i : ℕ, (i : ℕ∞) < n → CY i = flipTransform (f i) (fp i) (divisorSeq C CY i))
    (hthr : ∀ i : ℕ, (i : ℕ∞) < n →
      IsLeast {t : ℝ | 0 ≤ t ∧ MMP.Flips.IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B BY i + t • divisorSeq C CY i))} (lam i))
    (hdesc : ∀ i : ℕ, (i : ℕ∞) < n → ∃ D : RDivisor (W i),
      MMP.Flips.IsRCartierPullback (f i) D
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        MMP.Flips.IsRCartierPullback (fp i) D
          (flipTransform (f i) (fp i) (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)))) :
    (∀ᶠ i : ℕ in atTop, ∀ _ : (i : ℕ∞) < n, MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
      Disjoint (MMP.Flips.exceptionalSet (f i))
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i)) ∧
        Disjoint (MMP.Flips.exceptionalSet (fp i))
          ((DivisorWithCoeffs.roundDown (BY i)).supp : Set (Y i))) ∧
      ((∀ i : ℕ, (i : ℕ∞) < n → MMP.Flips.IsSmall ℂ (sW i) (modelStr sX sY i) (f i) →
        (MMP.Flips.exceptionalSet (f i) ∩
          ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i))).Nonempty)
        → n ≠ ⊤) :=
  Proof_thm_fourfold_real_dlt_ample_source_special_termination.solution hX hZ hπ hXq hK hB hC
    hdlt hnef hA0 hA hAB hAfloor hπY hfg hfpg hYq hstep hCY hthr hdesc

end MMP.Fourfold
