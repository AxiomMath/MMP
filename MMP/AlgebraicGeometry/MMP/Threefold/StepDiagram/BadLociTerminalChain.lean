module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Threefold step diagrams: bad loci, discrepancies and terminal chains

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a threefold step diagram, with bad locus `Σ ⊆ Z` (the
complement of the largest open set over which both `f⁻` and `f⁺` are isomorphisms) and bad loci
`W^± = (f^±)⁻¹(Σ)`. This file studies the geometry of `W^±` and the behaviour of log
discrepancies along the step, and applies it to stabilized tails of such steps and their
terminal chains.

A proper birational morphism onto a normal variety is an isomorphism over every point of
codimension one, the local ring there being a discrete valuation ring. Hence `W⁺` contains no
prime divisor of `X⁺`, `dim W⁺ ≤ 1`, and when `f⁻` is small also `dim W⁻ ≤ 1` and `Σ` is a
finite set of closed points. If `Σ ≠ ∅` then `dim W⁻ + dim W⁺ ≥ 2`: otherwise one of `f^±` is an
isomorphism and the relative ampleness of `-(K + B⁻)` or `K + B⁺` is violated on a contracted
curve.

For a normalized divisorial valuation `ξ`, `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`, with strict inequality
exactly when the centre of `ξ` lies in the bad locus. Off `Σ` the two pairs agree by locality of
discrepancies and crepant invariance; over `Σ` one compares the two crepant boundaries `Δ⁻`, `Δ⁺`
on a common model `W` realizing `ξ = ord_E`: `H = Δ⁻ - Δ⁺` is effective by the negativity lemma,
and if `E ⊄ Supp H` a curve in a fibre over a closed point of `Σ` would have `(H · C) = 0` and
`(H · C) < 0`. Consequences: klt and terminal pairs are preserved, lost divisors improve
strictly, decreasing the coefficients of a junction raises log discrepancies, and a label of a
terminal chain whose centre is a curve is fixed.

## Main results

* `MMP.Fourfold.IsThreefoldStepDiagram.badLocus_dimension`: `W⁺` contains no prime divisor,
  `dim W⁺ ≤ 1`, and if `f⁻` is small, `dim W⁻ ≤ 1` and `Σ` is a finite set of closed points.
* `MMP.Fourfold.IsThreefoldStepDiagram.two_le_topologicalKrullDim_badLocusMinus_add`:
  `dim W⁻ + dim W⁺ ≥ 2` when `Σ ≠ ∅`.
* `MMP.Fourfold.IsThreefoldStepDiagram.exists_irreducibleCloseds_subset_badLocusPlus`: a small
  non-isomorphic `f⁻` gives an irreducible curve in `W⁺`.
* `MMP.Fourfold.IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus`: `a⁻ < a⁺` iff
  `c_{X⁻}(ξ) ⊆ W⁻` iff `c_{X⁺}(ξ) ⊆ W⁺`.
* `MMP.Fourfold.IsThreefoldStepDiagram.lt_of_isExceptionalValuation`: lost divisors improve.
* `MMP.Fourfold.IsThreefoldStepDiagram.isKltPair_and_isKltTerminalPair_flipTransform`: klt and
  (for small `f⁻`) terminal pairs are preserved.
* `MMP.Fourfold.StabilizedTail.IsDecreasedBoundary.sub_eq_sum_and_le`: the decreased boundary of
  a junction.
* `MMP.Fourfold.StabilizedTail.TerminalChain.isFixedLabel_and_isJunctionLabelCoefficient`: a
  label with a curve centre is fixed.
* `MMP.Fourfold.transformDivisor_pullback_sub_pullback_eq_zero_of_isThreefoldStepDiagram`: the
  comparison divisor of a finite chain of threefold steps is exceptional.

## Implementation notes

Dimensions are Krull dimensions of the underlying closed subspaces (`topologicalKrullDim`, valued
in `WithBot ℕ∞`). Log discrepancies and centres of a valuation are the values satisfying
`MMP.Fourfold.IsValuationLogDiscrepancy` and `MMP.Intersection.IsCentre`, which determine them.
The source argues on the normalized graph `G` of `X⁻ ⇢ X⁺` with the graph divisor
`H = u^*(K + B⁻) - v^*(K + B⁺)`; here the same computations run on a common model realizing the
valuation at hand, and the dimension statements are proved with chains of specializations in
`W^±` rather than with upper semicontinuity of fibre dimension.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], the threefold terminal chain
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.38, 3.39
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Proper birational morphisms over points of codimension one -/

/-- Two points of `X` over the generic point of a prime divisor `Q` of the normal scheme `Y` are
equal, for `f : X ⟶ Y` separated, dominant and birational. -/
private theorem eq_of_map_eq_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f] [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (Q : MMP.Mori.PrimeDivisor Y) {x₁ x₂ : X}
    (h₁ : f x₁ = Q.genericPoint) (h₂ : f x₂ = Q.genericPoint) : x₁ = x₂ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (f x₁)) := by rw [h₁]; infer_instance
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf (h₂.trans h₁.symm)

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over the generic
point of every prime divisor: the local ring there is a discrete valuation ring, so the fibre is
a single point. -/
private theorem genericPoint_mem_biregularLocus_of_primeDivisor {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor Y) :
    P.genericPoint ∈ biregularLocus f :=
  haveI := hf.isDominant
  mem_biregularLocus_of_finite f hf (Set.Subsingleton.finite fun _ ha _ hb =>
    eq_of_map_eq_genericPoint f hf.functionFieldMap_bijective P ha hb)

/-- A proper birational morphism onto a normal variety is an isomorphism over every point of
codimension one. -/
private theorem mem_biregularLocus_of_coheight_eq_one {X Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) {z : Z} (hz : Order.coheight z = 1) : z ∈ biregularLocus f := by
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  rw [← AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hz]
  exact genericPoint_mem_biregularLocus_of_primeDivisor f hb _

/-! ### Dimensions of the bad loci -/

section BadLoci

/-- A quasi-sober subset of positive dimension of a `T₀` space contains two distinct points, one
specializing to the other. -/
private theorem exists_specializes_ne_of_topologicalKrullDim_pos {X : Type*} [TopologicalSpace X]
    [T0Space X] {F : Set X} [QuasiSober F] (h : 0 < topologicalKrullDim F) :
    ∃ a ∈ F, ∃ b ∈ F, b ⤳ a ∧ a ≠ b := by
  let _ : PartialOrder F := specializationOrder F
  have h' : 0 < Order.krullDim F := by
    rw [topologicalKrullDim] at h
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := F))]
  obtain ⟨a, b, hab⟩ := Order.krullDim_pos_iff.mp h'
  exact ⟨a, a.2, b, b.2, (show b ⤳ a from hab.le).map continuous_subtype_val,
    fun he => hab.ne (Subtype.ext he)⟩

/-- The generic point of the target lies in the biregular locus of a proper birational
morphism of varieties onto a normal variety. -/
private theorem genericPoint_mem_biregularLocus {X Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hb : IsBirationalMorphism f) :
    haveI := hZ.1.toIsIntegral
    genericPoint Z ∈ biregularLocus f := by
  haveI := hZ.1.toIsIntegral
  haveI := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hb.isDominant
  have hfin := MMP.Mori.map_genericPoint_mem_finiteFibreLocus f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  rw [MMP.Positivity.map_genericPoint_eq_of_isDominant] at hfin
  exact mem_biregularLocus_of_finite f hb hfin

/-- If the exceptional set of `f` has codimension at least two, then `f` and every proper
birational `g` onto the same normal variety are isomorphisms over the image of the generic point
of a prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {X Y Z : Scheme.{0}} [IsIntegral Y]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (g : Y ⟶ Z) [IsProper g] (hb : IsBirationalMorphism g)
    (P : AlgebraicGeometry.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f ∧ f P.genericPoint ∈ biregularLocus g := by
  have hη : P.genericPoint ∉ exceptionalSet f := fun hx => by
    have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 hx
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    exact absurd this (by decide)
  have h1 : f P.genericPoint ∈ biregularLocus f :=
    not_not.mp fun hc => hη (mem_exceptionalSet.mpr hc)
  refine ⟨h1, mem_biregularLocus_of_coheight_eq_one hZ g hb ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f h1,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]

/-- A prime divisor contains its generic point. -/
private theorem genericPoint_mem_support {X : Scheme.{u}} (P : AlgebraicGeometry.PrimeDivisor X) :
    P.genericPoint ∈ P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- In an irreducible scheme of dimension three, a closed set not containing the generic point
and containing no prime divisor contains no strict chain of three specializations. -/
private theorem false_of_chain {X : Scheme.{0}} [IrreducibleSpace X]
    (hdim : topologicalKrullDim X = 3) {W : Set X} (hW : IsClosed W) (hη : genericPoint X ∉ W)
    (hP : ∀ P : AlgebraicGeometry.PrimeDivisor X, ¬ P.support ⊆ W) (a b c : X) (ha : a ∈ W)
    (hb : b ∈ W) (hc : c ∈ W) (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b) (hbc' : b ≠ c) :
    False := by
  have hlt1 : a < genericPoint X := lt_of_le_not_ge (genericPoint_specializes a)
    (fun e => hη ((genericPoint_specializes a).antisymm e |>.eq ▸ ha))
  have hlt2 : b < a := lt_of_le_not_ge hab (fun e => hab' (hab.antisymm e).eq)
  have hlt3 : c < b := lt_of_le_not_ge hbc (fun e => hbc' (hbc.antisymm e).eq)
  have e1 := Order.coheight_add_one_le hlt1
  have e2 := Order.coheight_add_one_le hlt2
  have e3 := Order.coheight_add_one_le hlt3
  have e4 := Order.coheight_le_krullDim c
  have hX : Order.krullDim X = 3 := by
    rw [← hdim, topologicalKrullDim,
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  rw [hX] at e4
  have hc3 : Order.coheight c ≤ 3 :=
    WithBot.coe_le_coe.mp (e4 : ((Order.coheight c : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞))
  have ha1 : Order.coheight a = 1 := by
    have h1 : 1 ≤ Order.coheight a := le_trans le_add_self e1
    have h2 : Order.coheight a + 1 + 1 ≤ 3 := (add_le_add e2 le_rfl).trans (e3.trans hc3)
    generalize Order.coheight a = n at h1 h2 ⊢
    induction n using ENat.recTopCoe with
    | top => simp at h2
    | coe n => norm_cast at h1 h2 ⊢; omega
  refine hP (AlgebraicGeometry.PrimeDivisor.ofCoheightOne a ha1) ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hW.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ha)

/-- A closed subset of a scheme without strict chains of three specializations has dimension at
most one. -/
private theorem topologicalKrullDim_le_one {X : Scheme.{0}} {W : Set X} (hW : IsClosed W)
    (hchain : ∀ a b c : X, a ∈ W → b ∈ W → c ∈ W → a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False) :
    topologicalKrullDim W ≤ 1 := by
  haveI : QuasiSober W := hW.isClosedEmbedding_subtypeVal.quasiSober
  rw [topologicalKrullDim, Order.krullDim_le_one_iff]
  intro S1
  by_contra! hS
  obtain ⟨S0, h01⟩ := not_isMin_iff.mp hS.1
  obtain ⟨S2, h12⟩ := not_isMax_iff.mp hS.2
  obtain ⟨g0, hg0⟩ := QuasiSober.sober S0.isIrreducible S0.isClosed
  obtain ⟨g1, hg1⟩ := QuasiSober.sober S1.isIrreducible S1.isClosed
  obtain ⟨g2, hg2⟩ := QuasiSober.sober S2.isIrreducible S2.isClosed
  have key : ∀ {S T : IrreducibleCloseds W} {s t : W}, IsGenericPoint s S → IsGenericPoint t T →
      S < T → (t : X) ⤳ s ∧ (t : X) ≠ s := by
    intro S T s t hs ht hST
    have hle : (S : Set W) ⊆ T := hST.le
    refine ⟨(ht.specializes (hle hs.mem)).map continuous_subtype_val, fun he => ?_⟩
    obtain rfl : t = s := Subtype.ext he
    exact hST.ne (SetLike.coe_injective (hs.def.symm.trans ht.def))
  obtain ⟨h21, h21'⟩ := key hg1 hg2 h12
  obtain ⟨h10, h10'⟩ := key hg0 hg1 h01
  exact hchain g2 g1 g0 g2.2 g1.2 g0.2 h21 h10 h21' h10'

/-- A point `z` of a closed set `S` over which a proper birational `f` is not an isomorphism is
closed, if `f⁻¹(S)` contains no strict chain of three specializations. -/
private theorem isClosed_singleton_of_notMem_biregularLocus {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : AlgebraicGeometry.IsVariety ℂ sX)
    (hZ : AlgebraicGeometry.IsVariety ℂ sZ) [IsNormal Z] (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    [IsProper f] (hb : IsBirationalMorphism f) {S : Set Z} (hS : IsClosed S)
    (hchain : ∀ a b c : X, a ∈ f ⁻¹' S → b ∈ f ⁻¹' S → c ∈ f ⁻¹' S → a ⤳ b → b ⤳ c → a ≠ b →
      b ≠ c → False) {z : Z} (hzS : z ∈ S) (hz : z ∉ biregularLocus f) :
    IsClosed ({z} : Set Z) := by
  by_contra hnc
  obtain ⟨z0, hz0, hne⟩ : ∃ z0 ∈ closure ({z} : Set Z), z0 ≠ z := by
    by_contra! hall
    exact hnc (closure_subset_iff_isClosed.mp hall)
  have hpos : 0 < topologicalKrullDim (f ⁻¹' {z}) :=
    not_le.mp fun hle => hz (MMP.Fourfold.mem_biregularLocus_of_topologicalKrullDim_le hX hZ f hf
      hb hle)
  haveI : QuasiSober (f ⁻¹' {z}) := (f.fiberHomeo z).symm.isClosedEmbedding.quasiSober
  obtain ⟨b, (hb' : f b = z), a, (ha : f a = z), hab, hne'⟩ :=
    exists_specializes_ne_of_topologicalKrullDim_pos hpos
  have hcl : IsClosed (f '' closure {b}) := f.isClosedMap _ isClosed_closure
  obtain ⟨c, hc, hfc⟩ : z0 ∈ f '' closure {b} :=
    hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨b, subset_closure rfl, hb'⟩) hz0
  have hzS' : closure {z} ⊆ S := hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzS)
  refine hchain a b c (by rw [Set.mem_preimage, ha]; exact hzS)
    (by rw [Set.mem_preimage, hb']; exact hzS) (by rw [Set.mem_preimage, hfc]; exact hzS' hz0)
    hab (specializes_iff_mem_closure.mpr hc) hne'.symm (fun e => hne ?_)
  rw [← hfc, ← e, hb']

/-- A closed subset of a Noetherian quasi-sober space all of whose points are closed is
finite. -/
private theorem finite_of_forall_isClosed_singleton {Z : Type*} [TopologicalSpace Z]
    [NoetherianSpace Z] [QuasiSober Z] {S : Set Z} (hS : IsClosed S)
    (h : ∀ z ∈ S, IsClosed ({z} : Set Z)) : S.Finite := by
  obtain ⟨Zs, hZf, hZc, hZi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine hZf.sUnion fun t ht => ?_
  obtain ⟨g, hg⟩ := QuasiSober.sober (hZi t ht) (hZc t ht)
  have hgS : g ∈ ⋃₀ Zs := ⟨t, ht, hg.mem⟩
  rw [← hg.def, (h g hgS).closure_eq]
  exact Set.finite_singleton g

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Dimensions of the bad loci.** In a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, the
positive bad locus `W⁺ = badLocusPlus fm fp` contains no prime divisor of `X⁺`, and
`dim W⁺ ≤ 1`. If `f⁻` is small as well, then `dim W⁻ ≤ 1` for `W⁻ = badLocusMinus fm fp`, and
the bad locus `Σ = badLocusBase fm fp` is a finite set of closed points of `Z`. -/
@[mmp "lem_mmp_indexc_bad_loci_dimension"]
public theorem IsThreefoldStepDiagram.badLocus_dimension
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) :
    (∀ P : AlgebraicGeometry.PrimeDivisor Xp,
        ¬ (P.support : Set Xp) ⊆ (badLocusPlus fm fp : Set Xp)) ∧
      topologicalKrullDim (badLocusPlus fm fp : Set Xp) ≤ 1 ∧
      (IsSmallMorphism sXm sZ fm →
        topologicalKrullDim (badLocusMinus fm fp : Set Xm) ≤ 1 ∧
          (badLocusBase fm fp : Set Z).Finite ∧
          ∀ z ∈ (badLocusBase fm fp : Set Z), IsClosed ({z} : Set Z)) := by
  have hZ := h.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  have hXm := h.isNormalVariety_minus.1
  have hXp := h.isNormalVariety_plus.1
  have hηZ : genericPoint Z ∈ commonBiregularLocus fm fp :=
    ⟨genericPoint_mem_biregularLocus hZ fm hbm, genericPoint_mem_biregularLocus hZ fp hbp⟩
  have hηp : genericPoint Xp ∉ (badLocusPlus fm fp : Set Xp) := fun hη =>
    hη (show fp (genericPoint Xp) ∈ commonBiregularLocus fm fp from
      MMP.Positivity.map_genericPoint_eq_of_isDominant fp ▸ hηZ)
  have hηm : genericPoint Xm ∉ (badLocusMinus fm fp : Set Xm) := fun hη =>
    hη (show fm (genericPoint Xm) ∈ commonBiregularLocus fm fp from
      MMP.Positivity.map_genericPoint_eq_of_isDominant fm ▸ hηZ)
  have hnoP : ∀ P : AlgebraicGeometry.PrimeDivisor Xp,
      ¬ (P.support : Set Xp) ⊆ (badLocusPlus fm fp : Set Xp) := fun P hP =>
    have ⟨h1, h2⟩ := map_genericPoint_mem_biregularLocus hZ fp
      h.isSmallMorphism_plus.two_le_codimension fm hbm P
    hP (genericPoint_mem_support P) ⟨h2, h1⟩
  have hchainp := false_of_chain h.dim_plus (badLocusPlus fm fp).isClosed hηp hnoP
  refine ⟨hnoP, topologicalKrullDim_le_one (badLocusPlus fm fp).isClosed hchainp, fun hsm => ?_⟩
  have hnoPm : ∀ P : AlgebraicGeometry.PrimeDivisor Xm,
      ¬ (P.support : Set Xm) ⊆ (badLocusMinus fm fp : Set Xm) := fun P hP =>
    hP (genericPoint_mem_support P)
      (map_genericPoint_mem_biregularLocus hZ fm hsm.two_le_codimension fp hbp P)
  have hchainm := false_of_chain h.dim_minus (badLocusMinus fm fp).isClosed hηm hnoPm
  have hclosed : ∀ z ∈ (badLocusBase fm fp : Set Z), IsClosed ({z} : Set Z) := by
    intro z hz
    rcases not_and_or.mp hz with hz' | hz'
    · exact isClosed_singleton_of_notMem_biregularLocus hXm hZ.1 fm h.comp_eq_minus hbm
        (badLocusBase fm fp).isClosed hchainm hz hz'
    · exact isClosed_singleton_of_notMem_biregularLocus hXp hZ.1 fp h.comp_eq_plus hbp
        (badLocusBase fm fp).isClosed hchainp hz hz'
  refine ⟨topologicalKrullDim_le_one (badLocusMinus fm fp).isClosed hchainm, ?_, hclosed⟩
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsNoetherian Z := {}
  exact finite_of_forall_isClosed_singleton (badLocusBase fm fp).isClosed hclosed

end BadLoci

/-! ### The graph dimension bound -/

section GraphDimension

/-- An ample Cartier divisor `N` on `X` relative to `f` cannot have a positive multiple equal to
a multiple of a pull-back `ψ^* L` along a morphism `ψ` contracting a proper curve contracted by
`f`: the first has positive degree on the curve, the second degree zero. -/
private theorem false_of_nsmul_eq_zsmul_pullback {X Y Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (f : X ⟶ Z) (ψ : X ⟶ Y) (hψ : ψ ≫ sY = sX) (C : ProperCurve sX)
    (hCf : C.IsContractedBy f) (hCψ : C.IsContractedBy ψ)
    {N : Divisor X} (hN : N.IsCartier) (hamp : N.IsRelativelyAmple f hN)
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ T : irreducibleComponents X, ψ (componentGenericPoint X T) ∉ L.supp)
    {a : ℕ} (ha : 0 < a) (b : ℤ) (heq : (a : ℤ) • N = b • L.pullback hL hB) : False := by
  have hpos : 0 < N.degreeOn ℂ sX C.ι C.dim_le hN := by
    haveI := hN.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hamp
      C hCf
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  have hL' := hL.isCartier_pullback ψ hB
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy ψ hψ hL hB C hCψ
  have h1 := Divisor.degreeOn_zsmul' ℂ sX C.ι C.dim_le N hN a
  have h2 := Divisor.degreeOn_zsmul' ℂ sX C.ι C.dim_le _ hL' b
  rw [Divisor.degreeOn_congr heq _ (hL'.zsmul b), h2, h0, mul_zero] at h1
  have : (0 : ℤ) < a := by exact_mod_cast ha
  nlinarith

/-- A positive-dimensional fibre `f⁻¹(z)` of a morphism from a proper `k`-scheme contains a proper
curve, which `f` contracts. -/
private theorem exists_properCurve_isContractedBy {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsProper sX] [IsLocallyNoetherian X] (f : X ⟶ Z) {z : Z}
    (hz : IsClosed ({z} : Set Z)) (hpos : 0 < topologicalKrullDim (f ⁻¹' {z})) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hF : IsClosed (f ⁻¹' {z}) := hz.preimage f.continuous
  haveI : QuasiSober (f ⁻¹' {z}) := hF.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨a, haF, b, hbF, hba, hab⟩ := exists_specializes_ne_of_topologicalKrullDim_pos hpos
  obtain ⟨p, hpa, hp⟩ := (isClosed_closure (s := {a})).exists_closed_singleton
    ⟨a, subset_closure rfl⟩
  have hap : a ⤳ p := specializes_iff_mem_closure.mpr hpa
  have hbp : b ⤳ p := hba.trans hap
  have hbp' : b ∉ ({p} : Set X) := by
    rintro rfl
    have : a ∈ closure ({b} : Set X) := specializes_iff_mem_closure.mp hba
    rw [hp.closure_eq] at this
    exact hab this
  obtain ⟨y, hby, -, -, hy⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sX hbp hp hp rfl hbp'
  refine ⟨⟨y, hy⟩, fun x hx => ?_⟩
  have hsub : closure ({y} : Set X) ⊆ f ⁻¹' {z} :=
    closure_minimal (by
      rintro _ rfl
      exact (specializes_iff_mem_closure.mp hby |> closure_minimal
        (Set.singleton_subset_iff.mpr hbF) hF)) hF
  exact (hsub hx).trans (hsub (subset_closure rfl)).symm

/-! ### Coefficients of strict transforms and pull-backs -/

/-- Only `Q` has inverse transform `P`, when `f(η_P) = η_Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {X Y : Scheme.{u}} {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q Q' : MMP.Mori.PrimeDivisor Y)
    (he : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  have hs := support_inverseTransformPrimeDivisor h
  have hP : P.genericPoint ∈ (P.support : Set X) := genericPoint_mem_support P
  rw [hs] at hP
  have hcl : IsClosed (f ⁻¹' (Q'.support : Set Y)) :=
    (Q'.idealSheaf.support.isClosed).preimage f.continuous
  have hsub : (inverseTransform f Q'.idealSheaf.support : Set X) ⊆ f ⁻¹' (Q'.support : Set Y) :=
    closure_minimal (fun z hz => hz.1) hcl
  have hQ' : Q.genericPoint ∈ (Q'.support : Set Y) := he ▸ hsub hP
  have := Q'.eq_genericPoint_of_mem_support hQ' Q.coheight_genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this.symm

/-- **Coefficients of the strict transform.** If `f(η_{P⁻}) = f⁺(η_P) = η_Q` with `f⁺` an
isomorphism over `η_Q`, the coefficient of `P` in `(f⁺)⁻¹_* f_* D` is that of `P⁻` in `D`. -/
private theorem flipTransform_apply_eq {Xm Xp Z : Scheme.{u}} [IsIntegral Xm] [IsReduced Xm]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsSeparated fm]
    [IsDominant fm] (hfm : Function.Bijective (functionFieldMap fm))
    (Pm : MMP.Mori.PrimeDivisor Xm) (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
    (hm : fm Pm.genericPoint = Q.genericPoint) (hp : fp P.genericPoint = Q.genericPoint)
    (hQ : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D P = D Pm := by
  change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap D) P
    = D Pm
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hp
        (hp ▸ hQ))
      (fun Q' hQ' => eq_of_inverseTransformPrimeDivisor_eq_some P Q Q' hp hQ'),
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mpr hm)]
  intro Pm' h'
  have h'' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm' Q).mp h'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_genericPoint fm hfm Q h'' hm)

/-- The pull-back of a Cartier divisor `L = m D` along `ψ` is `m D'`, when every prime divisor `P`
of the source maps generically onto a prime divisor `P'` of the target, with an isomorphism of
local rings and `coeff_P D' = coeff_{P'} D`. -/
private theorem toQDivisor_pullback_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] (ψ : X ⟶ Y) {L : Divisor Y}
    (hL : L.IsCartier) (hB : ∀ T : irreducibleComponents X, ψ (componentGenericPoint X T) ∉ L.supp)
    {D : QDivisor Y} {D' : QDivisor X} {m : ℤ} (hLD : Divisor.toQDivisor L = m • D)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, ∃ P' : MMP.Mori.PrimeDivisor Y,
      ψ P.genericPoint = P'.genericPoint ∧ IsIso (ψ.stalkMap P.genericPoint) ∧ D' P = D P') :
    Divisor.toQDivisor (L.pullback hL hB) = m • D' := by
  ext P
  obtain ⟨P', he, hiso, hc⟩ := hcoeff P
  have h1 := MMP.Positivity.coeff_eq_of_isPullback P P' he hL (Divisor.isPullback_pullback hL hB)
  have h2 := congrArg (fun G : QDivisor Y => G P') hLD
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at h2
  rw [Divisor.coeff_toQDivisor, h1, DivisorWithCoeffs.coeff_apply (m • D'), Finsupp.smul_apply,
    zsmul_eq_mul, hc, ← h2]
  rfl

/-- Two divisors whose `ℚ`-divisors are the multiples `a D` and `b D` of one `ℚ`-divisor satisfy
`b N = a M`. -/
private theorem zsmul_eq_zsmul_of_toQDivisor_eq {X : Scheme.{u}} {N M : Divisor X}
    {D : QDivisor X} {a b : ℤ} (hN : Divisor.toQDivisor N = a • D)
    (hM : Divisor.toQDivisor M = b • D) : b • N = a • M :=
  Divisor.toQDivisor_injective (by rw [map_zsmul, map_zsmul, hN, hM, smul_comm])

/-- A scheme with a separated structure morphism to an affine scheme is separated over the
terminal scheme. -/
private theorem isSeparated_toTerminal {R : CommRingCat} {Z : Scheme.{u}} (s : Z ⟶ Spec R)
    [IsSeparated s] : IsSeparated (Z ↘ Limits.terminal Scheme) := by
  rw [Limits.terminal.hom_ext (Z ↘ _) (s ≫ (Spec R ↘ _))]
  infer_instance

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

omit [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [CompactSpace Xp]
  [IsLocallyNoetherian Xp] [IsNormal Xp] in
/-- The fibres of `f⁻` over the bad locus `Σ` lie in `W⁻`, so their dimension is at most
`dim W⁻`. -/
private theorem topologicalKrullDim_fibre_le_minus {z : Z} (hz : z ∈ badLocusBase fm fp) :
    topologicalKrullDim (fm ⁻¹' {z}) ≤ topologicalKrullDim (badLocusMinus fm fp : Set Xm) :=
  (Topology.IsEmbedding.inclusion (fun x (hx : fm x = z) =>
    show fm x ∈ badLocusBase fm fp from hx ▸ hz)).isInducing.topologicalKrullDim_le

omit [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [CompactSpace Xp]
  [IsLocallyNoetherian Xp] [IsNormal Xp] in
/-- The fibres of `f⁺` over the bad locus `Σ` lie in `W⁺`, so their dimension is at most
`dim W⁺`. -/
private theorem topologicalKrullDim_fibre_le_plus {z : Z} (hz : z ∈ badLocusBase fm fp) :
    topologicalKrullDim (fp ⁻¹' {z}) ≤ topologicalKrullDim (badLocusPlus fm fp : Set Xp) :=
  (Topology.IsEmbedding.inclusion (fun x (hx : fp x = z) =>
    show fp x ∈ badLocusBase fm fp from hx ▸ hz)).isInducing.topologicalKrullDim_le

/-- **The negative bad locus is not finite.** In a threefold step diagram with `Σ ≠ ∅`,
`dim W⁻ > 0`: otherwise `f⁻` is an isomorphism, `D⁺` is the pull-back of `D⁻` along
`(f⁻)⁻¹ ∘ f⁺`, and it has degree `0` on a curve contracted by `f⁺`, against its
`f⁺`-ampleness. -/
private theorem false_of_topologicalKrullDim_badLocusMinus_le_zero
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hbad : (badLocusBase fm fp : Set Z).Nonempty)
    (hW : topologicalKrullDim (badLocusMinus fm fp : Set Xm) ≤ 0) : False := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  haveI := hZ.2
  have hiso : IsIso fm := by
    rw [← isBiregular_top_iff, isBiregular_iff_le_biregularLocus]
    intro z _
    by_cases hz : z ∈ badLocusBase fm fp
    · exact mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_minus.1 hZ.1 fm
        h.comp_eq_minus h.isBirationalMorphism_minus
        ((topologicalKrullDim_fibre_le_minus hz).trans hW)
    · exact (not_not.mp hz).1
  obtain ⟨z, hzS, hzc⟩ := (badLocusBase fm fp).isClosed.exists_closed_singleton hbad
  have hpos : 0 < topologicalKrullDim (fp ⁻¹' {z}) :=
    (h.pos_dim_fibre_of_mem_badLocusBase hzc hzS).resolve_left
      (not_lt.mpr ((topologicalKrullDim_fibre_le_minus hzS).trans hW))
  haveI := h.isProjectiveVariety_plus
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy (sX := sXp) fp hzc hpos
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hZ.1.toIsSeparated
  haveI := isSeparated_toTerminal sZ
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective
  obtain ⟨m, hm, N, hN, hNeq, hamp⟩ := h.hasRelativelyAmpleMultiple_plus
  have hq := h.isQCartier_minus
  obtain ⟨L, hLeq, hL⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  set ψ : Xp ⟶ Xm := fp ≫ inv fm with hψdef
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' ψ L
  have hinv : inv fm ≫ sXm = sZ := by rw [IsIso.inv_comp_eq, h.comp_eq_minus]
  have hψ : ψ ≫ sXm = sXp := by rw [hψdef, Category.assoc, hinv, h.comp_eq_plus]
  have hCψ : C.IsContractedBy ψ := fun x hx => by
    rw [hψdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hkey := toQDivisor_pullback_eq ψ hL hB hLeq (D' := Divisor.toQDivisor
    (flipTransform fm fp K) + flipTransform fm fp B) fun P => by
    obtain ⟨Pm, Q, -, hQm, hQp, hQ, -, -⟩ := h.exists_primeDivisor_valuationOver_eq P
    have hm := map_genericPoint_eq_of_image_eq Pm Q hQm
    have hp := map_genericPoint_eq_of_image_eq P Q hQp
    have hpQ : fp P.genericPoint ∈ biregularLocus fp := hp ▸ hQ.2
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus fp hpQ
    refine ⟨Pm, ?_, ?_, ?_⟩
    · rw [hψdef, Scheme.Hom.comp_apply, hp, ← hm, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
    · rw [hψdef, Scheme.Hom.stalkMap_comp]
      have h1 : IsIso ((inv fm).stalkMap (fp P.genericPoint)) := inferInstance
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (MMP.isIso_stalkMap_of_mem_biregularLocus fp hpQ)
    · rw [Finsupp.add_apply, Finsupp.add_apply, ← DivisorWithCoeffs.coeff_apply,
        ← DivisorWithCoeffs.coeff_apply (Divisor.toQDivisor K), Divisor.coeff_toQDivisor,
        Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
        flipTransform_apply_eq hfm Pm P Q hm hp hQ.2, flipTransform_apply_eq hfm Pm P Q hm hp hQ.2]
  haveI := h.isNormalVariety_minus.1.toIsSeparated
  haveI := h.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI := h.isNormalVariety_minus.1.toQuasiCompact
  haveI := h.isNormalVariety_plus.1.toQuasiCompact
  exact false_of_nsmul_eq_zsmul_pullback fp ψ hψ C hC hCψ hN hamp hL hB
    (QDivisor.cartierIndex_pos hq) _ (zsmul_eq_zsmul_of_toQDivisor_eq hNeq hkey)

/-- A prime divisor of the threefold `X⁻` is a surface, so it does not lie in a closed subset of
dimension at most one: its generic point is outside `W⁻` when `dim W⁻ ≤ 1`. -/
private theorem genericPoint_notMem_badLocusMinus
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hW : topologicalKrullDim (badLocusMinus fm fp : Set Xm) ≤ 1) (P : MMP.Mori.PrimeDivisor Xm) :
    P.genericPoint ∉ (badLocusMinus fm fp : Set Xm) := by
  intro hP
  haveI := h.isNormalVariety_minus.1.toLocallyOfFiniteType
  have hsub : closure ({P.genericPoint} : Set Xm) ⊆ (badLocusMinus fm fp : Set Xm) :=
    closure_minimal (Set.singleton_subset_iff.mpr hP) (badLocusMinus fm fp).isClosed
  have hle := ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hW
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sXm P.genericPoint
  rw [P.coheight_genericPoint, h.dim_minus] at hdim
  have h2 : topologicalKrullDim (closure ({P.genericPoint} : Set Xm)) + ((1 : ℕ∞) : WithBot ℕ∞) ≤
      1 + 1 := add_le_add hle (le_of_eq WithBot.coe_one)
  rw [hdim] at h2
  exact absurd h2 (by decide)

/-- **A finite positive bad locus forces a surface in the negative one.** In a threefold step
diagram with `Σ ≠ ∅`, `dim W⁺ ≤ 0` and `dim W⁻ ≤ 1` are incompatible: then `f⁺` is an
isomorphism, no prime divisor of `X⁻` lies in `W⁻`, so `D⁻` is the pull-back of `D⁺` along
`(f⁺)⁻¹ ∘ f⁻`, of degree `0` on a curve contracted by `f⁻`, against the `f⁻`-ampleness of
`-D⁻`. -/
private theorem false_of_topologicalKrullDim_badLocusPlus_le_zero
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hbad : (badLocusBase fm fp : Set Z).Nonempty)
    (hWp : topologicalKrullDim (badLocusPlus fm fp : Set Xp) ≤ 0)
    (hWm : topologicalKrullDim (badLocusMinus fm fp : Set Xm) ≤ 1) : False := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  haveI := hZ.2
  have hiso : IsIso fp := by
    rw [← isBiregular_top_iff, isBiregular_iff_le_biregularLocus]
    intro z _
    by_cases hz : z ∈ badLocusBase fm fp
    · exact mem_biregularLocus_of_topologicalKrullDim_le h.isNormalVariety_plus.1 hZ.1 fp
        h.comp_eq_plus h.isSmallMorphism_plus.isBirationalMorphism
        ((topologicalKrullDim_fibre_le_plus hz).trans hWp)
    · exact (not_not.mp hz).2
  have hbir : biregularLocus fp = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff fp).mpr hiso))
  obtain ⟨z, hzS, hzc⟩ := (badLocusBase fm fp).isClosed.exists_closed_singleton hbad
  have hpos : 0 < topologicalKrullDim (fm ⁻¹' {z}) :=
    (h.pos_dim_fibre_of_mem_badLocusBase hzc hzS).resolve_right
      (not_lt.mpr ((topologicalKrullDim_fibre_le_plus hzS).trans hWp))
  haveI := h.isProjectiveVariety_minus
  obtain ⟨C, hC⟩ := exists_properCurve_isContractedBy (sX := sXm) fm hzc hpos
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hZ.1.toIsSeparated
  haveI := isSeparated_toTerminal sZ
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective
  obtain ⟨m, hm, N, hN, hNeq, hamp⟩ := h.hasRelativelyAmpleMultiple_minus
  have hq := h.isQCartier_plus
  obtain ⟨L, hLeq, hL⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hq
  set ψ : Xm ⟶ Xp := fm ≫ inv fp with hψdef
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' ψ L
  have hinv : inv fp ≫ sXp = sZ := by rw [IsIso.inv_comp_eq, h.comp_eq_plus]
  have hψ : ψ ≫ sXp = sXm := by rw [hψdef, Category.assoc, hinv, h.comp_eq_minus]
  have hCψ : C.IsContractedBy ψ := fun x hx => by
    rw [hψdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hkey := toQDivisor_pullback_eq ψ hL hB hLeq (D' := Divisor.toQDivisor K + B) fun Pm => by
    have hU : fm Pm.genericPoint ∈ commonBiregularLocus fm fp := by
      by_contra hn
      exact genericPoint_notMem_badLocusMinus h hWm Pm hn
    have hco : Order.coheight (fm Pm.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm hU.1]
      exact Pm.coheight_genericPoint
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco with hQdef
    have hm : fm Pm.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    have hco' : Order.coheight (inv fp Q.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (inv fp)]
      exact Q.coheight_genericPoint
    set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco' with hPdef
    have hP : P.genericPoint = inv fp Q.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco'
    have hp : fp P.genericPoint = Q.genericPoint := by
      rw [hP, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus fm hU.1
    refine ⟨P, ?_, ?_, ?_⟩
    · rw [hψdef, Scheme.Hom.comp_apply, hm]
      exact hP.symm
    · rw [hψdef, Scheme.Hom.stalkMap_comp]
      have h1 : IsIso ((inv fp).stalkMap (fm Pm.genericPoint)) := inferInstance
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (MMP.isIso_stalkMap_of_mem_biregularLocus fm hU.1)
    · have hQ : Q.genericPoint ∈ biregularLocus fp := by rw [hbir]; trivial
      rw [Finsupp.add_apply, Finsupp.add_apply, ← DivisorWithCoeffs.coeff_apply,
        ← DivisorWithCoeffs.coeff_apply (Divisor.toQDivisor (flipTransform fm fp K)),
        Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_apply, flipTransform_apply_eq hfm Pm P Q hm hp hQ,
        flipTransform_apply_eq hfm Pm P Q hm hp hQ]
  have hNeq' : Divisor.toQDivisor N = (-(m : ℤ)) • (Divisor.toQDivisor K + B) := by
    rw [hNeq, smul_neg, neg_smul]
  haveI := h.isNormalVariety_plus.1.toIsSeparated
  haveI := h.isNormalVariety_plus.1.toLocallyOfFiniteType
  haveI := h.isNormalVariety_plus.1.toQuasiCompact
  haveI := h.isNormalVariety_minus.1.toQuasiCompact
  exact false_of_nsmul_eq_zsmul_pullback fm ψ hψ C hC hCψ hN hamp hL hB
    (QDivisor.cartierIndex_pos hq) _ (zsmul_eq_zsmul_of_toQDivisor_eq hNeq' hkey)

/-- The arithmetic of the bound: in `WithBot ℕ∞`, `a > 0`, `b ≥ 0`, and `b > 0` whenever
`a ≤ 1`, give `a + b ≥ 2`. -/
private theorem two_le_add_of_not_le_zero {a b : WithBot ℕ∞} (ha : ¬ a ≤ 0) (hb : 0 ≤ b)
    (hab : a ≤ 1 → ¬ b ≤ 0) : 2 ≤ a + b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe b =>
  norm_cast at *
  induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe <;> simp_all <;>
    norm_cast at * <;> omega

/-- The positive bad locus `W⁺` is nonempty when `Σ` is, since the proper birational `f⁺` is
surjective; so `dim W⁺ ≥ 0`. -/
private theorem topologicalKrullDim_badLocusPlus_nonneg
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hbad : (badLocusBase fm fp : Set Z).Nonempty) :
    0 ≤ topologicalKrullDim (badLocusPlus fm fp : Set Xp) := by
  obtain ⟨z, hz⟩ := hbad
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hsurj : Set.range fp = Set.univ := by
    rw [← fp.isClosedMap.isClosed_range.closure_eq]; exact fp.denseRange.closure_range
  obtain ⟨x, hx⟩ : z ∈ Set.range fp := hsurj ▸ Set.mem_univ z
  let y : (badLocusPlus fm fp : Set Xp) := ⟨x, show fp x ∈ badLocusBase fm fp from hx ▸ hz⟩
  haveI : Nonempty (IrreducibleCloseds (badLocusPlus fm fp : Set Xp)) :=
    ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg
/-- **Graph dimension bound.** In a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` whose bad
locus `Σ = badLocusBase fm fp` is nonempty, the bad loci `W⁻ = badLocusMinus fm fp` and
`W⁺ = badLocusPlus fm fp` satisfy `dim W⁻ + dim W⁺ ≥ 2`. -/
@[mmp "lem_mmp_indexc_graph_dimension_bound"]
public theorem IsThreefoldStepDiagram.two_le_topologicalKrullDim_badLocusMinus_add
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hbad : (badLocusBase fm fp : Set Z).Nonempty) :
    2 ≤ topologicalKrullDim (badLocusMinus fm fp : Set Xm) +
      topologicalKrullDim (badLocusPlus fm fp : Set Xp) :=
  two_le_add_of_not_le_zero (false_of_topologicalKrullDim_badLocusMinus_le_zero h hbad)
    (topologicalKrullDim_badLocusPlus_nonneg h hbad) fun hm hp =>
    false_of_topologicalKrullDim_badLocusPlus_le_zero h hbad hp hm

end GraphDimension

/-! ### A curve in the positive bad locus -/

section PositiveCurve

private lemma eq_one_of_le_one_of_pos {x : WithBot ℕ∞} (h1 : x ≤ 1) (h0 : 0 < x) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe n => norm_cast at *; exact le_antisymm h1 (Order.one_le_iff_pos.mpr h0)

/-- A closed subset of dimension exactly one contains an irreducible closed subset of dimension
one: the image of one of its irreducible components of positive dimension. -/
private lemma exists_irreducibleCloseds_topologicalKrullDim_eq_one {X : Type*}
    [TopologicalSpace X] {W : Set X} (hW : IsClosed W) (hle : topologicalKrullDim W ≤ 1)
    (hpos : 0 < topologicalKrullDim W) :
    ∃ C : IrreducibleCloseds X, topologicalKrullDim C = 1 ∧ (C : Set X) ⊆ W := by
  obtain ⟨T, hT, hTdim⟩ : ∃ T ∈ irreducibleComponents W, 0 < topologicalKrullDim T := by
    by_contra! hall
    exact hpos.not_ge (MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents hall)
  have hCW : Subtype.val '' T ⊆ W := Subtype.coe_image_subset W T
  refine ⟨⟨_, hT.1.image _ continuous_subtype_val.continuousOn,
    hW.isClosedEmbedding_subtypeVal.isClosedMap T (isClosed_of_mem_irreducibleComponents T hT)⟩,
    eq_one_of_le_one_of_pos ?_ ?_, hCW⟩
  · exact (Topology.IsEmbedding.inclusion hCW).isInducing.topologicalKrullDim_le.trans hle
  · refine hTdim.trans_le (Topology.IsInducing.topologicalKrullDim_le
      (f := Set.codRestrict (Subtype.val ∘ Subtype.val : T → X) _ fun t => ⟨t, t.2, rfl⟩) ?_)
    exact (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).codRestrict _

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **A positive-side bad curve.** In a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with
`f⁻` small and not an isomorphism, the positive bad locus `W⁺ = badLocusPlus fm fp` contains an
irreducible curve. -/
@[mmp "lem_mmp_indexc_positive_curve_exists"]
public theorem IsThreefoldStepDiagram.exists_irreducibleCloseds_subset_badLocusPlus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    (hiso : ¬ IsIso fm) :
    ∃ C : IrreducibleCloseds Xp, topologicalKrullDim (C : Set Xp) = 1 ∧
      (C : Set Xp) ⊆ (badLocusPlus fm fp : Set Xp) := by
  -- `Σ` is nonempty, since otherwise `f⁻` is an isomorphism over all of `Z`.
  have hbad : (badLocusBase fm fp : Set Z).Nonempty := by
    by_contra hne
    refine hiso ((isBiregular_top_iff fm).mp ?_)
    rw [← top_unique fun z _ => by_contra fun hz => hne ⟨z, hz⟩]
    exact isBiregular_commonBiregularLocus_left fm fp
  obtain ⟨-, hplus, hminus⟩ := h.badLocus_dimension
  refine exists_irreducibleCloseds_topologicalKrullDim_eq_one (badLocusPlus fm fp).isClosed hplus
    (lt_of_not_ge fun h0 => ?_)
  have := (h.two_le_topologicalKrullDim_badLocusMinus_add hbad).trans
    (add_le_add (hminus hsmall).1 h0)
  norm_num at this

end PositiveCurve

/-! ### Strictness of the discrepancy comparison -/

section GraphStrict

/-! ### The common model -/

section CommonModel

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- The birational map `(f⁺)⁻¹ ∘ f⁻ : X⁻ ⤏ X⁺` of two birational morphisms to a separated
scheme is a birational map over `Z`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} [IsReduced X]
    [IsReduced X'] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom f' = f.toRationalMap := by
  obtain ⟨em, hem⟩ := hf
  obtain ⟨ep, hep⟩ := hf'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Y) hem
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep f' (𝟙 Y) hep
  set e := em.trans ep.symm with he
  have H : e.IsOver (f ≫ 𝟙 Y) (f' ≫ 𝟙 Y) := h1.trans h2.symm
  have H' : e.iso.hom ≫ e.target.ι ≫ f' = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using H
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H']
  simp

/-- **A common model realizing `ξ`.** For a threefold step diagram and a divisor `D` over `X⁻`
there is a normal variety `W` with proper birational morphisms `g : W ⟶ X⁻`, `g' : W ⟶ X⁺`,
`g ≫ f⁻ = g' ≫ f⁺`, and a prime divisor `E` of `W` with `ord_E` the valuation of `D`. -/
private theorem exists_commonModel {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (D : DivisorOver ℂ sXm) :
    ∃ (W : Scheme.{0}) (g : W ⟶ Xm) (g' : W ⟶ Xp) (hW : IsNormalVariety ℂ (g ≫ sXm))
      (hg : IsBirationalMorphism g), IsProper g ∧ IsProper g' ∧ IsBirationalMorphism g' ∧
      g ≫ fm = g' ≫ fp ∧ ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation = D.valuation := by
  have : IsSeparated sZ := h.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal sZ
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq h.isBirationalMorphism_minus
    h.isSmallMorphism_plus.isBirationalMorphism
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  obtain ⟨W, g, g', hW, hg, hgp, hg'p, hg', -, hcomm, P, hP⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
      h.isNormalVariety_minus h.isNormalVariety_plus fm fp φ hφ hφS D
  exact ⟨W, g, g', hW, hg, hgp, hg'p, hg', hcomm, P, hP⟩

end CommonModel

/-! ### Forms and orders over the base -/

section Forms

/-- Over the biregular locus of `f`, specialization lifts along `f`. -/
private theorem specializes_of_mem_biregularLocus {X Y : Scheme.{0}} (f : Y ⟶ X) {p x : Y}
    (hp : f p ∈ biregularLocus f) (hx : f x ∈ biregularLocus f) (h : f p ⤳ f x) : p ⤳ x := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p' : (f ⁻¹ᵁ V).toScheme := ⟨p, hp⟩
  let x' : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  have h1 : (f ∣_ V) p' ⤳ (f ∣_ V) x' := by
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff]
    change ((f ∣_ V) p').1 ⤳ ((f ∣_ V) x').1
    rwa [morphismRestrict_base_coe, morphismRestrict_base_coe]
  exact (((f ∣_ V).isOpenEmbedding.isInducing.specializes_iff).mp h1).map
    (f ⁻¹ᵁ V).ι.continuous

/-- The inverse transform under `f` of the prime divisor `Q`, when `f` is an isomorphism over
`η_Q = f(η_P)`, is `P`: the coefficient of `P` in `f⁻¹_* D` is the coefficient of `Q` in `D`. -/
private theorem inverseTransformDivisor_apply_eq {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (f : Y ⟶ X) (P : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X)
    (heq : f P.genericPoint = Q.genericPoint) (hQ : Q.genericPoint ∈ biregularLocus f)
    (D : DivisorWithCoeffs R X) : inverseTransformDivisor f D P = D Q := by
  set V := biregularLocus f
  have hmem : ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ E.support :=
    genericPoint_mem_support
  have hPV : f P.genericPoint ∈ V := heq ▸ hQ
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq ?_ (fun E' hE' => ?_) D
  · refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨_, hmem Q, hQ⟩, ?_⟩
    have hT : inverseTransform f Q.idealSheaf.support = P.idealSheaf.support := by
      apply SetLike.coe_injective
      change closure (f ⁻¹' ((Q.support : Set X) ∩ V)) = P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure P]
      refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
      · rintro x ⟨hxQ, hxV⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxQ
        rw [← specializes_iff_mem_closure]
        refine specializes_of_mem_biregularLocus f hPV hxV ?_
        rw [heq]
        exact specializes_iff_mem_closure.mpr hxQ
      · rw [Set.singleton_subset_iff]
        exact ⟨heq ▸ hmem Q, hPV⟩
    have := P.integral
    rw [inverseTransformIdeal, hT, MMP.Positivity.vanishingIdeal_support_of_isReduced]
  · obtain ⟨hne, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hE'
    have hE'V : E'.genericPoint ∈ V :=
      MMP.Intersection.genericPoint_mem_of_support_inter_nonempty E' hne
    have hsupp := support_inverseTransformPrimeDivisor hE'
    change P.support = closure (f ⁻¹' ((E'.support : Set X) ∩ V)) at hsupp
    have h1 : E'.genericPoint ⤳ Q.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← heq]
      have hP : P.genericPoint ∈ closure (f ⁻¹' ((E'.support : Set X) ∩ V)) :=
        hsupp ▸ genericPoint_mem_support P
      have := image_closure_subset_closure_image (f := f) f.continuous ⟨_, hP, rfl⟩
      refine closure_minimal ?_ (E'.idealSheaf.support.isClosed) this
      rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
    obtain ⟨q, hq⟩ := (f ∣_ V).surjective ⟨E'.genericPoint, hE'V⟩
    have hq' : f q.1 = E'.genericPoint := by
      rw [← morphismRestrict_base_coe, hq]
    have h2 : Q.genericPoint ⤳ E'.genericPoint := by
      have hqP : q.1 ∈ P.support := by
        rw [hsupp]
        exact subset_closure ⟨hq' ▸ hmem E', hq' ▸ hE'V⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
        at hqP
      rw [← heq, ← hq']
      exact hqP.map f.continuous
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.antisymm h2).eq

variable {k : Type} [Field k] [PerfectField k]

/-- Along a morphism `f` inducing an isomorphism of function fields, every rational pluri-form
is a pull-back: `τ = f^*σ`, with `σ ≠ 0` when `τ ≠ 0`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms (f ≫ sY) d m) :
    ∃ σ : RationalPluriForms sY d m, pullbackRationalPluriForms sY f σ = τ ∧
      (τ ≠ 0 → σ ≠ 0) := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  set bY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m with hbY
  set bX := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m with hbX
  obtain ⟨c, hc⟩ := hf.2 (bX.repr τ ())
  have hpull : pullbackRationalPluriForms sY f (c • bY ()) = τ := by
    change pullbackForms m (c • bY ()) = τ
    rw [pullbackForms_eq hω m]
    apply bX.ext_elem
    intro i
    obtain rfl : i = () := rfl
    rw [repr_pullbackFormsAlong hω m]
    simp only [bY, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact hc
  refine ⟨c • bY (), hpull, fun hτ hσ => hτ ?_⟩
  rw [← hpull, hσ]
  change pullbackForms m 0 = 0
  rw [pullbackForms_eq hω m]
  simp [pullbackFormsAlong]

/-- **Orders of pulled-back forms along a composite.** For `g : W ⟶ X` and a birational
`f : X ⟶ Y`, the order along `(W, g, F)` over `X` of `f^*σ` is the order along
`(W, g ≫ f, F)` over `Y` of `σ`. -/
private theorem ordPullback_pullbackRationalPluriForms {X Y W : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    [LocallyOfFiniteType (f ≫ sY)] (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    {g : W ⟶ X} (hW : IsNormalVariety k (g ≫ f ≫ sY)) (hg : IsBirationalMorphism g)
    (hgf : IsBirationalMorphism (g ≫ f)) (F : MMP.Mori.PrimeDivisor W) {m : ℤ}
    (σ : RationalPluriForms sY d m) :
    (⟨W, g, hW, hg, F⟩ : DivisorOver k (f ≫ sY)).ordPullback
        (pullbackRationalPluriForms sY f σ) =
      (⟨W, g ≫ f, hW, hgf, F⟩ : DivisorOver k sY).ordPullback σ := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant g := hg.isDominant
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ f ≫ sY)
  change F.ordForm (pullbackRationalPluriForms (f ≫ sY) g (pullbackRationalPluriForms sY f σ)) =
    F.ordForm (pullbackRationalPluriForms sY (g ≫ f) σ)
  rw [MMP.Flips.pullbackRationalPluriForms_comp f g hf.functionFieldMap_bijective
    hg.functionFieldMap_bijective hd σ]
  rfl

/-- **Comparing two forms along a divisor over `X`.** If `m'·ord_Γ(τ) = m·ord_Γ(τ')` along every
prime divisor `Γ` through `f(η_E)`, then `m'·ord_E(f^*τ) = m·ord_E(f^*τ')`: the ratio
`τ^{⊗m'} / τ'^{⊗m}` is a unit at `f(η_E)` by algebraic Hartogs. -/
private theorem mul_ordPullback_eq_of_forall {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) (D : DivisorOver k sX) {m m' : ℤ}
    {τ : RationalPluriForms sX n m} {τ' : RationalPluriForms sX n m'} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0)
    (hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (m' : ℚ) * Γ.ordForm τ = m * Γ.ordForm τ') :
    (m' : ℚ) * D.ordPullback τ = m * D.ordPullback τ' := by
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  set g : X.functionField := c ^ m' * c' ^ (-m) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord' : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'
    have e := hord Γ hΓ
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination e - (m' : ℚ) * f1 + (m : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord'
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) = 0 := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'
  linear_combination (m' : ℚ) * h1 - (m : ℚ) * h2 + hY0'

end Forms

/-! ### Intersection numbers along curves -/

section IntersectionNumbers

section Intersection

open MMP.Flips

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
  have := C.isCurve
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

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
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

end Intersection

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] in
/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
private theorem coeff_pullback_eq {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK Γ, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
  have hCq : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hE
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgen : GeneratesOn B m V τ := by
    refine ⟨hτ0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, h1, h2⟩ := hKcoeff Γ
    have h3 := hgord Γ hΓ
    qify at h1 h2 h3
    linear_combination h2 - hCq Γ - h3 - (m : ℚ) * h1
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, h]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ, hgen, ?_⟩
    qify at hordτ hKY hcoeff
    rw [hordτ, hKY, hcoeff]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

omit [CompactSpace X] in
/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
private theorem isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp) :
    (Divisor.toQDivisor K + B).IsPullback p hLB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + Δ) := by
  intro m hm D hD hDc
  have hB' : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp :=
    fun Z hZ => hLB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  refine ⟨D.pullback hDc hB', ?_, Divisor.isPullback_pullback hDc hB'⟩
  ext F
  have h := coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc
    (Divisor.isPullback_pullback hDc hB') hω0 hωK F
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  exact h

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers of `K + Δ` along a curve depend on `K` only up to linear equivalence. -/
private theorem intersectionNumber_add_eq_of_linearlyEquivalent [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {K₁ K₂ : Divisor X}
    (h : K₁.LinearlyEquivalent K₂) (Δ : QDivisor X) (h₁ : (Divisor.toQDivisor K₁ + Δ).IsQCartier)
    (h₂ : (Divisor.toQDivisor K₂ + Δ).IsQCartier) :
    (Divisor.toQDivisor K₁ + Δ).intersectionNumber k sX i hdim h₁ =
      (Divisor.toQDivisor K₂ + Δ).intersectionNumber k sX i hdim h₂ := by
  obtain ⟨D', hD', hD'c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul h₂
  set m := (Divisor.toQDivisor K₂ + Δ).cartierIndex h₂
  have hm := QDivisor.cartierIndex_pos h₂
  obtain ⟨φ, hφ⟩ := h
  set a : Additive (RationalFunctions X)ˣ := (m : ℤ) • Additive.ofMul φ with ha
  set G := D' + principalDivisorHom a with hG_def
  have hGc : G.IsCartier := hD'c.add (Divisor.isCartier_principalDivisor _)
  have hG : Divisor.toQDivisor G = (m : ℤ) • (Divisor.toQDivisor K₁ + Δ) := by
    have e : principalDivisorHom a = (m : ℤ) • (K₁ - K₂) := by
      rw [ha, map_zsmul, principalDivisorHom_apply, toMul_ofMul, hφ]
    rw [hG_def, e, map_add, hD', map_zsmul, map_sub, ← smul_add]
    congr 1
    abel
  have hGD : G.LinearlyEquivalent D' := ⟨a.toMul, by
    rw [hG_def, add_sub_cancel_left, principalDivisorHom_apply]⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₁ hm G hGc hG,
    QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ h₂ hm D' hD'c hD']
  congr 2
  have := hGc.isInvertibleModule_divisorialSheaf
  have := hD'c.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sX i hdim hGD.divisorialSheafIso

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- Two closed subschemes cut out by equal ideal sheaves are isomorphic over `X`. -/
private theorem exists_iso_subscheme_of_eq {I J : X.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

end Curves

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- The negative of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨m, hm, hC⟩ := hD
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, smul_neg, neg_neg]⟩

/-- `((-D) · C) = -(D · C)`. -/
private theorem intersectionNumber_neg (k : Type u) [Field k] {X C : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {D : QDivisor X}
    (hD : D.IsQCartier) (hD' : (-D).IsQCartier) :
    (-D).intersectionNumber k sX i hdim hD' = -(D.intersectionNumber k sX i hdim hD) := by
  have hadd := QDivisor.intersectionNumber_add' k sX i hdim D (-D) hD hD'
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  have h00 : (0 : QDivisor X).intersectionNumber k sX i hdim QDivisor.isQCartier_zero = 0 := by
    have := QDivisor.intersectionNumber_add' k sX i hdim (0 : QDivisor X) 0
      QDivisor.isQCartier_zero QDivisor.isQCartier_zero (by simpa using QDivisor.isQCartier_zero)
    simp only [add_zero] at this
    linarith
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ QDivisor.isQCartier_zero (add_neg_cancel D),
    h00] at hadd
  linarith

/-- **Projection onto the image curve.** Let `L' = u^*L` be the pull-back of a `ℚ`-Cartier
`ℚ`-divisor along a proper morphism `u : V ⟶ W` of normal varieties and `C ⊆ V` a proper curve
whose image `u(C)` is not a point. Then `u(C)` is a proper curve `C''` of `W` with generic point
`u(η_C)`, and `(L' · C) = d (L · C'')` with `d = [k(C) : k(C'')] > 0`. -/
private theorem exists_intersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) {L : QDivisor W} (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hpt : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w}) :
    ∃ C'' : ProperCurve sW, C''.point = u C.point ∧ ∃ d : ℚ, 0 < d ∧
      L'.intersectionNumber k sV C.ι C.dim_le hL' =
        d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  set φ := C.ι ≫ u with hφ
  have : AlgebraicGeometry.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
  have hcurve := isCurve_imageι_comp sW φ hpt
  have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hL h hcurve
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq (C.ker_comp (f := u))
  have : IsProper φ := IsProper.of_comp φ sW
  have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
  have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
      hcurve.topologicalKrullDim_eq_one
  have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := by
    rwa [Iso.eq_inv_comp]
  have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
    rw [hι, Category.assoc]; infer_instance
  let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
  have hφs : φ.toImage ≫ φ.imageι ≫ sW = C.ι ≫ sV := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hφ, Category.assoc, hu]
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι ≫ sW) := by
      rw [hφs]; infer_instance
    exact locallyOfFiniteType_of_comp φ.toImage (φ.imageι ≫ sW)
  have hnc : ¬ ∃ y : φ.image, ∀ x : C.scheme, φ.toImage.base x = y := by
    rintro ⟨y, hy⟩
    have hφy : ∀ x, φ x = φ.imageι y := fun x => by
      calc φ x = (φ.toImage ≫ φ.imageι) x := by rw [Scheme.Hom.toImage_imageι]
        _ = φ.imageι y := by rw [Scheme.Hom.comp_apply, hy x]
    obtain ⟨x⟩ : Nonempty C.scheme := inferInstance
    exact hpt ⟨φ.imageι y, Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨x, hφy x⟩, by rintro _ ⟨x, rfl⟩; exact hφy x⟩⟩
  have hdeg : 0 < degreeOver φ.toImage :=
    degreeOver_pos_of_not_constant k (C.ι ≫ sV) (φ.imageι ≫ sW) φ.toImage hφs hnc
  refine ⟨C'', rfl, (degreeOver φ.toImage : ℚ), by exact_mod_cast hdeg, key.trans ?_⟩
  rw [intersectionNumber_eq_of_iso_comp sW φ.imageι C''.ι _ C''.dim_le e he _ hL]

/-- **Projection of a contracted curve.** With `L' = u^*L` as in
`exists_intersectionNumber_pullback_eq_mul` and `C ⊆ V` a proper curve contracted by `u ≫ f`,
either `(L' · C) = 0` (when `u(C)` is a point), or `(L' · C) = d (L · u(C))` with `d ≥ 0`, where
`u(C)` is a proper curve of `W` contracted by `f`. -/
private theorem intersectionNumber_pullback_eq_zero_or {k : Type u} [Field k]
    {V W Y : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (f : W ⟶ Y) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (hC : C.IsContractedBy (u ≫ f)) :
    L'.intersectionNumber k sV C.ι C.dim_le hL' = 0 ∨
      ∃ d : ℚ, 0 ≤ d ∧ ∃ C'' : ProperCurve sW, C''.IsContractedBy f ∧
        L'.intersectionNumber k sV C.ι C.dim_le hL' =
          d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have := C.isCurve
  by_cases hpt : ∃ w : W, Set.range (C.ι ≫ u) = {w}
  · exact .inl (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hL h hpt)
  obtain ⟨C'', hC''u, d, hd, heq⟩ :=
    exists_intersectionNumber_pullback_eq_mul u hu hL h hL' C hpt
  refine .inr ⟨d, hd.le, C'', fun x hx => ?_, heq⟩
  have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
    (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
      rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
  rw [hC''u] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hsub hx
  simpa only [Scheme.Hom.comp_apply] using hC z hz

/-- An exceptional prime divisor of a morphism maps its generic point to a point of coheight at
least two. -/
private theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} (E : MMP.Mori.PrimeDivisor Y)
    (hE : RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  set η := E.genericPoint
  have hdef : RationalMap.DefinedAt (X := Y) f.toRationalMap η := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hsub : (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) : Set X) ⊆
      (RationalMap.transform (X := Y) f.toRationalMap E.idealSheaf.support : Set X) := by
    rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton]
    refine (TopologicalSpace.Closeds.isClosed _).closure_subset_iff.mpr ?_
    rintro _ rfl
    refine RationalMap.image_subset_transform f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨η, ?_, rfl⟩
    exact genericPoint_mem_support E
  have hle := le_closedsCodimension_iff.mp h2 _ hsub
  have hcodim : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton (f η)) =
      Order.coheight (f η) := by
    have h : TopologicalSpace.IrreducibleCloseds.closureSingleton (f η) =
        irreducibleSetEquivPoints.symm (f η) :=
      TopologicalSpace.IrreducibleCloseds.ext (by
        rw [TopologicalSpace.IrreducibleCloseds.coe_closureSingleton,
          coe_irreducibleEquivPoints_symm_apply])
    rw [codimension_eq_coheight, h]
    exact Order.coheight_orderIso irreducibleSetEquivPoints.symm (f η)
  rwa [hcodim] at hle

end IntersectionNumbers

/-! ### Positivity, negativity and the projection formula -/

section Negativity

/-- A prime divisor exceptional over `X` is exceptional in the sense of the dimension of its
centre: `dim c_X(E) + 2 ≤ dim X`. -/
private theorem isExceptionalPrimeDivisor_of_isExceptional {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [hp : IsProper f]
    (E : MMP.Mori.PrimeDivisor Y)
    (hE : MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    MMP.Flips.IsExceptionalPrimeDivisor sX f E := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  refine ⟨hY, hf, hp, ?_⟩
  have h2 := two_le_coheight_of_isExceptional E hE
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint]
  rw [← MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (f E.genericPoint)]
  gcongr
  have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (f E.genericPoint) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h2
  exact le_of_eq_of_le (by norm_cast) h2'

/-- A `ℚ`-divisor with a relatively ample multiple is positive on every contracted curve. -/
private theorem intersectionNumber_pos_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (hA : D.HasRelativelyAmpleMultiple f) (hD : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 < D.intersectionNumber k sX C.ι C.dim_le hD := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := hA
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hm L hL hLD]
  have := hL.isInvertibleModule_divisorialSheaf
  have h : 0 < L.degreeOn k sX C.ι C.dim_le hL :=
    MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC
  have h' : (0 : ℚ) < L.degreeOn k sX C.ι C.dim_le hL := by exact_mod_cast h
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  positivity

/-- **The negativity lemma for `ℚ`-Cartier divisors.** Let `f : Y ⟶ X` be a proper birational
morphism of normal varieties and `B` a `ℚ`-Cartier divisor on `Y` with `(B · C) ≤ 0` on every
curve contracted by `f`, whose coefficients along the prime divisors not exceptional over `X` are
nonnegative. Then `B` is effective. -/
private theorem nonneg_of_intersectionNumber_nonpos {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f]
    (hfb : IsBirationalMorphism f) {B : QDivisor Y} (hB : B.IsQCartier)
    (hnef : ∀ C : ProperCurve sY, C.IsContractedBy f →
      B.intersectionNumber k sY C.ι C.dim_le hB ≤ 0)
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ B.coeff P) :
    0 ≤ B := by
  obtain ⟨E, hEB, hEc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hB
  have hm : 0 < B.cartierIndex hB := QDivisor.cartierIndex_pos hB
  set m := B.cartierIndex hB with hm_def
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set BR := QDivisor.toRDivisor B with hBR
  have hBRE : BR = ((1 : ℝ) / m) • Divisor.toRDivisor E := by
    ext P
    have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hEB
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    change (QDivisor.toRDivisor B).coeff P = (((1 : ℝ) / m) • Divisor.toRDivisor E).coeff P
    rw [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    have h2 : ((E.coeff P : ℚ) : ℝ) = ((m * B.coeff P : ℚ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2]
    field_simp
  have hL0 : MMP.Flips.IsCartierCombination (0 : RDivisor X) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpb0 : MMP.Flips.IsRCartierPullback f (0 : RDivisor X) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hBRc : MMP.Flips.IsCartierCombination BR :=
    ⟨1, fun _ => 1 / (m : ℝ), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs]
      exact hBRE⟩
  have hMc : MMP.Flips.IsCartierCombination (-BR) :=
    ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, by
      rw [Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs, hBRE, neg_smul]⟩
  have hpres : -BR = ∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j •
      Divisor.toRDivisor ((fun _ => E) j) := by
    rw [Fin.sum_univ_one, hBRE, neg_smul]
  have hMnef : MMP.Flips.IsRelativelyNef k sY f (-BR) := by
    refine ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => E, fun _ => hEc, hpres, fun C hC x hx => ?_⟩
    have hx₀ : MMP.Flips.IsRIntersectionNumber k sY (-BR) (fun _ => -(1 / (m : ℝ)))
        (fun _ => E) C (∑ j : Fin 1, (fun _ => -(1 / (m : ℝ))) j *
          ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ)) :=
      ⟨fun _ => hEc, fun _ => E.degreeOn k sY C.ι C.dim_le hEc, hpres,
        fun _ => isCartierIntersectionNumber_degreeOn k sY C E hEc, rfl⟩
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hx₀,
      Fin.sum_univ_one]
    have hI := hnef C hC
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le B hB hm E hEc hEB] at hI
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have hdeg : (E.degreeOn k sY C.ι C.dim_le hEc : ℚ) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hmq.le hI
      rwa [mul_div_cancel₀ _ hmq.ne'] at this
    have hdeg' : ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hdeg
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have : 0 ≤ -(1 / (m : ℝ)) * ((E.degreeOn k sY C.ι C.dim_le hEc : ℤ) : ℝ) := by
      rw [neg_mul]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hdeg')
    exact this
  have hBG' : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      0 ≤ BR.coeff P := fun P hP => by
    rw [hBR, QDivisor.coeff_toRDivisor]
    exact_mod_cast hBG P hP
  have hnum : MMP.Flips.IsNumericallyEquivalentOver k sY f (0 : RDivisor Y) (-BR + BR) := by
    refine ⟨⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, by
      rw [neg_add_cancel]; exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    rw [neg_add_cancel] at h₂
    exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ h₁ h₂
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback k sX sY hX hY f hf
    hfb hL0 hpb0 hMc hMnef hBRc hBG' hnum
  refine Finsupp.le_def.mpr fun P => ?_
  have hP := heff P
  rw [hBR, QDivisor.coeff_toRDivisor] at hP
  change (0 : ℚ) ≤ B.coeff P
  exact_mod_cast hP

end Negativity

/-! ### The difference of the crepant boundaries -/

section CrepantDifference

variable {k : Type u} [Field k] [PerfectField k]

/-- **Projection of a curve onto a curve.** If `u` maps the proper curve `C` onto the proper curve
`C''`, then `(u^*L · C) = d (L · C'')` with `d = [k(C) : k(C'')] > 0`. -/
private theorem intersectionNumber_pullback_eq_mul_of_image
    {V W : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') (hL' : L'.IsQCartier) (C : ProperCurve sV)
    (C'' : ProperCurve sW) (hCC : u '' closure {C.point} = closure {C''.point}) :
    ∃ d : ℚ, 0 < d ∧ L'.intersectionNumber k sV C.ι C.dim_le hL' =
      d * L.intersectionNumber k sW C''.ι C''.dim_le hL := by
  have hcl : closure {u C.point} = closure {C''.point} := by
    rw [← hCC, ← Set.image_singleton, u.isClosedMap.closure_image_eq_of_continuous u.continuous]
  have hpt' : u C.point = C''.point :=
    ((specializes_iff_closure_subset.mpr hcl.ge).antisymm
      (specializes_iff_closure_subset.mpr hcl.le)).eq
  have hpt : ¬ ∃ w : W, Set.range (C.ι ≫ u) = {w} := by
    rintro ⟨w, hw⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι, hCC] at hw
    have hr := C''.range_ι
    rw [hw] at hr
    have : Subsingleton C''.scheme := ⟨fun a b => C''.ι.isEmbedding.injective (by
      have ha : C''.ι a ∈ ({w} : Set W) := hr ▸ ⟨a, rfl⟩
      have hb : C''.ι b ∈ ({w} : Set W) := hr ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C''.scheme
    rw [C''.dim_eq] at h0
    exact absurd h0 (by decide)
  obtain ⟨C₁, hC₁, hd⟩ := exists_intersectionNumber_pullback_eq_mul u hu hL h hL' C hpt
  obtain rfl : C₁ = C'' := ProperCurve.ext (hC₁.trans hpt')
  exact hd

/-- **The difference of two crepant boundaries along curves.** With `K_Z = div(g^*ω)`, crepancy
`K_Z + Δ_Z = g^*(K_X + Δ)` and `K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')` with `K'_Z ∼ K_Z` give
`((Δ_Z - Δ'_Z) · C) = (g^*(K_X + Δ) · C) - (g'^*(K_{X'} + Δ') · C)` for every curve `C`. -/
private theorem exists_intersectionNumber_sub_eq {n : ℕ} {X X' Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hQ : (Divisor.toQDivisor KX + Δ).IsQCartier)
    (hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier)
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hsZ : g' ≫ sX' = g ≫ sX)
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') :
    haveI : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
    ∃ (hH : (ΔZ - ΔZ').IsQCartier) (L L' : QDivisor Z)
      (hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX + Δ).supp)
      (hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
        (Divisor.toQDivisor KX' + Δ').supp)
      (_ : (Divisor.toQDivisor KX + Δ).IsPullback g hLB L)
      (_ : (Divisor.toQDivisor KX' + Δ').IsPullback g' hLB' L')
      (hLq : L.IsQCartier) (hLq' : L'.IsQCartier),
      ∀ C : ProperCurve (g ≫ sX), (ΔZ - ΔZ').intersectionNumber k (g ≫ sX) C.ι C.dim_le hH =
        L.intersectionNumber k (g ≫ sX) C.ι C.dim_le hLq -
          L'.intersectionNumber k (g ≫ sX) C.ι C.dim_le hLq' := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (g ≫ sX) := hZ.1
  have hnZ : topologicalKrullDim Z = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg, hK.1]
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω', hω0', hωK'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX' hK'
  have hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX + Δ).supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX' + Δ').supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω) with hKZ
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω') with hKZ'
  have hpb := isPullback_divisorOfForm_add hX hZ hg hK hΔZ hω0 hωK hLB
  have hpb' := isPullback_divisorOfForm_add hX' hZ' hg' hK' hΔZ' hω0' hωK' hLB'
  have hB := hpb.isQCartier hQ
  have hA := hpb'.isQCartier hQ'
  have hne : pullbackRationalPluriForms sX g ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hg hK.1 hω0
  have hlin : KZ'.LinearlyEquivalent KZ := by
    have key : ∀ (s : Z ⟶ Spec (.of k)) (_ : s = g ≫ sX) [LocallyOfFiniteType s]
        (τ : RationalPluriForms s n 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent KZ := by
      rintro s rfl _ τ hτ
      exact linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ (pullbackRationalPluriForms_ne_zero hX' hg' hK'.1 hω0')
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ')).IsQCartier := isQCartier_neg hA2
  have hH : ΔZ - ΔZ' = (Divisor.toQDivisor KZ + ΔZ) + -(Divisor.toQDivisor KZ + ΔZ') := by abel
  have hHq : (ΔZ - ΔZ').IsQCartier := hH ▸ hB.add hBn
  refine ⟨hHq, _, _, hLB, hLB', hpb, hpb', hB, hA, fun C => ?_⟩
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hB.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hB hBn,
    intersectionNumber_neg k _ C.ι C.dim_le hA2 hBn,
    ← intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin ΔZ' hA hA2]
  ring

end CrepantDifference

/-! ### The comparison of discrepancies -/

section Comparison

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- A proper curve lying in a fibre of `f` is contracted by `f`. -/
private theorem isContractedBy_of_subset_preimage {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y} {C : ProperCurve sX} {y : Y}
    (hC : closure {C.point} ⊆ f ⁻¹' {y}) : C.IsContractedBy f :=
  fun _ hx => (hC hx).trans (hC (subset_closure rfl)).symm

/-- **A curve in a positive-dimensional fibre.** Let `f : X ⟶ Z` be a proper birational morphism
of varieties with `f_* 𝒪_X = 𝒪_Z`, and `x ∈ X` a closed point. If `f` is not an isomorphism
over `f(x)`, then the fibre `f⁻¹(f(x))` contains a proper curve. -/
private theorem exists_properCurve_subset_fibre {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [IsProper sX] [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.IsVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (hfs : f ≫ sZ = sX) [IsProper f] (hfb : IsBirationalMorphism f)
    (hO : ∀ U : Z.Opens, IsIso (f.app U)) {x : X} (hx : IsClosed ({x} : Set X))
    (hxb : f x ∉ biregularLocus f) :
    ∃ C : ProperCurve sX, closure {C.point} ⊆ f ⁻¹' {f x} := by
  obtain ⟨C₀, hC₀c, hC₀i, hC₀d, hxC₀, y', hy'⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hX hZ.1 f hfs
      hfb hO hx (mem_exceptionalSet.mpr hxb)
  have hy'x : f '' C₀ = {f x} := by
    rw [hy', Set.singleton_eq_singleton_iff]
    exact (hy' ▸ Set.mem_image_of_mem f hxC₀ : f x ∈ ({y'} : Set Z)).symm
  obtain ⟨η₀, hη₀⟩ := QuasiSober.sober hC₀i hC₀c
  have hη₀ne : η₀ ∉ ({x} : Set X) := by
    intro hη
    rw [← hη₀.def, Set.mem_singleton_iff.mp hη, hx.closure_eq] at hC₀d
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set X)
    rw [hC₀d] at h0
    exact absurd h0 (by decide)
  obtain ⟨y₁, hη₀y₁, -, -, hy₁⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sX (hη₀.specializes hxC₀) hx hx rfl hη₀ne
  have hcl₁ : closure {y₁} ⊆ C₀ := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hC₀c
    rw [← hη₀.def]
    exact specializes_iff_mem_closure.mp hη₀y₁
  exact ⟨⟨y₁, hy₁⟩, fun x' hx' => hy'x ▸ Set.mem_image_of_mem f (hcl₁ hx')⟩

/-- **Lifting a curve of a fibre.** Along a proper dominant morphism `u : W ⟶ X` of varieties, a
proper curve `C'` of `X` inside the fibre `f⁻¹(y)` is the image of a proper curve `C` of `W`
inside `(u ≫ f)⁻¹(y)`. -/
private theorem exists_properCurve_image_eq_subset_fibre {W X Y : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} (hW : AlgebraicGeometry.IsVariety ℂ sW)
    (hX : AlgebraicGeometry.IsVariety ℂ sX) (u : W ⟶ X) (hu : u ≫ sX = sW) [IsProper u]
    [IsDominant u] (f : X ⟶ Y) {y : Y} (C' : ProperCurve sX)
    (hC' : closure {C'.point} ⊆ f ⁻¹' {y}) :
    ∃ C : ProperCurve sW, u '' closure {C.point} = closure {C'.point} ∧
      closure {C.point} ⊆ (u ≫ f) ⁻¹' {y} := by
  have : Surjective u := ⟨fun t => by
    rw [← Set.mem_range, ← u.isClosedMap.isClosed_range.closure_eq, u.denseRange.closure_range]
    trivial⟩
  obtain ⟨C, hC⟩ := MMP.Mori.ProperCurve.exists_image_closure_eq_of_surjective hW hX u hu C'
  refine ⟨C, hC, fun w hw => ?_⟩
  have : u w ∈ closure {C'.point} := hC ▸ Set.mem_image_of_mem u hw
  simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hC' this

/-- **Off the bad locus the discrepancies agree.** If `h(η_E) ∉ Σ`, then
`a(E, X⁻, B⁻) = a(E, X⁺, B⁺)`. -/
private theorem eq_of_notMem_badLocusBase {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {W : Scheme.{0}} {g : W ⟶ Xm}
    {g' : W ⟶ Xp} (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') [IsProper g] [IsProper g']
    (hcomm : g ≫ fm = g' ≫ fp) (E : MMP.Mori.PrimeDivisor W)
    (hE : fm (g E.genericPoint) ∉ badLocusBase fm fp) {n : ℕ} {K' : Divisor Xp}
    (hK : K.IsCanonicalDivisor sXm n) (hK' : K'.IsCanonicalDivisor sXp n) {c c' : ℚ}
    (hc : IsDiscrepancy sXm n K B ⟨W, g, hW, hg, E⟩ c)
    (hc' : IsDiscrepancy sXp n K' (flipTransform fm fp B) ⟨W, g', hW', hg', E⟩ c') :
    c = c' := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  obtain rfl := h.comp_eq_minus
  obtain rfl := h.comp_eq_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  -- the image of `η_E` lies in the common biregular locus
  set z := fm (g E.genericPoint) with hz
  have hzU : z ∈ commonBiregularLocus fm fp := by
    by_contra hzU
    exact hE (by rw [← SetLike.mem_coe, coe_badLocusBase]; exact hzU)
  have hzm : z ∈ biregularLocus fm := (inf_le_left : commonBiregularLocus fm fp ≤ _) hzU
  have hzp : z ∈ biregularLocus fp := (inf_le_right : commonBiregularLocus fm fp ≤ _) hzU
  have hz' : fp (g' E.genericPoint) = z := by
    rw [hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  -- dimensions
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  have hnZ : topologicalKrullDim Z = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hfmb
  have hdZ := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  -- the generators, as pull-backs of forms on `Z`
  obtain ⟨-, -, m, hm, -, U₁, hU₁, τ, hτ, hτa⟩ := hc
  obtain ⟨-, -, m', hm', -, U₂, hU₂, τ', hτ', hτa'⟩ := hc'
  obtain ⟨σ, rfl, hσ⟩ := exists_pullbackRationalPluriForms_eq fm hfmb.functionFieldMap_bijective
    hdZ τ
  obtain ⟨σ', rfl, hσ'⟩ := exists_pullbackRationalPluriForms_eq fp hfpb.functionFieldMap_bijective
    hdZ τ'
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ fm ≫ sZ)
  haveI := hg.isDominant
  haveI := hg'.isDominant
  have hgf : IsBirationalMorphism (g ≫ fm) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfmb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hgf' : IsBirationalMorphism (g' ≫ fp) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fp g'
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfpb)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg')
  set DZ : DivisorOver ℂ sZ := ⟨W, g ≫ fm, hW, hgf, E⟩ with hDZ
  set DZ' : DivisorOver ℂ sZ := ⟨W, g' ≫ fp, hW', hgf', E⟩ with hDZ'
  have e1 := ordPullback_pullbackRationalPluriForms fm hfmb hdZ hW hg hgf E σ
  have e2 := ordPullback_pullbackRationalPluriForms fp hfpb hdZ hW' hg' hgf' E σ'
  haveI := hgf.isDominant
  haveI := hgf'.isDominant
  have hv : DZ'.valuation = DZ.valuation := by
    change E.valuationOver (g' ≫ fp) = E.valuationOver (g ≫ fm)
    simp only [hcomm]
  have e3 := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hZ hnZ hv σ'
  -- the comparison along the prime divisors of `Z` through `z`
  have key := mul_ordPullback_eq_of_forall hZ hnZ DZ (hσ hτ.1) (hσ' hτ'.1) (m := (m : ℤ))
    (m' := (m' : ℤ)) fun Γ hΓ => by
    have hΓz : z ∈ Γ.support := hΓ
    have hηz : Γ.genericPoint ⤳ z := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓz
    obtain ⟨Γm, hΓm, hisom, htrm⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hXm hfmb Γ
    obtain ⟨Γp, hΓp, hisop, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hXp hfpb Γ
    haveI := hisom
    haveI := hisop
    have o1 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
      hfmb.functionFieldMap_bijective hdZ Γm Γ hΓm σ
    have o2 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hfpb.functionFieldMap_bijective hdZ Γp Γ hΓp σ'
    have hm1 : g E.genericPoint ∈ Γm.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      refine specializes_of_mem_biregularLocus fm (hΓm ▸ hηz.mem_open (biregularLocus fm).2 hzm)
        hzm ?_
      rw [hΓm]
      exact hηz
    have hp1 : g' E.genericPoint ∈ Γp.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
      refine specializes_of_mem_biregularLocus fp (hΓp ▸ hηz.mem_open (biregularLocus fp).2 hzp)
        (hz' ▸ hzp) ?_
      rw [hΓp, hz']
      exact hηz
    have g1 := hτ.2 Γm ⟨_, hm1, hU₁⟩
    have g2 := hτ'.2 Γp ⟨_, hp1, hU₂⟩
    have hcoeff : (flipTransform fm fp B).coeff Γp = B.coeff Γm := by
      change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap B)
        Γp = B Γm
      rw [inverseTransformDivisor_apply_eq fp Γp Γ hΓp (hηz.mem_open (biregularLocus fp).2 hzp)]
      exact htrm B
    rw [o1] at g1
    rw [o2, hcoeff] at g2
    linear_combination (m' : ℚ) * g1 - (m : ℚ) * g2
  rw [← e1] at key
  rw [← e3, ← e2] at key
  have hm0 : (m : ℚ) * m' ≠ 0 := by positivity
  have : (m : ℚ) * m' * (c - c') = 0 := by
    have k' : ((m' : ℤ) : ℚ) * ((m : ℚ) * c) = ((m : ℤ) : ℚ) * ((m' : ℚ) * c') := by
      rwa [hτa, hτa']
    push_cast at k'
    linear_combination k'
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hm0)

/-- **Over the bad locus the comparison is strict.** If `h(η_E) ∈ Σ`, then
`a(E, X⁻, B⁻) < a(E, X⁺, B⁺)`. -/
private theorem lt_of_mem_badLocusBase {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {W : Scheme.{0}} {g : W ⟶ Xm}
    {g' : W ⟶ Xp} (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') [IsProper g] [IsProper g']
    (hcomm : g ≫ fm = g' ≫ fp) (E : MMP.Mori.PrimeDivisor W)
    (hE : fm (g E.genericPoint) ∈ badLocusBase fm fp) {c c' : ℚ}
    (hc : IsDiscrepancy sXm 3 K B ⟨W, g, hW, hg, E⟩ c)
    (hc' : IsDiscrepancy sXp 3 (flipTransform fm fp K) (flipTransform fm fp B)
      ⟨W, g', hW', hg', E⟩ c') :
    c < c' := by
  -- instances
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  haveI : QuasiCompact sXm := hXm.1.toQuasiCompact
  haveI : QuasiCompact sXp := hXp.1.toQuasiCompact
  haveI : IsProper sXm :=
    isProper_of_isProjectiveMorphism sXm h.isProjectiveVariety_minus.isProjective
  haveI : IsProper sXp :=
    isProper_of_isProjectiveMorphism sXp h.isProjectiveVariety_plus.isProjective
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isSmallMorphism_plus.isProper
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (g ≫ sXm) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : QuasiCompact (g ≫ sXm) := hW.1.toQuasiCompact
  haveI := hg.isDominant
  haveI := hg'.isDominant
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ sXm) := hW.1
  haveI : AlgebraicGeometry.IsVariety ℂ sXm := hXm.1
  haveI : AlgebraicGeometry.IsVariety ℂ sXp := hXp.1
  have hsZ : g' ≫ sXp = g ≫ sXm := by
    rw [← h.comp_eq_plus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_minus]
  set h₀ := g ≫ fm with hh₀_def
  have hh₀ : IsBirationalMorphism h₀ := MMP.Mori.isBirationalMorphism_comp_of_isBirational fm g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfmb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
  have hsW : h₀ ≫ sZ = g ≫ sXm := by rw [hh₀_def, Category.assoc, h.comp_eq_minus]
  -- canonical divisors, pairs and crepant boundaries
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  obtain ⟨n', hK'⟩ := h.isCanonicalDivisor_plus
  have hn : n = 3 := by
    have := hK.topologicalKrullDim_eq.symm.trans h.dim_minus
    exact_mod_cast this
  have hn' : n' = 3 := by
    have := hK'.topologicalKrullDim_eq.symm.trans h.dim_plus
    exact_mod_cast this
  subst hn hn'
  have hPm : MMP.Mori.IsPair sXm B := ⟨hXm, 3, K, hK, h.isQCartier_minus⟩
  have hPp : MMP.Mori.IsPair sXp (flipTransform fm fp B) :=
    ⟨hXp, 3, flipTransform fm fp K, hK', h.isQCartier_plus⟩
  obtain ⟨⟨Δm, hΔm, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPm hK g hW hg
  obtain ⟨⟨Δp, hΔp, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPp hK' g' hW' hg'
  have hcE : c = -Δm.coeff E := IsDiscrepancy.eq hc (hΔm E)
  have hc'E : c' = -Δp.coeff E := IsDiscrepancy.eq hc' (hΔp E)
  -- the divisor `H = Δ⁻ - Δ⁺` along curves
  obtain ⟨hH, L, L', hLB, hLB', hL, hL', hLq, hLq', hform⟩ :=
    exists_intersectionNumber_sub_eq hXm hXp hK hK' h.isQCartier_minus h.isQCartier_plus hW hW'
      hg hg' hsZ hΔm hΔp
  set BW := Δm - Δp with hBW_def
  have hamp_m : ∀ C : ProperCurve sXm, C.IsContractedBy fm →
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sXm C.ι C.dim_le h.isQCartier_minus < 0 :=
    fun C hC => by
      have hpos := intersectionNumber_pos_of_hasRelativelyAmpleMultiple
        h.hasRelativelyAmpleMultiple_minus (isQCartier_neg h.isQCartier_minus) C hC
      rw [intersectionNumber_neg ℂ sXm C.ι C.dim_le h.isQCartier_minus
        (isQCartier_neg h.isQCartier_minus)] at hpos
      linarith
  have hamp_p : ∀ C : ProperCurve sXp, C.IsContractedBy fp →
      0 < (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).intersectionNumber
        ℂ sXp C.ι C.dim_le h.isQCartier_plus := fun C hC =>
    intersectionNumber_pos_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_plus
      h.isQCartier_plus C hC
  have hLle : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      L.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq ≤ 0 := fun C hC => by
    rcases intersectionNumber_pullback_eq_zero_or g rfl fm h.isQCartier_minus hL hLq C hC with
      h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonpos_of_nonneg_of_nonpos hd (hamp_m C'' hC'').le
  have hL'ge : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      0 ≤ L'.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq' := fun C hC => by
    rcases intersectionNumber_pullback_eq_zero_or g' hsZ fp h.isQCartier_plus hL' hLq' C
        (by rw [← hcomm]; exact hC) with h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonneg hd (hamp_p C'' hC'').le
  have hnef : ∀ C : ProperCurve (g ≫ sXm), C.IsContractedBy h₀ →
      BW.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hH ≤ 0 := fun C hC => by
    rw [hform C]
    linarith [hLle C hC, hL'ge C hC]
  -- the coefficients off the exceptional divisors vanish
  have hWZ : IsNormalVariety ℂ (h₀ ≫ sZ) := by rwa [hsW]
  have hBG : ∀ P : MMP.Mori.PrimeDivisor W,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor sZ h₀ P → 0 ≤ BW.coeff P := fun P hP => by
    by_cases hex : MMP.Mori.RationalMap.IsExceptional (X := W) h₀.toRationalMap P
    · exact absurd (isExceptionalPrimeDivisor_of_isExceptional hZ hWZ hh₀ P hex) hP
    · obtain ⟨Q, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hZ
        (⟨W, h₀, hWZ, hh₀, P⟩ : DivisorOver ℂ sZ) hex
      have hPQ : h₀ P.genericPoint = Q.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ.1 hv
      have hU : fm (g P.genericPoint) ∉ badLocusBase fm fp := by
        intro hmem
        rw [← SetLike.mem_coe, coe_badLocusBase] at hmem
        refine hmem ⟨?_, ?_⟩
        · change h₀ P.genericPoint ∈ biregularLocus fm
          rw [hPQ]; exact genericPoint_mem_biregularLocus_of_primeDivisor fm hfmb Q
        · change h₀ P.genericPoint ∈ biregularLocus fp
          rw [hPQ]; exact genericPoint_mem_biregularLocus_of_primeDivisor fp hfpb Q
      have := eq_of_notMem_badLocusBase h hW hW' hg hg' hcomm P hU hK hK' (hΔm P) (hΔp P)
      change 0 ≤ Δm.coeff P - Δp.coeff P
      linarith
  -- effectivity (the negativity lemma)
  have hBW : 0 ≤ BW := nonneg_of_intersectionNumber_nonpos hZ hW h₀ hsW hh₀ hH hnef hBG
  have hBWc : ∀ P, 0 ≤ BW.coeff P := fun P => Finsupp.le_def.mp hBW P
  -- strictness
  rw [hcE, hc'E, neg_lt_neg_iff]
  by_contra hle
  push Not at hle
  have hE0 : BW.coeff E = 0 := by
    refine le_antisymm ?_ (hBWc E)
    change Δm.coeff E - Δp.coeff E ≤ 0
    linarith
  have hηE : E.genericPoint ∉ BW.supp := by
    rw [DivisorWithCoeffs.mem_supp_iff]
    rintro ⟨P, hP, hEP⟩
    by_cases hPE : P = E
    · subst hPE; exact hP hE0
    · exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne (Ne.symm hPE) hEP
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (g ≫ sXm)
  have hEsupp : E.genericPoint ∈ (E.support : Set W) := genericPoint_mem_support E
  obtain ⟨e, ⟨heE, heS⟩, hec⟩ := nonempty_inter_closedPoints
    (⟨E.genericPoint, hEsupp, hηE⟩ : ((E.support : Set W) ∩ (BW.supp : Set W)ᶜ).Nonempty)
    ((show IsClosed (E.support : Set W) by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure).isLocallyClosed.inter
      BW.supp.isClosed.isOpen_compl.isLocallyClosed)
  have hecl : IsClosed ({e} : Set W) := mem_closedPoints_iff.mp hec
  set y := h₀ e with hy_def
  have hsp : E.genericPoint ⤳ e := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact heE
  have hyBad : y ∈ badLocusBase fm fp :=
    (hsp.map h₀.continuous).mem_closed (badLocusBase fm fp).isClosed hE
  -- the fibre over `y` misses `Supp H`
  have hnegq : (-BW).IsQCartier := isQCartier_neg hH
  have hnefneg : (-BW).IsRelativelyNef (g ≫ sXm) h₀ :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sXm) hnegq
      fun C hC => by
        rw [intersectionNumber_neg ℂ (g ≫ sXm) C.ι C.dim_le hH hnegq]
        linarith [hnef C hC]
  have hfib := MMP.Mori.QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    ℂ sZ (g ≫ sXm) hZ hW h₀ hsW hh₀ hH (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hBW)
    hnefneg y
  have hdisj : Disjoint (h₀.base ⁻¹' {y}) (BW.supp : Set W) :=
    hfib.resolve_left fun hsub => heS (hsub rfl)
  -- a curve `C` in the fibre, contradicting `(H · C) < 0`
  have hzero : ∀ C : ProperCurve (g ≫ sXm), closure {C.point} ⊆ h₀.base ⁻¹' {y} →
      BW.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hH = 0 := fun C hCy => by
    have hpt : C.point ∉ BW.supp := fun hmem =>
      Set.disjoint_left.mp hdisj (hCy (subset_closure rfl)) hmem
    obtain ⟨-, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff (g ≫ sXm) BW hH hBW
      C hpt
    exact hiff.mpr fun x hx hmem =>
      Set.disjoint_left.mp hdisj (hCy (specializes_iff_mem_closure.mp hx)) hmem
  have hyU : y ∉ commonBiregularLocus fm fp := by
    intro hyU
    have h' := hyBad
    rw [← SetLike.mem_coe, coe_badLocusBase] at h'
    exact h' hyU
  rw [show commonBiregularLocus fm fp = biregularLocus fm ⊓ biregularLocus fp from rfl] at hyU
  by_cases hym : y ∈ biregularLocus fm
  · -- `f⁺` is not an isomorphism over `y`
    have hxe : fp (g' e) = y := by
      rw [hy_def, ← Scheme.Hom.comp_apply, ← hcomm]
    have hgcl : IsClosed ({g' e} : Set Xp) := by simpa using g'.isClosedMap _ hecl
    obtain ⟨CX, hCXy⟩ := exists_properCurve_subset_fibre hXp.1 hZ fp h.comp_eq_plus hfpb
      h.isIso_app_plus hgcl (hxe ▸ fun hyp => hyU ⟨hym, hyp⟩)
    rw [hxe] at hCXy
    obtain ⟨C, hC, hCy⟩ := exists_properCurve_image_eq_subset_fibre hW.1 hXp.1 g' hsZ fp CX hCXy
    rw [← hcomm] at hCy
    obtain ⟨d, hd, hdeq⟩ := intersectionNumber_pullback_eq_mul_of_image g' hsZ h.isQCartier_plus hL'
      hLq' C CX hC
    have h1 := hzero C hCy
    have h2 := hform C
    have h3 := hLle C (isContractedBy_of_subset_preimage hCy)
    have h4 : 0 < L'.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq' := by
      rw [hdeq]; exact mul_pos hd (hamp_p CX (isContractedBy_of_subset_preimage hCXy))
    linarith
  · -- `f⁻` is not an isomorphism over `y`
    have hgcl : IsClosed ({g e} : Set Xm) := by simpa using g.isClosedMap _ hecl
    obtain ⟨CX, hCXy⟩ := exists_properCurve_subset_fibre hXm.1 hZ fm h.comp_eq_minus hfmb
      h.isIso_app_minus hgcl hym
    obtain ⟨C, hC, hCy⟩ := exists_properCurve_image_eq_subset_fibre hW.1 hXm.1 g rfl fm CX hCXy
    obtain ⟨d, hd, hdeq⟩ := intersectionNumber_pullback_eq_mul_of_image g rfl h.isQCartier_minus hL
      hLq C CX hC
    have h1 := hzero C hCy
    have h2 := hform C
    have h3 := hL'ge C (isContractedBy_of_subset_preimage hCy)
    have h4 : L.intersectionNumber ℂ (g ≫ sXm) C.ι C.dim_le hLq < 0 := by
      rw [hdeq]; exact mul_neg_of_pos_of_neg hd (hamp_m CX (isContractedBy_of_subset_preimage hCXy))
    linarith

end Comparison

/-! ### Centres and log discrepancies -/

section Centre

/-- The centre of a normalized divisorial valuation `ξ = ord_E`, for a divisor `(W, g, E)`
over `X`, is the closure of `g(η_E)`. -/
private theorem coe_eq_closure_of_isCentre {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {C : IrreducibleCloseds X}
    (hC : MMP.Intersection.IsCentre ℂ sX ξ C) (D : DivisorOver ℂ sX) (hD : D.valuation = ξ) :
    (C : Set X) = closure {D.f D.E.genericPoint} := by
  obtain ⟨D₀, -, hv₀, rfl⟩ := hC
  rw [D₀.center_eq_closure_genericPoint,
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX (hv₀.symm.trans hD.symm)]

/-- The closure of a point lies in the preimage `(f)⁻¹(Σ)` of the closed set `Σ` exactly when
the image of the point lies in `Σ`. -/
private theorem closure_subset_preimage_iff {X Y : Scheme.{0}} (f : X ⟶ Y) (S : Closeds Y)
    (x : X) : closure {x} ⊆ f ⁻¹' (S : Set Y) ↔ f x ∈ S :=
  ⟨fun hs => hs (subset_closure rfl),
    fun hx => closure_minimal (Set.singleton_subset_iff.mpr hx) (S.isClosed.preimage f.continuous)⟩

/-- The log discrepancy of `ξ = ord_E` is `1 + a(E, X, B)`. -/
private theorem eq_one_add_of_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {D : DivisorOver ℂ sX} (hDp : IsProper D.f) {c : ℚ}
    (hc : IsDiscrepancy sX n K B D c) {a : ℝ} (ha : IsValuationLogDiscrepancy sX B D.valuation a) :
    a = 1 + c := by
  obtain ⟨n', D', -, hv, hl⟩ := ha
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp) hv

end Centre

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- `ξ⁺`, the valuation of `k(X⁺)` corresponding to `ξ = ord_E`, is `ord_E` for `(W, g', E)`. -/
private theorem valuation_eq_of_comap_eq {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsIntegral Z]
    [IsDominant fm] [IsDominant fp] (hfp : IsBirationalMorphism fp) {W : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {g : W ⟶ Xm} {g' : W ⟶ Xp}
    (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ fm = g' ≫ fp)
    (E : MMP.Mori.PrimeDivisor W) {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : ξp.comap (functionFieldMap fp) =
      (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation.comap (functionFieldMap fm)) :
    (⟨W, g', hW', hg', E⟩ : DivisorOver ℂ sXp).valuation = ξp := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hinj : Function.Injective
      (Valuation.comap (Γ₀ := WithZero (Multiplicative ℤ)) (functionFieldMap fp)) := by
    intro v w hvw
    ext x
    obtain ⟨y, rfl⟩ := hfp.functionFieldMap_bijective.2 x
    exact congrArg (fun v => v y) hvw
  apply hinj
  rw [hξ]
  ext x
  simp only [Valuation.comap_apply]
  change E.divisorialValuation (functionFieldMap g' (functionFieldMap fp x)) =
    E.divisorialValuation (functionFieldMap g (functionFieldMap fm x))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [hcomm]

/-- **Strictness of the threefold comparison.** In a threefold step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)`, let `ξ` be a normalized divisorial valuation of `k(X⁻)` and `ξ⁺` the
corresponding valuation of `k(X⁺)` (with the same restriction to `k(Z)`). With
`a⁻ = a(ξ; X⁻, B⁻)`, `a⁺ = a(ξ⁺; X⁺, B⁺)` and centres `C⁻ = c_{X⁻}(ξ)`, `C⁺ = c_{X⁺}(ξ⁺)`, the
following are equivalent: `a⁻ < a⁺`; `C⁻ ⊆ W⁻`; `C⁺ ⊆ W⁺`. -/
@[mmp "lem_mmp_indexc_graph_strict"]
public theorem IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      ξp.comap (functionFieldMap fp) = ξ.comap (functionFieldMap fm))
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap)
    {Cm : IrreducibleCloseds Xm} {Cp : IrreducibleCloseds Xp}
    (hCm : MMP.Intersection.IsCentre ℂ sXm ξ Cm) (hCp : MMP.Intersection.IsCentre ℂ sXp ξp Cp) :
    List.TFAE [am < ap, (Cm : Set Xm) ⊆ badLocusMinus fm fp,
      (Cp : Set Xp) ⊆ badLocusPlus fm fp] := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hCm' := hCm
  obtain ⟨D, -, rfl, -⟩ := hCm'
  obtain ⟨W, g, g', hW, hg, hgp, hg'p, hg', hcomm, E, hE⟩ := exists_commonModel h D
  have hW' : IsNormalVariety ℂ (g' ≫ sXp) := by
    rwa [← h.comp_eq_plus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_minus]
  set Dm : DivisorOver ℂ sXm := ⟨W, g, hW, hg, E⟩ with hDm
  set Dp : DivisorOver ℂ sXp := ⟨W, g', hW', hg', E⟩ with hDp
  have hDpv : Dp.valuation = ξp :=
    valuation_eq_of_comap_eq h.isSmallMorphism_plus.isBirationalMorphism hW hW' hg hg' hcomm E
      (by rw [hE]; exact hξ)
  -- the centres
  have hCmc : (Cm : Set Xm) = closure {g E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_minus hCm Dm hE
  have hCpc : (Cp : Set Xp) = closure {g' E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_plus hCp Dp hDpv
  have h2 : (Cm : Set Xm) ⊆ badLocusMinus fm fp ↔ fm (g E.genericPoint) ∈ badLocusBase fm fp := by
    rw [hCmc, coe_badLocusMinus]
    exact closure_subset_preimage_iff fm _ _
  have h3 : (Cp : Set Xp) ⊆ badLocusPlus fm fp ↔ fm (g E.genericPoint) ∈ badLocusBase fm fp := by
    rw [hCpc, coe_badLocusPlus, closure_subset_preimage_iff fp, ← Scheme.Hom.comp_apply,
      ← hcomm, Scheme.Hom.comp_apply]
  -- the discrepancies
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  obtain ⟨n', hK'⟩ := h.isCanonicalDivisor_plus
  have hn : n = 3 := by
    have := hK.topologicalKrullDim_eq.symm.trans h.dim_minus
    exact_mod_cast this
  have hn' : n' = 3 := by
    have := hK'.topologicalKrullDim_eq.symm.trans h.dim_plus
    exact_mod_cast this
  subst hn hn'
  have hPm : MMP.Mori.IsPair sXm B := ⟨h.isNormalVariety_minus, 3, K, hK, h.isQCartier_minus⟩
  have hPp : MMP.Mori.IsPair sXp (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, 3, flipTransform fm fp K, hK', h.isQCartier_plus⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPm hK Dm
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp hK' Dp
  have ham' : am = 1 + c := eq_one_add_of_isValuationLogDiscrepancy hgp hc (hE ▸ ham)
  have hap' : ap = 1 + c' := eq_one_add_of_isValuationLogDiscrepancy hg'p hc' (hDpv ▸ hap)
  have h1 : am < ap ↔ fm (g E.genericPoint) ∈ badLocusBase fm fp := by
    rw [ham', hap', add_lt_add_iff_left, Rat.cast_lt]
    refine ⟨fun hlt => ?_, fun hmem => lt_of_mem_badLocusBase h hW hW' hg hg' hcomm E hmem hc hc'⟩
    by_contra hnm
    exact hlt.ne (eq_of_notMem_badLocusBase h hW hW' hg hg' hcomm E hnm hK hK' hc hc')
  tfae_have 1 ↔ 2 := h1.trans h2.symm
  tfae_have 2 ↔ 3 := h2.trans h3.symm
  tfae_finish

end GraphStrict

/-! ### Log discrepancies off the bad locus -/

section OffBadLocus

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {R S Γ₀ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ₀] {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S Γ₀} (h : v.comap g = w.comap g) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hg t
  exact congrArg (fun u : Valuation R Γ₀ => u s) h

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme is that of its closure,
through the identification of function fields. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext t
  change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [functionFieldMap_id_apply]

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {W Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- `functionFieldMap` only depends on the morphism. -/
private theorem functionFieldMap_congr {A C : Scheme.{0}} [IsIntegral A] [IsIntegral C]
    {a b : A ⟶ C} (hab : a = b) [IsDominant a] [IsDominant b] (t : C.functionField) :
    functionFieldMap a t = functionFieldMap b t := by
  subst hab
  rfl

/-- **Crepant invariance**, with the structure morphism of the source given up to equality: if
`ΔY` is the crepant boundary of `(X, Δ)` along a birational `φ : Y ⟶ X`, divisors over `Y` and
over `X` with corresponding valuations have the same discrepancies. -/
private theorem isDiscrepancy_iff_of_crepant {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {KX : Divisor X} {Δ : QDivisor X}
    {KY : Divisor Y} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ)
    (hKX : KX.IsCanonicalDivisor sX n) (φ : Y ⟶ X) [IsDominant φ] (hs : φ ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hφ : IsBirationalMorphism φ) (hKY : KY.IsCanonicalDivisor sY n)
    (hcb : ∀ (F : MMP.Mori.PrimeDivisor Y) (D : DivisorOver ℂ sX), D.valuation = F.valuationOver φ →
      IsDiscrepancy sX n KX Δ D (-ΔY.coeff F))
    (E : DivisorOver ℂ sY) (E' : DivisorOver ℂ sX)
    (hv : E'.valuation = E.valuation.comap (functionFieldMap φ)) (a : ℚ) :
    IsDiscrepancy sY n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a := by
  subst hs
  have hcb' : IsCrepantBoundary sX n KX Δ φ hY hφ ΔY := fun F => hcb F _ rfl
  exact (IsPair.isDiscrepancy_iff_of_crepant hP φ hY hφ hKX hKY (Or.inl hcb')).2 E E' hv a

/-- Off the bad locus the log discrepancies of corresponding divisors agree. -/
private theorem eq_of_not_subset_badLocusPlus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hc : ¬ (Dp.center : Set Xp) ⊆ badLocusPlus fm fp)
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am = ap := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxW⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [coe_badLocusPlus, coe_badLocusBase] at hxW
    simpa using hxW
  -- dimensions and canonical divisors
  obtain ⟨mp, hKp⟩ := h.isCanonicalDivisor_plus
  obtain ⟨mm, hKm⟩ := h.isCanonicalDivisor
  obtain rfl : mp = n := by
    exact_mod_cast hKp.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hap)
  obtain rfl : mm = n' := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ham)
  obtain rfl : mm = mp := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (h.dim_minus.trans (h.dim_plus.symm.trans hKp.topologicalKrullDim_eq))
  have hPp : IsPairWith sXp mm (flipTransform fm fp K) (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, hKp, h.isQCartier_plus⟩
  obtain ⟨cp, hcp⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp.isPair hKp Dp
  obtain ⟨cm, hcm⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm Dm
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcp ap).mp hap).2,
    ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcm am).mp ham).2]
  suffices hcc : cm = cp by rw [hcc]
  -- restriction of `Dp` to `V⁺ = (f⁺)⁻¹(U)`
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPp Dp _ hU
  have hcE := (hiff cp).mp hcp
  -- the identification `V⁺ ≅ V⁻ ⊆ X⁻` over `U`
  haveI : Nonempty (fp ⁻¹ᵁ commonBiregularLocus fm fp) := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
  haveI : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  let φ : (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ⟶ Xm :=
    (fp ∣_ commonBiregularLocus fm fp) ≫ inv (fm ∣_ commonBiregularLocus fm fp) ≫
      (fm ⁻¹ᵁ commonBiregularLocus fm fp).ι
  have hφ : φ ≫ fm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hs : φ ≫ sXm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, hφ, Category.assoc]
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  have hφb : IsBirationalMorphism φ := isBirationalMorphism_of_isOpenImmersion φ
  haveI : IsDominant φ := hφb.isDominant
  haveI : IsDominant (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι :=
    Opens.isDominant_ι ((fp ⁻¹ᵁ commonBiregularLocus fm fp).isOpen.dense
      ⟨hU.choose, hU.choose_spec.2⟩)
  haveI : IsDominant (φ ≫ fm) := inferInstance
  haveI : IsDominant ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp) := inferInstance
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective.2
  -- valuations of prime divisors of `V⁺`, read on `k(X⁻)` and on `k(X⁺)`
  have hvF : ∀ F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme,
      (F.valuationOver φ).comap (functionFieldMap fm) =
        MMP.Mori.PrimeDivisor.valuationOver
          (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F) fp := by
    intro F
    ext t
    simp only [MMP.Mori.PrimeDivisor.valuationOver, Valuation.comap_apply]
    rw [divisorialValuation_primeDivisorMap, Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hvE : Dm.valuation = (DivisorOver.valuation (⟨_, Dp.f ∣_ _, hY, hf, E'⟩ :
      DivisorOver ℂ ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp))).comap
        (functionFieldMap φ) := by
    apply comap_injective_of_surjective hfm
    rw [← hv, hval]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hcb : ∀ (F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme)
      (D : DivisorOver ℂ sXm), D.valuation = F.valuationOver φ →
      IsDiscrepancy sXm mm K B D
        (-((flipTransform fm fp B).restrictOpen (fp ⁻¹ᵁ commonBiregularLocus fm fp)).coeff F) := by
    intro F D hD
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨Pm, -, hPm, -, -, -, hcoef, -⟩ := h.exists_primeDivisor_valuationOver_eq
      (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F)
    rw [hcoef]
    obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm
      (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm)
    obtain ⟨cD, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm D
    have hvD :
        D.valuation = (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm).valuation := by
      rw [valuation_ofPrimeDivisor, hD]
      apply comap_injective_of_surjective hfm
      rw [hvF, ← hPm]
      rfl
    have e := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvD
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq h.isNormalVariety_minus hvD)
      hcD hc₀
    rw [← hc₀.eq_neg_coeff_of_ofPrimeDivisor h.isNormalVariety_minus, ← e]
    exact hcD
  have hcrep := isDiscrepancy_iff_of_crepant hB.isPair hKm φ hs hcE.1 hφb hcE.2.1 hcb
    ⟨_, Dp.f ∣_ _, hY, hf, E'⟩ Dm hvE cp
  exact hcm.eq (hcrep.mp hcE)

/-- **The comparison** `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`. -/
private theorem le_of_isLogDiscrepancy (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am ≤ ap := by
  by_cases hc : (Dp.center : Set Xp) ⊆ badLocusPlus fm fp
  · have ham' : IsValuationLogDiscrepancy sXm B Dm.valuation am := ⟨n', Dm, hDm, rfl, ham⟩
    have hap' : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) Dp.valuation ap :=
      ⟨n, Dp, hap.2.1, rfl, hap⟩
    have hCm : MMP.Intersection.IsCentre ℂ sXm Dm.valuation Dm.center := ⟨Dm, hDm, rfl, rfl⟩
    have hCp : MMP.Intersection.IsCentre ℂ sXp Dp.valuation Dp.center :=
      ⟨Dp, hap.2.1, rfl, rfl⟩
    have hT := IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hv
      ham' hap' hCm hCp
    exact (show am < ap from (hT.out 3 1).mp hc).le
  · exact (eq_of_not_subset_badLocusPlus h hB Dp Dm hv hc hap ham).le

end OffBadLocus

/-- A log discrepancy `a(ξ; X, B)` of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_unique {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : IsValuationLogDiscrepancy sX B ξ a) (h' : IsValuationLogDiscrepancy sX B ξ a') :
    a = a' := by
  obtain ⟨n, D, -, hD, ha⟩ := h
  obtain ⟨n', D', -, hD', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)

/-! ### Lost divisors -/

section LostDivisor

/-- The centre of `ord_E` on a normal variety `X` is the centre of `E` regarded as a divisor over
`X` through the identity. -/
private theorem isCentre_divisorialValuation {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (E : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsCentre k sX E.divisorialValuation
      (DivisorOver.ofPrimeDivisor k hX E).center :=
  ⟨_, (inferInstance : IsProper (𝟙 X)), Valuation.ext fun g => by
    change _ = E.divisorialValuation (functionFieldMap (𝟙 X) g)
    rw [functionFieldMap_id_apply], rfl⟩

/-- The centre of `E` regarded as a divisor over `X` through the identity is `E` itself. -/
private theorem coe_center_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (E : MMP.Mori.PrimeDivisor X) :
    ((DivisorOver.ofPrimeDivisor k hX E).center : Set X) = E.support := by
  simpa [DivisorOver.coe_center, DivisorOver.ofPrimeDivisor] using
    E.idealSheaf.support.isClosed.closure_eq

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Lost divisors improve strictly.** In a threefold step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)`, let `E` be a prime divisor of `X⁻` such that `ord_E`, transported to
the valuation `ξ⁺` of `k(X⁺)` with the same restriction to `k(Z)`, is exceptional over `X⁺`.
Then `a(ord_E; X⁻, B⁻) < a(ξ⁺; X⁺, B⁺)`. -/
@[mmp "lem_mmp_indexc_lost_divisor_improves"]
public theorem IsThreefoldStepDiagram.lt_of_isExceptionalValuation
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm)
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      ξp.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm))
    (hexc : MMP.Intersection.IsExceptionalValuation ℂ sXp ξp)
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B E.divisorialValuation am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap) :
    am < ap := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  obtain ⟨D, hD, hDv, hcod⟩ := hexc
  refine ((h.tfae_lt_and_centre_subset_badLocus hξ ham hap
    (isCentre_divisorialValuation h.isNormalVariety_minus E) ⟨D, hD, hDv, rfl⟩).out 1 2).mpr ?_
  rw [coe_center_ofPrimeDivisor]
  exact h.support_subset_badLocusMinus E ⟨ξp, hξ, D, hD, hDv, hcod⟩

end LostDivisor

/-! ### Klt and terminal pairs -/

section KltTerminal

section

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]; exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The pair `(X⁺, B⁺)` of a threefold step diagram with `(X⁻, B⁻)` a pair. -/
private theorem isPair_flipTransform (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B) : MMP.Fourfold.IsPair sXp (flipTransform fm fp B) := by
  obtain ⟨m, hK⟩ := h.isCanonicalDivisor_plus
  refine ⟨hB.isAlgClosed, hB.charZero, ⟨h.isNormalVariety_plus, m, _, hK, h.isQCartier_plus⟩,
    fun P => ?_⟩
  obtain ⟨Pm, -, -, -, -, -, hc, -⟩ := h.exists_primeDivisor_valuationOver_eq P
  rw [hc]
  exact h.nonneg Pm

/-- Every divisor `D⁺` over `X⁺` (with proper structure morphism) has a counterpart `D⁻` over
`X⁻`, proper, whose valuation agrees with that of `D⁺` on `k(Z)`. -/
private theorem exists_properDivisorOver_minus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (D : DivisorOver ℂ sXp) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ D' : DivisorOver ℂ sXm, IsProper D'.f ∧
      D.valuation.comap (functionFieldMap fp) = D'.valuation.comap (functionFieldMap fm) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  let e : Z.functionField ≃+* Xm.functionField :=
    RingEquiv.ofBijective (functionFieldMap fm)
      h.isBirationalMorphism_minus.functionFieldMap_bijective
  have hξ : ((D.valuation.comap (functionFieldMap fp)).comap e.symm.toRingHom).comap
      (functionFieldMap fm) = D.valuation.comap (functionFieldMap fp) := by
    ext t
    simp only [Valuation.comap_apply]
    congr 2
    exact e.symm_apply_apply t
  obtain ⟨D', hD'p, hD'v⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    h.isNormalVariety_minus fp fm h.isSmallMorphism_plus.isBirationalMorphism
    h.isBirationalMorphism_minus (isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus)
    h.comp_eq_plus h.comp_eq_minus D _ hξ
  exact ⟨D', hD'p, by rw [hD'v, hξ]⟩

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_toTerminal sX
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe]

/-- A normalized divisorial valuation realized by a proper divisor `D` over a variety is
exceptional iff the centre of `D` has codimension at least two. -/
private theorem isExceptionalValuation_valuation_iff {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (D : DivisorOver k sX) (hD : IsProper D.f) :
    MMP.Intersection.IsExceptionalValuation k sX D.valuation ↔ 2 ≤ codimension D.center := by
  refine ⟨fun ⟨D₁, _, h, hc⟩ => ?_, fun h => ⟨D, hD, rfl, h⟩⟩
  rwa [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX h]

/-- A divisor over `X⁺` exceptional over `X⁺` has an exceptional counterpart over `X⁻` when `f⁻`
is small. -/
private theorem isExceptional_of_isSmallMorphism
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    (Dp : DivisorOver ℂ sXp) (hDp : IsProper Dp.f) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (he : Dp.IsExceptional) : Dm.IsExceptional := by
  have hT := (IsThreefoldStepDiagram.isExceptionalValuation_iff_of_isSmallMorphism h hsmall).1
    Dm.valuation Dp.valuation ⟨Dm, hDm, rfl⟩ hv
  rw [isExceptional_iff_two_le_codimension h.isNormalVariety_minus,
    ← isExceptionalValuation_valuation_iff h.isNormalVariety_minus.1 Dm hDm, hT,
    isExceptionalValuation_valuation_iff h.isNormalVariety_plus.1 Dp hDp,
    ← isExceptional_iff_two_le_codimension h.isNormalVariety_plus]
  exact he

/-- The log discrepancy of a proper divisor over a pair exists. -/
private theorem exists_isLogDiscrepancy (hB : MMP.Fourfold.IsPair sXm B) (Dm : DivisorOver ℂ sXm)
    (hDm : IsProper Dm.f) :
    ∃ (n : ℕ) (am : ℝ), MMP.Intersection.IsLogDiscrepancy sXm n (QDivisor.toRDivisor B) Dm am := by
  obtain ⟨-, n, K', hK', -⟩ := hB.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hK' Dm
  exact ⟨n, _, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDm⟩

/-- **Log discrepancies do not drop along a threefold step.** Every log discrepancy `a⁺` of a
divisor `D⁺` over `(X⁺, B⁺)` bounds from above a log discrepancy `a⁻ ≤ a⁺` of a divisor `D⁻` over
`(X⁻, B⁻)`, which is exceptional whenever `D⁺` is and `f⁻` is small. -/
private theorem exists_isLogDiscrepancy_minus_le (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B) {n : ℕ} {Dp : DivisorOver ℂ sXp} {ap : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap) :
    ∃ (Dm : DivisorOver ℂ sXm) (n' : ℕ) (am : ℝ),
      MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am ∧ am ≤ ap ∧
      (IsSmallMorphism sXm sZ fm → Dp.IsExceptional → Dm.IsExceptional) := by
  obtain ⟨Dm, hDm, hv⟩ := exists_properDivisorOver_minus h Dp
  obtain ⟨n', am, ham⟩ := exists_isLogDiscrepancy hB Dm hDm
  exact ⟨Dm, n', am, ham, le_of_isLogDiscrepancy h hB Dp Dm hDm hv hap ham,
    fun hsmall => isExceptional_of_isSmallMorphism h hsmall Dp hap.2.1 Dm hDm hv⟩

end

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **Klt and terminal are preserved by threefold steps.** In a threefold step diagram
`(X⁻, B⁻) → Z ← (X⁺, B⁺)` with `(X⁻, B⁻)` klt, the pair `(X⁺, B⁺)` is klt; if moreover `f⁻` is
small and `(X⁻, B⁻)` is terminal, then `(X⁺, B⁺)` is terminal. -/
@[mmp "lem_mmp_indexc_klt_terminal_preserved"]
public theorem IsThreefoldStepDiagram.isKltPair_and_isKltTerminalPair_flipTransform
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hklt : IsKltPair sXm B) :
    IsKltPair sXp (flipTransform fm fp B) ∧
      (IsSmallMorphism sXm sZ fm → IsKltTerminalPair sXm B →
        IsKltTerminalPair sXp (flipTransform fm fp B)) := by
  have hklt' : IsKltPair sXp (flipTransform fm fp B) :=
    ⟨isPair_flipTransform h hklt.1, fun _ _ _ hap => by
      obtain ⟨Dm, n', am, ham, hle, -⟩ := exists_isLogDiscrepancy_minus_le h hklt.1 hap
      exact (hklt.2 n' Dm am ham).trans_le hle⟩
  refine ⟨hklt', fun hsmall hterm => ⟨hklt', fun _ _ _ hex hap => ?_⟩⟩
  obtain ⟨Dm, n', am, ham, hle, hex'⟩ := exists_isLogDiscrepancy_minus_le h hklt.1 hap
  exact (hterm.2 n' Dm am (hex' hsmall hex) ham).trans_le hle

end KltTerminal

/-! ### Decreasing the boundary of a junction -/

/-- **Subtracting an effective Cartier divisor raises log discrepancies.** If `a = a(F; X, B)`,
`C₀` is an effective Cartier divisor and `c ≥ 0`, then `a(F; X, B - c C₀) = a + c ord_F(C₀)`,
which is at least `a`. -/
private theorem exists_isLogDiscrepancy_sub_smul_ge {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}
    {B : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) {C₀ : Divisor X} (hC₀ : C₀.IsCartier)
    (hC₀e : ∀ P, 0 ≤ C₀.coeff P) {c : ℝ} (hc : 0 ≤ c) :
    ∃ a' : ℝ, a ≤ a' ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B - c • Divisor.toRDivisor C₀) D a' := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  have hB₀ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f C₀
  obtain ⟨C₀', hC₀'⟩ := hC₀.exists_isPullback hB₀
  have hnn : 0 ≤ C₀'.coeff D.E :=
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hC₀
      (fun P _ => hC₀e P) hC₀' D.E ((D.E.genericPoint_mem_iff _).mp trivial)
  refine ⟨a + c * (C₀'.coeff D.E : ℝ), ?_, hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r (-c),
    Fin.snoc C C₀, Fin.snoc C' C₀', ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ c * (C₀'.coeff D.E : ℝ) := mul_nonneg hc (by exact_mod_cast hnn)
    linarith
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC₀
    · simpa using hC j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, ← hrel Γ, smul_eq_mul]
    ring
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨by simpa using hB₀, by simpa using hC₀'⟩
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- Subtracting a nonnegative combination of effective Cartier divisors raises log
discrepancies. -/
private theorem exists_isLogDiscrepancy_sub_sum_ge {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}
    {D : DivisorOver k sX} {ι : Type*} (C : ι → Divisor X) (hC : ∀ j, (C j).IsCartier)
    (hCe : ∀ j P, 0 ≤ (C j).coeff P) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (S : Finset ι)
    {B : RDivisor X} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ a' : ℝ, a ≤ a' ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B - ∑ j ∈ S, c j • Divisor.toRDivisor (C j))
        D a' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨a, le_rfl, by simpa using h⟩
  | insert j S hj ih =>
    obtain ⟨a₁, ha₁, h₁⟩ := ih
    obtain ⟨a₂, ha₂, h₂⟩ := exists_isLogDiscrepancy_sub_smul_ge h₁ (hC j) (hCe j) (hc j)
    refine ⟨a₂, ha₁.trans ha₂, ?_⟩
    rw [Finset.sum_insert hj, sub_add_eq_sub_sub_swap]
    exact h₂

/-- **Lowering the coefficients of prime divisors raises log discrepancies** on a variety where a
positive multiple of every Weil divisor is Cartier: `a(ξ; X, Θ) ≤ a(ξ; X, Θ - ∑_s c_s E_s)` for
`c_s ≥ 0`. Write `Θ - ∑_s c_s E_s = Θ - ∑_s (c_s / N_s) (N_s E_s)` with `N_s E_s` Cartier. -/
private theorem le_of_isValuationLogDiscrepancy_sub_sum_single {k : Type} [Field k]
    [PerfectField k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)}
    (hX : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    {ι : Type*} [Fintype ι] (E : ι → MMP.Mori.PrimeDivisor X) {c : ι → ℚ} (hc : ∀ s, 0 ≤ c s)
    {Θ : QDivisor X} {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {b b' : ℝ}
    (hb : IsValuationLogDiscrepancy sX Θ ξ b)
    (hb' : IsValuationLogDiscrepancy sX (Θ - ∑ s, Finsupp.single (E s) (c s)) ξ b') :
    b ≤ b' := by
  classical
  obtain ⟨n, D, -, hDv, hD⟩ := hb
  obtain ⟨n', D', -, hD'v, hD'⟩ := hb'
  choose N hN hNc using fun s => hX (Finsupp.single (E s) (1 : ℤ))
  let C : ι → Divisor X := fun s => ((N s : ℕ) : ℤ) • Finsupp.single (E s) (1 : ℤ)
  let c' : ι → ℝ := fun s => (c s : ℝ) / (N s : ℝ)
  have hCe : ∀ s P, 0 ≤ (C s).coeff P := fun s P => by
    change (0 : ℤ) ≤ ((N s : ℕ) : ℤ) • (Finsupp.single (E s) (1 : ℤ)) P
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  have hc' : ∀ s, 0 ≤ c' s := fun s => div_nonneg (by exact_mod_cast hc s) (Nat.cast_nonneg _)
  obtain ⟨b'', hb'', hD''⟩ := exists_isLogDiscrepancy_sub_sum_ge C hNc hCe c' hc' Finset.univ hD
  have hR : QDivisor.toRDivisor (Θ - ∑ s, Finsupp.single (E s) (c s)) =
      QDivisor.toRDivisor Θ - ∑ s, c' s • Divisor.toRDivisor (C s) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub,
      QDivisor.coeff_toRDivisor]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Rat.cast_sub,
      Rat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hN0 : (N s : ℝ) ≠ 0 := by exact_mod_cast (hN s).ne'
    change _ = c' s * ((C s).coeff P : ℝ)
    simp only [C, c', DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> field_simp <;> simp
  rw [← hR] at hD''
  linarith [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD'' hD'
    (hDv.trans hD'v.symm)]

namespace StabilizedTail

/-- **Decreasing coefficients raises log discrepancies.** Let `(p_i, Θ_i)` be a crepant junction
of `(X_i, B_i)` extracting `I_∞ = I(X_i, B_i)`, with divisors `E_{i,s}`, and `Θ_i'` its decreased
boundary. Then `Θ_i - Θ_i' = ∑_{s ∈ I_∞} (a_{i+1}(s) - a_i(s)) E_{i,s}`, this divisor is
effective, and `a(ξ; Y_i, Θ_i) ≤ a(ξ; Y_i, Θ_i')` for every normalized divisorial valuation `ξ`
of `k(Y_i)`. -/
@[mmp "lem_mmp_indexc_decrease_discrepancy"]
public theorem IsDecreasedBoundary.sub_eq_sum_and_le {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    {J : CrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') :
    (∀ a a' : I → ℚ, (∀ s : I, T.IsLogDiscrepancyAt i s (a s)) →
      (∀ s : I, ∃ s' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)),
        T.IsTransportedValuation i s s' ∧ T.IsLogDiscrepancyAt (i + 1) s' (a' s)) →
      J.Θ - Θ' = ∑ s : I, Finsupp.single (J.E s) (a' s - a s)) ∧
    0 ≤ J.Θ - Θ' ∧
    ∀ (ξ : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))) (b b' : ℝ),
      IsValuationLogDiscrepancy (J.p ≫ T.sX i) J.Θ ξ b →
      IsValuationLogDiscrepancy (J.p ≫ T.sX i) Θ' ξ b' → b ≤ b' := by
  classical
  obtain ⟨a₀, ha₀, hΘ⟩ := J.Θ_eq
  obtain ⟨a₁, ha₁, hΘ'eq⟩ := hΘ'
  have hdiff : J.Θ - Θ' = ∑ s : I, Finsupp.single (J.E s) (a₁ s - a₀ s) := by
    rw [hΘ, hΘ'eq, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finsupp.single_sub]
    congr 1
    ring
  have hst := T.isThreefoldStepDiagram i
  haveI : IsIntegral (T.Z i) := hst.isNormalVariety_target.1.toIsIntegral
  haveI := hst.isBirationalMorphism_minus.isDominant
  haveI := hst.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hle : ∀ s, a₀ s ≤ a₁ s := by
    intro s
    obtain ⟨n, Dm, hDm, hDmv, ham⟩ := ha₀ s
    obtain ⟨s'', htr, n', Dp, -, hDpv, hap⟩ := ha₁ s
    rw [T.B_eq i] at hap
    have hv : Dp.valuation.comap (functionFieldMap (T.fp i)) =
        Dm.valuation.comap (functionFieldMap (T.f i)) := by
      rw [hDpv, hDmv]
      exact htr
    exact_mod_cast le_of_isLogDiscrepancy hst (T.isKltPair i).1 Dp Dm hDm hv hap ham
  have hnonneg : 0 ≤ J.Θ - Θ' := by
    rw [hdiff]
    exact Finset.sum_nonneg fun s _ => Finsupp.single_nonneg.mpr (sub_nonneg.mpr (hle s))
  refine ⟨fun a a' ha ha' => ?_, hnonneg, fun ξ b b' hb hb' => ?_⟩
  · rw [hdiff]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e0 : a s = a₀ s := by exact_mod_cast isValuationLogDiscrepancy_unique (ha s) (ha₀ s)
    obtain ⟨s', hs', hs'a⟩ := ha' s
    obtain ⟨s'', hs'', hs''a⟩ := ha₁ s
    have hss : s' = s'' := by
      unfold StabilizedTail.IsTransportedValuation at hs' hs''
      exact comap_injective_of_surjective
        hst.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
        (hs'.trans hs''.symm)
    subst hss
    have e1 : a' s = a₁ s := by exact_mod_cast isValuationLogDiscrepancy_unique hs'a hs''a
    rw [e0, e1]
  · refine le_of_isValuationLogDiscrepancy_sub_sum_single J.isQFactorial.2 J.E
      (fun s => sub_nonneg.mpr (hle s)) hb ?_
    rwa [← hdiff, sub_sub_cancel]

end StabilizedTail

/-! ### Fixed labels -/

section InverseTransform

variable {X Y : Scheme.{0}} {R : Type*} [AddCommMonoid R] {g : Y ⟶ X}

/-- A prime divisor of `Y` which is the inverse transform of no prime divisor of `X` has
coefficient zero in every inverse transform `g⁻¹_* B`. -/
private theorem coeff_inverseTransformDivisor_eq_zero {F : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P, inverseTransformPrimeDivisor g P ≠ some F) (B : DivisorWithCoeffs R X) :
    (inverseTransformDivisor g B).coeff F = 0 := by
  classical
  induction B using Finsupp.induction_linear with
  | zero => simp [DivisorWithCoeffs.coeff]
  | add B B' hB hB' =>
    rw [map_add, DivisorWithCoeffs.coeff, Finsupp.add_apply, ← DivisorWithCoeffs.coeff,
      ← DivisorWithCoeffs.coeff, hB, hB', add_zero]
  | single P r =>
    rw [inverseTransformDivisor_single]
    rcases hP : inverseTransformPrimeDivisor g P with _ | E
    · rfl
    · exact Finsupp.single_eq_of_ne fun hEF => h P (hEF ▸ hP)

end InverseTransform

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- No prime divisor of `X` has an exceptional prime divisor as its inverse transform: the generic
point of `E_s` maps to a point of codimension `≥ 2`, while that of a prime divisor has
codimension `1`. -/
private theorem inverseTransformPrimeDivisor_ne_E (J : CrepantJunction sX B I) (s : I)
    (P : MMP.Mori.PrimeDivisor X) : inverseTransformPrimeDivisor J.p P ≠ some (J.E s) := by
  intro hP
  have hX : IsSeparated (X ↘ ⊤_ Scheme) :=
    haveI := J.isKltPair.1.isPair.1.1
    isSeparated_toTerminal sX
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hexc := (J.isExceptional_iff (J.E s)).mpr ⟨s, rfl⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hexc
  have h2 := hexc (J.p (J.E s).genericPoint)
    (subset_closure ⟨_, genericPoint_mem_support (J.E s), rfl⟩)
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The coefficient of `Θ = p⁻¹_* B + ∑ (1 - a_s) E_s` along a prime divisor `F` of `Y`. -/
private theorem coeff_Θ (J : CrepantJunction sX B I) {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (F : MMP.Mori.PrimeDivisor J.Y) :
    J.Θ.coeff F = (inverseTransformDivisor J.p B).coeff F +
      ∑ s : I, (Finsupp.single (J.E s) (1 - a s) : QDivisor J.Y) F := by
  rw [hΘ, DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.finset_sum_apply]
  rfl

/-- The coefficient of `Θ` along `E_s` is `1 - a(s; X, B)`. -/
private theorem coeff_Θ_E (J : CrepantJunction sX B I) {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (s : I) : J.Θ.coeff (J.E s) = 1 - a s := by
  classical
  rw [coeff_Θ J hΘ, coeff_inverseTransformDivisor_eq_zero (inverseTransformPrimeDivisor_ne_E J s),
    zero_add, Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
      (J.injective.ne hts.symm)) (by simp)]
  simp

end Junction

/-! ### Curves off the bad locus -/

section Curves

/-- Over the common biregular locus `U` of `f⁻` and `f⁺`, points with the same image have the
same coheight: `f^±` restrict to open immersions over `U`. -/
private theorem coheight_eq_of_mem_commonBiregularLocus {Xm Xp Z : Scheme.{0}} (fm : Xm ⟶ Z)
    (fp : Xp ⟶ Z) {x : Xm} {x' : Xp} (hxx : fm x = fp x')
    (hU : fm x ∈ commonBiregularLocus fm fp) : Order.coheight x = Order.coheight x' := by
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ Z) (y : Y),
      IsBiregular f (commonBiregularLocus fm fp) → f y ∈ commonBiregularLocus fm fp →
        Order.coheight (f y) = Order.coheight y := by
    intro Y f y hf hy
    haveI : IsIso (f ∣_ commonBiregularLocus fm fp) := hf
    have e : (f ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ f =
        (f ∣_ commonBiregularLocus fm fp) ≫ (commonBiregularLocus fm fp).ι :=
      (morphismRestrict_ι _ _).symm
    haveI : IsOpenImmersion ((f ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ f) := by
      rw [e]; infer_instance
    let y' : (f ⁻¹ᵁ commonBiregularLocus fm fp).toScheme := ⟨y, hy⟩
    have h1 := coheight_eq_of_isOpenImmersion (x := y') ((f ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ f)
    have h2 := coheight_eq_of_isOpenImmersion (x := y') (f ⁻¹ᵁ commonBiregularLocus fm fp).ι
    exact h1.trans h2.symm
  rw [← key fm x (isBiregular_commonBiregularLocus_left fm fp) hU,
    ← key fp x' (isBiregular_commonBiregularLocus_right fm fp) (hxx ▸ hU), hxx]

/-- On two threefolds, closures of points of the same coheight have the same dimension; we only
need that one of them being a curve forces the other to be a curve. -/
private theorem topologicalKrullDim_closure_eq_one {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] (sX : X ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] (hdim : topologicalKrullDim X = 3)
    (hdim' : topologicalKrullDim X' = 3) {x : X} {x' : X'}
    (hc : Order.coheight x = Order.coheight x')
    (h1 : topologicalKrullDim (closure {x} : Set X) = 1) :
    topologicalKrullDim (closure {x'} : Set X') = 1 := by
  have a := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  have b := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' x'
  rw [h1, hdim] at a
  rw [hdim', ← hc] at b
  generalize Order.coheight x = c at a b
  generalize topologicalKrullDim (closure {x'} : Set X') = d at b ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd a (by decide)
  | coe c =>
    have hc2 : c = 2 := by
      have : ((1 + c : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) := WithBot.coe_injective (by push_cast; exact a)
      have := Nat.cast_injective this
      omega
    subst hc2
    induction d using WithBot.recBotCoe with
    | bot => exact absurd b (by decide)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd b (by decide)
      | coe d =>
        have : ((d + 2 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) := WithBot.coe_injective (by push_cast; exact b)
        have := Nat.cast_injective this
        have : d = 1 := by omega
        subst this
        rfl

end Curves

/-! ### The induction along the tail -/

section Tail

variable {T : StabilizedTail}

/-- A valuation `u ∈ I(X_j, B_j)` has a transport to `k(X_{j+1})` lying in
`I(X_{j+1}, B_{j+1})`. -/
private theorem exists_isTransportedValuation_mem {j : ℕ}
    {u : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    (hu : u ∈ lowDiscrepancySet (T.sX j) (T.B j)) :
    ∃ u' ∈ lowDiscrepancySet (T.sX (j + 1)) (T.B (j + 1)), T.IsTransportedValuation j u u' := by
  have he := T.lowDiscrepancySet_eq j
  haveI : IsIntegral (T.Z j) := (T.isThreefoldStepDiagram j).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram j).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hmem : u.comap (functionFieldMap (T.f j)) ∈
      valuationsOver (T.f j) (lowDiscrepancySet (T.sX j) (T.B j)) := ⟨u, hu, rfl⟩
  rw [he] at hmem
  obtain ⟨u', hu', hu'e⟩ := hmem
  exact ⟨u', hu', hu'e⟩

/-- The transports of a valuation of `I_∞` lie in the low-discrepancy sets of the tail. -/
private theorem mem_lowDiscrepancySet_of_isTransportedValuationFrom
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    (hν : ν ∈ T.lowDiscrepancySetLimit) :
    ∀ (i : ℕ) {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom i ν w → w ∈ lowDiscrepancySet (T.sX i) (T.B i)
  | 0, w, hw => (show w = ν from hw) ▸ hν
  | i + 1, w, hw => by
    obtain ⟨u, hu, huw⟩ := hw
    haveI : IsIntegral (T.Z i) :=
      (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    obtain ⟨u', hu', he⟩ := exists_isTransportedValuation_mem
      (mem_lowDiscrepancySet_of_isTransportedValuationFrom hν i hu)
    have hb := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
    have : w = u' := comap_injective_of_surjective hb.functionFieldMap_bijective.2
      (huw.trans he.symm)
    exact this ▸ hu'

/-- **The induction step.** If `w ∈ I(X_j, B_j)` has log discrepancy `a` and a curve `V` as centre
on `X_j`, and every curve of `W_j⁻` has `mld > 1`, then its transport `w'` to `k(X_{j+1})` lies
in `I(X_{j+1}, B_{j+1})`, has log discrepancy `a`, and its centre on `X_{j+1}` is a curve. -/
private theorem exists_step {j : ℕ}
    (hmld : ∀ V : IrreducibleCloseds (T.X j),
      topologicalKrullDim (V : Set (T.X j)) = 1 →
      (V : Set (T.X j)) ⊆ (T.badLocusMinusAt j : Set (T.X j)) →
      1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint)
    {w : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    (hw : w ∈ lowDiscrepancySet (T.sX j) (T.B j)) {a : ℚ} (ha : T.IsLogDiscrepancyAt j w a)
    {V : IrreducibleCloseds (T.X j)} (hV : MMP.Intersection.IsCentre ℂ (T.sX j) w V)
    (hVdim : topologicalKrullDim (V : Set (T.X j)) = 1) :
    ∃ w', w' ∈ lowDiscrepancySet (T.sX (j + 1)) (T.B (j + 1)) ∧
      T.IsTransportedValuation j w w' ∧ T.IsLogDiscrepancyAt (j + 1) w' a ∧
      ∃ V' : IrreducibleCloseds (T.X (j + 1)),
        MMP.Intersection.IsCentre ℂ (T.sX (j + 1)) w' V' ∧
          topologicalKrullDim (V' : Set (T.X (j + 1))) = 1 := by
  have h := T.isThreefoldStepDiagram j
  haveI : IsIntegral (T.Z j) := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := (T.isProjectiveVariety j).1.toLocallyOfFiniteType
  haveI := (T.isProjectiveVariety (j + 1)).1.toLocallyOfFiniteType
  obtain ⟨w', hw'low, htr⟩ := exists_isTransportedValuation_mem hw
  have hw'low' := hw'low
  -- `a ≤ 1`
  obtain ⟨-, a₀, ha₀, ha₀1⟩ := hw
  have ha1 : (a : ℝ) ≤ 1 := (isValuationLogDiscrepancy_unique ha ha₀) ▸ ha₀1
  -- `V ⊄ W_j⁻`
  have hX := h.isNormalVariety_minus
  obtain ⟨n, Dm, hDmp, hDmv, hlm⟩ := id ha
  have hVc : (V : Set (T.X j)) = closure {Dm.f Dm.E.genericPoint} :=
    coe_eq_closure_of_isCentre hX hV Dm hDmv
  have hnot : ¬ (V : Set (T.X j)) ⊆ badLocusMinus (T.f j) (T.fp j) := by
    intro hsub
    have h1 := hmld V hVdim hsub
    have h2 : minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint ≤
        (((a : ℝ)) : EReal) := by
      apply sInf_le
      refine ⟨n, Dm, a, hlm, ?_, rfl⟩
      rw [Dm.center_eq_closure_genericPoint, ← hVc,
        V.isIrreducible.isGenericPoint_genericPoint_closure, V.isClosed.closure_eq]
    have h3 : (1 : EReal) < ((a : ℝ) : EReal) := h1.trans_le h2
    have h4 : (1 : ℝ) < a := by exact_mod_cast h3
    linarith
  -- the common model
  obtain ⟨W, g, g', hW, hg, -, -, hg', hcomm, E, hE⟩ := exists_commonModel h Dm
  have hW' : IsNormalVariety ℂ (g' ≫ T.sX (j + 1)) := by
    rwa [← h.comp_eq_plus, ← Category.assoc, ← hcomm, Category.assoc, h.comp_eq_minus]
  have hDp' : (⟨W, g', hW', hg', E⟩ : DivisorOver ℂ (T.sX (j + 1))).valuation = w' :=
    valuation_eq_of_comap_eq h.isSmallMorphism_plus.isBirationalMorphism hW hW' hg hg' hcomm E
      (by rw [hE, hDmv]; exact htr)
  -- the log discrepancy on `X_{j+1}`
  obtain ⟨-, ap, hap, -⟩ := hw'low
  have hap' := hap
  rw [T.B_eq j] at hap
  obtain ⟨n', Dp, hDpp, hDpv, hlp⟩ := hap
  have hCp : MMP.Intersection.IsCentre ℂ (T.sX (j + 1)) w' Dp.center :=
    ⟨Dp, hDpp, hDpv.symm, rfl⟩
  have hT := IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus h htr ha
    ⟨n', Dp, hDpp, hDpv, hlp⟩ hV hCp
  have hc : ¬ (Dp.center : Set (T.X (j + 1))) ⊆ badLocusPlus (T.f j) (T.fp j) :=
    fun hsub => hnot ((hT.out 2 3).mpr hsub)
  have heq : (a : ℝ) = ap := eq_of_not_subset_badLocusPlus h (T.isKltPair j).1 Dp Dm
    (by rw [hDpv, hDmv]; exact htr) hc hlp hlm
  refine ⟨w', hw'low', htr, heq ▸ hap', Dp.center, hCp, ?_⟩
  -- the centre on `X_{j+1}` is a curve
  have hCpc : (Dp.center : Set (T.X (j + 1))) = closure {g' E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_plus hCp _ hDp'
  have hVc' : (V : Set (T.X j)) = closure {g E.genericPoint} :=
    coe_eq_closure_of_isCentre hX hV ⟨W, g, hW, hg, E⟩ (hE.trans hDmv)
  have hz : T.f j (g E.genericPoint) ∈ commonBiregularLocus (T.f j) (T.fp j) := by
    by_contra hz
    apply hnot
    rwa [hVc', coe_badLocusMinus, closure_subset_preimage_iff]
  have hxx : T.f j (g E.genericPoint) = T.fp j (g' E.genericPoint) := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  rw [hCpc]
  exact topologicalKrullDim_closure_eq_one (T.sX j) (T.sX (j + 1)) (T.dim_eq j)
    (T.dim_eq (j + 1)) (coheight_eq_of_mem_commonBiregularLocus _ _ hxx hz) (hVc' ▸ hVdim)

/-- **The induction along the tail.** If the transport `w` of `ν ∈ I_∞` to `k(X_i)` has log
discrepancy `a` and a curve as centre, and every curve of `W_j⁻`, `j ≥ i`, has `mld > 1`, then for
every `j ≥ i` the transport of `ν` to `k(X_j)` lies in `I(X_j, B_j)`, has log discrepancy `a` and
a curve as centre. -/
private theorem exists_transport_of_isCentre_curve
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    (hν : ν ∈ T.lowDiscrepancySetLimit) {i : ℕ}
    (hmld : ∀ j ≥ i, ∀ V : IrreducibleCloseds (T.X j),
      topologicalKrullDim (V : Set (T.X j)) = 1 →
      (V : Set (T.X j)) ⊆ (T.badLocusMinusAt j : Set (T.X j)) →
      1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint)
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.IsTransportedValuationFrom i ν w)
    {V : IrreducibleCloseds (T.X i)} (hV : MMP.Intersection.IsCentre ℂ (T.sX i) w V)
    (hVdim : topologicalKrullDim (V : Set (T.X i)) = 1)
    {a : ℚ} (ha : T.IsLogDiscrepancyAt i w a) :
    ∀ j ≥ i, ∃ wj : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ)),
      T.IsTransportedValuationFrom j ν wj ∧ wj ∈ lowDiscrepancySet (T.sX j) (T.B j) ∧
        T.IsLogDiscrepancyAt j wj a ∧ ∃ Vj : IrreducibleCloseds (T.X j),
          MMP.Intersection.IsCentre ℂ (T.sX j) wj Vj ∧
            topologicalKrullDim (Vj : Set (T.X j)) = 1 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    exact ⟨w, hw, mem_lowDiscrepancySet_of_isTransportedValuationFrom hν i hw, ha, V, hV, hVdim⟩
  | succ j hij ih =>
    obtain ⟨wj, hwj, hlow, haj, Vj, hVj, hdj⟩ := ih
    obtain ⟨w', hw', htr, ha', V', hV', hd'⟩ := exists_step (hmld j hij) hlow haj hVj hdj
    exact ⟨w', ⟨wj, hwj, htr⟩, hw', ha', V', hV', hd'⟩

/-- At the `j`-th junction, the label `E_{0, s}` is `E_{j, w}` for the transport `w ∈ I(X_j, B_j)`
of `s`, whose coefficient in `Θ_j` is `1 - a_j(w)`. -/
private theorem isJunctionLabelCoefficient_of_isTransportedValuationFrom
    (C : StabilizedTail.TerminalChain T) (s : C.I 0) {j : ℕ}
    {w : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.IsTransportedValuationFrom j s.1 w) (hlow : w ∈ lowDiscrepancySet (T.sX j) (T.B j))
    {a : ℚ} (ha : T.IsLogDiscrepancyAt j w a) :
    C.IsJunctionLabelCoefficient ⟨(C.junction 0).E s, C.isLabel_E s⟩ j (1 - a) := by
  let t : C.I j := ⟨w, by rw [← Finset.mem_coe, C.coe_I j]; exact hlow⟩
  refine ⟨(C.junction j).E t, ⟨w, ?_, (C.junction j).valuation_eq t⟩, ?_⟩
  · rw [StabilizedTail.TerminalChain.labelValuation_E]
    exact hw
  · obtain ⟨a', ha', hΘ⟩ := (C.junction j).Θ_eq
    change (C.junction j).Θ.coeff ((C.junction j).E t) = 1 - a
    rw [coeff_Θ_E _ hΘ t]
    have : (a' t : ℝ) = a := isValuationLogDiscrepancy_unique (ha' t) ha
    rw [show a' t = a by exact_mod_cast this]

end Tail

namespace StabilizedTail

namespace TerminalChain

/-- **An extracted label with a curve centre is fixed.** Let `C` be a terminal chain over a
stabilized tail `T`, and let `i₁` be such that for every `j ≥ i₁`, every irreducible curve
`V ⊆ W_j⁻` has `mld_{η_V}(X_j, B_j) > 1`. Let `s ∈ I_∞`, and suppose that for some `i ≥ i₁` the
centre on `X_i` of `s` (regarded as the valuation `w` of `k(X_i)`) is a curve `V`. If
`a = a_i(s) = a(w; X_i, B_i)`, then the label `E_{0,s}` is fixed, and its coefficient at the
`j`-th junction is `1 - a` for every `j ≥ i`. -/
@[mmp "lem_mmp_indexc_curve_label_fixed"]
public theorem isFixedLabel_and_isJunctionLabelCoefficient {T : StabilizedTail}
    (C : TerminalChain T) {i₁ : ℕ}
    (hmld : ∀ j ≥ i₁, ∀ V : IrreducibleCloseds (T.X j),
      topologicalKrullDim (V : Set (T.X j)) = 1 →
      (V : Set (T.X j)) ⊆ (T.badLocusMinusAt j : Set (T.X j)) →
      1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint)
    (s : C.I 0) {i : ℕ} (hi : i₁ ≤ i)
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.IsTransportedValuationFrom i s.1 w)
    {V : IrreducibleCloseds (T.X i)} (hV : MMP.Intersection.IsCentre ℂ (T.sX i) w V)
    (hVdim : topologicalKrullDim (V : Set (T.X i)) = 1)
    {a : ℚ} (ha : T.IsLogDiscrepancyAt i w a) :
    C.IsFixedLabel ⟨(C.junction 0).E s, C.isLabel_E s⟩ ∧
      ∀ j ≥ i, C.IsJunctionLabelCoefficient ⟨(C.junction 0).E s, C.isLabel_E s⟩ j (1 - a) := by
  have hs : s.1 ∈ T.lowDiscrepancySetLimit := by
    show s.1 ∈ lowDiscrepancySet (T.sX 0) (T.B 0)
    rw [← C.coe_I 0]
    exact s.2
  have hcoef : ∀ j ≥ i,
      C.IsJunctionLabelCoefficient ⟨(C.junction 0).E s, C.isLabel_E s⟩ j (1 - a) := fun j hj => by
    obtain ⟨wj, hwj, hlow, haj, -⟩ := exists_transport_of_isCentre_curve hs
      (fun j hj => hmld j (hi.trans hj)) hw hV hVdim ha j hj
    exact isJunctionLabelCoefficient_of_isTransportedValuationFrom C s hwj hlow haj
  exact ⟨⟨1 - a, i, hcoef⟩, hcoef⟩

end TerminalChain

end StabilizedTail

/-! ### Finite chains of threefold steps -/

/-- **The comparison divisor of a finite chain of threefold steps is exceptional.** For threefold
step diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k < m`, with transported canonical
divisors `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k` and boundaries `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`, and
birational morphisms `q_k : W ⟶ V_k`, `k ≤ m`, over `ℂ` from a smooth projective complex variety
with `q_k ≫ g_k = q_{k+1} ≫ g_k⁺`, the push-forward along `q_m` of
`q_0^*(K_0 + Θ_0) - q_m^*(K_m + Θ_m)` vanishes. -/
@[mmp "lem_mmp_indexc_finite_program_exceptional"]
public theorem transformDivisor_pullback_sub_pullback_eq_zero_of_isThreefoldStepDiagram (m : ℕ)
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (hstep : ∀ k < m,
      IsThreefoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWs : MMP.Mori.IsSmoothScheme sW)
    (q : ∀ k, W ⟶ V k) (hq : ∀ k ≤ m, IsBirationalMorphism (q k))
    (hqs : ∀ k ≤ m, q k ≫ sV k = sW)
    (hcomp : ∀ k < m, q k ≫ g k = q (k + 1) ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    RationalMap.transformDivisor (X := W) (q m).toRationalMap
      ((Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
        (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ) = 0 :=
  transformDivisor_pullback_sub_pullback_eq_zero_of_isSmallMorphism m sV K Θ sT g gp
    (fun k hk => isProper_of_isProjectiveMorphism _ (hstep k hk).isProjectiveMorphism_minus)
    (fun k hk => (hstep k hk).isBirationalMorphism_minus)
    (fun k hk => (hstep k hk).isSmallMorphism_plus) hK hΘ q hq hcomp hD₀ hDₘ h₀ hₘ

end MMP.Fourfold
