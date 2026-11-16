module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FlipBadSetFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FlipDifference
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.FlipWeightsOutsideBadSet
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainWeightMonotone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.ChowForm.Defs
import MMP.AlgebraicGeometry.ChowForm.CoreSkeleton
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.MonomialValuationWeight
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.Normalization.IntegralScheme
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Strict decrease of the difficulty along a move of a prepared chain

Let `(Y, Θ) ⤏ (Y', Θ')` be a move of a prepared chain: a coefficient decrease
`(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or a small terminal flip `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge. If some
normalized divisorial valuation `v` exceptional over both `Y` and `Y'` has strictly smaller weight
on the target, `w_v(Y', Θ') < w_v(Y, Θ)`, then the difficulty strictly decreases,
`𝒟(Y', Θ') < 𝒟(Y, Θ)`.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.difficulty_lt_of_valuationWeight_lt`: the strict
  decrease of the difficulty.

## Implementation notes

The models of the prepared chain are indexed by
`MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex` and a move from the model `x` to the
model `x'` is one of three kinds:

* the coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` from the junction `(i, none)` to the model
  `(i, some 0)` of the `i`-th bridge, when the bridge has at least one flip; both models live on
  the variety `Y_i`, and a valuation of `ℂ(Y_i)` is a valuation of both;
* the coefficient decrease of a bridge without flips, from the junction `(i, none)` to the next
  junction `(i + 1, none)`: the decreased pair `(Y_i, Θ_i')` is then `(Y_{i+1}, Θ_{i+1})` through
  the identification `e : Y_i = V_0 ≅ Y_{i+1}` of the bridge, and a valuation `v` of `ℂ(Y_i)`
  corresponds to the valuation `v'` of `ℂ(Y_{i+1})` obtained by pulling back along `e`;
* a small terminal flip move `μ` (`MMP.Fourfold.StabilizedTail.PreparedChain.FlipMove`), with step
  diagram `Y⁻ → Z ← Y⁺`; a valuation `v'` of `ℂ(Y⁺)` corresponds to the valuation `v` of `ℂ(Y⁻)`
  when their restrictions to `ℂ(Z)` agree, as in
  `MMP.Fourfold.StabilizedTail.PreparedChain.flipBadSet`.

The weights are `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at the admissible
scale of the prepared chain; that predicate contains that the valuation is a normalized divisorial
valuation exceptional over the model. Difficulties are the predicate
`MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty` on their values.
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Curves -/

section

open CategoryTheory AlgebraicGeometry

/-- The closure of the generic point of a proper curve, as a subspace of `X`, has dimension
one: it is the image of the closed embedding `C ⟶ X`. -/
private theorem MMP.Mori.ProperCurve.topologicalKrullDim_closure_point {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

end

/-! ### Port of `lem_mmp_indexd_echoes` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.IndexdStrict.Card_echoes

open MMP.Mori MMP.Fourfold MMP.Resolution

/-! ### Preliminaries -/

/-- The support of a prime divisor is closed. -/
private theorem isClosed_support {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y) :
    IsClosed (E.support : Set Y) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isClosed_closure

/-- In a scheme of dimension three, an irreducible closed subset of codimension two is a
curve. -/
private theorem topologicalKrullDim_eq_one_of_codimension_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 3) (V : IrreducibleCloseds Y) (hV : codimension V = 2) :
    topologicalKrullDim (V : Set Y) = 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at hV
  rw [hV] at h
  generalize topologicalKrullDim (V : Set Y) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast
        exact h
      have h'' : d + 2 = 3 := by exact_mod_cast WithBot.coe_inj.mp h'
      obtain rfl : d = 1 := by omega
      rfl

/-! ### Components of an snc closed subset -/

/-- An irreducible closed subset maximal in a closed set of pure codimension one of a scheme is
the support of a prime divisor. -/
private theorem exists_primeDivisor_support_eq_of_maximal {Y : Scheme.{u}} {T : Closeds Y}
    (hT : IsPureCodimOne T) {W : IrreducibleCloseds Y}
    (hW : Maximal (fun V : IrreducibleCloseds Y => (V : Set Y) ⊆ T) W) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W := by
  have h1 := hT W hW
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq

/-- An irreducible component of a closed set of pure codimension one of a scheme is the support of
a prime divisor. -/
private theorem exists_primeDivisor_support_eq {Y : Scheme.{u}} {T : Set Y} (hTc : IsClosed T)
    (hpure : IsPureCodimOne (⟨T, hTc⟩ : Closeds Y)) {W : Set Y} (hW : W ∈ componentsOf T) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W :=
  exists_primeDivisor_support_eq_of_maximal hpure
    (W := ⟨W, hW.1.1, Aux.isClosed_of_mem_componentsOf hTc hW⟩)
    ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩

/-- A point of a closed set of pure codimension one of a Noetherian scheme lies on a prime divisor
contained in it. -/
private theorem exists_primeDivisor_mem_support_subset {Y : Scheme.{u}} [NoetherianSpace Y]
    {T : Closeds Y} (hT : IsPureCodimOne T) {y : Y} (hy : y ∈ (T : Set Y)) :
    ∃ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support ∧ (P.support : Set Y) ⊆ T := by
  obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf T.isClosed).2 hy)
  obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq T.isClosed hT hW
  exact ⟨P, hP ▸ hyW, hP ▸ hW.1.2⟩

/-- **The components of an snc closed subset.** The prime divisors whose generic points lie on a
divisor `T` with simple normal crossings on a smooth scheme form a finite set whose reduced sum is
an snc divisor. -/
private theorem exists_finset_isSNC_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [NoetherianSpace Y] (hsm : IsSmoothScheme sY)
    {T : Set Y} (hT : IsSNCClosedSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      (⋃ F ∈ S, (F.support : Set Y)) = T := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : LocallyOfFinitePresentation sY :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sY)).mpr inferInstance
  haveI : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
  obtain ⟨hTc, hT0 | ⟨hpure, hfin, -⟩⟩ := id hT
  · refine ⟨∅, ?_, by simp [hT0]⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
  have hinj : Set.InjOn (fun P : MMP.Mori.PrimeDivisor Y => (P.support : Set Y))
      {P | (P.support : Set Y) ∈ componentsOf T} := fun P _ Q _ hPQ =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ.le
  have hfinS : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ∈ componentsOf T}.Finite :=
    Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 fun _ hP => hP)) hinj
  set S := hfinS.toFinset with hSdef
  have hmemS : ∀ P, P ∈ S ↔ (P.support : Set Y) ∈ componentsOf T := fun P => by
    rw [hSdef, Set.Finite.mem_toFinset]; rfl
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2)
      fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
  exact ⟨S, MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset
    sY hreg S (hU ▸ hT), hU⟩

/-- A prime divisor lies in the support of a reduced sum `∑_{E ∈ S} E` exactly when it is in
`S`. -/
private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-! ### The support of the crepant boundary -/

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The support of the crepant boundary.** For a proper birational morphism `f : Y ⟶ X` from a
normal variety, every prime divisor in the support of the crepant boundary `Δ_Y` is
`f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f G.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hGe
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hc' : ΔY.coeff G = Δ.coeff P := neg_injective ((hΔY G).eq hd)
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc',
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-! ### Log-smooth data with prescribed labels -/

/-- **Log-smooth data with labels.** Let `(X, B)` be a klt pair and `D` a finite set of prime
divisors containing `Supp B`. A log resolution `π : W ⟶ X` of `(X, D)` which is an isomorphism
over the snc locus of `(X, D)`, with `T` the reduced sum of the components of
`Ex(π) ∪ π⁻¹(Supp D)`, is a log-smooth datum of `(X, B)`. -/
private theorem exists_isLogSmoothDatum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltPair sX B) (D : Finset (MMP.Mori.PrimeDivisor X))
    (hD : B.support ⊆ D) :
    ∃ (W : Scheme.{u}) (π : W ⟶ X) (T : Divisor W), IsLogSmoothDatum sX B π T ∧
      IsPureCodimOne (exceptionalSet π) ∧
      (⋃ E ∈ T.support, (E.support : Set W)) =
        (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) ∧
      ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
        IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X))) →
        IsIso (π ∣_ U) := by
  classical
  haveI : IsAlgClosed k := hB.1.isAlgClosed
  haveI : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.isPair
  obtain ⟨Y, f, hres, hpure, hS, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D
  haveI : IsProper f := IsProjective.isProper hres.isProjective
  have hfres : IsSmoothResolution sX f :=
    ⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  obtain ⟨⟨BY, hBY, -⟩, -⟩ :=
    IsPair.existsUnique_isCrepantBoundary hB.1.isPair hK f hY hfres.isBirationalMorphism
  obtain ⟨S, hsncS, hU⟩ :=
    exists_finset_isSNC_of_isSNCClosedSubset (f ≫ sX) hfres.isSmoothScheme hS
  have hsupp : (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support = S :=
    Finset.ext (mem_support_sum_single S)
  have hmem : ∀ G : MMP.Mori.PrimeDivisor Y, G.genericPoint ∈ (⋃ F ∈ S, (F.support : Set Y)) →
      G ∈ S := fun G hG => by
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  have hBD : (B.support.sup fun E => (E.idealSheaf.support : Set X)) ⊆
      (D.sup fun E => (E.idealSheaf.support : Set X)) := Finset.sup_mono hD
  refine ⟨Y, f, ∑ E ∈ S, Finsupp.single E (1 : ℤ), ⟨hB, hres.isProjective,
    hfres.isBirationalMorphism, hY, hfres.isSmoothScheme, fun P => ?_, hsncS, fun y hy => ?_,
    n, K, BY, hBY, fun G hG => ?_⟩, hpure, by rw [hsupp, hU], hiso⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    by_cases hP : P ∈ S <;> simp [Finsupp.single_apply, hP]
  · rw [hsupp, hU]
    exact Or.inl hy
  · rw [hsupp]
    apply hmem
    rw [hU]
    exact (genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hX, hK, hq⟩ hY
      hfres.isBirationalMorphism hBY hG).imp id fun h => hBD h

/-! ### Exceptional divisors and the log discrepancies of the components -/

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ :=
    Closeds.ext (by rw [Closeds.coe_closure]; exact D.coe_center.symm)
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

/-- **The log discrepancies of the prime divisors of a log-smooth datum.** Let `(π, T)` be a
log-smooth datum of a terminal pair `(X, B)`. Every prime divisor `G` of `W` has a log
discrepancy `a_G > 0`; it is `> 1` when the generic point of `G` lies in `Ex(π)`, and it is
`1 - b_P` when `π` maps the generic point of `G` to that of a prime divisor `P` of `X`. -/
private theorem exists_logDiscrepancy_primeDivisor {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltTerminalPair sX B) {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) :
    ∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
      ∃ aT : MMP.Mori.PrimeDivisor W → ℝ,
        (∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
          ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j)) ∧
        (∀ j, 0 < aT j) ∧
        (∀ j, j.genericPoint ∈ (exceptionalSet π : Set W) → 1 < aT j) ∧
        ∀ j (P : MMP.Mori.PrimeDivisor X), π j.genericPoint = P.genericPoint →
          aT j = 1 - (B.coeff P : ℝ) := by
  haveI : IsAlgClosed k := hB.1.1.isAlgClosed
  haveI : CharZero k := hB.1.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.1.isPair
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : IsIntegral W := hW.1.toIsIntegral
  let DT : MMP.Mori.PrimeDivisor W → DivisorOver k sX :=
    fun j => ⟨W, π, hW, hπ.isBirationalMorphism, j⟩
  have hex : ∀ j, ∃ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) (DT j) a := fun j => by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.1.isPair hK (DT j)
    exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstance : IsProper π)⟩
  choose aT haT using hex
  refine ⟨n, K, hK, aT, haT, fun j => hB.1.2 n (DT j) (aT j) (haT j),
    fun j hj => hB.2 n (DT j) (aT j) ?_ (haT j), fun j P hP => ?_⟩
  · rw [isExceptional_iff_two_le_codimension hX, MMP.Positivity.DivisorOver.codimension_center]
    have hcod := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX π (hY := hX.1)
      (hX := hW.1) hπ.isBirationalMorphism
    exact (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hcod) _
      (MMP.Mori.mem_exceptionalSet.1 hj)
  · have hc1 : codimension (DT j).center = 1 := by
      rw [MMP.Positivity.DivisorOver.codimension_center]
      change Order.coheight (π j.genericPoint) = 1
      rw [hP]
      exact P.coheight_genericPoint
    have hne : ¬ (DT j).IsExceptional := by
      rw [isExceptional_iff_two_le_codimension hX, hc1]
      decide
    obtain ⟨P', hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff ⟨hX, hK, hq⟩ _ hne
    have hPP : P' = P := by
      refine MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset ?_
      rw [← hc, DivisorOver.center_eq_closure_genericPoint,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change closure {π j.genericPoint} ⊆ _
      rw [hP]
    subst hPP
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique (haT j)
      (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd inferInstance)]
    push_cast
    ring

/-! ### Lifting prime divisors over the biregular locus -/

/-- **Prime divisors lift over the biregular locus.** If `π : W ⟶ X` is an isomorphism over a
neighbourhood of `π(w)` and `S` is a prime divisor of `X` through `π(w)`, there is a prime divisor
`G` of `W` through `w` with `π(η_G) = η_S`, whose ideal at `w` is the image of that of `S` under
the isomorphism `𝒪_{X,π(w)} ≅ 𝒪_{W,w}`. -/
private theorem exists_primeDivisor_lift {X W : Scheme.{u}} (π : W ⟶ X) {w : W}
    (hw : π w ∈ MMP.Mori.biregularLocus π) (S : MMP.Mori.PrimeDivisor X)
    (hS : π w ∈ S.support) :
    ∃ G : MMP.Mori.PrimeDivisor W, w ∈ G.support ∧ π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf w =
        Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk S.idealSheaf (π w)) := by
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus π hw
  let e : X.presheaf.stalk (π w) ≃+* W.presheaf.stalk w :=
    (asIso (π.stalkMap w)).commRingCatIsoToRingEquiv
  obtain ⟨q, hq, hqI, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
  set q' : PrimeSpectrum (W.presheaf.stalk w) := PrimeSpectrum.comap e.symm.toRingHom q
  have hmap : π (W.fromSpecStalk w q') = S.genericPoint := by
    have h : π (W.fromSpecStalk w q') =
        X.fromSpecStalk (π w) (PrimeSpectrum.comap (π.stalkMap w).hom q') := by
      have := congrArg (fun g : Spec (W.presheaf.stalk w) ⟶ X => g q')
        (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := w))
      simp only [Scheme.Hom.comp_apply] at this
      exact this.symm
    rw [h, ← hq]
    congr 1
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change a ∈ Ideal.comap (π.stalkMap w).hom (Ideal.comap e.symm.toRingHom q.asIdeal) ↔ _
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change e.symm (e a) ∈ q.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  have hgen : π (W.fromSpecStalk w q') ∈ MMP.Mori.biregularLocus π := by
    rw [hmap]
    refine (Specializes.mem_open ?_ (MMP.Mori.biregularLocus π).isOpen hw)
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hS
  have h1 : Order.coheight (W.fromSpecStalk w q') = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus π hgen, hmap]
    exact S.coheight_genericPoint
  set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hsupp : (G.support : Set W) = closure {W.fromSpecStalk w q'} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [hsupp]
    exact specializes_iff_mem_closure.1 (MMP.Resolution.specializes_fromSpecStalk w q')
  · change π (AlgebraicGeometry.PrimeDivisor.genericPoint G) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hmap
  · have hcl : G.idealSheaf.support = Closeds.closure {W.fromSpecStalk w q'} :=
      Closeds.ext (by rw [Closeds.coe_closure]; exact hsupp)
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf G, hcl,
      Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk w q', hqI]
    exact Ideal.comap_symm e

/-! ### Centres over a birational morphism -/

/-- The generic point of the centre of a divisor `D` over `X` is the image of the generic point
of `D`. -/
private theorem genericPoint_center_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) :
    D.center.isIrreducible.genericPoint = D.f D.E.genericPoint :=
  (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).eq
    D.center_eq_closure_genericPoint.symm

section Centres

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsIntegral W] [IsSeparated sX] {π : W ⟶ X} [IsDominant π]

/-- If `π_* v_{D'} = v_{D₀}` for a divisor `D'` over `W` and a divisor `D₀` over `X`, then `π`
maps the generic point of the centre of `D'` to that of the centre of `D₀`. -/
private theorem map_genericPoint_eq_of_comap_eq (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation) :
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

/-- If `π_* v_{D'} = v_{D₀}`, then `π` maps the generic point of `c_W(D')` to that of
`c_X(D₀)`. -/
private theorem map_genericPoint_center_eq_of_comap_eq (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation) :
    π D'.center.isIrreducible.genericPoint = D₀.center.isIrreducible.genericPoint := by
  rw [genericPoint_center_eq, genericPoint_center_eq]
  exact map_genericPoint_eq_of_comap_eq D' D₀ hξ

/-- **A centre off the exceptional locus has the same codimension downstairs.** -/
private theorem codimension_center_eq_of_notMem_exceptionalSet (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation)
    (hη : D'.f D'.E.genericPoint ∉ (exceptionalSet π : Set W)) :
    codimension D₀.center = codimension D'.center := by
  rw [MMP.Positivity.DivisorOver.codimension_center, MMP.Positivity.DivisorOver.codimension_center,
    ← map_genericPoint_eq_of_comap_eq D' D₀ hξ]
  exact MMP.Positivity.coheight_map_of_mem_biregularLocus π
    (by_contra fun h => hη (MMP.Mori.mem_exceptionalSet.2 h))

end Centres

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

/-! ### The log-smooth formula at the centre -/

/-- **The log-smooth formula at the centre.** Let `(π, T)` be a log-smooth datum of `(X, B)`,
with log discrepancies `a_G` of the prime divisors of `W`, and `D` a divisor over `X` with log
discrepancy `a`. Then `v_D = π_* v_{D'}` for a divisor `D'` over `W`, the reduced snc
discrepancy `e_T(v_{D'})` is a natural number `e`, and for local equations `z_j` of the
components `T_j` through the centre of `D'` the orders `m_j = v_{D'}(z_j) ≥ 1` satisfy
`a = ∑_j m_j a_j + e`. -/
private theorem exists_logSmoothFormula_at_centre {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ}
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a) :
    haveI := hπ.isBirationalMorphism.isDominant
    ∃ D' : DivisorOver k (π ≫ sX),
      MMP.Intersection.IsCentre k (π ≫ sX) D'.valuation D'.center ∧
      D'.valuation.comap (functionFieldMap π) = D.valuation ∧
      ∃ e : ℕ, IsReducedSNCDiscrepancy (π ≫ sX) T D'.valuation e ∧
      ∃ (z : sncIndexSet T (D'.center : Set W) →
          W.presheaf.stalk D'.center.isIrreducible.genericPoint)
        (m : sncIndexSet T (D'.center : Set W) → ℤ),
        (∀ j, IdealSheafData.stalk j.1.idealSheaf D'.center.isIrreducible.genericPoint =
          Ideal.span {z j}) ∧
        (∀ j, 1 ≤ m j) ∧
        (∀ j, D'.valuation (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) ∧
        a = ∑ j, (m j : ℝ) * aT j + e := by
  classical
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  let φ := RingEquiv.ofBijective (functionFieldMap π)
    hπ.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨Z, hZ, e, he, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D ha.2.1 ha (D.valuation.comap φ.symm.toRingHom)
      (by ext f; exact congrArg D.valuation (φ.symm_apply_apply f))
  obtain ⟨D', hD'p, hξD', rfl⟩ := hZ
  have hηj : ∀ j : sncIndexSet T (D'.center : Set W),
      D'.center.isIrreducible.genericPoint ∈ (j.1.support : Set W) := fun j =>
    (Finset.mem_filter.1 j.2).2
      (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  choose z hzp hz using fun j : sncIndexSet T (D'.center : Set W) =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sX) hπ.isSmoothScheme j.1 (hηj j)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D' (genericPoint_center_eq D')
    (hzp j).ne_zero ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  obtain ⟨e, rfl⟩ := he.exists_eq_natCast
  refine ⟨D', ⟨D', hD'p, rfl, rfl⟩, ?_, e, hξD' ▸ he, z, m, hz, hm1, hm,
    hform z m hz (hξD' ▸ hm)⟩
  rw [← hξD']
  ext f
  exact congrArg D.valuation (φ.symm_apply_apply f)

/-! ### Uniqueness of the reduced snc discrepancy -/

/-- Pulling valuations back along the inclusion of a nonempty open subscheme is injective. -/
private theorem comap_functionFieldMap_ι_injective {X : Scheme.{u}} [IsIntegral X]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (U : X.Opens) [Nonempty U] :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    Function.Injective (Valuation.comap (Γ₀ := Γ₀) (functionFieldMap U.ι)) := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hsurj := (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩).2
  intro v w hvw
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun v => v y) hvw

/-- **The reduced snc discrepancy is unique.** -/
private theorem IsReducedSNCDiscrepancy.unique {k : Type u} [Field k] [PerfectField k]
    {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {T : Divisor W} {ξ : Valuation W.functionField ℤᵐ⁰} {e e' : ℝ}
    (h : IsReducedSNCDiscrepancy sW T ξ e) (h' : IsReducedSNCDiscrepancy sW T ξ e') :
    e = e' := by
  obtain ⟨hWv, -, -, -, Z, hZ, hne, n, D, -, hξD, ha⟩ := h
  obtain ⟨-, -, -, -, Z', hZ', hne', n', D', -, hξD', ha'⟩ := h'
  obtain rfl : Z = Z' := by
    obtain ⟨D₀, -, hv₀, rfl⟩ := hZ
    obtain ⟨D₁, -, hv₁, rfl⟩ := hZ'
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv (hv₀.symm.trans hv₁)
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha'
    (comap_functionFieldMap_ι_injective _ (hξD.symm.trans hξD'))

/-! ### Two components through a centre off the exceptional locus -/

/-- A member of a regular system of parameters of a regular local ring is not in `𝔪²`. -/
private theorem notMem_sq_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R} (hz : IsRegularSystemOfParameters z)
    (m : Fin n) : z m ∉ IsLocalRing.maximalIdeal R ^ 2 := fun h => by
  haveI := IsRegularLocalRing.isDomain R
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero (MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m)) h
    (MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters hz m)

/-- A generator of the ideal of a component of an snc divisor at a point is not in `𝔪²`. -/
private theorem notMem_sq_of_isSNC {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} {T : Divisor W} (hT : T.IsSNC sW) (hsm : IsSmoothScheme sW)
    [LocallyOfFiniteType sW] {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ T.support) {w : W}
    (hw : w ∈ E.support) {z : W.presheaf.stalk w}
    (hz : IdealSheafData.stalk E.idealSheaf w = Ideal.span {z}) :
    z ∉ IsLocalRing.maximalIdeal (W.presheaf.stalk w) ^ 2 := by
  haveI : LocallyOfFinitePresentation sW :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sW)).mpr inferInstance
  haveI : Smooth sW := Aux.smooth_of_isSmoothScheme' sW hsm
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sW w
  haveI := IsRegularLocalRing.isDomain (W.presheaf.stalk w)
  obtain ⟨n, c, j, hc, -, hI⟩ := hT.2 w
  have h1 := notMem_sq_of_isRegularSystemOfParameters hc (j ⟨E, hE, hw⟩)
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz.symm.trans (hI ⟨E, hE, hw⟩))
  intro h
  exact h1 (hu ▸ Ideal.mul_mem_right _ _ h)

/-- In a weighted monomial ideal of weight `1`, a generator `z_j` of the maximal ideal outside
`𝔪²` has order exactly one. -/
private theorem isGreatest_weightedMonomialIdeal_one {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ι → R}
    (hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal R) (j : ι)
    (hj : z j ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsGreatest {m : ℕ | z j ∈ weightedMonomialIdeal z (fun _ => 1) m} 1 := by
  refine ⟨Ideal.subset_span ⟨Pi.single j 1, by simp, by simp [Pi.single_apply]⟩, fun m hm => ?_⟩
  by_contra h2
  refine hj (weightedMonomialIdeal_antitone z _ (show 2 ≤ m by simp at h2 ⊢; omega) hm |>
    fun h => (Ideal.span_le.2 ?_) h)
  rintro r ⟨β, hβ, rfl⟩
  have hmem : ∏ i, z i ^ β i ∈ ∏ i, IsLocalRing.maximalIdeal R ^ β i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hzm i) _
  rw [Finset.prod_pow_eq_pow_sum] at hmem
  exact Ideal.pow_le_pow_right (by simpa using hβ) hmem

/-- **Two components through a centre off the exceptional locus.** Let `(π, T)` be a log-smooth
datum of a terminal pair `(X, B)`, with log discrepancies `a_G` of the prime divisors of `W`, and
let `Z ⊆ W` be irreducible closed with generic point outside `Ex(π)`, contained in at least two
components of `T`. Then the components through `Z` have `∑ a_j > 1`: the monomial valuation of
weight `(1, …, 1)` at a component of their intersection is exceptional over `X`, with log
discrepancy `∑ a_j`. -/
private theorem one_lt_sum_of_two_le_card {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltTerminalPair sX B) {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    {Z : IrreducibleCloseds W}
    (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    (hJ : 2 ≤ (sncIndexSet T (Z : Set W)).card) :
    1 < ∑ j ∈ sncIndexSet T (Z : Set W), aT j := by
  classical
  haveI : IsAlgClosed k := hB.1.1.isAlgClosed
  haveI : CharZero k := hB.1.1.charZero
  obtain ⟨hX, -⟩ := hB.1.1.isPair
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : CompactSpace W := (hW.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : IsSeparated sX := hX.1.toIsSeparated
  set J := sncIndexSet T (Z : Set W) with hJdef
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set W) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hZη : (Z : Set W) = closure {η} :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def.symm
  have hJsub : ∀ E ∈ J, (Z : Set W) ⊆ E.support := fun E hE => (Finset.mem_filter.1 hE).2
  have hcl : IsClosed (⋂ E ∈ J, (E.support : Set W)) :=
    isClosed_biInter fun E _ => isClosed_support E
  have hηI : η ∈ ⋂ E ∈ J, (E.support : Set W) :=
    Set.mem_iInter₂.2 fun E hE => hJsub E hE hηZ
  obtain ⟨C, hC, hηC⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hcl).2 hηI)
  let Z₀ : IrreducibleCloseds W := ⟨C, hC.1.1, Aux.isClosed_of_mem_componentsOf hcl hC⟩
  have hZZ₀ : (Z : Set W) ⊆ Z₀ := by
    rw [hZη]
    exact closure_minimal (Set.singleton_subset_iff.2 hηC) Z₀.isClosed
  have hZ₀I : (Z₀ : Set W) ⊆ ⋂ E ∈ J, (E.support : Set W) := hC.1.2
  have hJ₀ : sncIndexSet T (Z₀ : Set W) = J := by
    ext E
    simp only [hJdef, sncIndexSet, Finset.mem_filter]
    refine ⟨fun ⟨hE, h⟩ => ⟨hE, hZZ₀.trans h⟩, fun ⟨hE, h⟩ => ⟨hE, fun x hx => ?_⟩⟩
    exact Set.mem_iInter₂.1 (hZ₀I hx) E (Finset.mem_filter.2 ⟨hE, h⟩)
  obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := Finset.one_lt_card.1 hJ
  have hprim : ∀ d : ℕ, (∀ j : J, d ∣ (fun _ => 1 : J → ℕ) j) → d = 1 :=
    fun d hd => Nat.dvd_one.1 (hd ⟨j₁, hj₁⟩)
  obtain ⟨ν, hν⟩ := exists_isMonomialValuationOfWeight (π ≫ sX) hW.1 hπ.isSmoothScheme T
    hπ.isReducedEffective hπ.isSNC J ⟨j₁, hj₁⟩ (Finset.filter_subset _ _) Z₀ hC (fun _ => 1)
    (fun _ => one_pos) hprim
  set η₀ := Z₀.isIrreducible.genericPoint
  have hη₀Z₀ : η₀ ∈ (Z₀ : Set W) := (Z₀.isIrreducible.isGenericPoint_genericPoint Z₀.isClosed).mem
  have hη₀ : ∀ E : J, η₀ ∈ E.1.support := fun E => Set.mem_iInter₂.1 (hZ₀I hη₀Z₀) E.1 E.2
  choose z hzp hz using fun E : J =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sX) hπ.isSmoothScheme E.1 (hη₀ E)
  have hνm := hν z hz
  have he₀ := isReducedSNCDiscrepancy_zero_of_isMonomialValuationOfWeight (π ≫ sX) hνm hprim
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨D', hD'p, hνD', hZ₀D'⟩, hval⟩ := hνm
  haveI := D'.isIntegral
  haveI := D'.isDominant
  haveI : IsProper D'.f := hD'p
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  have hbir : IsBirationalMorphism (D'.f ≫ π) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational π D'.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hπ.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D'.isBirationalMorphism)
  haveI := hbir.isDominant
  let D₀ : DivisorOver k sX :=
    ⟨D'.Y, D'.f ≫ π, by rw [Category.assoc]; exact D'.isNormalVariety, hbir, D'.E⟩
  have hD₀p : IsProper D₀.f := (inferInstance : IsProper (D'.f ≫ π))
  have hv₀ : D'.valuation.comap (functionFieldMap π) = D₀.valuation := by
    ext t
    change D'.E.divisorialValuation (functionFieldMap D'.f (functionFieldMap π t)) =
      D'.E.divisorialValuation (functionFieldMap (D'.f ≫ π) t)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  -- the centre of `ν` is off `Ex(π)` and has codimension at least two
  set p := D'.f D'.E.genericPoint
  have hpZ₀ : p ∈ (Z₀ : Set W) := by
    rw [hZ₀D', D'.center_eq_closure_genericPoint]; exact subset_closure rfl
  have hpη : p ⤳ η := by
    have : η ∈ (D'.center : Set W) := hZ₀D' ▸ hZZ₀ hηZ
    rwa [D'.center_eq_closure_genericPoint, ← specializes_iff_mem_closure] at this
  have hpEx : p ∉ (exceptionalSet π : Set W) := fun h =>
    hZ (hpη.mem_closed (exceptionalSet π).isClosed h)
  have hcod : codimension D₀.center = codimension D'.center :=
    codimension_center_eq_of_notMem_exceptionalSet D' D₀ hv₀ hpEx
  have h2 : 2 ≤ codimension D'.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    have key : ∀ E ∈ J, p ≠ E.genericPoint → 2 ≤ Order.coheight p := by
      intro E hE hne
      have hpE : p ∈ (E.support : Set W) := Set.mem_iInter₂.1 (hZ₀I hpZ₀) E hE
      have hle : p ≤ E.genericPoint := specializes_iff_mem_closure.mpr
        (by rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
      have hlt : p < E.genericPoint := lt_of_le_not_ge hle fun h => hne
        (Specializes.antisymm (show p ⤳ E.genericPoint from h)
          (show E.genericPoint ⤳ p from hle)).eq
      have h := Order.coheight_add_one_le hlt
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
      exact h
    by_cases h₁ : p = j₁.genericPoint
    · exact key j₂ hj₂ fun h => hj₁₂
        (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h₁.symm.trans h))
    · exact key j₁ hj₁ h₁
  have hex : D₀.IsExceptional := (isExceptional_iff_two_le_codimension hX D₀).2 (hcod ▸ h2)
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.1.isPair hK D₀
  have haν := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hD₀p
  have hterm := hB.2 n D₀ _ hex haν
  obtain ⟨Z', hZ', e', he', hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D₀ hD₀p haν ν (hνD' ▸ hv₀)
  obtain rfl : Z' = Z₀ := by
    obtain ⟨D'', -, hνD'', rfl⟩ := hZ'
    rw [hZ₀D']
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hW.1 (hνD''.symm.trans hνD')
  obtain rfl : e' = 0 := IsReducedSNCDiscrepancy.unique he' he₀
  have hmem : ∀ j : sncIndexSet T (Z₀ : Set W), j.1 ∈ J := fun j => hJ₀ ▸ j.2
  have hval1 : ∀ j : J, ν (algebraMap _ W.functionField (z j)) = WithZero.exp (-(1 : ℤ)) := by
    intro j
    obtain ⟨M, hM, hνM⟩ := hval (z j) (hzp j).ne_zero
    have h1 := isGreatest_weightedMonomialIdeal_one
      (fun i => (IsLocalRing.mem_maximalIdeal _).2 (hzp i).not_unit) j
      (notMem_sq_of_isSNC hπ.isSNC hπ.isSmoothScheme (Finset.mem_filter.1 j.2).1 (hη₀ j) (hz j))
    rw [hνM, hM.unique h1]
    rfl
  have hsum := hform (fun j => z ⟨j.1, hmem j⟩) (fun _ => 1) (fun j => hz ⟨j.1, hmem j⟩)
    (fun j => hval1 ⟨j.1, hmem j⟩)
  simp only [Int.cast_one, one_mul, add_zero] at hsum
  rw [Finset.sum_coe_sort (sncIndexSet T (Z₀ : Set W)) aT, hJ₀] at hsum
  rw [← hsum]
  exact hterm

/-! ### Components of `T` through a centre off the exceptional locus -/

/-- A morphism is injective on the points over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X W : Scheme.{u}} (π : W ⟶ X) {a b : W}
    (ha : π a ∈ MMP.Mori.biregularLocus π) (hab : π a = π b) : a = b := by
  haveI : IsIso (π ∣_ MMP.Mori.biregularLocus π) := MMP.Mori.isBiregular_biregularLocus π
  have ha' : a ∈ π ⁻¹ᵁ MMP.Mori.biregularLocus π := ha
  have hb' : b ∈ π ⁻¹ᵁ MMP.Mori.biregularLocus π := show π b ∈ _ from hab ▸ ha
  let pa : (π ⁻¹ᵁ MMP.Mori.biregularLocus π).toScheme := ⟨a, ha'⟩
  let pb : (π ⁻¹ᵁ MMP.Mori.biregularLocus π).toScheme := ⟨b, hb'⟩
  have h := (π ∣_ MMP.Mori.biregularLocus π).isOpenEmbedding.injective
    (a₁ := pa) (a₂ := pb) (Subtype.ext (by
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact hab))
  exact congrArg Subtype.val h

/-- A point of coheight one on a prime divisor is its generic point. -/
private theorem eq_genericPoint_of_coheight_eq_one {X : Scheme.{u}} (S : MMP.Mori.PrimeDivisor X)
    {p : X} (hp : p ∈ S.support) (h1 : Order.coheight p = 1) : p = S.genericPoint := by
  have hle : p ≤ S.genericPoint := specializes_iff_mem_closure.mpr
    (by rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
  by_contra hne
  have hlt : p < S.genericPoint := lt_of_le_not_ge hle fun h => hne
    (Specializes.antisymm (show p ⤳ S.genericPoint from h)
      (show S.genericPoint ⤳ p from hle)).eq
  have h := Order.coheight_add_one_le hlt
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, h1] at h
  exact absurd h (by decide)

section Components

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {π : W ⟶ X} {T : Divisor W}
  {D : Finset (MMP.Mori.PrimeDivisor X)}

/-- A prime divisor `S ∈ D` through `π(η)`, for `η` the generic point of `Z` off `Ex(π)`, lifts
to a component of `T` through `Z`, when `T` has support `Ex(π) ∪ π⁻¹(Supp D)`. -/
private theorem exists_mem_sncIndexSet_lift
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {S : MMP.Mori.PrimeDivisor X} (hSD : S ∈ D) (hS : π Z.isIrreducible.genericPoint ∈ S.support) :
    ∃ G ∈ sncIndexSet T (Z : Set W), π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf Z.isIrreducible.genericPoint =
        Ideal.map (π.stalkMap Z.isIrreducible.genericPoint).hom
          (IdealSheafData.stalk S.idealSheaf (π Z.isIrreducible.genericPoint)) := by
  classical
  have hηB : π Z.isIrreducible.genericPoint ∈ MMP.Mori.biregularLocus π := by
    by_contra h; exact hZ (MMP.Mori.mem_exceptionalSet.2 h)
  obtain ⟨G, hηG, hGS, hGI⟩ := exists_primeDivisor_lift π hηB S hS
  have hGT : G.genericPoint ∈ ⋃ E ∈ T.support, (E.support : Set W) := by
    rw [hT]
    refine Or.inr ?_
    rw [Set.mem_preimage, hGS, Finset.sup_set_eq_biUnion]
    exact Set.mem_iUnion₂.2 ⟨S, hSD, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
  obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.1 hGT
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen
  refine ⟨E, Finset.mem_filter.2 ⟨hE, ?_⟩, hGS, hGI⟩
  rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
  exact closure_minimal (Set.singleton_subset_iff.2 hηG) (isClosed_support E)

/-- A component of `T` through `Z`, for `Z` with generic point `η` off `Ex(π)`, lies over a prime
divisor `S ∈ D` through `π(η)`, its generic point going to that of `S`. -/
private theorem exists_genericPoint_eq_of_mem_sncIndexSet
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ sncIndexSet T (Z : Set W)) :
    E.genericPoint ∉ (exceptionalSet π : Set W) ∧ ∃ S ∈ D,
      π Z.isIrreducible.genericPoint ∈ S.support ∧ π E.genericPoint = S.genericPoint := by
  classical
  have hηZ := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hEgen : E.genericPoint ⤳ Z.isIrreducible.genericPoint := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (Finset.mem_filter.1 hE).2 hηZ
  have hEEx : E.genericPoint ∉ (exceptionalSet π : Set W) := fun h =>
    hZ (hEgen.mem_closed (exceptionalSet π).isClosed h)
  have hET : E.genericPoint ∈ ⋃ E ∈ T.support, (E.support : Set W) :=
    Set.mem_iUnion₂.2 ⟨E, (Finset.mem_filter.1 hE).1,
      MMP.Flips.primeDivisor_genericPoint_mem_support E⟩
  rw [hT] at hET
  rcases hET with hET | hET
  · exact absurd hET hEEx
  rw [Set.mem_preimage, Finset.sup_set_eq_biUnion] at hET
  obtain ⟨S, hSD, hES⟩ := Set.mem_iUnion₂.1 hET
  have hEB : π E.genericPoint ∈ MMP.Mori.biregularLocus π := by
    by_contra h; exact hEEx (MMP.Mori.mem_exceptionalSet.2 h)
  have h1 : Order.coheight (π E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus π hEB]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  have hES' := eq_genericPoint_of_coheight_eq_one S hES h1
  refine ⟨hEEx, S, hSD, ?_, hES'⟩
  exact (hEgen.map π.continuous).mem_closed (isClosed_support S) hES

end Components

/-! ### The one-label smooth locus below a centre off the exceptional locus -/

/-- At a point where `𝒪_{Y,y} ⧸ I_{S,y}` is regular, the prime divisor `S` is regular. -/
private theorem notMem_image_singularLocus_of_isRegularLocalRing_quotient {Y : Scheme.{u}}
    (S : MMP.Mori.PrimeDivisor Y) {y : Y}
    (h : IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk S.idealSheaf y)) :
    y ∉ S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme := by
  rintro ⟨z, hz, rfl⟩
  exact hz (IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z))

/-- At a point of a smooth prime divisor `G`, the ring `𝒪_{W,w} ⧸ I_{G,w}` is regular. -/
private theorem isRegularLocalRing_quotient_of_isSmoothScheme {k : Type u} [Field k]
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW]
    (G : MMP.Mori.PrimeDivisor W) (hG : IsSmoothScheme (G.idealSheaf.subschemeι ≫ sW)) {w : W}
    (hw : w ∈ G.support) :
    IsRegularLocalRing (W.presheaf.stalk w ⧸ IdealSheafData.stalk G.idealSheaf w) := by
  obtain ⟨z, rfl⟩ : w ∈ Set.range G.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  haveI : LocallyOfFinitePresentation (G.idealSheaf.subschemeι ≫ sW) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := G.idealSheaf.subschemeι ≫ sW)).mpr inferInstance
  haveI : Smooth (G.idealSheaf.subschemeι ≫ sW) := Aux.smooth_of_isSmoothScheme' _ hG
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (G.idealSheaf.subschemeι ≫ sW) z
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z).symm

/-- **A centre on exactly one component and off the exceptional locus lies over `Y°`.** Let
`(π, T)` be a log-smooth datum whose divisor `T` has support `Ex(π) ∪ π⁻¹(Supp L)`, and let the
generic point `η` of `Z ⊆ W` lie off `Ex(π)` on exactly one component `G` of `T`. Then `π(η)`
lies in the one-label smooth locus of `(X, L)`, on a label `P`, the only label through `π(η)`. -/
private theorem mem_oneLabelSmoothLocus_of_sncIndexSet_eq_singleton {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) {L : Finset (MMP.Mori.PrimeDivisor X)}
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (L.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {G : MMP.Mori.PrimeDivisor W} (hJ : sncIndexSet T (Z : Set W) = {G}) :
    π Z.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧
      ∃ P ∈ L, π Z.isIrreducible.genericPoint ∈ P.support ∧
        ∀ S ∈ L, π Z.isIrreducible.genericPoint ∈ S.support → S = P := by
  classical
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (π ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := π ≫ sX)).mpr inferInstance
  haveI : Smooth (π ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hπ.isSmoothScheme
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set W) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hηB : π η ∈ MMP.Mori.biregularLocus π := by
    by_contra h; exact hZ (MMP.Mori.mem_exceptionalSet.2 h)
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus π hηB
  let e : X.presheaf.stalk (π η) ≃+* W.presheaf.stalk η :=
    (asIso (π.stalkMap η)).commRingCatIsoToRingEquiv
  have hGT : G ∈ sncIndexSet T (Z : Set W) := hJ ▸ Finset.mem_singleton_self G
  -- a label through `π(η)` lifts to `G`
  have hlift : ∀ S ∈ L, π η ∈ S.support → π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf η =
        Ideal.map (π.stalkMap η).hom (IdealSheafData.stalk S.idealSheaf (π η)) := by
    intro S hSL hS
    obtain ⟨G', hG'J, hG'⟩ := exists_mem_sncIndexSet_lift hT hZ hSL hS
    rw [hJ, Finset.mem_singleton] at hG'J
    exact hG'J ▸ hG'
  obtain ⟨-, P, hPL, hηP, -⟩ := exists_genericPoint_eq_of_mem_sncIndexSet hT hZ hGT
  have huniq : ∀ S ∈ L, π η ∈ S.support → S = P := fun S hSL hS =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hlift S hSL hS).1.symm.trans (hlift P hPL hηP).1)
  refine ⟨?_, P, hPL, hηP, huniq⟩
  rw [mem_oneLabelSmoothLocus_iff]
  refine ⟨?_, fun S hSL => ?_, fun S hSL S' hS'L hne h => hne ?_⟩
  · haveI := isRegularLocalRing_stalk_of_smooth_over_field (π ≫ sX) η
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · by_cases hS : π η ∈ S.support
    · refine notMem_image_singularLocus_of_isRegularLocalRing_quotient S ?_
      haveI := isRegularLocalRing_quotient_of_isSmoothScheme G
        (hπ.isSNC.1 G (Finset.mem_filter.1 hGT).1) ((Finset.mem_filter.1 hGT).2 hηZ)
      exact IsRegularLocalRing.of_ringEquiv
        (Ideal.quotientEquiv _ _ e (hlift S hSL hS).2).symm
    · rintro ⟨z, -, hz⟩
      refine hS ?_
      have : S.idealSheaf.subschemeι z ∈ Set.range S.idealSheaf.subschemeι := ⟨z, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι, hz] at this
      exact this
  · exact (huniq S hSL h.1).trans (huniq S' hS'L h.2).symm

/-- A centre whose generic point lies in `Ex(π)`, of pure codimension one and covered by `T`, lies
on a component of `T` whose generic point is in `Ex(π)`. -/
private theorem exists_mem_sncIndexSet_of_mem_exceptionalSet {X W : Scheme.{u}} [NoetherianSpace W]
    {π : W ⟶ X} {T : Divisor W} (hpure : IsPureCodimOne (exceptionalSet π))
    (hT : (exceptionalSet π : Set W) ⊆ ⋃ E ∈ T.support, (E.support : Set W))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∈ (exceptionalSet π : Set W)) :
    ∃ E ∈ sncIndexSet T (Z : Set W), E.genericPoint ∈ (exceptionalSet π : Set W) := by
  classical
  obtain ⟨E, hηE, hEsub⟩ := exists_primeDivisor_mem_support_subset hpure hZ
  have hEgen := hEsub (MMP.Flips.primeDivisor_genericPoint_mem_support E)
  obtain ⟨E', hE', hgen⟩ := Set.mem_iUnion₂.1 (hT hEgen)
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen
  refine ⟨E', Finset.mem_filter.2 ⟨hE', ?_⟩, hEgen⟩
  rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
  exact closure_minimal (Set.singleton_subset_iff.2 hηE) (isClosed_support E')

/-- A component through a centre met by exactly two components `G₀, G₁` is one of them. -/
private theorem eq_or_eq_of_sncIndexSet_eq_pair {W : Scheme.{u}} {T : Divisor W} {Z : Set W}
    [DecidableEq (MMP.Mori.PrimeDivisor W)] {G₀ G₁ : MMP.Mori.PrimeDivisor W}
    (hJ : sncIndexSet T Z = {G₀, G₁})
    (i : sncIndexSet T Z) : i.1 = G₀ ∨ i.1 = G₁ := by
  simpa [hJ] using i.2

/-! ### Echo ideals as monomial ideals -/

section EchoAlgebra

variable {R : Type*} [CommRing R]

/-- The ideal generated by the monomials `t^a x^b` of weight `a + j b ≥ n`. -/
private def pairMonomialIdeal (t x : R) (j n : ℕ) : Ideal R :=
  Ideal.span {r | ∃ a b : ℕ, n ≤ a + j * b ∧ r = t ^ a * x ^ b}

private theorem pairMonomialIdeal_def (t x : R) (j n : ℕ) :
    pairMonomialIdeal t x j n = Ideal.span {r | ∃ a b : ℕ, n ≤ a + j * b ∧ r = t ^ a * x ^ b} :=
  rfl

/-- Powers of `𝔪 = (x, t)` are generated by the monomials of degree at least the exponent. -/
private theorem pow_le_pairMonomialIdeal_one {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) (c : ℕ) : 𝔪 ^ c ≤ pairMonomialIdeal t x 1 c := by
  induction c with
  | zero =>
    intro r _
    have h1 : (1 : R) ∈ pairMonomialIdeal t x 1 0 := by
      rw [pairMonomialIdeal_def]
      exact Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩
    simpa using Ideal.mul_mem_left (pairMonomialIdeal t x 1 0) r h1
  | succ c ih =>
    calc 𝔪 ^ (c + 1) = 𝔪 ^ c * 𝔪 := pow_succ _ _
      _ ≤ pairMonomialIdeal t x 1 c * Ideal.span {x, t} := Ideal.mul_mono ih h𝔪.ge
      _ ≤ pairMonomialIdeal t x 1 (c + 1) := ?_
    rw [pairMonomialIdeal_def, pairMonomialIdeal_def, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨a, b, hab, rfl⟩, s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact Ideal.subset_span ⟨a, b + 1, by omega, by ring⟩
    · exact Ideal.subset_span ⟨a + 1, b, by omega, by ring⟩

/-- If `𝔪 = (x, t)` and `j ≥ 1`, the echo ideal `∑_b x^b 𝔪^{n - jb}` is generated by the
monomials `t^a x^b` with `a + j b ≥ n`. -/
private theorem echoIdeal_eq_pairMonomialIdeal {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    echoIdeal x 𝔪 j n = pairMonomialIdeal t x j n := by
  refine le_antisymm (iSup_le fun b => ?_) ?_
  · refine (Ideal.mul_mono_right (pow_le_pairMonomialIdeal_one h𝔪 _)).trans ?_
    rw [pairMonomialIdeal_def, pairMonomialIdeal_def, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, rfl, _, ⟨a', b', h, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨a', b + b', ?_, by ring⟩
    have : b' ≤ j * b' := Nat.le_mul_of_pos_left b' hj
    rw [Nat.mul_add]
    omega
  · rw [pairMonomialIdeal_def]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.mem_iSup_of_mem b ?_
    rw [mul_comm (t ^ a)]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (Ideal.pow_le_pow_right (show n - j * b ≤ a by omega) (Ideal.pow_mem_pow ?_ a))
    exact h𝔪 ▸ Ideal.subset_span (by simp)

/-- A weighted monomial ideal on two variables `z i₀, z i₁` is generated by the monomials
`z i₁^a z i₀^b` of weight `a α_{i₁} + b α_{i₀} ≥ n`. -/
private theorem weightedMonomialIdeal_eq_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i₀ i₁ : ι} (h01 : i₀ ≠ i₁) (huniv : ∀ i, i = i₀ ∨ i = i₁) (z : ι → R) (α : ι → ℕ)
    (n : ℕ) :
    weightedMonomialIdeal z α n =
      Ideal.span {r | ∃ a b : ℕ, n ≤ α i₁ * a + α i₀ * b ∧ r = z i₁ ^ a * z i₀ ^ b} := by
  have huniv' : (Finset.univ : Finset ι) = {i₀, i₁} := by
    ext i; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact huniv i
  have hsum : ∀ β : ι → ℕ, ∑ i, α i * β i = α i₀ * β i₀ + α i₁ * β i₁ := fun β => by
    rw [huniv', Finset.sum_pair h01]
  have hprod : ∀ β : ι → ℕ, ∏ i, z i ^ β i = z i₀ ^ β i₀ * z i₁ ^ β i₁ := fun β => by
    rw [huniv', Finset.prod_pair h01]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨β, hβ, rfl⟩
    refine Ideal.subset_span ⟨β i₁, β i₀, by rw [hsum] at hβ; omega, by rw [hprod]; ring⟩
  · rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.subset_span ⟨fun i => if i = i₀ then b else a, ?_, ?_⟩
    · have e := hsum (fun i => if i = i₀ then b else a)
      beta_reduce at e
      rw [if_pos rfl, if_neg h01.symm] at e
      rw [e]; omega
    · have e := hprod (fun i => if i = i₀ then b else a)
      beta_reduce at e
      rw [if_pos rfl, if_neg h01.symm] at e
      rw [e]; ring

/-- The image of `pairMonomialIdeal t x j n` under a ring homomorphism. -/
private theorem map_pairMonomialIdeal {S : Type*} [CommRing S] (φ : R →+* S) (t x : R)
    (j n : ℕ) :
    (pairMonomialIdeal t x j n).map φ = pairMonomialIdeal (φ t) (φ x) j n := by
  rw [pairMonomialIdeal_def, pairMonomialIdeal_def, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨a, b, h, rfl⟩, rfl⟩
    exact ⟨a, b, h, by simp⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨_, ⟨a, b, h, rfl⟩, by simp⟩

end EchoAlgebra

/-! ### Echo values from a monomial valuation over the biregular locus -/

open Classical in
/-- **Echo values from a monomial valuation.** Let `π : W ⟶ Y` induce an isomorphism
`𝒪_{Y,y} ≅ 𝒪_{W,w}` with `π(w) = y`, where `w` is the generic point of `Z ⊆ W` and exactly two
components `G_P ≠ G_L` of `T` pass through `Z`, their ideals at `w` the images of those of the
prime divisors `P`, `L'` of `Y`. Let `x`, `t` be local equations of `P`, `L'` at `y` with
`𝔪_y = (x, t)`. If `ξ_W` is monomial of weight `(j, 1)` at `Z` for `G_P + G_L`, then
`ξ = π_* ξ_W` satisfies the echo formula `ξ(f) = max {n : f ∈ ∑_b x^b 𝔪^{n - jb}}` on
`𝒪_{Y,y}`. -/
private theorem isEchoValue_of_isMonomialValuationOfWeight {k : Type u} [Field k]
    {Y W : Scheme.{u}} [IsIntegral Y] [IsIntegral W] {sW : W ⟶ Spec (.of k)} (π : W ⟶ Y)
    [IsDominant π] {T : Divisor W} {Z : IrreducibleCloseds W} (w : W)
    (hw : Z.isIrreducible.genericPoint = w) (y : Y) (hy : π w = y) (hiso : IsIso (π.stalkMap w))
    {Gx Gt : MMP.Mori.PrimeDivisor W} (hne : Gx ≠ Gt)
    (hJ : sncIndexSet T (Z : Set W) = {Gx, Gt}) {P L' : MMP.Mori.PrimeDivisor Y}
    (hGx : IdealSheafData.stalk Gx.idealSheaf w =
      Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk P.idealSheaf (π w)))
    (hGt : IdealSheafData.stalk Gt.idealSheaf w =
      Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk L'.idealSheaf (π w)))
    {x t : Y.presheaf.stalk y} (hx : IdealSheafData.stalk P.idealSheaf y = Ideal.span {x})
    (ht : IdealSheafData.stalk L'.idealSheaf y = Ideal.span {t})
    (hxt : Ideal.span {x, t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) {j : ℕ}
    (hj : 1 ≤ j) {ξW : Valuation W.functionField ℤᵐ⁰} {α : sncIndexSet T (Z : Set W) → ℕ}
    (hαP : ∀ i, i.1 = Gx → α i = j) (hαL : ∀ i, i.1 = Gt → α i = 1)
    (hmono : ∀ z : sncIndexSet T (Z : Set W) → W.presheaf.stalk Z.isIrreducible.genericPoint,
      (∀ i, IdealSheafData.stalk i.1.idealSheaf Z.isIrreducible.genericPoint =
        Ideal.span {z i}) →
        IsMonomialValuationOfWeight sW T (sncIndexSet T (Z : Set W)) Z z α ξW) :
    ∀ f : Y.presheaf.stalk y, f ≠ 0 → ∃ M : ℕ,
      IsGreatest {n : ℕ | f ∈ echoIdeal x (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) j n}
        M ∧
      ξW.comap (functionFieldMap π) (algebraMap _ Y.functionField f) =
        WithZero.exp (-(M : ℤ)) := by
  classical
  subst hw
  subst hy
  let φ := (π.stalkMap Z.isIrreducible.genericPoint).hom
  have hbij : Function.Bijective φ :=
    (asIso (π.stalkMap Z.isIrreducible.genericPoint)).commRingCatIsoToRingEquiv.bijective
  have hGxJ : Gx ∈ sncIndexSet T (Z : Set W) := by rw [hJ]; simp
  have hGtJ : Gt ∈ sncIndexSet T (Z : Set W) := by rw [hJ]; simp
  let i₀ : sncIndexSet T (Z : Set W) := ⟨Gx, hGxJ⟩
  let i₁ : sncIndexSet T (Z : Set W) := ⟨Gt, hGtJ⟩
  have h01 : i₀ ≠ i₁ := fun h => hne (congrArg Subtype.val h)
  have huniv : ∀ i, i = i₀ ∨ i = i₁ := fun i =>
    (eq_or_eq_of_sncIndexSet_eq_pair hJ i).imp Subtype.ext Subtype.ext
  let z : sncIndexSet T (Z : Set W) → W.presheaf.stalk Z.isIrreducible.genericPoint :=
    fun i => if i = i₀ then φ x else φ t
  have hz₀ : z i₀ = φ x := if_pos rfl
  have hz₁ : z i₁ = φ t := if_neg h01.symm
  have hz : ∀ i,
      IdealSheafData.stalk i.1.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z i} := by
    intro i
    rcases huniv i with rfl | rfl
    · rw [hz₀]
      change IdealSheafData.stalk Gx.idealSheaf Z.isIrreducible.genericPoint = _
      rw [hGx, hx, Ideal.map_span, Set.image_singleton]
    · rw [hz₁]
      change IdealSheafData.stalk Gt.idealSheaf Z.isIrreducible.genericPoint = _
      rw [hGt, ht, Ideal.map_span, Set.image_singleton]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hval⟩ := hmono z hz
  have hα₀ : α i₀ = j := hαP i₀ rfl
  have hα₁ : α i₁ = 1 := hαL i₁ rfl
  have hideal : ∀ n, weightedMonomialIdeal z α n =
      (echoIdeal x (IsLocalRing.maximalIdeal _) j n).map φ := by
    intro n
    rw [weightedMonomialIdeal_eq_of_pair h01 huniv, echoIdeal_eq_pairMonomialIdeal hxt hj,
      map_pairMonomialIdeal, pairMonomialIdeal_def, hz₀, hz₁, hα₀, hα₁]
    congr 1
    ext r
    simp only [Set.mem_setOf_eq, one_mul]
  intro f hf
  have hφf : φ f ≠ 0 := fun h => hf (hbij.1 (h.trans (map_zero φ).symm))
  obtain ⟨M, hM, hξM⟩ := hval (φ f) hφf
  refine ⟨M, ?_, ?_⟩
  · have hset : {n : ℕ | f ∈ echoIdeal x (IsLocalRing.maximalIdeal _) j n} =
        {n : ℕ | φ f ∈ weightedMonomialIdeal z α n} := by
      ext n
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hideal, ← Ideal.mem_comap,
        Ideal.comap_map_of_bijective _ hbij]
    rw [hset]
    exact hM
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hξM

/-! ### Valuations of small log discrepancy at a curve of the one-label smooth locus -/

/-- **Below log discrepancy two, a valuation centred at a curve of `Y°` is an echo.** Let `(Y, Θ)`
be a terminal pair on a normal threefold, `L ⊇ Supp Θ` a finite set of labels, and `ξ = v_D` a
normalized divisorial valuation with `a(ξ; Y, Θ) < 2` whose centre is a curve `V ⊆ P`, `P ∈ L`,
with generic point in `Y°`. Complete a local equation `x` of `P` at `η_V` to a regular system of
parameters `(x, t)`, with `t` a local equation of a prime divisor `L'`, and take a log resolution
`π : W ⟶ Y` of `(Y, L + L')` which is an isomorphism over `η_V`. The two components of the
log-smooth formula give `a(ξ; Y, Θ) = ξ(x)(1 - b_P) + ξ(t) + e_T(ξ)`, so `ξ(t) = 1`,
`e_T(ξ) = 0`, and `ξ` is monomial of weight `(ξ(x), 1)`: an echo of order `ξ(x)` of `P` at
`V`. -/
private theorem exists_isEcho_of_mem_oneLabelSmoothLocus {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ) {L : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsupp : Θ.support ⊆ L) (hdim : topologicalKrullDim Y = 3)
    {D : DivisorOver k sY} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) D a) (ha2 : a < 2)
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∈ L) (hVP : (D.center : Set Y) ⊆ P.support)
    (hV : topologicalKrullDim (D.center : Set Y) = 1)
    (hη : D.center.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) :
    ∃ j, IsEcho sY L P D.center j D.valuation := by
  classical
  haveI : IsAlgClosed k := hΘ.1.1.isAlgClosed
  haveI : CharZero k := hΘ.1.1.charZero
  have hY : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  set V := D.center with hVdef
  set y := V.isIrreducible.genericPoint with hydef
  have hyV : y ∈ (V : Set Y) := (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hyP : y ∈ P.support := hVP hyV
  haveI hreg : IsRegularLocalRing (Y.presheaf.stalk y) := (mem_oneLabelSmoothLocus_iff.mp hη).1
  -- a local equation `x` of `P` at `η_V`, and its completion `t`
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hyP
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk y)
  obtain ⟨x, hxq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
  have hx : IdealSheafData.stalk P.idealSheaf y = Ideal.span {x} := hq.trans hxq
  obtain ⟨⟨t, ht, U, hyU, hUL, hUS, xU, tU, hxU, htU, SU, LU, Zu, hSU, hSUx, hLUt, hne, hsnc,
    hZu, hZmax⟩, -⟩ := isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation sY L P
      V 1 hY hdim hP hVP hV hη le_rfl x hx
  have hxt : Ideal.span {x, t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    have := ht.1
    rwa [Matrix.range_cons_cons_empty] at this
  set u : U.toScheme := ⟨y, hyU⟩ with hu
  have huZ : u ∈ (Zu : Set U.toScheme) := by rw [hZu]; exact hyV
  have huLU : u ∈ LU.support := (hZmax.1.2 huZ).2
  -- the prime divisor `L' = {t = 0}` of `Y`
  set L' := OpenWeilRestriction.primeDivisorMap U.ι LU with hL'def
  have hL'supp : ∀ v : U.toScheme, U.ι v ∈ L'.support ↔ v ∈ LU.support :=
    MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι LU
  have hyL' : y ∈ L'.support := (hL'supp u).2 huLU
  have ht' : IdealSheafData.stalk L'.idealSheaf y = Ideal.span {t} := by
    have h1 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map U.ι L'.idealSheaf u
    rw [MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap, hLUt u, ← htU] at h1
    let φ : Y.presheaf.stalk (U.ι u) →+* U.toScheme.presheaf.stalk u := (U.ι.stalkMap u).hom
    have hbij : Function.Bijective φ :=
      (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv.bijective
    let t' : Y.presheaf.stalk (U.ι u) := t
    have h2 : Ideal.map φ (Ideal.span {t'}) =
        Ideal.map φ (IdealSheafData.stalk L'.idealSheaf (U.ι u)) := by
      rw [Ideal.map_span, Set.image_singleton]
      exact h1
    have h3 := congrArg (Ideal.comap φ) h2
    rw [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h3
    exact h3.symm
  have hL'L : L' ∉ L := by
    intro h
    have h1 : L' = P := eq_of_mem_oneLabelSmoothLocus hη h hP hyL' hyP
    have h2 : LU.genericPoint ∈ SU.support := by
      have h3 : U.ι LU.genericPoint ∈ L'.support :=
        (hL'supp _).2 (MMP.Flips.primeDivisor_genericPoint_mem_support LU)
      rw [h1] at h3
      rw [hSU]
      exact h3
    exact hne (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support h2)
  have hcoeff : Θ.coeff L' = 0 := by
    by_contra h
    exact hL'L (hsupp (by rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]))
  -- a log resolution of `(Y, L + L')`, an isomorphism over `U`
  have hsupp' : Θ.support ⊆ insert L' L := hsupp.trans (Finset.subset_insert _ _)
  obtain ⟨W, π, T, hπ, -, hT, hiso⟩ := exists_isLogSmoothDatum hΘ.1 (insert L' L) hsupp'
  have hUsm : IsSmoothScheme (U.ι ≫ sY) := by
    haveI : LocallyOfFinitePresentation (U.ι ≫ sY) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sY)).mpr inferInstance
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, eq_top_iff]
    intro v _
    refine ((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (U.ι ≫ sY)).1 v).2 ?_
    haveI : IsRegularLocalRing (Y.presheaf.stalk (U.ι v)) :=
      (mem_oneLabelSmoothLocus_iff.mp (hUL v.2)).1
    exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap v)).commRingCatIsoToRingEquiv
  have hpre : U.ι ⁻¹' ((insert L' L).sup fun E => (E.idealSheaf.support : Set Y)) =
      ⋃ F ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support,
        (F.support : Set U.toScheme) := by
    rw [MMP.Intersection.support_reducedDivisorOf]
    ext v
    simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂, Finset.mem_insert,
      Finset.mem_singleton, exists_prop]
    constructor
    · rintro ⟨S, hS, hvS⟩
      rcases hS with rfl | hSL
      · exact ⟨LU, Or.inr rfl, (hL'supp v).1 hvS⟩
      · by_cases hSP : S = P
        · subst hSP
          refine ⟨SU, Or.inl rfl, ?_⟩
          rw [hSU]
          exact hvS
        · exact absurd hvS (Set.disjoint_left.1 (hUS S hSL hSP) v.2)
    · rintro ⟨F, hF, hvF⟩
      rcases hF with rfl | rfl
      · refine ⟨P, Or.inr hP, ?_⟩
        rw [hSU] at hvF
        exact hvF
      · exact ⟨L', Or.inl rfl, (hL'supp v).2 hvF⟩
  have hUsnc : IsSNCClosedSubset (U.ι ≫ sY)
      (U.ι ⁻¹' ((insert L' L).sup fun E => (E.idealSheaf.support : Set Y))) := by
    rw [hpre]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hsnc
  have hUiso := hiso U hUsm hUsnc
  have hyB : y ∈ MMP.Mori.biregularLocus π := MMP.Mori.le_biregularLocus hUiso hyU
  -- the log-smooth formula on `W`
  obtain ⟨n₂, K₂, hK₂, aT, haT, hpos, -, hval⟩ := exists_logDiscrepancy_primeDivisor hΘ hπ
  obtain rfl : n = n₂ := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK₂.topologicalKrullDim_eq
  have hWv : IsNormalVariety k (π ≫ sY) := hπ.isNormalVariety
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hWv.2
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨D', -, hΦ, e0, he, hrest⟩ := exists_logSmoothFormula_at_centre hπ aT haT ha
  set η := D'.center.isIrreducible.genericPoint
  obtain ⟨z, m, hz, hm1, hm, hform'⟩ := hrest
  have hπη : π η = y := map_genericPoint_center_eq_of_comap_eq D' D hΦ
  have hηB : π η ∈ MMP.Mori.biregularLocus π := by rw [hπη]; exact hyB
  have hηEx : η ∉ (exceptionalSet π : Set W) := fun h => (MMP.Mori.mem_exceptionalSet.1 h) hηB
  -- the components of `T` through the centre are the lifts of `P` and `L'`
  obtain ⟨Gx, hGxJ, hGxgen, hGxI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_of_mem hP) (by rw [hπη]; exact hyP)
  obtain ⟨Gt, hGtJ, hGtgen, hGtI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_self L' L) (by rw [hπη]; exact hyL')
  have hPL' : P ≠ L' := fun h => hL'L (h ▸ hP)
  have hGxGt : Gx ≠ Gt := fun h => hPL' (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hGxgen.symm.trans ((congrArg (fun G => π G.genericPoint) h).trans hGtgen)))
  have hJ : sncIndexSet T (D'.center : Set W) = {Gx, Gt} := by
    ext E
    rw [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hE => ?_, fun h => h.elim (fun h => h ▸ hGxJ) (fun h => h ▸ hGtJ)⟩
    obtain ⟨hEEx, S, hSD, hηS, hES⟩ := exists_genericPoint_eq_of_mem_sncIndexSet hT hηEx hE
    have hEB : π E.genericPoint ∈ MMP.Mori.biregularLocus π := by
      by_contra h; exact hEEx (MMP.Mori.mem_exceptionalSet.2 h)
    rw [Finset.mem_insert] at hSD
    rcases hSD with rfl | hSL
    · exact Or.inr (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_of_mem_biregularLocus π hEB (hES.trans hGtgen.symm)))
    · have hSP : S = P := eq_of_mem_oneLabelSmoothLocus hη hSL hP (by rw [← hπη]; exact hηS) hyP
      subst hSP
      exact Or.inl (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_of_mem_biregularLocus π hEB (hES.trans hGxgen.symm)))
  -- the formula has the two terms `ξ(x) (1 - b_P)` and `ξ(t)`
  let i₀ : sncIndexSet T (D'.center : Set W) := ⟨Gx, hGxJ⟩
  let i₁ : sncIndexSet T (D'.center : Set W) := ⟨Gt, hGtJ⟩
  have h01 : i₀ ≠ i₁ := fun h => hGxGt (congrArg Subtype.val h)
  have huniv : ∀ i, i = i₀ ∨ i = i₁ := fun i =>
    (eq_or_eq_of_sncIndexSet_eq_pair hJ i).imp Subtype.ext Subtype.ext
  have hsum : ∑ j, (m j : ℝ) * aT j = m i₀ * aT Gx + m i₁ * aT Gt :=
    Fintype.sum_eq_add i₀ i₁ h01 fun i hi => ((huniv i).elim hi.1 hi.2).elim
  have haGt : aT Gt = 1 := by rw [hval Gt L' hGtgen, hcoeff]; simp
  have hm₀ : (1 : ℝ) ≤ m i₀ := by exact_mod_cast hm1 i₀
  have hm₁' : (1 : ℝ) ≤ m i₁ := by exact_mod_cast hm1 i₁
  have hpos₀ := hpos Gx
  rw [hsum, haGt] at hform'
  have hlt : (m i₁ : ℝ) + e0 < 2 := by nlinarith
  have hm₁ : m i₁ = 1 := by
    have : (m i₁ : ℝ) < 2 := by linarith [(e0.cast_nonneg : (0 : ℝ) ≤ e0)]
    have : m i₁ < 2 := by exact_mod_cast this
    have := hm1 i₁
    omega
  have he0 : e0 = 0 := by
    rw [hm₁] at hlt
    have : (e0 : ℝ) < 1 := by push_cast at hlt; linarith
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  subst he0
  have he' : IsReducedSNCDiscrepancy (π ≫ sY) T D'.valuation 0 := by simpa using he
  -- the zero-error valuation is monomial of weight `(ξ(x), 1)`
  obtain ⟨Z₃, hZ₃, -, α, -, hall⟩ :=
    IsReducedSNCDiscrepancy.isMonomialValuationOfWeight_of_eq_zero he'
  obtain rfl : Z₃ = D'.center := by
    obtain ⟨D'', -, hv'', rfl⟩ := hZ₃
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv.1 hv''.symm
  have hαm : ∀ j, (α j : ℤ) = m j := fun j => by
    have h1 := (hall z hz).1 j
    rw [hm j] at h1
    have h2 := WithZero.exp_injective h1
    omega
  have hα₁ : α i₁ = 1 := by
    have := hαm i₁
    rw [hm₁] at this
    exact_mod_cast this
  have hjj : 1 ≤ α i₀ := by
    have := hαm i₀
    have := hm1 i₀
    omega
  have hecho := isEchoValue_of_isMonomialValuationOfWeight π η rfl y hπη
    (MMP.isIso_stalkMap_of_mem_biregularLocus π hηB) hGxGt hJ hGxI hGtI hx ht' hxt hjj
    (fun i hi => by rw [show i = i₀ from Subtype.ext hi])
    (fun i hi => by rw [show i = i₁ from Subtype.ext hi]; exact hα₁) (fun z' hz' => (hall z' hz').2)
  refine ⟨α i₀, hY, hdim, hP, hVP, hV, hη, hjj, ⟨D, ha.2.1, rfl, rfl⟩, x, hx, fun f hf => ?_⟩
  obtain ⟨M, hM, hξM⟩ := hecho f hf
  exact ⟨M, hM, hΦ ▸ hξM⟩

/-! ### Finiteness -/

open MMP.Mori MMP.Fourfold in
/-- **Finitely many non-echoes below log discrepancy two.** Let `(Y, Θ)` be a terminal pair on a
projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors containing
the support of `Θ`. Then the normalized divisorial valuations `ξ` of `ℂ(Y)`, exceptional over
`Y`, with `a(ξ; Y, Θ) < 2`, which are not an echo (`MMP.Fourfold.IsEcho`) of any order of any
label `S ∈ L` at any curve, form a finite set. -/
private theorem _root_.MMP.Fourfold.finite_setOf_not_isEcho
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (_hY : MMP.Mori.IsProjectiveVariety ℂ sY) (_hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sY ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ sY ξ ∧
        (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          IsEcho sY L S V j ξ}.Finite := by
  classical
  have hY : IsNormalVariety ℂ sY := hΘ.1.1.isPair.1
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  obtain ⟨W, π, T, hπ, hpure, hT, -⟩ := exists_isLogSmoothDatum hΘ.1 L hsupp
  obtain ⟨n, K, hK, aT, haT, hpos, hexc, -⟩ := exists_logDiscrepancy_primeDivisor hΘ hπ
  have hWv : IsNormalVariety ℂ (π ≫ sY) := hπ.isNormalVariety
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hWv.2
  haveI : CompactSpace W := (hWv.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  haveI := hπ.isBirationalMorphism.isDominant
  set M : ℕ := ⌈∑ j ∈ T.support, 2 / aT j⌉₊ + 1 with hM
  refine ((finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sY) T (M := M)
    (Nat.le_add_left 1 _)).image fun ξ => ξ.comap (functionFieldMap π)).subset ?_
  rintro ξ ⟨-, ⟨D₀, -, hξD₀, hcod⟩, ⟨a, ha2, n', D, hDξ, ha⟩, hnot⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  -- the log-smooth formula at the centre `c_W(ξ)`, with `ξ(Tⱼ) = mⱼ ≥ 1`
  obtain ⟨D', hZ₀, hΦ, e0, he, hrest⟩ := exists_logSmoothFormula_at_centre hπ aT haT ha
  refine ⟨D'.valuation, ?_, hΦ.trans hDξ⟩
  set η := D'.center.isIrreducible.genericPoint
  obtain ⟨z, m, hz, hm1, hm, hform'⟩ := hrest
  have hgen : η = D'.f D'.E.genericPoint := genericPoint_center_eq D'
  have hterm : ∀ j : sncIndexSet T (D'.center : Set W), 0 ≤ (m j : ℝ) * aT j := fun j =>
    mul_nonneg (by exact_mod_cast (zero_le_one.trans (hm1 j))) (hpos j).le
  have hle1 : ∀ j : sncIndexSet T (D'.center : Set W), aT j ≤ (m j : ℝ) * aT j := fun j =>
    le_mul_of_one_le_left (hpos j).le (by exact_mod_cast hm1 j)
  by_cases he0 : e0 = 0
  · -- `e_T(ξ) = 0`: `ξ` lies in the finite set of zero-error valuations of bounded order
    subst he0
    refine ⟨by simpa using he, fun Z' hZ' j hj z' hz' => ?_⟩
    obtain rfl : Z' = D'.center := by
      obtain ⟨D'', -, hξD'', rfl⟩ := hZ'
      exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv.1 hξD''.symm
    have hval : D'.valuation (algebraMap _ W.functionField z') =
        WithZero.exp (-m ⟨j, hj⟩) := by
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz'.symm.trans (hz ⟨j, hj⟩))
      rw [← hm, ← hu, map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
        _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' η hgen) u, mul_one]
    rw [hval, WithZero.exp_le_exp, neg_le_neg_iff]
    have h1 : (m ⟨j, hj⟩ : ℝ) * aT j < 2 := by
      have := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ ⟨j, hj⟩)
      push_cast at hform'
      linarith
    have h2 : (m ⟨j, hj⟩ : ℝ) < 2 / aT j := by rw [lt_div_iff₀ (hpos j)]; exact h1
    have h3 : 2 / aT j ≤ ∑ i ∈ T.support, 2 / aT i :=
      Finset.single_le_sum (fun i _ => (div_pos two_pos (hpos i)).le) (Finset.mem_filter.1 hj).1
    have h4 := Nat.le_ceil (∑ i ∈ T.support, 2 / aT i)
    exact_mod_cast (show (m ⟨j, hj⟩ : ℝ) ≤ M by rw [hM]; push_cast; linarith)
  · -- `e_T(ξ) ≥ 1`: `ξ` is an echo
    exfalso
    have he1 : (1 : ℝ) ≤ e0 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 he0
    have hsum1 : ∑ j, (m j : ℝ) * aT j < 1 := by linarith
    have hlt1 : ∀ j : sncIndexSet T (D'.center : Set W), aT j < 1 := fun j =>
      (hle1 j).trans_lt ((Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)).trans_lt
        hsum1)
    -- the centre on `W` is off `Ex(π)`
    have hηEx : η ∉ (exceptionalSet π : Set W) := fun h => by
      obtain ⟨E, hE, hEex⟩ := exists_mem_sncIndexSet_of_mem_exceptionalSet hpure
        hπ.exceptionalSet_subset h
      exact absurd (hexc E hEex) (not_lt.2 (hlt1 ⟨E, hE⟩).le)
    have hcodW : codimension D₀.center = codimension D'.center :=
      codimension_center_eq_of_notMem_exceptionalSet D' D₀ (hΦ.trans (hDξ.trans hξD₀))
        (hgen ▸ hηEx)
    have hcodD : codimension D.center = codimension D'.center :=
      codimension_center_eq_of_notMem_exceptionalSet D' D hΦ (hgen ▸ hηEx)
    have hne : codimension D'.center ≠ ⊤ := by
      intro htop
      have h1 : ((Order.coheight D'.center : ℕ∞) : WithBot ℕ∞) ≤
          Order.krullDim (IrreducibleCloseds W) := Order.coheight_le_krullDim _
      rw [← codimension_eq_coheight, htop] at h1
      change _ ≤ topologicalKrullDim W at h1
      haveI := hY.1
      haveI := hWv.1
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (π ≫ sY)
        hπ.isBirationalMorphism, hdim] at h1
      exact absurd h1 (by decide)
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hne
    replace hc := hc.symm
    have hc2 : 2 ≤ c := by
      rw [hcodW, hc] at hcod
      exact_mod_cast hcod
    have hce := he.sub_card_sncIndexSet_le hZ₀ hc
    push_cast at hform'
    rcases Nat.lt_or_ge (sncIndexSet T (D'.center : Set W)).card 2 with hcard | hcard
    · rcases Nat.lt_succ_iff.1 hcard |>.lt_or_eq with hcard0 | hcard1
      · -- no component through the centre: `a = e_T(ξ) ≥ codim ≥ 2`
        have hcard0 : (sncIndexSet T (D'.center : Set W)).card = 0 := by omega
        rw [hcard0] at hce
        have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
        have hs0 : ∑ j, (m j : ℝ) * aT j = 0 := by
          haveI : IsEmpty (sncIndexSet T (D'.center : Set W)) :=
            ⟨fun j => (Finset.card_pos.2 ⟨j.1, j.2⟩).ne' hcard0⟩
          exact Finset.sum_of_isEmpty _
        push_cast at hce
        linarith
      · -- exactly one component through the centre: an echo
        obtain ⟨G, hG⟩ := Finset.card_eq_one.1 hcard1
        rw [hcard1] at hce
        have hGJ : G ∈ sncIndexSet T (D'.center : Set W) := hG ▸ Finset.mem_singleton_self G
        have hpos' : 0 < ∑ j, (m j : ℝ) * aT j :=
          lt_of_lt_of_le (mul_pos (by exact_mod_cast (zero_lt_one.trans_le (hm1 ⟨G, hGJ⟩)))
            (hpos G)) (Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ ⟨G, hGJ⟩))
        have he02 : e0 ≤ 1 := by
          have : (e0 : ℝ) < 2 := by linarith
          have : e0 < 2 := by exact_mod_cast this
          omega
        have hc2' : c = 2 := by
          have : (e0 : ℝ) ≤ 1 := by exact_mod_cast he02
          have : (c : ℝ) ≤ 2 := by push_cast at hce; linarith
          have : c ≤ 2 := by exact_mod_cast this
          omega
        obtain ⟨hηY, P, hPL, hηP, -⟩ :=
          mem_oneLabelSmoothLocus_of_sncIndexSet_eq_singleton hπ hT hηEx hG
        have hπη : π η = D.center.isIrreducible.genericPoint :=
          map_genericPoint_center_eq_of_comap_eq D' D hΦ
        have hV : topologicalKrullDim (D.center : Set Y) = 1 :=
          topologicalKrullDim_eq_one_of_codimension_eq_two sY hdim D.center
            (by rw [hcodD, hc, hc2']; rfl)
        have hVP : (D.center : Set Y) ⊆ P.support := by
          rw [← (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).def,
            ← hπη]
          exact closure_minimal (Set.singleton_subset_iff.2 hηP) (isClosed_support P)
        obtain ⟨j, hj⟩ := exists_isEcho_of_mem_oneLabelSmoothLocus hΘ hsupp hdim ha ha2 hPL hVP hV
          (hπη ▸ hηY)
        exact hnot ⟨P, D.center, j, hDξ ▸ hj⟩
    · -- two components through the centre: excluded by terminality
      have h := one_lt_sum_of_two_le_card hΘ hπ hK aT haT hηEx hcard
      have : ∑ j ∈ sncIndexSet T (D'.center : Set W), aT j ≤ ∑ j, (m j : ℝ) * aT j := by
        rw [← Finset.sum_coe_sort]
        exact Finset.sum_le_sum fun j _ => hle1 j
      linarith

end MMP.IndexdStrict.Card_echoes

end

/-! ### Port of `lem_mmp_indexd_echoes_generic` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.IndexdStrict.Card_echoes_generic

/-- In `WithBot ℕ∞`, `d + c = 3` with `d = 1` forces `c = 2`. -/
private theorem eq_two_of_one_add_eq_three {c : ℕ∞}
    (h : (1 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 2 := by
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h'
    norm_cast
    omega

/-- On a variety of dimension three, a curve has codimension two. -/
private theorem codimension_eq_two {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 3) (V : IrreducibleCloseds Y)
    (hV : topologicalKrullDim (V : Set Y) = 1) : codimension V = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim, hV] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  exact eq_two_of_one_add_eq_three h

/-- The coefficients of the boundary of a klt pair are `< 1`. -/
private theorem coeff_lt_one_of_isKltPair {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {B : QDivisor Y}
    (hB : IsKltPair sY B) (P : MMP.Mori.PrimeDivisor Y) : B.coeff P < 1 := by
  have hpair := hB.1.isPair
  have hX : IsNormalVariety ℂ sY := hpair.1
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 Y)
    infer_instance
  have hpos := hB.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hprop)
  have heq := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha
  rw [heq] at hpos
  push_cast at hpos
  exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)

/-- A divisorial valuation has at most one centre. -/
private theorem isCentre_unique {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    (hX : IsNormalVariety ℂ sY) {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    {V V' : IrreducibleCloseds Y} (hV : MMP.Intersection.IsCentre ℂ sY ξ V)
    (hV' : MMP.Intersection.IsCentre ℂ sY ξ V') : V = V' := by
  obtain ⟨D, -, hD, rfl⟩ := hV
  obtain ⟨D', -, hD', rfl⟩ := hV'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hD.symm.trans hD')

/-- On a threefold, a divisorial valuation centred on a curve is exceptional. -/
private theorem isExceptionalValuation_of_isCentre {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 3)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 1)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hC : MMP.Intersection.IsCentre ℂ sY ξ V) : MMP.Intersection.IsExceptionalValuation ℂ sY ξ := by
  obtain ⟨D, hD, hv, rfl⟩ := hC
  exact ⟨D, hD, hv, (codimension_eq_two sY hdim _ hV).ge⟩

/-- The label of an echo at `V` is the only label containing `V`: the generic point of `V` lies
in the one-label smooth locus. -/
private theorem eq_of_isEcho_of_subset {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {S S' : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ} {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (he : IsEcho sY L S V j ξ) (hS' : S' ∈ L) (hVS' : (V : Set Y) ⊆ S'.support) : S' = S := by
  have hη (T : MMP.Mori.PrimeDivisor Y) (hT : (V : Set Y) ⊆ T.support) :
      V.isIrreducible.genericPoint ∈ T.support :=
    hT (V.isClosed.closure_subset V.isIrreducible.isGenericPoint_genericPoint_closure.mem)
  exact eq_of_mem_oneLabelSmoothLocus he.2.2.2.2.2.1 hS' he.2.2.1 (hη S' hVS') (hη S he.2.2.2.1)

/-- **Generic curve centres below log discrepancy two are echoes.** Let `(Y, Θ)` be a terminal
pair on a projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors
containing the support of `Θ`. There is a finite set `𝒮` of irreducible curves of `Y` such that
for every irreducible curve `V ∉ 𝒮` and every normalized divisorial valuation `ξ` of `ℂ(Y)` with
centre `V` and `a(ξ; Y, Θ) < 2`, the generic point of `V` lies in the one-label smooth locus
`MMP.Fourfold.oneLabelSmoothLocus L`, a unique label `S ∈ L` contains `V`, and `ξ` is an echo
(`MMP.Fourfold.IsEcho`) of some order `j ≥ 1` of `S` at `V` with log discrepancy
`1 + j (1 - Θ(S))`. -/
private theorem _root_.MMP.Fourfold.exists_finite_forall_isEcho_of_isCentre
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    ∃ 𝒮 : Set (IrreducibleCloseds Y), 𝒮.Finite ∧
      (∀ V ∈ 𝒮, topologicalKrullDim (V : Set Y) = 1) ∧
      ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 → V ∉ 𝒮 →
        ∀ ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
          MMP.Intersection.IsCentre ℂ sY ξ V → (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) →
            V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧
              ∃ S ∈ L, (V : Set Y) ⊆ S.support ∧
                (∀ S' ∈ L, (V : Set Y) ⊆ S'.support → S' = S) ∧
                ∃ j : ℕ, 1 ≤ j ∧ IsEcho sY L S V j ξ ∧
                  HasLogDiscrepancy sY Θ ξ (1 + j * (1 - (Θ.coeff S : ℝ))) := by
  have hX : IsNormalVariety ℂ sY := hΘ.1.1.isPair.1
  have : LocallyOfFiniteType sY := hX.1.toLocallyOfFiniteType
  set F := {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sY ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ sY ξ ∧
        (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          IsEcho sY L S V j ξ}
  have hF : F.Finite := finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp
  refine ⟨{V | topologicalKrullDim (V : Set Y) = 1 ∧ ∃ ξ ∈ F, MMP.Intersection.IsCentre ℂ sY ξ V},
    (hF.biUnion fun ξ _ => Set.Subsingleton.finite (s := {V | MMP.Intersection.IsCentre ℂ sY ξ V})
      fun _ hV _ hV' => isCentre_unique hX hV hV').subset fun V ⟨_, ξ, hξ, hV⟩ =>
        Set.mem_biUnion hξ hV, fun V hV => hV.1, ?_⟩
  intro V hV hVS ξ hC ha
  obtain ⟨S, V', j, he⟩ : ∃ S V' j, IsEcho sY L S V' j ξ := by
    by_contra h
    obtain ⟨D, hD, hv, -⟩ := id hC
    exact hVS ⟨hV, ξ, ⟨⟨D, hD, hv⟩, isExceptionalValuation_of_isCentre hdim hV hC, ha, h⟩, hC⟩
  obtain rfl : V' = V := isCentre_unique hX he.2.2.2.2.2.2.2.1 hC
  exact ⟨he.2.2.2.2.2.1, S, he.2.2.1, he.2.2.2.1, fun _ => eq_of_isEcho_of_subset he, j,
    he.2.2.2.2.2.2.1, he,
    he.hasLogDiscrepancy hΘ.1.1 hsupp fun S' _ => coeff_lt_one_of_isKltPair hΘ.1 S'⟩

end MMP.IndexdStrict.Card_echoes_generic

end

/-! ### Port of `lem_mmp_indexd_echoes_curve` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace MMP.IndexdStrict.Card_echoes_curve

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- A divisorial valuation has at most one centre. -/
private theorem isCentre_unique (hvar : IsNormalVariety ℂ sY)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {V V' : IrreducibleCloseds Y}
    (hV : MMP.Intersection.IsCentre ℂ sY ξ V) (hV' : MMP.Intersection.IsCentre ℂ sY ξ V') :
    V = V' := by
  obtain ⟨D, -, hD, rfl⟩ := hV
  obtain ⟨D', -, hD', rfl⟩ := hV'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hvar.1 (hD.symm.trans hD')

/-- On a threefold, a valuation centred on a curve is exceptional: the centre has
codimension `3 - 1 = 2`. -/
private theorem isExceptionalValuation_of_isCentre (hvar : IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 1)
    (hξ : MMP.Intersection.IsCentre ℂ sY ξ V) :
    MMP.Intersection.IsExceptionalValuation ℂ sY ξ := by
  obtain ⟨D, hp, rfl, rfl⟩ := hξ
  refine ⟨D, hp, rfl, ?_⟩
  haveI : LocallyOfFiniteType sY := hvar.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (D.f D.E.genericPoint)
  rw [← D.center_eq_closure_genericPoint, hV, hdim] at h
  rw [MMP.Positivity.DivisorOver.codimension_center]
  generalize Order.coheight (D.f D.E.genericPoint) = c at h ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe m =>
    have : 1 + m = 3 := by
      have h' : ((1 + m : ℕ) : WithBot ℕ∞) = (3 : ℕ) := by push_cast; exact h
      exact_mod_cast h'
    exact_mod_cast (by omega : 2 ≤ m)

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {Θ : QDivisor Y}
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : HasLogDiscrepancy sY Θ ξ a) (h' : HasLogDiscrepancy sY Θ ξ a') : a = a' := by
  obtain ⟨n, D, hD, h⟩ := h
  obtain ⟨n', D', hD', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hD.trans hD'.symm)

/-- For a label `S`, the echoes of `S` at `V` with log discrepancy `< 2` are finitely many: the
echo of order `j` is unique and has log discrepancy `1 + j (1 - b_S)`, which is `< 2` only for
`j < 1 / (1 - b_S)`. -/
private theorem finite_setOf_isEcho {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ j, IsEcho sY L S V j ξ) ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have hb : (Θ.coeff S : ℝ) < 1 := by exact_mod_cast coeff_lt_one_of_isKltPair hΘ S
  refine ((Finset.range ⌈1 / (1 - (Θ.coeff S : ℝ))⌉₊).finite_toSet.biUnion
    (t := fun j => {ξ | IsEcho sY L S V j ξ}) fun j _ => ?_).subset ?_
  · refine Set.Subsingleton.finite fun ξ hξ ξ' hξ' => ?_
    obtain ⟨hY, hdim, hS, hVS, hV, hη, hj, -⟩ := id hξ
    exact ((existsUnique_isEcho hY hdim hS hVS hV hη).1 j hj).unique hξ hξ'
  · rintro ξ ⟨⟨j, hξ⟩, a, ha, hξa⟩
    have h := HasLogDiscrepancy.unique hξa
      (hξ.hasLogDiscrepancy hΘ.1 hsupp fun S' _ => coeff_lt_one_of_isKltPair hΘ S')
    exact Set.mem_biUnion (x := j)
      (Finset.mem_range.2 (Nat.lt_ceil.2 ((lt_div_iff₀ (sub_pos.2 hb)).2 (by linarith)))) hξ

/-- **Finitely many valuations below log discrepancy two at a fixed curve.** Let `(Y, Θ)` be a
terminal pair on a projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime
divisors containing the support of `Θ`. For every irreducible closed curve `V ⊆ Y`, the
normalized divisorial valuations `ξ` of `ℂ(Y)` with centre `V` (`MMP.Intersection.IsCentre`) and
`a(ξ; Y, Θ) < 2` form a finite set. -/
private theorem _root_.MMP.Fourfold.finite_setOf_isCentre
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    (V : IrreducibleCloseds Y) (hV : topologicalKrullDim (V : Set Y) = 1) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsCentre ℂ sY ξ V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a}.Finite := by
  obtain ⟨hvar, -⟩ := id hΘ.1.1.isPair
  refine ((finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp).union (L.finite_toSet.biUnion
    fun S _ => finite_setOf_isEcho hΘ.1 hsupp S V)).subset ?_
  rintro ξ ⟨hC, hξa⟩
  by_cases he : ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
      IsEcho sY L S V j ξ
  · obtain ⟨S, V', j, hξ⟩ := he
    obtain rfl := isCentre_unique hvar hξ.2.2.2.2.2.2.2.1 hC
    exact Or.inr (Set.mem_biUnion (x := S) hξ.2.2.1 ⟨⟨j, hξ⟩, hξa⟩)
  · obtain ⟨D, hp, hD, -⟩ := id hC
    exact Or.inl ⟨⟨D, hp, hD⟩, isExceptionalValuation_of_isCentre hvar hdim hV hC, hξa, he⟩

end MMP.IndexdStrict.Card_echoes_curve

end

/-! ### Port of `lem_mmp_indexd_echoes_points` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.IndexdStrict.Card_echoes_points

/-- A one-point subspace has Krull dimension zero. -/
private theorem topologicalKrullDim_singleton {X : Type*} [TopologicalSpace X] (y : X) :
    topologicalKrullDim ({y} : Set X) = 0 := by
  have : Nonempty (IrreducibleCloseds ({y} : Set X)) :=
    ⟨⟨closure {⟨y, rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact (topologicalKrullDim_zero_of_discreteTopology _).antisymm Order.krullDim_nonneg

/-- On an integral scheme of dimension `n`, locally of finite type over a field, a point whose
closure is a single point has coheight `n`. -/
private theorem coheight_eq_of_closure_eq_singleton {k : Type*} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hdim : topologicalKrullDim Y = n) {x y : Y} (hx : closure {x} = ({y} : Set Y)) :
    Order.coheight x = n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY x
  rw [hx, hdim, topologicalKrullDim_singleton, zero_add] at h
  exact_mod_cast h

/-- **Point-centred valuations below log discrepancy two.** Let `(Y, Θ)` be a terminal pair on a
projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors containing
the support of `Θ`. Then the normalized divisorial valuations `ξ` of `ℂ(Y)` whose centre on `Y`
is a closed point and with `a(ξ; Y, Θ) < 2` form a finite set. -/
private theorem _root_.MMP.Fourfold.finite_setOf_isCentre_singleton
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : MMP.Fourfold.IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : MMP.Fourfold.IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ (Z : IrreducibleCloseds Y) (y : Y),
          MMP.Intersection.IsCentre ℂ sY ξ Z ∧ (Z : Set Y) = {y}) ∧
        ∃ a < 2, MMP.Fourfold.HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  refine (MMP.Fourfold.finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp).subset ?_
  rintro ξ ⟨⟨Z, y, ⟨D, hD, hξ, hZ⟩, hZy⟩, ha⟩
  refine ⟨⟨D, hD, hξ⟩, ⟨D, hD, hξ, ?_⟩, ha, ?_⟩
  · rw [MMP.Positivity.DivisorOver.codimension_center, coheight_eq_of_closure_eq_singleton sY
      (n := 3) (mod_cast hdim) (by rw [← D.center_eq_closure_genericPoint, ← hZ, hZy])]
    decide
  · rintro ⟨S, V, j, -, -, -, -, hV1, -, -, ⟨D', hD', hξ', hV'⟩, -⟩
    have hc := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hY.toIsVariety
      (hξ.symm.trans hξ')
    rw [← hV', ← hZ] at hc
    rw [← hc, hZy, topologicalKrullDim_singleton] at hV1
    exact absurd hV1 (by decide)

end MMP.IndexdStrict.Card_echoes_points

end

/-! ### Port of `lem_mmp_indexd_point_support_finite` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.IndexdStrict.Card_point_support_finite

/-- **Finitely many weighted point valuations.** On a model `(Y, Θ)` of a prepared chain, the
normalized divisorial valuations `v` of `ℂ(Y)` whose centre on `Y` is a closed point and whose
weight `w_v` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed
admissible scale) is nonzero form a finite set. -/
private theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCentre_singleton
    {T : MMP.Fourfold.StabilizedTail}
    (Q : MMP.Fourfold.StabilizedTail.PreparedChain T)
    (x : Q.ModelIndex) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      (∃ (Z : IrreducibleCloseds (Q.chain.model x.1)) (y : Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            (Z : Set (Q.chain.model x.1)) = {y}) ∧
        ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hΘ, hY, hQ, hdim, -⟩ := Q.echoSetting_model x
  refine (MMP.Fourfold.finite_setOf_isCentre_singleton _ hY hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl).subset ?_
  rintro v ⟨hc, w, ⟨-, a, ⟨n, D, -, hDv, hD⟩, rfl⟩, hw⟩
  exact ⟨hc, a, lt_of_not_ge fun ha ↦ hw (MMP.Fourfold.difficultyWeight_of_nonpos
    (sub_nonpos.2 ha)), n, D, hDv, hD⟩

end MMP.IndexdStrict.Card_point_support_finite

end

/-! ### Port of `lem_mmp_indexd_curve_support_finite` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.IndexdStrict.Card_curve_support_finite

/-- **Finitely many weighted valuations at a curve.** On a model `(Y, Θ)` of a prepared chain,
for an irreducible closed curve `C ⊆ Y` with generic point `γ.point`, the normalized divisorial
valuations `v` of `ℂ(Y)` with centre `C` whose weight `w_v`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed admissible scale) is
nonzero form a finite set. -/
private theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCentre_closure
    {T : MMP.Fourfold.StabilizedTail}
    (Q : MMP.Fourfold.StabilizedTail.PreparedChain T)
    (x : Q.ModelIndex) (γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1)) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
            (Z : Set (Q.chain.model x.1)) = closure {γ.point}) ∧
        ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hΘ, hY, hQ, hdim, -⟩ := Q.echoSetting_model x
  let V : IrreducibleCloseds (Q.chain.model x.1) :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  refine (MMP.Fourfold.finite_setOf_isCentre _ hY hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl V
    γ.topologicalKrullDim_closure_point).subset ?_
  rintro v ⟨⟨Z, hc, hZ⟩, w, ⟨-, a, ⟨n, D, -, hDv, hD⟩, rfl⟩, hw⟩
  obtain rfl : Z = V := IrreducibleCloseds.ext hZ
  exact ⟨hc, a, lt_of_not_ge fun ha =>
    hw (MMP.Fourfold.difficultyWeight_of_nonpos (sub_nonpos.mpr ha)), n, D, hDv, hD⟩

end MMP.IndexdStrict.Card_curve_support_finite

end

/-! ### Port of `lem_mmp_indexd_brackets_cofinite` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.IndexdStrict.Card_brackets_cofinite

/-! ### Valuations -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- A valuation with a log discrepancy over a proper model has that log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- The default of a label of coefficient zero vanishes: `d(0) = ∑_{j ≥ 1} w(1 - j) = 0`. -/
private theorem defaultWeight_zero (N : ℕ) : defaultWeight N 0 = 0 := by
  rw [defaultWeight]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [finsum_eq_if]
  split_ifs with hj
  · apply difficultyWeight_of_nonpos
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · rfl

/-! ### Dimension arithmetic -/

/-- In `WithBot ℕ∞`, `d + 1 = n + 1` forces `d = n`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = ((n + 1 : ℕ) : ℕ∞)) :
    d = (n : ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe h).elim
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact (ENat.top_ne_coe (n + 1) (WithBot.coe_injective h)).elim
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_injective (by simpa using h)
      rw [Nat.succ_injective (by exact_mod_cast h' : m + 1 = n + 1)]

/-- The coheight form of `eq_of_add_one_eq`: `1 + c = n + 1` in `WithBot ℕ∞` forces `c = n`. -/
private theorem eq_of_one_add_eq {c : ℕ∞} {n : ℕ} (h : (1 : WithBot ℕ∞) + c = ((n + 1 : ℕ) : ℕ∞)) :
    c = n :=
  WithBot.coe_injective (eq_of_add_one_eq (by rwa [add_comm] at h))

/-! ### Centres of labels -/

section LabelCentre

variable {T : StabilizedTail}

/-- The valuation of `k(X_i)` transported from a valuation of `k(X_0)` is unique. -/
private theorem isTransportedValuationFrom_unique : ∀ (i : ℕ)
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, ht⟩, ⟨u', hu', ht'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    have hd := T.isThreefoldStepDiagram i
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (ht.trans ht'.symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have hY' : MMP.Mori.IsNormalVariety ℂ (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  let D : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P⟩
  let D' : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P'⟩
  have hD : D.valuation = D'.valuation := by
    change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
    rw [hv]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hD)

/-- Along the programme of a bridge, every `π_k : V_k ⟶ Z_i` induces a surjection
`k(Z_i) → k(V_k)` of function fields: `π_0 = f_i ∘ p_i` is birational, and
`π_{k+1} = h_k ∘ g_k⁺` with `π_k = h_k ∘ g_k` and `g_k`, `g_k⁺` birational. -/
private theorem surjective_functionFieldMap_modelMap (C : T.TerminalChain) (i : ℕ)
    [IsIntegral (T.Z i)] :
    ∀ k ≤ (C.bridge i).P.m,
      ∀ [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)],
        Function.Surjective
          (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k))
  | 0, _, _ => by
    have hb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    have hp := (C.junction i).isBirationalMorphism
    haveI := hp.isDominant
    intro z
    obtain ⟨y, rfl⟩ := hp.functionFieldMap_bijective.2 z
    obtain ⟨x, rfl⟩ := hb.functionFieldMap_bijective.2 y
    exact ⟨x, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply
      (C.junction i).p (T.f i) x).symm⟩
  | k + 1, hk, hdom => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isThreefoldStepDiagram k hk'
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hg := hd.isBirationalMorphism_minus
    haveI := hg.isDominant
    have hgp := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hgp.isDominant
    have hπ : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k + 1) =
        (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hπ' : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k =
        (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    haveI hgph : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
    haveI : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.gp k) _
    haveI : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) :=
      hπ' ▸ inferInstance
    have IH := surjective_functionFieldMap_modelMap C i k hk'.le
    have hh : Function.Surjective (functionFieldMap ((C.bridge i).P.h k)) := by
      intro t
      obtain ⟨z, hz⟩ := IH (functionFieldMap ((C.bridge i).P.g k) t)
      refine ⟨z, (functionFieldMap ((C.bridge i).P.g k)).injective ?_⟩
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        ← MMP.Positivity.DivisorOver.functionFieldMap_congr hπ', hz]
    intro t
    obtain ⟨y, rfl⟩ := hgp.functionFieldMap_bijective.2 t
    obtain ⟨z, rfl⟩ := hh y
    have e1 := @MMP.Positivity.DivisorOver.functionFieldMap_congr _ _ _ _ _ _ hdom hgph hπ
    exact ⟨z, (congrArg (fun φ => φ z) e1).trans
      (@MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ _ _ _ _
        ((C.bridge i).P.gp k) ((C.bridge i).P.h k) hgp.isDominant inferInstance hgph z).symm⟩

/-- The centre of a label on a normal model of a terminal chain is unique. -/
private theorem isLabelCentre_unique (C : T.TerminalChain) (S : C.Label) :
    ∀ (x : C.ModelIndex), MMP.Mori.IsNormalVariety ℂ (C.modelStructure x) →
      ∀ {P P' : MMP.Mori.PrimeDivisor (C.model x)},
        C.IsLabelCentre S x P → C.IsLabelCentre S x P' → P = P'
  | ⟨i, none⟩, hY, P, P', ⟨w, hw, hPw⟩, ⟨w', hw', hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY (C.junction i).p hb.isDominant
      hb.functionFieldMap_bijective.2 _ _ (hPw.trans hPw'.symm)
  | ⟨i, some k⟩, hY, P, P', ⟨w, hw, hdom, hPw⟩, ⟨w', hw', _, hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY _ hdom
      (@surjective_functionFieldMap_modelMap T C i _ k k.2.le hdom) _ _ (hPw.trans hPw'.symm)

end LabelCentre

/-! ### A low-discrepancy valuation along a curve inside a boundary component -/

section MonomialValuation

/-- The order-reversing monoid map `WithTop ℤ → (WithZero (Multiplicative ℤ))`, `n ↦ exp (-n)`,
`⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → (WithZero (Multiplicative ℤ))
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private theorem expNeg_top : expNeg ⊤ = 0 := rfl

private theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private theorem expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R (WithZero (Multiplicative ℤ)) where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private theorem valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

private theorem isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    MMP.Mori.IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← hxy.1]
  congr 1
  ext
  simp [Matrix.range_cons, Set.pair_comm]

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

/-- **A low-discrepancy valuation along a curve in the boundary.** Let `(Y, Θ)` be a pair on a
normal threefold, smooth at the generic point `η_V` of an irreducible closed curve `V`, and let
`V ⊆ S` for a prime divisor `S` with `Θ(S) > 0`. Then the monomial valuation `v_{x,t;1}` at `η_V`
has centre `V` and log discrepancy `a(v; Y, Θ) ≤ 2 - Θ(S) < 2`. -/
private theorem exists_isCentre_hasLogDiscrepancy_lt_two {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : MMP.Mori.QDivisor Y} (hΘ : MMP.Fourfold.IsPair sY Θ) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 1)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {S : MMP.Mori.PrimeDivisor Y} (hVS : (V : Set Y) ⊆ S.support) (hb : 0 < Θ.coeff S) :
    ∃ v : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sY v V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ v a := by
  classical
  have hlft : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  have hdf := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [hgen.def, hV, hdim] at hdf
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := eq_of_one_add_eq (n := 2) hdf
  have hdim2 : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoh]
    rfl
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [hdim2] at h
    exact_mod_cast h.symm
  have hxt : MMP.Mori.IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap hxt) (le_refl 1)
  have hvalW : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation (z 1) (z 0) 1 f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V (z 0) (z 1) 1 (valuationOfAddValuation W) := by
    refine ⟨hY, ?_, inferInstance, hxt, le_rfl, hvalW⟩
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]
    exact hcoh
  have hvc := hv.isNormalizedDivisorialValuation_and_isCentre.2
  choose f hf0 hf using fun P : MMP.Mori.PrimeDivisor Y =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) P
  have hla := hv.hasLogDiscrepancy hΘ f (fun P _ => hf P)
  refine ⟨_, hvc, _, ?_, hla⟩
  -- the order of a local equation is a natural number, at least `1` along `S`
  have hM : ∀ P : MMP.Mori.PrimeDivisor Y,
      0 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) ∧
        (V.isIrreducible.genericPoint ∈ P.support →
          1 ≤ -WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P)))) := by
    intro P
    obtain ⟨M, hMv, hvM⟩ := hvalW (f P) (hf0 P)
    rw [hvM, WithZero.log_exp, neg_neg]
    refine ⟨Int.natCast_nonneg M, fun hP => ?_⟩
    obtain ⟨q, -, hq, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hP
    have hmem : f P ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) := by
      have : f P ∈ q.asIdeal := by
        rw [← hq, hf P]
        exact Ideal.mem_span_singleton_self _
      exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top this
    have h1 : (1 : ℕ∞) ≤ M := by
      rw [← hMv, monomialValuation_one_eq_iSup hxt]
      exact le_iSup₂_of_le (f := fun (n : ℕ) (_ : f P ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk V.isIrreducible.genericPoint) ^ n) =>
          (n : ℕ∞)) 1 (by rwa [pow_one]) le_rfl
    exact_mod_cast h1
  have hηS : V.isIrreducible.genericPoint ∈ S.support := hVS hgen.mem
  have hSsupp : S ∈ Θ.support := Finsupp.mem_support_iff.mpr hb.ne'
  have hle : (Θ.coeff S : ℝ) ≤ ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) :
        ℝ) := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun P => (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) : ℝ))
      (fun P _ => mul_nonneg (by exact_mod_cast hΘ.nonneg P) (by exact_mod_cast (hM P).1))
      hSsupp)
    exact le_mul_of_one_le_right (by exact_mod_cast hΘ.nonneg S) (by exact_mod_cast (hM S).2 hηS)
  have hbR : (0 : ℝ) < (Θ.coeff S : ℝ) := by exact_mod_cast hb
  rw [Nat.cast_one]
  linarith

end MonomialValuation

/-! ### Branch numbers at a regular point of a prime divisor -/

section BranchNumber

/-- **Branch number one at a regular point.** Let `S` be a prime divisor of a threefold `Y`
and `V ⊆ S` an irreducible closed curve at whose generic point `S` is regular. Then exactly one
prime divisor of the normalization `S^ν` maps onto `V`: `r_{V} = 1`. -/
private theorem branchNumber_eq_one {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 3)
    (S : MMP.Mori.PrimeDivisor Y)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 1)
    (hVS : (V : Set Y) ⊆ S.support)
    (hreg : V.isIrreducible.genericPoint ∉
      S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme) :
    branchNumber S V = 1 := by
  classical
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI hvarS : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨-, -, hfinν, hsurj, -⟩, ⟨U, hU, hiso⟩, -⟩ :=
    MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)
  set ν := S.idealSheaf.subscheme.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral
      S.idealSheaf.subscheme) with hν
  set ι := S.idealSheaf.subschemeι with hι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  -- the point `s` of `S` over `η_V`
  obtain ⟨s, hs⟩ : V.isIrreducible.genericPoint ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    exact hVS hgen.mem
  have hsreg : IsRegularLocalRing (S.idealSheaf.subscheme.presheaf.stalk s) := by
    by_contra h
    exact hreg ⟨s, h, hs⟩
  have hsU : s ∈ U := by
    rw [← SetLike.mem_coe, hU]
    haveI := IsRegularLocalRing.isDomain (S.idealSheaf.subscheme.presheaf.stalk s)
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid
      (S.idealSheaf.subscheme.presheaf.stalk s)
    exact (inferInstance : IsIntegrallyClosed (S.idealSheaf.subscheme.presheaf.stalk s))
  -- `S` is a surface and `closure {s}` a curve, so `s` has coheight one in `S`
  have hdimS : topologicalKrullDim S.idealSheaf.subscheme = 2 := by
    have hdP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY S.genericPoint
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at hdP
    let e := ι.isClosedEmbedding.isEmbedding.toHomeomorph
    let e' := e.trans (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι S.idealSheaf))
    exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).trans
      (eq_of_add_one_eq (n := 2) hdP)
  have hdimCs : topologicalKrullDim (closure ({s} : Set S.idealSheaf.subscheme)) = 1 := by
    rw [← hV]
    have hemb : Topology.IsEmbedding
        (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) :=
      ι.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) =
        (V : Set Y) := by
      rw [show (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) = ι ∘ Subtype.val
        from rfl, Set.range_comp, Subtype.range_coe,
        ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hs, hgen.def]
    let e := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hcohs : Order.coheight s = 1 := by
    have hdS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (S.idealSheaf.subschemeι ≫ sY) s
    rw [hdimS, hdimCs] at hdS
    exact eq_of_one_add_eq (n := 1) hdS
  -- over `U` the normalization is an isomorphism
  haveI := hsurj
  haveI := hiso
  haveI := hfinν
  obtain ⟨z₀, hz₀⟩ := ν.surjective s
  have hcomm : ∀ p, U.ι ((ν ∣_ U) p) = ν ((ν ⁻¹ᵁ U).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hlift : ∀ z, ν z = s → ∃ p, (ν ⁻¹ᵁ U).ι p = z := fun z hz => by
    have : z ∈ Set.range (ν ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      show ν z ∈ U
      rw [hz]
      exact hsU
    exact this
  obtain ⟨p₀, hp₀⟩ := hlift z₀ hz₀
  have huniq : ∀ z, ν z = s → z = z₀ := by
    intro z hz
    obtain ⟨p, hp⟩ := hlift z hz
    have h1 : U.ι ((ν ∣_ U) p) = U.ι ((ν ∣_ U) p₀) := by rw [hcomm, hcomm, hp, hp₀, hz, hz₀]
    have h2 := (ν ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective h1)
    rw [← hp, ← hp₀, h2]
  have hcoh0 : Order.coheight z₀ = 1 := by
    calc Order.coheight z₀ = Order.coheight ((ν ⁻¹ᵁ U).ι p₀) := by rw [hp₀]
      _ = Order.coheight p₀ := coheight_eq_of_isOpenImmersion _
      _ = Order.coheight ((ν ∣_ U) p₀) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight (U.ι ((ν ∣_ U) p₀)) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight s := by rw [hcomm, hp₀, hz₀]
      _ = 1 := hcohs
  -- the images of prime divisors of `S^ν`
  have hfun : ⇑(ν ≫ ι) = ⇑ι ∘ ⇑ν := funext fun _ => rfl
  have hcl : IsClosedMap (ν ≫ ι) := by
    rw [hfun]
    exact ι.isClosedEmbedding.isClosedMap.comp ν.isClosedMap
  have himg : ∀ Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)),
      (ν ≫ ι) '' Q.support = closure {ι (ν Q.genericPoint)} := by
    intro Q
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hcl.closure_image_eq_of_continuous (ν ≫ ι).continuous, Set.image_singleton]
    rfl
  have hset : {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)} =
        {AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [himg]
    constructor
    · intro hQ
      have hQη : ι (ν Q.genericPoint) = V.isIrreducible.genericPoint :=
        (inseparable_iff_closure_eq.mpr (hQ.trans hgen.def.symm)).eq
      have hνQ : ν Q.genericPoint = s := ι.isClosedEmbedding.injective (hQη.trans hs.symm)
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact huniq _ hνQ
    · rintro rfl
      have hg0 : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0) = z₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [hg0, hz₀, hs, hgen.def]
  change {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)}.ncard = 1
  rw [hset, Set.ncard_singleton]

end BranchNumber

/-! ### Brackets off a finite set of curves -/

/-- A sum over `t` is the sum over `s` along an injection `g : s → t` whose image contains the
support of the summand on `t`. -/
private theorem finsum_mem_eq_finsum_mem_comp {α ι M : Type*} [AddCommMonoid M] {f : α → M}
    {g : ι → α} {s : Set ι} {t : Set α} (hg : Set.InjOn g s) (hst : g '' s ⊆ t)
    (hts : t ∩ Function.support f ⊆ g '' s) :
    ∑ᶠ a ∈ t, f a = ∑ᶠ i ∈ s, f (g i) := by
  rw [← finsum_mem_image hg, ← finsum_mem_inter_support, ← finsum_mem_inter_support (s := g '' s),
    (Set.subset_inter hts Set.inter_subset_right).antisymm
      (Set.inter_subset_inter_left _ hst)]

/-- Proper curves are determined by their closures, so finitely many closures carry finitely many
proper curves. -/
private theorem finite_setOf_closure_point_mem {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} {𝒮 : Set (Set X)} (h : 𝒮.Finite) :
    {γ : MMP.Mori.ProperCurve sX | closure {γ.point} ∈ 𝒮}.Finite :=
  h.preimage fun _ _ _ _ he => MMP.Mori.ProperCurve.ext (inseparable_iff_closure_eq.mpr he).eq

/-- **Brackets vanish off a finite set of curves.** On a model `(Y, Θ)` of a prepared chain there
is a finite set `𝒮` of irreducible closed subsets such that the bracket `β_C` vanishes at every
curve `C ∉ 𝒮`: off the set of `exists_finite_forall_isEcho_of_isCentre`, either no valuation with
centre `C` has `a < 2`, so all weights at `C` vanish and every label through `C` has coefficient
zero (by `exists_isCentre_hasLogDiscrepancy_lt_two`) and default `d(0) = 0`; or the valuations of
nonzero weight at `C` are the echoes of the unique label `S_h` through `C`, which sum to `d(b_h)`,
while `r_{C,h} = 1` (`branchNumber_eq_one`). -/
private theorem exists_finite_forall_isCurveBracket_eq_zero {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex) :
    ∃ 𝒮 : Set (IrreducibleCloseds (Q.chain.model x.1)), 𝒮.Finite ∧
      ∀ γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1),
        closure {γ.point} ∉ ((↑) : _ → Set (Q.chain.model x.1)) '' 𝒮 →
        ∀ β : ℤ, Q.IsCurveBracket x γ β → β = 0 := by
  classical
  set Y := Q.chain.model x.1
  set sY := Q.chain.modelStructure x.1
  set Θ := Q.chain.modelBoundary x.1
  obtain ⟨hΘ, hY, hQf, hdim, ⟨c, hcinj, hcc, hcsupp, hccoeff⟩, hreg⟩ := Q.echoSetting_model x
  have hnv : MMP.Mori.IsNormalVariety ℂ sY := hQf.1
  have hpair : MMP.Fourfold.IsPair sY Θ := hΘ.1.1
  have : Finite Q.chain.Label := Q.chain.finite_label
  set L : Finset (MMP.Mori.PrimeDivisor Y) := (Set.finite_range c).toFinset
  have hmemL : ∀ S ∈ L, ∃ h, c h = S := fun S hS => (Set.finite_range c).mem_toFinset.mp hS
  have hcL : ∀ h, c h ∈ L := fun h => (Set.finite_range c).mem_toFinset.mpr ⟨h, rfl⟩
  have hsupp : Θ.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp P (Finsupp.mem_support_iff.mp hP))
  have hlt : ∀ S ∈ L, Θ.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff h).2
  obtain ⟨𝒮, h𝒮, -, h𝒮gen⟩ := exists_finite_forall_isEcho_of_isCentre sY hY hQf hdim hΘ hsupp
  refine ⟨𝒮, h𝒮, fun γ hγ β hβ => ?_⟩
  let V : IrreducibleCloseds Y :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hV𝒮 : V ∉ 𝒮 := fun h => hγ ⟨V, h, rfl⟩
  have hVdim : topologicalKrullDim (V : Set Y) = 1 := γ.topologicalKrullDim_closure_point
  -- the valuations of the first sum are those with centre `V`
  have hcent : {v | ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
      (Z : Set Y) = closure {γ.point}} = {v | MMP.Intersection.IsCentre ℂ sY v V} :=
    Set.ext fun v => ⟨fun ⟨Z, hc, hZ⟩ => by
      obtain rfl : Z = V := IrreducibleCloseds.ext hZ
      exact hc, fun hc => ⟨V, hc, rfl⟩⟩
  obtain ⟨w, r, d, hw, hr, hd, hβeq⟩ := hβ
  change β = ((∑ᶠ v ∈ {v | ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧
      (Z : Set Y) = closure {γ.point}}, w v : ℕ) : ℤ) - _ at hβeq
  rw [hcent] at hβeq
  have hcen : ∀ S P, Q.chain.IsLabelCentre S x.1 P → P = c S := fun S P h =>
    isLabelCentre_unique Q.chain S x.1 hnv h (hcc S)
  have hr' : ∀ S, r S = branchNumber (c S) (closure {γ.point}) := fun S => by
    obtain ⟨P, hP, h⟩ := hr S
    rw [h, hcen S P hP]
  have hd' : ∀ S, d S = defaultWeight Q.scale ((Θ.coeff (c S) : ℚ) : ℝ) := fun S => by
    obtain ⟨b, ⟨P, hP, hb⟩, h⟩ := hd S
    rw [h, ← hb, hcen S P hP]
  have hw' : ∀ v, MMP.Intersection.IsCentre ℂ sY v V →
      ∃ a, HasLogDiscrepancy sY Θ v a ∧ w v = difficultyWeight Q.scale (2 - a) := fun v hv => by
    obtain ⟨-, a, ha, h⟩ := hw v ((Set.ext_iff.mp hcent v).mpr hv)
    exact ⟨a, IsValuationLogDiscrepancy.hasLogDiscrepancy ha, h⟩
  have hwpos : ∀ v, MMP.Intersection.IsCentre ℂ sY v V → w v ≠ 0 →
      ∃ a < 2, HasLogDiscrepancy sY Θ v a := fun v hv hne => by
    obtain ⟨a, ha, h⟩ := hw' v hv
    exact ⟨a, lt_of_not_ge fun h2 =>
      hne (h.trans (difficultyWeight_of_nonpos (sub_nonpos.mpr h2))), ha⟩
  rw [hβeq, sub_eq_zero, Nat.cast_inj]
  by_cases hcase : ∃ ξ, MMP.Intersection.IsCentre ℂ sY ξ V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a
  · -- some valuation at `C` has `a < 2`: the weights at `C` are those of the echoes
    obtain ⟨ξ, hξc, hξa⟩ := hcase
    obtain ⟨hη, S₀, hS₀L, hVS₀, huniq, -⟩ := h𝒮gen V hVdim hV𝒮 ξ hξc hξa
    obtain ⟨h₀, rfl⟩ := hmemL S₀ hS₀L
    obtain ⟨hex, -, hdist⟩ := existsUnique_isEcho hnv hdim hS₀L hVS₀ hVdim hη
    let g : ℕ → Valuation Y.functionField (WithZero (Multiplicative ℤ)) := fun j =>
      if h : 1 ≤ j then (hex j h).exists.choose else (hex 1 le_rfl).exists.choose
    have hg : ∀ j, 1 ≤ j → IsEcho sY L (c h₀) V j (g j) := fun j h => by
      simp only [g, dif_pos h]
      exact (hex j h).exists.choose_spec
    have hgc : ∀ j, 1 ≤ j → MMP.Intersection.IsCentre ℂ sY (g j) V := fun j h =>
      (hg j h).2.2.2.2.2.2.2.1
    have hval : ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ sY v V}, w v =
        defaultWeight Q.scale ((Θ.coeff (c h₀) : ℚ) : ℝ) := by
      rw [finsum_mem_eq_finsum_mem_comp (g := g) (s := {j | 1 ≤ j})
        (fun j hj j' hj' he => by_contra fun hne => hdist j j' _ _ (hg j hj) (hg j' hj') hne he)
        (by rintro _ ⟨j, hj, rfl⟩; exact hgc j hj)
        (fun v ⟨hv, hwv0⟩ => by
          obtain ⟨-, S', hS'L, hVS', -, j, hj, he, -⟩ := h𝒮gen V hVdim hV𝒮 v hv (hwpos v hv hwv0)
          obtain rfl := huniq S' hS'L hVS'
          exact ⟨j, hj, (hex j hj).unique (hg j hj) he⟩)]
      refine finsum_mem_congr rfl fun j (hj : 1 ≤ j) => ?_
      obtain ⟨a, ha, h⟩ := hw' _ (hgc j hj)
      rw [h, HasLogDiscrepancy.unique ha ((hg j hj).hasLogDiscrepancy hpair hsupp hlt)]
      congr 1
      ring
    rw [hval, finsum_eq_single _ h₀ fun S hS => ?_]
    · haveI : AlgebraicGeometry.IsVariety ℂ sY := hnv.1
      rw [hr', hd', show branchNumber (c h₀) (closure {γ.point}) = 1 from
        branchNumber_eq_one (sY := sY) hdim (c h₀) hVdim hVS₀
          ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 (c h₀) (hcL h₀)), one_mul]
    · rw [hr', branchNumber_eq_zero_of_not_subset (Z := closure {γ.point})
        (fun h => hS (hcinj (huniq _ (hcL S) h))), zero_mul]
  · -- no valuation at `C` has `a < 2`: all weights at `C` and all defaults through `C` vanish
    push Not at hcase
    rw [finsum_mem_eq_zero_of_forall_eq_zero (s := {v | MMP.Intersection.IsCentre ℂ sY v V})
        fun v hv => by_contra fun hne =>
        let ⟨a, ha, hla⟩ := hwpos v hv hne; hcase v hv a ha hla,
      finsum_eq_zero_of_forall_eq_zero fun S => ?_]
    by_cases hVS : closure {γ.point} ⊆ (c S).support
    · have hb : Θ.coeff (c S) = 0 := by
        by_contra hb
        haveI := hreg V hVdim
        obtain ⟨v, hvc, a, ha, hla⟩ := exists_isCentre_hasLogDiscrepancy_lt_two hpair hnv hdim
          hVdim hVS (lt_of_le_of_ne (hccoeff S).1 (Ne.symm hb))
        exact hcase v hvc a ha hla
      rw [hd', hb, Rat.cast_zero, defaultWeight_zero, mul_zero]
    · rw [hr', branchNumber_eq_zero_of_not_subset hVS, zero_mul]

/-- **Brackets vanish at almost every curve.** On a model `(Y, Θ)` of a prepared chain, only
finitely many irreducible closed curves `C ⊆ Y` have a nonzero bracket `β_C(Y, Θ)`
(`MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`). -/
private theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.finite_setOf_isCurveBracket_ne_zero
    {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    (x : Q.ModelIndex) :
    {γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1) |
      ∃ β : ℤ, Q.IsCurveBracket x γ β ∧ β ≠ 0}.Finite := by
  obtain ⟨𝒮, h𝒮, key⟩ := exists_finite_forall_isCurveBracket_eq_zero Q x
  refine (finite_setOf_closure_point_mem (h𝒮.image ((↑) : IrreducibleCloseds _ → Set _))).subset
    fun γ ⟨β, hβ, hβ0⟩ => ?_
  by_contra hγ
  exact hβ0 (key γ hγ β hβ)

end MMP.IndexdStrict.Card_brackets_cofinite

end

/-! ### Port of `lem_mmp_indexd_coefficient_move_echo_unchanged` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.IndexdStrict.Card_coefficient_move_echo_unchanged

/-! ### Weights of the orders of a default -/

/-- If the defaults `d(b)` and `d(b')` agree, for `b, b' < 1`, then so do the weights
`w(1 - j(1 - b))` and `w(1 - j(1 - b'))` of every order `j ≥ 1`. -/
private theorem difficultyWeight_eq_of_defaultWeight_eq (N : ℕ) {b b' : ℝ} (hb : b < 1)
    (hb' : b' < 1) (hd : defaultWeight N b = defaultWeight N b') {j : ℕ} (hj : 1 ≤ j) :
    difficultyWeight N (1 - j * (1 - b)) = difficultyWeight N (1 - j * (1 - b')) := by
  wlog hle : b' ≤ b generalizing b b'
  · exact (this hb' hb hd.symm (le_of_not_ge hle)).symm
  have hfin := (finite_support_difficultyWeight N hb).union (finite_support_difficultyWeight N hb')
  set s := hfin.toFinset
  let F : ℝ → ℕ → ℕ := fun c j => if 1 ≤ j then difficultyWeight N (1 - j * (1 - c)) else 0
  have key : ∀ c, (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - c))) ⊆ s →
      defaultWeight N c = ∑ j ∈ s, F c j := by
    intro c hc
    rw [defaultWeight, finsum_eq_sum_of_support_subset _ (s := s) ?_]
    · exact Finset.sum_congr rfl fun j _ => finsum_eq_if
    · intro j hj
      rw [Function.mem_support, finsum_eq_if] at hj
      split_ifs at hj with h1
      · exact hc hj
      · exact absurd rfl hj
  have h1 := key b (by rw [hfin.coe_toFinset]; exact Set.subset_union_left)
  have h2 := key b' (by rw [hfin.coe_toFinset]; exact Set.subset_union_right)
  have hle' : ∀ j ∈ s, F b' j ≤ F b j := fun j _ => by
    simp only [F]
    split_ifs
    · exact difficultyWeight_mono N
        (sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith) j.cast_nonneg) 1)
    · exact le_rfl
  have heq := (Finset.sum_eq_sum_iff_of_le hle').mp (by rw [← h1, ← h2, hd])
  by_cases hj' : j ∈ s
  · have := heq j hj'
    simp only [F, if_pos hj] at this
    exact this.symm
  · have : j ∉ (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - b))) ∪
        (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - b'))) :=
      fun h => hj' (hfin.mem_toFinset.mpr h)
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at this
    rw [this.1, this.2]

/-! ### Valuations of prime divisors -/

/-- Valuations with the same pull-back along a surjective ring map are equal. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (fun v : Valuation B Γ => v.comap φ) := by
  intro v v' h
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  exact congrArg (fun u : Valuation A Γ => u a) h

/-- `ord_P` regarded through a composite is `ord_P` regarded through the first map, restricted
along the second. -/
private theorem valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)] :
    P.valuationOver (f ≫ g) = (P.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- `valuationOver` only depends on the morphism. -/
private theorem valuationOver_congr {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {f g : X ⟶ Y} [hf : IsDominant f]
    [hg : IsDominant g] (h : f = g) : P.valuationOver f = P.valuationOver g := by
  subst h
  rfl

/-- On a normal variety, a prime divisor is determined by its valuation seen through a dominant
morphism inducing a surjection of function fields. -/
private theorem eq_of_valuationOver_eq {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : X ⟶ Y)
    [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    {P P' : MMP.Mori.PrimeDivisor X} (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have h1 : P.divisorialValuation = P'.divisorialValuation := comap_injective_of_surjective hf h
  have h2 : (DivisorOver.ofPrimeDivisor ℂ hX P).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hX P').valuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) =
      P'.divisorialValuation (functionFieldMap (𝟙 X) g)
    rw [MMP.Mori.functionFieldMap_id_apply, h1]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 h2)

/-- The image of a prime divisor under an isomorphism. -/
private noncomputable def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Transport of prime divisors along an isomorphism. -/
private noncomputable def primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W) :
    MMP.Mori.PrimeDivisor V ≃ MMP.Mori.PrimeDivisor W where
  toFun := mapOfIso e
  invFun := mapOfIso e.symm
  left_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e.symm (mapOfIso e Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp
  right_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e (mapOfIso e.symm Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp

private theorem genericPoint_primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  genericPoint_mapOfIso e Q

/-- Transport along an isomorphism preserves the divisorial valuation. -/
private theorem divisorialValuation_primeDivisorEquivOfIso {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (e : V ≅ W) [IsDominant e.hom] (Q : MMP.Mori.PrimeDivisor V) :
    Q.divisorialValuation.comap (functionFieldMap e.hom) =
      (primeDivisorEquivOfIso e Q).divisorialValuation := by
  ext g
  rw [Valuation.comap_apply]
  by_cases hg : g = 0
  · subst hg; simp
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (primeDivisorEquivOfIso e Q)
      (genericPoint_mapOfIso e Q).symm]

/-- `ord_Q` regarded through `e ≫ b`, for an isomorphism `e`, is `ord` of the transported prime
divisor regarded through `b`. -/
private theorem valuationOver_iso_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) (b : W ⟶ Z) [IsDominant b]
    [IsDominant e.hom] [IsDominant (e.hom ≫ b)] :
    Q.valuationOver (e.hom ≫ b) = (primeDivisorEquivOfIso e Q).valuationOver b := by
  rw [valuationOver_comp, PrimeDivisor.valuationOver, divisorialValuation_primeDivisorEquivOfIso]
  rfl

/-- The inverse transform along an isomorphism has, at `P`, the coefficient at the image of
`P`. -/
private theorem coeff_inverseTransformDivisor_iso {V W : Scheme.{0}} (e : V ≅ W)
    (D : MMP.Mori.QDivisor W) (P : MMP.Mori.PrimeDivisor V) :
    (inverseTransformDivisor e.hom D).coeff P = D.coeff (primeDivisorEquivOfIso e P) := by
  have htop : biregularLocus e.hom = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))
  exact MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint
    (genericPoint_mapOfIso e P).symm (by rw [htop]; trivial) D

/-! ### Label centres on the decreased pair -/

/-- Transported valuations are unique: the identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})` are
isomorphisms. -/
private theorem isTransportedValuationFrom_unique {T : StabilizedTail} : ∀ {i : ℕ}
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨_, hu, huw⟩, ⟨_, hu', huw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique hu hu'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    exact comap_injective_of_surjective
      ((T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
        |>.functionFieldMap_bijective.2)
      (huw.trans huw'.symm)

section LabelCentre

variable {T : StabilizedTail} (C : StabilizedTail.TerminalChain T)

/-- A label has at most one centre on a junction. -/
private theorem eq_of_isLabelCentre_none {S : C.Label} {i : ℕ}
    (hX : IsNormalVariety ℂ ((C.junction i).p ≫ T.sX i))
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  obtain ⟨w, hw, hP⟩ := h
  obtain ⟨w', hw', hP'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  exact eq_of_valuationOver_eq hX _ (C.junction i).isBirationalMorphism.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- The centre of a label on a junction `Y_i` is its centre on the first model `V_0 = Y_i` of the
`i`-th bridge. -/
private theorem isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨w, hw, (inferInstance : IsDominant ((C.junction i).p ≫ T.f i)), ?_⟩
  change P.valuationOver ((C.junction i).p ≫ T.f i) = _
  rw [valuationOver_comp, hP]

/-- A label has at most one centre on the first model of a bridge. -/
private theorem eq_of_isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    (hX : IsNormalVariety ℂ ((C.junction i).p ≫ T.sX i))
    {P P' : MMP.Mori.PrimeDivisor (C.junction i).Y}
    (h : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P) (h' : C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P') :
    P = P' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, _, hP⟩ := h
  obtain ⟨w', hw', _, hP'⟩ := h'
  obtain rfl := isTransportedValuationFrom_unique hw hw'
  have hb : IsBirationalMorphism ((C.junction i).p ≫ T.f i) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp (C.junction i).isBirationalMorphism
      (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
  exact eq_of_valuationOver_eq hX ((C.junction i).p ≫ T.f i) hb.functionFieldMap_bijective.2
    (hP.trans hP'.symm)

/-- When the `i`-th bridge has no step, its end identifies the decreased pair `(Y_i, Θ_i')` with
the next junction `(Y_{i+1}, Θ_{i+1})`. -/
private theorem exists_iso_of_m_eq_zero (i : ℕ) (hm : (C.bridge i).P.m = 0) :
    ∃ e : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
      (C.bridge i).Θ' = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ ∧
      (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (e : modelSeq (C.junction i).Y (C.bridge i).P.Y m ≅ (C.junction (i + 1)).Y),
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY m =
        e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i → m = 0 →
      ∃ e : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
        (C.bridge i).Θ' = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m e hb hπ rfl
    exact ⟨e, hb, hπ⟩
  exact key _ (C.bridge i).e (C.bridge i).boundary_eq (C.bridge i).modelMap_eq hm

/-- Through the identification `e : Y_i ≅ Y_{i+1}` of a bridge with no step, the centre of a
label on `Y_i` is carried to its centre on `Y_{i+1}`. -/
private theorem isLabelCentre_succ_of_iso {S : C.Label} {i : ℕ}
    (e : (C.junction i).Y ≅ (C.junction (i + 1)).Y)
    (hπ : (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i + 1, none⟩ (primeDivisorEquivOfIso e P) := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI : IsDominant e.hom := (isBirationalMorphism_of_isIso e.hom).isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨_, ⟨w, hw, ?_⟩, rfl⟩
  change ((primeDivisorEquivOfIso e P).valuationOver (C.junction (i + 1)).p).comap
    (functionFieldMap (T.fp i)) = w.comap (functionFieldMap (T.f i))
  rw [← valuationOver_comp, ← valuationOver_iso_comp, ← hP, ← valuationOver_comp]
  exact valuationOver_congr _ (by rw [hπ])

end LabelCentre

/-! ### Log discrepancies along an isomorphism -/

section IsoTransport

open MMP.Fourfold.Oai4C1.CommonModel

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X U : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [IsIntegral U]
    (hX : IsNormalVariety ℂ sX)
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

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- The divisor `(Y, f ≫ g, E)` over `W`, for a divisor `(Y, f, E)` over `V` and a dominant open
immersion `g : V ⟶ W`. -/
private noncomputable def compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) : DivisorOver ℂ sW where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc, hs]
  isBirationalMorphism := by
    haveI := D.isIntegral
    exact isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_of_isOpenImmersion g ⊤ dense_univ)
  E := D.E

/-- The valuation of `(Y, f ≫ g, E)` is that of `(Y, f, E)` carried along `g`. -/
private theorem valuation_compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) :
    (compOpen g hs D).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := (compOpen g hs D).isDominant
  refine Valuation.ext fun t => ?_
  change D.E.valuationOver (D.f ≫ g) t = D.E.valuationOver D.f (functionFieldMap g t)
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **Log discrepancies are invariant under isomorphisms of pairs.** Let `φ : V ≅ W` be an
isomorphism of normal varieties over `ℂ`, `B'` a `ℚ`-divisor on `W` and `B` the divisor on `V`
with `coeff_Γ B = coeff_{φ(Γ)} B'`. If `(Y, f, E)` is a divisor over `V` and `(Y', f', E')` one
over `W` with the corresponding valuation, then `a(E, V, B) = a(E', W, B')`. -/
private theorem eq_of_isLogDiscrepancy_of_iso [CompactSpace V] (φ : V ≅ W)
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : φ.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap φ.hom Γ))
    {n n' : ℕ} {D : DivisorOver ℂ sV} {D' : DivisorOver ℂ sW} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sV n (QDivisor.toRDivisor B) D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sW n' (QDivisor.toRDivisor B') D' a')
    (hv : D'.valuation = D.valuation.comap (functionFieldMap φ.hom)) : a = a' := by
  subst hs
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  obtain ⟨hW, -, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, -, hCc, hdec, -, -⟩ := id ha'
  obtain ⟨hV, -, -, -, ⟨K₀, hK₀, -⟩, -⟩ := id ha
  have hnn : n = n' := by
    have h1 := hK₀.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    rw [(Scheme.homeoOfIso φ).isHomeomorph.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm.trans h2
  subst hnn
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (φ.hom ≫ sW) := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hbφ : IsBirationalMorphism φ.hom := isBirationalMorphism_of_isIso _
  have hbij : Function.Bijective (functionFieldMap φ.hom) := hbφ.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW)
    hK'.topologicalKrullDim_eq
  -- the pull-backs `L_i = φ^* C_i` and `M_i = f^* L_i`
  choose L hL using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant φ.hom (hCc i)
  have hLc : ∀ i, (L i).IsCartier := fun i => (hL i).isCartier (hCc i)
  choose M hM using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hLc i)
  set Dφ := compOpen φ.hom rfl D
  haveI : IsDominant (D.f ≫ φ.hom) := Dφ.isDominant
  have hpφ : IsProper Dφ.f := by
    change IsProper (D.f ≫ φ.hom)
    infer_instance
  have hord : D.ordPullback (pullbackRationalPluriForms sW φ.hom ω) = Dφ.ordPullback ω := by
    change D.E.ordForm (pullbackRationalPluriForms (φ.hom ≫ sW) D.f
      (pullbackRationalPluriForms sW φ.hom ω)) =
        D.E.ordForm (pullbackRationalPluriForms sW (D.f ≫ φ.hom) ω)
    rw [pullbackRationalPluriForms_comp φ.hom D.f hbij
      (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
    rfl
  have h1 : MMP.Intersection.IsLogDiscrepancy sW n (QDivisor.toRDivisor B') Dφ
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) :=
    ⟨hW, hpφ, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, M, hCc, hdec, fun i => ⟨_, isPullback_comp
      (hL i) (hM i) (fun Z =>
      MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ φ.hom) (C i) Z)⟩, rfl⟩
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' h1
    (hv.trans (valuation_compOpen φ.hom rfl D).symm)
  -- the same data, pulled back to `V`
  have hne : pullbackRationalPluriForms sW φ.hom ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hW hbφ hK'.topologicalKrullDim_eq hω
  have hcan : (divisorOfForm (pullbackRationalPluriForms sW φ.hom ω)).IsCanonicalDivisor
      (φ.hom ≫ sW) n := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hne
    rw [one_smul] at this
    exact hK₀.of_linearlyEquivalent this
  have hdec2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      ((Γ.ordForm (pullbackRationalPluriForms sW φ.hom ω) : ℤ) : ℝ) +
        (QDivisor.toRDivisor B).coeff Γ = ∑ i, r i * ((L i).coeff Γ : ℝ) := by
    intro Γ
    set Γ' := OpenWeilRestriction.primeDivisorMap φ.hom Γ
    have hΓ : φ.hom Γ.genericPoint = Γ'.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso φ.hom hbij hd Γ Γ' hΓ ω,
      QDivisor.coeff_toRDivisor, hB Γ]
    simp_rw [MMP.Positivity.coeff_eq_of_isPullback Γ Γ' hΓ (hCc _) (hL _)]
    have := hdec Γ'
    rwa [QDivisor.coeff_toRDivisor] at this
  have h2 : MMP.Intersection.IsLogDiscrepancy (φ.hom ≫ sW) n (QDivisor.toRDivisor B) D
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) := by
    refine ⟨hV, hp, _, hne, ⟨_, hcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, L, M, hLc,
      hdec2, fun i => ⟨_, hM i⟩, ?_⟩
    rw [hord]
    rfl
  exact (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h2).trans e1.symm

/-- A divisor over a normal variety is exceptional exactly when the image of the generic point of
its divisor has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hX
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- `(Y, f ≫ e, E)` is exceptional over `W` when `(Y, f, E)` is exceptional over `V`, for an
isomorphism `e : V ≅ W`. -/
private theorem isExceptional_compOpen [CompactSpace V] (e : V ≅ W) {sW : W ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (hV : IsNormalVariety ℂ sV)
    (hW : IsNormalVariety ℂ sW) {D : DivisorOver ℂ sV} (hD : D.IsExceptional) :
    (compOpen e.hom hs D).IsExceptional := by
  rw [isExceptional_iff_two_le_coheight hW]
  rw [isExceptional_iff_two_le_coheight hV] at hD
  change 2 ≤ Order.coheight ((D.f ≫ e.hom) D.E.genericPoint)
  rwa [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- **Terminality is invariant under isomorphisms of pairs.** -/
private theorem isKltTerminalPair_of_iso [CompactSpace V] (e : V ≅ W) {sW : W ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) {B : QDivisor V} {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hklt : IsKltPair sV B) (hB' : IsKltTerminalPair sW B') : IsKltTerminalPair sV B := by
  refine ⟨hklt, fun n D a hD ha => ?_⟩
  have hV : IsNormalVariety ℂ sV := hklt.1.isPair.1
  have hW : IsNormalVariety ℂ sW := hB'.1.1.isPair.1
  obtain ⟨-, n₀, K, hK, -⟩ := hB'.1.1.isPair
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  have hp' : IsProper (compOpen e.hom hs D).f := by
    change IsProper (D.f ≫ e.hom)
    infer_instance
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB'.1.1.isPair hK
    (compOpen e.hom hs D)
  have ha' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp'
  have hB2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap e.hom Γ) := fun Γ => by
    have hΓ : primeDivisorEquivOfIso e Γ = OpenWeilRestriction.primeDivisorMap e.hom Γ :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_primeDivisorEquivOfIso e Γ).trans
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm)
    rw [hB Γ, hΓ]
  rw [eq_of_isLogDiscrepancy_of_iso e hs hB2 ha ha' (valuation_compOpen e.hom hs D)]
  exact hB'.2 n₀ _ _ (isExceptional_compOpen e hs hV hW hD) ha'

end IsoTransport

/-! ### The decreased pair -/

/-- The decreased pair `(Y_i, Θ_i')` of a prepared chain, `i ≥ i₀`, is terminal, supported on
the label centres `c S` of the junction `Y_i`, with coefficients in `[0, 1)` there, and every
default `d(b_h)` of the junction agrees with `d(b_h')` of the decreased pair. -/
private theorem decreased_setting {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i)
    (c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩))
    (hc : ∀ S, Q.chain.IsLabelCentre S ⟨i, none⟩ (c S)) :
    IsKltTerminalPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' ∧
      (∀ P, (Q.chain.bridge i).Θ'.coeff P ≠ 0 → P ∈ Set.range c) ∧
      ∀ S, 0 ≤ (Q.chain.bridge i).Θ'.coeff (c S) ∧ (Q.chain.bridge i).Θ'.coeff (c S) < 1 ∧
        defaultWeight Q.scale ((Q.chain.modelBoundary ⟨i, none⟩).coeff (c S) : ℝ) =
          defaultWeight Q.scale ((Q.chain.bridge i).Θ'.coeff (c S) : ℝ) := by
  classical
  obtain ⟨hΘ, -, -, -, -, -⟩ := StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, none⟩, hi⟩
  have hX : IsNormalVariety ℂ ((Q.chain.junction i).p ≫ T.sX i) := hΘ.1.1.isPair.1
  have hd0 : ∀ S d, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ d →
      d = defaultWeight Q.scale ((Q.chain.modelBoundary ⟨i, none⟩).coeff (c S) : ℝ) := by
    rintro S d ⟨b, ⟨P, hP, rfl⟩, rfl⟩
    rw [eq_of_isLabelCentre_none Q.chain hX hP (hc S)]
  by_cases hm : 0 < (Q.chain.bridge i).P.m
  · obtain ⟨hΘy, -, -, -, ⟨c', -, hc'c, hc'supp, hc'coeff⟩, -⟩ :=
      StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, some ⟨0, hm⟩⟩, hi⟩
    have hcc' : ∀ S, c' S = c S := fun S =>
      eq_of_isLabelCentre_some_zero Q.chain hm hX (hc'c S)
        (isLabelCentre_some_zero Q.chain hm (hc S))
    refine ⟨hΘy, fun P hP => ?_, fun S => ?_⟩
    · obtain ⟨S, hS⟩ := hc'supp P hP
      exact ⟨S, (hcc' S).symm.trans hS⟩
    · obtain ⟨h0, h1⟩ := hc'coeff S
      rw [hcc' S] at h0 h1
      refine ⟨h0, h1, ?_⟩
      obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
      rw [← hd0 S d (hd ⟨i, none⟩ hi)]
      obtain ⟨b, ⟨P, hP, rfl⟩, rfl⟩ := hd ⟨i, some ⟨0, hm⟩⟩ hi
      rw [eq_of_isLabelCentre_some_zero Q.chain hm hX hP
        (isLabelCentre_some_zero Q.chain hm (hc S))]
      rfl
  · have hm0 : (Q.chain.bridge i).P.m = 0 := by omega
    obtain ⟨e, hΘe, hπ⟩ := exists_iso_of_m_eq_zero Q.chain i hm0
    obtain ⟨hΘ1, -, -, -, ⟨c1, -, hc1c, hc1supp, hc1coeff⟩, -⟩ :=
      StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i + 1, none⟩, Nat.le_succ_of_le hi⟩
    have hX1 : IsNormalVariety ℂ ((Q.chain.junction (i + 1)).p ≫ T.sX (i + 1)) :=
      hΘ1.1.1.isPair.1
    have hs : e.hom ≫ (Q.chain.junction (i + 1)).p ≫ T.sX (i + 1) =
        (Q.chain.junction i).p ≫ T.sX i := by
      have h1 := congrArg (· ≫ T.sZ i) hπ
      simp only [Category.assoc] at h1
      rw [(T.isThreefoldStepDiagram i).comp_eq_minus,
        (T.isThreefoldStepDiagram i).comp_eq_plus] at h1
      exact h1.symm
    have hcoeff : ∀ P, (Q.chain.bridge i).Θ'.coeff P =
        (Q.chain.junction (i + 1)).Θ.coeff (primeDivisorEquivOfIso e P) := fun P => by
      rw [hΘe]
      exact coeff_inverseTransformDivisor_iso e _ P
    have hc1 : ∀ S, primeDivisorEquivOfIso e (c S) = c1 S := fun S =>
      eq_of_isLabelCentre_none Q.chain hX1 (isLabelCentre_succ_of_iso Q.chain e hπ (hc S)) (hc1c S)
    refine ⟨isKltTerminalPair_of_iso e hs hcoeff (Q.chain.bridge i).P.isKltPair hΘ1,
      fun P hP => ?_, fun S => ?_⟩
    · rw [hcoeff] at hP
      obtain ⟨S, hS⟩ := hc1supp _ hP
      exact ⟨S, (primeDivisorEquivOfIso e).injective ((hc1 S).trans hS)⟩
    · rw [hcoeff (c S), hc1 S]
      refine ⟨(hc1coeff S).1, (hc1coeff S).2, ?_⟩
      obtain ⟨d, hd⟩ := Q.isLabelDefault_const S
      rw [← hd0 S d (hd ⟨i, none⟩ hi)]
      obtain ⟨b, ⟨P, hP, rfl⟩, rfl⟩ := hd ⟨i + 1, none⟩ (Nat.le_succ_of_le hi)
      rw [eq_of_isLabelCentre_none Q.chain hX1 hP (hc1c S)]
      rfl

/-! ### Log discrepancies of valuations -/

/-- A valuation with a log discrepancy over a proper model has that log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- **Weights at generic curves are unchanged by a coefficient decrease.** Let `i ≥ i₀` index a
junction `(Y_i, Θ_i)` of a prepared chain, and let `Θ_i'` be the decreased boundary of the
`i`-th bridge. There is a finite set `𝓔` of irreducible closed curves of `Y_i` such that for
every curve `C ∉ 𝓔` and every normalized divisorial valuation `v` of `ℂ(Y_i)` with centre `C`,
the weight `w(2 - a(v; Y_i, Θ_i'))` of `v` for `Θ_i'` equals its weight for `Θ_i`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`, at the fixed admissible
scale). -/
private theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.exists_finite_isValuationWeight_eq
    {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) :
    ∃ 𝓔 : Set (MMP.Mori.ProperCurve (Q.chain.modelStructure ⟨i, none⟩)), 𝓔.Finite ∧
      ∀ γ ∉ 𝓔,
        ∀ v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
          (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point}) →
          ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
            (MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
              ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
                  (Q.chain.bridge i).Θ' v a ∧ w' = difficultyWeight Q.scale (2 - a)) →
            w' = w := by
  classical
  set Y := Q.chain.model ⟨i, none⟩
  set sY := Q.chain.modelStructure ⟨i, none⟩
  set Θ := Q.chain.modelBoundary ⟨i, none⟩
  set Θ' := (Q.chain.bridge i).Θ'
  obtain ⟨hΘ, hY, hQ, hdim, ⟨c, -, hcc, hcsupp, hccoeff⟩, -⟩ :=
    StabilizedTail.PreparedChain.echoSetting_model Q ⟨⟨i, none⟩, hi⟩
  obtain ⟨hΘ', hcsupp', hccoeff'⟩ := decreased_setting Q hi c hcc
  have : Finite Q.chain.Label := StabilizedTail.TerminalChain.finite_label Q.chain
  set L : Finset (MMP.Mori.PrimeDivisor Y) := (Set.finite_range c).toFinset
  have hmemL : ∀ S ∈ L, ∃ h, c h = S := fun S hS => (Set.finite_range c).mem_toFinset.mp hS
  have hsupp : Θ.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp P (Finsupp.mem_support_iff.mp hP))
  have hsupp' : Θ'.support ⊆ L := fun P hP =>
    (Set.finite_range c).mem_toFinset.mpr (hcsupp' P (Finsupp.mem_support_iff.mp hP))
  have hlt : ∀ S ∈ L, Θ.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff h).2
  have hlt' : ∀ S ∈ L, Θ'.coeff S < 1 := fun S hS => by
    obtain ⟨h, rfl⟩ := hmemL S hS
    exact (hccoeff' h).2.1
  obtain ⟨𝒮, h𝒮, -, h𝒮gen⟩ :=
    exists_finite_forall_isEcho_of_isCentre sY hY hQ hdim hΘ hsupp
  obtain ⟨𝒮', h𝒮', -, h𝒮gen'⟩ :=
    exists_finite_forall_isEcho_of_isCentre sY hY hQ hdim hΘ' hsupp'
  refine ⟨{γ | ∃ Z ∈ 𝒮 ∪ 𝒮', (Z : Set Y) = closure {γ.point}}, ?_, ?_⟩
  · refine ((h𝒮.union h𝒮').biUnion fun Z _ =>
      (?_ : Set.Subsingleton {γ : MMP.Mori.ProperCurve sY |
        (Z : Set Y) = closure {γ.point}}).finite).subset ?_
    · rintro ⟨p, hp⟩ (h : (Z : Set Y) = closure {p}) ⟨p', hp'⟩ (h' : (Z : Set Y) = closure {p'})
      obtain rfl : p = p' := (inseparable_iff_closure_eq.mpr (h.symm.trans h')).eq
      rfl
    · rintro γ ⟨Z, hZ, h⟩
      exact Set.mem_biUnion hZ h
  · rintro γ hγ v ⟨Z, hcen, hZ⟩ w w' ⟨-, a, ha, rfl⟩ ⟨-, a', ha', rfl⟩
    have hZ𝒮 : Z ∉ 𝒮 ∪ 𝒮' := fun h => hγ ⟨Z, h, hZ⟩
    have hZdim : topologicalKrullDim (Z : Set Y) = 1 := hZ ▸ γ.topologicalKrullDim_closure_point
    have hla := IsValuationLogDiscrepancy.hasLogDiscrepancy ha
    have hla' := IsValuationLogDiscrepancy.hasLogDiscrepancy ha'
    -- an echo has the same weight for both boundaries
    have hecho : ∀ (S : MMP.Mori.PrimeDivisor Y) (j : ℕ), S ∈ L → 1 ≤ j →
        IsEcho sY L S Z j v →
        difficultyWeight Q.scale (2 - a') = difficultyWeight Q.scale (2 - a) := by
      intro S j hS hj he
      obtain ⟨h, rfl⟩ := hmemL S hS
      have e1 := HasLogDiscrepancy.unique hla (he.hasLogDiscrepancy hΘ.1.1 hsupp hlt)
      have e2 := HasLogDiscrepancy.unique hla' (he.hasLogDiscrepancy hΘ'.1.1 hsupp' hlt')
      have hsub : ∀ x : ℝ, (2 : ℝ) - (1 + (j : ℝ) * (1 - x)) = 1 - j * (1 - x) :=
        fun x => by ring
      rw [e1, e2, hsub, hsub]
      exact (difficultyWeight_eq_of_defaultWeight_eq Q.scale
        (by exact_mod_cast (hccoeff h).2) (by exact_mod_cast (hccoeff' h).2.1)
        (hccoeff' h).2.2 hj).symm
    by_cases h2 : a < 2
    · obtain ⟨-, S, hS, -, -, j, hj, he, -⟩ :=
        h𝒮gen Z hZdim (fun h => hZ𝒮 (Or.inl h)) v hcen ⟨a, h2, hla⟩
      exact hecho S j hS hj he
    by_cases h2' : a' < 2
    · obtain ⟨-, S, hS, -, -, j, hj, he, -⟩ :=
        h𝒮gen' Z hZdim (fun h => hZ𝒮 (Or.inr h)) v hcen ⟨a', h2', hla'⟩
      exact hecho S j hS hj he
    rw [difficultyWeight_of_nonpos (by linarith), difficultyWeight_of_nonpos (by linarith)]

end MMP.IndexdStrict.Card_coefficient_move_echo_unchanged

end

/-! ### Port of `lem_mmp_indexd_coefficient_move_difference` -/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace MMP.IndexdStrict.Card_coefficient_move_difference

open MMP.IndexdStrict.Card_coefficient_move_echo_unchanged

/-! ### Transport along an isomorphism of normal varieties -/

section Transport

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- Transporting a valuation along `e` and back along `e⁻¹` gives it back. -/
private theorem comap_inv_comap_hom (e : V ≅ W)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) :
    (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.inv) = v := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (e.hom_inv_id),
    MMP.Mori.functionFieldMap_id_apply]

/-- The centre of a transported valuation is the image of the centre. -/
private theorem isCentre_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hs : e.hom ≫ sW = sV) {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {Z : IrreducibleCloseds V} (h : MMP.Intersection.IsCentre ℂ sV v Z) :
    ∃ Z' : IrreducibleCloseds W, MMP.Intersection.IsCentre ℂ sW
      (v.comap (functionFieldMap e.hom)) Z' ∧ (Z' : Set W) = e.hom.base '' Z := by
  obtain ⟨D, hp, rfl, rfl⟩ := h
  refine ⟨(compOpen e.hom hs D).center,
    ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, rfl⟩, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
      MMP.Positivity.DivisorOver.center_eq_closureSingleton]
    change closure {(D.f ≫ e.hom) D.E.genericPoint} = e.hom.base '' closure {D.f D.E.genericPoint}
    have := (Scheme.homeoOfIso e).image_closure ({D.f D.E.genericPoint} : Set V)
    rw [Set.image_singleton] at this
    rw [Scheme.Hom.comp_apply]
    exact this.symm

/-- A transported exceptional valuation is exceptional. -/
private theorem isExceptionalValuation_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV)
    {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sV v) :
    MMP.Intersection.IsExceptionalValuation ℂ sW (v.comap (functionFieldMap e.hom)) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hc ⊢
    change 2 ≤ Order.coheight ((D.f ≫ e.hom) D.E.genericPoint)
    rwa [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- Log discrepancies are carried along an isomorphism of pairs. -/
private theorem isValuationLogDiscrepancy_comap [CompactSpace V] (e : V ≅ W)
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W} (hB : ∀ Γ, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hB' : MMP.Mori.IsPair sW B') {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sV B v a) :
    IsValuationLogDiscrepancy sW B' (v.comap (functionFieldMap e.hom)) a := by
  obtain ⟨n, D, hp, rfl, ha⟩ := h
  obtain ⟨-, n₀, K, hK, -⟩ := id hB'
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp' : IsProper (compOpen e.hom hs D).f := by
    change IsProper (D.f ≫ e.hom)
    infer_instance
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB' hK (compOpen e.hom hs D)
  have ha' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp'
  have hB2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap e.hom Γ) := fun Γ => by
    have hΓ : primeDivisorEquivOfIso e Γ = OpenWeilRestriction.primeDivisorMap e.hom Γ :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_primeDivisorEquivOfIso e Γ).trans
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm)
    rw [hB Γ, hΓ]
  have hac := eq_of_isLogDiscrepancy_of_iso e hs hB2 ha ha' (valuation_compOpen e.hom hs D)
  exact ⟨n₀, compOpen e.hom hs D, hp', valuation_compOpen e.hom hs D, hac ▸ ha'⟩

end Transport

/-! ### Curves, prime divisors and normalizations along an isomorphism -/

section IsoCurves

variable {V W : Scheme.{0}}

/-- An isomorphism carries the closure of a point to the closure of its image. -/
private theorem image_closure_singleton (e : V ≅ W) (x : V) :
    e.hom.base '' closure ({x} : Set V) = closure {e.hom x} := by
  have := (Scheme.homeoOfIso e).image_closure ({x} : Set V)
  rw [Set.image_singleton] at this
  exact this

private theorem inv_comp_eq_of_hom_comp_eq (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) : e.inv ≫ sV = sW := by
  rw [← hs, Iso.inv_hom_id_assoc]

private theorem inv_hom_apply (e : V ≅ W) (x : W) : e.hom (e.inv x) = x := by
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

private theorem hom_inv_apply (e : V ≅ W) (x : V) : e.inv (e.hom x) = x := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- The image of a proper curve under an isomorphism over `ℂ`. -/
private noncomputable def properCurveMap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (γ : ProperCurve sV) : ProperCurve sW :=
  ⟨e.hom γ.point,
    MMP.Chow.DeterminantCurveForm.isProperCurve_iso e sV sW hs γ.point γ.isProperCurve⟩

private theorem closure_properCurveMap_point (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (γ : ProperCurve sV) :
    closure {(properCurveMap e hs γ).point} = e.hom.base '' closure {γ.point} :=
  (image_closure_singleton e γ.point).symm

/-- Proper curves correspond along an isomorphism over `ℂ`. -/
private noncomputable def properCurveEquiv (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) : ProperCurve sV ≃ ProperCurve sW where
  toFun := properCurveMap e hs
  invFun := properCurveMap e.symm (inv_comp_eq_of_hom_comp_eq e hs)
  left_inv γ := ProperCurve.ext (hom_inv_apply e γ.point)
  right_inv γ := ProperCurve.ext (inv_hom_apply e γ.point)

private theorem properCurveEquiv_apply (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) (γ : ProperCurve sV) :
    properCurveEquiv e hs γ = properCurveMap e hs γ := rfl

/-- The support of a transported prime divisor is the image of the support. -/
private theorem support_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e P).support = e.hom.base '' P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_closure_singleton]
  have h := genericPoint_primeDivisorEquivOfIso e P
  exact congrArg (fun x => closure {x}) h

private theorem primeDivisorEquivOfIso_symm_apply (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P) = P :=
  (primeDivisorEquivOfIso e).left_inv P

/-- The ideal sheaf of a transported prime divisor is the image of the ideal sheaf. -/
private theorem idealSheaf_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.map e.hom = (primeDivisorEquivOfIso e P).idealSheaf := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      (primeDivisorEquivOfIso e P).idealSheaf _ rfl, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  change closure (e.hom.base '' P.support) = (primeDivisorEquivOfIso e P).support
  rw [support_primeDivisorEquivOfIso]
  exact ((Scheme.homeoOfIso e).isClosedMap _ P.idealSheaf.support.isClosed).closure_eq

/-- The closed subschemes of a prime divisor and of its transport are isomorphic. -/
private noncomputable def subschemeIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.subscheme ≅ (primeDivisorEquivOfIso e P).idealSheaf.subscheme where
  hom := P.idealSheaf.subschemeMap (primeDivisorEquivOfIso e P).idealSheaf e.hom
    (idealSheaf_primeDivisorEquivOfIso e P).ge
  inv := (primeDivisorEquivOfIso e P).idealSheaf.subschemeMap P.idealSheaf e.inv (by
    have h := idealSheaf_primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P)
    rw [primeDivisorEquivOfIso_symm_apply] at h
    exact h.ge)
  hom_inv_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp
  inv_hom_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp

private theorem subschemeIso_hom_ι (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (subschemeIso e P).hom ≫ (primeDivisorEquivOfIso e P).idealSheaf.subschemeι =
      P.idealSheaf.subschemeι ≫ e.hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ (idealSheaf_primeDivisorEquivOfIso e P).ge

/-- Isomorphic schemes have isomorphic normalizations, compatibly with the normalization
morphisms. -/
private theorem exists_iso_normalizationScheme_of_iso {X X' : Scheme}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hX' : ∀ U : X'.Opens, IsCompact (U : Set X') → (irreducibleComponents U).Finite)
    (e : X ≅ X') :
    ∃ E : X.normalizationScheme hX ≅ X'.normalizationScheme hX',
      E.hom ≫ X'.normalization hX' = X.normalization hX ≫ e.hom := by
  have hgen : ∀ {Y Y' : Scheme} (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) (e : Y ≅ Y') (η : genericPoints (Y.normalizationScheme hY)),
      (Y.normalization hY ≫ e.hom) η.1 ∈ genericPoints Y' := fun hY e η =>
    genericPoints_image_of_generalizingMap _ (Scheme.homeoOfIso e).isOpenEmbedding.generalizingMap
      (Scheme.normalization_mem_genericPoints _ hY η.2)
  have := X.isNormal_normalizationScheme hX
  have := X'.isNormal_normalizationScheme hX'
  obtain ⟨a, ha, -⟩ := Scheme.existsUnique_lift_normalization hX' _ (hgen hX e)
  obtain ⟨b, hb, -⟩ := Scheme.existsUnique_lift_normalization hX _ (hgen hX' e.symm)
  obtain ⟨g, -, hu⟩ := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η => Scheme.normalization_mem_genericPoints _ hX η.2)
  obtain ⟨g', -, hu'⟩ := Scheme.existsUnique_lift_normalization hX' (X'.normalization hX')
    (fun η => Scheme.normalization_mem_genericPoints _ hX' η.2)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [hu (a ≫ b) (by dsimp only; rw [Category.assoc, hb, ← Category.assoc, ha]; simp),
      hu (𝟙 _) (by dsimp only; simp)]
  · rw [hu' (b ≫ a) (by dsimp only; rw [Category.assoc, ha, ← Category.assoc, hb]; simp),
      hu' (𝟙 _) (by dsimp only; simp)]

/-- The normalizations of a prime divisor and of its transport are isomorphic over the
isomorphism. -/
private theorem exists_iso_primeDivisorNormalizationScheme (e : V ≅ W)
    (P : MMP.Mori.PrimeDivisor V) :
    ∃ E : primeDivisorNormalizationScheme P ≅
        primeDivisorNormalizationScheme (primeDivisorEquivOfIso e P),
      E.hom ≫ primeDivisorNormalization (primeDivisorEquivOfIso e P) =
        primeDivisorNormalization P ≫ e.hom := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  obtain ⟨E, hE⟩ := exists_iso_normalizationScheme_of_iso
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) (subschemeIso e P)
  refine ⟨E, ?_⟩
  change E.hom ≫ (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) =
    (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) ≫ e.hom
  rw [← Category.assoc, hE, Category.assoc, subschemeIso_hom_ι, Category.assoc]

/-- **Branch numbers are invariant under isomorphism.** -/
private theorem branchNumber_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (Z : Set V) :
    branchNumber (primeDivisorEquivOfIso e P) (e.hom.base '' Z) = branchNumber P Z := by
  obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme e P
  have key : ∀ R : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      primeDivisorNormalization (primeDivisorEquivOfIso e P) ''
          (primeDivisorEquivOfIso E R).support =
        e.hom.base '' (primeDivisorNormalization P '' R.support) := by
    intro R
    rw [support_primeDivisorEquivOfIso, Set.image_image, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    simpa using congrArg (fun f => f.base x) hE
  have hinj : Function.Injective (Set.image e.hom.base) :=
    Set.image_injective.mpr (Scheme.homeoOfIso e).injective
  unfold branchNumber
  rw [← Set.ncard_image_of_injective _ (primeDivisorEquivOfIso E).injective]
  congr 1
  ext R'
  refine ⟨fun h => ⟨(primeDivisorEquivOfIso E).symm R', hinj ?_, Equiv.apply_symm_apply _ _⟩, ?_⟩
  · rw [← key, Equiv.apply_symm_apply]
    exact h
  · rintro ⟨R, hR, rfl⟩
    change _ = _
    rw [key]
    exact congrArg _ hR

/-- **Boxed ranks are invariant under isomorphism over `ℂ`.** -/
private theorem boxedSurfaceRank_eq_of_iso {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X'.Over (Spec (.of ℂ))] [MMP.IsComplexScheme X]
    [MMP.IsComplexScheme X'] (E : X ≅ X')
    (hE : E.hom ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ)) :
    boxedSurfaceRank X = boxedSurfaceRank X' := by
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1)).Over
      (Spec (.of ℂ)) := ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1⟩
  haveI := MMP.Fourfold.isComplexScheme_projectiveSpace 1 rfl
  let G : CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) ≅
      CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ))
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) :=
    asIso (Limits.pullback.map _ _ _ _ E.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hE])
      (by rw [Category.comp_id, Category.id_comp]))
  have hG : G.hom ≫ (Limits.pullback.snd _ _ ≫
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) =
      Limits.pullback.snd _ _ ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1 := by
    simp only [G, asIso_hom, Limits.pullback.map, Limits.pullback.lift_snd_assoc,
      Category.comp_id]
  haveI : MMP.IsComplexScheme (CategoryTheory.Limits.pullback (X ↘ Spec (.of ℂ))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback X _
  haveI : MMP.IsComplexScheme (CategoryTheory.Limits.pullback (X' ↘ Spec (.of ℂ))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback X' _
  exact (MMP.Analytic.cycleRank_eq_of_iso G hG).2.2.2 2

end IsoCurves

/-! ### Centres of exceptional valuations on a threefold -/

section Centres

variable {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}

/-- The centre of a valuation on a variety is unique. -/
private theorem isCentre_unique (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    (h : MMP.Intersection.IsCentre ℂ sX v Z) (h' : MMP.Intersection.IsCentre ℂ sX v Z') :
    Z = Z' := by
  obtain ⟨D, -, rfl, rfl⟩ := h
  obtain ⟨D', -, hv, rfl⟩ := h'
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX hv]

/-- **Exceptional centres on a threefold.** An exceptional valuation of a proper threefold over
`ℂ` has a centre, and the centre is a closed point or a proper curve. -/
private theorem exists_isCentre_of_isExceptionalValuation [LocallyOfFiniteType sX] [IsProper sX]
    (hdim : topologicalKrullDim X = 3)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sX v) :
    ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧
      ((∃ p : X, (Z : Set X) = {p}) ∨ ∃ γ : ProperCurve sX, (Z : Set X) = closure {γ.point}) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨D.center, ⟨D, hp, rfl, rfl⟩, ?_⟩
  rw [MMP.Positivity.DivisorOver.codimension_center] at hc
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton]
  set z := D.f D.E.genericPoint
  have hK : Order.krullDim X = 3 := by
    rw [← hdim]
    exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  have hno : ∀ w₁ w₂ : X, z ⤳ w₁ → w₁ ⤳ w₂ → z ≠ w₁ → w₁ ≠ w₂ → False := by
    intro w₁ w₂ h1 h2 h3 h4
    have l1 : w₁ < z := lt_of_le_not_ge (show w₁ ≤ z from h1)
      fun h => h3 (h1.antisymm (show w₁ ⤳ z from h)).eq
    have l2 : w₂ < w₁ := lt_of_le_not_ge (show w₂ ≤ w₁ from h2)
      fun h => h4 (h2.antisymm (show w₂ ⤳ w₁ from h)).eq
    have e1 := Order.height_add_one_le l2
    have e2 := Order.height_add_one_le l1
    have hht : (2 : ℕ∞) ≤ Order.height z :=
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Order.height w₂ + 1 + 1 := by gcongr; exact zero_le
        _ ≤ Order.height w₁ + 1 := by gcongr
        _ ≤ Order.height z := e2
    have hk := Order.height_add_coheight_le_krullDim z
    rw [hK] at hk
    have hk' : Order.height z + Order.coheight z ≤ 3 := by
      have : ((Order.height z + Order.coheight z : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        exact hk
      exact WithBot.coe_le_coe.mp this
    have h4 : (4 : ℕ∞) ≤ 3 := by
      calc (4 : ℕ∞) = 2 + 2 := by norm_num
        _ ≤ Order.height z + Order.coheight z := add_le_add hht hc
        _ ≤ 3 := hk'
    exact absurd h4 (by decide)
  rcases MMP.Chow.DeterminantCurveForm.isClosed_or_isProperCurve sX z hno with hcl | hpc
  · exact Or.inl ⟨z, hcl.closure_eq⟩
  · exact Or.inr ⟨⟨z, hpc⟩, rfl⟩

/-- A point centre and a curve centre of the same valuation cannot both occur. -/
private theorem not_isCentre_singleton_and_closure (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    {p : X} (γ : ProperCurve sX) (h : MMP.Intersection.IsCentre ℂ sX v Z) (hZ : (Z : Set X) = {p})
    (h' : MMP.Intersection.IsCentre ℂ sX v Z') (hZ' : (Z' : Set X) = closure {γ.point}) :
    False := by
  obtain rfl := isCentre_unique hX h h'
  have h1 := γ.topologicalKrullDim_closure_point
  rw [← hZ', hZ, topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at h1
  exact absurd h1 (by decide)

/-- Two curve centres of the same valuation are the same curve. -/
private theorem eq_of_isCentre_closure (hX : MMP.Mori.IsVariety ℂ sX)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z Z' : IrreducibleCloseds X}
    {γ γ' : ProperCurve sX} (h : MMP.Intersection.IsCentre ℂ sX v Z)
    (hZ : (Z : Set X) = closure {γ.point}) (h' : MMP.Intersection.IsCentre ℂ sX v Z')
    (hZ' : (Z' : Set X) = closure {γ'.point}) : γ = γ' := by
  obtain rfl := isCentre_unique hX h h'
  exact ProperCurve.ext (inseparable_iff_closure_eq.mpr (hZ.symm.trans hZ')).eq

end Centres

/-! ### Finite sums -/

/-- A finsum over `s` whose support in `s` lies in a finite set `t` is a sum over `t`. -/
private theorem natCast_finsum_mem_eq_sum {α : Type*} {f : α → ℕ} {s : Set α} (t : Finset α)
    (h : s ∩ Function.support f ⊆ t) [DecidablePred (· ∈ s)] :
    ((∑ᶠ a ∈ s, f a : ℕ) : ℤ) = ∑ a ∈ t, if a ∈ s then (f a : ℤ) else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (by rwa [Set.support_indicator]),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- `natCast_finsum_mem_eq_sum` for a sum over the values satisfying a predicate. -/
private theorem natCast_finsum_eq_sum {α : Type*} {f : α → ℕ} {P : α → Prop} (t : Finset α)
    (h : ∀ a, P a → f a ≠ 0 → a ∈ t) [DecidablePred P] :
    ((∑ᶠ (a) (_ : P a), f a : ℕ) : ℤ) = ∑ a ∈ t, if P a then (f a : ℤ) else 0 :=
  natCast_finsum_mem_eq_sum (s := {a | P a}) t fun a ⟨ha, hne⟩ => h a ha hne

/-- A sum over the values satisfying `P` is a sum along an injection `g` whose image is the set
of values satisfying `P`. -/
private theorem finsum_eq_finsum_comp_of_injective {α β M : Type*} [AddCommMonoid M]
    {f : β → M} {P : β → Prop} {R : α → Prop} {g : α → β} (hg : Function.Injective g)
    (h : ∀ b, P b ↔ ∃ a, R a ∧ g a = b) :
    ∑ᶠ (b) (_ : P b), f b = ∑ᶠ (a) (_ : R a), f (g a) := by
  have hs : {b | P b} = g '' {a | R a} := Set.ext fun b => h b
  have := finsum_mem_image (f := f) (s := {a | R a}) hg.injOn
  rw [← hs] at this
  exact this

/-! ### The difference of difficulties -/

/-- The log discrepancy of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_unique {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a b : ℝ}
    (ha : IsValuationLogDiscrepancy sX B v a) (hb : IsValuationLogDiscrepancy sX B v b) :
    a = b := by
  obtain ⟨n, D, -, hv, ha⟩ := ha
  obtain ⟨n', D', -, hv', hb⟩ := hb
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb (hv.trans hv'.symm)

/-- **The difficulty change under a coefficient decrease**, for a decreased pair `V` identified
with `Y_i` by an isomorphism `φ : V ≅ Y_i` over `ℂ` that carries the boundary of `V` to `Θ_i'` and
the label centres of `V` to those of `Y_i`. -/
private theorem main {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (y : Q.ModelIndex) (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hs : φ.hom ≫ Q.chain.modelStructure ⟨i, none⟩ = Q.chain.modelStructure y.1)
    (hB : ∀ Γ, (Q.chain.modelBoundary y.1).coeff Γ =
      (Q.chain.bridge i).Θ'.coeff (primeDivisorEquivOfIso φ Γ))
    (hpair : MMP.Mori.IsPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ')
    (hc : ∀ S P, Q.chain.IsLabelCentre S y.1 P →
      Q.chain.IsLabelCentre S ⟨i, none⟩ (primeDivisorEquivOfIso φ P)) :
    ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))),
      F.Finite ∧
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v ∉ F, ∀ v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap φ.hom) = v →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale y.1 v' w' → w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D → Q.IsDifficulty y D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, ∀ v' : Valuation (Q.chain.model y.1).functionField
              (WithZero (Multiplicative ℤ)),
            v'.comap (functionFieldMap φ.hom) = v →
              Q.chain.IsValuationWeight Q.scale y.1 v' (w' v)) →
          D - D' = ∑ᶠ (v) (_ : v ∈ F), ((w v : ℤ) - w' v) := by
  classical
  -- transport of valuations
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Valuation (Q.chain.model y.1).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
      ∀ v', Φ v' = v'.comap (functionFieldMap φ.hom) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
      ∀ v, Ψ v = v.comap (functionFieldMap φ.inv) := ⟨_, fun _ => rfl⟩
  have hΨΦ : ∀ v', Ψ (Φ v') = v' := fun v' => by rw [hΨ, hΦ]; exact comap_inv_comap_hom φ v'
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by rw [hΦ, hΨ]; exact comap_inv_comap_hom φ.symm v
  have hΨinj : Function.Injective Ψ := fun a b h => by rw [← hΦΨ a, h, hΦΨ]
  have hs' : φ.inv ≫ Q.chain.modelStructure y.1 = Q.chain.modelStructure ⟨i, none⟩ :=
    inv_comp_eq_of_hom_comp_eq φ hs
  -- the two models
  obtain ⟨hΘx, hprojx, -, hdimx, -, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  obtain ⟨hΘy, hprojy, -, -, -, -⟩ := Q.echoSetting_model y
  haveI : CompactSpace (Q.chain.model y.1) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (Q.chain.modelStructure y.1) := hprojy
    exact QuasiCompact.compactSpace_of_compactSpace (Q.chain.modelStructure y.1)
  have hnvW : IsNormalVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hΘx.1.1.isPair.1
  have hvarW : MMP.Mori.IsVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hnvW.1
  haveI : IsProper (Q.chain.modelStructure ⟨i, none⟩) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hprojx
    infer_instance
  haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) :=
    hnvW.1.toLocallyOfFiniteType
  -- weights
  have hux : ∀ {v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))} {w₁ w₂ : ℕ},
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w₁ →
        Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w₂ → w₁ = w₂ := by
    rintro v w₁ w₂ ⟨-, a, ha, rfl⟩ ⟨-, b, hb, rfl⟩
    rw [isValuationLogDiscrepancy_unique ha hb]
  have huy : ∀ {v : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ))}
      {w₁ w₂ : ℕ}, Q.chain.IsValuationWeight Q.scale y.1 v w₁ →
        Q.chain.IsValuationWeight Q.scale y.1 v w₂ → w₁ = w₂ := by
    rintro v w₁ w₂ ⟨-, a, ha, rfl⟩ ⟨-, b, hb, rfl⟩
    rw [isValuationLogDiscrepancy_unique ha hb]
  have hwt : ∀ v' w', Q.chain.IsValuationWeight Q.scale y.1 v' w' →
      MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
          (Q.chain.bridge i).Θ' (Φ v') a ∧ w' = difficultyWeight Q.scale (2 - a) := by
    rintro v' w' ⟨hex, a, ha, rfl⟩
    rw [hΦ]
    exact ⟨isExceptionalValuation_comap φ hs hex, a,
      isValuationLogDiscrepancy_comap φ hs hB hpair ha, rfl⟩
  -- centres
  have hptV : ∀ {v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model y.1)} {p : Q.chain.model y.1},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v' Z →
        (Z : Set (Q.chain.model y.1)) = {p} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') Z' ∧
            (Z' : Set (Q.chain.model ⟨i, none⟩)) = {φ.hom p} := by
    intro v' Z p h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ hs h
    exact ⟨Z', hΦ v' ▸ h', by rw [hZ', hZ, Set.image_singleton]⟩
  have hptW : ∀ {v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)} {p : Q.chain.model ⟨i, none⟩},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z →
        (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z' ∧
            (Z' : Set (Q.chain.model y.1)) = {φ.inv p} := by
    intro v Z p h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ.symm hs' h
    exact ⟨Z', hΨ v ▸ h', by rw [hZ', hZ, Set.image_singleton]; rfl⟩
  have hcenV : ∀ {v' : Valuation (Q.chain.model y.1).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model y.1)} {γ' : ProperCurve (Q.chain.modelStructure y.1)},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v' Z →
        (Z : Set (Q.chain.model y.1)) = closure {γ'.point} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) (Φ v') Z' ∧
            (Z' : Set (Q.chain.model ⟨i, none⟩)) =
              closure {(properCurveEquiv φ hs γ').point} := by
    intro v' Z γ' h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ hs h
    exact ⟨Z', hΦ v' ▸ h', by
      rw [hZ', hZ, properCurveEquiv_apply, closure_properCurveMap_point]⟩
  have hcenW : ∀ {v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))}
      {Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)}
      {γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩)},
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z →
        (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point} →
        ∃ Z' : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z' ∧
            (Z' : Set (Q.chain.model y.1)) =
              closure {((properCurveEquiv φ hs).symm γ).point} := by
    intro v Z γ h hZ
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap φ.symm hs' h
    exact ⟨Z', hΨ v ▸ h', by
      rw [hZ', hZ]
      exact (closure_properCurveMap_point φ.symm hs' γ).symm⟩
  -- the curves along which weights are unchanged
  obtain ⟨𝓔, h𝓔, hE⟩ := Q.exists_finite_isValuationWeight_eq hi
  -- point and curve centres
  obtain ⟨pt, hpt⟩ : ∃ pt : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)) → Prop, ∀ v, pt v ↔
        ∃ (Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)) (p : Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨cen, hcen⟩ : ∃ cen : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) →
      Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → Prop,
      ∀ γ v, cen γ v ↔ ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point} := ⟨_, fun _ _ => Iff.rfl⟩
  -- the finite set `F`
  obtain ⟨F, hF⟩ : ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))), ∀ v, v ∈ F ↔
        MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
          (pt v ∨ ∃ γ ∈ 𝓔, cen γ v) ∧
          ((∃ w, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w ∧ w ≠ 0) ∨
            ∃ w', Q.chain.IsValuationWeight Q.scale y.1 (Ψ v) w' ∧ w' ≠ 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hFfin : F.Finite := by
    have hA := Q.finite_setOf_isCentre_singleton ⟨⟨i, none⟩, hi⟩
    have hA' := Q.finite_setOf_isCentre_singleton y
    refine (((hA.union (h𝓔.biUnion fun γ _ =>
      Q.finite_setOf_isCentre_closure ⟨⟨i, none⟩, hi⟩ γ)).union
        ((hA'.image Φ).union (h𝓔.biUnion fun γ _ =>
          (Q.finite_setOf_isCentre_closure y ((properCurveEquiv φ hs).symm γ)).image Φ)))).subset ?_
    intro v hv
    obtain ⟨-, hc, ⟨w, hw, hw0⟩ | ⟨w', hw', hw0⟩⟩ := (hF v).1 hv
    · rcases hc with hp | ⟨γ, hγ, hc⟩
      · exact Or.inl (Or.inl ⟨(hpt v).1 hp, w, hw, hw0⟩)
      · exact Or.inl (Or.inr (Set.mem_biUnion hγ ⟨(hcen γ v).1 hc, w, hw, hw0⟩))
    · rcases hc with hp | ⟨γ, hγ, hc⟩
      · obtain ⟨Z, p, hZ, hp⟩ := (hpt v).1 hp
        obtain ⟨Z', h', hZ'⟩ := hptW hZ hp
        exact Or.inr (Or.inl ⟨Ψ v, ⟨⟨Z', _, h', hZ'⟩, w', hw', hw0⟩, hΦΨ v⟩)
      · obtain ⟨Z, hZ, hZγ⟩ := (hcen γ v).1 hc
        obtain ⟨Z', h', hZ'⟩ := hcenW hZ hZγ
        exact Or.inr (Or.inr (Set.mem_biUnion hγ ⟨Ψ v, ⟨⟨Z', h', hZ'⟩, w', hw', hw0⟩, hΦΨ v⟩))
  refine ⟨F, hFfin, fun v hv => ((hF v).1 hv).1, ?_, ?_⟩
  · intro v hvF v' hv' w w' hw hw'
    rw [← hΦ] at hv'
    subst hv'
    obtain ⟨Z, hZ, ⟨p, hp⟩ | ⟨γ, hγ⟩⟩ := exists_isCentre_of_isExceptionalValuation hdimx hw.1
    · by_contra hne
      apply hvF
      refine (hF _).2 ⟨hw.1, Or.inl ((hpt _).2 ⟨Z, p, hZ, hp⟩), ?_⟩
      by_cases hw0 : w = 0
      · exact Or.inr ⟨w', by rw [hΨΦ]; exact hw', by omega⟩
      · exact Or.inl ⟨w, hw, hw0⟩
    · by_cases hγ𝓔 : γ ∈ 𝓔
      · by_contra hne
        apply hvF
        refine (hF _).2 ⟨hw.1, Or.inr ⟨γ, hγ𝓔, (hcen _ _).2 ⟨Z, hZ, hγ⟩⟩, ?_⟩
        by_cases hw0 : w = 0
        · exact Or.inr ⟨w', by rw [hΨΦ]; exact hw', by omega⟩
        · exact Or.inl ⟨w, hw, hw0⟩
      · exact (hE γ hγ𝓔 (Φ v') ⟨Z, hZ, hγ⟩ w w' hw (hwt v' w' hw')).symm
  · intro D D' hD hD' w w' hw hw'
    have hw'' : ∀ v ∈ F, Q.chain.IsValuationWeight Q.scale y.1 (Ψ v) (w' v) :=
      fun v hv => hw' v hv (Ψ v) ((hΦ _).symm.trans (hΦΨ v))
    obtain ⟨wD, β, d, ρ, hwD, hβ, hd, hρ, rfl⟩ := hD
    obtain ⟨wD', β', d', ρ', hwD', hβ', hd', hρ', rfl⟩ := hD'
    set 𝔉 := hFfin.toFinset with h𝔉
    have hmem𝔉 : ∀ {v}, v ∈ 𝔉 ↔ v ∈ F := fun {v} => hFfin.mem_toFinset
    set Ψc := properCurveEquiv φ hs with hΨc
    -- centres of labels and defaults
    have hcenx : ∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩)},
        Q.chain.IsLabelCentre S ⟨i, none⟩ P → Q.chain.IsLabelCentre S ⟨i, none⟩ P' → P = P' :=
      fun S P P' h h' => eq_of_isLabelCentre_none Q.chain hnvW h h'
    have hceny : ∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model y.1)},
        Q.chain.IsLabelCentre S y.1 P → Q.chain.IsLabelCentre S y.1 P' → P = P' :=
      fun S P P' h h' => (primeDivisorEquivOfIso φ).injective (hcenx S (hc S P h) (hc S P' h'))
    have hdefu : ∀ (z : Q.chain.ModelIndex), (∀ S {P P' : MMP.Mori.PrimeDivisor (Q.chain.model z)},
        Q.chain.IsLabelCentre S z P → Q.chain.IsLabelCentre S z P' → P = P') →
        ∀ S {a b : ℕ}, Q.chain.IsLabelDefault Q.scale S z a →
          Q.chain.IsLabelDefault Q.scale S z b → a = b := by
      rintro z hz S a b ⟨c₁, ⟨P, hP, rfl⟩, rfl⟩ ⟨c₂, ⟨P', hP', rfl⟩, rfl⟩
      rw [hz S hP hP']
    choose d₀ hd₀ using Q.isLabelDefault_const
    have hdx : ∀ S {a : ℕ}, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ a → a = d₀ S :=
      fun S a h => hdefu _ hcenx S h (hd₀ S ⟨i, none⟩ hi)
    have hdy : ∀ S {a : ℕ}, Q.chain.IsLabelDefault Q.scale S y.1 a → a = d₀ S :=
      fun S a h => hdefu _ hceny S h (hd₀ S y.1 y.2)
    -- the label terms
    have hlab : ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) = ((∑ᶠ S, d' S * ρ' S : ℕ) : ℤ) := by
      congr 1
      refine finsum_congr fun S => ?_
      rw [hdx S (hd S), hdy S (hd' S)]
      congr 1
      obtain ⟨P, hP, hρP⟩ := hρ S
      obtain ⟨P', hP', hρP'⟩ := hρ' S
      obtain rfl := hcenx S (hc S P' hP') hP
      dsimp only at hρP hρP'
      rw [hρP, hρP']
      obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme φ P'
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure y.1) P'
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩)
        (primeDivisorEquivOfIso φ P')
      haveI := Q.chain.isComplexScheme_primeDivisorNormalizationScheme_model y.1 P'
      haveI := Q.chain.isComplexScheme_primeDivisorNormalizationScheme_model ⟨i, none⟩
        (primeDivisorEquivOfIso φ P')
      exact (boxedSurfaceRank_eq_of_iso E (by
        change E.hom ≫ (primeDivisorNormalization _ ≫ _) = primeDivisorNormalization P' ≫ _
        rw [← Category.assoc, hE, Category.assoc, hs])).symm
    -- the point sums
    have hpts : ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            ∃ p : Q.chain.model ⟨i, none⟩, IsClosed ({p} : Set (Q.chain.model ⟨i, none⟩)) ∧
              (Z : Set (Q.chain.model ⟨i, none⟩)) = {p}), wD v : ℕ) : ℤ) -
        ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model y.1),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) v Z ∧
            ∃ p : Q.chain.model y.1, IsClosed ({p} : Set (Q.chain.model y.1)) ∧
              (Z : Set (Q.chain.model y.1)) = {p}), wD' v : ℕ) : ℤ) =
        ∑ v ∈ 𝔉, if pt v then ((w v : ℤ) - w' v) else 0 := by
      rw [natCast_finsum_eq_sum 𝔉 ?_, natCast_finsum_eq_sum (𝔉.image Ψ) ?_,
        Finset.sum_image (fun a _ b _ h => hΨinj h), ← Finset.sum_sub_distrib]
      · refine Finset.sum_congr rfl fun v hv => ?_
        have hvF := hmem𝔉.1 hv
        by_cases hp : pt v
        · obtain ⟨Z, p, hZ, hZp⟩ := (hpt v).1 hp
          obtain ⟨Z', hZ', hZ'p⟩ := hptW hZ hZp
          have h1 : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                ∃ p : Q.chain.model ⟨i, none⟩, IsClosed ({p} : Set (Q.chain.model ⟨i, none⟩)) ∧
                  (Z : Set (Q.chain.model ⟨i, none⟩)) = {p} :=
            ⟨Z, hZ, p, hZp ▸ Z.isClosed, hZp⟩
          have h2 : ∃ Z : IrreducibleCloseds (Q.chain.model y.1),
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure y.1) (Ψ v) Z ∧
                ∃ p : Q.chain.model y.1, IsClosed ({p} : Set (Q.chain.model y.1)) ∧
                  (Z : Set (Q.chain.model y.1)) = {p} :=
            ⟨Z', hZ', _, hZ'p ▸ Z'.isClosed, hZ'p⟩
          rw [if_pos h1, if_pos h2, if_pos hp, hux (hwD v h1) (hw v hvF),
            huy (hwD' (Ψ v) h2) (hw'' v hvF)]
        · rw [if_neg, if_neg, if_neg hp, sub_zero]
          · rintro ⟨Z', hZ', p', -, hZ'p⟩
            obtain ⟨Z, hZ, hZp⟩ := hptV hZ' hZ'p
            exact hp ((hpt v).2 ⟨Z, _, hΦΨ v ▸ hZ, hZp⟩)
          · rintro ⟨Z, hZ, p, -, hZp⟩
            exact hp ((hpt v).2 ⟨Z, p, hZ, hZp⟩)
      · rintro v' hv' hne
        obtain ⟨Z', hZ', p', -, hZ'p⟩ := id hv'
        obtain ⟨Z, hZ, hZp⟩ := hptV hZ' hZ'p
        exact Finset.mem_image.2 ⟨Φ v', hmem𝔉.2 ((hF _).2 ⟨(hwt v' _ (hwD' v' hv')).1,
          Or.inl ((hpt _).2 ⟨Z, _, hZ, hZp⟩),
          Or.inr ⟨wD' v', by rw [hΨΦ]; exact hwD' v' hv', hne⟩⟩), hΨΦ v'⟩
      · rintro v hv hne
        obtain ⟨Z, hZ, p, -, hZp⟩ := id hv
        exact hmem𝔉.2 ((hF v).2 ⟨(hwD v hv).1, Or.inl ((hpt v).2 ⟨Z, p, hZ, hZp⟩),
          Or.inl ⟨wD v, hwD v hv, hne⟩⟩)
    -- the brackets
    have hbr : ∑ᶠ γ, β γ - ∑ᶠ γ', β' γ' =
        ∑ γ ∈ h𝓔.toFinset, ∑ v ∈ 𝔉, if cen γ v then ((w v : ℤ) - w' v) else 0 := by
      have hkey : ∀ γ, β γ - β' (Ψc.symm γ) =
          if γ ∈ 𝓔 then ∑ v ∈ 𝔉, (if cen γ v then ((w v : ℤ) - w' v) else 0) else 0 := by
        intro γ
        obtain ⟨wβ, r, dβ, hwβ, hr, hdβ, hβeq⟩ := hβ γ
        obtain ⟨wβ', r', dβ', hwβ', hr', hdβ', hβeq'⟩ := hβ' (Ψc.symm γ)
        have hclos : closure {γ.point} = φ.hom.base '' closure {(Ψc.symm γ).point} := by
          change _ = φ.hom.base '' closure {(properCurveMap φ.symm hs' γ).point}
          rw [closure_properCurveMap_point, Set.image_image]
          change _ = (fun x => φ.hom (φ.inv x)) '' _
          simp_rw [inv_hom_apply, Set.image_id']
        have hrd : (∑ᶠ S, r S * dβ S : ℕ) = ∑ᶠ S, r' S * dβ' S := by
          refine finsum_congr fun S => ?_
          rw [hdx S (hdβ S), hdy S (hdβ' S)]
          congr 1
          obtain ⟨P, hP, hrP⟩ := hr S
          obtain ⟨P', hP', hrP'⟩ := hr' S
          obtain rfl := hcenx S (hc S P' hP') hP
          rw [hrP, hrP', hclos, branchNumber_primeDivisorEquivOfIso]
        rw [hβeq, hβeq', hrd, sub_sub_sub_cancel_right]
        split_ifs with hγ
        · rw [natCast_finsum_eq_sum 𝔉 ?_, natCast_finsum_eq_sum (𝔉.image Ψ) ?_,
            Finset.sum_image (fun a _ b _ h => hΨinj h), ← Finset.sum_sub_distrib]
          · refine Finset.sum_congr rfl fun v hv => ?_
            have hvF := hmem𝔉.1 hv
            by_cases hcv : cen γ v
            · obtain ⟨Z, hZ, hZγ⟩ := (hcen γ v).1 hcv
              obtain ⟨Z', hZ', hZ'γ⟩ := hcenW hZ hZγ
              rw [if_pos ⟨Z, hZ, hZγ⟩, if_pos ⟨Z', hZ', hZ'γ⟩, if_pos hcv,
                hux (hwβ v ⟨Z, hZ, hZγ⟩) (hw v hvF), huy (hwβ' (Ψ v) ⟨Z', hZ', hZ'γ⟩) (hw'' v hvF)]
            · rw [if_neg (fun h => hcv ((hcen γ v).2 h)), if_neg, if_neg hcv, sub_zero]
              rintro ⟨Z', hZ', hZ'γ⟩
              obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
              rw [hΦΨ] at hZ
              rw [Equiv.apply_symm_apply] at hZγ
              exact hcv ((hcen γ v).2 ⟨Z, hZ, hZγ⟩)
          · rintro v' hv' hne
            obtain ⟨Z', hZ', hZ'γ⟩ := id hv'
            obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
            rw [Equiv.apply_symm_apply] at hZγ
            exact Finset.mem_image.2 ⟨Φ v', hmem𝔉.2 ((hF _).2 ⟨(hwt v' _ (hwβ' v' hv')).1,
              Or.inr ⟨γ, hγ, (hcen _ _).2 ⟨Z, hZ, hZγ⟩⟩,
              Or.inr ⟨wβ' v', by rw [hΨΦ]; exact hwβ' v' hv', hne⟩⟩), hΨΦ v'⟩
          · rintro v hv hne
            exact hmem𝔉.2 ((hF v).2 ⟨(hwβ v hv).1, Or.inr ⟨γ, hγ, (hcen γ v).2 hv⟩,
              Or.inl ⟨wβ v, hwβ v hv, hne⟩⟩)
        · rw [finsum_eq_finsum_comp_of_injective (f := wβ') (R := fun v =>
              ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
                MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
                  (Z : Set (Q.chain.model ⟨i, none⟩)) = closure {γ.point}) hΨinj ?_, sub_eq_zero]
          · congr 1
            refine finsum_congr fun v => finsum_congr fun hv => ?_
            obtain ⟨Z, hZ, hZγ⟩ := hv
            obtain ⟨Z', hZ', hZ'γ⟩ := hcenW hZ hZγ
            have h1 := hwt (Ψ v) _ (hwβ' (Ψ v) ⟨Z', hZ', hZ'γ⟩)
            rw [hΦΨ] at h1
            exact (hE γ hγ v ⟨Z, hZ, hZγ⟩ _ _ (hwβ v ⟨Z, hZ, hZγ⟩) h1).symm
          · intro v'
            constructor
            · rintro ⟨Z', hZ', hZ'γ⟩
              obtain ⟨Z, hZ, hZγ⟩ := hcenV hZ' hZ'γ
              rw [Equiv.apply_symm_apply] at hZγ
              exact ⟨Φ v', ⟨Z, hZ, hZγ⟩, hΨΦ v'⟩
            · rintro ⟨v, ⟨Z, hZ, hZγ⟩, rfl⟩
              exact hcenW hZ hZγ
      have hfin1 : (Function.support β).Finite :=
        (Q.finite_setOf_isCurveBracket_ne_zero ⟨⟨i, none⟩, hi⟩).subset
          fun γ hγ => ⟨β γ, hβ γ, hγ⟩
      have hfin2 : (Function.support fun γ => β' (Ψc.symm γ)).Finite :=
        ((Q.finite_setOf_isCurveBracket_ne_zero y).image Ψc).subset
          fun γ hγ => ⟨Ψc.symm γ, ⟨β' _, hβ' _, hγ⟩, Ψc.apply_symm_apply γ⟩
      rw [← finsum_comp_equiv Ψc.symm, ← finsum_sub_distrib hfin1 hfin2,
        finsum_eq_sum_of_support_subset _ (s := h𝓔.toFinset) ?_]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        rw [hkey γ, if_pos (h𝓔.mem_toFinset.1 hγ)]
      · intro γ hγ
        rw [h𝓔.coe_toFinset]
        by_contra hγ𝓔
        exact hγ ((hkey γ).trans (if_neg hγ𝓔))
    -- every valuation of `F` has exactly one centre among the points and the curves of `𝓔`
    have hdec : ∀ v ∈ 𝔉, ((w v : ℤ) - w' v) = (if pt v then ((w v : ℤ) - w' v) else 0) +
        ∑ γ ∈ h𝓔.toFinset, if cen γ v then ((w v : ℤ) - w' v) else 0 := by
      intro v hv
      obtain ⟨-, hc, -⟩ := (hF v).1 (hmem𝔉.1 hv)
      rcases hc with hp | ⟨γ₀, hγ₀, hc₀⟩
      · rw [if_pos hp, Finset.sum_eq_zero, add_zero]
        intro γ _
        rw [if_neg]
        intro hcγ
        obtain ⟨Z, p, hZ, hZp⟩ := (hpt v).1 hp
        obtain ⟨Z', hZ', hZ'γ⟩ := (hcen γ v).1 hcγ
        exact not_isCentre_singleton_and_closure hvarW γ hZ hZp hZ' hZ'γ
      · have hnp : ¬ pt v := fun hp => by
          obtain ⟨Z, p, hZ, hZp⟩ := (hpt v).1 hp
          obtain ⟨Z', hZ', hZ'γ⟩ := (hcen γ₀ v).1 hc₀
          exact not_isCentre_singleton_and_closure hvarW γ₀ hZ hZp hZ' hZ'γ
        rw [if_neg hnp, zero_add, Finset.sum_eq_single γ₀, if_pos hc₀]
        · intro γ _ hne
          rw [if_neg]
          intro hcγ
          obtain ⟨Z, hZ, hZγ⟩ := (hcen γ v).1 hcγ
          obtain ⟨Z', hZ', hZ'γ⟩ := (hcen γ₀ v).1 hc₀
          exact hne (eq_of_isCentre_closure hvarW hZ hZγ hZ' hZ'γ)
        · intro h
          exact absurd (h𝓔.mem_toFinset.2 hγ₀) h
    rw [finsum_mem_eq_finite_toFinset_sum _ hFfin, ← h𝔉, Finset.sum_congr rfl hdec,
      Finset.sum_add_distrib, Finset.sum_comm (s := 𝔉)]
    linear_combination hpts + hbr + hlab

/-- Along a bridge with no step, the decreased pair `(Y_i, Θ_i')` is identified with the next
junction `(Y_{i+1}, Θ_{i+1})` by the identification `φ⁻¹` of the end of the bridge. -/
private theorem decreased_of_m_eq_zero {T : StabilizedTail} (C : StabilizedTail.TerminalChain T)
    (i : ℕ) (h : (C.bridge i).P.m = 0) (φ : (C.junction (i + 1)).Y ≅ (C.junction i).Y)
    (hφ : φ.hom = (C.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) h)) :
    (C.bridge i).Θ' = inverseTransformDivisor φ.inv (C.junction (i + 1)).Θ ∧
      (C.junction i).p ≫ T.f i = φ.inv ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (hm : m = 0)
      (e : modelSeq (C.junction i).Y (C.bridge i).P.Y m ≅ (C.junction (i + 1)).Y)
      (φ : (C.junction (i + 1)).Y ≅ (C.junction i).Y),
      φ.hom = e.inv ≫ eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) →
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY m =
        e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i →
      (C.bridge i).Θ' = inverseTransformDivisor φ.inv (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = φ.inv ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m rfl e φ hφ hb hπ
    let e' : (C.junction i).Y ≅ (C.junction (i + 1)).Y := e
    have hφ' : φ.hom = e'.inv := by
      rw [eqToHom_refl, Category.comp_id] at hφ
      exact hφ
    obtain rfl : φ = e'.symm := Iso.ext hφ'
    exact ⟨hb, hπ⟩
  exact key _ h (C.bridge i).e φ hφ (C.bridge i).boundary_eq (C.bridge i).modelMap_eq

/-- The transport data of a coefficient-decrease move along a bridge with no step. -/
private theorem transport_of_m_eq_zero {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) (h : (Q.chain.bridge i).P.m = 0)
    (φ : (Q.chain.junction (i + 1)).Y ≅ (Q.chain.junction i).Y)
    (hφ : φ.hom = (Q.chain.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)) :
    φ.hom ≫ ((Q.chain.junction i).p ≫ T.sX i) = (Q.chain.junction (i + 1)).p ≫ T.sX (i + 1) ∧
      (∀ Γ : MMP.Mori.PrimeDivisor (Q.chain.junction (i + 1)).Y,
        (Q.chain.junction (i + 1)).Θ.coeff Γ =
          (Q.chain.bridge i).Θ'.coeff (primeDivisorEquivOfIso φ Γ)) ∧
      ∀ S (P : MMP.Mori.PrimeDivisor (Q.chain.junction (i + 1)).Y),
        Q.chain.IsLabelCentre S ⟨i + 1, none⟩ P →
          Q.chain.IsLabelCentre S ⟨i, none⟩ (primeDivisorEquivOfIso φ P) := by
  obtain ⟨hΘ, hπ⟩ := decreased_of_m_eq_zero Q.chain i h φ hφ
  obtain ⟨-, -, -, -, ⟨c, -, hcc, -, -⟩, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  obtain ⟨hΘ1, -, -, -, -, -⟩ := Q.echoSetting_model ⟨⟨i + 1, none⟩, Nat.le_succ_of_le hi⟩
  have hnv1 : IsNormalVariety ℂ ((Q.chain.junction (i + 1)).p ≫ T.sX (i + 1)) :=
    hΘ1.1.1.isPair.1
  refine ⟨?_, fun Γ => ?_, fun S P hP => ?_⟩
  · have h1 := congrArg (· ≫ T.sZ i) hπ
    simp only [Category.assoc] at h1
    rw [(T.isThreefoldStepDiagram i).comp_eq_minus,
      (T.isThreefoldStepDiagram i).comp_eq_plus] at h1
    rw [h1, Iso.hom_inv_id_assoc]
  · have h1 := congrArg (fun D => D.coeff (primeDivisorEquivOfIso φ Γ)) hΘ
    refine (h1.trans ?_).symm
    exact (coeff_inverseTransformDivisor_iso φ.symm _ _).trans
      (congrArg _ (primeDivisorEquivOfIso_symm_apply φ Γ))
  · have h1 := isLabelCentre_succ_of_iso Q.chain φ.symm hπ (hcc S)
    have h2 : P = primeDivisorEquivOfIso φ.symm (c S) :=
      eq_of_isLabelCentre_none Q.chain hnv1 hP h1
    have h3 : primeDivisorEquivOfIso φ (primeDivisorEquivOfIso φ.symm (c S)) = c S :=
      (primeDivisorEquivOfIso φ.symm).left_inv (c S)
    rw [h2, h3]
    exact hcc S

/-- **The difficulty change under a coefficient decrease.** Let `i ≥ i₀` index a junction
`(Y_i, Θ_i)` of a prepared chain, and let the model `y` with the identification `φ : Y_y ≅ Y_i`
be its decreased pair `(Y_i, Θ_i')`: the model `(i, some 0)` with `φ` the identity when
`0 < m_i`, and the next junction `(i + 1, none)` with `φ` induced by the inverse of the
identification `e : V_{m_i} ≅ Y_{i+1}` of the bridge when `m_i = 0`. There is a finite set `F`
of valuations of `ℂ(Y_i)` exceptional over `Y_i` such that every weight
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`) of a valuation `v ∉ F` for
`Θ_i` equals every weight of `v` for `Θ_i'`, and for difficulties `D = 𝒟(Y_i, Θ_i)` and
`D' = 𝒟(Y_i, Θ_i')` (`MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`) and weights
`w v = w_v(Y_i, Θ_i)`, `w' v = w_v(Y_i, Θ_i')` on `F`,
`D - D' = ∑_{v ∈ F} (w v - w' v)`. -/
private theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.exists_finite_isDifficulty_sub_eq_finsum
    {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) {i : ℕ} (hi : Q.start ≤ i) (y : Q.ModelIndex)
    (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hφ : (∃ (h : 0 < (Q.chain.bridge i).P.m) (hy : y.1 = ⟨i, some ⟨0, h⟩⟩),
        φ.hom = eqToHom ((congrArg Q.chain.model hy).trans
          (rfl : Q.chain.model ⟨i, some ⟨0, h⟩⟩ = Q.chain.model ⟨i, none⟩))) ∨
      (∃ (h : (Q.chain.bridge i).P.m = 0) (hy : y.1 = ⟨i + 1, none⟩),
        φ.hom = eqToHom (congrArg Q.chain.model hy) ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h))) :
    ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))),
      F.Finite ∧
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v ∉ F, ∀ v' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ)),
        v'.comap (functionFieldMap φ.hom) = v →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale y.1 v' w' → w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D → Q.IsDifficulty y D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, ∀ v' : Valuation (Q.chain.model y.1).functionField
              (WithZero (Multiplicative ℤ)),
            v'.comap (functionFieldMap φ.hom) = v →
              Q.chain.IsValuationWeight Q.scale y.1 v' (w' v)) →
          D - D' = ∑ᶠ (v) (_ : v ∈ F), ((w v : ℤ) - w' v) := by
  obtain ⟨hΘx, -, -, -, ⟨c, -, hcc, -, -⟩, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  have hnvW : IsNormalVariety ℂ ((Q.chain.junction i).p ≫ T.sX i) := hΘx.1.1.isPair.1
  have hpair : MMP.Mori.IsPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' :=
    (Q.chain.bridge i).P.isKltPair.1.isPair
  rcases hφ with ⟨h, hy, hφeq⟩ | ⟨h, hy, hφeq⟩
  · obtain ⟨p, hφ'⟩ : ∃ p : Q.chain.model y.1 = Q.chain.model ⟨i, none⟩, φ.hom = eqToHom p :=
      ⟨_, hφeq⟩
    clear hφeq
    obtain ⟨y, hy0⟩ := y
    change y = _ at hy
    subst hy
    have hφ1 : φ.hom = 𝟙 (Q.chain.junction i).Y := hφ'.trans (eqToHom_refl _ _)
    have hφid : ∀ x, φ.hom x = x := fun x => (congrArg (fun f => f.base x) hφ1).trans rfl
    have hequiv : ∀ Γ, primeDivisorEquivOfIso φ Γ = Γ := fun Γ =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_primeDivisorEquivOfIso φ Γ).trans (hφid _))
    refine main Q hi ⟨_, hy0⟩ φ ?_ (fun Γ => by rw [hequiv]; rfl) hpair fun S P hP => ?_
    · exact (congrArg (· ≫ Q.chain.modelStructure ⟨i, none⟩) hφ1).trans (Category.id_comp _)
    · rw [hequiv, eq_of_isLabelCentre_some_zero Q.chain h hnvW hP
        (isLabelCentre_some_zero Q.chain h (hcc S))]
      exact hcc S
  · obtain ⟨p, hφ'⟩ : ∃ p : Q.chain.model y.1 = Q.chain.model ⟨i + 1, none⟩,
        φ.hom = eqToHom p ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h) :=
      ⟨_, hφeq⟩
    clear hφeq
    obtain ⟨y, hy0⟩ := y
    change y = _ at hy
    subst hy
    rw [eqToHom_refl, Category.id_comp] at hφ'
    obtain ⟨hs, hB, hc⟩ := transport_of_m_eq_zero Q hi h φ hφ'
    exact main Q hi ⟨_, hy0⟩ φ hs hB hpair hc

end MMP.IndexdStrict.Card_coefficient_move_difference

end

/-! ### The strict decrease -/

namespace MMP.IndexdStrict

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Fourfold.StabilizedTail
  MMP.Fourfold.StabilizedTail.PreparedChain

/-- A finite sum of nonnegative integers with a positive term is positive. -/
private theorem lt_of_sub_eq_finsum_mem {α : Type*} {F : Set α} (hF : F.Finite) {f : α → ℤ}
    (h0 : ∀ u ∈ F, 0 ≤ f u) {v : α} (hv : v ∈ F) (hpos : 0 < f v) {D D' : ℤ}
    (hD : D - D' = ∑ᶠ u ∈ F, f u) : D' < D := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum f hF] at hD
  have : 0 < ∑ u ∈ hF.toFinset, f u :=
    Finset.sum_pos' (fun u hu => h0 u (hF.mem_toFinset.1 hu)) ⟨v, hF.mem_toFinset.2 hv, hpos⟩
  omega

/-- The weight of a valuation on a model of a terminal chain is unique. -/
private theorem isValuationWeight_unique {T : StabilizedTail} {C : T.TerminalChain} {N : ℕ}
    {x : C.ModelIndex} {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    {w₁ w₂ : ℕ} (h₁ : C.IsValuationWeight N x v w₁) (h₂ : C.IsValuationWeight N x v w₂) :
    w₁ = w₂ := by
  obtain ⟨-, a, ⟨n, D, -, hv, ha⟩, rfl⟩ := h₁
  obtain ⟨-, b, ⟨n', D', -, hv', hb⟩, rfl⟩ := h₂
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hb (hv.trans hv'.symm)]

/-- Every valuation exceptional over a model of a prepared chain has a weight there. -/
private theorem exists_isValuationWeight {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex)
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure x.1) v) :
    ∃ w, Q.chain.IsValuationWeight Q.scale x.1 v w := by
  obtain ⟨hΘ, -⟩ := Q.echoSetting_model x
  have hpair := hΘ.1.1.isPair
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨D, hDp, rfl, -⟩ := id hv
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK D
  exact ⟨_, hv, _, ⟨n, D, hDp, rfl,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩, rfl⟩

/-- **A coefficient decrease with a strict weight drop**, for the decreased pair `y` identified
with `Y_i` by `φ`. -/
private theorem lt_of_coefficient_move {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (y : Q.ModelIndex) (φ : Q.chain.model y.1 ≅ Q.chain.model ⟨i, none⟩)
    (hφ : (∃ (h : 0 < (Q.chain.bridge i).P.m) (hy : y.1 = ⟨i, some ⟨0, h⟩⟩),
        φ.hom = eqToHom ((congrArg Q.chain.model hy).trans
          (rfl : Q.chain.model ⟨i, some ⟨0, h⟩⟩ = Q.chain.model ⟨i, none⟩))) ∨
      (∃ (h : (Q.chain.bridge i).P.m = 0) (hy : y.1 = ⟨i + 1, none⟩),
        φ.hom = eqToHom (congrArg Q.chain.model hy) ≫ (Q.chain.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h)))
    (hs' : φ.inv ≫ Q.chain.modelStructure y.1 = Q.chain.modelStructure ⟨i, none⟩)
    (hmono : ∀ (u : Valuation (Q.chain.model ⟨i, none⟩).functionField
        (WithZero (Multiplicative ℤ))) (n n' : ℕ),
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ u n →
        Q.chain.IsValuationWeight Q.scale y.1 (u.comap (functionFieldMap φ.inv)) n' → n' ≤ n)
    {v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))}
    {w w' : ℕ} (hw : Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w)
    (hw' : Q.chain.IsValuationWeight Q.scale y.1 (v.comap (functionFieldMap φ.inv)) w')
    (hlt : w' < w) {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty y D') : D' < D := by
  classical
  obtain ⟨F, hF, hFex, hFout, hdiff⟩ :=
    PreparedChain.exists_finite_isDifficulty_sub_eq_finsum Q hi y φ hφ
  have hcomap : ∀ u : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)),
      (u.comap (functionFieldMap φ.inv)).comap (functionFieldMap φ.hom) = u := fun u =>
    MMP.IndexdStrict.Card_coefficient_move_difference.comap_inv_comap_hom φ.symm u
  have hinj : ∀ (u : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)))
      (u' : Valuation (Q.chain.model y.1).functionField (WithZero (Multiplicative ℤ))),
      u'.comap (functionFieldMap φ.hom) = u → u' = u.comap (functionFieldMap φ.inv) := by
    rintro u u' rfl
    exact (MMP.IndexdStrict.Card_coefficient_move_difference.comap_inv_comap_hom φ u').symm
  let wx : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) →
      ℕ := fun u => if h : ∃ n, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ u n then h.choose
        else 0
  let wy : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) →
      ℕ := fun u => if h : ∃ n, Q.chain.IsValuationWeight Q.scale y.1
        (u.comap (functionFieldMap φ.inv)) n then h.choose else 0
  have hwx : ∀ u ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ u (wx u) := fun u hu => by
    have h := exists_isValuationWeight Q ⟨⟨i, none⟩, hi⟩ (hFex u hu)
    simp only [wx, dif_pos h]
    exact h.choose_spec
  have hwy' : ∀ u ∈ F, Q.chain.IsValuationWeight Q.scale y.1
      (u.comap (functionFieldMap φ.inv)) (wy u) := fun u hu => by
    have h : ∃ n, Q.chain.IsValuationWeight Q.scale y.1 (u.comap (functionFieldMap φ.inv)) n :=
      exists_isValuationWeight Q y
        (MMP.IndexdStrict.Card_coefficient_move_difference.isExceptionalValuation_comap φ.symm hs'
          (hFex u hu))
    simp only [wy, dif_pos h]
    exact h.choose_spec
  have hwy : ∀ u ∈ F, ∀ u' : Valuation (Q.chain.model y.1).functionField
      (WithZero (Multiplicative ℤ)), u'.comap (functionFieldMap φ.hom) = u →
        Q.chain.IsValuationWeight Q.scale y.1 u' (wy u) := fun u hu u' hu' => by
    rw [hinj u u' hu']
    exact hwy' u hu
  have hvF : v ∈ F := by
    by_contra hvF
    have := hFout v hvF _ (hcomap v) w w' hw hw'
    omega
  refine lt_of_sub_eq_finsum_mem hF (f := fun u => (wx u : ℤ) - wy u) (fun u hu => ?_) hvF ?_
    (hdiff D D' hD hD' wx wy hwx hwy)
  · have := hmono u _ _ (hwx u hu) (hwy' u hu)
    omega
  · have h1 := isValuationWeight_unique (hwx v hvF) hw
    have h2 := isValuationWeight_unique (hwy' v hvF) hw'
    omega

/-- The extension of function fields along an isomorphism is surjective. -/
private theorem functionFieldMap_surjective_of_isIso {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] (f : A ⟶ B) [IsIso f] [IsDominant f] :
    Function.Surjective (functionFieldMap f) :=
  (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion f ⊤ ⟨genericPoint A, trivial⟩).2

/-- The extension of function fields along a composite of morphisms with surjective
extensions is surjective. -/
private theorem functionFieldMap_comp_surjective {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [hb : IsDominant b]
    [IsDominant (a ≫ b)] (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) :
    Function.Surjective (functionFieldMap (a ≫ b)) := by
  intro t
  obtain ⟨s, rfl⟩ := ha t
  obtain ⟨r, rfl⟩ := hb s
  exact ⟨r, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b r).symm⟩

/-- The morphism `V_{k+1} ⟶ T_k` of a flip of a bridge induces a surjection of function
fields. -/
private theorem functionFieldMap_flipTargetMapOf_surjective {T : StabilizedTail}
    (C : T.TerminalChain) (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) :
    haveI := C.isIntegral_flipBase i k
    haveI := C.isDominant_flipTargetMapOf i k d
    Function.Surjective (functionFieldMap (C.flipTargetMapOf i k d)) := by
  haveI := C.isIntegral_flipBase i k
  have hb := ((C.bridge i).P.isThreefoldStepDiagram k k.2).isSmallMorphism_plus.isBirationalMorphism
  haveI := hb.isDominant
  have hgp := hb.functionFieldMap_bijective.2
  cases d with
  | isTrue _ => exact hgp
  | isFalse h =>
    have hm : (C.bridge i).P.m = k.1 + 1 := by omega
    haveI hD : IsDominant ((C.bridge i).P.gp k) := hb.isDominant
    haveI : IsDominant (eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) ≫
        (C.bridge i).P.gp k) :=
      ⟨hD.denseRange.comp (inferInstance : IsDominant (eqToHom (congrArg
        (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm))).denseRange
        ((C.bridge i).P.gp k).continuous⟩
    exact functionFieldMap_comp_surjective (C.bridge i).e.inv
      (eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm) ≫ (C.bridge i).P.gp k)
      (functionFieldMap_surjective_of_isIso _)
      (functionFieldMap_comp_surjective
        (eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hm)) ((C.bridge i).P.gp k)
        (hb := hD) (functionFieldMap_surjective_of_isIso _) hgp)

/-- The morphism `Y⁺ ⟶ Z` of a flip move induces a surjection of function fields. -/
private theorem functionFieldMap_targetMap_surjective {T : StabilizedTail} {Q : PreparedChain T}
    (μ : Q.FlipMove) : Function.Surjective (functionFieldMap μ.targetMap) :=
  functionFieldMap_flipTargetMapOf_surjective Q.chain μ.1.1 μ.1.2 _

end MMP.IndexdStrict

namespace MMP.Fourfold.StabilizedTail.PreparedChain

variable {T : StabilizedTail}

open MMP.IndexdStrict in
/-- On a prepared chain, let `(Y, Θ) ⤏ (Y', Θ')` be a move from the model `x` to the model `x'`,
and suppose some normalized divisorial valuation `v` exceptional over `Y` and `Y'` has
`w_v(Y', Θ') < w_v(Y, Θ)`. Then `𝒟(Y', Θ') < 𝒟(Y, Θ)`. -/
@[mmp "prop_mmp_indexd_strict"]
public theorem difficulty_lt_of_valuationWeight_lt (Q : PreparedChain T) {x x' : Q.ModelIndex}
    (hmove :
      (∃ (i : ℕ) (hi : Q.start ≤ i) (h : 0 < (Q.chain.bridge i).P.m),
        x = ⟨⟨i, none⟩, hi⟩ ∧ x' = ⟨⟨i, some ⟨0, h⟩⟩, hi⟩ ∧
        ∃ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
          (w w' : ℕ), Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w ∧
            Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨0, h⟩⟩ v w' ∧ w' < w) ∨
      (∃ (i : ℕ) (hi : Q.start ≤ i) (h : (Q.chain.bridge i).P.m = 0),
        x = ⟨⟨i, none⟩, hi⟩ ∧ x' = ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ ∧
        ∃ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)))
          (v' : Valuation (Q.chain.model ⟨i + 1, none⟩).functionField
            (WithZero (Multiplicative ℤ))) (w w' : ℕ),
          v' = v.comap (functionFieldMap (eqToHom (congrArg
            (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h.symm) ≫
              (Q.chain.bridge i).e.hom)) ∧
          Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w ∧
            Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ v' w' ∧ w' < w) ∨
      (∃ μ : Q.FlipMove, x = μ.source ∧ x' = μ.target ∧
        ∃ (v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)))
          (v' : Valuation (Q.chain.model μ.target.1).functionField
            (WithZero (Multiplicative ℤ))) (w w' : ℕ),
          v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
          Q.chain.IsValuationWeight Q.scale μ.source.1 v w ∧
            Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' ∧ w' < w))
    {D D' : ℤ} (hD : Q.IsDifficulty x D) (hD' : Q.IsDifficulty x' D') : D' < D := by
  rcases hmove with ⟨i, hi, h, rfl, rfl, v, w, w', hw, hw', hlt⟩ |
    ⟨i, hi, h, rfl, rfl, v, v', w, w', rfl, hw, hw', hlt⟩ |
    ⟨μ, rfl, rfl, v, v', w, w', hvv', hw, hw', hlt⟩
  · -- a coefficient decrease inside a bridge with flips
    let φ : Q.chain.model ⟨i, some ⟨0, h⟩⟩ ≅ Q.chain.model ⟨i, none⟩ := Iso.refl _
    have hid : ∀ u : Valuation (Q.chain.model ⟨i, none⟩).functionField
        (WithZero (Multiplicative ℤ)), u.comap (functionFieldMap φ.inv) = u := fun u => by
      ext t
      exact congrArg u (MMP.Mori.functionFieldMap_id_apply t)
    refine lt_of_coefficient_move Q hi ⟨⟨i, some ⟨0, h⟩⟩, hi⟩ φ
      (Or.inl ⟨h, rfl, rfl⟩) (Category.id_comp _) (fun u n n' hn hn' => ?_) hw
      (by rwa [hid]) hlt hD hD'
    exact (le_of_isValuationWeight_of_move Q).1 i hi h u n n' hn (by rwa [hid] at hn')
  · -- the coefficient decrease of a bridge without flips
    let φ : Q.chain.model ⟨i + 1, none⟩ ≅ Q.chain.model ⟨i, none⟩ :=
      (eqToIso (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h.symm) ≪≫
        (Q.chain.bridge i).e).symm
    have hφ' : φ.hom = (Q.chain.bridge i).e.inv ≫
        eqToHom (congrArg (modelSeq (Q.chain.junction i).Y (Q.chain.bridge i).P.Y) h) :=
      rfl
    obtain ⟨hs, -, -⟩ :=
      MMP.IndexdStrict.Card_coefficient_move_difference.transport_of_m_eq_zero Q hi h φ hφ'
    refine lt_of_coefficient_move Q hi ⟨⟨i + 1, none⟩, hi.trans i.le_succ⟩ φ
      (Or.inr ⟨h, rfl, by rw [eqToHom_refl, Category.id_comp]; exact hφ'⟩)
      (MMP.IndexdStrict.Card_coefficient_move_difference.inv_comp_eq_of_hom_comp_eq φ hs)
      (fun u n n' hn hn' => ?_) hw hw' hlt hD hD'
    exact (le_of_isValuationWeight_of_move Q).2.1 i hi h u _ n n' rfl hn hn'
  · -- a small terminal flip
    classical
    have hsurj := functionFieldMap_targetMap_surjective μ
    have huniq : ∀ u₁ u₂ : Valuation (Q.chain.model μ.target.1).functionField
        (WithZero (Multiplicative ℤ)),
        u₁.comap (functionFieldMap μ.targetMap) = u₂.comap (functionFieldMap μ.targetMap) →
          u₁ = u₂ := by
      intro u₁ u₂ h12
      ext t
      obtain ⟨s, rfl⟩ := hsurj t
      exact congrArg (fun u : Valuation _ (WithZero (Multiplicative ℤ)) => u s) h12
    let wm : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)) →
        ℕ := fun u => if h : ∃ n, Q.chain.IsValuationWeight Q.scale μ.source.1 u n then h.choose
          else 0
    let wp : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ)) →
        ℕ := fun u => if h : ∃ n, ∃ u' : Valuation (Q.chain.model μ.target.1).functionField
            (WithZero (Multiplicative ℤ)),
          u'.comap (functionFieldMap μ.targetMap) = u.comap (functionFieldMap μ.sourceMap) ∧
            Q.chain.IsValuationWeight Q.scale μ.target.1 u' n then h.choose else 0
    have hwm : ∀ u ∈ Q.flipBadSet μ, Q.chain.IsValuationWeight Q.scale μ.source.1 u (wm u) := by
      rintro u ⟨-, u', -, n, n', hn, -, -⟩
      have h : ∃ n, Q.chain.IsValuationWeight Q.scale μ.source.1 u n := ⟨n, hn⟩
      simp only [wm, dif_pos h]
      exact h.choose_spec
    have hwp : ∀ u ∈ Q.flipBadSet μ, ∀ u'' : Valuation (Q.chain.model μ.target.1).functionField
        (WithZero (Multiplicative ℤ)),
        u''.comap (functionFieldMap μ.targetMap) = u.comap (functionFieldMap μ.sourceMap) →
          Q.chain.IsValuationWeight Q.scale μ.target.1 u'' (wp u) := by
      rintro u ⟨-, u', hu', n, n', -, hn', -⟩ u'' hu''
      have h : ∃ n, ∃ u' : Valuation (Q.chain.model μ.target.1).functionField
          (WithZero (Multiplicative ℤ)),
          u'.comap (functionFieldMap μ.targetMap) = u.comap (functionFieldMap μ.sourceMap) ∧
            Q.chain.IsValuationWeight Q.scale μ.target.1 u' n := ⟨n', u', hu', hn'⟩
      simp only [wp, dif_pos h]
      obtain ⟨u₀, hu₀, hw₀⟩ := h.choose_spec
      rwa [huniq u'' u₀ (hu''.trans hu₀.symm)]
    have hvB : v ∈ Q.flipBadSet μ := by
      by_contra hvB
      have := eq_of_isValuationWeight_of_notMem_flipBadSet Q μ hvB hvv' hw hw'
      omega
    refine lt_of_sub_eq_finsum_mem (finite_flipBadSet Q μ) (f := fun u => (wm u : ℤ) - wp u)
      (fun u hu => ?_) hvB ?_ (sub_eq_finsum_of_isDifficulty_of_flipMove Q μ hD hD' hwm hwp)
    · obtain ⟨-, u', hu', -⟩ := id hu
      have := (le_of_isValuationWeight_of_move Q).2.2 μ u u' _ _ hu' (hwm u hu) (hwp u hu u' hu')
      omega
    · have h1 := isValuationWeight_unique (hwm v hvB) hw
      have h2 := isValuationWeight_unique (hwp v hvB v' hvv') hw'
      omega

end MMP.Fourfold.StabilizedTail.PreparedChain
