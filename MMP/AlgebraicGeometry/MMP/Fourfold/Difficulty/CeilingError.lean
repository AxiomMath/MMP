module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FirstDefaultError
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MultiplicityBound
import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.MonomialValuationWeight
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# The local ceiling error at a curve on a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain at its admissible scale `N`, and let `C ⊆ Y` be an
irreducible closed curve. The bracket
`β_C = ∑_{c_Y(v) = C} w_v - ∑_h r_{C,h} d_h`
compares the weights `w_v` of the divisorial valuations centred at `C` with the defaults `d_h` of
the labels `S_h`, counted with their branch numbers `r_{C,h}` at `C`. It is bounded below by the
ceiling error of the varying labels:
`β_C ≥ -max{r_C^var - 1, 0}`, where `r_C^var = ∑_{h varying} r_{C,h}`.
No normal crossing condition on `Θ` at the generic point of `C` is required.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket.neg_max_le`: the inequality above.

## Implementation notes

* The curve is a proper curve `MMP.Mori.ProperCurve` of the model, recorded by its generic point.
  The bracket and the varying branch number are characterised by the predicates
  `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket` and
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingBranchNumber` on their values, so the
  statement takes values `β` and `r_C^var` pinned by those predicates.
* The inequality is stated in `ℤ`, with `max{r - 1, 0}` written `max ((r : ℤ) - 1) 0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.IndexdCeilingError

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Echoes

open MMP.Mori MMP.Fourfold MMP.Resolution

/-- For `c : ℕ∞`, the equation `1 + c = 3` in `WithBot ℕ∞` forces `c = 2`. -/
private theorem eq_two_of_one_add_eq_three {c : ℕ∞}
    (h : (1 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 3) : c = 2 := by
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rwa [WithBot.coe_add])
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h'
    norm_cast
    omega

/-- Dimension arithmetic: `d + 2 = 3` forces `d = 1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe e =>
      have h' : (((e + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast
        exact h
      have : e + 2 = 3 := by exact_mod_cast WithBot.coe_injective h'
      obtain rfl : e = 1 := by omega
      rfl

/-- A point of a prime divisor other than its generic point has coheight at least two. -/
private theorem two_le_coheight_of_mem_support {X : Scheme.{u}} (S : MMP.Mori.PrimeDivisor X)
    {p : X} (hp : p ∈ S.support) (hne : p ≠ S.genericPoint) : 2 ≤ Order.coheight p := by
  have hs : S.genericPoint ⤳ p := specializes_iff_mem_closure.mpr
    (by rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
  have h : Order.coheight S.genericPoint + 1 ≤ Order.coheight p :=
    Order.coheight_add_one_le (lt_of_le_not_ge hs fun e => hne.symm (hs.antisymm e).eq)
  rwa [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h

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
  exact eq_one_of_add_two_eq_three h

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
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : LocallyOfFinitePresentation sY :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sY)).mpr inferInstance
  have : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
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
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2)
      fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    have := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
  exact ⟨S, MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset
    sY hreg S (hU ▸ hT), hU⟩

/-- An element lies in the support of `∑_{E ∈ S} single E 1` exactly when it is in `S`. -/
private theorem mem_support_sum_single {α : Type*} (S : Finset α) (G : α) :
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
  have : IsAlgClosed k := hB.1.isAlgClosed
  have : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.isPair
  obtain ⟨Y, f, hres, hpure, hS, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D
  have : IsProper f := IsProjective.isProper hres.isProjective
  have hfres : IsSmoothResolution sX f :=
    ⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsNormal Y := hY.2
  have : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  have : AlgebraicGeometry.IsNoetherian Y := {}
  obtain ⟨⟨BY, hBY, -⟩, -⟩ :=
    IsPair.existsUnique_isCrepantBoundary hB.1.isPair hK f hY hfres.isBirationalMorphism
  obtain ⟨S, hsncS, hU⟩ :=
    exists_finset_isSNC_of_isSNCClosedSubset (f ≫ sX) hfres.isSmoothScheme hS
  have hsupp : (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support = S :=
    Finset.ext fun G => mem_support_sum_single S G
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
    refine hmem _ ?_
    rw [hU]
    exact (genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hX, hK, hq⟩ hY
      hfres.isBirationalMorphism hBY hG).imp_right (hBD ·)

/-! ### Exceptional divisors and the log discrepancies of the components -/

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
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
  have : IsAlgClosed k := hB.1.1.isAlgClosed
  have : CharZero k := hB.1.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.1.isPair
  have : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  have : IsIntegral W := hW.1.toIsIntegral
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
    have hcod := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX π
      (hY := hX.1) (hX := hW.1) hπ.isBirationalMorphism
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
  have := MMP.isIso_stalkMap_of_mem_biregularLocus π hw
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
      Closeds.ext (by rwa [Closeds.coe_closure])
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
    have := hπ.isBirationalMorphism.isDominant
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
  have := hπ.isBirationalMorphism.isDominant
  have : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
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
  have := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
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
  have := IsRegularLocalRing.isDomain R
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
  have : LocallyOfFinitePresentation sW :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sW)).mpr inferInstance
  have : Smooth sW := Aux.smooth_of_isSmoothScheme' sW hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field sW w
  have := IsRegularLocalRing.isDomain (W.presheaf.stalk w)
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
  have : IsAlgClosed k := hB.1.1.isAlgClosed
  have : CharZero k := hB.1.1.charZero
  obtain ⟨hX, -⟩ := hB.1.1.isPair
  have : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  have : IsIntegral W := hW.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : IsNormal W := hW.2
  have : CompactSpace W := (hW.1.toQuasiCompact).compactSpace_of_compactSpace
  have : AlgebraicGeometry.IsNoetherian W := {}
  have := hπ.isBirationalMorphism.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  set J := sncIndexSet T (Z : Set W) with hJdef
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set W) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hZη : (Z : Set W) = closure {η} :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def.symm
  have hJsub : ∀ E ∈ J, (Z : Set W) ⊆ E.support := fun E hE => (Finset.mem_filter.1 hE).2
  have hcl : IsClosed (⋂ E ∈ J, (E.support : Set W)) :=
    isClosed_biInter fun E _ => SNCWeight.PrimeDivisorUnion.isClosed_support E
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
  have := D'.isIntegral
  have := D'.isDominant
  have : IsProper D'.f := hD'p
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have hbir : IsBirationalMorphism (D'.f ≫ π) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational π D'.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hπ.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D'.isBirationalMorphism)
  have := hbir.isDominant
  let D₀ : DivisorOver k sX :=
    ⟨D'.Y, D'.f ≫ π, by simpa only [Category.assoc] using D'.isNormalVariety, hbir, D'.E⟩
  have hD₀p : IsProper D₀.f := (inferInstance : IsProper (D'.f ≫ π))
  have hv₀ : D'.valuation.comap (functionFieldMap π) = D₀.valuation := by
    ext t
    change D'.E.divisorialValuation (functionFieldMap D'.f (functionFieldMap π t)) =
      D'.E.divisorialValuation (functionFieldMap (D'.f ≫ π) t)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  -- the centre of `ν` is off `Ex(π)` and has codimension at least two
  set p := D'.f D'.E.genericPoint
  have hpZ₀ : p ∈ (Z₀ : Set W) := by
    rw [hZ₀D', D'.center_eq_closure_genericPoint]
    exact subset_closure rfl
  have hpη : p ⤳ η := by
    have : η ∈ (D'.center : Set W) := hZ₀D' ▸ hZZ₀ hηZ
    rwa [D'.center_eq_closure_genericPoint, ← specializes_iff_mem_closure] at this
  have hpEx : p ∉ (exceptionalSet π : Set W) := fun h =>
    hZ (hpη.mem_closed (exceptionalSet π).isClosed h)
  have hcod : codimension D₀.center = codimension D'.center :=
    codimension_center_eq_of_notMem_exceptionalSet D' D₀ hv₀ hpEx
  have h2 : 2 ≤ codimension D'.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    have key : ∀ E ∈ J, p ≠ E.genericPoint → 2 ≤ Order.coheight p := fun E hE =>
      two_le_coheight_of_mem_support E (Set.mem_iInter₂.1 (hZ₀I hpZ₀) E hE)
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
  have : IsIso (π ∣_ MMP.Mori.biregularLocus π) := MMP.Mori.isBiregular_biregularLocus π
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
  by_contra hne
  have h := two_le_coheight_of_mem_support S hp hne
  rw [h1] at h
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
  exact closure_minimal (Set.singleton_subset_iff.2 hηG)
    (SNCWeight.PrimeDivisorUnion.isClosed_support E)

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
  exact (hEgen.map π.continuous).mem_closed (SNCWeight.PrimeDivisorUnion.isClosed_support S) hES

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
  have : LocallyOfFinitePresentation (G.idealSheaf.subschemeι ≫ sW) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := G.idealSheaf.subschemeι ≫ sW)).mpr inferInstance
  have : Smooth (G.idealSheaf.subschemeι ≫ sW) := Aux.smooth_of_isSmoothScheme' _ hG
  have := isRegularLocalRing_stalk_of_smooth_over_field (G.idealSheaf.subschemeι ≫ sW) z
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
  have : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (π ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := π ≫ sX)).mpr inferInstance
  have : Smooth (π ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hπ.isSmoothScheme
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set W) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hηB : π η ∈ MMP.Mori.biregularLocus π :=
    of_not_not fun h => hZ (MMP.Mori.mem_exceptionalSet.2 h)
  have := MMP.isIso_stalkMap_of_mem_biregularLocus π hηB
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
  · have := isRegularLocalRing_stalk_of_smooth_over_field (π ≫ sX) η
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · by_cases hS : π η ∈ S.support
    · refine notMem_image_singularLocus_of_isRegularLocalRing_quotient S ?_
      have := isRegularLocalRing_quotient_of_isSmoothScheme G
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
  exact closure_minimal (Set.singleton_subset_iff.2 hηE)
    (SNCWeight.PrimeDivisorUnion.isClosed_support E')

/-- A component through a centre met by exactly two components `G₀, G₁` is one of them. -/
private theorem eq_or_eq_of_sncIndexSet_eq_pair {W : Scheme.{u}} {T : Divisor W} {Z : Set W}
    [DecidableEq (MMP.Mori.PrimeDivisor W)] {G₀ G₁ : MMP.Mori.PrimeDivisor W}
    (hJ : sncIndexSet T Z = {G₀, G₁})
    (i : sncIndexSet T Z) : i.1 = G₀ ∨ i.1 = G₁ := by
  simpa [hJ] using i.2

/-! ### Echo ideals as monomial ideals -/

section EchoAlgebra

variable {R : Type*} [CommRing R]

/-- Powers of `𝔪 = (x, t)` are generated by the monomials of degree at least the exponent. -/
private theorem pow_le_monomialIdeal_one {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) (c : ℕ) : 𝔪 ^ c ≤ MMP.Resolution.monomialIdeal t x 1 c := by
  induction c with
  | zero =>
    intro r _
    have h1 : (1 : R) ∈ MMP.Resolution.monomialIdeal t x 1 0 := by
      rw [MMP.Resolution.monomialIdeal]
      exact Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩
    simpa using Ideal.mul_mem_left (MMP.Resolution.monomialIdeal t x 1 0) r h1
  | succ c ih =>
    calc 𝔪 ^ (c + 1) = 𝔪 ^ c * 𝔪 := pow_succ _ _
      _ ≤ MMP.Resolution.monomialIdeal t x 1 c * Ideal.span {x, t} := Ideal.mul_mono ih h𝔪.ge
      _ ≤ MMP.Resolution.monomialIdeal t x 1 (c + 1) := ?_
    rw [MMP.Resolution.monomialIdeal, MMP.Resolution.monomialIdeal, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨a, b, hab, rfl⟩, s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact Ideal.subset_span ⟨a, b + 1, by omega, by ring⟩
    · exact Ideal.subset_span ⟨a + 1, b, by omega, by ring⟩

/-- If `𝔪 = (x, t)` and `j ≥ 1`, the echo ideal `∑_b x^b 𝔪^{n - jb}` is generated by the
monomials `t^a x^b` with `a + j b ≥ n`. -/
private theorem echoIdeal_eq_monomialIdeal {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    echoIdeal x 𝔪 j n = MMP.Resolution.monomialIdeal t x j n := by
  refine le_antisymm (iSup_le fun b => ?_) ?_
  · refine (Ideal.mul_mono_right (pow_le_monomialIdeal_one h𝔪 _)).trans ?_
    rw [MMP.Resolution.monomialIdeal, MMP.Resolution.monomialIdeal, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, rfl, _, ⟨a', b', h, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨a', b + b', ?_, by ring⟩
    have : b' ≤ j * b' := Nat.le_mul_of_pos_left b' hj
    rw [Nat.mul_add]
    omega
  · rw [MMP.Resolution.monomialIdeal]
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

/-- The image of `MMP.Resolution.monomialIdeal t x j n` under a ring homomorphism. -/
private theorem map_monomialIdeal {S : Type*} [CommRing S] (φ : R →+* S) (t x : R)
    (j n : ℕ) :
    (MMP.Resolution.monomialIdeal t x j n).map φ =
      MMP.Resolution.monomialIdeal (φ t) (φ x) j n := by
  rw [MMP.Resolution.monomialIdeal, MMP.Resolution.monomialIdeal, Ideal.map_span]
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
  have hGxJ : Gx ∈ sncIndexSet T (Z : Set W) := by simp [hJ]
  have hGtJ : Gt ∈ sncIndexSet T (Z : Set W) := by simp [hJ]
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
    rw [weightedMonomialIdeal_eq_of_pair h01 huniv, echoIdeal_eq_monomialIdeal hxt hj,
      map_monomialIdeal, MMP.Resolution.monomialIdeal, hz₀, hz₁, hα₀, hα₁]
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

/-- An open subscheme contained in the one-label smooth locus is smooth over `k`. -/
private theorem isSmoothScheme_of_subset_oneLabelSmoothLocus {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {U : Y.Opens}
    (hUL : (U : Set Y) ⊆ oneLabelSmoothLocus L) : IsSmoothScheme (U.ι ≫ sY) := by
  have : LocallyOfFinitePresentation (U.ι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sY)).mpr inferInstance
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, eq_top_iff]
  intro v _
  refine ((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (U.ι ≫ sY)).1 v).2 ?_
  have : IsRegularLocalRing (Y.presheaf.stalk (U.ι v)) :=
    (mem_oneLabelSmoothLocus_iff.mp (hUL v.2)).1
  exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap v)).commRingCatIsoToRingEquiv

/-- If `a = m₀ c + m₁ + e < 2` with `m₀, m₁ ≥ 1` and `c > 0`, then `m₁ = 1` and `e = 0`. -/
private theorem eq_one_and_eq_zero_of_lt_two {m₀ m₁ : ℤ} {e : ℕ} {a c : ℝ} (h₀ : 1 ≤ m₀)
    (h₁ : 1 ≤ m₁) (hc : 0 < c) (ha : a = m₀ * c + m₁ * 1 + e) (ha2 : a < 2) :
    m₁ = 1 ∧ e = 0 := by
  have h₀' : (1 : ℝ) ≤ m₀ := by exact_mod_cast h₀
  have h₁' : (1 : ℝ) ≤ m₁ := by exact_mod_cast h₁
  have he : (0 : ℝ) ≤ e := e.cast_nonneg
  have hlt : (m₁ : ℝ) + e < 2 := by nlinarith
  have hm : m₁ < 2 := by exact_mod_cast (show (m₁ : ℝ) < 2 by linarith)
  have he1 : (e : ℝ) < 1 := by linarith
  exact ⟨by omega, Nat.lt_one_iff.1 (by exact_mod_cast he1)⟩

/-- An ideal whose image under a bijective ring map is generated by the image of `t` is
generated by `t`. -/
private theorem eq_span_singleton_of_map_eq {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Bijective φ) {I : Ideal R} {t : R}
    (h : Ideal.span {φ t} = I.map φ) : I = Ideal.span {t} := by
  have h' : (Ideal.span {t}).map φ = I.map φ := by rwa [Ideal.map_span, Set.image_singleton]
  have h₂ := congrArg (Ideal.comap φ) h'
  rw [Ideal.comap_map_of_bijective _ hφ, Ideal.comap_map_of_bijective _ hφ] at h₂
  exact h₂.symm

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
  have : IsAlgClosed k := hΘ.1.1.isAlgClosed
  have : CharZero k := hΘ.1.1.charZero
  have hY : IsNormalVariety k sY := hΘ.1.1.isPair.1
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  set V := D.center with hVdef
  set y := V.isIrreducible.genericPoint with hydef
  have hyV : y ∈ (V : Set Y) := (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hyP : y ∈ P.support := hVP hyV
  have hreg : IsRegularLocalRing (Y.presheaf.stalk y) := (mem_oneLabelSmoothLocus_iff.mp hη).1
  -- a local equation `x` of `P` at `η_V`, and its completion `t`
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hyP
  have := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk y)
  obtain ⟨x, hxq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
  have hx : IdealSheafData.stalk P.idealSheaf y = Ideal.span {x} := hq.trans hxq
  obtain ⟨⟨t, ht, U, hyU, hUL, hUS, xU, tU, hxU, htU, SU, LU, Zu, hSU, hSUx, hLUt, hne, hsnc,
    hZu, hZmax⟩, -⟩ := isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation sY L P
      V 1 hY hdim hP hVP hV hη le_rfl x hx
  have hxt : Ideal.span {x, t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    have := ht.1
    rwa [Matrix.range_cons_cons_empty] at this
  set u : U.toScheme := ⟨y, hyU⟩ with hu
  have huZ : u ∈ (Zu : Set U.toScheme) := by rwa [hZu]
  have huLU : u ∈ LU.support := (hZmax.1.2 huZ).2
  -- the prime divisor `L' = {t = 0}` of `Y`
  set L' := OpenWeilRestriction.primeDivisorMap U.ι LU with hL'def
  have hL'supp : ∀ v : U.toScheme, U.ι v ∈ L'.support ↔ v ∈ LU.support :=
    MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι LU
  have hyL' : y ∈ L'.support := (hL'supp u).2 huLU
  have ht' : IdealSheafData.stalk L'.idealSheaf y = Ideal.span {t} := by
    have h1 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map U.ι L'.idealSheaf u
    rw [MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap, hLUt u, ← htU] at h1
    exact eq_span_singleton_of_map_eq (φ := (U.ι.stalkMap u).hom) (t := t)
      (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv.bijective h1
  have hL'L : L' ∉ L := by
    intro h
    have h1 : L' = P := eq_of_mem_oneLabelSmoothLocus hη h hP hyL' hyP
    have h2 : LU.genericPoint ∈ SU.support := by
      have h3 : U.ι LU.genericPoint ∈ L'.support :=
        (hL'supp _).2 (MMP.Flips.primeDivisor_genericPoint_mem_support LU)
      rw [h1] at h3
      rwa [hSU]
    exact hne (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support h2)
  have hcoeff : Θ.coeff L' = 0 := by
    by_contra h
    exact hL'L (hsupp (by rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]))
  -- a log resolution of `(Y, L + L')`, an isomorphism over `U`
  have hsupp' : Θ.support ⊆ insert L' L := hsupp.trans (Finset.subset_insert _ _)
  obtain ⟨W, π, T, hπ, -, hT, hiso⟩ := exists_isLogSmoothDatum hΘ.1 (insert L' L) hsupp'
  have hUsm : IsSmoothScheme (U.ι ≫ sY) := isSmoothScheme_of_subset_oneLabelSmoothLocus hUL
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
          exact ⟨SU, Or.inl rfl, by rwa [hSU]⟩
        · exact absurd hvS (Set.disjoint_left.1 (hUS S hSL hSP) v.2)
    · rintro ⟨F, hF, hvF⟩
      rcases hF with rfl | rfl
      · exact ⟨P, Or.inr hP, by rwa [hSU] at hvF⟩
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
  have : IsIntegral W := hWv.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  have : IsNormal W := hWv.2
  have := hπ.isBirationalMorphism.isDominant
  obtain ⟨D', -, hΦ, e0, he, hrest⟩ := exists_logSmoothFormula_at_centre hπ aT haT ha
  set η := D'.center.isIrreducible.genericPoint
  obtain ⟨z, m, hz, hm1, hm, hform'⟩ := hrest
  have hπη : π η = y := map_genericPoint_center_eq_of_comap_eq D' D hΦ
  have hηB : π η ∈ MMP.Mori.biregularLocus π := by rwa [hπη]
  have hηEx : η ∉ (exceptionalSet π : Set W) := fun h => (MMP.Mori.mem_exceptionalSet.1 h) hηB
  -- the components of `T` through the centre are the lifts of `P` and `L'`
  obtain ⟨Gx, hGxJ, hGxgen, hGxI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_of_mem hP) (by rwa [hπη])
  obtain ⟨Gt, hGtJ, hGtgen, hGtI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_self L' L) (by rwa [hπη])
  have hPL' : P ≠ L' := fun h => hL'L (h ▸ hP)
  have hGxGt : Gx ≠ Gt := fun h => hPL' (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hGxgen.symm.trans ((congrArg (fun G => π G.genericPoint) h).trans hGtgen)))
  have hJ : sncIndexSet T (D'.center : Set W) = {Gx, Gt} := by
    ext E
    rw [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hE => ?_, fun h => h.elim (fun h => h ▸ hGxJ) (fun h => h ▸ hGtJ)⟩
    obtain ⟨hEEx, S, hSD, hηS, hES⟩ := exists_genericPoint_eq_of_mem_sncIndexSet hT hηEx hE
    have hEB : π E.genericPoint ∈ MMP.Mori.biregularLocus π :=
      of_not_not fun h => hEEx (MMP.Mori.mem_exceptionalSet.2 h)
    rw [Finset.mem_insert] at hSD
    rcases hSD with rfl | hSL
    · exact Or.inr (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_of_mem_biregularLocus π hEB (hES.trans hGtgen.symm)))
    · have hSP : S = P := eq_of_mem_oneLabelSmoothLocus hη hSL hP (by rwa [← hπη]) hyP
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
  have haGt : aT Gt = 1 := by simp [hval Gt L' hGtgen, hcoeff]
  rw [hsum, haGt] at hform'
  obtain ⟨hm₁, rfl⟩ := eq_one_and_eq_zero_of_lt_two (hm1 i₀) (hm1 i₁) (hpos Gx) hform' ha2
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
`Y`, with `a(ξ; Y, Θ) < 2`, which are not an echo of any order of any label at any curve, form a
finite set. -/
private theorem finite_setOf_not_isEcho {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (_ : MMP.Mori.IsProjectiveVariety ℂ sY) (_ : MMP.Fourfold.IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : MMP.Fourfold.IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sY ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ sY ξ ∧
        (∃ a < 2, MMP.Fourfold.HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          MMP.Fourfold.IsEcho sY L S V j ξ}.Finite := by
  classical
  have hY : IsNormalVariety ℂ sY := hΘ.1.1.isPair.1
  have : IsSeparated sY := hY.1.toIsSeparated
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  obtain ⟨W, π, T, hπ, hpure, hT, -⟩ := exists_isLogSmoothDatum hΘ.1 L hsupp
  obtain ⟨n, K, hK, aT, haT, hpos, hexc, -⟩ := exists_logDiscrepancy_primeDivisor hΘ hπ
  have hWv : IsNormalVariety ℂ (π ≫ sY) := hπ.isNormalVariety
  have : IsIntegral W := hWv.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  have : IsNormal W := hWv.2
  have : CompactSpace W := (hWv.1.toQuasiCompact).compactSpace_of_compactSpace
  have : AlgebraicGeometry.IsNoetherian W := {}
  have := hπ.isBirationalMorphism.isDominant
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
    have h2 : (m ⟨j, hj⟩ : ℝ) < 2 / aT j := (lt_div_iff₀ (hpos j)).2 h1
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
      have := hY.1
      have := hWv.1
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
          have : IsEmpty (sncIndexSet T (D'.center : Set W)) :=
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
          exact closure_minimal (Set.singleton_subset_iff.2 hηP)
            (SNCWeight.PrimeDivisorUnion.isClosed_support P)
        obtain ⟨j, hj⟩ := exists_isEcho_of_mem_oneLabelSmoothLocus hΘ hsupp hdim ha ha2 hPL hVP hV
          (hπη ▸ hηY)
        exact hnot ⟨P, D.center, j, hDξ ▸ hj⟩
    · -- two components through the centre: excluded by terminality
      have h := one_lt_sum_of_two_le_card hΘ hπ hK aT haT hηEx hcard
      have : ∑ j ∈ sncIndexSet T (D'.center : Set W), aT j ≤ ∑ j, (m j : ℝ) * aT j := by
        rw [← Finset.sum_coe_sort]
        exact Finset.sum_le_sum fun j _ => hle1 j
      linarith

end Echoes

section EchoesCurve

open MMP.Mori MMP.Fourfold

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
  have : LocallyOfFiniteType sY := hvar.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (D.f D.E.genericPoint)
  rw [← D.center_eq_closure_genericPoint, hV, hdim] at h
  rw [MMP.Positivity.DivisorOver.codimension_center]
  exact (eq_two_of_one_add_eq_three h).ge

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

/-- On a projective `ℚ`-factorial terminal threefold, only finitely many divisorial valuations
centred at a curve `V` have log discrepancy `< 2`. -/
private theorem finite_setOf_isCentre {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y]
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

end EchoesCurve

section Labels

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail IsLocalRing

/-! ### Uniqueness of the centre of a label -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The transport of a valuation of `k(X_0)` to `k(X_i)` is unique. -/
private theorem isTransportedValuationFrom_unique {T : StabilizedTail} :
    ∀ (i : ℕ) {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
      {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, h⟩, ⟨u', hu', h'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    have := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    have := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    exact valuation_eq_of_comap_eq
      ((T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism
        |>.functionFieldMap_bijective.2)
      ((show _ = _ from h).trans (show _ = _ from h').symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
    (D := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P)
    (D' := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P') (by
      change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
      rw [hv]; rfl)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- The extension of function fields of a composite is the composite of the extensions. -/
private theorem coe_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] :
    ⇑(functionFieldMap (a ≫ b)) = functionFieldMap a ∘ functionFieldMap b :=
  funext fun t => (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm

/-- A composite of dominant morphisms surjective on function fields is surjective on them. -/
private theorem surjective_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] {a : A ⟶ B} {b : B ⟶ C} [IsDominant a] [IsDominant b]
    (ha : Function.Surjective (functionFieldMap a))
    (hb : Function.Surjective (functionFieldMap b)) :
    Function.Surjective (functionFieldMap (a ≫ b)) := by
  rw [coe_functionFieldMap_comp]
  exact ha.comp hb

/-- If `a ≫ b` is surjective on function fields, so is `b` (field maps are injective). -/
private theorem surjective_functionFieldMap_of_comp {A B C : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] [IsIntegral C] {a : A ⟶ B} {b : B ⟶ C} [IsDominant a] [IsDominant b]
    (hab : Function.Surjective (functionFieldMap (a ≫ b))) :
    Function.Surjective (functionFieldMap b) := by
  rw [coe_functionFieldMap_comp] at hab
  exact hab.of_comp_left (functionFieldMap a).injective

/-- If `π : V ⟶ Z` is dominant and induces a surjection of function fields, so does every
morphism `π_k : V_k ⟶ Z`, `k ≤ m`, of a finite relative programme over `Z` from `V`. -/
private theorem surjective_functionFieldMap_modelMap_of_le {V Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} [IsIntegral Z] {K : MMP.Mori.Divisor V}
    {Θ : MMP.Mori.QDivisor V}
    (P : RelativeThreefoldProgram sV sZ π K Θ) [IsDominant π]
    (hπ : Function.Surjective (functionFieldMap π)) :
    ∀ n ≤ P.m, ∃ _ : IsDominant (modelMap π P.πY n),
      Function.Surjective (functionFieldMap (modelMap π P.πY n))
  | 0, _ => ⟨‹_›, hπ⟩
  | n + 1, hn => by
    obtain ⟨hd, hs⟩ := surjective_functionFieldMap_modelMap_of_le P hπ n (by omega)
    have hD := P.isThreefoldStepDiagram n (by omega)
    have := hD.isNormalVariety_target.1.toIsIntegral
    have := hD.isBirationalMorphism_minus.isDominant
    have := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    revert hd hs
    rw [P.modelMap_eq n (by omega)]
    intro hd hs
    have : IsDominant (P.h n) := IsDominant.of_comp (P.g n) (P.h n)
    change ∃ _ : IsDominant (P.πY n), Function.Surjective (functionFieldMap (P.πY n))
    rw [P.πY_eq n (by omega)]
    exact ⟨inferInstance, surjective_functionFieldMap_comp
      hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
      (surjective_functionFieldMap_of_comp hs)⟩

/-- On the model `V_k` of a bridge, the morphism `π_k : V_k ⟶ Z_i` induces a surjection of
function fields. -/
private theorem surjective_functionFieldMap_modelMap {T : StabilizedTail}
    (C : TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    [IsIntegral (T.Z i)] [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)] :
    Function.Surjective
      (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) := by
  have hpb := (C.junction i).isBirationalMorphism
  have hfb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
  have := hpb.isDominant
  have := hfb.isDominant
  exact ((surjective_functionFieldMap_modelMap_of_le (C.bridge i).P
    (surjective_functionFieldMap_comp hpb.functionFieldMap_bijective.2
      hfb.functionFieldMap_bijective.2) k k.2.le).2)

/-- The centre of a label on a model of a terminal chain is unique. -/
private theorem isLabelCentre_unique {T : StabilizedTail} (C : TerminalChain T)
    {S : C.Label} {x : C.ModelIndex} {P P' : MMP.Mori.PrimeDivisor (C.model x)}
    (h : C.IsLabelCentre S x P) (h' : C.IsLabelCentre S x P') : P = P' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hPw⟩ := h
    obtain ⟨w', hw', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    have := hb.isDominant
    exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
      hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)
  · obtain ⟨w, hw, hdom, hPw⟩ := h
    obtain ⟨w', hw', _hdom', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    have := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact primeDivisor_eq_of_valuationOver_eq
      ((C.bridge i).P.isQFactorial k (by omega)).1
      (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)
      (surjective_functionFieldMap_modelMap C i k) (hPw.trans hPw'.symm)

/-! ### The order valuation at a curve -/

/-- The map `WithTop ℤ → ℤᵐ⁰` sending `⊤ ↦ 0` and `n ↦ exp (-n)`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private lemma expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg, ← WithTop.coe_add, neg_add, WithZero.exp_add, mul_comm]

private lemma expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R ℤᵐ⁰ where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg]
  map_one' := by simp [← WithTop.coe_zero, expNeg]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

/-- A pair `(x, y)` is a regular system of parameters iff it spans `𝔪` and `dim A = 2`. -/
private lemma isRegularSystemOfParameters_pair_iff {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A} :
    IsRegularSystemOfParameters ![x, y] ↔
      Ideal.span {x, y} = maximalIdeal A ∧ ringKrullDim A = 2 := by
  rw [isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl

/-- A regular system of parameters `(x, y)` remains one after swapping its entries. -/
private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  rw [isRegularSystemOfParameters_pair_iff, Set.pair_comm]
  exact isRegularSystemOfParameters_pair_iff.1 hxy

/-- For a regular system of parameters `(x, t)` of `𝒪_{X,η_V}` at the generic point of a
codimension-two irreducible closed subset `V` of a normal variety, and `j ≥ 1`, the monomial
valuation `v_{x,t;j}` exists. -/
private theorem exists_isWeightedMonomialValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hX : IsNormalVariety ℂ sX) {V : IrreducibleCloseds X}
    (hcodim : codimension V = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint))
    {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    (hxt : IsRegularSystemOfParameters ![x, t]) {j : ℕ} (hj : 1 ≤ j) :
    ∃ v : Valuation X.functionField ℤᵐ⁰, IsWeightedMonomialValuation sX V x t j v := by
  have := hreg
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    X.functionField (isRegularSystemOfParameters_swap hxt) hj
  refine ⟨valuationOfAddValuation W, hX, hcodim, hreg, hxt, hj, fun f hf => ?_⟩
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
  refine ⟨M, hM.symm, ?_⟩
  change expNeg (W _) = _
  rw [hW, ← hM]
  rfl

/-- On a normal complex threefold, the order of the local ring at the generic point of an
irreducible closed curve along which it is regular is a generic blowup valuation. -/
private theorem exists_isGenericBlowupValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] (hX : IsNormalVariety ℂ sX) (h3 : topologicalKrullDim X = 3)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 1)
    (hreg : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint)) :
    ∃ v : Valuation X.functionField ℤᵐ⁰, IsGenericBlowupValuation sX V v := by
  have := hreg
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, h3] at h
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := eq_two_of_one_add_eq_three h
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  obtain ⟨n, z, hz⟩ :=
    MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  have hz' : IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨v, hv⟩ := exists_isWeightedMonomialValuation hX hcodim hreg hz' le_rfl
  exact ⟨v, (isGenericBlowupValuation_iff_isWeightedMonomialValuation h3 hV hcodim hz').mpr hv⟩

/-- The sum `∑_h m_h b_h` over the labels is the multiplicity `mult_{η_C} Θ` of the boundary,
since `Θ = ∑_h b_h S_h` for the pairwise distinct centres `S_h` of the labels. -/
private theorem finsum_mul_eq_multiplicityAt {T : StabilizedTail} (Q : PreparedChain T)
    (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1))
    (m : Q.chain.Label → ℕ) (b : Q.chain.Label → ℚ)
    (hm : ∀ S, (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      Q.chain.IsLabelCentre S x.1 P ∧ MMP.Resolution.multAt P.idealSheaf γ.point = m S) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        m S = 0))
    (hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S)) :
    ∑ᶠ S, (m S : ℚ) * b S =
      DivisorWithCoeffs.multiplicityAt (Q.chain.modelBoundary x.1) γ.point := by
  classical
  obtain ⟨-, -, -, -, ⟨c, hc, hcentre, hsupp, -⟩, -⟩ := Q.echoSetting_model x
  set Θ := Q.chain.modelBoundary x.1
  let f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) → ℚ := fun P =>
    ((P.multiplicityAt γ.point).toNat : ℚ) * Θ.coeff P
  have hmb : ∀ S, (m S : ℚ) * b S = f (c S) := fun S => by
    obtain ⟨P, hP, hPb⟩ := hb S
    obtain rfl := isLabelCentre_unique _ hP (hcentre S)
    rcases hm S with ⟨P, hP', hPm⟩ | ⟨h, -⟩
    · obtain rfl := isLabelCentre_unique _ hP' (hcentre S)
      have : (c S).multiplicityAt γ.point = m S := by
        rw [← hPm, PrimeDivisor.multiplicityAt, MMP.Resolution.multAt,
          MMP.Resolution.idealOrder, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
      simp only [f, this, ENat.toNat_coe, Θ, hPb]
    · exact absurd (hcentre S) (h _)
  have := Q.chain.finite_label
  have := Fintype.ofFinite Q.chain.Label
  rw [finsum_eq_sum_of_fintype, DivisorWithCoeffs.multiplicityAt, Finsupp.sum]
  calc ∑ S, (m S : ℚ) * b S = ∑ P ∈ Finset.univ.image c, f P := by
        rw [Finset.sum_image fun S _ S' _ h => hc h]
        exact Finset.sum_congr rfl fun S _ => hmb S
    _ = ∑ P ∈ Finsupp.support Θ, f P := by
      refine (Finset.sum_subset (fun P hP => ?_) fun P _ hP => ?_).symm
      · obtain ⟨S, rfl⟩ := hsupp P (by simpa [DivisorWithCoeffs.coeff_apply] using hP)
        exact Finset.mem_image_of_mem c (Finset.mem_univ S)
      · simp [f, DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP]
    _ = _ := Finset.sum_congr rfl fun P _ => by
      simp [f, nsmul_eq_mul, DivisorWithCoeffs.coeff_apply]

end Labels

/-! ### Branch numbers and multiplicities -/

section Branch

open MMP.Mori MMP.Fourfold

/-- The multiplicity of a prime divisor along an irreducible closed subset is the multiplicity of
its ideal at the generic point. -/
private theorem multiplicityAlong_eq_multAt {Y : Scheme.{0}} (D : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) :
    D.multiplicityAlong V = MMP.Resolution.multAt D.idealSheaf V.isIrreducible.genericPoint := by
  rw [MMP.Mori.PrimeDivisor.multiplicityAlong, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rfl

/-- On a threefold, the generic point of a proper curve has coheight two. -/
private theorem coheight_point_eq_two {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (γ : MMP.Mori.ProperCurve sY) : Order.coheight γ.point = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY γ.point
  rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, γ.isProperCurve.dim_eq, hY] at h
  exact eq_two_of_one_add_eq_three h

/-- On a threefold that is regular at the generic points of its curves, the branch number of a
prime divisor `P` at a proper curve `C` is at most the multiplicity of `P` at `η_C`. -/
private theorem branchNumber_le_multAt {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3)
    (hreg : ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 →
      IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint))
    (γ : MMP.Mori.ProperCurve sY) (P : MMP.Mori.PrimeDivisor Y) :
    (branchNumber P (closure {γ.point}) : ℕ∞) ≤ MMP.Resolution.multAt P.idealSheaf γ.point := by
  let V : IrreducibleCloseds Y :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hηV : V.isIrreducible.genericPoint = γ.point :=
    (V.isIrreducible.isGenericPoint_genericPoint_closure).eq (by
      change closure {γ.point} = closure (closure {γ.point})
      rw [closure_closure])
  have hdimV : topologicalKrullDim (V : Set Y) = 1 := by
    change topologicalKrullDim (closure {γ.point} : Set Y) = 1
    rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq]
    exact γ.isProperCurve.dim_eq
  have hring : ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [ringKrullDim_stalk_eq_coheight, hηV, coheight_point_eq_two _ hY γ]
    rfl
  have h := encard_branches_le_multiplicityAlong sY V (hreg V hdimV) hring P
  rw [multiplicityAlong_eq_multAt, hηV] at h
  rw [branchNumber, Set.ncard_def]
  exact (ENat.coe_toNat_le_self _).trans h

end Branch

/-! ### Local equations and regular parameters -/

section LocalAlgebra

open IsLocalRing MMP.Mori

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

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The order of a principal ideal `(g)`, `g ≠ 0`, of a Noetherian local domain is finite. -/
private theorem idealOrder_span_ne_top [IsDomain R] [IsNoetherianRing R] {g : R} (hg : g ≠ 0) :
    MMP.Resolution.idealOrder (Ideal.span {g}) ≠ ⊤ := by
  intro htop
  apply hg
  have h : g ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.mpr fun n =>
    ((MMP.Resolution.natCast_le_idealOrder_iff' _ n).mp (by rw [htop]; exact le_top))
      (Ideal.mem_span_singleton_self g)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at h

/-- A generator of an ideal of order one lies in `𝔪 ∖ 𝔪²`. -/
private theorem mem_maximalIdeal_and_notMem_sq_of_idealOrder_eq_one {g : R}
    (h : MMP.Resolution.idealOrder (Ideal.span {g}) = 1) :
    g ∈ maximalIdeal R ∧ g ∉ maximalIdeal R ^ 2 := by
  refine ⟨?_, fun hg => ?_⟩
  · have := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {g}) 1).mp
      (by rw [h]; rfl)
    rw [pow_one] at this
    exact this (Ideal.mem_span_singleton_self g)
  · have := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {g}) 2).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hg)
    rw [h] at this
    exact absurd this (by decide)

/-- The first member `x` of a regular system of parameters `(x, t)` does not lie in `(t)`. -/
private theorem notMem_span_singleton_of_isRegularSystemOfParameters [IsNoetherianRing R]
    {x t : R} (h : IsRegularSystemOfParameters ![x, t]) : x ∉ Ideal.span {t} := by
  intro hx
  obtain ⟨hspan, hdim⟩ := isRegularSystemOfParameters_pair_iff.1 h
  have ht : t ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {t} := by
    rw [← hspan, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hx, Ideal.mem_span_singleton_self t⟩
  have h1 : (maximalIdeal R).height ≤ 1 :=
    le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr ht) ▸
      Ideal.height_span_singleton_le_one ((mem_maximalIdeal t).mp ht)
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hdim] at h2
  have : ((maximalIdeal R).height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  rw [h2] at this
  exact absurd this (by decide)

/-- `v_{x,t;j}(s) = M` as soon as `s ∈ I_M ∖ I_{M+1}`. -/
private theorem monomialValuation_eq_of_mem_of_notMem {x t s : R} {j M : ℕ}
    (h1 : s ∈ MMP.Resolution.monomialIdeal t x j M)
    (h2 : s ∉ MMP.Resolution.monomialIdeal t x j (M + 1)) :
    MMP.Resolution.monomialValuation t x j s = M := by
  refine le_antisymm (iSup₂_le fun ν hν => ?_) (le_iSup₂_of_le M h1 le_rfl)
  by_contra hlt
  refine h2 (Ideal.span_mono ?_ hν)
  rintro r ⟨a, l, hal, rfl⟩
  exact ⟨a, l, le_trans (by exact_mod_cast Order.add_one_le_of_lt (not_le.mp hlt)) hal, rfl⟩

/-- For a regular system of parameters `(x, t)` of a two-dimensional local ring and `j ≥ 1`, the
monomial valuation of weights `(j, 1)` takes the value `v_{x,t;j}(x) = j`. -/
private theorem monomialValuation_self [IsNoetherianRing R] {x t : R}
    (h : IsRegularSystemOfParameters ![x, t]) {j : ℕ} (hj : 1 ≤ j) :
    MMP.Resolution.monomialValuation t x j x = j := by
  have hxm : x ∈ maximalIdeal R := h.1 ▸ Ideal.subset_span ⟨0, rfl⟩
  refine monomialValuation_eq_of_mem_of_notMem (Ideal.subset_span ⟨0, 1, by simp, by simp⟩) ?_
  intro hmem
  have hle : MMP.Resolution.monomialIdeal t x j (j + 1) ≤
      Ideal.span {t} ⊔ Ideal.span {x ^ 2} := by
    refine Ideal.span_le.mpr ?_
    rintro r ⟨a, l, hal, rfl⟩
    rcases a with _ | a
    · have hl : 2 ≤ l := by
        by_contra hl
        have : j * l ≤ j * 1 := Nat.mul_le_mul_left _ (by omega)
        omega
      refine Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨x ^ (l - 2), ?_⟩)
      rw [pow_zero, one_mul, ← pow_add]
      congr 1
      omega
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨t ^ a * x ^ l, by ring⟩)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hmem)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hu : IsUnit (1 - b * x) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := add_mem hm (Ideal.mul_mem_left _ b hxm)
      simpa using this))
  apply notMem_span_singleton_of_isRegularSystemOfParameters h
  have : x * (1 - b * x) = a * t := by linear_combination -hyz
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  rw [show x = a * t * w by rw [← this, mul_assoc, hw, mul_one]]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t))

/-- In a two-dimensional regular local ring, every `x ∈ 𝔪 ∖ 𝔪²` extends to a regular system of
parameters `(x, t)`. -/
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
    by_contra h
    rw [not_or] at h
    apply hx2
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 h.2) hb)
  obtain ⟨t, ht⟩ : ∃ t, Ideal.span {x, t} = IsLocalRing.maximalIdeal R := by
    rcases hunit with hu | hu
    · exact ⟨b, key hab c₀ c₁ hx.symm hu⟩
    · exact ⟨a, key (by rwa [Set.pair_comm]) c₁ c₀ (by rw [← hx]; ring) hu⟩
  refine ⟨t, ?_, by exact_mod_cast hdim⟩
  rw [← ht]
  congr 1
  ext
  simp [Matrix.range_cons, or_comm]

end LocalAlgebra

/-! ### Weighted monomial valuations at a curve -/

section Monomial

open IsLocalRing MMP.Mori MMP.Fourfold

/-- The monomial valuation `v_{x,t;j}` takes the value `exp (-j)` on `x`. -/
private theorem apply_self_of_isWeightedMonomialValuation {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] {V : IrreducibleCloseds X} {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    {j : ℕ} {v : Valuation X.functionField ℤᵐ⁰} (hv : IsWeightedMonomialValuation sX V x t j v) :
    v (algebraMap _ X.functionField x) = WithZero.exp (-(j : ℤ)) := by
  obtain ⟨-, -, hreg, hxt, hj, hval⟩ := hv
  have := hreg
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk V.isIrreducible.genericPoint)
  have hx0 : x ≠ 0 := fun h =>
    notMem_span_singleton_of_isRegularSystemOfParameters hxt (h ▸ zero_mem _)
  obtain ⟨M, hM, hvM⟩ := hval x hx0
  rw [monomialValuation_self hxt hj] at hM
  rw [hvM, show M = j by exact_mod_cast hM.symm]

/-- **The log discrepancy of `v_{x,t;j}` along a label.** Let `(X, Θ)` be a pair with effective
boundary, `v = v_{x,t;j}` a monomial valuation at `η_V`, and `S₀` a prime divisor whose ideal at
`η_V` is generated by `x`. Then `a(v; X, Θ) ≤ 1 + j (1 - Θ(S₀))`: the other components of `Θ`
only lower the log discrepancy. -/
private theorem exists_hasLogDiscrepancy_le_of_isWeightedMonomialValuation {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Θ : QDivisor X} (hΘ : MMP.Fourfold.IsPair sX Θ) (hΘ0 : ∀ S, 0 ≤ Θ.coeff S)
    {V : IrreducibleCloseds X} {x t : X.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation X.functionField ℤᵐ⁰} (hv : IsWeightedMonomialValuation sX V x t j v)
    (S₀ : MMP.Mori.PrimeDivisor X)
    (hS₀ : IdealSheafData.stalk S₀.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x}) :
    ∃ a : ℝ, HasLogDiscrepancy sX Θ v a ∧ a ≤ 1 + j * (1 - (Θ.coeff S₀ : ℝ)) := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) := hv.2.2.1
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk V.isIrreducible.genericPoint)
  choose g hg0 hg using exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint)
  let f : MMP.Mori.PrimeDivisor X → X.presheaf.stalk V.isIrreducible.genericPoint :=
    fun S => if S = S₀ then x else g S
  have hf : ∀ S, IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint =
      Ideal.span {f S} := fun S => by
    by_cases h : S = S₀
    · subst h; simp [f, hS₀]
    · simp [f, h, hg]
  have hx0 : x ≠ 0 := fun h =>
    notMem_span_singleton_of_isRegularSystemOfParameters hv.2.2.2.1 (h ▸ zero_mem _)
  have hf0 : ∀ S, f S ≠ 0 := fun S => by
    by_cases h : S = S₀
    · simp [f, h, hx0]
    · simp [f, h, hg0]
  refine ⟨_, hv.hasLogDiscrepancy hΘ f (fun S _ => hf S), ?_⟩
  have hval : ∀ S, ∃ M : ℕ, (-WithZero.log (v (algebraMap _ X.functionField (f S))) : ℤ) = M :=
    fun S => by
      obtain ⟨M, -, hvM⟩ := hv.2.2.2.2.2 (f S) (hf0 S)
      exact ⟨M, by rw [hvM, WithZero.log_exp, neg_neg]⟩
  have hterm : ∀ S, 0 ≤ (Θ.coeff S : ℝ) *
      -((WithZero.log (v (algebraMap _ X.functionField (f S))) : ℤ) : ℝ) := fun S => by
    obtain ⟨M, hM⟩ := hval S
    rw [← Int.cast_neg, hM]
    exact mul_nonneg (by exact_mod_cast hΘ0 S) (by positivity)
  have hS₀v : -((WithZero.log (v (algebraMap _ X.functionField (f S₀))) : ℤ) : ℝ) = j := by
    rw [show f S₀ = x from if_pos rfl, apply_self_of_isWeightedMonomialValuation hv,
      WithZero.log_exp]
    push_cast
    ring
  push_cast
  by_cases hmem : S₀ ∈ Θ.support
  · have := Finset.single_le_sum (fun S _ => hterm S) hmem
    rw [hS₀v] at this
    nlinarith
  · have h0 : Θ.coeff S₀ = 0 := by
      simpa [MMP.Mori.DivisorWithCoeffs.coeff_apply] using Finsupp.notMem_support_iff.mp hmem
    have := Finset.sum_nonneg fun S (_ : S ∈ Θ.support) => hterm S
    rw [h0]
    push_cast
    linarith

end Monomial

/-! ### Defaults and finite sums -/

section Arithmetic

open MMP.Fourfold

/-- **Splitting the default.** For `0 ≤ b < 1` the default `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))` is
`w(b)` plus a finite sum of the terms with `j ≥ 2`. -/
private theorem exists_defaultWeight_eq_add (N : ℕ) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ K : ℕ, defaultWeight N b = difficultyWeight N b +
      ∑ j ∈ Finset.Ico 2 K, difficultyWeight N (1 - j * (1 - b)) := by
  obtain ⟨hnz, hsum, -⟩ := defaultWeight_finite N hb0 hb1
  set K := ⌈1 / (1 - b)⌉₊ with hK
  have hpos : 0 < 1 - b := by linarith
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
  have hfK : difficultyWeight N (1 - K * (1 - b)) = 0 := by
    by_contra h
    have := hnz K hK1 h
    have := Nat.le_ceil (1 / (1 - b))
    rw [← hK] at this
    linarith
  refine ⟨K + 1, ?_⟩
  rw [hsum, ← add_zero (∑ j ∈ Finset.Ico 1 K, _), ← hfK, ← Finset.sum_Ico_succ_top hK1,
    Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  congr 1
  congr 1
  push_cast
  ring

/-- A term `w(1 - j(1 - b))` with `j ≥ 2` and `b ≤ 1/2` vanishes. -/
private theorem difficultyWeight_eq_zero_of_two_le (N : ℕ) {b : ℝ} (hb : b ≤ 1 / 2) {j : ℕ}
    (hj : 2 ≤ j) : difficultyWeight N (1 - j * (1 - b)) = 0 := by
  apply difficultyWeight_of_nonpos
  have : (2 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- A finitely supported sum of natural numbers over a set dominates the sum over any finite
subset. -/
private theorem sum_le_finsum_mem {α : Type*} {A : Set α} {g : α → ℕ}
    (hfin : (A ∩ Function.support g).Finite) (F : Finset α) (hF : ∀ a ∈ F, a ∈ A) :
    ∑ a ∈ F, g a ≤ ∑ᶠ (a) (_ : a ∈ A), g a := by
  change _ ≤ ∑ᶠ a ∈ A, g a
  have hFA : (F : Set α) ⊆ A := fun a ha => hF a ha
  rw [← Set.union_diff_cancel hFA, finsum_mem_union' Set.disjoint_sdiff_right
    (F.finite_toSet.inter_of_left _)
    (hfin.subset (Set.inter_subset_inter_left _ Set.diff_subset)), finsum_mem_coe_finset]
  exact Nat.le_add_right _ _

end Arithmetic

/-! ### The local ceiling error -/

section Main

open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedTail IsLocalRing

/-- **Local ceiling error.** On a model `(Y, Θ)` of a prepared chain `Q`, indexed by `x`, let `γ`
be an irreducible closed curve of `Y`, `β` its bracket
`∑_{c_Y(v) = γ} w_v - ∑_h r_{γ,h} d_h`
(`MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`) and `rv` its varying branch number
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingBranchNumber`). Then
`β ≥ -max{rv - 1, 0}`. -/
@[mmp "lem_mmp_indexd_ceiling_error"]
theorem _root_.MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket.neg_max_le
    {T : MMP.Fourfold.StabilizedTail} {Q : MMP.Fourfold.StabilizedTail.PreparedChain T}
    {x : Q.ModelIndex} {γ : MMP.Mori.ProperCurve (Q.chain.modelStructure x.1)} {β : ℤ} {rv : ℕ}
    (hβ : Q.IsCurveBracket x γ β) (hrv : Q.chain.IsVaryingBranchNumber x.1 γ rv) :
    -max ((rv : ℤ) - 1) 0 ≤ β := by
  classical
  obtain ⟨w, r, d, hw, hr, hd, rfl⟩ := hβ
  obtain ⟨hT, hproj, hQf, hdim, ⟨c, hcinj, hc, hsupp, hcoeff⟩, hreg⟩ := Q.echoSetting_model x
  have := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hT.1.1.isPair.1
  have : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hproj.toLocallyOfFiniteType
  set N := Q.scale with hN
  set Θ := Q.chain.modelBoundary x.1 with hΘ
  -- the curve `C`, its generic point and its local ring
  let V : IrreducibleCloseds (Q.chain.model x.1) :=
    ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hη : V.isIrreducible.genericPoint = γ.point :=
    (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).eq isGenericPoint_closure
  have hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 1 :=
    (MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq γ.point).symm.trans γ.dim_eq
  have hregV := hreg V hV
  have := IsRegularLocalRing.isDomain (Q.chain.model x.1 |>.presheaf.stalk
    V.isIrreducible.genericPoint)
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := by
    rw [hη, coheight_point_eq_two _ hdim γ]
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  have hring : ringKrullDim ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) =
      2 := by
    rw [ringKrullDim_stalk_eq_coheight, hcoh]; rfl
  -- coefficients, multiplicities, branch numbers and defaults of the labels
  set b : Q.chain.Label → ℚ := fun S => Θ.coeff (c S) with hbdef
  have hb : ∀ S, Q.chain.IsLabelCoefficient S x.1 (b S) := fun S => ⟨c S, hc S, rfl⟩
  have hb0 : ∀ S, (0 : ℝ) ≤ b S := fun S => by exact_mod_cast (hcoeff S).1
  have hb1 : ∀ S, (b S : ℝ) < 1 := fun S => by exact_mod_cast (hcoeff S).2
  have hΘ0 : ∀ P, 0 ≤ Θ.coeff P := fun P => by
    by_cases hP : Θ.coeff P = 0
    · rw [hP]
    · obtain ⟨S, rfl⟩ := hsupp P hP
      exact (hcoeff S).1
  have hmtop : ∀ S, MMP.Resolution.multAt (c S).idealSheaf γ.point ≠ ⊤ := fun S => by
    obtain ⟨g, hg0, hg⟩ := exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint)
      (c S)
    rw [← hη, MMP.Resolution.multAt, hg]
    exact idealOrder_span_ne_top hg0
  set m : Q.chain.Label → ℕ := fun S =>
    (MMP.Resolution.multAt (c S).idealSheaf γ.point).toNat with hmdef
  have hm : ∀ S, MMP.Resolution.multAt (c S).idealSheaf γ.point = m S := fun S =>
    (ENat.coe_toNat (hmtop S)).symm
  have hrm : ∀ S, r S ≤ m S := fun S => by
    obtain ⟨P, hP, hrP⟩ := hr S
    rw [isLabelCentre_unique Q.chain hP (hc S)] at hrP
    have h := branchNumber_le_multAt hdim hreg γ (c S)
    rw [hm, ← hrP] at h
    exact_mod_cast h
  have hdS : ∀ S, d S = defaultWeight N (b S) := fun S => by
    obtain ⟨b', ⟨P, hP, hPb⟩, h⟩ := hd S
    rw [h, ← hPb, isLabelCentre_unique Q.chain hP (hc S)]
  -- the first default error and the multiplicity bound
  have h1 := Q.difficultyWeight_sum_mul_labelCoefficient_ge x γ m b r rv
    (fun S => ⟨c S, hc S, hm S⟩) hb hr hrv
  have h2 := Q.sum_mul_labelCoefficient_lt_one x γ m b (fun S => Or.inl ⟨c S, hc S, hm S⟩) hb
  have h3 := finsum_mul_eq_multiplicityAt Q x γ m b (fun S => Or.inl ⟨c S, hc S, hm S⟩) hb
  simp only [finsum_eq_sum_of_fintype] at h1 h2 h3
  set σ : ℝ := ∑ S, (m S : ℝ) * (b S : ℝ) with hσ
  have hσ' : ((MMP.Mori.DivisorWithCoeffs.multiplicityAt Θ V.isIrreducible.genericPoint : ℚ) :
      ℝ) = σ := by
    rw [hη, ← h3, hσ]; push_cast; rfl
  -- the valuations centred at `C`
  set A : Set (Valuation (Q.chain.model x.1).functionField ℤᵐ⁰) :=
    {v | ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
        (Z : Set (Q.chain.model x.1)) = closure {γ.point}} with hA
  have hmemA : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V → v ∈ A :=
    fun v hv => ⟨V, hv, rfl⟩
  have hcentreA : ∀ v ∈ A, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V := by
    rintro v ⟨Z, hZ, hZV⟩
    obtain rfl : Z = V := IrreducibleCloseds.ext hZV
    exact hZ
  have hwA : ∀ v ∈ A, ∀ a : ℝ, HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ v a →
      w v = difficultyWeight N (2 - a) := by
    intro v hv a ha
    obtain ⟨-, a', ⟨n', D', -, hD'v, hD'⟩, hwa⟩ := hw v hv
    obtain ⟨n, D, hDv, hD⟩ := ha
    rw [hwa, MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD' hD
      (hD'v.trans hDv.symm)]
  have hfin : (A ∩ Function.support w).Finite := by
    have hL : Θ.support ⊆ Finset.univ.image c := by
      intro P hP
      obtain ⟨S, rfl⟩ := hsupp P (by simpa [MMP.Mori.DivisorWithCoeffs.coeff_apply] using hP)
      simp
    refine (finite_setOf_isCentre (Q.chain.modelStructure x.1) hproj hQf hdim hT hL V hV).subset ?_
    · rintro v ⟨hv, hwv⟩
      refine ⟨hcentreA v hv, ?_⟩
      obtain ⟨-, a, ⟨n, D, -, hDv, hD⟩, hwa⟩ := hw v hv
      refine ⟨a, ?_, n, D, hDv, hD⟩
      by_contra ha
      exact hwv (hwa.trans (difficultyWeight_of_nonpos (by linarith)))
  have hsumF : ∀ F : Finset (Valuation (Q.chain.model x.1).functionField ℤᵐ⁰),
      (∀ v ∈ F, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V) →
      ∑ v ∈ F, w v ≤ ∑ᶠ (v) (_ : v ∈ A), w v := fun F hF =>
    sum_le_finsum_mem hfin F fun v hv => hmemA v (hF v hv)
  -- the weight of the generic blowup valuation `v_C`
  have hgen : ∀ v, IsGenericBlowupValuation (Q.chain.modelStructure x.1) V v →
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧
        w v = difficultyWeight N σ := by
    intro v hv
    obtain ⟨-, hcen, -, ha⟩ := hv.hasLogDiscrepancy hT.1.1
    refine ⟨hcen, ?_⟩
    rw [hwA v (hmemA v hcen) _ ha, hσ']
    congr 1
    ring
  -- splitting the defaults
  choose K hK using fun S => exists_defaultWeight_eq_add N (hb0 S) (hb1 S)
  set H : Q.chain.Label → ℕ := fun S =>
    ∑ j ∈ Finset.Ico 2 (K S), difficultyWeight N (1 - j * (1 - (b S : ℝ))) with hH
  have hH0 : ∀ S, (b S : ℝ) ≤ 1 / 2 → H S = 0 := fun S hS =>
    Finset.sum_eq_zero fun j hj =>
      difficultyWeight_eq_zero_of_two_le N hS (Finset.mem_Ico.mp hj).1
  -- the key inequality on the valuations centred at `C`
  have hkey : difficultyWeight N σ + ∑ S, r S * H S ≤ ∑ᶠ (v) (_ : v ∈ A), w v := by
    by_cases hbig : ∃ h, 1 ≤ r h ∧ (1 / 2 : ℝ) < b h
    · obtain ⟨h, hrh, hbh⟩ := hbig
      -- at most one label through `C` has `b > 1/2`, with `m = r = 1`
      have hmb : ∀ S, (0 : ℝ) ≤ (m S : ℝ) * (b S : ℝ) := fun S =>
        mul_nonneg (Nat.cast_nonneg _) (hb0 S)
      have hσ1 : σ < 1 := by
        rw [hσ]
        exact_mod_cast h2
      have hle_σ : ∀ S, (m S : ℝ) * b S ≤ σ := fun S =>
        Finset.single_le_sum (fun S _ => hmb S) (Finset.mem_univ S)
      have hmh1 : 1 ≤ m h := hrh.trans (hrm h)
      have hmh : m h = 1 := by
        by_contra hne
        have h2le : (2 : ℝ) ≤ m h := by exact_mod_cast (by omega : 2 ≤ m h)
        have := hle_σ h
        nlinarith [hb0 h]
      have hrh1 : r h = 1 := le_antisymm (hmh ▸ hrm h) hrh
      have hother : ∀ S, S ≠ h → r S * H S = 0 := by
        intro S hS
        by_cases hrS : r S = 0
        · simp [hrS]
        by_cases hbS : (b S : ℝ) ≤ 1 / 2
        · simp [hH0 S hbS]
        exfalso
        have hmS : 1 ≤ m S := (Nat.one_le_iff_ne_zero.mpr hrS).trans (hrm S)
        have hpair : (m S : ℝ) * b S + (m h : ℝ) * b h ≤ σ := by
          rw [hσ, ← Finset.sum_pair (f := fun i => (m i : ℝ) * (b i : ℝ)) hS]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hmb i
        have : (1 : ℝ) ≤ m S := by exact_mod_cast hmS
        have : (1 : ℝ) ≤ m h := by exact_mod_cast hmh1
        nlinarith
      have hsumH : ∑ S, r S * H S = H h := by
        rw [Finset.sum_eq_single h (fun S _ hS => hother S hS) (by simp), hrh1, one_mul]
      rw [hsumH]
      -- a local equation `x` of `S_h` at `η_C`, completed to regular parameters `(x, t)`
      obtain ⟨g, -, hg⟩ := exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint)
        (c h)
      have hord : MMP.Resolution.idealOrder (Ideal.span {g}) = 1 := by
        rw [← hg, ← MMP.Resolution.multAt, hη, hm, hmh]
        rfl
      obtain ⟨hgm, hg2⟩ := mem_maximalIdeal_and_notMem_sq_of_idealOrder_eq_one hord
      obtain ⟨t, hgt⟩ := exists_isRegularSystemOfParameters_pair hring hgm hg2
      -- the monomial valuations `v_j = v_{x,t;j}`
      choose! vf hvf using fun (j : ℕ) (hj : 1 ≤ j) =>
        exists_isWeightedMonomialValuation hY hcodim hregV hgt hj
      have hcen : ∀ j, 1 ≤ j →
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (vf j) V := fun j hj =>
        (hvf j hj).isNormalizedDivisorialValuation_and_isCentre.2
      have hJ : ∀ j ∈ (insert 1 (Finset.Ico 2 (K h)) : Finset ℕ), 1 ≤ j := fun j hj => by
        simp only [Finset.mem_insert, Finset.mem_Ico] at hj
        omega
      have hvinj : Set.InjOn vf (insert 1 (Finset.Ico 2 (K h)) : Finset ℕ) := by
        intro j hj k hk hjk
        have h' : WithZero.exp (-(j : ℤ)) = WithZero.exp (-(k : ℤ)) := by
          rw [← apply_self_of_isWeightedMonomialValuation (hvf j (hJ j hj)),
            ← apply_self_of_isWeightedMonomialValuation (hvf k (hJ k hk)), hjk]
        exact_mod_cast neg_inj.mp (WithZero.exp_injective h')
      have hwj : ∀ j : ℕ, 1 ≤ j → difficultyWeight N (1 - j * (1 - (b h : ℝ))) ≤ w (vf j) := by
        intro j hj
        obtain ⟨a, ha, hale⟩ := exists_hasLogDiscrepancy_le_of_isWeightedMonomialValuation
          hT.1.1 hΘ0 (hvf j hj) (c h) hg
        have hale' : a ≤ 1 + j * (1 - (b h : ℝ)) := hale
        rw [hwA _ (hmemA _ (hcen j hj)) a ha]
        exact difficultyWeight_mono N (by linarith)
      have hw1 : w (vf 1) = difficultyWeight N σ :=
        (hgen _ ((isGenericBlowupValuation_iff_isWeightedMonomialValuation hdim hV hcodim
          hgt).mpr (hvf 1 le_rfl))).2
      have hF := hsumF ((insert 1 (Finset.Ico 2 (K h))).image vf) fun v hv => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        exact hcen j (hJ j hj)
      rw [Finset.sum_image hvinj, Finset.sum_insert (by simp), hw1] at hF
      refine le_trans (Nat.add_le_add_left (Finset.sum_le_sum fun j hj => hwj j ?_) _) hF
      exact hJ j (Finset.mem_insert_of_mem hj)
    · push Not at hbig
      have hsumH : ∑ S, r S * H S = 0 := Finset.sum_eq_zero fun S _ => by
        by_cases hrS : r S = 0
        · simp [hrS]
        · simp [hH0 S (hbig S (Nat.one_le_iff_ne_zero.mpr hrS))]
      rw [hsumH, add_zero]
      obtain ⟨v, hv⟩ := exists_isGenericBlowupValuation hY hdim V hV hregV
      obtain ⟨hcv, hwv⟩ := hgen v hv
      have := hsumF {v} (by simpa using hcv)
      rwa [Finset.sum_singleton, hwv] at this
  -- conclusion
  have hrd : (∑ᶠ S, r S * d S : ℕ) = ∑ S, r S * difficultyWeight N (b S) + ∑ S, r S * H S := by
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hdS, hK, mul_add]
  rw [hrd]
  push_cast
  change _ ≤ ((∑ᶠ (v) (_ : v ∈ A), w v : ℕ) : ℤ) - _
  have hkey' : ((difficultyWeight N σ : ℕ) : ℤ) + ∑ S, (r S : ℤ) * (H S : ℤ) ≤
      ((∑ᶠ (v) (_ : v ∈ A), w v : ℕ) : ℤ) := by exact_mod_cast hkey
  linarith

end Main

end MMP.IndexdCeilingError
