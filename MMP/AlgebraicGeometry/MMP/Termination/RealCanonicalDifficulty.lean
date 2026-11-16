module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltSmallDiscrepancyCenters
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Singularities.Bertini.HyperplaneDiscrepancyBound
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The real-threshold canonical difficulty drops along real canonical flips

Let `(X₀, B₀) ⟶ Z₀ ⟵ (X₁, B₁) ⟶ ⋯` be an extremal real flip sequence of real canonical pairs of
`ℚ`-factorial threefolds. The canonical difficulty
`𝔡(X, B) = ∑_{s ∈ S(B)} #𝓔_{2 - s}(X, B)` counts exceptional valuations of small log
discrepancy, `d` being the largest coefficient of `B`. It is finite for every real canonical pair,
since only finitely many exceptional valuations have log discrepancy `< 2 - d`.

Along a step of the sequence the identification `k(X⁺) ≅ k(X)` over `k(Z)` maps each
`𝓔_u(X⁺, B⁺)` into `𝓔_u(X, B)`: log discrepancies do not decrease across a flip (the negativity
lemma on a common smooth model). So `𝔡` does not increase. Now let `C` be a flipped curve. Every
divisor centred at the generic point `η_C` has log discrepancy strictly larger than on `X`, hence
`> 1`; so `X⁺` is terminal near `η_C` and therefore regular there (Kollár–Mori 5.18). The blow-up
of `C` then gives an exceptional divisor of log discrepancy `2 - ∑ mult_C(P) b_P` over `X⁺`. Its
valuation lies in `𝓔_{2-s}(X, B)` but not in the image of `𝓔_{2-s}(X⁺, B⁺)`, so `𝔡` drops
strictly whenever `s = ∑ mult_C(P) b_P ≥ d`. This happens when `C` lies in a component of maximal
coefficient, and at every step when `B = 0`.

## Main results

* `MMP.Fourfold.RealFlipSequence.realCanonicalDifficulty_ne_top_and_antitone`: finiteness of `𝔡`,
  its monotonicity along a real flip sequence, and the two strict-drop criteria.
* `MMP.Fourfold.IsRealFlipStep.exists_isLogDiscrepancy_le`: log discrepancies do not decrease
  across a real flip, and increase strictly over a point with a positive-dimensional fibre in
  `X⁺` (FA 2.28 for small contractions).
* `MMP.Fourfold.IsRealFlipStep.exists_commonModel_lt_of_notMem_biregularLocus`: on a smooth common
  model, every point over the non-biregular locus of `f` or `f⁺` lies on a prime divisor whose log
  discrepancy strictly increases across the flip.
* `MMP.Fourfold.IsRealFlipStep.isExceptional_of_map_eq`: a divisor over `X` with the same centre
  on `Z` as an exceptional divisor over `X⁺` is exceptional.
* `MMP.Fourfold.exists_isLogDiscrepancy`, `MMP.Fourfold.exists_divisorOfForm_eq`: existence of
  log discrepancies when `K_X + B` is `ℝ`-Cartier, and of a rational top form with divisor `K_X`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.28, 4.12–4.13,
  6.9
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollar-mori], 5.18
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution

/-! ### Components of an snc closed subset -/

/-- An irreducible closed subset maximal in a closed set of pure codimension one of a scheme is
the support of a prime divisor. -/
private theorem exists_primeDivisor_support_eq_of_maximal {Y : Scheme.{0}} {T : Closeds Y}
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
private theorem exists_primeDivisor_support_eq {Y : Scheme.{0}} {T : Set Y} (hTc : IsClosed T)
    (hpure : IsPureCodimOne (⟨T, hTc⟩ : Closeds Y)) {W : Set Y} (hW : W ∈ componentsOf T) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W :=
  exists_primeDivisor_support_eq_of_maximal hpure
    (W := ⟨W, hW.1.1, Aux.isClosed_of_mem_componentsOf hTc hW⟩)
    ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩

/-- **The components of an snc closed subset.** The prime divisors whose generic points lie on a
divisor `T` with simple normal crossings on a smooth scheme form a finite set whose reduced sum is
an snc divisor. -/
private theorem exists_finset_isSNC_of_isSNCClosedSubset {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] [NoetherianSpace Y] (hsm : IsSmoothScheme sY)
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
    rw [hSdef, Set.Finite.mem_toFinset]; rfl
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2) fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    have := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
  exact ⟨S, MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset
    sY hreg S (hU ▸ hT), hU⟩

/-- A prime divisor lies in the support of a reduced sum `∑_{E ∈ S} E` exactly when it is in
`S`. -/
private theorem mem_support_sum_single {X : Scheme.{0}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-! ### Adding a multiple of a prime divisor to the boundary on a smooth variety -/

/-- On a smooth variety, adding `c P` to the boundary lowers a log discrepancy by `c` times the
coefficient of `E` in the pull-back of `P`. -/
private theorem isLogDiscrepancy_add_single {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (P : MMP.Mori.PrimeDivisor X) (c : ℝ) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ P' : Divisor D.Y,
      (∃ hB, MMP.Mori.Divisor.IsPullback D.f (Finsupp.single P 1 : Divisor X) hB P') ∧
      MMP.Intersection.IsLogDiscrepancy sX n (B + Finsupp.single P c) D
        (a - c * (P'.coeff D.E : ℝ)) := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  have hC₀ : Divisor.IsCartier (Finsupp.single P 1 : Divisor X) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P
  have hB₀ := MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f
    (Finsupp.single P (1 : ℤ) : Divisor X)
  obtain ⟨C₀', hC₀'⟩ := hC₀.exists_isPullback hB₀
  refine ⟨C₀', ⟨hB₀, hC₀'⟩, hnv, hprop, ω, hω0, hK, m + 1, Fin.snoc r c,
    Fin.snoc C (Finsupp.single P 1), Fin.snoc C' C₀', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hC₀
    · simpa using hC j
  · intro Γ
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add, ← hrel Γ]
    have : ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ) =
        (if P = Γ then 1 else 0) := by
      change ((Finsupp.single P (1 : ℤ)) Γ : ℝ) = _
      rw [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]
    have h2 : DivisorWithCoeffs.coeff (Finsupp.single P c : RDivisor X) Γ =
        if P = Γ then c else 0 := by
      change (Finsupp.single P c) Γ = _
      rw [Finsupp.single_apply]
    rw [h2]
    split_ifs <;> simp [add_assoc]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨by simpa using hB₀, by simpa using hC₀'⟩
    · simpa using hpb j
  · rw [Fin.sum_univ_castSucc, ha]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- On a smooth variety, adding `∑_{P ∈ s} c_P P` to the boundary lowers a log discrepancy by
`∑_{P ∈ s} c_P μ_P`, where `μ_P` is the coefficient of `E` in the pull-back of `P`. -/
private theorem isLogDiscrepancy_add_sum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) {n : ℕ} {B : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c μ : MMP.Mori.PrimeDivisor X → ℝ)
    (hμ : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∀ P ∈ s, ∀ P' : Divisor D.Y,
        (∃ hB, MMP.Mori.Divisor.IsPullback D.f (Finsupp.single P 1 : Divisor X) hB P') →
          (P'.coeff D.E : ℝ) = μ P) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + ∑ P ∈ s, Finsupp.single P (c P)) D
      (a - ∑ P ∈ s, c P * μ P) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert P s hP ih =>
    obtain ⟨P', hP', h'⟩ := isLogDiscrepancy_add_single hsm
      (ih fun Q hQ => hμ Q (Finset.mem_insert_of_mem hQ)) P (c P)
    rw [hμ P (Finset.mem_insert_self _ _) P' hP'] at h'
    have e1 : B + ∑ Q ∈ insert P s, Finsupp.single Q (c Q) =
        B + ∑ Q ∈ s, Finsupp.single Q (c Q) + Finsupp.single P (c P) := by
      rw [Finset.sum_insert hP]
      abel
    have e2 : a - ∑ Q ∈ insert P s, c Q * μ Q = a - ∑ Q ∈ s, c Q * μ Q - c P * μ P := by
      rw [Finset.sum_insert hP]
      ring
    rwa [e1, e2]

/-! ### Coefficients of the pull-back of a prime divisor with invertible ideal -/

/-- The pull-back of `P` has coefficient `0` along `E` when `f(η_E) ∉ P`. -/
private theorem coeff_isPullback_single_eq_zero {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉
        MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y)}
    {P' : Divisor X} (h : MMP.Mori.Divisor.IsPullback f (Finsupp.single P 1 : Divisor Y) hB P')
    (E : MMP.Mori.PrimeDivisor X) (hE : f E.genericPoint ∉ P.support) : P'.coeff E = 0 := by
  obtain ⟨N, hN, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P hP h E
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap,
    (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support P.idealSheaf _).2 hE,
    Ideal.map_top, MMP.Threefold.Resolution.idealOrder_top] at hN
  rw [hc]
  have : N = 0 := by exact_mod_cast hN.symm
  simp [this]

/-- If `z` generates the ideal of `P` at `x = f(η_E)` and `v_E(z) = exp (-m)`, the pull-back of
`P` has coefficient `m` along `E`. -/
private theorem coeff_isPullback_single_eq_of_stalk_eq_span {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : X ⟶ Y} [IsDominant f] (P : MMP.Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    {hB : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉
        MMP.Mori.DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y)}
    {P' : Divisor X} (h : MMP.Mori.Divisor.IsPullback f (Finsupp.single P 1 : Divisor Y) hB P')
    (E : MMP.Mori.PrimeDivisor X) {x : Y} (hx : f E.genericPoint = x) (z : Y.presheaf.stalk x)
    (hz : IdealSheafData.stalk P.idealSheaf x = Ideal.span {z}) (m : ℤ)
    (hm : E.valuationOver f (algebraMap _ Y.functionField z) = WithZero.exp (-m)) :
    P'.coeff E = m := by
  subst hx
  obtain ⟨N, hN, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P hP h E
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap, hz, Ideal.map_span,
    Set.image_singleton] at hN
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, functionFieldMap_algebraMap_stalk] at hm
  set g : E.localRing := (f.stalkMap E.genericPoint).hom z with hgdef
  have := E.isDiscreteValuationRing_localRing
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hm
    exact WithZero.exp_ne_zero hm.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨K, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  rw [hgu, MMP.Threefold.Resolution.idealOrder_span_unit_mul_pow hϖ u K] at hN
  have hu : E.divisorialValuation (algebraMap E.localRing X.functionField u) = 1 := by
    refine le_antisymm ((E.divisorialValuation_le_one_iff _).2 ⟨u, rfl⟩) (not_lt.1 fun hlt => ?_)
    exact (IsLocalRing.mem_maximalIdeal _).1
      ((E.divisorialValuation_algebraMap_lt_one_iff _).1 hlt) u.isUnit
  rw [hgu, map_mul, map_mul, hu, one_mul, map_pow, map_pow,
    E.divisorialValuation_algebraMap_of_irreducible hϖ, ← WithZero.exp_nsmul] at hm
  have hK : (K : ℤ) = m := by
    have := WithZero.exp_injective hm
    simp only [nsmul_eq_mul, mul_neg, mul_one, neg_inj] at this
    exact this
  have hKN : K = N := by exact_mod_cast hN
  rw [hc, ← hKN, hK]

/-! ### The dictionary between the two log discrepancies -/

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

/-- A discrepancy in the sense of *Flips and abundance* is a log discrepancy minus one, on every
proper model of the valuation. -/
public theorem isLogDiscrepancy_of_isDiscrepancy {n : ℕ} {K : Divisor X} {B : RDivisor X}
    {v : Valuation X.functionField ℤᵐ⁰} {a : ℝ} (h : MMP.Flips.IsDiscrepancy sX n K B v a)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) (hv : D.valuation = v) :
    MMP.Intersection.IsLogDiscrepancy sX n B D (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hE, rfl, hw⟩ := h
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1
    ⟨D, hD⟩
  have hab := hb.eq hw (hv.trans hE.symm)
  have := isLogDiscrepancy_of_isDiscrepancyWith hK hb
  rwa [hab] at this

/-- Every divisor with proper model has a log discrepancy once `K_X + B` is `ℝ`-Cartier. -/
public theorem exists_isLogDiscrepancy (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
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

/-! ### The log-smooth formula for a real boundary -/

section LogSmooth

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : AlgebraicGeometry.IsVariety ℂ (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

/-- If `T` is reduced and `B` is supported in `T`, then `B + ∑_{P ∈ T} (1 - b_P) P = T`. -/
private theorem add_sum_single_one_sub_coeff_eq_toRDivisor {W : Scheme.{0}} {T : Divisor W}
    {B : RDivisor W} (hT : MMP.Intersection.IsReducedEffective T)
    (hB : ∀ P, B.coeff P ≠ 0 → P ∈ T.support) :
    B + ∑ P ∈ T.support, Finsupp.single P (1 - B.coeff P) = Divisor.toRDivisor T := by
  classical
  refine Finsupp.ext fun P => ?_
  have e2 : (Divisor.toRDivisor T) P = (T P : ℝ) := rfl
  rw [Finsupp.add_apply, e2, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hPT
  · have hT1 : T P = 1 := (hT P).resolve_left (Finsupp.mem_support_iff.1 hPT)
    change B.coeff P + (1 - B.coeff P) = ((T P : ℤ) : ℝ)
    rw [hT1]; push_cast; ring
  · have hBP : B P = 0 := by
      by_contra h
      exact hPT (hB P h)
    rw [Finsupp.notMem_support_iff.1 hPT, hBP]
    simp

/-- **The log-smooth formula for a real boundary.** Let `π : Y ⟶ X` be a proper birational
morphism from a smooth variety, `T` a reduced snc divisor on `Y`, and `D_Y` the crepant boundary
of `(X, B)`, `K_Y + D_Y = π^*(K_X + B)`, supported in `T`. Let `D'` be a proper divisor over `Y`
realizing the valuation of a divisor `D` over `X` with log discrepancy `a`. Then, with
`J` the components of `T` through the centre of `D'` on `Y`,
`a = ∑_{j ∈ J} ξ(T_j) (1 - coeff_{T_j} D_Y) + e_T(ξ)`. -/
private theorem exists_isReducedSNCDiscrepancy_and_logDiscrepancy_eq_sum {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    {π : Y ⟶ X} [IsProper π] [LocallyOfFiniteType (π ≫ sX)] (hY : IsNormalVariety ℂ (π ≫ sX))
    (hπ : IsBirationalMorphism π) (hsm : IsSmoothScheme (π ≫ sX)) {T : Divisor Y}
    (hT : MMP.Intersection.IsReducedEffective T) (hsnc : T.IsSNC (π ≫ sX)) {DY : RDivisor Y}
    (hpb : haveI := hπ.isDominant
      MMP.Flips.IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + B)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DY))
    (hDT : ∀ P, DY.coeff P ≠ 0 → P ∈ T.support)
    (D : DivisorOver ℂ sX) {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    (D' : DivisorOver ℂ (π ≫ sX)) (hD' : IsProper D'.f)
    (hv : haveI := hπ.isDominant; D'.valuation.comap (functionFieldMap π) = D.valuation) :
    ∃ e : ℝ, IsReducedSNCDiscrepancy (π ≫ sX) T D'.valuation e ∧
      ∀ (z : sncIndexSet T (D'.center : Set Y) →
          Y.presheaf.stalk D'.center.isIrreducible.genericPoint)
        (m : sncIndexSet T (D'.center : Set Y) → ℤ),
        (∀ j, IdealSheafData.stalk j.1.idealSheaf D'.center.isIrreducible.genericPoint =
          Ideal.span {z j}) →
        (∀ j, D'.valuation (algebraMap _ Y.functionField (z j)) = WithZero.exp (-m j)) →
        a = ∑ j, (m j : ℝ) * (1 - DY.coeff j) + e := by
  classical
  haveI := hπ.isDominant
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : AlgebraicGeometry.IsVariety ℂ (π ≫ sX) := hY.1
  have hdimX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdimW : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX) hπ).symm.trans
      hdimX
  -- the crepant transfer
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω hK hY hπ hsm
  have hFX := isDiscrepancy_of_isLogDiscrepancy ha hω hK hKB
  rw [← hv] at hFX
  have hFY := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX hω hK hKB π hY hπ hpb hKY
    ⟨D', hD'⟩ (a - 1)).mp hFX
  have hLW := isLogDiscrepancy_of_isDiscrepancy hFY D' hD' rfl
  rw [show 1 + (a - 1) = a by ring] at hLW
  -- the coefficients of the pull-backs of the `Tⱼ` along `E`
  haveI := D'.isIntegral
  haveI := D'.isLocallyNoetherian
  haveI := D'.isNormal
  haveI := D'.isDominant
  haveI : CompactSpace D'.Y :=
    (D'.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  let μ : MMP.Mori.PrimeDivisor Y → ℝ := fun P =>
    ((Divisor.pullback (Finsupp.single P 1 : Divisor Y)
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _)).coeff D'.E : ℝ)
  have hμP : ∀ (P : MMP.Mori.PrimeDivisor Y) (P' : Divisor D'.Y),
      (∃ hB, MMP.Mori.Divisor.IsPullback D'.f (Finsupp.single P 1 : Divisor Y) hB P') →
        (P'.coeff D'.E : ℝ) = μ P := by
    rintro P P' ⟨hB, hP'⟩
    simp only [μ]
    rw [hP'.eq (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (Divisor.isPullback_pullback _ _)]
  -- shift the boundary from `D_Y` to `T`
  have hLT := isLogDiscrepancy_add_sum hsm hLW T.support (fun P => 1 - DY.coeff P) μ
    (fun P _ P' hP' => hμP P P' hP')
  rw [add_sum_single_one_sub_coeff_eq_toRDivisor hT hDT] at hLT
  -- the generic point of the centre
  have hgen : D'.center.isIrreducible.genericPoint = D'.f D'.E.genericPoint :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).eq
      (D'.center_eq_closure_genericPoint).symm
  have hηZ : ∀ E ∈ T.support, ¬ (D'.center : Set Y) ⊆ E.support →
      D'.center.isIrreducible.genericPoint ∉ E.support := by
    intro E _ hE hmem
    apply hE
    rw [← (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed)]
    refine closure_minimal (Set.singleton_subset_iff.2 hmem) ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    exact isClosed_closure
  set U := sncComplement T (D'.center : Set Y)
  have hηU : D'.center.isIrreducible.genericPoint ∈ U :=
    MMP.Fourfold.SNCWeight.mem_sncComplement_iff.2 hηZ
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hηmem : D'.center.isIrreducible.genericPoint ∈ (D'.center : Set Y) :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  -- localize the pair `(Y, T)` to `U`
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hsm hdimW
  have hPWT : IsPairWith (π ≫ sX) n KW (Divisor.toQDivisor T) :=
    ⟨hY, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨cT, hcT⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWT.isPair hKW D'
  have heT : a - ∑ j ∈ T.support, (1 - DY.coeff j) * μ j = 1 + (cT : ℝ) := by
    refine MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hcT ?_
    rw [QDivisor.toRDivisor_toQDivisor]
    exact hLT
  obtain ⟨hYU, hfU, E', hE', hvU, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPWT D' U ⟨_, hηmem, hηU⟩
  have hcU := (hiff cT).1 hcT
  have hpU : IsProper (D'.f ∣_ U) := by
    haveI : IsProper D'.f := hD'
    infer_instance
  have hLU := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcU hpU
  have hZ₀ : MMP.Intersection.IsCentre ℂ (π ≫ sX) D'.valuation D'.center :=
    ⟨D', hD', rfl, rfl⟩
  refine ⟨1 + (cT : ℝ), ⟨hY.1, hsm, hT, hsnc, D'.center, hZ₀, ⟨⟨_, hηU⟩⟩,
    n, ⟨_, D'.f ∣_ U, hYU, hfU, E'⟩, hpU, hvU, ?_⟩, ?_⟩
  · rw [← toRDivisor_restrictOpen_sncComplement hT]
    exact hLU
  · intro z m hz hm
    have hμm : ∀ j : sncIndexSet T (D'.center : Set Y), μ j = (m j : ℝ) := by
      intro j
      have hc := coeff_isPullback_single_eq_of_stalk_eq_span (j : MMP.Mori.PrimeDivisor Y)
        (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (π ≫ sX) hsm j)
        (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _))
        D'.E hgen.symm (z j) (hz j) (m j) (hm j)
      simp only [μ]
      exact_mod_cast hc
    have hμ0 : ∀ j ∈ T.support, j ∉ sncIndexSet T (D'.center : Set Y) →
        (1 - DY.coeff j) * μ j = 0 := by
      intro j hjT hjJ
      have hZj : ¬ (D'.center : Set Y) ⊆ j.support := fun h => hjJ (Finset.mem_filter.2 ⟨hjT, h⟩)
      have hc := coeff_isPullback_single_eq_zero j
        (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (π ≫ sX) hsm j)
        (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D'.f _))
        D'.E (by rw [← hgen]; exact hηZ j hjT hZj)
      simp only [μ]
      rw [hc]
      simp
    have hsum : ∑ j ∈ T.support, (1 - DY.coeff j) * μ j =
        ∑ j : sncIndexSet T (D'.center : Set Y), (m j : ℝ) * (1 - DY.coeff j) := by
      have h2 : ∑ j ∈ sncIndexSet T (D'.center : Set Y), (1 - DY.coeff j) * μ j =
          ∑ j : sncIndexSet T (D'.center : Set Y), (m j : ℝ) * (1 - DY.coeff j) := by
        rw [← Finset.sum_coe_sort (sncIndexSet T (D'.center : Set Y))]
        exact Finset.sum_congr rfl fun j _ => by rw [hμm j, mul_comm]
      rw [← h2]
      exact (Finset.sum_subset (Finset.filter_subset _ _) hμ0).symm
    rw [← hsum]
    linarith

end LogSmooth

/-! ### Exceptional and non-exceptional divisors -/

section Exceptional

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- A non-exceptional divisor over a normal variety has the valuation of a prime divisor. -/
public theorem exists_valuation_eq_of_not_isExceptional (hX : IsNormalVariety ℂ sX)
    {D : DivisorOver ℂ sX} (hD : ¬ D.IsExceptional) :
    ∃ Q : MMP.Mori.PrimeDivisor X, D.valuation = (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation := by
  rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX,
    ← MMP.Positivity.DivisorOver.codimension_center,
    MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hD
  push Not at hD
  exact hD

/-- The valuation of the divisor `(X, 𝟙, Q)` over `X` is `ord_Q`. -/
private theorem valuation_ofPrimeDivisor (hX : IsNormalVariety ℂ sX)
    (Q : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation = Q.divisorialValuation :=
  Valuation.ext fun φ => by
    change Q.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]

variable [CompactSpace X] [LocallyOfFiniteType sX]

/-- The log discrepancy of a prime divisor `Q` of `X` is `1 - coeff_Q B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {B : RDivisor X} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
      (1 - B.coeff Q) := by
  have h := MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω hK hKB Q
  have := isLogDiscrepancy_of_isDiscrepancy h (DivisorOver.ofPrimeDivisor ℂ hX Q)
    (inferInstanceAs (IsProper (𝟙 X))) (valuation_ofPrimeDivisor hX Q)
  rwa [← sub_eq_add_neg] at this

end Exceptional

/-! ### Forms, boundaries and prime divisors of smooth models -/

/-- A canonical divisor of a normal complex variety is the divisor of a nonzero rational top
form. -/
public theorem exists_divisorOfForm_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  exact ⟨ω, hω0, DivisorWithCoeffs.ext' hωK⟩

/-- The boundary of a real canonical pair is effective. -/
private theorem coeff_nonneg_of_isRealCanonicalPair {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)} {BW : RDivisor W}
    (h : IsRealCanonicalPair sW BW) (P : MMP.Mori.PrimeDivisor W) : 0 ≤ BW.coeff P := by
  by_cases hP : BW.coeff P = 0
  · exact hP.ge
  · exact (h.2.1 P hP).1.le

section PrimeDiscrepancy

open MMP.Flips

/-- **Discrepancies of the prime divisors of a smooth model.** If `π : W ⟶ X` is a smooth
birational model and `div(π^*ω) + D_W = π^*(div ω + B)`, then every prime divisor `P` of `W` has
discrepancy `a(ord_P, X, B) = -coeff_P D_W`. -/
private theorem isDiscrepancy_primeDivisor_of_isRCartierPullback {X W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hKω : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {π : W ⟶ X} [IsProper π]
    [LocallyOfFiniteType (π ≫ sX)] (hW : IsNormalVariety ℂ (π ≫ sX)) (hπ : IsBirationalMorphism π)
    (hsm : IsSmoothScheme (π ≫ sX)) {DW : RDivisor W}
    (hpb : haveI := hπ.isDominant
      IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + B)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW))
    (P : MMP.Mori.PrimeDivisor W) :
    IsDiscrepancy sX n (divisorOfForm ω) B (⟨W, π, hW, hπ, P⟩ : DivisorOver ℂ sX).valuation
      (-DW.coeff P) := by
  haveI := hπ.isDominant
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω0 hKω hW hπ hsm
  have hKDY : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW) := by
    obtain ⟨m, r, L₀, L, hLc, -, hL, heq⟩ := hpb
    exact ⟨m, r, L, fun j => (hL j).2.isCartier (hLc j), by
      rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  let ER : MMP.Flips.ProperDivisorOver ℂ (π ≫ sX) :=
    ⟨DivisorOver.ofPrimeDivisor ℂ hW P, (inferInstance : IsProper (𝟙 W))⟩
  have hER : ER.valuation = P.divisorialValuation := valuation_ofPrimeDivisor hW P
  have h1 := isDiscrepancy_divisorialValuation hW _
    (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' π
      hπ.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hKω.topologicalKrullDim_eq) hω0)
    hKY hKDY P
  rw [← hER] at h1
  have h2 := (isDiscrepancy_comap_functionFieldMap_iff hX hω0 hKω hKB π hW hπ hpb hKY ER _).mpr h1
  rwa [hER] at h2

end PrimeDiscrepancy

/-! ### Finiteness of the small exceptional log discrepancies -/

section Finite

/-- **A centre off the exceptional locus has the same codimension downstairs.** Let `π : W ⟶ X`
be dominant, `D'` a divisor over `W` whose centre has generic point outside `Ex(π)`, and `D₀` a
divisor over `X` with `π_* v_{D'} = v_{D₀}`. Then `π` is a local isomorphism at the generic point
of the centre of `D'`, which maps to that of `D₀`, so the two centres have the same
codimension. -/
private theorem codimension_center_eq_of_notMem_exceptionalSet {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral W] [IsSeparated sX]
    {π : W ⟶ X} [IsDominant π] (D' : DivisorOver k (π ≫ sX)) (D₀ : DivisorOver k sX)
    (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation)
    (hη : D'.f D'.E.genericPoint ∉ (exceptionalSet π : Set W)) :
    codimension D₀.center = codimension D'.center := by
  open MMP.Positivity.DivisorOver in
  have hx₀ : π (D'.f D'.E.genericPoint) = D₀.f D₀.E.genericPoint := by
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
  rw [MMP.Positivity.DivisorOver.codimension_center, MMP.Positivity.DivisorOver.codimension_center,
    ← hx₀]
  exact MMP.Positivity.coheight_map_of_mem_biregularLocus π
    (by_contra fun h => hη (MMP.Mori.mem_exceptionalSet.2 h))

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

/-- The maximal coefficient of a boundary with all coefficients below one is below one. -/
private theorem realThresholdMax_lt_one {X : Scheme.{0}} {B : RDivisor X}
    (hB : ∀ P, B.coeff P ≠ 0 → 0 < B.coeff P ∧ B.coeff P < 1) : realThresholdMax B < 1 := by
  classical
  obtain h | h := Finset.mem_insert.mp (Finset.max'_mem (insert 0 (B.support.image B.coeff))
    (Finset.insert_nonempty _ _))
  · rw [realThresholdMax, h]; exact one_pos
  · obtain ⟨P, hP, hPe⟩ := Finset.mem_image.mp h
    rw [realThresholdMax, ← hPe]
    exact (hB P (Finsupp.mem_support_iff.mp hP)).2

/-- Every coefficient of `B` is at most the maximal coefficient `d`. -/
private theorem coeff_le_realThresholdMax {X : Scheme.{0}} (B : RDivisor X)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ realThresholdMax B := by
  by_cases hP : P ∈ B.support
  · exact le_realThresholdMax_of_mem_support B hP
  · rw [show B.coeff P = 0 from Finsupp.notMem_support_iff.mp hP]
    exact zero_le_realThresholdMax B

/-- **Finitely many exceptional valuations below the maximal-boundary cutoff.** For a real
canonical pair `(X, B)` with maximal coefficient `d`, only finitely many exceptional divisorial
valuations with centre on `X` have log discrepancy `< u` when `u ≤ 2 - d`. -/
private theorem finite_logDiscrepancyLtSet {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (sW : W ⟶ Spec (.of ℂ)) (BW : RDivisor W)
    (h : IsRealCanonicalPair sW BW) {u : ℝ} (hu : u ≤ 2 - realThresholdMax BW) :
    (logDiscrepancyLtSet sW BW u).Finite := by
  classical
  obtain ⟨hX, hcoef, ⟨n, K, hK, hKB⟩, hcan⟩ := h
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hX.1
  haveI : LocallyOfFiniteType sW := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace W := (hX.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : IsSeparated sW := hX.1.toIsSeparated
  set d := realThresholdMax BW with hd
  have hd1 : d < 1 := realThresholdMax_lt_one hcoef
  have hd0 : 0 ≤ d := zero_le_realThresholdMax BW
  have hcd : ∀ Q, BW.coeff Q ≤ d := coeff_le_realThresholdMax BW
  -- a rational top form with divisor `K`
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hX hK
  have hK' : (divisorOfForm ω).IsCanonicalDivisor sW n := hdiv ▸ hK
  have hKB' : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + BW) := by
    obtain ⟨m, r, C, hC, hc⟩ := hKB
    refine ⟨m, r, C, hC, DivisorWithCoeffs.ext' fun Γ => ?_⟩
    have h1 := hc Γ
    rw [hdiv]
    simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor]
    exact h1
  -- a log resolution of `(X, Supp B)`
  obtain ⟨Y, π, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sW hX BW.support
  haveI : IsProper π := hres.isProjective.isProper
  have hπb := hres.isBirationalMorphism
  have hfres : IsSmoothResolution sW π := ⟨inferInstance, hπb, hres.isSmoothScheme⟩
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sW) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sW)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : AlgebraicGeometry.IsVariety ℂ (π ≫ sW) := hY.1
  haveI := hπb.isDominant
  obtain ⟨S, hsncS, hU⟩ :=
    exists_finset_isSNC_of_isSNCClosedSubset (π ≫ sW) hres.isSmoothScheme hS
  set T : Divisor Y := ∑ E ∈ S, Finsupp.single E (1 : ℤ) with hTdef
  have hsupp : T.support = S := by ext G; exact mem_support_sum_single S G
  have hTred : MMP.Intersection.IsReducedEffective T := fun P => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    by_cases hP : P ∈ S <;> simp [Finsupp.single_apply, hP]
  have hmem : ∀ G : MMP.Mori.PrimeDivisor Y,
      G.genericPoint ∈ (⋃ F ∈ S, (F.support : Set Y)) → G ∈ S := fun G hG => by
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  -- the crepant boundary `D_Y`
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback π hKB'
  set DY : RDivisor Y :=
    G - Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sW π ω)) with hDYdef
  have hpb : MMP.Flips.IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + BW)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sW π ω)) + DY) := by
    rw [hDYdef, add_sub_cancel]; exact hG
  -- the log discrepancies of the prime divisors of `Y`
  let DP : MMP.Mori.PrimeDivisor Y → DivisorOver ℂ sW := fun P => ⟨Y, π, hY, hπb, P⟩
  have hDP : ∀ P, MMP.Intersection.IsLogDiscrepancy sW n BW (DP P) (1 - DY.coeff P) := fun P => by
    have h := isLogDiscrepancy_of_isDiscrepancy (isDiscrepancy_primeDivisor_of_isRCartierPullback hX
      hω0 hK' hKB' hY hπb hres.isSmoothScheme hpb P) (DP P) (inferInstanceAs (IsProper π)) rfl
    rwa [← sub_eq_add_neg] at h
  have hge : ∀ P, 1 - d ≤ 1 - DY.coeff P := by
    intro P
    by_cases hEx : (DP P).IsExceptional
    · have := hcan n (DP P) _ hEx (hDP P)
      linarith [zero_le_realThresholdMax BW]
    · obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hX hEx
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq (hDP P)
        (isLogDiscrepancy_ofPrimeDivisor hX hω0 hK' hKB' Q) hQ
      rw [this]
      linarith [hcd Q]
  have hDT : ∀ P, DY.coeff P ≠ 0 → P ∈ T.support := by
    intro P hP
    rw [hsupp]
    by_contra hPS
    have hηU : P.genericPoint ∉ (⋃ F ∈ S, (F.support : Set Y)) := fun h => hPS (hmem P h)
    rw [hU] at hηU
    have hηE : P.genericPoint ∉ (MMP.Mori.exceptionalSet π : Set Y) := fun h => hηU (Or.inl h)
    have hηB : π P.genericPoint ∉
        (BW.support.sup fun E => (E.idealSheaf.support : Set W)) :=
      fun h => hηU (Or.inr h)
    have hbir : π P.genericPoint ∈ biregularLocus π := by
      by_contra h
      exact hηE (MMP.Mori.mem_exceptionalSet.mpr h)
    have hco : Order.coheight (π P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus π hbir]
      exact P.coheight_genericPoint
    have hEx : ¬ (DP P).IsExceptional := by
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX]
      change ¬ 2 ≤ Order.coheight (π P.genericPoint)
      rw [hco]
      decide
    obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hX hEx
    have hπQ : π P.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hQ
    have hQ0 : BW.coeff Q = 0 := by
      by_contra hQ0
      apply hηB
      rw [hπQ, Finset.sup_set_eq_biUnion]
      exact Set.mem_iUnion₂.2 ⟨Q, Finsupp.mem_support_iff.mpr hQ0,
        MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq (hDP P)
      (isLogDiscrepancy_ofPrimeDivisor hX hω0 hK' hKB' Q) hQ
    rw [hQ0] at this
    exact hP (by linarith)
  have hd1' : 0 < 1 - d := by linarith
  set M : ℕ := ⌈2 / (1 - d)⌉₊ + 1 with hM
  refine ((finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sW) T (M := M)
    (Nat.le_add_left 1 _)).image fun ξ => ξ.comap (functionFieldMap π)).subset ?_
  rintro v ⟨n', D, a, hDex, rfl, ha, hau⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  have hDp : IsProper D.f := ha.2.1
  obtain ⟨D₁, hD₁, -⟩ :=
    MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hX.1 π hY.1 hπb
    ⟨D, hDp⟩
  refine ⟨D₁.valuation, ?_, hD₁⟩
  obtain ⟨e, heT, hform⟩ := exists_isReducedSNCDiscrepancy_and_logDiscrepancy_eq_sum hX hω0 hK'
    hKB' hY hπb hres.isSmoothScheme hTred hsncS hpb hDT D ha D₁.toDivisorOver D₁.isProper hD₁
  set D' := D₁.toDivisorOver with hD'def
  have hlt : a < 2 - d := lt_of_lt_of_le hau hu
  set η := D'.center.isIrreducible.genericPoint
  have hgen : η = D'.f D'.E.genericPoint :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).eq
      (D'.center_eq_closure_genericPoint).symm
  have hηj : ∀ j : sncIndexSet T (D'.center : Set Y), η ∈ (j.1.support : Set Y) := fun j =>
    (Finset.mem_filter.1 j.2).2
      (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  choose z hzp hz using fun j : sncIndexSet T (D'.center : Set Y) =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sW) hres.isSmoothScheme j.1 (hηj j)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D' hgen (hzp j).ne_zero
    ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  have hform' := hform z m hz hm
  obtain ⟨e0, rfl⟩ := heT.exists_eq_natCast
  have hZ₀ : MMP.Intersection.IsCentre ℂ (π ≫ sW) D₁.valuation D'.center :=
    ⟨D', D₁.isProper, rfl, rfl⟩
  have hterm : ∀ j : sncIndexSet T (D'.center : Set Y),
      (1 - d) * (m j : ℝ) ≤ (m j : ℝ) * (1 - DY.coeff j) := fun j => by
    have h1 : (1 : ℝ) ≤ m j := by exact_mod_cast hm1 j
    nlinarith [hge j]
  have hsum_ge : ∀ j : sncIndexSet T (D'.center : Set Y),
      (1 - d) * (m j : ℝ) ≤ ∑ i, (m i : ℝ) * (1 - DY.coeff i) := fun j =>
    (hterm j).trans (Finset.single_le_sum (f := fun i => (m i : ℝ) * (1 - DY.coeff i))
      (fun i _ => le_trans (mul_nonneg hd1'.le (by exact_mod_cast (zero_le_one.trans (hm1 i))))
        (hterm i)) (Finset.mem_univ j))
  by_cases hJ : (sncIndexSet T (D'.center : Set Y)).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hJ
    have he0 : e0 = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ e0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have h2 := hsum_ge ⟨j₀, hj₀⟩
      have h3 : (1 : ℝ) ≤ m ⟨j₀, hj₀⟩ := by exact_mod_cast hm1 _
      nlinarith
    subst he0
    refine ⟨by exact_mod_cast heT, fun Z' hZ' j hj z' hz' => ?_⟩
    obtain rfl : Z' = D'.center := by
      obtain ⟨D'', -, hξD'', rfl⟩ := hZ'
      exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hY.1 hξD''.symm
    have hval : D₁.valuation (algebraMap _ Y.functionField z') =
        WithZero.exp (-m ⟨j, hj⟩) := by
      obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz'.symm.trans (hz ⟨j, hj⟩))
      rw [← hm, ← hw, map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
        _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' η hgen) w, mul_one]
    rw [hval, WithZero.exp_le_exp, neg_le_neg_iff]
    have h1 := hsum_ge ⟨j, hj⟩
    have h2 : (1 - d) * (m ⟨j, hj⟩ : ℝ) < 2 := by push_cast at hform'; linarith
    have h3 : (m ⟨j, hj⟩ : ℝ) < 2 / (1 - d) := by
      rw [lt_div_iff₀ hd1']; linarith
    have h4 := Nat.le_ceil (2 / (1 - d))
    have h5 : (m ⟨j, hj⟩ : ℝ) ≤ M := by rw [hM]; push_cast; linarith
    exact_mod_cast h5
  · exfalso
    haveI : IsEmpty (sncIndexSet T (D'.center : Set Y)) := ⟨fun j => hJ ⟨j.1, j.2⟩⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hform'
    have hdimW := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (π ≫ sW)
        hπb).symm.trans hK.topologicalKrullDim_eq
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (show codimension D'.center ≠ ⊤ by
      intro htop
      have h1 : ((Order.coheight D'.center : ℕ∞) : WithBot ℕ∞) ≤
          Order.krullDim (IrreducibleCloseds Y) := Order.coheight_le_krullDim _
      rw [← codimension_eq_coheight, htop] at h1
      change _ ≤ topologicalKrullDim Y at h1
      rw [hdimW] at h1
      norm_cast at h1)
    have hce := heT.sub_card_sncIndexSet_le hZ₀ hc.symm
    rw [Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hJ)] at hce
    have hηex : η ∉ (MMP.Mori.exceptionalSet π : Set Y) := fun hex => by
      have hηU : η ∈ (⋃ F ∈ S, (F.support : Set Y)) := by rw [hU]; exact Or.inl hex
      obtain ⟨E, hE, hηE⟩ := Set.mem_iUnion₂.1 hηU
      refine hJ ⟨E, Finset.mem_filter.2 ⟨hsupp ▸ hE, ?_⟩⟩
      rw [← (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed)]
      refine closure_minimal (Set.singleton_subset_iff.2 hηE) ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
      exact isClosed_closure
    have hcod : 2 ≤ codimension D.center := by
      rw [MMP.Positivity.DivisorOver.codimension_center]
      exact (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hDex
    rw [codimension_center_eq_of_notMem_exceptionalSet D' D hD₁ (hgen ▸ hηex), ← hc] at hcod
    have : 2 ≤ c := by exact_mod_cast hcod
    have : (2 : ℝ) ≤ c := by exact_mod_cast this
    push_cast at hce hform'
    linarith

end Finite

/-! ### Small contractions -/

section Small

variable {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **A small contraction is an isomorphism off codimension two.** For a small birational
contraction `f : X ⟶ Z` there are closed subsets `V ⊆ X` and `W ⊆ Z` of points of coheight at
least two, with `X ∖ V ⊆ f⁻¹(Z ∖ W)`, such that `f` is an isomorphism over `Z ∖ W`: the section of
the separated `f⁻¹(Z ∖ W) ⟶ Z ∖ W` given by `X ∖ V` is a closed immersion, so `X ∖ V` is
open and closed in the irreducible `f⁻¹(Z ∖ W)`. -/
private theorem exists_closeds_isIso_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  -- `X ∖ V` is nonempty: it contains the generic point
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

variable [IsLocallyNoetherian X] [IsNormal X]

/-- Points of coheight at most one of the base lie in the biregular locus of a small
contraction. -/
private theorem mem_biregularLocus_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

/-- A small contraction maps the generic point of a prime divisor to a point of coheight one,
in its biregular locus. -/
private theorem coheight_map_genericPoint_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 ∧ f P.genericPoint ∈ biregularLocus f := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hb : f P.genericPoint ∈ biregularLocus f := le_biregularLocus hiso (h hPV)
  exact ⟨by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    P.coheight_genericPoint], hb⟩

/-- Two prime divisors with the same image under a small contraction coincide. -/
private theorem primeDivisor_eq_of_map_eq_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) {P Q : MMP.Mori.PrimeDivisor X}
    (hPQ : f P.genericPoint = f Q.genericPoint) : P = Q := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hQV : Q.genericPoint ∈ (V.compl : Set X) := fun hQ =>
    absurd (hV _ hQ) (by rw [Q.coheight_genericPoint]; decide)
  have key : ∀ p : (f ⁻¹ᵁ W.compl).toScheme,
      Scheme.Opens.ι (X := Z) W.compl ((f ∣_ W.compl) p) = f ((f ⁻¹ᵁ W.compl).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hinj := (ConcreteCategory.bijective_of_isIso (f ∣_ W.compl).base).1
  let p : (f ⁻¹ᵁ W.compl).toScheme := ⟨P.genericPoint, h hPV⟩
  let q : (f ⁻¹ᵁ W.compl).toScheme := ⟨Q.genericPoint, h hQV⟩
  have heq : (f ∣_ W.compl) p = (f ∣_ W.compl) q :=
    (Scheme.Opens.ι (X := Z) W.compl).isOpenEmbedding.injective (by rw [key p, key q]; exact hPQ)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (congrArg Subtype.val (hinj heq))

end Small

section SmallPair

variable {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- Every prime divisor of `X` corresponds, through `Z`, to a prime divisor of `X⁺`. -/
private theorem exists_primeDivisor_map_eq_of_isSmall {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hb := mem_biregularLocus_of_isSmall hfp hz.le
  obtain ⟨x', hx'⟩ :=
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

/-- The strict transform `(f⁺)⁻¹_* f_* D` across two small contractions has, at the prime divisor
`P⁺` corresponding to `P`, the coefficient of `D` at `P`. -/
private theorem flipTransform_apply_of_isSmall [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper f := hf.isProper
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall hfp (hQ ▸ hz).le) D

end SmallPair

/-! ### The threshold set across a flip -/

section Threshold

/-- `d` and `S(B)` depend only on the coefficients along the support. -/
private theorem realThresholdSet_eq_of_bijOn {X X' : Scheme.{0}} {B : RDivisor X}
    {B' : RDivisor X'} (e : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor X')
    (he : Set.BijOn e B.support B'.support) (hc : ∀ P ∈ B.support, B'.coeff (e P) = B.coeff P) :
    realThresholdMax B' = realThresholdMax B ∧ realThresholdSet B' = realThresholdSet B := by
  classical
  have himg : B'.support.image B'.coeff = B.support.image B.coeff := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨P', hP', rfl⟩
      obtain ⟨P, hP, rfl⟩ := he.surjOn hP'
      exact ⟨P, hP, (hc P hP).symm⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨e P, he.mapsTo hP, hc P hP⟩
  have hmax : realThresholdMax B' = realThresholdMax B := by
    simp only [realThresholdMax, himg]
  refine ⟨hmax, ?_⟩
  have hsum : ∀ n : MMP.Mori.PrimeDivisor X' → ℕ,
      ∑ P' ∈ B'.support, (n P' : ℝ) * B'.coeff P' =
        ∑ P ∈ B.support, (n (e P) : ℝ) * B.coeff P := fun n =>
    (Finset.sum_nbij e (fun P hP => he.mapsTo hP) he.injOn he.surjOn fun P hP => by
      rw [hc P hP]).symm
  ext t
  simp only [realThresholdSet, Set.mem_setOf_eq, hmax]
  constructor
  · rintro ⟨⟨n, rfl⟩, h1, h2⟩
    exact ⟨⟨fun P => n (e P), hsum n⟩, h1, h2⟩
  · rintro ⟨⟨n, rfl⟩, h1, h2⟩
    let n' : MMP.Mori.PrimeDivisor X' → ℕ := fun P' => ∑ P ∈ B.support with e P = P', n P
    have hn : ∑ P ∈ B.support, (n P : ℝ) * B.coeff P =
        ∑ P' ∈ B'.support, (n' P' : ℝ) * B'.coeff P' := by
      simp only [n', Nat.cast_sum, Finset.sum_mul]
      rw [← Finset.sum_fiberwise_of_maps_to (g := e) (t := B'.support)
        (fun P hP => he.mapsTo hP) (fun P => (n P : ℝ) * B.coeff P)]
      refine Finset.sum_congr rfl fun P' _ => Finset.sum_congr rfl fun P hP => ?_
      obtain ⟨hP', rfl⟩ := Finset.mem_filter.mp hP
      rw [hc P hP']
    exact ⟨⟨n', hn⟩, hn ▸ h1, hn ▸ h2⟩

/-- **The threshold set is invariant under a flip.** Small contractions identify the prime
divisors on the two sides with the same coefficients, so `d` and `S(B)` do not change. -/
private theorem realThresholdSet_flipTransform {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) (B : RDivisor X) :
    realThresholdMax (flipTransform f fp B) = realThresholdMax B ∧
      realThresholdSet (flipTransform f fp B) = realThresholdSet B := by
  classical
  choose e he using exists_primeDivisor_map_eq_of_isSmall hf hfp
  have hc : ∀ P, (flipTransform f fp B).coeff (e P) = B.coeff P := fun P => by
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hf hfp hfb (he P) B
  refine realThresholdSet_eq_of_bijOn e ⟨fun P hP => ?_, fun P _ Q _ hPQ => ?_, fun P' hP' => ?_⟩
    fun P _ => hc P
  · simp only [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hP ⊢
    rwa [hc P]
  · exact primeDivisor_eq_of_map_eq_of_isSmall hf ((he P).symm.trans (hPQ ▸ he Q))
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfp hf P'
    have hcP : (flipTransform f fp B).coeff P' = B.coeff P := by
      simp only [DivisorWithCoeffs.coeff_apply]
      exact flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm B
    refine ⟨P, ?_, primeDivisor_eq_of_map_eq_of_isSmall hfp ((he P).trans hP)⟩
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hP' ⊢
    rwa [← hcP]

end Threshold

/-! ### Finiteness of the difficulty -/

/-- **The difficulty of a real canonical pair is finite.** -/
private theorem realCanonicalDifficulty_ne_top {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (sW : W ⟶ Spec (.of ℂ)) (BW : RDivisor W)
    (h : IsRealCanonicalPair sW BW) : realCanonicalDifficulty sW BW ≠ ⊤ := by
  have hS := realThresholdSet_finite BW (coeff_nonneg_of_isRealCanonicalPair h)
  rw [realCanonicalDifficulty, Set.encard_ne_top_iff]
  refine hS.biUnion fun s hs => ?_
  exact (Set.finite_singleton s).prod
    (finite_logDiscrepancyLtSet sW BW h (by linarith [hs.2.1]))

/-! ### Intersection numbers and nefness of pull-backs -/

section NegHelpers

open MMP MMP.Flips

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}}
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
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν
    ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
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
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
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
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
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
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

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
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **Projection formula** for an `ℝ`-combination `D = ∑ r_j L_j` of Cartier divisors:
`h^*D · C' = [k(C') : k(C)] · (D · C)` when `h` maps the proper curve `C'` onto `C`. -/
private theorem sum_degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier)
    (hB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (L j).supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    ∑ j, r j * (((L j).pullback (hL j) (hB j)).degreeOn k (h ≫ sY) C'.ι C'.dim_le
        ((hL j).isCartier_pullback h (hB j)) : ℝ) =
      (residueFieldDegree h C'.point : ℝ) *
        ∑ j, r j * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) := by
  simp only [degreeOn_pullback_eq_mul h (hL _) (hB _) C' C hC, Int.cast_mul, Int.cast_natCast,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
/-- **Pulling back a divisor nonpositive on contracted curves.** Let `h : Y' ⟶ Y` be proper and
`B = ∑ s_j N_j` a combination of Cartier divisors with `B · C ≤ 0` on every curve contracted by
`f : Y ⟶ X`. Then `-h^*B = -∑ s_j h^*N_j` is `(h ≫ f)`-nef: by the projection formula a curve
`C'` contracted by `h ≫ f` has `h^*B · C' = [k(C') : k(h C')] (B · h C')` if `h(C')` is a curve,
which is then contracted by `f`, and `h^*B · C' = 0` if `h(C')` is a point. -/
private theorem isRelativelyNef_neg_sum_pullback {k : Type u} [Field k] {X Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [IsProper h] [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ X) {m : ℕ} (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hNB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp)
    (hBC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0) :
    IsRelativelyNef k (h ≫ sY) (h ≫ f)
      (-∑ j, s j • Divisor.toRDivisor ((N j).pullback (hN j) (hNB j))) := by
  have hN'c : ∀ j, ((N j).pullback (hN j) (hNB j)).IsCartier := fun j =>
    (hN j).isCartier_pullback h (hNB j)
  refine ⟨m, fun j => -s j, _, hN'c, by simp [← Finset.sum_neg_distrib], fun C' hC' x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (h ≫ sY) C' (fun j => -s j) _ hN'c
  rw [(IsRIntersectionNumber.eq_and_linear k (h ≫ sY) C').1 _ _ _ _ _ _ _ hx
    (by simpa [← Finset.sum_neg_distrib] using hx0)]
  by_cases hc : IsProperCurve sY (h C'.point)
  · -- `h(C')` is a curve `C`, contracted by `f`
    let C : ProperCurve sY := ⟨_, hc⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      have hsub : closure ({h C'.point} : Set Y) ⊆ h '' closure ({C'.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    simp only [degreeOn_pullback_eq_mul h (hN _) (hNB _) C' C rfl, Int.cast_mul, Int.cast_natCast,
      Finset.sum_neg_distrib, mul_left_comm (s _), ← Finset.mul_sum, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hBC C hCf)
  · -- `h(C')` is a point
    simp [degreeOn_pullback_eq_zero h (hN _) (hNB _) C' hc]

/-- The intersection number of `-D` is the negative of that of `D`, for the negated
presentation. -/
private theorem isRIntersectionNumber_neg {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {C : ProperCurve sX}
    {x : ℝ} (h : IsRIntersectionNumber k sX D r L C x) :
    IsRIntersectionNumber k sX (-D) (fun j => -r j) L C (-x) := by
  obtain ⟨hL, d, hD, hd, hx⟩ := h
  refine ⟨hL, d, ?_, hd, ?_⟩
  · rw [hD, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  · rw [hx, ← Finset.sum_neg_distrib]
    simp [neg_mul]

/-- If `-D` is `f`-nef, then `D · C ≤ 0` for every curve `C` contracted by `f`. -/
private theorem nonpos_of_isRelativelyNef_neg {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    {D : RDivisor X} (hnef : IsRelativelyNef k sX f (-D)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX D r L C x) : x ≤ 0 := by
  obtain ⟨m', r', L', hL', hpres, hall⟩ := hnef
  have hy := isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hpres] at hy
  have := (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _
    (isRIntersectionNumber_neg hx) hy
  linarith [hall C hC _ hy]

/-- A prime divisor `F` of `Y` is exceptional over the normal variety `X` exactly when its image
`g(η_F)` has coheight at least two. -/
private theorem isExceptionalPrimeDivisor_iff_two_le_coheight {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX g F ↔ 2 ≤ Order.coheight (g F.genericPoint) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  constructor
  · rintro ⟨_, _, _, hexc⟩
    unfold ProperDivisorOver.IsExceptional at hexc
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn] at hexc
    exact (withBot_add_two_le_iff hd).mp hexc
  · intro h2
    refine ⟨hY, hg, ‹_›, ?_⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn]
    exact (withBot_add_two_le_iff hd).mpr h2

end NegHelpers

/-! ### Common models -/

section CommonModel

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y`, the birational map
`φ = f'⁻¹ ∘ f : X ⇢ X'` satisfies `f' ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', φ.IsBirational ∧ φ.compHom f' = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hf'
  set e := e₁.trans e₂.symm
  have h : e.IsOver f f' := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

section Comp

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{0}} (f : Y ⟶ X) [IsProper f]
  (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The divisor `(Y', f ∘ g, E)` over `X` of a divisor `(Y', g, E)` over `Y`. -/
private def compDivisorOver (E : ProperDivisorOver k (f ≫ sX)) :
    ProperDivisorOver k sX where
  Y := E.Y
  f := E.f ≫ f
  isNormalVariety := by
    have h := E.isNormalVariety
    rwa [← Category.assoc] at h
  isBirationalMorphism := by
    haveI := E.isIntegral
    haveI := E.isProper
    exact MMP.Mori.isBirationalMorphism_comp_of_isBirational f E.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism E.isBirationalMorphism)
  E := E.E
  isProper := by
    haveI := E.isProper
    infer_instance

/-- The valuation of the composite divisor over `X` is `ord_E ∘ f^*`. -/
private theorem compDivisorOver_valuation (E : ProperDivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext a
  change E.E.divisorialValuation _ = E.E.divisorialValuation _
  congr 1
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply E.f f a).symm

end Comp

end CommonModel

/-! ### Forms on birational models -/

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

/-! ### Changing the structure morphism -/

section Structure

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {s₁ s₂ : Y ⟶ Spec (.of ℂ)}

private theorem exists_form_divisorOfForm_eq [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (h : s₁ = s₂) {n : ℕ} (τ : RationalPluriForms s₁ n 1) (hτ : τ ≠ 0) :
    ∃ τ' : RationalPluriForms s₂ n 1, τ' ≠ 0 ∧ divisorOfForm τ' = divisorOfForm τ := by
  subst h; exact ⟨τ, hτ, rfl⟩

private theorem isDiscrepancy_of_eq_structure [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (h : s₁ = s₂) {n : ℕ} {K : Divisor Y} {D : RDivisor Y} {v : Valuation Y.functionField ℤᵐ⁰}
    {a : ℝ} (hd : MMP.Flips.IsDiscrepancy s₁ n K D v a) : MMP.Flips.IsDiscrepancy s₂ n K D v a := by
  subst h; exact hd

private theorem isRelativelyNef_of_eq_structure {S : Scheme.{0}} [QuasiCompact s₁]
    [QuasiCompact s₂] (h : s₁ = s₂) {g : Y ⟶ S} {D : RDivisor Y}
    (hd : MMP.Flips.IsRelativelyNef ℂ s₁ g D) : MMP.Flips.IsRelativelyNef ℂ s₂ g D := by
  subst h; exact hd

/-- A proper divisor over `Y`, for another (equal) structure morphism. -/
private def properDivisorOverOfEq (h : s₁ = s₂) (E : MMP.Flips.ProperDivisorOver ℂ s₁) :
    MMP.Flips.ProperDivisorOver ℂ s₂ where
  Y := E.Y
  f := E.f
  isNormalVariety := h ▸ E.isNormalVariety
  isBirationalMorphism := E.isBirationalMorphism
  E := E.E
  isProper := E.isProper

end Structure

/-! ### Positivity and nefness -/

section Positivity

open MMP.Flips

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- A relatively ample Cartier divisor in the sense of *Flips and abundance* has positive degree
on every contracted proper curve. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {g : X ⟶ Y} {L : Divisor X}
    (hL : IsRelativelyAmpleCartier g L) (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < L.degreeOn ℂ sX C.ι C.dim_le hL.1 := by
  obtain ⟨hLc, hamp⟩ := hL
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hM : MMP.Mori.IsRelativelyAmple g L.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hM C hC

/-- An ample `ℝ`-divisor `∑ rⱼ Lⱼ` over `Y` has positive degree on every contracted curve. -/
private theorem sum_degreeOn_pos_of_isRelativelyAmple {g : X ⟶ Y} {m : ℕ} (hm : 1 ≤ m)
    {r : Fin m → ℝ} (hr : ∀ j, 0 < r j) {L : Fin m → Divisor X}
    (hL : ∀ j, IsRelativelyAmpleCartier g (L j)) (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j).1 : ℝ) :=
  Finset.sum_pos (fun j _ => mul_pos (hr j)
    (by exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier (hL j) C hC))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- A sum of nef `ℝ`-divisors over `Y` is nef over `Y`. -/
private theorem isRelativelyNef_add {g : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef ℂ sX g D₁) (h₂ : IsRelativelyNef ℂ sX g D₂) :
    IsRelativelyNef ℂ sX g (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl, hn₂⟩ := h₂
  have hc : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (fun j => by simpa using hL₁ j) (fun j => by simpa using hL₂ j)
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, hc, ?_, fun C hC x hx => ?_⟩
  · simp [Fin.sum_univ_add]
  · have hx₁ := isRIntersectionNumber_sum_degreeOn ℂ sX C r₁ L₁ hL₁
    have hx₂ := isRIntersectionNumber_sum_degreeOn ℂ sX C r₂ L₂ hL₂
    have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 _ _ r₁ L₁ r₂ L₂ _ _ 1 1 hx₁ hx₂
    simp only [one_smul, one_mul] at hsum
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hsum]
    exact add_nonneg (hn₁ C hC _ hx₁) (hn₂ C hC _ hx₂)

end Positivity

/-! ### Multiplicities along divisors over a smooth variety -/

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
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

section Multiplicity

open MMP.Flips

variable {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
  {sW : W ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sW]

/-- The pull-back of a prime divisor through the centre of `D` has coefficient at least one along
`D`. -/
private theorem one_le_coeff_pullback_single (hsm : IsSmoothScheme sW) (P : MMP.Mori.PrimeDivisor W)
    (D : DivisorOver ℂ sW) (hD : D.f D.E.genericPoint ∈ P.support) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    haveI := D.isIntegral
    haveI := D.isDominant
    haveI : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
    1 ≤ (Divisor.pullback (Finsupp.single P 1 : Divisor W)
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _)).coeff D.E := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨z, hzp, hz⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sW hsm P hD
  obtain ⟨m, hm1, hm⟩ := exists_valuation_eq_exp_neg D rfl hzp.ne_zero
    ((IsLocalRing.mem_maximalIdeal _).2 hzp.not_unit)
  have hc := coeff_isPullback_single_eq_of_stalk_eq_span P
    (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf sW hsm P)
    (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _))
    D.E rfl z hz m hm
  rw [hc]; exact hm1

/-- The pull-back of a prime divisor has nonnegative coefficients. -/
private theorem coeff_pullback_single_nonneg (hsm : IsSmoothScheme sW) (P : MMP.Mori.PrimeDivisor W)
    (D : DivisorOver ℂ sW) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    haveI := D.isIntegral
    haveI := D.isDominant
    haveI : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
    0 ≤ (Divisor.pullback (Finsupp.single P 1 : Divisor W)
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm P)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _)).coeff D.E := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨N, -, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder P
    (MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf sW hsm P)
    (Divisor.isPullback_pullback (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _)) D.E
  rw [hc]; exact Int.natCast_nonneg N

/-- **Multiplicities over a smooth variety.** Every `ℝ`-divisor `G` on a smooth variety has, along
every proper divisor `E` over it, a multiplicity `μ = ∑_P coeff_P(G) coeff_E(P)` computed from its
prime components; it scales with `G`, and it is positive when `G` is effective and the centre of
`E` lies in `Supp G`. -/
private theorem exists_isMultiplicityAlong_of_isSmoothScheme (hW : IsNormalVariety ℂ sW)
    (hsm : IsSmoothScheme sW) (G : RDivisor W) (E : MMP.Flips.ProperDivisorOver ℂ sW) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (μ : ℝ),
      IsMultiplicityAlong sW G r L E.valuation E μ ∧
      IsMultiplicityAlong sW (-G) (-r) L E.valuation E (-μ) ∧
      (G.IsEffective → E.f E.E.genericPoint ∈ (G.supp : Set W) → 0 < μ) := by
  classical
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  set S := G.support
  set e := S.equivFin
  let P : Fin S.card → MMP.Mori.PrimeDivisor W := fun j => (e.symm j : _)
  let r : Fin S.card → ℝ := fun j => G.coeff (P j)
  let L : Fin S.card → Divisor W := fun j => Finsupp.single (P j) 1
  have hLc : ∀ j, (L j).IsCartier := fun j =>
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _
  let L' : Fin S.card → Divisor E.Y := fun j => Divisor.pullback (L j) (hLc j)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f _)
  have hpb : ∀ j, ∃ hB : ∀ Z : irreducibleComponents E.Y,
      E.f (componentGenericPoint E.Y Z) ∉ (L j).supp, (L j).IsPullback E.f hB (L' j) :=
    fun j => ⟨_, Divisor.isPullback_pullback _ _⟩
  have hG : G = ∑ j, r j • Divisor.toRDivisor (L j) := eq_sum_coeff_smul_single G
  have hcenter : HasNonemptyCenter ℂ sW E.valuation := hasNonemptyCenter_valuation E
  refine ⟨S.card, r, L, ∑ j, r j * ((L' j).coeff E.E : ℝ),
    ⟨hW, hcenter, rfl, hLc, hG, L', hpb, rfl⟩,
    ⟨hW, hcenter, rfl, hLc, by rw [hG, ← Finset.sum_neg_distrib]; simp [neg_smul], L', hpb,
      by simp [Finset.sum_neg_distrib, neg_mul]⟩, fun hGe hx => ?_⟩
  obtain ⟨Q, hQ0, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  have hQS : Q ∈ S := Finsupp.mem_support_iff.mpr hQ0
  have hterm : ∀ j, 0 ≤ r j * ((L' j).coeff E.E : ℝ) := fun j =>
    mul_nonneg (hGe _) (by exact_mod_cast coeff_pullback_single_nonneg hsm (P j) E.toDivisorOver)
  set j₀ := e ⟨Q, hQS⟩
  have hPj₀ : P j₀ = Q := by simp [P, j₀]
  have hpos : 0 < r j₀ * ((L' j₀).coeff E.E : ℝ) := by
    have h1 : 0 < r j₀ := by
      simp only [r, hPj₀]
      exact lt_of_le_of_ne (hGe Q) (Ne.symm hQ0)
    have h2 : (1 : ℝ) ≤ ((L' j₀).coeff E.E : ℝ) := by
      have := one_le_coeff_pullback_single hsm (P j₀) E.toDivisorOver (hPj₀ ▸ hxQ)
      exact_mod_cast this
    nlinarith
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j₀))

/-- On a smooth variety, an `ℝ`-divisor whose support misses a proper curve has intersection
number `0` with it. -/
private theorem exists_isRIntersectionNumber_zero_of_disjoint [QuasiCompact sW]
    (hsm : IsSmoothScheme sW) (G : RDivisor W) (C : ProperCurve sW)
    (hC : Disjoint (closure ({C.point} : Set W)) (G.supp : Set W)) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W), IsRIntersectionNumber ℂ sW G r L C 0 := by
  classical
  set P : Fin G.support.card → MMP.Mori.PrimeDivisor W := fun j => (G.support.equivFin.symm j : _)
  have hLc : ∀ j, Divisor.IsCartier (Finsupp.single (P j) 1 : Divisor W) := fun j =>
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm (P j)
  have hx := isRIntersectionNumber_sum_degreeOn ℂ sW C (fun j => G.coeff (P j))
    (fun j => Finsupp.single (P j) 1) hLc
  rw [← eq_sum_coeff_smul_single G] at hx
  have hdeg : ∀ j,
      Divisor.degreeOn ℂ sW C.ι C.dim_le (Finsupp.single (P j) 1 : Divisor W) (hLc j) = 0 := by
    intro j
    have hPS : P j ∈ G.support := (G.support.equivFin.symm j).2
    have hdisj : Disjoint ((P j).support : Set W) (closure {C.point}) := by
      refine (hC.mono_right fun x hx => ?_).symm
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨P j, by
        rw [DivisorWithCoeffs.coeff_apply]; exact Finsupp.mem_support_iff.mp hPS, hx⟩
    have h0 := MMP.Threefold.Resolution.intersectionNumber_single_eq_zero_of_disjoint hsm (P j) C
      hdisj
    rw [MMP.Mori.QDivisor.intersectionNumber_toQDivisor ℂ sW C.ι C.dim_le _ (hLc j)] at h0
    exact_mod_cast h0
  refine ⟨_, fun j => G.coeff (P j), fun j => Finsupp.single (P j) 1, ?_⟩
  simpa [hdeg] using hx

end Multiplicity

/-! ### Residue degrees of non-contracted curves -/

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton_of_not_isContractedBy (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := not_exists_range_eq_singleton_of_not_isContractedBy u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end Pullback

/-! ### Proper curves in fibres -/

section FibreCurves

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
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
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme.{u}}
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

/-- Let `f : X ⟶ Y` be a proper morphism of `k`-schemes of finite type onto a normal variety, and
`η ⤳ p` a non-trivial specialization in the fibre of `f` over a closed point `y`, with `p` closed.
Then `f` contracts a proper curve of `X` lying over `y`. -/
private theorem exists_properCurve_isContractedBy_of_specializes (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : X ⟶ Y) (hf : f ≫ sY = sX)
    [IsProper f] {y : Y} (hy : IsClosed ({y} : Set Y)) {η p : X} (hηp : η ⤳ p)
    (hp : IsClosed ({p} : Set X)) (hne : η ≠ p) (hηy : f η = y) (hpy : f p = y) :
    ∃ C : ProperCurve sX, C.IsContractedBy f ∧ f C.point = y := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  let ι := f.fiberι y
  let sF := ι ≫ sX
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp k sY f hY y hy
  have : IsLocallyNoetherian (f.fiber y) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {y} := f.range_fiberι y
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηy
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpy
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber y)) := by
    have : ({p'} : Set (f.fiber y)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact hp.preimage ι.continuous
  obtain ⟨y', -, -, hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c hp'c (Set.mem_singleton p') (fun h => hne (by
      rw [Set.mem_singleton_iff] at h; rw [← hη', ← hp', h]))
  let C' : ProperCurve sF := ⟨y', hy'⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  let C : ProperCurve sX := ⟨ι y', isProperCurve_of_injective sX ι ι.isEmbedding.injective C'⟩
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {y} := by
    rw [← hrange, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have h2 : f (ι y') = y := hclF (subset_closure rfl)
  refine ⟨C, fun z hz => ?_, h2⟩
  exact (hclF hz).trans h2.symm

/-- A proper curve `Γ` contracted by `u : Y ⟶ S` is the image, under a proper surjective
`g : W ⟶ Y`, of a proper curve `Γ'` of `W` which is contracted by `g ≫ u` but not by `g`. -/
private theorem exists_properCurve_lift {W Y S : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] [QuasiCompact sY] (g : W ⟶ Y) [IsProper g] [Surjective g]
    [LocallyOfFiniteType (g ≫ sY)] [QuasiCompact (g ≫ sY)] (u : Y ⟶ S) (Γ : ProperCurve sY)
    (hΓ : Γ.IsContractedBy u) :
    ∃ Γ' : ProperCurve (g ≫ sY), g Γ'.point = Γ.point ∧ Γ'.IsContractedBy (g ≫ u) ∧
      ¬ Γ'.IsContractedBy g := by
  obtain ⟨Γ', hΓ'pt, hΓ'img⟩ := MMP.Mori.ProperCurve.exists_map_eq (g ≫ sY) sY g rfl Γ
  refine ⟨Γ', hΓ'pt, fun y hy => ?_, fun hc => ?_⟩
  · have hgy : g y ∈ closure ({Γ.point} : Set Y) := hΓ'img ▸ ⟨y, hy, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hΓ _ hgy, hΓ'pt]
  have hsing : closure ({Γ.point} : Set Y) = {Γ.point} := by
    rw [← hΓ'img]
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Γ'.point, subset_closure rfl, hΓ'pt⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hc y hy, hΓ'pt]
  have : Subsingleton Γ.scheme := ⟨fun a b => Γ.ι.isEmbedding.injective <| by
    have ha : Γ.ι a ∈ Set.range Γ.ι := ⟨a, rfl⟩
    have hb : Γ.ι b ∈ Set.range Γ.ι := ⟨b, rfl⟩
    rw [Γ.range_ι, hsing] at ha hb
    exact ha.trans hb.symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology Γ.scheme
  rw [Γ.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A proper birational morphism `g` onto a normal variety contracts a proper curve over every
closed point outside its biregular locus: by Zariski's main theorem the fibre is infinite there,
so it has an infinite irreducible component, whose generic point specializes to a closed point
other than itself. -/
private theorem exists_properCurve_isContractedBy_of_notMem_biregularLocus {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (hX : IsNormalVariety ℂ sX)
    (hY : IsNormalVariety ℂ sY) (g : X ⟶ Y) (hg : g ≫ sY = sX) [IsProper g]
    (hgb : IsBirationalMorphism g) {y : Y} (hy : IsClosed ({y} : Set Y))
    (hyb : y ∉ biregularLocus g) : ∃ C : ProperCurve sX, C.IsContractedBy g ∧ g C.point = y := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := (hX.1.toQuasiCompact).compactSpace_of_compactSpace
  have : IsNoetherian X := ⟨⟩
  obtain ⟨hU, hI⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hgb)).1 inferInstance
  have hinf : (g.base ⁻¹' {y}).Infinite := fun hfin =>
    hyb (le_biregularLocus (V := ⟨_, hU⟩) hI hfin)
  obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (hy.preimage g.continuous)
  obtain ⟨t, htS, htinf⟩ : ∃ t ∈ S, t.Infinite := by
    by_contra! hfin
    exact hinf (hFS ▸ hSf.sUnion fun t ht => hfin t ht)
  have htF : t ⊆ g.base ⁻¹' {y} := hFS ▸ Set.subset_sUnion_of_mem htS
  have hgen := (hScl t htS).closure_eq ▸ (hSirr t htS).isGenericPoint_genericPoint_closure
  obtain ⟨p, hpt, hpc⟩ := (hScl t htS).exists_closed_singleton (hSirr t htS).nonempty
  refine exists_properCurve_isContractedBy_of_specializes ℂ sX sY hX hY g hg hy
    (hgen.specializes hpt) hpc (fun he => htinf ?_) (htF hgen.mem) (htF hpt)
  rw [← hgen.def, he, hpc.closure_eq]
  exact Set.finite_singleton _

end FibreCurves

/-! ### The discrepancy comparison across a real flip -/

section Comparison

open MMP.Flips

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Z]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
  {fp : X' ⟶ Z}

/-- **The negativity lemma on a smooth common model of a real flip.** There is a smooth common
model `X ⟵ W ⟶ X⁺` over `Z`, with `h : W ⟶ Z`, and an effective `ℝ`-divisor
`F = p^*(K + B) - q^*(K⁺ + B⁺)` on it, such that:
* `h⁻¹(z) ⊆ Supp F` for every `z ∈ Z` over which `f` or `f⁺` contracts a proper curve: otherwise
  the fibre misses `Supp F`, and a curve `Γ'` of `W` over the contracted curve would have
  `F · Γ' = 0`, while `F · Γ' < 0` (over `f`, as `-(K + B)` is `f`-ample) or `F · Γ' > 0`
  (over `f⁺`, as `K⁺ + B⁺` is `f⁺`-ample);
* `Supp F` contains every point of `W` lying over the complement of the biregular locus of `f` or
  of `f⁺`: `W` is Jacobson, and `f` or `f⁺` contracts a curve over every closed point there;
* for a divisor `D₁` over `W` with images `D` over `X` and `D⁺` over `X⁺`,
  `a(D⁺, X⁺, B⁺) - a(D, X, B) = mult_{D₁} F ≥ 0`, positive when the centre of `D₁` lies in
  `Supp F`. -/
private theorem IsRealFlipStep.exists_smoothCommonModel
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m, K.IsCanonicalDivisor sX m) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (p : W ⟶ X) (q : W ⟶ X') (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q),
      IsNormalVariety ℂ (p ≫ sX) ∧ IsProper p ∧ IsProper q ∧ p ≫ f = q ≫ fp ∧
      IsSmoothScheme (p ≫ sX) ∧ ∃ F : RDivisor W,
      (∀ z : Z, ((∃ Γ : ProperCurve sX, Γ.IsContractedBy f ∧ f Γ.point = z) ∨
          ∃ Γ : ProperCurve sX', Γ.IsContractedBy fp ∧ fp Γ.point = z) →
        (p ≫ f).base ⁻¹' {z} ⊆ (F.supp : Set W)) ∧
      (∀ w : W, ((p ≫ f).base w ∉ biregularLocus f ∨ (p ≫ f).base w ∉ biregularLocus fp) →
        w ∈ (F.supp : Set W)) ∧
      ∀ (D₁ : DivisorOver ℂ (p ≫ sX)) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (n : ℕ)
        (a a' : ℝ), IsProper D₁.f →
        (haveI := hpb.isDominant; D.valuation = D₁.valuation.comap (functionFieldMap p)) →
        (haveI := hqb.isDominant; D'.valuation = D₁.valuation.comap (functionFieldMap q)) →
        MMP.Intersection.IsLogDiscrepancy sX n B D a →
        MMP.Intersection.IsLogDiscrepancy sX' n B' D' a' →
        a ≤ a' ∧ (D₁.f D₁.E.genericPoint ∈ (F.supp : Set W) → a < a') := by
  classical
  have hneg := hstep.isNegativeExtremalContraction
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have hsm := hstep.isSmall
  have hsm' := hstep.isSmall_flip
  have hfs : f ≫ sZ = sX := hsm.comp_eq
  have hfps : fp ≫ sZ = sX' := hsm'.comp_eq
  have hX'v : IsNormalVariety ℂ sX' := ⟨hsm'.isVariety_source, inferInstance⟩
  haveI : IsProper f := hsm.isProper
  haveI : IsProper fp := hsm'.isProper
  have hfb := hstep.isBirationalMorphism
  have hfpb := hstep.isBirationalMorphism_flip
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  -- the common model
  obtain ⟨φ, hφb, hφ⟩ := exists_isBirational_compHom_eq hfb hfpb
  obtain ⟨W, p, q, hWv, hWsm, hpP, hqP, hpb, hqb, -, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sX sX' sZ hXv hX'v hZv.1 f fp hfs hfps φ
      ⟨hφb, hφ⟩
  haveI := hpP
  haveI := hqP
  have hpq : q ≫ sX' = p ≫ sX := by
    rw [← hfps, ← Category.assoc, ← hcomm, Category.assoc, hfs]
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := (hWv.toQuasiCompact).compactSpace_of_compactSpace
  haveI : IsNormal W :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm).2
  have hW : IsNormalVariety ℂ (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hWq : IsNormalVariety ℂ (q ≫ sX') := hpq ▸ hW
  haveI : LocallyOfFiniteType (q ≫ sX') := hWq.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWv.toQuasiCompact
  haveI : QuasiCompact (q ≫ sX') := hWq.1.toQuasiCompact
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  -- dimensions
  obtain ⟨n, hK0⟩ := hK
  have hdX : topologicalKrullDim X = n := hK0.topologicalKrullDim_eq
  have hdXZ : topologicalKrullDim X = topologicalKrullDim Z := hsm.dim_eq
  have hdX'Z : topologicalKrullDim X' = topologicalKrullDim Z := hsm'.dim_eq
  have hdX' : topologicalKrullDim X' = n := hdX'Z.trans (hdXZ.symm.trans hdX)
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hWv
  have hdW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm.trans
      hdX
  -- the forms
  obtain ⟨m₁, hK'0⟩ := hstep.isCanonicalDivisor_flip
  have hm₁ : n = m₁ := by
    have := hK'0.topologicalKrullDim_eq.symm.trans hdX'
    exact_mod_cast this.symm
  subst hm₁
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hXv hK0
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sX n := hdiv ▸ hK0
  have hKBX : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B) := by
    rw [hdiv]; exact hneg.isCartierCombination
  set τ := pullbackRationalPluriForms sX p ω with hτ
  have hτ0 : τ ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdX) hω0
  obtain ⟨τ', hτ'0, hτ'⟩ := exists_form_divisorOfForm_eq hpq.symm τ hτ0
  obtain ⟨ω', hω'⟩ := exists_pullbackRationalPluriForms_eq q hqb.functionFieldMap_bijective hdX' τ'
  have hω'0 : ω' ≠ 0 := by
    rintro rfl
    exact hτ'0 (hω' ▸ pullbackRationalPluriForms_zero q)
  have hK'ω : (divisorOfForm ω').IsCanonicalDivisor sX' n :=
    isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hX'v hK'0 hω'0
  -- the presentations of the two adjoint divisors
  obtain ⟨m, r, L, hm1, hr, hL, hA⟩ := hneg.isRelativelyAntiAmple
  obtain ⟨m', r', L', hm'1, hr', hL', hA'⟩ := hstep.isRelativelyAmple_flip
  obtain ⟨φ₀, hφ₀⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX'v hK'0
    (m := 1) hω'0
  rw [one_smul] at hφ₀
  set N : Divisor X' := divisorOfForm ω' - K' with hN
  have hNc : N.IsCartier := hφ₀ ▸ Divisor.isCartier_principalDivisor φ₀
  have hNlin : N.LinearlyEquivalent 0 := ⟨φ₀, by rw [sub_zero]; exact hφ₀⟩
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  set r'' : Fin (m' + 1) → ℝ := Fin.snoc r' 1 with hr''
  set L'' : Fin (m' + 1) → Divisor X' := Fin.snoc L' N with hL''
  have hL''c : ∀ j, (L'' j).IsCartier := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [L''] using hNc
    · simpa [L''] using (hL' i).1
  have hAX : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [hdiv]
    have := congrArg Neg.neg hA
    simp only [neg_neg] at this
    change logCanonicalDivisor K B = _
    rw [this, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  have hAX' : Divisor.toRDivisor (divisorOfForm ω') + B' =
      ∑ j, r'' j • Divisor.toRDivisor (L'' j) := by
    rw [Fin.sum_univ_castSucc]
    simp only [r'', L'', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
    rw [← hA']
    simp only [logCanonicalDivisor, N, map_sub]
    abel
  -- pull-backs to the common model
  set GX : RDivisor W := ∑ j, (-r j) • Divisor.toRDivisor ((L j).pullback (hLc j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j))) with hGX
  set GY : RDivisor W := ∑ j, r'' j • Divisor.toRDivisor ((L'' j).pullback (hL''c j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j))) with hGY
  have hGXp : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + B) GX :=
    ⟨m, fun j => -r j, L, _, hLc, hAX, fun j => ⟨_, Divisor.isPullback_pullback _ _⟩, rfl⟩
  have hGYp : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω') + B') GY :=
    ⟨m' + 1, r'', L'', _, hL''c, hAX', fun j => ⟨_, Divisor.isPullback_pullback _ _⟩, rfl⟩
  set KW := divisorOfForm τ with hKW
  set DW : RDivisor W := GX - Divisor.toRDivisor KW with hDW
  set DW' : RDivisor W := GY - Divisor.toRDivisor KW with hDW'
  have hpbW : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + DW) := by
    rw [hDW, ← hτ, ← hKW, add_sub_cancel]; exact hGXp
  have hdivq : divisorOfForm (pullbackRationalPluriForms sX' q ω') = KW := by rw [hω', hτ']
  have hpbW' : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω') + B')
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX' q ω')) + DW') := by
    rw [hdivq, hDW', add_sub_cancel]; exact hGYp
  -- canonical divisors on `W`
  have hKWp : (divisorOfForm (pullbackRationalPluriForms sX p ω)).IsCanonicalDivisor
      (p ≫ sX) n := isCanonicalDivisor_divisorOfForm_pullback hXv hω0 hKω hW hpb hWsm
  have hWsm' : IsSmoothScheme (q ≫ sX') := hpq ▸ hWsm
  have hKWq : (divisorOfForm (pullbackRationalPluriForms sX' q ω')).IsCanonicalDivisor
      (q ≫ sX') n := isCanonicalDivisor_divisorOfForm_pullback hX'v hω'0 hK'ω hWq hqb hWsm'
  have hKBX' : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω') + B') :=
    ⟨m' + 1, r'', L'', hL''c, by rw [hAX']; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  -- the negativity lemma for `F = D_W - D_W'` over `Z`
  set h : W ⟶ Z := p ≫ f with hh
  haveI : IsProper h := by rw [hh]; infer_instance
  have hhs : h ≫ sZ = p ≫ sX := by rw [hh, Category.assoc, hfs]
  have hhb : IsBirationalMorphism h := MMP.Mori.isBirationalMorphism_comp_of_isBirational f p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb)
  have hhq : h = q ≫ fp := hcomm
  have hFc : IsCartierCombination (DW - DW') :=
    ⟨_, fun j => (DW - DW').coeff ((DW - DW').support.equivFin.symm j),
      fun j => Finsupp.single ((DW - DW').support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1,
      fun j => MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hWsm _, by
      conv_lhs => rw [eq_sum_coeff_smul_single (DW - DW')]
      simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hFexc : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P →
      (DW - DW').coeff P = 0 := by
    intro P hP
    have hdWZ : topologicalKrullDim W = topologicalKrullDim Z := hdW.trans (hdX.symm.trans hdXZ)
    have hcoP : Order.coheight (h P.genericPoint) = 1 := by
      have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hZv h (hhs ▸ hW) hhb P).not.mp hP
      have h1 := MMP.Flips.coheight_le_coheight_map sZ (p ≫ sX) hZv.1 hWv h hhs hdWZ
        P.genericPoint
      rw [P.coheight_genericPoint] at h1
      refine le_antisymm (Order.le_of_lt_add_one ?_) h1
      rw [one_add_one_eq_two]; exact not_le.mp h2
    -- the image in `X`
    have hcop : Order.coheight (p P.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX (p ≫ sX) hXv.1 hWv p rfl
        (hdW.trans hdX.symm) P.genericPoint
      have h2 := MMP.Flips.coheight_le_coheight_map sZ sX hZv.1 hXv.1 f hfs hdXZ
        (p P.genericPoint)
      rw [P.coheight_genericPoint] at h1
      rw [show f (p P.genericPoint) = h P.genericPoint from rfl, hcoP] at h2
      exact le_antisymm h2 h1
    have hcoq : Order.coheight (q P.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX' (q ≫ sX') hX'v.1 hWq.1 q rfl
        (hdW.trans hdX'.symm) P.genericPoint
      have h2 := MMP.Flips.coheight_le_coheight_map sZ sX' hZv.1 hX'v.1 fp hfps hdX'Z
        (q P.genericPoint)
      rw [P.coheight_genericPoint] at h1
      rw [show fp (q P.genericPoint) = h P.genericPoint by
        rw [hhq, Scheme.Hom.comp_apply], hcoP] at h2
      exact le_antisymm h2 h1
    have hnex : ¬ (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sX).IsExceptional := by
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hXv]
      change ¬ 2 ≤ Order.coheight (p P.genericPoint)
      rw [hcop]; decide
    have hnex' : ¬ (⟨W, q, hWq, hqb, P⟩ : DivisorOver ℂ sX').IsExceptional := by
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX'v]
      change ¬ 2 ≤ Order.coheight (q P.genericPoint)
      rw [hcoq]; decide
    obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hXv hnex
    obtain ⟨Q', hQ'⟩ := exists_valuation_eq_of_not_isExceptional hX'v hnex'
    have hpQ : p P.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
    have hqQ : q P.genericPoint = Q'.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'v.1 hQ'
    have hd1 := isDiscrepancy_primeDivisor_of_isRCartierPullback hXv hω0 hKω hKBX hW hpb hWsm
      hpbW P
    have hd2 := isDiscrepancy_divisorialValuation hXv ω hω0 hKω hKBX Q
    rw [hQ, valuation_ofPrimeDivisor hXv Q] at hd1
    have he1 := hd1.eq hd2
    have hd1' := isDiscrepancy_primeDivisor_of_isRCartierPullback hX'v hω'0 hK'ω hKBX' hWq hqb
      hWsm' hpbW' P
    have hd2' := isDiscrepancy_divisorialValuation hX'v ω' hω'0 hK'ω hKBX' Q'
    rw [hQ', valuation_ofPrimeDivisor hX'v Q'] at hd1'
    have he2 := hd1'.eq hd2'
    have hQQ' : fp Q'.genericPoint = f Q.genericPoint := by
      rw [← hqQ, ← hpQ]
      have := congrArg (fun g : W ⟶ Z => g P.genericPoint) (hh.symm.trans hhq)
      simpa only [Scheme.Hom.comp_apply] using this.symm
    have hcoef : B'.coeff Q' = B.coeff Q := by
      rw [hstep.eq_flipTransform]
      simp only [DivisorWithCoeffs.coeff_apply]
      exact flipTransform_apply_of_isSmall hZv hsm hsm' hfb hQQ' B
    rw [DivisorWithCoeffs.coeff_sub]
    linarith
  -- `-F` is nef over `Z`
  have hNdeg : ∀ C : ProperCurve sX', N.degreeOn ℂ sX' C.ι C.dim_le hNc = 0 := fun C =>
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX' C.ι C.dim_le hNc hNlin
  -- `(K⁺ + B⁺) · Γ > 0` on a curve `Γ` contracted by `f⁺`
  have hΓpos : ∀ Γ : ProperCurve sX', Γ.IsContractedBy fp →
      0 < ∑ j, r'' j * ((L'' j).degreeOn ℂ sX' Γ.ι Γ.dim_le (hL''c j) : ℝ) := fun Γ hΓ => by
    rw [Fin.sum_univ_castSucc]
    simp only [r'', L'', Fin.snoc_castSucc, Fin.snoc_last, hNdeg Γ, Int.cast_zero, mul_zero,
      add_zero]
    exact sum_degreeOn_pos_of_isRelativelyAmple hm'1 hr' hL' Γ hΓ
  have hGYnef : IsRelativelyNef ℂ (q ≫ sX') (q ≫ fp) GY := by
    have := isRelativelyNef_neg_sum_pullback (k := ℂ) (sY := sX') q fp (fun j => -r'' j) L'' hL''c
      (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j))
      (fun C hC => by
        simp only [neg_mul, Finset.sum_neg_distrib, neg_nonpos]
        exact (hΓpos C hC).le)
    simpa [GY, neg_smul, Finset.sum_neg_distrib] using this
  have hGXnef : IsRelativelyNef ℂ (p ≫ sX) (p ≫ f) (-GX) :=
    isRelativelyNef_neg_sum_pullback (k := ℂ) (sY := sX) p f (fun j => -r j) L hLc
      (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j))
      (fun C hC => by
        have hpos := sum_degreeOn_pos_of_isRelativelyAmple hm1 hr hL C hC
        simp only [neg_mul, Finset.sum_neg_distrib, neg_nonpos]
        exact hpos.le)
  have hnef : IsRelativelyNef ℂ (p ≫ sX) h (-(DW - DW')) := by
    have h1 := isRelativelyNef_of_eq_structure hpq hGYnef
    rw [← hhq] at h1
    have h2 := isRelativelyNef_add h1 hGXnef
    have : -(DW - DW') = GY + -GX := by simp only [hDW, hDW']; abel
    rw [this]; exact h2
  obtain ⟨hFeff, hfib⟩ :=
    isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg ℂ sZ
      (p ≫ sX) hZv hW h hhs hhb hFc hFexc hnef
  -- the intersection numbers on a curve of `W`
  have hNXc : ∀ j, ((L j).pullback (hLc j)
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j))).IsCartier :=
    fun j => (hLc j).isCartier_pullback p _
  have hNYc : ∀ j, ((L'' j).pullback (hL''c j)
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j))).IsCartier :=
    fun j => (hL''c j).isCartier_pullback q _
  have hFeq2 : (1 : ℝ) • GX + (-1 : ℝ) • GY = DW - DW' := by
    simp only [hDW, hDW', one_smul, neg_one_smul]; abel
  -- a curve `Γ'` contracted by `h` on which `F` has nonzero degree has its fibre in `Supp F`
  have hcurve : ∀ {s : W ⟶ Spec (.of ℂ)} [LocallyOfFiniteType s] [QuasiCompact s],
      IsSmoothScheme s → ∀ Γ' : ProperCurve s, Γ'.IsContractedBy h →
      (∀ (m0 : ℕ) (r0 : Fin m0 → ℝ) (L0 : Fin m0 → Divisor W) (x : ℝ),
        IsRIntersectionNumber ℂ s (DW - DW') r0 L0 Γ' x → x ≠ 0) →
      h.base ⁻¹' {h Γ'.point} ⊆ ((DW - DW').supp : Set W) := by
    intro s _ _ hs Γ' hΓ' hne
    refine (hfib _).resolve_right fun hdisj => ?_
    obtain ⟨m0, r0, L0, h0⟩ := exists_isRIntersectionNumber_zero_of_disjoint hs (DW - DW') Γ'
      (hdisj.mono_left fun y hy => hΓ' y hy)
    exact hne _ _ _ _ h0 rfl
  haveI : Surjective p := ⟨by
    rw [← Set.range_eq_univ, ← p.isClosedMap.isClosed_range.closure_eq, p.denseRange.closure_eq]⟩
  haveI : Surjective q := ⟨by
    rw [← Set.range_eq_univ, ← q.isClosedMap.isClosed_range.closure_eq, q.denseRange.closure_eq]⟩
  have hfibC : ∀ z : Z, ((∃ Γ : ProperCurve sX, Γ.IsContractedBy f ∧ f Γ.point = z) ∨
      ∃ Γ : ProperCurve sX', Γ.IsContractedBy fp ∧ fp Γ.point = z) →
      h.base ⁻¹' {z} ⊆ ((DW - DW').supp : Set W) := by
    rintro z (⟨Γ, hΓc, hΓz⟩ | ⟨Γ, hΓc, hΓz⟩)
    · -- over `f`: `G_X · Γ' < 0 ≤ G_Y · Γ'`
      obtain ⟨Γ', hΓ'pt, hΓ'h, hnc⟩ := exists_properCurve_lift sX p f Γ hΓc
      have hz : h Γ'.point = z := by rw [hh, Scheme.Hom.comp_apply, hΓ'pt, hΓz]
      rw [← hz]
      refine hcurve hWsm Γ' hΓ'h fun m0 r0 L0 x hx hx0 => ?_
      have hxGX := isRIntersectionNumber_sum_degreeOn ℂ (p ≫ sX) Γ' (fun j => -r j) _ hNXc
      have hGX := sum_degreeOn_pullback_eq_mul p (fun j => -r j) L hLc
        (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j)) Γ' Γ
        hΓ'pt.symm
      simp only [neg_mul, Finset.sum_neg_distrib, mul_neg] at hGX
      have hpos := mul_pos (by exact_mod_cast residueFieldDegree_pos p rfl Γ' hnc :
        (0 : ℝ) < residueFieldDegree p Γ'.point)
        (sum_degreeOn_pos_of_isRelativelyAmple hm1 hr hL Γ hΓc)
      have hxGY := isRIntersectionNumber_sum_degreeOn ℂ (p ≫ sX) Γ' r'' _ hNYc
      have hGYnef' : IsRelativelyNef ℂ (p ≫ sX) h (-(-GY)) := by
        rw [neg_neg, hhq]; exact isRelativelyNef_of_eq_structure hpq hGYnef
      have hGY0 := nonpos_of_isRelativelyNef_neg hGYnef' Γ' hΓ'h (isRIntersectionNumber_neg hxGY)
      have hF := (IsRIntersectionNumber.eq_and_linear ℂ (p ≫ sX) Γ').2 GX GY _ _ _ _ _ _ 1 (-1)
        hxGX hxGY
      rw [hFeq2] at hF
      have := (IsRIntersectionNumber.eq_and_linear ℂ (p ≫ sX) Γ').1 _ _ _ _ _ _ _ hF hx
      simp only [neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · -- over `f⁺`: `G_X · Γ' ≤ 0 < G_Y · Γ'`
      obtain ⟨Γ', hΓ'pt, hΓ'h, hnc⟩ := exists_properCurve_lift sX' q fp Γ hΓc
      rw [← hhq] at hΓ'h
      have hz : h Γ'.point = z := by rw [hhq, Scheme.Hom.comp_apply, hΓ'pt, hΓz]
      rw [← hz]
      refine hcurve hWsm' Γ' hΓ'h fun m0 r0 L0 x hx hx0 => ?_
      have hxGX := isRIntersectionNumber_sum_degreeOn ℂ (q ≫ sX') Γ' (fun j => -r j) _ hNXc
      have hGXle := nonpos_of_isRelativelyNef_neg (isRelativelyNef_of_eq_structure hpq.symm hGXnef)
        Γ' hΓ'h hxGX
      have hxGY := isRIntersectionNumber_sum_degreeOn ℂ (q ≫ sX') Γ' r'' _ hNYc
      have hGY := sum_degreeOn_pullback_eq_mul q r'' L'' hL''c
        (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j)) Γ' Γ
        hΓ'pt.symm
      have hpos := mul_pos (by exact_mod_cast residueFieldDegree_pos q rfl Γ' hnc :
        (0 : ℝ) < residueFieldDegree q Γ'.point) (hΓpos Γ hΓc)
      have hF := (IsRIntersectionNumber.eq_and_linear ℂ (q ≫ sX') Γ').2 GX GY _ _ _ _ _ _ 1 (-1)
        hxGX hxGY
      rw [hFeq2] at hF
      have := (IsRIntersectionNumber.eq_and_linear ℂ (q ≫ sX') Γ').1 _ _ _ _ _ _ _ hF hx
      linarith
  -- every point over the non-biregular locus lies in `Supp F`, as `W` is Jacobson
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (p ≫ sX)
  have hpoint : ∀ w : W, (h.base w ∉ biregularLocus f ∨ h.base w ∉ biregularLocus fp) →
      w ∈ ((DW - DW').supp : Set W) := by
    intro w hw
    by_contra hwF
    obtain ⟨w₀, ⟨hw₀w, hw₀F⟩, hw₀c⟩ := nonempty_inter_closedPoints
      (Z := closure {w} ∩ ((DW - DW').supp : Set W)ᶜ) ⟨w, subset_closure rfl, hwF⟩
      (isClosed_closure.isLocallyClosed.inter
        (DW - DW').supp.isClosed.isOpen_compl.isLocallyClosed)
    have hsp : h w ⤳ h w₀ := (specializes_iff_mem_closure.mpr hw₀w).map h.continuous
    have hz₀ : IsClosed ({h w₀} : Set Z) := by simpa using h.isClosedMap _ hw₀c
    refine hw₀F (hfibC (h w₀) ?_ rfl)
    rcases hw with hb | hb
    · exact Or.inl (exists_properCurve_isContractedBy_of_notMem_biregularLocus sX sZ hXv hZv f hfs
        hfb hz₀ fun hb₀ => hb (hsp.mem_open (biregularLocus f).isOpen hb₀))
    · exact Or.inr (exists_properCurve_isContractedBy_of_notMem_biregularLocus sX' sZ hX'v hZv fp
        hfps hfpb hz₀ fun hb₀ => hb (hsp.mem_open (biregularLocus fp).isOpen hb₀))
  refine ⟨W, inferInstance, inferInstance, inferInstance, p, q, hpb, hqb, hW, hpP, hqP, hcomm,
    hWsm, DW - DW', hfibC, hpoint, fun D₁ D D' n' a a' hD₁ hv hv' ha ha' => ?_⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hdX
  -- the crepant transfers to `W`
  let D₁p : ProperDivisorOver ℂ (p ≫ sX) := ⟨D₁, hD₁⟩
  let D₁q : ProperDivisorOver ℂ (q ≫ sX') := properDivisorOverOfEq hpq.symm D₁p
  have hFX := isDiscrepancy_of_isLogDiscrepancy ha hω0 hKω hKBX
  rw [hv] at hFX
  have hFW := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXv hω0 hKω hKBX p hW hpb
    hpbW hKWp D₁p (a - 1)).mp hFX
  have hFX' := isDiscrepancy_of_isLogDiscrepancy ha' hω'0 hK'ω hKBX'
  rw [hv'] at hFX'
  have hFW' := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX'v hω'0 hK'ω hKBX' q hWq hqb
    hpbW' hKWq D₁q (a' - 1)).mp hFX'
  rw [hdivq] at hFW'
  have hFW'p := isDiscrepancy_of_eq_structure hpq hFW'
  -- the multiplicity of `F` along `D₁`
  obtain ⟨mF, rF, LF, μ, hμ, hμneg, hμpos⟩ :=
    exists_isMultiplicityAlong_of_isSmoothScheme hW hWsm (DW - DW') D₁p
  have hsubeq : DW' - DW = -(DW - DW') := by abel
  have hFW'' := IsDiscrepancy.sub_of_isMultiplicityAlong hFW (hsubeq ▸ hμneg)
  have heq : a - 1 - -μ = a' - 1 := hFW''.eq hFW'p
  have hμ0 : 0 ≤ μ :=
    IsMultiplicityAlong.nonneg hμ (DivisorWithCoeffs.isEffective_iff_nonneg.mp hFeff)
  exact ⟨by linarith, fun hmem => by linarith [hμpos hFeff hmem]⟩

/-- **Log discrepancies do not decrease across a real flip**, and increase strictly over a point
of `Z` with a positive-dimensional fibre in `X⁺` (FA 2.28 for small contractions). Every proper
divisor `E⁺` over `X⁺` is realized by a proper divisor `E` over `X` with the same valuation of
`k(Z)` and the same centre on `Z`, and `a(E, X, B) ≤ a(E⁺, X⁺, B⁺)`. -/
public theorem IsRealFlipStep.exists_isLogDiscrepancy_le
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m, K.IsCanonicalDivisor sX m) (E' : DivisorOver ℂ sX') (hE'p : IsProper E'.f) :
    ∃ E : DivisorOver ℂ sX, IsProper E.f ∧
      (haveI := hstep.isBirationalMorphism.isDominant
       haveI := hstep.isBirationalMorphism_flip.isDominant
       E.valuation.comap (functionFieldMap f) = E'.valuation.comap (functionFieldMap fp)) ∧
      f (E.f E.E.genericPoint) = fp (E'.f E'.E.genericPoint) ∧
      ∀ (n n' : ℕ) (a a' : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B E a →
        MMP.Intersection.IsLogDiscrepancy sX' n' B' E' a' →
        a ≤ a' ∧ ((∃ Γ : ProperCurve sX', Γ.IsContractedBy fp ∧
            fp Γ.point = fp (E'.f E'.E.genericPoint)) →
          IsClosed {fp (E'.f E'.E.genericPoint)} → a < a') := by
  obtain ⟨W, _, _, _, p, q, hpb, hqb, hW, hpP, hqP, hcomm, -, F, hfib, -, hcmp⟩ :=
    hstep.exists_smoothCommonModel hK
  haveI := hpP
  haveI := hqP
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI := hstep.isBirationalMorphism.isDominant
  haveI := hstep.isBirationalMorphism_flip.isDominant
  have hsm' := hstep.isSmall_flip
  have hX'v : IsNormalVariety ℂ sX' := ⟨hsm'.isVariety_source, inferInstance⟩
  have hpq : q ≫ sX' = p ≫ sX := by
    rw [← hsm'.comp_eq, ← Category.assoc, ← hcomm, Category.assoc, hstep.isSmall.comp_eq]
  have hWq : IsNormalVariety ℂ (q ≫ sX') := hpq ▸ hW
  -- the realization of `E⁺` on `W`
  obtain ⟨D₁, hD₁, -⟩ := ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hX'v.1 q
    hWq.1 hqb ⟨E', hE'p⟩
  set D₁p := properDivisorOverOfEq hpq D₁ with hD₁p
  set E := compDivisorOver p hpb D₁p with hE
  have hEv : E.valuation = D₁.valuation.comap (functionFieldMap p) :=
    compDivisorOver_valuation p hpb D₁p
  set E'' := compDivisorOver q hqb D₁ with hE''
  have hE''v : E''.valuation = E'.valuation := (compDivisorOver_valuation q hqb D₁).trans hD₁
  have hcommff : ∀ t, functionFieldMap p (functionFieldMap f t) =
      functionFieldMap q (functionFieldMap fp t) := fun t => by
    haveI : IsDominant (p ≫ f) := hcomm ▸ inferInstance
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  have hval : E.valuation.comap (functionFieldMap f) =
      E'.valuation.comap (functionFieldMap fp) := by
    rw [hEv, ← hE''v, compDivisorOver_valuation q hqb D₁]
    ext t
    simp only [Valuation.comap_apply]
    rw [hcommff t]
  have hpt : f (E.f E.E.genericPoint) = fp (E'.f E'.E.genericPoint) := by
    have h1 : E'.f E'.E.genericPoint = E''.f E''.E.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'v.1 hE''v.symm
    rw [h1]
    change f (p (D₁.f D₁.E.genericPoint)) = fp (q (D₁.f D₁.E.genericPoint))
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  refine ⟨E.toDivisorOver, E.isProper, hval, hpt, fun n n' a a' ha ha' => ?_⟩
  obtain rfl : n = n' := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      (hstep.isSmall.dim_eq.trans (hsm'.dim_eq.symm.trans
        (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha')))
  obtain ⟨hle, hlt⟩ := hcmp D₁p.toDivisorOver E.toDivisorOver E' n a a' D₁p.isProper hEv
    hD₁.symm ha ha'
  exact ⟨hle, fun hΓ _ => hlt (hfib _ (Or.inr hΓ) hpt)⟩

/-- **Log discrepancies increase strictly over the non-biregular locus of a real flip.** There is
a smooth common model `X ⟵ W ⟶ X⁺` over `Z` on which every point `w` lying over a point of `Z`
outside the biregular locus of `f` or of `f⁺` lies on a prime divisor `E` of `W` with
`a(E, X, B) < a(E, X⁺, B⁺)`. -/
public theorem IsRealFlipStep.exists_commonModel_lt_of_notMem_biregularLocus
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m, K.IsCanonicalDivisor sX m) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (r : W ⟶ X) (q : W ⟶ X') (hr : IsBirationalMorphism r) (hq : IsBirationalMorphism q),
      IsProper r ∧ IsProper q ∧ r ≫ f = q ≫ fp ∧ IsSmoothScheme (r ≫ sX) ∧
      ∀ w : W, ((r ≫ f).base w ∉ MMP.Mori.biregularLocus f ∨
          (r ≫ f).base w ∉ MMP.Mori.biregularLocus fp) →
        ∃ E : MMP.Mori.PrimeDivisor W, w ∈ (E.support : Set W) ∧
          ∀ (n : ℕ) (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (a a' : ℝ),
            (haveI := hr.isDominant; D.valuation = E.valuationOver r) →
            (haveI := hq.isDominant; D'.valuation = E.valuationOver q) →
            MMP.Intersection.IsLogDiscrepancy sX n B D a →
            MMP.Intersection.IsLogDiscrepancy sX' n B' D' a' → a < a' := by
  obtain ⟨W, _, _, _, r, q, hr, hq, hW, hrP, hqP, hcomm, hWsm, F, -, hpoint, hcmp⟩ :=
    hstep.exists_smoothCommonModel hK
  refine ⟨W, inferInstance, inferInstance, inferInstance, r, q, hr, hq, hrP, hqP, hcomm, hWsm,
    fun w hw => ?_⟩
  obtain ⟨E, hE0, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hpoint w hw)
  refine ⟨E, hwE, fun n D D' a a' hv hv' ha ha' => ?_⟩
  have hEv := valuation_ofPrimeDivisor hW E
  refine (hcmp (DivisorOver.ofPrimeDivisor ℂ hW E) D D' n a a' (inferInstanceAs (IsProper (𝟙 W)))
    (by rw [hEv]; exact hv) (by rw [hEv]; exact hv') ha ha').2 ?_
  exact DivisorWithCoeffs.mem_supp_iff.mpr
    ⟨E, hE0, MMP.Flips.primeDivisor_genericPoint_mem_support E⟩

end Comparison

/-! ### `ℚ`-factorial varieties -/

section QFactorial

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- Dividing the coefficient by `m` undoes the multiple `m D`:
`(c / m) • (m D) = c • D` for `m > 0`. -/
private theorem div_smul_toRDivisor_zsmul {X : Scheme.{u}} (c : ℝ) {m : ℕ} (hm : 0 < m)
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

/-- **Effective boundaries lower log discrepancies** on a `ℚ`-factorial variety:
`a(E, X, B) ≤ a(E, X, 0)` for an effective `ℝ`-divisor `B`. -/
private theorem isLogDiscrepancy_le_of_isQFactorial (hX : IsNormalVariety ℂ sX)
    (hq : IsQFactorial sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB : 0 ≤ B) {E : DivisorOver ℂ sX} (hEp : IsProper E.f) {a a₀ : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E a)
    (ha₀ : MMP.Intersection.IsLogDiscrepancy sX n 0 E a₀) : a ≤ a₀ := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hX hK
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sX n := hdiv ▸ hK
  have hF := isDiscrepancy_of_isLogDiscrepancy ha hω0 hKω
    (isCartierCombination_of_isQFactorial hq _)
  have hF₀ := isDiscrepancy_of_isLogDiscrepancy ha₀ hω0 hKω
    (isCartierCombination_of_isQFactorial hq _)
  obtain ⟨m, r, L, hLc, hBeq⟩ := exists_presentation_of_isQFactorial hq B
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  have hmult : IsMultiplicityAlong sX (B - 0) r L (⟨E, hEp⟩ : ProperDivisorOver ℂ sX).valuation
      ⟨E, hEp⟩ (∑ j, r j * ((L' j).coeff E.E : ℝ)) :=
    ⟨hX, hasNonemptyCenter_valuation ⟨E, hEp⟩, rfl, hLc, by rw [sub_zero]; exact hBeq, L',
      fun j => ⟨_, hL' j⟩, rfl⟩
  have hμ := IsMultiplicityAlong.nonneg hmult (by rw [sub_zero]; exact hB)
  have h1 := IsDiscrepancy.sub_of_isMultiplicityAlong hF₀ hmult
  have h2 := h1.eq hF
  linarith

end QFactorial

/-! ### The log discrepancy of the blow-up of a regular codimension-two centre -/

section BlowupDiscrepancy

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **The blow-up of a regular codimension-two centre.** Let `X` be a `ℚ`-factorial normal
variety, `W ⊆ X` an irreducible closed subset of codimension two at whose generic point `X` is
regular, and `E` a proper divisor over `X` with the valuation of the exceptional divisor of the
blow-up of `W`. Then for every `ℝ`-divisor `B = ∑ b_P P`,
`a(E, X, B) = 2 - ∑ b_P mult_W P`. -/
private theorem isLogDiscrepancy_blowUp (hX : IsNormalVariety ℂ sX) (hq : IsQFactorial sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (B : RDivisor X)
    (Wc : IrreducibleCloseds X) (hc2 : codimension Wc = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk Wc.isIrreducible.genericPoint))
    (D : DivisorOver ℂ sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨Wc, Wc.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j] (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hDη : D.f D.E.genericPoint = Wc.isIrreducible.genericPoint)
    (E : DivisorOver ℂ sX) (hEp : IsProper E.f) (hEv : E.valuation = D.valuation) :
    MMP.Intersection.IsLogDiscrepancy sX n B E
      (2 - ∑ P ∈ B.support, ((P.multiplicityAlong Wc).toNat : ℝ) * B.coeff P) := by
  classical
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  set μP : MMP.Mori.PrimeDivisor X → ℝ := fun P => ((P.multiplicityAlong Wc).toNat : ℝ)
  -- the log discrepancy for a `ℚ`-boundary
  have hmori : ∀ B₀ : QDivisor X, (Divisor.toQDivisor K + B₀).IsQCartier →
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B₀) E
        (2 - ((B₀.sum fun Γ b => b * ((Γ.multiplicityAlong Wc).toNat : ℚ) : ℚ) : ℝ)) := by
    intro B₀ hB₀
    have h1 := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing sX hX hK B₀ hB₀ Wc (c := 2)
      (by rw [hc2]; rfl) le_rfl hreg D j hj hDη
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hX, n, K, hK, hB₀⟩ hK E
    have heq := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX, hK, hB₀⟩ hEv.symm h1 hc
    have h2 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hEp
    convert h2 using 1
    rw [← heq]
    push_cast
    ring
  -- the forms
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hX hK
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sX n := hdiv ▸ hK
  have hKC : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + 0) := by
    obtain ⟨m, hm, hmK⟩ := hq.2 K
    refine ⟨1, fun _ => (1 / (m : ℝ)), fun _ => (m : ℤ) • K, fun _ => hmK, ?_⟩
    rw [hdiv, add_zero, Fin.sum_univ_one, ← MMP.Flips.toRDivisor_eq_mapCoeffs,
      div_smul_toRDivisor_zsmul 1 hm, one_smul]
  -- the empty boundary: `a(E, X, 0) = 2`
  have hK0 : (Divisor.toQDivisor K + 0).IsQCartier := isQCartier_of_isQFactorial sX hq _
  have ha0 := hmori 0 hK0
  simp only [map_zero, Finsupp.sum_zero_index, Rat.cast_zero, sub_zero] at ha0
  have hF0 := isDiscrepancy_of_isLogDiscrepancy ha0 hω0 hKω hKC
  -- Cartier multiples of the prime divisors and their pull-backs
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hq.2 (Finsupp.single P 1)
  set L' : MMP.Mori.PrimeDivisor X → Divisor E.Y := fun P =>
    Divisor.pullback ((mq P : ℤ) • Finsupp.single P 1) (hmqC P)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f _)
  have hL'pb : ∀ P, ∃ hB, Divisor.IsPullback E.f ((mq P : ℤ) • Finsupp.single P 1) hB (L' P) :=
    fun P => ⟨_, Divisor.isPullback_pullback _ _⟩
  have hcenter : HasNonemptyCenter ℂ sX (⟨E, hEp⟩ : ProperDivisorOver ℂ sX).valuation :=
    hasNonemptyCenter_valuation ⟨E, hEp⟩
  -- the multiplicity along `E` of each prime divisor is `mult_W P`
  have hμP : ∀ P : MMP.Mori.PrimeDivisor X,
      (1 / (mq P : ℝ)) * ((L' P).coeff E.E : ℝ) = μP P := by
    intro P
    have hKP : (Divisor.toQDivisor K + Divisor.toQDivisor (Finsupp.single P 1)).IsQCartier :=
      MMP.Fourfold.isQCartier_of_isQFactorial sX hq _
    have haP := hmori _ hKP
    have hsumP : ((Divisor.toQDivisor (Finsupp.single P 1 : Divisor X)).sum fun Γ b =>
        b * ((Γ.multiplicityAlong Wc).toNat : ℚ)) = ((P.multiplicityAlong Wc).toNat : ℚ) := by
      have hsq : Divisor.toQDivisor (Finsupp.single P 1 : Divisor X) =
          Finsupp.single P (1 : ℚ) := by
        refine DivisorWithCoeffs.ext' fun Q => ?_
        rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
          Finsupp.single_apply, Finsupp.single_apply]
        split_ifs <;> simp
      rw [hsq, Finsupp.sum_single_index (by simp), one_mul]
    rw [hsumP, QDivisor.toRDivisor_toQDivisor] at haP
    have hFP := isDiscrepancy_of_isLogDiscrepancy haP hω0 hKω (by
      obtain ⟨m, r, L, hLc, hsum⟩ := hKC
      have hsum' : Divisor.toRDivisor (divisorOfForm ω) = ∑ j, r j • Divisor.toRDivisor (L j) := by
        simpa only [add_zero, MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum
      refine ⟨m + 1, Fin.snoc r (1 / (mq P : ℝ)), Fin.snoc L ((mq P : ℤ) • Finsupp.single P 1),
        fun i => Fin.lastCases (by simpa using hmqC P) (fun i => by simpa using hLc i) i, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, ← MMP.Flips.toRDivisor_eq_mapCoeffs,
        div_smul_toRDivisor_zsmul 1 (hmq P), one_smul, hsum'])
    have hmult : IsMultiplicityAlong sX (Divisor.toRDivisor (Finsupp.single P 1) - 0)
        (fun _ : Fin 1 => 1 / (mq P : ℝ)) (fun _ => (mq P : ℤ) • Finsupp.single P 1)
        (⟨E, hEp⟩ : ProperDivisorOver ℂ sX).valuation ⟨E, hEp⟩
        ((1 / (mq P : ℝ)) * ((L' P).coeff E.E : ℝ)) := by
      refine ⟨hX, hcenter, rfl, fun _ => hmqC P, ?_, fun _ => L' P, fun _ => hL'pb P, by simp⟩
      rw [sub_zero, Fin.sum_univ_one, div_smul_toRDivisor_zsmul 1 (hmq P), one_smul]
    have h1 := IsDiscrepancy.sub_of_isMultiplicityAlong hF0 hmult
    have h2 := h1.eq hFP
    simp only [μP]
    push_cast at h2
    linarith
  -- the multiplicity of `B`
  set S := B.support
  set Pj : Fin S.card → MMP.Mori.PrimeDivisor X := fun j => (S.equivFin.symm j : _)
  have hmultB : IsMultiplicityAlong sX (B - 0)
      (fun j => B.coeff (Pj j) / (mq (Pj j) : ℝ))
      (fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1)
      (⟨E, hEp⟩ : ProperDivisorOver ℂ sX).valuation ⟨E, hEp⟩
      (∑ j, B.coeff (Pj j) / (mq (Pj j) : ℝ) * ((L' (Pj j)).coeff E.E : ℝ)) := by
    refine ⟨hX, hcenter, rfl, fun j => hmqC _, ?_, fun j => L' (Pj j), fun j => hL'pb _, rfl⟩
    rw [sub_zero]
    conv_lhs => rw [eq_sum_coeff_smul_single B]
    exact Finset.sum_congr rfl fun j _ => (div_smul_toRDivisor_zsmul _ (hmq _) _).symm
  have hFB := IsDiscrepancy.sub_of_isMultiplicityAlong hF0 hmultB
  have hLB := isLogDiscrepancy_of_isDiscrepancy hFB E hEp rfl
  convert hLB using 1
  have hsumB : ∑ j, B.coeff (Pj j) / (mq (Pj j) : ℝ) * ((L' (Pj j)).coeff E.E : ℝ) =
      ∑ P ∈ S, μP P * B.coeff P := by
    have : ∀ j, B.coeff (Pj j) / (mq (Pj j) : ℝ) * ((L' (Pj j)).coeff E.E : ℝ) =
        μP (Pj j) * B.coeff (Pj j) := fun j => by
      rw [← hμP (Pj j)]; ring
    simp only [this]
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp S.equivFin.symm (fun Q => μP Q * B.coeff Q)
  rw [hsumB]
  ring

end BlowupDiscrepancy

/-! ### Regularity at a terminal codimension-two point -/

section Regularity

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **A codimension-two point at which every centred divisor is terminal is regular** (on a real
canonical pair with `ℚ`-factorial base). The finitely many non-terminal valuations
(`a(v, X, B) ≤ 1 < 2 - d`) have centres missing `η`, so on the complementary open `U ∋ η` the
variety is terminal: every exceptional divisor over `U` has discrepancy `> 0`, hence `≥ 1/m`.
Terminal varieties are smooth in codimension two (Kollár–Mori 5.18). -/
private theorem isRegularLocalRing_of_forall_one_lt [CompactSpace X] {B : RDivisor X}
    (hc : IsRealCanonicalPair sX B) (hq : IsQFactorial sX) {η : X}
    (hco : Order.coheight η = 2)
    (hη : ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), IsProper E.f → E.IsExceptional →
      E.f E.E.genericPoint = η → MMP.Intersection.IsLogDiscrepancy sX n B E a → 1 < a) :
    IsRegularLocalRing (X.presheaf.stalk η) := by
  classical
  have hc0 := hc
  obtain ⟨hX, hcoef, ⟨n, K, hK, hKB⟩, -⟩ := hc0
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hB0 : 0 ≤ B := coeff_nonneg_of_isRealCanonicalPair hc
  -- the forms and the real log discrepancies
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hX hK
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sX n := hdiv ▸ hK
  have hlog : ∀ E : DivisorOver ℂ sX, IsProper E.f →
      ∃ a, MMP.Intersection.IsLogDiscrepancy sX n B E a := fun E hE =>
    exists_isLogDiscrepancy hX hω0 hKω (isCartierCombination_of_isQFactorial hq _) E hE
  -- the non-terminal valuations
  set N₁ : Set (Valuation X.functionField ℤᵐ⁰) := {v | ∃ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ),
    E.IsExceptional ∧ E.valuation = v ∧ MMP.Intersection.IsLogDiscrepancy sX m B E a ∧ a ≤ 1}
  have hd1 : realThresholdMax B < 1 := realThresholdMax_lt_one hcoef
  have hN₁ : N₁.Finite := (finite_logDiscrepancyLtSet sX B hc le_rfl).subset
    fun v ⟨m, E, a, hE, hv, ha, ha1⟩ => ⟨m, E, a, hE, hv, ha, by linarith⟩
  set Zc : Valuation X.functionField ℤᵐ⁰ → Set X := fun v =>
    closure {x | ∃ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional ∧ E.valuation = v ∧
      MMP.Intersection.IsLogDiscrepancy sX m B E a ∧ a ≤ 1 ∧ E.f E.E.genericPoint = x}
  have hηZ : ∀ v ∈ N₁, η ∉ Zc v := by
    rintro v ⟨m₀, E₀, a₀, hE₀, hv₀, ha₀, ha₀1⟩ hηv
    have hsub : {x | ∃ (m : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional ∧
        E.valuation = v ∧ MMP.Intersection.IsLogDiscrepancy sX m B E a ∧ a ≤ 1 ∧
        E.f E.E.genericPoint = x} ⊆ {E₀.f E₀.E.genericPoint} := by
      rintro x ⟨m, E, a, -, hv, -, -, rfl⟩
      exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 (hv.trans hv₀.symm)
    have hsp : E₀.f E₀.E.genericPoint ⤳ η :=
      specializes_iff_mem_closure.mpr (closure_mono hsub hηv)
    have h2 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX E₀).mp hE₀
    by_cases heq : E₀.f E₀.E.genericPoint = η
    · exact absurd (hη m₀ E₀ a₀ ha₀.2.1 hE₀ heq ha₀) (not_lt.mpr ha₀1)
    · have hle : η ≤ E₀.f E₀.E.genericPoint := hsp
      have hlt : η < E₀.f E₀.E.genericPoint :=
        lt_of_le_not_ge hle fun h => heq (hsp.antisymm h).eq
      have hfin : Order.coheight (E₀.f E₀.E.genericPoint) < ⊤ :=
        lt_of_le_of_lt (Order.coheight_anti hle) (by rw [hco]; exact ENat.coe_lt_top 2)
      have := Order.coheight_strictAnti hlt hfin
      rw [hco] at this
      exact absurd (lt_of_le_of_lt h2 this) (lt_irrefl _)
  -- the open set `U ∋ η`
  have hBd : IsClosed (⋃ v ∈ N₁, Zc v) := hN₁.isClosed_biUnion fun v _ => isClosed_closure
  set U : X.Opens := ⟨(⋃ v ∈ N₁, Zc v)ᶜ, hBd.isOpen_compl⟩ with hU
  have hηU : η ∈ U := by
    change η ∉ ⋃ v ∈ N₁, Zc v
    simp only [Set.mem_iUnion, not_exists]
    exact fun v hv => hηZ v hv
  haveI : Nonempty U := ⟨⟨η, hηU⟩⟩
  -- `(U, 0)` is terminal
  have hK0 : (Divisor.toQDivisor K + 0).IsQCartier := isQCartier_of_isQFactorial sX hq _
  have hPW : IsPairWith sX n K 0 := ⟨hX, hK, hK0⟩
  obtain ⟨m, hm, hmC⟩ := hK0.exists_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hres0 : (0 : QDivisor X).restrictOpen U = 0 := by
    ext W; rfl
  have hterm : IsTerminalPair (U.ι ≫ sX) n (K.restrictOpen U) 0 := by
    have hPU := hPW.restrictOpen U
    rw [hres0] at hPU
    refine ⟨hPU, lt_of_lt_of_le (b := (((1 : ℝ) / m : ℝ) : EReal))
      (by exact_mod_cast (by positivity : (0 : ℝ) < 1 / m))
      (le_discrep_iff.mpr fun D a hD ha => ?_)⟩
    obtain ⟨D₁, hD₁x, -, hD₁U, hD₁a⟩ := hPW.exists_isDiscrepancy_of_restrictOpen U hD (by
      rw [hres0]; exact ha)
    -- `a ∈ (1/m) ℤ`
    obtain ⟨-, V, hxV, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hPW.isPair hK hmC
      (D₁.f D₁.E.genericPoint)
    have ha' : IsDiscrepancy sX n K 0 D₁ (D₁.ordPullback τ / m) := by
      refine ⟨hX, hK, m, hm, hmC, V, hxV, τ, hτ, ?_⟩
      have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    have heq : a = D₁.ordPullback τ / m := hD₁a.eq ha'
    -- `a > 0`
    obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D₁
    have hEc : E.f E.E.genericPoint = D₁.f D₁.E.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hE
    have hEx : E.toDivisorOver.IsExceptional := by
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX]
      rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX] at hD₁x
      change 2 ≤ Order.coheight (E.f E.E.genericPoint)
      rwa [hEc]
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK E.toDivisorOver
    have hab : a = b := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hE.symm hD₁a hb
    have hlog0 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb E.isProper
    rw [map_zero] at hlog0
    obtain ⟨aB, haB⟩ := hlog E.toDivisorOver E.isProper
    have hle := isLogDiscrepancy_le_of_isQFactorial hX hq hK hB0 E.isProper haB hlog0
    have hpos : (0 : ℚ) < a := by
      by_contra hneg
      push Not at hneg
      have hb0 : (b : ℝ) ≤ 0 := by exact_mod_cast hab ▸ hneg
      have hvN : E.valuation ∈ N₁ := ⟨n, E.toDivisorOver, aB, hEx, rfl, haB, by linarith⟩
      have hcZ : E.f E.E.genericPoint ∈ Zc E.valuation :=
        subset_closure ⟨n, E.toDivisorOver, aB, hEx, rfl, haB, by linarith, rfl⟩
      have hcU : E.f E.E.genericPoint ∈ U := by
        obtain ⟨y, hyc, hyU⟩ := hD₁U
        rw [D₁.center_eq_closure_genericPoint] at hyc
        rw [hEc]
        exact (specializes_iff_mem_closure.mpr hyc).mem_open U.isOpen hyU
      exact hcU (Set.mem_biUnion hvN hcZ)
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have hord : (1 : ℤ) ≤ D₁.ordPullback τ := by
      exact_mod_cast (div_pos_iff_of_pos_right hmq).mp (heq ▸ hpos)
    have hge : (1 : ℚ) / m ≤ a :=
      heq ▸ div_le_div_of_nonneg_right (by exact_mod_cast hord) hmq.le
    have : ((1 : ℝ) / m) ≤ (a : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hge
    exact_mod_cast this
  -- terminal varieties are smooth in codimension two
  let x : U.toScheme := ⟨η, hηU⟩
  have hcox : Order.coheight x = 2 := by
    have h := hco
    rwa [show η = U.ι x from rfl, Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding] at h
  have hsm : x ∈ MMP.Mori.smoothLocus (U.ι ≫ sX) := by
    by_contra hns
    have h3 := MMP.Mori.IsTerminalPair.three_le_coheight_of_mem_singularLocus hterm hns
    rw [hcox] at h3
    exact absurd h3 (by decide)
  obtain ⟨V, hxV, hV⟩ := MMP.Mori.mem_smoothLocus_iff.mp hsm
  have : Smooth (V.ι ≫ U.ι ≫ sX) := hV
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ U.ι ≫ sX) ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv
    ((V.stalkIso ⟨x, hxV⟩).commRingCatIsoToRingEquiv.trans
      (U.stalkIso x).commRingCatIsoToRingEquiv)

end Regularity

/-! ### Transporting valuations across a flip -/

section Transport

/-- **Transport of valuations.** For birational morphisms `f : X ⟶ Z ⟵ X⁺ : f⁺` there is an
injective map `T` from the valuations of `k(X⁺)` to those of `k(X)` with `T(v)` the valuation
agreeing with `v` on `k(Z)`. -/
private theorem exists_transport {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    [IsIntegral Z] {f : X ⟶ Z} {fp : X' ⟶ Z} [IsDominant f] [IsDominant fp]
    (hf : Function.Bijective (functionFieldMap f))
    (hfp : Function.Bijective (functionFieldMap fp)) :
    ∃ T : Valuation X'.functionField ℤᵐ⁰ → Valuation X.functionField ℤᵐ⁰, T.Injective ∧
      ∀ (w : Valuation X.functionField ℤᵐ⁰) (v : Valuation X'.functionField ℤᵐ⁰),
        w.comap (functionFieldMap f) = v.comap (functionFieldMap fp) → w = T v := by
  let ef := RingEquiv.ofBijective (functionFieldMap f) hf
  let g : X.functionField →+* X'.functionField :=
    (functionFieldMap fp).comp ef.symm.toRingHom
  have hg : ∀ t, g (functionFieldMap f t) = functionFieldMap fp t := fun t => by
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    congr 1
    exact ef.symm_apply_apply t
  have hgs : Function.Surjective g := fun y => by
    obtain ⟨t, rfl⟩ := hfp.2 y
    exact ⟨_, hg t⟩
  refine ⟨fun v => v.comap g, fun v₁ v₂ h => ?_, fun w v h => ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := hgs y
    exact congrArg (fun v : Valuation X.functionField ℤᵐ⁰ => v x) h
  · ext x
    obtain ⟨t, rfl⟩ := hf.2 x
    have := congrArg (fun v : Valuation Z.functionField ℤᵐ⁰ => v t) h
    simp only [Valuation.comap_apply] at this ⊢
    rw [this, hg]

end Transport

/-! ### Counting -/

section Counting

/-- An injection of the threshold sets bounds the disjoint unions. -/
private theorem encard_le_of_injective {α β : Type*} (S : Set ℝ) (E : ℝ → Set α)
    (E' : ℝ → Set β) (T : β → α) (hT : T.Injective) (h : ∀ s ∈ S, T '' E' s ⊆ E s) :
    (⋃ s ∈ S, {s} ×ˢ E' s).encard ≤ (⋃ s ∈ S, {s} ×ˢ E s).encard := by
  rw [← (Function.injective_id.prodMap hT).encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨⟨s, v⟩, hv, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, exists_prop] at hv ⊢
  obtain ⟨s', hs', rfl, hv⟩ := hv
  exact ⟨s, hs', rfl, h s hs' ⟨v, hv, rfl⟩⟩

/-- An injection of the threshold sets missing one element of a finite target is strict. -/
private theorem encard_lt_of_injective {α β : Type*} (S : Set ℝ) (E : ℝ → Set α)
    (E' : ℝ → Set β) (T : β → α) (hT : T.Injective) (h : ∀ s ∈ S, T '' E' s ⊆ E s)
    (hfin : (⋃ s ∈ S, {s} ×ˢ E s).encard ≠ ⊤) {s₀ : ℝ} (hs₀ : s₀ ∈ S) {v₀ : α}
    (hv₀ : v₀ ∈ E s₀) (hv₀' : v₀ ∉ T '' E' s₀) :
    (⋃ s ∈ S, {s} ×ˢ E' s).encard < (⋃ s ∈ S, {s} ×ˢ E s).encard := by
  rw [← (Function.injective_id.prodMap hT).encard_image]
  have hsub : Prod.map id T '' (⋃ s ∈ S, {s} ×ˢ E' s) ⊆ ⋃ s ∈ S, {s} ×ˢ E s := by
    rintro _ ⟨⟨s, v⟩, hv, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, exists_prop] at hv ⊢
    obtain ⟨s', hs', rfl, hv⟩ := hv
    exact ⟨s, hs', rfl, h s hs' ⟨v, hv, rfl⟩⟩
  have hfin' := Set.encard_ne_top_iff.mp hfin
  refine (hfin'.subset hsub).encard_lt_encard ⟨hsub, fun hsup => ?_⟩
  have hmem : (s₀, v₀) ∈ ⋃ s ∈ S, {s} ×ˢ E s := by
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, exists_prop]
    exact ⟨s₀, hs₀, rfl, hv₀⟩
  obtain ⟨⟨s, v⟩, hv, he⟩ := hsup hmem
  simp only [Prod.map, id, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, exists_prop] at hv
  obtain ⟨s', -, rfl, hv⟩ := hv
  exact hv₀' ⟨v, hv, rfl⟩

end Counting

/-! ### One step of the flip sequence -/

section Step

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
  {fp : X' ⟶ Z}

/-- Every proper divisor over the source of a real flip step has a log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_isRealFlipStep
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) {m : ℕ} (hK : K.IsCanonicalDivisor sX m)
    (E : DivisorOver ℂ sX) (hE : IsProper E.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX m B E a := by
  have hXv := hstep.isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hXv hK
  exact exists_isLogDiscrepancy hXv hω0 (hdiv ▸ hK)
    (by rw [hdiv]; exact hstep.isNegativeExtremalContraction.isCartierCombination) E hE

/-- Across a flip, a divisor over `X` with the same centre on `Z` as an exceptional divisor over
`X⁺` is exceptional over `X`. -/
public theorem IsRealFlipStep.isExceptional_of_map_eq
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (E : DivisorOver ℂ sX) (E' : DivisorOver ℂ sX')
    (hpt : f (E.f E.E.genericPoint) = fp (E'.f E'.E.genericPoint)) (hE' : E'.IsExceptional) :
    E.IsExceptional := by
  have hXv := hstep.isNegativeExtremalContraction.isNormalVariety_source
  have hX'v : IsNormalVariety ℂ sX' := ⟨hstep.isSmall_flip.isVariety_source, inferInstance⟩
  by_contra hE
  obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hXv hE
  have hEQ : E.f E.E.genericPoint = Q.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
  obtain ⟨hz1, -⟩ := coheight_map_genericPoint_of_isSmall hstep.isSmall Q
  have hb := mem_biregularLocus_of_isSmall hstep.isSmall_flip hz1.le
  rw [← hEQ, hpt] at hz1 hb
  have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb
  rw [hz1] at h1
  have h2 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX'v E').mp hE'
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- The ideal of a prime divisor at a point of an integral scheme is nonzero. -/
private theorem stalkIdeal_ne_bot {Y : Scheme} [IsIntegral Y] (D : MMP.Mori.PrimeDivisor Y)
    (x : Y) : D.idealSheaf.stalkIdeal x ≠ ⊥ := by
  have hD : D.idealSheaf ≠ ⊥ := by
    intro h0
    have hsupp : D.support = Set.univ := by
      change ((D.idealSheaf.support : Set Y)) = _
      rw [h0, Scheme.IdealSheafData.support_bot]; rfl
    have hgen : IsGenericPoint D.genericPoint (Set.univ : Set Y) := by
      rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    have h1 := D.coheight_genericPoint
    have h2 : Order.coheight D.genericPoint = 0 := by
      rw [Order.coheight_eq_zero]
      intro b hb
      have hb' : b ⤳ D.genericPoint := hb
      have hbgen : IsGenericPoint b (Set.univ : Set Y) := by
        refine (isGenericPoint_iff_specializes).mpr fun w => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        exact hb'.trans (hgen.specializes (Set.mem_univ w))
      exact (hbgen.eq hgen).symm ▸ le_rfl
    rw [h2] at h1
    exact absurd h1 (by decide)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hne := Stacks.IdealSheaf.ideal_ne_bot D.idealSheaf hD (U := ⟨V, hV⟩) hxV
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro h0
  have h1 := D.idealSheaf.germ_mem_stalkIdeal ⟨V, hV⟩ hxV hg
  rw [h0, Ideal.mem_bot] at h1
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact hg0 (germ_injective_of_isIntegral Y x hxV (h1.trans (map_zero _).symm))

/-- A prime divisor through the generic point of `W` has finite positive multiplicity along `W`
(Krull's intersection theorem in the noetherian local ring at `η_W`). -/
private theorem one_le_toNat_multiplicityAlong {Y : Scheme} [IsIntegral Y]
    [IsLocallyNoetherian Y] (P : MMP.Mori.PrimeDivisor Y) (W : IrreducibleCloseds Y)
    (h : W.isIrreducible.genericPoint ∈ (P.support : Set Y)) :
    1 ≤ (P.multiplicityAlong W).toNat := by
  set R := Y.presheaf.stalk W.isIrreducible.genericPoint
  set I := P.idealSheaf.stalkIdeal W.isIrreducible.genericPoint
  have hI0 : I ≠ ⊥ := stalkIdeal_ne_bot P _
  have hIm : I ≤ IsLocalRing.maximalIdeal R :=
    P.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support h
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ¬ I ≤ IsLocalRing.maximalIdeal R ^ s := by
    by_contra! hall
    apply hI0
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    exact le_iInf hall
  have hle : P.multiplicityAlong W ≤ s := iSup₂_le fun t ht => by
    have : t < s := by
      by_contra! hst
      exact hs (ht.trans (Ideal.pow_le_pow_right hst))
    exact_mod_cast this.le
  have h1 : (1 : ℕ∞) ≤ P.multiplicityAlong W :=
    le_iSup₂_of_le (f := fun (s : ℕ) (_ : I ≤ IsLocalRing.maximalIdeal R ^ s) => (s : ℕ∞)) 1
      (by simpa using hIm) le_rfl
  have hne : P.multiplicityAlong W ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top s) hle
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at h1 ⊢
  rw [ENat.toNat_coe]
  exact_mod_cast h1

/-- A subset of positive topological Krull dimension has two distinct points. -/
private theorem nontrivial_of_topologicalKrullDim_pos {α : Type*} [TopologicalSpace α]
    {T : Set α} (h : 0 < topologicalKrullDim T) : T.Nontrivial := by
  obtain ⟨A, B, hAB⟩ := Order.krullDim_pos_iff.mp h
  obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
  have hsub : (A : Set T) ⊂ B := hAB
  obtain ⟨b, hbB, hbA⟩ := Set.exists_of_ssubset hsub
  exact ⟨a.1, a.2, b.1, b.2, fun hab => hbA (Subtype.ext hab ▸ ha)⟩

/-- **The blow-up of a flipped curve.** For a flipped curve `C` of a step of a real flip sequence
of real canonical `ℚ`-factorial threefolds, with `m_P = mult_C P`, there is an exceptional proper
divisor `E_C` over `X⁺` whose log discrepancy is `2 - ∑ m_P b_P` (so `∑ m_P b_P ≤ 1`), and whose
centre on `Z` is a closed point over which `f⁺` contracts a proper curve. -/
private theorem exists_flippedCurve_divisorOver
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m, K.IsCanonicalDivisor sX m)
    (hc : IsRealCanonicalPair sX B) (hc' : IsRealCanonicalPair sX' B')
    (hq' : IsQFactorial sX') (hd' : topologicalKrullDim X' = 3) (C : Set X')
    (hC : MMP.Flips.IsFlippingCurve ℂ sX' sZ fp C) :
    ∃ m : MMP.Mori.PrimeDivisor X' → ℕ, (∀ P, C ⊆ (P.support : Set X') → 1 ≤ m P) ∧
      ∃ E' : DivisorOver ℂ sX', IsProper E'.f ∧ E'.IsExceptional ∧
        (∃ n, MMP.Intersection.IsLogDiscrepancy sX' n B' E'
          (2 - ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P)) ∧
        (∃ Γ : ProperCurve sX', Γ.IsContractedBy fp ∧
          fp Γ.point = fp (E'.f E'.E.genericPoint)) ∧
        IsClosed {fp (E'.f E'.E.genericPoint)} := by
  classical
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hXv := hstep.isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hX'v : IsNormalVariety ℂ sX' := hc'.1
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  obtain ⟨-, -, hcomp, hprop, z, hzc, hmax, hdim⟩ := hC
  haveI : IsProper fp := hprop
  -- `C` is closed and irreducible
  have hFc : IsClosed {x : X' | fp x = z} := hzc.preimage fp.continuous
  have hCcl : IsClosed C := by
    have : closure C ⊆ C := hmax.2 ⟨hmax.1.1.closure, closure_minimal hmax.1.2 hFc⟩ subset_closure
    exact closure_subset_iff_isClosed.mp this
  set Wc : IrreducibleCloseds X' := ⟨C, hmax.1.1, hCcl⟩
  set η := Wc.isIrreducible.genericPoint with hηdef
  have hηgen : IsGenericPoint η C := Wc.isIrreducible.isGenericPoint_genericPoint_closure.trans
    hCcl.closure_eq
  have hηC : η ∈ C := hηgen.mem
  have hηz : fp η = z := hmax.1.2 hηC
  have hCnt := nontrivial_of_topologicalKrullDim_pos hdim
  -- a closed point `p ≠ η` of `C`
  haveI : CompactSpace X' := inferInstance
  obtain ⟨p, hpC, hpc⟩ := hCcl.exists_closed_singleton hmax.1.1.nonempty
  have hpη : η ≠ p := by
    rintro rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hCnt
    have hC1 : C = {η} := by rw [← hηgen.def, hpc.closure_eq]
    rw [hC1] at ha hb
    exact hab (ha.trans hb.symm)
  obtain ⟨Γ, hΓc, hΓz⟩ := exists_properCurve_isContractedBy_of_specializes ℂ sX' sZ hX'v hZ fp
    hcomp hzc (hηgen.specializes hpC) hpc hpη hηz (hmax.1.2 hpC)
  -- `η` has codimension two
  have hco : Order.coheight η = 2 := by
    refine le_antisymm ?_ ?_
    · have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' η
      rw [hηgen.def, hd'] at h
      by_contra hlt
      push Not at hlt
      have hdim' := hdim
      generalize topologicalKrullDim C = d at h hdim'
      generalize Order.coheight η = c at h hlt
      induction d using WithBot.recBotCoe with
      | bot => exact absurd hdim' (by simp)
      | coe d =>
        have h0' : ((d + c : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
          rw [WithBot.coe_add]; exact h
        have h0 : d + c = 3 := WithBot.coe_injective h0'
        have hd0 : 0 < d := by exact_mod_cast hdim'
        induction d using ENat.recTopCoe with
        | top => exact absurd h0 (by simp)
        | coe d =>
          induction c using ENat.recTopCoe with
          | top => exact absurd h0 (by simp)
          | coe c =>
            have h'' : d + c = 3 := by exact_mod_cast h0
            have hd0' : 0 < d := by exact_mod_cast hd0
            have hc2 : 2 < c := by exact_mod_cast hlt
            omega
    · obtain ⟨V, W, hV, -, hVW, hiso⟩ := exists_closeds_isIso_of_isSmall hstep.isSmall_flip
      by_contra hlt
      push Not at hlt
      by_cases hηV : η ∈ (V : Set X')
      · exact absurd (hV η hηV) (not_le.mpr hlt)
      · have hηU : η ∈ fp ⁻¹ᵁ W.compl := hVW hηV
        have hinj : Set.InjOn fp (fp ⁻¹ᵁ W.compl : Set X') := by
          intro a ha b hb hab
          let a' : (fp ⁻¹ᵁ W.compl).toScheme := ⟨a, ha⟩
          let b' : (fp ⁻¹ᵁ W.compl).toScheme := ⟨b, hb⟩
          have e1 := morphismRestrict_base_coe fp W.compl a'
          have e2 := morphismRestrict_base_coe fp W.compl b'
          have := (fp ∣_ W.compl).isOpenEmbedding.injective
            (Subtype.ext (e1.trans (hab.trans e2.symm)) : (fp ∣_ W.compl) a' = (fp ∣_ W.compl) b')
          exact congrArg Subtype.val this
        obtain ⟨a, ha, b, hb, hab⟩ := hCnt
        have hU : ∀ c ∈ C, c ∈ (fp ⁻¹ᵁ W.compl : Set X') := fun c hc => by
          change fp c ∈ (W.compl : Set Z)
          rw [hmax.1.2 hc, ← hηz]; exact hηU
        exact hab (hinj (hU a ha) (hU b hb) ((hmax.1.2 ha).trans (hmax.1.2 hb).symm))
  -- every divisor over `X⁺` centred at `η` is terminal
  obtain ⟨m₀, hK0⟩ := hK
  have hlog := exists_isLogDiscrepancy_of_isRealFlipStep hstep hK0
  have hη : ∀ (n : ℕ) (E' : DivisorOver ℂ sX') (a' : ℝ), IsProper E'.f → E'.IsExceptional →
      E'.f E'.E.genericPoint = η → MMP.Intersection.IsLogDiscrepancy sX' n B' E' a' → 1 < a' := by
    intro n E' a' hE'p hE'x hE'η ha'
    obtain ⟨E, hEp, -, hpt, hcmp⟩ := hstep.exists_isLogDiscrepancy_le ⟨m₀, hK0⟩ E' hE'p
    obtain ⟨a, ha⟩ := hlog E hEp
    have h1 := hc.2.2.2 m₀ E a (hstep.isExceptional_of_map_eq E E' hpt hE'x) ha
    have h2 := (hcmp m₀ n a a' ha ha').2 ⟨Γ, hΓc, by rw [hΓz, hE'η, hηz]⟩
      (by rw [hE'η, hηz]; exact hzc)
    linarith
  have hreg := isRegularLocalRing_of_forall_one_lt hc' hq' hco hη
  -- the blow-up of `C`
  have hc2 : codimension Wc = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]; exact hco
  obtain ⟨D, j, hjo, hj, hDη⟩ := (MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp
    sX' hX'v Wc hc2.ge hreg).1
  obtain ⟨E', hE'⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX'v D
  have hE'c : E'.f E'.E.genericPoint = η :=
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'v.1 hE').trans hDη
  obtain ⟨-, -, ⟨n', K'', hK'', -⟩, -⟩ := hc'
  refine ⟨fun P => (P.multiplicityAlong Wc).toNat, fun P hP =>
    one_le_toNat_multiplicityAlong P Wc (hP hηC), E'.toDivisorOver, E'.isProper, ?_,
    ⟨n', isLogDiscrepancy_blowUp hX'v hq' hK'' B' Wc hc2 hreg D j hj hDη E'.toDivisorOver
      E'.isProper hE'⟩, ⟨Γ, hΓc, ?_⟩, ?_⟩
  · rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX'v]
    change 2 ≤ Order.coheight (E'.f E'.E.genericPoint)
    rw [hE'c, hco]
  · change fp Γ.point = fp (E'.f E'.E.genericPoint)
    rw [hE'c, hηz, hΓz]
  · change IsClosed {fp (E'.f E'.E.genericPoint)}
    rw [hE'c, hηz]; exact hzc

/-- **Transport of the threshold sets along a flip.** The identification `k(X⁺) ≅ k(X)` over
`k(Z)` maps every `𝓔_u(X⁺, B⁺)` into `𝓔_u(X, B)`; and for every flipped curve `C`, with
`m_P = mult_C P`, the valuation of the blow-up of `C` lies in `𝓔_{2 - s}(X, B)` but its preimage
does not lie in `𝓔_{2 - s}(X⁺, B⁺)`, where `s = ∑ m_P b_P ≤ 1`. -/
private theorem exists_transport_of_isRealFlipStep
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m, K.IsCanonicalDivisor sX m)
    (hc : IsRealCanonicalPair sX B) (hc' : IsRealCanonicalPair sX' B')
    (hq' : IsQFactorial sX') (hd' : topologicalKrullDim X' = 3) :
    ∃ T : Valuation X'.functionField ℤᵐ⁰ → Valuation X.functionField ℤᵐ⁰, T.Injective ∧
      (∀ u, T '' logDiscrepancyLtSet sX' B' u ⊆ logDiscrepancyLtSet sX B u) ∧
      ∀ C : Set X', MMP.Flips.IsFlippingCurve ℂ sX' sZ fp C →
        ∃ m : MMP.Mori.PrimeDivisor X' → ℕ, (∀ P, C ⊆ (P.support : Set X') → 1 ≤ m P) ∧
          (∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P) ≤ 1 ∧
          ∃ v ∈ logDiscrepancyLtSet sX B (2 - ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P),
            v ∉ T '' logDiscrepancyLtSet sX' B' (2 - ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P) := by
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hXv := hstep.isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hfb := hstep.isBirationalMorphism
  have hfpb := hstep.isBirationalMorphism_flip
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  obtain ⟨T, hT, hTchar⟩ := exists_transport hfb.functionFieldMap_bijective
    hfpb.functionFieldMap_bijective
  -- every proper divisor over `X` has a log discrepancy
  obtain ⟨m₀, hK0⟩ := hK
  have hlog := exists_isLogDiscrepancy_of_isRealFlipStep hstep hK0
  refine ⟨T, hT, fun u => ?_, fun C hC => ?_⟩
  · rintro _ ⟨v, ⟨n', E', a', hE'x, rfl, ha', hlt⟩, rfl⟩
    obtain ⟨E, hEp, hval, hpt, hcmp⟩ := hstep.exists_isLogDiscrepancy_le ⟨m₀, hK0⟩ E' ha'.2.1
    obtain ⟨a, ha⟩ := hlog E hEp
    exact ⟨m₀, E, a, hstep.isExceptional_of_map_eq E E' hpt hE'x, hTchar _ _ hval, ha,
      lt_of_le_of_lt (hcmp m₀ n' a a' ha ha').1 hlt⟩
  · obtain ⟨m, hm1, E', hE'p, hE'x, ⟨n', ha'⟩, hΓ, hzc⟩ :=
      exists_flippedCurve_divisorOver hstep ⟨m₀, hK0⟩ hc hc' hq' hd' C hC
    set s := ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P
    have hs1 : s ≤ 1 := by
      have := hc'.2.2.2 n' E' _ hE'x ha'
      linarith
    obtain ⟨E, hEp, hval, hpt, hcmp⟩ := hstep.exists_isLogDiscrepancy_le ⟨m₀, hK0⟩ E' hE'p
    obtain ⟨a, ha⟩ := hlog E hEp
    refine ⟨m, hm1, hs1, E.valuation, ⟨m₀, E, a, hstep.isExceptional_of_map_eq E E' hpt hE'x, rfl,
      ha, (hcmp m₀ n' a _ ha ha').2 hΓ hzc⟩, ?_⟩
    rintro ⟨w, ⟨n'', E'', a'', -, rfl, ha'', hlt⟩, hw⟩
    have hwE : E''.valuation = E'.valuation := hT (hw.trans (hTchar _ _ hval))
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha'' ha' hwE
    linarith

/-- **The difficulty along one step.** It does not increase, and it drops at a flipped curve `C`
with `d ≤ ∑ m_P b_P`. -/
private theorem realCanonicalDifficulty_le_and_lt
    (hstep : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m, K.IsCanonicalDivisor sX m)
    (hc : IsRealCanonicalPair sX B) (hc' : IsRealCanonicalPair sX' B')
    (hq' : IsQFactorial sX') (hd' : topologicalKrullDim X' = 3) :
    realCanonicalDifficulty sX' B' ≤ realCanonicalDifficulty sX B ∧
      ∀ C : Set X', MMP.Flips.IsFlippingCurve ℂ sX' sZ fp C →
        ∃ m : MMP.Mori.PrimeDivisor X' → ℕ, (∀ P, C ⊆ (P.support : Set X') → 1 ≤ m P) ∧
          (realThresholdMax B' ≤ ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P →
            realCanonicalDifficulty sX' B' < realCanonicalDifficulty sX B) := by
  obtain ⟨T, hT, hsub, hC⟩ := exists_transport_of_isRealFlipStep hstep hK hc hc' hq' hd'
  have hZ := hstep.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  obtain ⟨hmax, hS⟩ := hstep.eq_flipTransform ▸ realThresholdSet_flipTransform hZ
    hstep.isSmall hstep.isSmall_flip hstep.isBirationalMorphism hstep.isBirationalMorphism_flip B
  have hS' : realThresholdSet B' = realThresholdSet B := hstep.eq_flipTransform ▸ hS
  refine ⟨?_, fun C hC' => ?_⟩
  · rw [realCanonicalDifficulty, realCanonicalDifficulty, hS']
    exact encard_le_of_injective _ _ _ T hT fun s _ => hsub (2 - s)
  · obtain ⟨m, hm1, hs1, v, hv, hv'⟩ := hC C hC'
    refine ⟨m, hm1, fun hds => ?_⟩
    rw [realCanonicalDifficulty, realCanonicalDifficulty, hS']
    refine encard_lt_of_injective _ _ _ T hT (fun s _ => hsub (2 - s))
      (realCanonicalDifficulty_ne_top sX B hc) (s₀ := ∑ P ∈ B'.support, (m P : ℝ) * B'.coeff P)
      ?_ hv hv'
    rw [← hS']
    exact ⟨⟨m, rfl⟩, hds, hs1⟩

end Step

/-! ### Flipped curves -/

section FlippedCurve

/-- A subset containing two distinct points `a ⤳ b` of a `T₀` space has positive topological
Krull dimension. -/
private theorem topologicalKrullDim_pos_of_specializes {α : Type*} [TopologicalSpace α]
    [T0Space α] {T : Set α} {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ⤳ b) (hne : a ≠ b) :
    0 < topologicalKrullDim T :=
  zero_lt_one.trans_le <| one_le_topologicalKrullDim_of_specializes_of_ne
    (x := (⟨a, ha⟩ : T)) (y := ⟨b, hb⟩)
    (Topology.IsInducing.subtypeVal.specializes_iff.mp hab) fun h => hne (congrArg Subtype.val h)

/-- A birational contraction onto a normal variety without flipping curves is an isomorphism:
an infinite fibre over a closed point has an infinite irreducible component, which has positive
dimension; so every fibre over a closed point is finite, the open finite-fibre locus contains every
closed point and is everything, and the morphism is an isomorphism over it. -/
private theorem isIso_of_forall_not_isFlippingCurve {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z} [IsNormal Z]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (hf : MMP.Flips.IsBirationalContraction k sZ sY f)
    (h : ∀ C, ¬ MMP.Flips.IsFlippingCurve k sY sZ f C) :
    IsIso f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have : IsNoetherian Y := ⟨⟩
  have hfp := hf.isProper
  have hb : IsBirational f := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hf.surjective_and_isBirational.2
  obtain ⟨hU, hI⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1 hfp
  have hall : MMP.Resolution.Bridges.finiteFibreLocus f = Set.univ := by
    by_contra hne
    have : CompactSpace Z :=
      hf.surjective_and_isBirational.1.surj.compactSpace f.continuous
    obtain ⟨z, hz, hzc⟩ := hU.isClosed_compl.exists_closed_singleton
      (Set.nonempty_compl.mpr hne)
    have hinf : (f ⁻¹' {z}).Infinite := hz
    have hFc : IsClosed (f ⁻¹' {z}) := hzc.preimage f.continuous
    obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    obtain ⟨t, htS, htinf⟩ : ∃ t ∈ S, t.Infinite := by
      by_contra! hfin
      exact hinf (hFS ▸ hSf.sUnion fun t ht => hfin t ht)
    obtain ⟨t', htt', ht'max⟩ := hSf.exists_le_maximal htS
    have ht'S : t' ∈ S := ht'max.prop
    have ha := (hScl t' ht'S).closure_eq ▸ (hSirr t' ht'S).isGenericPoint_genericPoint_closure
    obtain ⟨c, hct, hca⟩ :=
      (htinf.diff (Set.finite_singleton (hSirr t' ht'S).genericPoint)).nonempty
    have ht'F : t' ⊆ f ⁻¹' {z} := hFS ▸ Set.subset_sUnion_of_mem ht'S
    refine h t' ⟨hf.isVariety_source, hf.isVariety_target, hf.comp_eq, hfp, z, hzc,
      ⟨⟨hSirr t' ht'S, ht'F⟩, ?_⟩,
      topologicalKrullDim_pos_of_specializes ha.mem (htt' hct) (ha.specializes (htt' hct))
        fun h => hca h.symm⟩
    rintro U ⟨hUirr, hUF⟩ htU
    obtain ⟨s, hs, hUs⟩ := (isIrreducible_iff_sUnion_isClosed.mp hUirr) hSf.toFinset
      (fun s hs => hScl s (hSf.mem_toFinset.mp hs))
      (by rw [Set.Finite.coe_toFinset, ← hFS]; exact hUF)
    exact hUs.trans (ht'max.2 (hSf.mem_toFinset.mp hs) (htU.trans hUs))
  have hI' : IsIso (f ∣_ ⊤) := (show (⟨_, hU⟩ : Z.Opens) = ⊤ from Opens.ext hall) ▸ hI
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => (⊤ : Z.Opens)) (by simp)).mpr fun _ => hI'

end FlippedCurve

/-! ### The models of a real flip sequence -/

section Sequence

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X}

private theorem natCast_succ_le_iff {n : ℕ∞} {j : ℕ} :
    ((j + 1 : ℕ) : ℕ∞) ≤ n ↔ (j : ℕ∞) < n := by
  push_cast
  exact ENat.add_one_le_iff (ENat.coe_ne_top j)

/-- The canonical divisors `K_i` of the models of a real flip sequence are canonical. -/
private theorem isCanonicalDivisor_divisorSeq (σ : RealFlipSequence sX K B) :
    ∀ i : ℕ, (i : ℕ∞) ≤ σ.n →
      ∃ m, Divisor.IsCanonicalDivisor (modelStr sX σ.sY i) m (divisorSeq K σ.KY i)
  | 0, _ => σ.isCanonicalDivisor
  | j + 1, h => (σ.isRealFlipStep j (natCast_succ_le_iff.mp h)).isCanonicalDivisor_flip

/-- The boundaries of a real flip sequence starting from the empty boundary are empty. -/
private theorem divisorSeq_eq_zero (σ : RealFlipSequence sX K B) (hB : B = 0) :
    ∀ i : ℕ, (i : ℕ∞) ≤ σ.n → divisorSeq B σ.BY i = 0
  | 0, _ => hB
  | j + 1, h => by
      have hj := natCast_succ_le_iff.mp h
      change σ.BY j = 0
      rw [(σ.isRealFlipStep j hj).eq_flipTransform, divisorSeq_eq_zero σ hB j hj.le, map_zero]

end Sequence

/-! ### The main theorem -/

/-- The canonical difficulty `𝔡(W, B_W)` of every real canonical pair over `ℂ` is finite; and
along an extremal real flip sequence `σ` of real canonical pairs `(X_i, B_i)`, `𝔡(X_i, B_i)` is
nonincreasing at every step; it strictly decreases at a step `X_i ⟶ Z_i ⟵ X_{i+1}` having a
flipped curve contained in a component of
`B_{i+1}` of maximal coefficient; and, for the empty boundary, it strictly decreases at every
step. -/
@[mmp "lem_fourfold_real_canonical_difficulty_drop"]
public theorem RealFlipSequence.realCanonicalDifficulty_ne_top_and_antitone
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} (σ : RealFlipSequence sX K B)
    (hσ : ∀ i : ℕ, (i : ℕ∞) ≤ σ.n →
      IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) :
    (∀ {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
      (sW : W ⟶ Spec (.of ℂ)) (BW : RDivisor W),
      IsRealCanonicalPair sW BW → realCanonicalDifficulty sW BW ≠ ⊤) ∧
    (∀ i : ℕ, (i : ℕ∞) < σ.n →
      realCanonicalDifficulty (σ.sY i) (σ.BY i) ≤
        realCanonicalDifficulty (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) ∧
    (∀ i : ℕ, (i : ℕ∞) < σ.n → ∀ (C : Set (σ.Y i)) (P : MMP.Mori.PrimeDivisor (σ.Y i)),
      MMP.Flips.IsFlippingCurve ℂ (σ.sY i) (σ.sZ i) (σ.fp i) C →
      P ∈ (σ.BY i).support → (σ.BY i).coeff P = realThresholdMax (σ.BY i) →
      C ⊆ (P.support : Set (σ.Y i)) →
      realCanonicalDifficulty (σ.sY i) (σ.BY i) <
        realCanonicalDifficulty (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) ∧
    (B = 0 → ∀ i : ℕ, (i : ℕ∞) < σ.n →
      realCanonicalDifficulty (σ.sY i) (σ.BY i) <
        realCanonicalDifficulty (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) := by
  have hstep := fun (i : ℕ) (hi : (i : ℕ∞) < σ.n) =>
    realCanonicalDifficulty_le_and_lt (σ.isRealFlipStep i hi)
      (isCanonicalDivisor_divisorSeq σ i hi.le) (hσ i hi.le)
      (hσ (i + 1) (natCast_succ_le_iff.mpr hi))
      (σ.isQFactorial (i + 1) (natCast_succ_le_iff.mpr hi))
      (σ.dim_eq (i + 1) (natCast_succ_le_iff.mpr hi))
  have hnn : ∀ (i : ℕ), (i : ℕ∞) < σ.n → ∀ P, 0 ≤ (σ.BY i).coeff P := fun i hi =>
    coeff_nonneg_of_isRealCanonicalPair (hσ (i + 1) (natCast_succ_le_iff.mpr hi))
  refine ⟨realCanonicalDifficulty_ne_top, fun i hi => (hstep i hi).1,
    fun i hi C P hC hP hPd hCP => ?_, fun hB i hi => ?_⟩
  · obtain ⟨m, hm1, hlt⟩ := (hstep i hi).2 C hC
    refine hlt ?_
    rw [← hPd]
    have h1 : (1 : ℝ) ≤ m P := by exact_mod_cast hm1 P hCP
    calc (σ.BY i).coeff P ≤ (m P : ℝ) * (σ.BY i).coeff P := by nlinarith [hnn i hi P]
      _ ≤ ∑ Q ∈ (σ.BY i).support, (m Q : ℝ) * (σ.BY i).coeff Q :=
        Finset.single_le_sum (f := fun Q => (m Q : ℝ) * (σ.BY i).coeff Q)
          (fun Q _ => mul_nonneg (Nat.cast_nonneg _) (hnn i hi Q)) hP
  · have hB0 : σ.BY i = 0 := divisorSeq_eq_zero σ hB (i + 1) (natCast_succ_le_iff.mpr hi)
    have hs := σ.isRealFlipStep i hi
    have hZ := hs.isNegativeExtremalContraction.isNormalVariety_target
    haveI : IsNormal (σ.Z i) := hZ.2
    obtain ⟨C, hC⟩ : ∃ C, MMP.Flips.IsFlippingCurve ℂ (σ.sY i) (σ.sZ i) (σ.fp i) C := by
      by_contra hno
      push Not at hno
      exact hs.not_isIso_flip (isIso_of_forall_not_isFlippingCurve
        hs.isSmall_flip.toIsBirationalContraction hno)
    obtain ⟨m, -, hlt⟩ := (hstep i hi).2 C hC
    refine hlt ?_
    rw [hB0, realThresholdMax_zero]
    simp

end MMP.Fourfold
