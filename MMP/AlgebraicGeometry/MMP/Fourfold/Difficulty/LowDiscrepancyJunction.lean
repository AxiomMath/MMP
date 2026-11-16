module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.RingTheory.SerreCondition.ExtSupportCriterion
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Low valuations of a klt pair, and junctions extracting them

Let `(X, B)` be a klt pair over an algebraically closed field `k` of characteristic zero. Only
finitely many normalized divisorial valuations `ξ` of `k(X)` are exceptional over `X` and have
log discrepancy `a(ξ; X, B) ≤ 1`: the low-discrepancy set `I(X, B)` is finite.

Choose a log resolution `π : W ⟶ X` of `(X, Supp B)` and let `T = ∑ⱼ Tⱼ` be the reduced snc
divisor on `W` whose support is `Ex(π) ∪ π⁻¹(Supp B)`; it contains the exceptional locus and the
support of the crepant pull-back `B_W`, so `(π, T)` is a log-smooth datum. Put
`aⱼ = a(ord_{Tⱼ}; X, B) > 0`. For `ξ` as above, with centre `Z` on `W`, `J(ξ)` the components of
`T` through `Z` and `e_T(ξ) ∈ ℤ_{≥0}` the reduced snc discrepancy, the log-smooth formula reads
`a(ξ; X, B) = ∑_{j ∈ J(ξ)} ξ(Tⱼ) aⱼ + e_T(ξ)`.

* If `J(ξ) ≠ ∅`, every `ξ(Tⱼ)`, `j ∈ J(ξ)`, is a positive integer, so `e_T(ξ) = 0` and
  `ξ(Tⱼ) ≤ 1 / aⱼ`; there are only finitely many such valuations.
* If `J(ξ) = ∅`, then `a(ξ; X, B) = e_T(ξ) ≥ codim Z`, so `codim Z ≤ 1`. The generic point of `Z`
  avoids `T ⊇ Ex(π)`, so `π` is a local isomorphism there and the centre of `ξ` on `X` has the
  same codimension `≤ 1`: `ξ` is not exceptional over `X`.

Now let `(X, B)` be an effective rational klt pair on a normal projective complex threefold and
`(p, Θ)`, `p : Y ⟶ X`, a crepant junction of `(X, B)` extracting the whole set `I(X, B)`. Then
`(Y, Θ)` is a terminal pair and every coefficient of `Θ` lies in `[0, 1)`. A divisor `(W, g, F)`
over `Y` is a divisor `(W, g ≫ p, F)` over `X`; since `K_Y + Θ = p^*(K_X + B)`, both have the
same log discrepancy. If `F` is exceptional over `Y`, its valuation is exceptional over `X` and is
not in `I(X, B)`, whose members have divisorial centres `E_s` on `Y`; so its log discrepancy is
`> 1`. The coefficients of `p⁻¹_* B` lie in `[0, 1)` because `(X, B)` is klt, and
`1 - a(s; X, B) ∈ [0, 1)` because `0 < a(s; X, B) ≤ 1`.

## Main results

* `MMP.Fourfold.IsKltPair.finite_lowDiscrepancySet`: `I(X, B)` is finite for a klt pair.
* `MMP.Fourfold.CrepantJunction.isKltTerminalPair_of_coe_eq_lowDiscrepancySet`: a crepant
  junction extracting `I(X, B)` is terminal, with boundary coefficients in `[0, 1)`.

## Implementation notes

* A crepant junction (`MMP.Fourfold.CrepantJunction`) extracts a finite set `I` of valuations;
  "extracting `I(X, B)`" is the hypothesis that `I`, as a set, is
  `MMP.Fourfold.lowDiscrepancySet sX B`.
* `Θ` is a `ℚ`-divisor, so it is rational by its type; effectivity of `Θ` is the lower bound in
  `Θ.coeff P ∈ [0, 1)`. Effectivity of `B` is part of `MMP.Fourfold.IsKltPair`.

## References

* [OpenAI, *Projective lc fourfolds*], Lemma on small discrepancies.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution

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

/-- **The components of an snc closed subset.** A closed subset `T` with simple normal crossings on
a smooth scheme is the union of the supports of a finite set of prime divisors whose reduced sum
is an snc divisor. -/
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
  set S := hfinS.toFinset
  have hmemS : ∀ P, P ∈ S ↔ (P.support : Set Y) ∈ componentsOf T := fun _ => hfinS.mem_toFinset
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

/-! ### The support of the crepant boundary -/

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The strict-transform part of the crepant boundary.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, a prime divisor `G` of `Y` that is not `f`-exceptional is the
birational transform `f⁻¹_* P` of a prime divisor `P` of `X`, and the crepant boundary `Δ_Y` has
`coeff_G(Δ_Y) = coeff_P(Δ)`. -/
private theorem exists_coeff_eq_of_not_isExceptional (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨P, neg_injective ((hΔY G).eq hd), hη⟩

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
  · obtain ⟨P, hc, hη⟩ := exists_coeff_eq_of_not_isExceptional hP hY hf hΔY hGe
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc,
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-! ### Existence of a log-smooth datum -/

/-- **Log-smooth data exist.** A klt pair `(X, B)` has a log-smooth datum: a log resolution
`π : W ⟶ X` of `(X, Supp B)`, with `T` the reduced sum of the components of
`Ex(π) ∪ π⁻¹(Supp B)`. -/
private theorem exists_isLogSmoothDatum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltPair sX B) :
    ∃ (W : Scheme.{u}) (π : W ⟶ X) (T : Divisor W), IsLogSmoothDatum sX B π T := by
  classical
  have : IsAlgClosed k := hB.1.isAlgClosed
  have : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.isPair
  obtain ⟨Y, f, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  have : IsProper f := hres.isProjective.isProper
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
    Finset.ext fun G => by
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]; simp [Finsupp.single_apply]
  have hmem : ∀ G : MMP.Mori.PrimeDivisor Y, G.genericPoint ∈ (⋃ F ∈ S, (F.support : Set Y)) →
      G ∈ S := fun G hG => by
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  refine ⟨Y, f, ∑ E ∈ S, Finsupp.single E (1 : ℤ), ⟨hB, hres.isProjective,
    hfres.isBirationalMorphism, hY, hfres.isSmoothScheme, fun P => ?_, hsncS, fun y hy => ?_,
    n, K, BY, hBY, fun G hG => ?_⟩⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    by_cases hP : P ∈ S <;> simp [Finsupp.single_apply, hP]
  · rw [hsupp, hU]
    exact Or.inl hy
  · rw [hsupp]
    refine hmem G ?_
    rw [hU]
    exact genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hX, hK, hq⟩ hY
      hfres.isBirationalMorphism hBY hG

/-! ### Finiteness -/

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
  refine ⟨-WithZero.log (D.valuation (algebraMap _ W.functionField z)), ?_,
    by rw [neg_neg, WithZero.exp_log hne]⟩
  have h := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D η hη z hz
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

/-- **The arithmetic of the case `J(ξ) ≠ ∅`.** If positive integers `mⱼ` and positive reals
`aⱼ`, indexed by a nonempty set, satisfy `∑ⱼ mⱼ aⱼ + e ≤ 1` with `e ∈ ℕ`, then `e = 0` and
`mⱼ ≤ 1 / aⱼ` for every `j`. -/
private theorem eq_zero_and_le_one_div_of_sum_add_le {ι : Type*} [Fintype ι] {m : ι → ℤ}
    {a : ι → ℝ} (hm : ∀ i, 1 ≤ m i) (ha : ∀ i, 0 < a i) {e : ℕ}
    (h : ∑ i, (m i : ℝ) * a i + e ≤ 1) (j : ι) : e = 0 ∧ (m j : ℝ) ≤ 1 / a j := by
  have hj := Finset.single_le_sum (fun i _ => mul_nonneg
    (Int.cast_nonneg (zero_le_one.trans (hm i))) (ha i).le) (Finset.mem_univ j)
  have h1 : (1 : ℝ) ≤ m j := by exact_mod_cast hm j
  have hj' : a j ≤ m j * a j := by nlinarith [ha j]
  refine ⟨Nat.lt_one_iff.1 (by exact_mod_cast (show (e : ℝ) < 1 by linarith [ha j])), ?_⟩
  rw [le_div_iff₀ (ha j)]
  linarith [e.cast_nonneg (α := ℝ)]

/-- A valuation pulls back along a bijective ring homomorphism from a valuation of its target. -/
private theorem exists_comap_eq_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (f : R →+* S) (hf : Function.Bijective f)
    (v : Valuation R Γ) : ∃ w : Valuation S Γ, w.comap f = v := by
  let e := RingEquiv.ofBijective f hf
  refine ⟨v.comap e.symm.toRingHom, ?_⟩
  ext x
  exact congrArg v (e.symm_apply_apply x)

/-- An upper bound `x ≤ 1 / aⱼ`, `j ∈ s`, with all `aᵢ > 0`, gives `x ≤ ⌈∑_{i ∈ s} 1 / aᵢ⌉ + 1`. -/
private theorem le_ceil_sum_one_div_add_one {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {j : ι} (hj : j ∈ s) {x : ℝ} (hx : x ≤ 1 / a j) :
    x ≤ ((⌈∑ i ∈ s, 1 / a i⌉₊ + 1 : ℕ) : ℝ) := by
  have h2 := Finset.single_le_sum (fun i _ => (one_div_pos.2 (ha i)).le) hj
  have h3 := Nat.le_ceil (∑ i ∈ s, 1 / a i)
  push_cast
  linarith

/-- On a scheme of finite dimension, every irreducible closed subset has finite codimension. -/
private theorem codimension_ne_top_of_topologicalKrullDim_eq {W : Scheme.{u}} {n : ℕ}
    (h : topologicalKrullDim W = n) (Z : IrreducibleCloseds W) : codimension Z ≠ ⊤ := by
  intro htop
  have h1 : ((Order.coheight Z : ℕ∞) : WithBot ℕ∞) ≤
      Order.krullDim (IrreducibleCloseds W) := Order.coheight_le_krullDim _
  rw [← codimension_eq_coheight, htop] at h1
  change _ ≤ topologicalKrullDim W at h1
  rw [h] at h1
  norm_cast at h1

open Classical in
/-- If no component of `T` contains the irreducible closed subset `Z`, the generic point of `Z`
lies on no component of `T`. -/
private theorem genericPoint_notMem_of_not_nonempty_sncIndexSet {W : Scheme.{u}} {T : Divisor W}
    (Z : IrreducibleCloseds W) (hJ : ¬ (sncIndexSet T (Z : Set W)).Nonempty) :
    Z.isIrreducible.genericPoint ∉ ⋃ E ∈ T.support, (E.support : Set W) := fun h => by
  obtain ⟨E, hE, hηE⟩ := Set.mem_iUnion₂.1 h
  refine hJ ⟨E, Finset.mem_filter.2 ⟨hE, ?_⟩⟩
  rw [← Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed]
  refine closure_minimal (Set.singleton_subset_iff.2 hηE) ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  exact isClosed_closure

/-- The generic point of the centre of a divisor `D` over `X` is the image of the generic point
of `D`. -/
private theorem genericPoint_center_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) :
    D.center.isIrreducible.genericPoint = D.f D.E.genericPoint :=
  (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).eq
    D.center_eq_closure_genericPoint.symm

open Classical in
/-- **A centre on no component of `T` has reduced snc discrepancy at least two.** Let `(π, T)` be
a log-smooth datum of a klt pair on `X`, and `D'` a divisor over `W` whose centre lies in no
component of `T` and whose pushforward valuation is that of a divisor `D₀` over `X` with centre of
codimension at least two. Then the reduced snc discrepancy of `v_{D'}` is at least two. -/
private theorem two_le_of_not_nonempty_sncIndexSet {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} [IsDominant π] {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T)
    {D' : DivisorOver k (π ≫ sX)}
    {D₀ : DivisorOver k sX} (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation)
    (hcod : 2 ≤ codimension D₀.center)
    (hZ : MMP.Intersection.IsCentre k (π ≫ sX) D'.valuation D'.center) {e : ℝ}
    (heT : IsReducedSNCDiscrepancy (π ≫ sX) T D'.valuation e)
    (hJ : ¬ (sncIndexSet T (D'.center : Set W)).Nonempty) : 2 ≤ e := by
  have hB := hπ.isKltPair
  have : IsAlgClosed k := hB.1.isAlgClosed
  have : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, -⟩ := hB.1.isPair
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  have : IsSeparated sX := hX.1.toIsSeparated
  have hdimW : topologicalKrullDim W = n :=
    have := hX.1
    have := hW.1
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX)
      hπ.isBirationalMorphism).symm.trans hK.topologicalKrullDim_eq
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1
    (codimension_ne_top_of_topologicalKrullDim_eq hdimW D'.center)
  have hce := heT.sub_card_sncIndexSet_le hZ hc.symm
  rw [Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hJ)] at hce
  have hgen := genericPoint_center_eq D'
  have hηex : D'.center.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W) := fun hex =>
    genericPoint_notMem_of_not_nonempty_sncIndexSet D'.center hJ (hπ.exceptionalSet_subset hex)
  rw [codimension_center_eq_of_notMem_exceptionalSet D' D₀ hξ (hgen ▸ hηex), ← hc] at hcod
  have : (2 : ℝ) ≤ c := by exact_mod_cast hcod
  push_cast at hce
  linarith

/-- Two generators of the same principal ideal of the stalk at the generic point of the centre of
`D` have the same `D`-valuation. -/
private theorem valuation_algebraMap_eq_of_span_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] (D : DivisorOver k sW)
    {z z' : W.presheaf.stalk D.center.isIrreducible.genericPoint}
    (h : Ideal.span {z'} = Ideal.span {z}) :
    D.valuation (algebraMap _ W.functionField z') =
      D.valuation (algebraMap _ W.functionField z) := by
  have hgen := genericPoint_center_eq D
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  rw [← hu, map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
    _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ hgen) u, mul_one]

open Classical in
/-- At the generic point of the centre of a divisor `D` over `W`, every component of `T` through
the centre has a prime local equation `z j` of `D`-valuation `exp (-m j)`, with `1 ≤ m j`. -/
private theorem exists_prime_stalk_valuation_eq_exp_neg {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) (D : DivisorOver k (π ≫ sX)) :
    ∃ (z : sncIndexSet T (D.center : Set W) → W.presheaf.stalk D.center.isIrreducible.genericPoint)
      (m : sncIndexSet T (D.center : Set W) → ℤ), (∀ j, 1 ≤ m j) ∧
      (∀ j, IdealSheafData.stalk j.1.idealSheaf D.center.isIrreducible.genericPoint =
        Ideal.span {z j}) ∧
      ∀ j, D.valuation (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j) := by
  have : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  have hgen := genericPoint_center_eq D
  choose z hzp hz using fun j : sncIndexSet T (D.center : Set W) =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sX) hπ.isSmoothScheme j.1
      ((Finset.mem_filter.1 j.2).2
        (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).mem)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D hgen (hzp j).ne_zero
    ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  exact ⟨z, m, hm1, hz, hm⟩

/-- Every prime divisor of `W` has a positive log discrepancy over the klt pair `(X, B)`. -/
private theorem exists_pos_isLogDiscrepancy_of_isLogSmoothDatum {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ} {K : Divisor X}
    (hK : Divisor.IsCanonicalDivisor sX n K) :
    ∃ aT : MMP.Mori.PrimeDivisor W → ℝ, (∀ j, MMP.Intersection.IsLogDiscrepancy sX n
      (QDivisor.toRDivisor B) ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j)) ∧
      ∀ j, 0 < aT j := by
  have hB := hπ.isKltPair
  have : IsAlgClosed k := hB.1.isAlgClosed
  have : CharZero k := hB.1.charZero
  have := hπ.isBirationalMorphism.isDominant
  have : IsProper π := IsProjective.isProper hπ.isProjective
  have hex : ∀ j : MMP.Mori.PrimeDivisor W, ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n
      (QDivisor.toRDivisor B) ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ a :=
    fun j => by
      obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.isPair hK
        ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩
      exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
        (inferInstance : IsProper π)⟩
  choose aT haT using hex
  exact ⟨aT, haT, fun j => hB.2 n _ (aT j) (haT j)⟩

/-- **Finiteness on a log-smooth datum.** If `(π, T)` is a log-smooth datum of the klt pair
`(X, B)`, the low-discrepancy set `I(X, B)` is finite. -/
private theorem finite_lowDiscrepancySet_of_isLogSmoothDatum {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) :
    (lowDiscrepancySet sX B).Finite := by
  classical
  have hB := hπ.isKltPair
  have : IsAlgClosed k := hB.1.isAlgClosed
  have : CharZero k := hB.1.charZero
  have := hπ.isBirationalMorphism.isDominant
  have : IsProper π := IsProjective.isProper hπ.isProjective
  obtain ⟨hX, n, K, hK, -⟩ := hB.1.isPair
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  have : IsSeparated sX := hX.1.toIsSeparated
  have : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  obtain ⟨aT, haT, haT0⟩ := exists_pos_isLogDiscrepancy_of_isLogSmoothDatum hπ hK
  set M : ℕ := ⌈∑ j ∈ T.support, 1 / aT j⌉₊ + 1
  refine ((finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sX) T (M := M)
    (Nat.le_add_left 1 _)).image fun ξ => ξ.comap (functionFieldMap π)).subset ?_
  rintro ξ ⟨⟨D₀, -, hξD₀, hcod⟩, a, ⟨n', D, hDp, hDξ, ha⟩, ha1⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  obtain ⟨ξW, hΦ⟩ := exists_comap_eq_of_bijective (functionFieldMap π)
    hπ.isBirationalMorphism.functionFieldMap_bijective ξ
  refine ⟨ξW, ?_, hΦ⟩
  obtain ⟨Z, hZ, eT, heT, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D hDp ha ξW (hΦ.trans hDξ.symm)
  obtain ⟨D', -, rfl, rfl⟩ := id hZ
  obtain ⟨z, m, hm1, hz, hm⟩ := exists_prime_stalk_valuation_eq_exp_neg hπ D'
  have hform' := hform z m hz hm
  obtain ⟨e0, rfl⟩ := heT.exists_eq_natCast
  push_cast at hform'
  by_cases hJ : (sncIndexSet T (D'.center : Set W)).Nonempty
  · have hsum : ∑ j, (m j : ℝ) * aT j + e0 ≤ 1 := hform' ▸ ha1
    have hle := eq_zero_and_le_one_div_of_sum_add_le hm1 (fun j => haT0 j) hsum
    obtain ⟨j₀, hj₀⟩ := hJ
    obtain rfl := (hle ⟨j₀, hj₀⟩).1
    refine ⟨by exact_mod_cast heT, fun Z' hZ' j hj z' hz' => ?_⟩
    obtain rfl : Z' = D'.center := by
      obtain ⟨D'', -, hξD'', rfl⟩ := hZ'
      exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hW.1 hξD''.symm
    rw [valuation_algebraMap_eq_of_span_eq D' (hz'.symm.trans (hz ⟨j, hj⟩)), hm,
      WithZero.exp_le_exp, neg_le_neg_iff]
    exact_mod_cast (show (m ⟨j, hj⟩ : ℝ) ≤ M from
      le_ceil_sum_one_div_add_one haT0 (Finset.mem_filter.1 hj).1 (hle ⟨j, hj⟩).2)
  · have : IsEmpty (sncIndexSet T (D'.center : Set W)) := ⟨fun j => hJ ⟨j.1, j.2⟩⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hform'
    have := two_le_of_not_nonempty_sncIndexSet hπ (hΦ.trans hξD₀) hcod hZ heT hJ
    linarith

/-- **Finitely many valuations of log discrepancy at most one.** For a klt pair `(X, B)`
(`MMP.Fourfold.IsKltPair`), the low-discrepancy set `MMP.Fourfold.lowDiscrepancySet sX B` — the
normalized divisorial valuations `ξ` of `k(X)` exceptional over `X` with `a(ξ; X, B) ≤ 1` — is
finite. -/
@[mmp "lem_oai4_small_discrepancies"]
public theorem IsKltPair.finite_lowDiscrepancySet {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltPair sX B) :
    (lowDiscrepancySet sX B).Finite := by
  obtain ⟨W, π, T, hπ⟩ := exists_isLogSmoothDatum hB
  have : IsIntegral W := hπ.isNormalVariety.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  have : IsNormal W := hπ.isNormalVariety.2
  exact finite_lowDiscrepancySet_of_isLogSmoothDatum hπ

/-! ### Junctions extracting all low valuations -/

section Junction

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField ℤᵐ⁰)}

/-- The source of a crepant junction is quasi-compact: it is projective over `ℂ`. -/
private theorem CrepantJunction.compactSpace_Y (J : CrepantJunction sX B I) :
    CompactSpace J.Y := by
  have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety.isProjective
  exact QuasiCompact.compactSpace_of_compactSpace (J.p ≫ sX)

attribute [local instance] CrepantJunction.compactSpace_Y

/-- The structure morphism `Y ⟶ Spec ℂ` of the source of a crepant junction. -/
private noncomputable abbrev CrepantJunction.sY (J : CrepantJunction sX B I) :
    J.Y ⟶ Spec (.of ℂ) :=
  J.p ≫ sX

/-- The morphism `p` of a crepant junction is proper. -/
private theorem isProper_p (J : CrepantJunction sX B I) : IsProper J.p :=
  isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism

/-- A divisor `(W, g, F)` over the source `Y` of a junction, with `g` proper, as the divisor
`(W, g ≫ p, F)` over `X`. -/
private noncomputable def compDivisorOver (J : CrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) [IsProper D.f] : DivisorOver ℂ sX where
  Y := D.Y
  f := D.f ≫ J.p
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc]
  isBirationalMorphism := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := isProper_p J
    exact isBirationalMorphism_comp_of_isBirational J.p D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

/-- The valuation of `(W, g ≫ p, F)` is that of `(W, g, F)`, transported to `k(X)` along `p`. -/
private theorem valuation_compDivisorOver (J : CrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) [IsProper D.f] :
    have := J.isBirationalMorphism.isDominant
    (compDivisorOver J D).valuation = D.valuation.comap (functionFieldMap J.p) := by
  have := J.isBirationalMorphism.isDominant
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : IsDominant (D.f ≫ J.p) := (compDivisorOver J D).isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ J.p) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap J.p t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

private theorem isProper_compDivisorOver (J : CrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) [IsProper D.f] : IsProper (compDivisorOver J D).f := by
  have := isProper_p J
  change IsProper (D.f ≫ J.p)
  infer_instance

/-- The centre of a divisor exceptional over a normal variety has codimension at least two. -/
private theorem two_le_codimension_center_of_isExceptional {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) (hE : D.IsExceptional) : 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sY := hY.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hY
  unfold DivisorOver.IsExceptional at hE
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hE
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc] at hE
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ at hE
  rwa [closedsCodimension_coe] at hE

/-- A prime divisor `Q` of the source `Y` of a junction, as the divisor `(Y, p, Q)` over `X`. -/
private def primeDivisorOver (J : CrepantJunction sX B I) (Q : MMP.Mori.PrimeDivisor J.Y) :
    DivisorOver ℂ sX :=
  ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩

/-- A divisor exceptional over `Y` does not have the valuation `ord_Q` of a prime divisor `Q` of
`Y`. -/
private theorem valuation_compDivisorOver_ne (J : CrepantJunction sX B I)
    {D : DivisorOver ℂ J.sY} [IsProper D.f] (hE : D.IsExceptional)
    (Q : MMP.Mori.PrimeDivisor J.Y) :
    (compDivisorOver J D).valuation ≠ (primeDivisorOver J Q).valuation := by
  intro hv
  have hY := J.isQFactorial.1
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := J.isBirationalMorphism.isDominant
  have hbij := IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism
  have hvY : D.valuation = (DivisorOver.ofPrimeDivisor ℂ hY Q).valuation := by
    ext h
    obtain ⟨g, rfl⟩ := hbij.2 h
    have := congrArg (fun v => v g) hv
    have hc : functionFieldMap (D.f ≫ J.p) g = functionFieldMap D.f (functionFieldMap J.p g) :=
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ g).symm
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ J.p) g) =
      Q.divisorialValuation (functionFieldMap J.p g) at this
    change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap J.p g)) =
      Q.divisorialValuation (functionFieldMap (𝟙 J.Y) (functionFieldMap J.p g))
    rw [MMP.Mori.functionFieldMap_id_apply, ← hc, this]
  exact (two_le_codimension_center_of_isExceptional hY D hE |>
    (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY D).mp) _ hvY

/-- The valuation of a divisor exceptional over `Y` is none of the extracted valuations, whose
centres on `Y` are the divisors `E_s`. -/
private theorem valuation_compDivisorOver_notMem (J : CrepantJunction sX B I)
    {D : DivisorOver ℂ J.sY} [IsProper D.f] (hE : D.IsExceptional) :
    (compDivisorOver J D).valuation ∉ (I : Set _) := fun hmem =>
  valuation_compDivisorOver_ne J hE (J.E ⟨_, hmem⟩) (J.valuation_eq ⟨_, hmem⟩).symm

/-- **Strict transforms.** Every prime divisor `P` of `X` has a strict transform `Q` on `Y`, with
`ord_Q = ord_P` as valuations of `k(X)`. -/
private theorem exists_valuation_primeDivisorOver_eq (J : CrepantJunction sX B I)
    (hX : IsNormalVariety ℂ sX) (P : MMP.Mori.PrimeDivisor X) :
    ∃ Q : MMP.Mori.PrimeDivisor J.Y,
      (primeDivisorOver J Q).valuation = (DivisorOver.ofPrimeDivisor ℂ hX P).valuation := by
  have := isProper_p J
  have := J.isBirationalMorphism.isDominant
  obtain ⟨y, hy, hcoh, -, -⟩ := MMP.Intersection.exists_preimage_of_coheight_eq_one J.p
    (IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_⟩
  refine MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX _ P ?_
  change J.p (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh).genericPoint = _
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]

/-- A divisor exceptional over `Y` is exceptional over `X`. -/
private theorem isExceptionalValuation_compDivisorOver (J : CrepantJunction sX B I)
    {D : DivisorOver ℂ J.sY} [IsProper D.f] (hE : D.IsExceptional) :
    MMP.Intersection.IsExceptionalValuation ℂ sX (compDivisorOver J D).valuation := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  by_contra h
  have h2 : ¬ 2 ≤ codimension (compDivisorOver J D).center :=
    fun h2 => h ⟨_, isProper_compDivisorOver J D, rfl, h2⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at h2
  push Not at h2
  obtain ⟨P, hP⟩ := h2
  obtain ⟨Q, hQ⟩ := exists_valuation_primeDivisorOver_eq J hX P
  exact valuation_compDivisorOver_ne J hE Q (hP.trans hQ.symm)

/-- The log discrepancies of the extracted valuations lie in `(0, 1]`. -/
private theorem logDiscrepancy_mem_Ioc (J : CrepantJunction sX B I) {a : I → ℚ}
    (ha : ∀ s : I, IsValuationLogDiscrepancy sX B s (a s)) (s : I) :
    0 < a s ∧ a s ≤ 1 := by
  obtain ⟨n, D, -, hv, hlog⟩ := ha s
  obtain ⟨-, a', ⟨n', D', -, hv', hlog'⟩, hle⟩ := J.subset_lowDiscrepancySet s.2
  have heq : ((a s : ℚ) : ℝ) = a' :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hlog' (hv.trans hv'.symm)
  have hpos := J.isKltPair.2 n D _ hlog
  exact ⟨by exact_mod_cast hpos, by exact_mod_cast heq ▸ hle⟩

/-- The strict transform `p⁻¹_* B` does not contain the exceptional divisors `E_s`. -/
private theorem coeff_inverseTransformDivisor_E_eq_zero (J : CrepantJunction sX B I) (s : I) :
    (inverseTransformDivisor J.p B).coeff (J.E s) = 0 := by
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  refine MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero (fun P hP => ?_) _
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hE : (primeDivisorOver J (J.E s)).IsExceptional :=
    (J.isExceptional_iff _).mpr ⟨s, rfl⟩
  have h2 := two_le_codimension_center_of_isExceptional hX _ hE
  rw [MMP.Positivity.DivisorOver.codimension_center] at h2
  change 2 ≤ Order.coheight (J.p (J.E s).genericPoint) at h2
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The coefficients of a klt boundary are `< 1`. -/
private theorem coeff_lt_one_of_isKltPair (hB : IsKltPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P < 1 := by
  have hpair := hB.1.isPair
  have hX : IsNormalVariety ℂ sX := hpair.1
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 X)
    infer_instance
  have hpos := hB.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hprop)
  have heq := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha
  rw [heq] at hpos
  push_cast at hpos
  exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)

/-- The strict transform `p⁻¹_* B` has coefficients in `[0, 1)`: those of the klt boundary `B`. -/
private theorem coeff_inverseTransformDivisor_mem_Ico (J : CrepantJunction sX B I)
    (Γ : MMP.Mori.PrimeDivisor J.Y) :
    0 ≤ (inverseTransformDivisor J.p B).coeff Γ ∧ (inverseTransformDivisor J.p B).coeff Γ < 1 := by
  change 0 ≤ (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ ∧
    (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff Γ < 1
  by_cases h : ∃ P, inverseTransformPrimeDivisor J.p P = some Γ
  · obtain ⟨P, hP⟩ := h
    have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hP).1
    have hinj : ∀ P', inverseTransformPrimeDivisor J.p P' = some Γ → P' = P := fun P' hP' =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hP').1.symm.trans hη)
    rw [DivisorWithCoeffs.coeff, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP hinj]
    exact ⟨J.isKltPair.1.nonneg P, coeff_lt_one_of_isKltPair J.isKltPair P⟩
  · push Not at h
    rw [DivisorWithCoeffs.coeff, MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero h B]
    norm_num

/-- The coefficients of the boundary of a junction lie in `[0, 1)`. -/
private theorem coeff_Θ_mem_Ico (J : CrepantJunction sX B I) :
    ∀ Γ : MMP.Mori.PrimeDivisor J.Y, 0 ≤ J.Θ.coeff Γ ∧ J.Θ.coeff Γ < 1 := by
  classical
  obtain ⟨a, ha, hΘ⟩ := J.Θ_eq
  intro Γ
  have hsum : (∑ s : I, Finsupp.single (J.E s) (1 - a s) : QDivisor J.Y).coeff Γ =
      ∑ s : I, if J.E s = Γ then 1 - a s else 0 := by
    change (∑ s : I, Finsupp.single (J.E s) (1 - a s)) Γ = _
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun s _ => Finsupp.single_apply
  rw [hΘ, DivisorWithCoeffs.coeff_add, hsum]
  by_cases hΓ : Γ ∈ Set.range J.E
  · obtain ⟨t, rfl⟩ := hΓ
    rw [coeff_inverseTransformDivisor_E_eq_zero, zero_add,
      Finset.sum_eq_single t (fun s _ hst => if_neg (fun h => hst (J.injective h)))
        (fun h => absurd (Finset.mem_univ t) h), if_pos rfl]
    have := logDiscrepancy_mem_Ioc J ha t
    constructor <;> linarith
  · rw [Finset.sum_eq_zero (fun s _ => if_neg (fun h => hΓ ⟨s, h⟩)), add_zero]
    exact coeff_inverseTransformDivisor_mem_Ico J Γ

/-- **Junctions extracting all low valuations are terminal.** Let `(X, B)` be an effective
rational klt pair on a normal projective complex threefold and `J = (p, Θ)` a crepant junction of
`(X, B)` extracting `I = I(X, B)`. Then `(Y, Θ)` is a terminal pair and every coefficient of `Θ`
lies in `[0, 1)`; in particular `Θ` is effective. -/
@[mmp "prop_mmp_indexc_junction_terminal"]
public theorem CrepantJunction.isKltTerminalPair_of_coe_eq_lowDiscrepancySet
    (J : CrepantJunction sX B I) (hI : (I : Set _) = lowDiscrepancySet sX B) :
    IsKltTerminalPair (J.p ≫ sX) J.Θ ∧ ∀ P, J.Θ.coeff P ∈ Set.Ico (0 : ℚ) 1 := by
  have := J.isBirationalMorphism.isDominant
  obtain ⟨hpair, -, hlog⟩ := J.isCrepant
  refine ⟨⟨⟨hpair, fun n D a ha => ?_⟩, fun n D a hE ha => ?_⟩, coeff_Θ_mem_Ico J⟩
  · obtain ⟨n', D', -, -, h'⟩ := (hlog D.valuation a).mp ⟨n, D, ha.2.1, rfl, ha⟩
    exact J.isKltPair.2 n' D' a h'
  · have : IsProper D.f := ha.2.1
    by_contra! hle
    apply valuation_compDivisorOver_notMem J hE
    rw [hI]
    refine ⟨isExceptionalValuation_compDivisorOver J hE, a, ?_, hle⟩
    rw [valuation_compDivisorOver]
    exact (hlog D.valuation a).mp ⟨n, D, ha.2.1, rfl, ha⟩

end Junction

end MMP.Fourfold
