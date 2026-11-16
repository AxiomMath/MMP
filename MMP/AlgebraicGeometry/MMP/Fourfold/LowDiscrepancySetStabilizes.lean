module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.Singularities.Surface.NormalizedExceptionalMatrix
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus

/-!
# The low-discrepancy sets of a small klt step sequence stabilize

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a step sequence which is small from the index `0` and
in which every `(X_i, B_i)` is klt. Then the stable low-discrepancy set `I_∞ = ⋂_{i ≥ 0} I_i` is
finite, and the low-discrepancy sets `I_i = I(X_i, B_i)` are eventually equal to `I_∞`: there is
`i₀` such that, for every `i ≥ i₀`, the valuations of `k(X_i)` corresponding to the elements of
`I_∞` are exactly the elements of `I_i`.

The proof has two parts. First, `I_0 = I(X_0, B_0)` is finite: on a log resolution `W → X_0`
with reduced snc divisor `T ⊇ Exc ∪ Supp B_W`, an exceptional valuation `ξ` with
`a(ξ; X_0, B_0) ≤ 1` has zero reduced snc discrepancy and bounded orders along the components of
`T` through its centre, and there are only finitely many of those. Second, pulled back to
valuations of `k(X_0)`, the sets `I_i` decrease, since `I_{i+1} ⊆ I_i`; a decreasing sequence of
subsets of a finite set is eventually constant, equal to its intersection `I_∞`.

## Main results

* `MMP.Fourfold.StepSequence.finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq`:
  `I_∞` is finite and `I_i = I_∞` for all `i ≥ i₀`.

## Implementation notes

The sets `I_i` consist of valuations of the different function fields `k(X_i)`, and `I_∞` of
valuations of `k(X_0)`. The equality `I_i = I_∞` is stated, as in
`MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail`, as the equality of `I_i` with the image of
`I_∞` under the identification `MMP.Fourfold.StepSequence.Corresponds i`.

The identifications `k(X_0) ≅ k(X_i)` along the step sequence are bijections of valuations, since
every `f_i`, `f_i⁺` is birational; this makes `Corresponds i` the graph of a bijection, which is
what turns the nested sets `I_i` into a decreasing sequence of subsets of the valuations of
`k(X_0)`.

## References

* [OpenAI, *Projective lc fourfolds*], lemmas on small discrepancies and on the stable
  low-discrepancy set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.Fourfold.StepSequence

open MMP.Mori MMP.Fourfold MMP.Resolution

/-! ### Valuations along a bijective ring hom -/

/-- Pulling valuations back along a surjective ring hom is injective. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ)
    {v w : Valuation B Γ} (h : v.comap φ = w.comap φ) : v = w := by
  ext x
  obtain ⟨y, rfl⟩ := hφ x
  exact congrArg (fun u : Valuation A Γ => u y) h

/-- Pulling valuations back along a bijective ring hom is surjective. -/
private theorem exists_comap_eq_of_bijective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Bijective φ)
    (w : Valuation A Γ) : ∃ v : Valuation B Γ, v.comap φ = w := by
  let e := RingEquiv.ofBijective φ hφ
  refine ⟨w.comap e.symm.toRingHom, ?_⟩
  ext x
  exact congrArg w (e.symm_apply_apply x)

section Finiteness

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

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
  set S := hfinS.toFinset
  have hmemS : ∀ P, P ∈ S ↔ (P.support : Set Y) ∈ componentsOf T := fun _ => hfinS.mem_toFinset
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2).antisymm fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
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
  haveI : IsAlgClosed k := hB.1.isAlgClosed
  haveI : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.isPair
  obtain ⟨Y, f, hres, -, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  haveI : IsProper f := hres.isProjective.isProper
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
    Finset.ext fun G => by
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
      simp [Finsupp.single_apply]
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
    apply hmem
    rw [hU]
    exact genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hX, hK, hq⟩ hY
      hfres.isBirationalMorphism hBY hG

/-! ### Finiteness -/

/-- **A centre off the exceptional locus has the same codimension downstairs.** Let `π : W ⟶ X`
be dominant, `D'` a divisor over `W` whose centre has generic point outside `Ex(π)`, and `D₀` a
divisor over `X` with `π_* v_{D'} = v_{D₀}`. Then the centres of `D₀` and `D'` have the same
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

/-- The local equations `zⱼ` at the generic point of the centre of a divisor `D` over a smooth
`W` of the components `Tⱼ` of `T` through the centre, and their `v_D`-orders `mⱼ ≥ 1`. -/
private theorem exists_localEquation_valuation_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [LocallyOfFiniteType sW] (hsm : IsSmoothScheme sW)
    (T : Divisor W) (D : DivisorOver k sW) :
    ∃ (z : sncIndexSet T (D.center : Set W) → W.presheaf.stalk D.center.isIrreducible.genericPoint)
      (m : sncIndexSet T (D.center : Set W) → ℤ),
      (∀ j, IdealSheafData.stalk j.1.idealSheaf D.center.isIrreducible.genericPoint =
        Ideal.span {z j}) ∧ (∀ j, 1 ≤ m j) ∧
      ∀ j, D.valuation (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j) := by
  classical
  have hZ := D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed
  choose z hzp hz using fun j : sncIndexSet T (D.center : Set W) =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sW hsm j.1 ((Finset.mem_filter.1 j.2).2 hZ.mem)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D
    (hZ.eq D.center_eq_closure_genericPoint.symm) (hzp j).ne_zero
    ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  exact ⟨z, m, hz, hm1, hm⟩

/-- Two generators of the same principal ideal of the local ring at the centre of a divisor `D`
have the same `v_D`-value. -/
private theorem valuation_algebraMap_eq_of_span_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] (D : DivisorOver k sW) {η : W}
    (hη : η = D.f D.E.genericPoint) {z z' : W.presheaf.stalk η}
    (h : Ideal.span {z'} = Ideal.span {z}) :
    D.valuation (algebraMap _ W.functionField z') =
      D.valuation (algebraMap _ W.functionField z) := by
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  rw [map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
    _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D η hη) u, mul_one]

/-- An integer `m ≤ 1 / aⱼ`, with `j ∈ s` and every `aᵢ > 0`, is at most
`⌈∑_{i ∈ s} 1 / aᵢ⌉ + 1`. -/
private theorem le_ceil_sum_one_div_add_one {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {j : ι} (hj : j ∈ s) {m : ℤ} (hm : (m : ℝ) ≤ 1 / a j) :
    m ≤ ((⌈∑ i ∈ s, 1 / a i⌉₊ + 1 : ℕ) : ℤ) := by
  have h₁ : 1 / a j ≤ ∑ i ∈ s, 1 / a i :=
    Finset.single_le_sum (fun i _ => (one_div_pos.2 (ha i)).le) hj
  have h₂ := Nat.le_ceil (∑ i ∈ s, 1 / a i)
  have h₃ : (m : ℝ) ≤ ((⌈∑ i ∈ s, 1 / a i⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h₃

/-- In a space of finite dimension `n`, every irreducible closed subset has finite
codimension. -/
private theorem codimension_ne_top_of_topologicalKrullDim_eq {W : Type*} [TopologicalSpace W]
    {n : ℕ}
    (h : topologicalKrullDim W = n) (Z : IrreducibleCloseds W) : codimension Z ≠ ⊤ := by
  intro htop
  have h₁ : ((Order.coheight Z : ℕ∞) : WithBot ℕ∞) ≤
      Order.krullDim (IrreducibleCloseds W) := Order.coheight_le_krullDim _
  rw [← codimension_eq_coheight, htop] at h₁
  change _ ≤ topologicalKrullDim W at h₁
  rw [h] at h₁
  norm_cast at h₁

/-- **A centre through no component of `T` has the same codimension downstairs.** On a log-smooth
datum `(π, T)`, if no component of `T` contains the centre of a divisor `D'` over `W`, then the
centre of a divisor `D₀` over `X` with `π_* v_{D'} = v_{D₀}` has the same codimension as that of
`D'`. -/
private theorem codimension_center_eq_of_not_nonempty_sncIndexSet {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX)
    (hξ : haveI := hπ.isBirationalMorphism.isDominant
      D'.valuation.comap (functionFieldMap π) = D₀.valuation)
    (hJ : ¬ (sncIndexSet T (D'.center : Set W)).Nonempty) :
    codimension D₀.center = codimension D'.center := by
  classical
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨hX, -, -, -, -⟩ := hπ.isKltPair.1.isPair
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hZ := D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed
  have hη : D'.center.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W) := fun hex => by
    obtain ⟨E, hE, hηE⟩ := Set.mem_iUnion₂.1 (hπ.exceptionalSet_subset hex)
    refine hJ ⟨E, Finset.mem_filter.2 ⟨hE, ?_⟩⟩
    rw [← hZ]
    refine closure_minimal (Set.singleton_subset_iff.2 hηE) ?_
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
    exact isClosed_closure
  exact codimension_center_eq_of_notMem_exceptionalSet D' D₀ hξ
    (hZ.eq D'.center_eq_closure_genericPoint.symm ▸ hη)

/-- **Bounded orders of a lift.** Let `(π, T)` be a log-smooth datum of `(X, B)` and `aⱼ > 0` the
log discrepancies of the prime divisors of `W`. A lift `ξ_W` to `k(W)` of a valuation in
`I(X, B)` has zero reduced snc discrepancy and order at most `⌈∑ⱼ 1 / aⱼ⌉ + 1` along every
component of `T` through its centre. -/
private theorem isReducedSNCDiscrepancy_zero_and_le_of_mem_lowDiscrepancySet {k : Type u}
    [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ}
    (hn : topologicalKrullDim X = n) {aT : MMP.Mori.PrimeDivisor W → ℝ}
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    (haT0 : ∀ j, 0 < aT j) {ξ : Valuation X.functionField ℤᵐ⁰}
    (hξ : ξ ∈ lowDiscrepancySet sX B) (ξW : Valuation W.functionField ℤᵐ⁰)
    (hΦ : haveI := hπ.isBirationalMorphism.isDominant
      ξW.comap (functionFieldMap π) = ξ) :
    IsReducedSNCDiscrepancy (π ≫ sX) T ξW 0 ∧
      ∀ Z : IrreducibleCloseds W, MMP.Intersection.IsCentre k (π ≫ sX) ξW Z →
        ∀ j ∈ sncIndexSet T (Z : Set W),
          ∀ z : W.presheaf.stalk Z.isIrreducible.genericPoint,
            IdealSheafData.stalk j.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z} →
              WithZero.exp (-((⌈∑ j ∈ T.support, 1 / aT j⌉₊ + 1 : ℕ) : ℤ)) ≤
                ξW (algebraMap _ W.functionField z) := by
  classical
  haveI : IsAlgClosed k := hπ.isKltPair.1.isAlgClosed
  haveI : CharZero k := hπ.isKltPair.1.charZero
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨hX, -, -, -, -⟩ := hπ.isKltPair.1.isPair
  haveI : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  obtain ⟨⟨D₀, -, hξD₀, hcod⟩, a, ⟨n', D, hDp, hDξ, ha⟩, ha1⟩ := hξ
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hn
  obtain ⟨Z, hZ, eT, heT, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D hDp ha ξW (hΦ.trans hDξ.symm)
  obtain ⟨D', -, rfl, rfl⟩ := id hZ
  have hgen : D'.center.isIrreducible.genericPoint = D'.f D'.E.genericPoint :=
    (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).eq
      D'.center_eq_closure_genericPoint.symm
  obtain ⟨z, m, hz, hm1, hm⟩ := exists_localEquation_valuation_eq hπ.isSmoothScheme T D'
  have hform' := hform z m hz hm
  obtain ⟨e0, rfl⟩ := heT.exists_eq_natCast
  push_cast at hform'
  by_cases hJ : (sncIndexSet T (D'.center : Set W)).Nonempty
  · have hsum : ∑ j, (m j : ℝ) * aT j + e0 ≤ 1 := hform' ▸ ha1
    have key := eq_zero_and_le_one_div_of_sum_add_le hm1 (fun j => haT0 j) hsum
    obtain ⟨j₀, hj₀⟩ := hJ
    obtain rfl := (key ⟨j₀, hj₀⟩).1
    refine ⟨by exact_mod_cast heT, fun Z' hZ' j hj z' hz' => ?_⟩
    obtain rfl : Z' = D'.center := by
      obtain ⟨D'', -, hξD'', rfl⟩ := hZ'
      exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hπ.isNormalVariety.1 hξD''.symm
    rw [valuation_algebraMap_eq_of_span_eq D' hgen (hz'.symm.trans (hz ⟨j, hj⟩)), hm,
      WithZero.exp_le_exp, neg_le_neg_iff]
    exact le_ceil_sum_one_div_add_one haT0 (Finset.mem_filter.1 hj).1
      (key ⟨j, hj⟩).2
  · exfalso
    haveI : IsEmpty (sncIndexSet T (D'.center : Set W)) := ⟨fun j => hJ ⟨j.1, j.2⟩⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hform'
    have hdimW :=
      haveI := hX.1
      haveI := hπ.isNormalVariety.1
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX)
        hπ.isBirationalMorphism).symm.trans hn
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1
      (codimension_ne_top_of_topologicalKrullDim_eq hdimW D'.center)
    have hce := heT.sub_card_sncIndexSet_le hZ hc.symm
    rw [Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hJ)] at hce
    rw [codimension_center_eq_of_not_nonempty_sncIndexSet hπ D' D₀ (hΦ.trans hξD₀) hJ,
      ← hc] at hcod
    have : (2 : ℝ) ≤ c := by exact_mod_cast hcod
    push_cast at hce
    linarith

/-- **Finiteness on a log-smooth datum.** If `(π, T)` is a log-smooth datum of the klt pair
`(X, B)`, the low-discrepancy set `I(X, B)` is finite. -/
private theorem finite_lowDiscrepancySet_of_isLogSmoothDatum {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) :
    (lowDiscrepancySet sX B).Finite := by
  have hB := hπ.isKltPair
  haveI : IsAlgClosed k := hB.1.isAlgClosed
  haveI : CharZero k := hB.1.charZero
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  obtain ⟨-, n, K, hK, -⟩ := hB.1.isPair
  let DT : MMP.Mori.PrimeDivisor W → DivisorOver k sX :=
    fun j => ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩
  have hex : ∀ j, ∃ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) (DT j) a := fun j => by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.isPair hK (DT j)
    exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstance : IsProper π)⟩
  choose aT haT using hex
  refine ((finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sX) T
    (M := ⌈∑ j ∈ T.support, 1 / aT j⌉₊ + 1) (Nat.le_add_left 1 _)).image
      fun ξ => ξ.comap (functionFieldMap π)).subset fun ξ hξ => ?_
  obtain ⟨ξW, hΦ⟩ :=
    exists_comap_eq_of_bijective hπ.isBirationalMorphism.functionFieldMap_bijective ξ
  exact ⟨ξW, isReducedSNCDiscrepancy_zero_and_le_of_mem_lowDiscrepancySet hπ
    hK.topologicalKrullDim_eq haT (fun j => hB.2 n (DT j) (aT j) (haT j)) hξ ξW hΦ, hΦ⟩

/-- **Finitely many valuations of log discrepancy at most one.** For a klt pair `(X, B)`, the
low-discrepancy set `I(X, B)` is finite. -/
private theorem finite_lowDiscrepancySet {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsKltPair sX B) :
    (MMP.Fourfold.lowDiscrepancySet sX B).Finite := by
  obtain ⟨W, π, T, hπ⟩ := exists_isLogSmoothDatum hB
  haveI : IsIntegral W := hπ.isNormalVariety.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hπ.isNormalVariety.2
  exact finite_lowDiscrepancySet_of_isLogSmoothDatum hπ

end Finiteness

/-! ### Stabilization -/

section StepSequence

variable (S : StepSequence)

/-- `f_i` induces an isomorphism of function fields. -/
private theorem bijective_functionFieldMap_f (i : ℕ) :
    Function.Bijective (functionFieldMap (S.f i)) :=
  (S.isFourfoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective

/-- `f_i⁺` induces an isomorphism of function fields. -/
private theorem bijective_functionFieldMap_fp (i : ℕ) :
    Function.Bijective (functionFieldMap (S.fp i)) :=
  (S.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective

/-- A valuation of `k(X_{i+1})` is the transport of at most one valuation of `k(X_i)`. -/
private theorem isTransportedValuation_left_unique {i : ℕ} {η ζ} {η'}
    (h₁ : S.IsTransportedValuation i η η') (h₂ : S.IsTransportedValuation i ζ η') : η = ζ :=
  comap_injective_of_surjective (bijective_functionFieldMap_f S i).2 (h₁.symm.trans h₂)

/-- A valuation of `k(X_i)` has at most one transport to `k(X_{i+1})`. -/
private theorem isTransportedValuation_right_unique {i : ℕ} {η} {η' ζ'}
    (h₁ : S.IsTransportedValuation i η η') (h₂ : S.IsTransportedValuation i η ζ') : η' = ζ' :=
  comap_injective_of_surjective (bijective_functionFieldMap_fp S i).2 (h₁.trans h₂.symm)

/-- Every valuation of `k(X_{i+1})` is the transport of a valuation of `k(X_i)`. -/
private theorem exists_isTransportedValuation {i : ℕ} (η') :
    ∃ η, S.IsTransportedValuation i η η' :=
  exists_comap_eq_of_bijective (bijective_functionFieldMap_f S i) _ |>.imp fun _ h => h.symm

/-- `Corresponds i` is functional. -/
private theorem corresponds_right_unique : ∀ {i : ℕ} {ξ} {η ζ},
    S.Corresponds i ξ η → S.Corresponds i ξ ζ → η = ζ
  | 0, _, _, _, h₁, h₂ => h₁.trans h₂.symm
  | _ + 1, _, _, _, ⟨_, hc₁, ht₁⟩, ⟨_, hc₂, ht₂⟩ => by
    obtain rfl := corresponds_right_unique hc₁ hc₂
    exact isTransportedValuation_right_unique S ht₁ ht₂

/-- Every valuation of `k(X_i)` corresponds to a valuation of `k(X_0)`. -/
private theorem exists_corresponds : ∀ (i : ℕ) (η), ∃ ξ, S.Corresponds i ξ η
  | 0, η => ⟨η, rfl⟩
  | i + 1, η' => by
    obtain ⟨η, hη⟩ := exists_isTransportedValuation S (i := i) η'
    obtain ⟨ξ, hξ⟩ := exists_corresponds i η
    exact ⟨ξ, η, hξ, hη⟩

/-- `I_i`, pulled back to valuations of `k(X_0)`. -/
private def pullbackSet (i : ℕ) : Set (Valuation (S.X 0).functionField ℤᵐ⁰) :=
  {ξ | ∃ η ∈ S.lowDiscrepancySetAt i, S.Corresponds i ξ η}

/-- The pulled-back sets decrease, since `I_{i+1} ⊆ I_i`. -/
private theorem pullbackSet_succ_subset (hsmall : S.IsSmallFrom 0) (hklt : S.IsKlt) (i : ℕ) :
    pullbackSet S (i + 1) ⊆ pullbackSet S i := by
  rintro ξ ⟨η', hη', ζ, hζ, hζη'⟩
  obtain ⟨η, hη, hηη'⟩ := S.exists_mem_lowDiscrepancySetAt_of_mem_succ hsmall hklt i hη'
  obtain rfl := isTransportedValuation_left_unique S hηη' hζη'
  exact ⟨η, hη, hζ⟩

end StepSequence

/-- An antitone sequence of sets, the first of which is finite, is eventually constant. -/
private theorem exists_forall_ge_eq_of_antitone {α : Type*} {P : ℕ → Set α} (hP : Antitone P)
    (h0 : (P 0).Finite) : ∃ i₀, ∀ i, i₀ ≤ i → P i = P i₀ := by
  obtain ⟨i₀, hi₀⟩ := Nat.sInf_mem (Set.range_nonempty fun i => (P i).ncard)
  exact ⟨i₀, fun i hi => Set.eq_of_subset_of_ncard_le (hP hi)
    (hi₀.trans_le (Nat.sInf_le ⟨i, rfl⟩)) (h0.subset (hP (Nat.zero_le _)))⟩

/-- In a step sequence small from the index `0` through klt pairs, the stable low-discrepancy set
`I_∞` is finite, and there is `i₀` such that `I_i = I_∞` for every `i ≥ i₀`: the valuations of
`k(X_i)` corresponding to the elements of `I_∞` are exactly the elements of `I_i`. -/
@[mmp "lem_oai4_c1_low_discrepancy_stabilizes"]
public theorem finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq
    (S : StepSequence) (hsmall : S.IsSmallFrom 0) (hklt : S.IsKlt) :
    S.stableLowDiscrepancySet.Finite ∧
      ∃ i₀, ∀ i, i₀ ≤ i → S.lowDiscrepancySetAt i =
        {η | ∃ ξ ∈ S.stableLowDiscrepancySet, S.Corresponds i ξ η} := by
  have h0 : (pullbackSet S 0).Finite :=
    (finite_lowDiscrepancySet (hklt 0)).subset fun ξ ⟨η, hη, h⟩ => h ▸ hη
  have hanti : Antitone (pullbackSet S) :=
    antitone_nat_of_succ_le (pullbackSet_succ_subset S hsmall hklt)
  have hstable : S.stableLowDiscrepancySet = ⋂ i, pullbackSet S i := by
    ext ξ
    simp [stableLowDiscrepancySet, pullbackSet]
  refine ⟨h0.subset (hstable ▸ Set.iInter_subset _ 0), ?_⟩
  obtain ⟨i₀, hi₀⟩ := exists_forall_ge_eq_of_antitone hanti h0
  have hinf : S.stableLowDiscrepancySet = pullbackSet S i₀ := by
    rw [hstable]
    refine (Set.iInter_subset _ i₀).antisymm (Set.subset_iInter fun i => ?_)
    rcases le_total i i₀ with h | h
    · exact hanti h
    · exact (hi₀ i h).ge
  refine ⟨i₀, fun i hi => Set.ext fun η => ⟨fun hη => ?_, ?_⟩⟩
  · obtain ⟨ξ, hξ⟩ := exists_corresponds S i η
    refine ⟨ξ, ?_, hξ⟩
    rw [hinf, ← hi₀ i hi]
    exact ⟨η, hη, hξ⟩
  · rintro ⟨ξ, hξ, hξη⟩
    rw [hinf, ← hi₀ i hi] at hξ
    obtain ⟨η₁, hη₁, hξη₁⟩ := hξ
    rwa [corresponds_right_unique S hξη hξη₁]

end MMP.Fourfold.StepSequence
