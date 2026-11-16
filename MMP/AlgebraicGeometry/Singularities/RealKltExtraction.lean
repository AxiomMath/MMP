module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.MMP.MinimalModel.SpecifiedExtraction
import MMP.AlgebraicGeometry.Divisor.SmallAffineMovingDivisors
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Vanishing.CoveringTrick
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness

/-!
# Extracting divisors of small log discrepancy from a real klt pair

Let `(X, B)` be an effective klt pair with real boundary on a normal projective complex variety
of dimension `n ≥ 3`, and assume the projective floor-program inputs `P(n)`. Given finitely many
distinct divisorial valuations `E_j` exceptional over `X` with log discrepancy
`a(E_j; X, B) ≤ 1`, there is a projective birational morphism `p : V ⟶ X` from a `ℚ`-factorial
normal projective variety whose exceptional prime divisors are exactly the centres `F_j` of the
`E_j` on `V`; the boundary `B_V = p⁻¹_* B + ∑_j (1 - a(E_j; X, B)) F_j` is effective and klt, and
`K_V + B_V = p^*(K_X + B)`. With no valuations, `p` is a small projective `ℚ`-factorialization.

## Main results

* `MMP.Fourfold.exists_isQFactorial_extraction_of_isRealKltPair`

## Implementation notes

The valuations are given by divisors `E j` over `X` (`MMP.Mori.DivisorOver`), indexed by a finite
type, with pairwise distinct valuations; their log discrepancies `a j` enter through
`MMP.Intersection.IsLogDiscrepancy`. "`p` extracts exactly the `E_j`" is: prime divisors `F j` of
`V` with `ord_{F j} = v(E j)` as valuations of `k(X)`, `j ↦ F j` injective, and the
`p`-exceptional prime divisors are exactly the `F j`. The identity `K_V + B_V = p^*(K_X + B)` is
stated for a canonical divisor `K_V` of `V` with `p_* K_V = K_X` (both cut out by one rational top
form) and the pull-back of `ℝ`-Cartier divisors `MMP.Flips.IsRCartierPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.RealExtractionNormalSource

open MMP.Fourfold MMP.Mori

universe u

section Presentation

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The pull-backs of finitely many Cartier divisors along a divisor `(Y, f, E)` over `X`. -/
private theorem exists_isPullback_divisorOver (D : DivisorOver k sX) {κ : Type*}
    (L : κ → Divisor X) (hL : ∀ x, (L x).IsCartier) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ L' : κ → Divisor D.Y, ∀ x, ∃ hB, (L x).IsPullback D.f hB (L' x) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI : CompactSpace D.Y := D.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
  choose L' hL' using fun x =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hL x)
  exact ⟨L', fun x => ⟨_, hL' x⟩⟩

/-- **The log discrepancy read off a Cartier presentation.** Let `K = div ω` be a canonical
divisor and `K + B = ∑ₓ Rₓ Lₓ` with `Lₓ` Cartier. For a divisor `(Y, f, E)` over `X` with `f`
proper and pull-backs `L'ₓ = f^* Lₓ`, the log discrepancy `a(E; X, B)` is
`1 + ord_E(f^*ω) - ∑ₓ Rₓ coeff_E(L'ₓ)`. -/
private theorem isLogDiscrepancy_of_presentation (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hω : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    {κ : Type*} [Fintype κ] (R : κ → ℝ) (L : κ → Divisor X) (hL : ∀ x, (L x).IsCartier)
    {B : RDivisor X}
    (hB : ∀ Γ, (K.coeff Γ : ℝ) + B.coeff Γ = ∑ x, R x * ((L x).coeff Γ : ℝ))
    (D : DivisorOver k sX) (hD : IsProper D.f) (L' : κ → Divisor D.Y)
    (hL' : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∀ x, ∃ hB, (L x).IsPullback D.f hB (L' x)) :
    MMP.Intersection.IsLogDiscrepancy sX n B D
      (1 + (D.ordPullback ω : ℝ) - ∑ x, R x * ((L' x).coeff D.E : ℝ)) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  let e := Fintype.equivFin κ
  refine ⟨hX, hD, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, Fintype.card κ, R ∘ e.symm,
    L ∘ e.symm, L' ∘ e.symm, fun j => hL _, fun Γ => ?_, fun j => hL' _, ?_⟩
  · rw [hω, hB, ← e.symm.sum_comp]
    rfl
  · rw [← e.symm.sum_comp (fun x => R x * ((L' x).coeff D.E : ℝ))]
    rfl

end Presentation

section Coefficients

open scoped Classical in
/-- The coefficient of the image of a divisor under a partial map `φ` of prime divisors at `Γ`:
the sum of the coefficients along the prime divisors that `φ` sends to `Γ`. -/
private theorem coeff_mapPrimeDivisors {R : Type*} [AddCommMonoid R] {X Y : Scheme.{u}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : DivisorWithCoeffs R X)
    (Γ : MMP.Mori.PrimeDivisor Y) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Γ =
      ∑ P ∈ D.support, if φ P = some Γ then D P else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply,
    Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun P _ => ?_
  cases h : φ P with
  | none => simp
  | some Q => simp [Finsupp.single_apply]

open scoped Classical in
/-- The coefficients of `∑_{P ∈ s} f(P) P` for a finite set `s` of prime divisors. -/
private theorem coeff_sum_single_coe {R : Type*} [AddCommMonoid R] {X : Scheme.{u}}
    (s : Finset (MMP.Mori.PrimeDivisor X)) (f : s → R) (Γ : MMP.Mori.PrimeDivisor X) :
    (∑ i : s, Finsupp.single i.1 (f i) : DivisorWithCoeffs R X).coeff Γ =
      if h : Γ ∈ s then f ⟨Γ, h⟩ else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨Γ, h⟩ (fun i _ hi => by
      simp only [Finsupp.single_apply]
      exact if_neg fun h' => hi (Subtype.ext h')) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun i _ => by
      simp only [Finsupp.single_apply]
      exact if_neg fun (h' : i.1 = Γ) => h (h' ▸ i.2)

/-- The coefficients of a combination `∑ⱼ rⱼ Lⱼ` of integral divisors. -/
private theorem coeff_sum_smul_mapCoeffs {R : Type*} [Ring R] {X : Scheme.{u}} {m : ℕ}
    (r : Fin m → R) (L : Fin m → Divisor X) (Γ : MMP.Mori.PrimeDivisor X) :
    (∑ j, r j • (L j).mapCoeffs (Int.cast : ℤ → R) Int.cast_zero).coeff Γ =
      ∑ j, r j * ((L j).coeff Γ : R) := by
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, DivisorWithCoeffs.mapCoeffs,
    Finsupp.mapRange_apply]

end Coefficients

section RealCrepant

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **The real crepant boundary on a model extracting exactly the given divisors.** Let `(X, B)`
be an effective real klt pair with `K + B` `ℝ`-Cartier, and `p : V ⟶ X` a proper birational
morphism from a normal variety whose exceptional prime divisors are exactly the `F j`, with
`ord_{F j} = v(E j)` and `a j = a(E j; X, B) ≤ 1`. Then `B_V = p⁻¹_* B + ∑ⱼ (1 - a j) F j` is
effective and klt, and `K_V + B_V = p^*(K + B)` for some canonical divisor `K_V` of `V` with
`p_* K_V = K`. -/
private theorem nonneg_and_isRealKltPair_and_exists_isRCartierPullback
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + B))
    {ι : Type*} [Fintype ι] (E : ι → DivisorOver ℂ sX) (a : ι → ℝ)
    (ha : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n B (E j) (a j)) (ha1 : ∀ j, a j ≤ 1)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {p : V ⟶ X}
    (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) [IsProper p]
    (F : ι → MMP.Mori.PrimeDivisor V) (hF : Function.Injective F)
    (hval : ∀ j, (⟨V, p, hV, hp, F j⟩ : DivisorOver ℂ sX).valuation = (E j).valuation)
    (hexc : ∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) p.toRationalMap P ↔ P ∈ Set.range F) :
    (∀ P, 0 ≤ (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j)).coeff P) ∧
      IsRealKltPair (p ≫ sX)
        (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j)) ∧
      ∃ KV : Divisor V, KV.IsCanonicalDivisor (p ≫ sX) n ∧
        RationalMap.transformDivisor p.toRationalMap KV = K ∧
        MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor K B)
          (MMP.Flips.logCanonicalDivisor KV
            (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j))) := by
  classical
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ (p ≫ sX) := hV.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : LocallyOfFiniteType (p ≫ sX) := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace V := hV.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : IsDominant p := hp.isDominant
  set BV := inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j) with hBV
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hnV : topologicalKrullDim V = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp).symm.trans hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, R, L, hLc, hKBeq⟩ := hKB
  have hKBeq' : Divisor.toRDivisor K + B = ∑ x, R x • Divisor.toRDivisor (L x) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hKBeq
  have hpres : ∀ Γ, (K.coeff Γ : ℝ) + B.coeff Γ = ∑ x, R x * ((L x).coeff Γ : ℝ) := by
    intro Γ
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hKBeq'
    simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor] using this
  choose L' hL' using fun x => MMP.Threefold.Bridges.exists_isPullback_of_isDominant p (hLc x)
  have hL'c : ∀ x, (L' x).IsCartier := fun x => (hL' x).isCartier (hLc x)
  set ωV : RationalPluriForms (p ≫ sX) n 1 := pullbackRationalPluriForms sX p ω
  set KV : Divisor V := divisorOfForm ωV
  have hωV0 : ωV ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hp.functionFieldMap_bijective hd hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hV hnV
  have hKV : KV.IsCanonicalDivisor (p ≫ sX) n := hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hωV0)
  -- the log discrepancy of each prime divisor of `V`
  let DP : MMP.Mori.PrimeDivisor V → DivisorOver ℂ sX := fun P => ⟨V, p, hV, hp, P⟩
  have hlogP : ∀ P, MMP.Intersection.IsLogDiscrepancy sX n B (DP P)
      (1 + (KV.coeff P : ℝ) - ∑ x, R x * ((L' x).coeff P : ℝ)) := fun P =>
    isLogDiscrepancy_of_presentation hX hK hω0 hω R L hLc hpres (DP P) inferInstance L'
      fun x => ⟨_, hL' x⟩
  have hkey : ∀ P, BV.coeff P = 1 - (1 + (KV.coeff P : ℝ) - ∑ x, R x * ((L' x).coeff P : ℝ)) ∧
      0 ≤ BV.coeff P := by
    intro P
    have hBVc : BV.coeff P = (inverseTransformDivisor p B).coeff P +
        ∑ j, (Finsupp.single (F j) (1 - a j) : RDivisor V) P := by
      rw [hBV, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_apply (∑ j, _),
        Finsupp.finset_sum_apply]
    by_cases hP : P ∈ Set.range F
    · obtain ⟨j, rfl⟩ := hP
      have haj := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq (hlogP (F j)) (ha j)
        (hval j)
      have h0 : (inverseTransformDivisor p B).coeff (F j) = 0 := by
        change (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff (F j) = 0
        rw [coeff_mapPrimeDivisors]
        refine Finset.sum_eq_zero fun Q _ => if_neg fun hQ => ?_
        have hη :=
          (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1
        have hex := (hexc (F j)).2 ⟨j, rfl⟩
        have h2 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX (DP (F j))).1 hex
        change 2 ≤ Order.coheight (p (F j).genericPoint) at h2
        rw [hη, Q.coheight_genericPoint] at h2
        exact absurd h2 (by decide)
      have h1 : ∑ j', (Finsupp.single (F j') (1 - a j') : RDivisor V) (F j) = 1 - a j := by
        rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Finsupp.single_apply, hF.eq_iff, hj'])
          (by simp)]
        simp
      rw [hBVc, h0, h1, zero_add, haj]
      exact ⟨by ring, by linarith [ha1 j]⟩
    · have hne : ¬ (DP P).IsExceptional := fun h => hP ((hexc P).1 h)
      obtain ⟨Q, hQv⟩ : ∃ Q : MMP.Mori.PrimeDivisor X,
          (DP P).valuation = (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation := by
        by_contra hcon
        push Not at hcon
        apply hne
        rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX,
          ← MMP.Positivity.DivisorOver.codimension_center]
        exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX _).2 hcon
      have hlogQ : MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
          (1 - B.coeff Q) := by
        have h := isLogDiscrepancy_of_presentation hX hK hω0 hω R L hLc hpres
          (DivisorOver.ofPrimeDivisor ℂ hX Q) (by change IsProper (𝟙 X); infer_instance) L
          (fun x => ⟨_, MMP.Mori.divisor_isPullback_id (L x)
            (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (𝟙 X) (L x))⟩)
        convert h using 1
        rw [MMP.Mori.DivisorOver.ordPullback_ofPrimeDivisor hX hn Q ω, hω]
        change _ = 1 + (K.coeff Q : ℝ) - ∑ x, R x * ((L x).coeff Q : ℝ)
        rw [← hpres Q]
        ring
      have haQ := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq (hlogP P) hlogQ hQv
      have hη : p P.genericPoint = Q.genericPoint :=
        MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hQv
      have hbir : p P.genericPoint ∈ biregularLocus p := by
        by_contra hx
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
          (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX p (hY := hX.1) (hX := hV.1)
            hp) _ hx
        rw [hη, Q.coheight_genericPoint] at this
        exact absurd this (by decide)
      have hinv :=
        MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη hbir
      have huniq : ∀ Q', inverseTransformPrimeDivisor p Q' = some P → Q' = Q := fun Q' h =>
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
            h).1.symm.trans hη)
      have hcoef : (inverseTransformDivisor p B).coeff P = B.coeff Q := by
        change (DivisorWithCoeffs.mapPrimeDivisors _ B).coeff P = _
        rw [coeff_mapPrimeDivisors]
        by_cases hQs : Q ∈ B.support
        · rw [Finset.sum_eq_single Q (fun Q' _ hQ' => if_neg fun h => hQ' (huniq Q' h))
            (fun h => absurd hQs h), if_pos hinv]
          rfl
        · rw [Finset.sum_eq_zero fun Q' hQ' => if_neg fun h => hQs (huniq Q' h ▸ hQ')]
          exact (Finsupp.notMem_support_iff.mp hQs).symm
      have h1 : ∑ j, (Finsupp.single (F j) (1 - a j) : RDivisor V) P = 0 :=
        Finset.sum_eq_zero fun j _ => by
          simp [Finsupp.single_apply, show F j ≠ P from fun h => hP ⟨j, h⟩]
      rw [hBVc, hcoef, h1, add_zero, haQ]
      exact ⟨by ring, hB Q⟩
  have hpresV : ∀ Γ, (KV.coeff Γ : ℝ) + BV.coeff Γ = ∑ x, R x * ((L' x).coeff Γ : ℝ) :=
    fun Γ => by rw [(hkey Γ).1]; ring
  have hGeq : Divisor.toRDivisor KV + BV = ∑ x, R x • Divisor.toRDivisor (L' x) := by
    refine Finsupp.ext fun Γ => ?_
    have h := hpresV Γ
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor] at h
    exact h
  refine ⟨fun P => (hkey P).2, ⟨hV, fun P => ?_, ⟨n, KV, hKV, m, R, L', hL'c, fun Γ => ?_⟩, ?_⟩,
    KV, hKV, ?_, m, R, L, L', hLc, hKBeq', fun x => ⟨_, hL' x⟩, hGeq⟩
  · have hpos := hklt.2.2.2 n (DP P) _ (hlogP P)
    rw [(hkey P).1]
    linarith
  · exact hpresV Γ
  · -- crepant invariance of the log discrepancies
    intro n' D a₀ h₀
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    haveI := D.isIntegral
    haveI := D.isDominant
    haveI hD : IsProper D.f := h₀.2.1
    obtain ⟨L'', hL''⟩ := exists_isPullback_divisorOver D L' hL'c
    have h₁ := isLogDiscrepancy_of_presentation hV hKV hωV0 (fun Γ => rfl) R L' hL'c hpresV D hD
      L'' hL''
    have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h₀ h₁
    have hD' : IsProper (MMP.Mori.compDivisorOver p hV hp D).f := by
      change IsProper (D.f ≫ p)
      infer_instance
    have h₂ := isLogDiscrepancy_of_presentation hX hK hω0 hω R L hLc hpres
      (MMP.Mori.compDivisorOver p hV hp D) hD' L'' (fun x => by
        obtain ⟨hB'', h''⟩ := hL'' x
        exact ⟨_, MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hL' x) h''
          (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ p) (L x))⟩)
    have hpos := hklt.2.2.2 n _ _ h₂
    have hord : (MMP.Mori.compDivisorOver p hV hp D).ordPullback ω = D.ordPullback ωV := by
      change D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ p) ω) =
        D.E.ordForm (pullbackRationalPluriForms (p ≫ sX) D.f (pullbackRationalPluriForms sX p ω))
      rw [MMP.Flips.pullbackRationalPluriForms_comp p D.f hp.functionFieldMap_bijective
        D.isBirationalMorphism.functionFieldMap_bijective hd ω]
      rfl
    rw [heq]
    rw [hord] at hpos
    exact hpos
  · -- the push-forward of `K_V`
    refine Finsupp.ext fun P => ?_
    obtain ⟨E', hE', hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hV hp P
    rw [htr]
    change E'.ordForm ωV = K P
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hp.functionFieldMap_bijective
      hd E' P hE' ω, hω]
    rfl

end RealCrepant

section RationalAffine

open Topology Filter

variable {p : ℕ}

private theorem ratAffineForm_add (f g : (Fin p → ℚ) × ℚ) (x : Fin p → ℝ) :
    ratAffineForm (f + g) x = ratAffineForm f x + ratAffineForm g x := by
  simp only [ratAffineForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

private theorem ratAffineForm_smul (c : ℚ) (f : (Fin p → ℚ) × ℚ) (x : Fin p → ℝ) :
    ratAffineForm (c • f) x = c * ratAffineForm f x := by
  simp only [ratAffineForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Rat.cast_mul, mul_add, Finset.mul_sum, mul_assoc]

private theorem ratAffineForm_neg (f : (Fin p → ℚ) × ℚ) (x : Fin p → ℝ) :
    ratAffineForm (-f) x = -ratAffineForm f x := by
  simpa using ratAffineForm_smul (-1) f x

private theorem ratAffineForm_sub (f g : (Fin p → ℚ) × ℚ) (x : Fin p → ℝ) :
    ratAffineForm (f - g) x = ratAffineForm f x - ratAffineForm g x := by
  rw [sub_eq_add_neg, ratAffineForm_add, ratAffineForm_neg, ← sub_eq_add_neg]

private theorem ratAffineForm_sum {α : Type*} (s : Finset α) (f : α → (Fin p → ℚ) × ℚ)
    (x : Fin p → ℝ) : ratAffineForm (∑ a ∈ s, f a) x = ∑ a ∈ s, ratAffineForm (f a) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ratAffineForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratAffineForm_add, ih]

private theorem ratAffineForm_const (q : ℚ) (x : Fin p → ℝ) :
    ratAffineForm ((0, q) : (Fin p → ℚ) × ℚ) x = q := by
  simp [ratAffineForm]

private theorem ratAffineForm_single (j : Fin p) (x : Fin p → ℝ) :
    ratAffineForm ((Pi.single j 1, 0) : (Fin p → ℚ) × ℚ) x = x j := by
  simp [ratAffineForm, Pi.single_apply, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]

/-- **The midpoint argument.** A rational affine function nonnegative on the ball of radius `ε`
about `t₀` and positive at `t₀` is positive on the ball of radius `ε / 2`: its value at `q` is the
mean of its values at `t₀` and at the reflection `2q - t₀`, which lies in the larger ball. -/
private theorem ratAffineForm_pos_of_nonneg_ball (f : (Fin p → ℚ) × ℚ) {t₀ q : Fin p → ℝ} {ε : ℝ}
    (hf : ∀ t, dist t t₀ < ε → 0 ≤ ratAffineForm f t) (h₀ : 0 < ratAffineForm f t₀)
    (hq : dist q t₀ < ε / 2) : 0 < ratAffineForm f q := by
  have h := hf ((2 : ℝ) • (q - t₀) + t₀) (by
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, ← dist_eq_norm]
    norm_num
    linarith)
  rw [ratAffineForm_affine] at h
  linarith

/-- The rational points are dense in `ℝ^p`. -/
private theorem denseRange_ratCast_pi :
    DenseRange fun q : Fin p → ℚ => fun j => (q j : ℝ) :=
  DenseRange.piMap fun _ => Rat.denseRange_cast

/-- **Rational points near `t₀` on its smallest rational affine hull.** For finitely many rational
affine functions nonnegative at `t₀` and a neighbourhood `U` of `t₀`, there is a rational point of
`U` at which they are all still nonnegative. -/
private theorem exists_rat_mem_of_nonneg (t₀ : Fin p → ℝ) {U : Set (Fin p → ℝ)} (hU : U ∈ 𝓝 t₀)
    (I : Finset ((Fin p → ℚ) × ℚ)) (hI : ∀ f ∈ I, 0 ≤ ratAffineForm f t₀) :
    ∃ q : Fin p → ℚ, (fun j => (q j : ℝ)) ∈ U ∧
      ∀ f ∈ I, 0 ≤ ratAffineForm f fun j => (q j : ℝ) := by
  classical
  set N : Set (Fin p → ℝ) :=
    {x | (∀ f ∈ (∅ : Finset ((Fin p → ℚ) × ℚ)), ratAffineForm f x = 0) ∧
      ∀ f ∈ I, 0 ≤ ratAffineForm f x}
  have hN : IsRationalPolyhedron N := ⟨∅, I, rfl⟩
  have hN₀ : N ∈ 𝓝[(rationalAffineHull t₀ : Set (Fin p → ℝ))] t₀ :=
    (rational_hull_neighborhood hN ⟨by simp, hI⟩).1
  obtain ⟨m, p₀, e, -, -, hchar⟩ := exists_rational_frame t₀
  obtain ⟨s₀, hs₀⟩ := (hchar t₀).1 (self_mem_rationalAffineHull t₀)
  let φ : (Fin m → ℝ) → (Fin p → ℝ) := fun s j => (p₀ j : ℝ) + ∑ i, s i * (e i j : ℝ)
  have hφc : Continuous φ := by fun_prop
  have hφt : Tendsto φ (𝓝 s₀) (𝓝[(rationalAffineHull t₀ : Set (Fin p → ℝ))] t₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun s => (hchar _).2 ⟨s, rfl⟩⟩
    have := hφc.tendsto s₀
    rwa [show φ s₀ = t₀ from hs₀.symm] at this
  have hA : φ ⁻¹' (N ∩ U) ∈ 𝓝 s₀ := hφt (inter_mem hN₀ (mem_nhdsWithin_of_mem_nhds hU))
  obtain ⟨O, hOA, hO, hs₀O⟩ := mem_nhds_iff.1 hA
  obtain ⟨s, hsO⟩ := (denseRange_ratCast_pi (p := m)).exists_mem_open hO ⟨s₀, hs₀O⟩
  obtain ⟨hsN, hsU⟩ := hOA hsO
  refine ⟨fun j => p₀ j + ∑ i, s i * e i j, ?_, fun f hf => ?_⟩
  · convert hsU using 1
    funext j
    push_cast
    rfl
  · convert hsN.2 f hf using 2
    funext j
    push_cast
    rfl

/-- A continuous function nonnegative at the rational points of an open set is nonnegative on
it. -/
private theorem nonneg_of_forall_ratCast {U : Set (Fin p → ℝ)} (hU : IsOpen U)
    {f : (Fin p → ℝ) → ℝ} (hf : Continuous f)
    (h : ∀ q : Fin p → ℚ, (fun j => (q j : ℝ)) ∈ U → 0 ≤ f fun j => (q j : ℝ)) {t : Fin p → ℝ}
    (ht : t ∈ U) : 0 ≤ f t := by
  by_contra hlt
  push Not at hlt
  have hO : IsOpen (U ∩ f ⁻¹' Set.Iio 0) := hU.inter (isOpen_Iio.preimage hf)
  obtain ⟨q, hqU, hq⟩ := denseRange_ratCast_pi.exists_mem_open hO ⟨t, ht, hlt⟩
  exact absurd (h q hqU) (not_le.2 hq)

end RationalAffine

section RationalApproximation

open Topology Filter

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **A nearby rational klt boundary.** Let `(X, B)` be an effective real klt pair with `K + B`
`ℝ`-Cartier, and `E j` finitely many divisors over `X` with `a(E j; X, B) ≤ 1`. Then there is an
effective `ℚ`-divisor `Δ` with `(X, Δ)` klt and `0 < a(E j; X, Δ) ≤ 1` for every `j`. -/
private theorem exists_isKltPair_isLogDiscrepancy_le_one (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + B))
    {ι : Type*} [Fintype ι] (E : ι → DivisorOver ℂ sX) (a : ι → ℝ)
    (ha : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n B (E j) (a j)) (ha1 : ∀ j, a j ≤ 1) :
    ∃ Δ : QDivisor X, IsKltPair sX Δ ∧ ∀ j, ∃ a' : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) (E j) a' ∧
        0 < a' ∧ a' ≤ 1 := by
  classical
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  -- the components of `B` and the rational Cartier locus through its coefficients
  let P : B.support → MMP.Mori.PrimeDivisor X := Subtype.val
  have hBsum : ∑ i : B.support, Finsupp.single (P i) (B.coeff i.1) = B := by
    rw [Finset.sum_coe_sort B.support (fun x => Finsupp.single x (B.coeff x))]
    exact Finsupp.sum_single B
  obtain ⟨Vs, b₀, p, w, hVs, hbV, hVR, hVq, -⟩ :=
    exists_rat_affineSubspace_isCartierCombination_and_coeff_pullback_affine sX hX hK P
      (fun i => B.coeff i.1) (by simp only [hBsum]; exact hKB)
  -- its parametrization `t ↦ c(t) = b₀ + ∑ⱼ tⱼ wⱼ`
  let cq : (Fin p → ℚ) → B.support → ℚ := fun q i => b₀ i + ∑ j, q j * w j i
  let c : (Fin p → ℝ) → B.support → ℝ := fun t i => (b₀ i : ℝ) + ∑ j, t j * (w j i : ℝ)
  have hccast : ∀ q i, ((cq q i : ℚ) : ℝ) = c (fun j => (q j : ℝ)) i := fun q i => by
    simp [cq, c]
  have hcV : ∀ t, (fun i => c t i) ∈ Vs := by
    intro t
    rw [hVs, AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun]
    refine ⟨t, funext fun i => ?_⟩
    simp [c, Finset.sum_apply]
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Fin p → ℝ, ∀ i, c t₀ i = B.coeff i.1 := by
    rw [hVs, AffineSubspace.mem_mk', Submodule.mem_span_range_iff_exists_fun] at hbV
    obtain ⟨t, ht⟩ := hbV
    refine ⟨t, fun i => ?_⟩
    have := congrFun ht i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vsub_eq_sub, Pi.sub_apply] at this
    simp only [c]
    linarith
  let BR : (Fin p → ℝ) → RDivisor X := fun t => ∑ i, Finsupp.single (P i) (c t i)
  let BQ : (Fin p → ℚ) → QDivisor X := fun q => ∑ i, Finsupp.single (P i) (cq q i)
  have hBRcoeff : ∀ t Γ, (BR t).coeff Γ = if h : Γ ∈ B.support then c t ⟨Γ, h⟩ else 0 :=
    fun t Γ => coeff_sum_single_coe B.support (c t) Γ
  have hBQcoeff : ∀ q Γ, (BQ q).coeff Γ = if h : Γ ∈ B.support then cq q ⟨Γ, h⟩ else 0 :=
    fun q Γ => coeff_sum_single_coe B.support (cq q) Γ
  have hBQR : ∀ q, QDivisor.toRDivisor (BQ q) = BR (fun j => (q j : ℝ)) := by
    intro q
    refine Finsupp.ext fun Γ => ?_
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      QDivisor.coeff_toRDivisor, hBQcoeff, hBRcoeff]
    split_ifs
    · exact hccast _ _
    · simp
  have hBRt₀ : BR t₀ = B := by
    refine Finsupp.ext fun Γ => ?_
    rw [← DivisorWithCoeffs.coeff_apply, hBRcoeff]
    split_ifs with h
    · exact ht₀ _
    · exact (Finsupp.notMem_support_iff.1 h).symm
  -- rational presentations of `K + B(t)` at the vertices `0, e₁, …, e_p`
  let uq : Option (Fin p) → Fin p → ℚ := fun o => o.elim 0 fun j => Pi.single j 1
  have hpo : ∀ o, MMP.Flips.IsCartierCombination (Divisor.toQDivisor K + BQ (uq o)) := fun o =>
    hVq (cq (uq o)) (by
      convert hcV (fun j => (uq o j : ℝ)) using 1
      funext i
      exact hccast _ _)
  choose m r L hL hLeq using hpo
  have hLcoeff : ∀ o Γ, (K.coeff Γ : ℝ) + (BR (fun j => (uq o j : ℝ))).coeff Γ =
      ∑ i, (r o i : ℝ) * ((L o i).coeff Γ : ℝ) := by
    intro o Γ
    have := congrArg (fun D : QDivisor X => ((D.coeff Γ : ℚ) : ℝ)) (hLeq o)
    simp only [DivisorWithCoeffs.coeff_add, coeff_sum_smul_mapCoeffs, Rat.cast_add,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at this
    rw [← hBQR, QDivisor.coeff_toRDivisor, ← this]
    simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom,
      DivisorWithCoeffs.coeff_apply]
  -- the barycentric weights `λ_o(t)` of the vertices, rational affine in `t`
  let lam : Option (Fin p) → (Fin p → ℝ) → ℝ := fun o t => o.elim (1 - ∑ j, t j) t
  let glam : Option (Fin p) → (Fin p → ℚ) × ℚ :=
    fun o => o.elim ((fun _ => -1, 1) : (Fin p → ℚ) × ℚ) fun j => (Pi.single j 1, 0)
  have hglam : ∀ o t, lam o t = ratAffineForm (glam o) t := by
    rintro (_ | j) t
    · simp only [lam, glam, Option.elim_none, ratAffineForm]
      push_cast
      simp only [neg_one_mul, Finset.sum_neg_distrib]
      ring
    · exact (ratAffineForm_single j t).symm
  have hlam_aff : ∀ (α : ℝ) (β : Fin p → ℝ) (t : Fin p → ℝ),
      ∑ o, lam o t * (α + ∑ j, (uq o j : ℝ) * β j) = α + ∑ j, t j * β j := by
    intro α β t
    have hs : ∀ j', ∑ j, (((Pi.single j' 1 : Fin p → ℚ) j : ℚ) : ℝ) * β j = β j' := fun j' => by
      simp [Pi.single_apply, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]
    rw [Fintype.sum_option]
    simp only [lam, uq, Option.elim_none, Option.elim_some, Pi.zero_apply, Rat.cast_zero,
      zero_mul, Finset.sum_const_zero, add_zero, hs, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, sub_mul, one_mul]
    ring
  -- a presentation of `K + B(t)` with coefficients rational affine in `t`
  let R : (Fin p → ℝ) → (Σ o, Fin (m o)) → ℝ := fun t x => lam x.1 t * (r x.1 x.2 : ℝ)
  let Lk : (Σ o, Fin (m o)) → Divisor X := fun x => L x.1 x.2
  have hLk : ∀ x, (Lk x).IsCartier := fun x => hL x.1 x.2
  have hpresT : ∀ t Γ, (K.coeff Γ : ℝ) + (BR t).coeff Γ = ∑ x, R t x * ((Lk x).coeff Γ : ℝ) := by
    intro t Γ
    rw [Fintype.sum_sigma]
    simp only [R, Lk, mul_assoc, ← Finset.mul_sum, ← hLcoeff, hBRcoeff]
    split_ifs with h
    · calc (K.coeff Γ : ℝ) + c t ⟨Γ, h⟩
          = (K.coeff Γ + b₀ ⟨Γ, h⟩) + ∑ j, t j * (w j ⟨Γ, h⟩ : ℝ) := by
            simp only [c, add_assoc]
        _ = ∑ o, lam o t * ((K.coeff Γ + b₀ ⟨Γ, h⟩) + ∑ j, (uq o j : ℝ) * (w j ⟨Γ, h⟩ : ℝ)) :=
            (hlam_aff _ _ t).symm
        _ = _ := by simp only [c, add_assoc]
    · have := hlam_aff (K.coeff Γ) 0 t
      simpa using this.symm
  -- the log discrepancies `a_D(t)` of `(X, B(t))`
  choose L' hL' using fun D : DivisorOver ℂ sX => exists_isPullback_divisorOver D Lk hLk
  let aD : DivisorOver ℂ sX → (Fin p → ℝ) → ℝ := fun D t =>
    1 + (D.ordPullback ω : ℝ) - ∑ x, R t x * ((L' D x).coeff D.E : ℝ)
  have hlog : ∀ D : DivisorOver ℂ sX, IsProper D.f → ∀ t,
      MMP.Intersection.IsLogDiscrepancy sX n (BR t) D (aD D t) := fun D hD t =>
    isLogDiscrepancy_of_presentation hX hK hω0 hω (R t) Lk hLk (hpresT t) D hD (L' D) (hL' D)
  let gD : DivisorOver ℂ sX → (Fin p → ℚ) × ℚ := fun D =>
    ((0, 1 + (D.ordPullback ω : ℚ)) : (Fin p → ℚ) × ℚ) -
      ∑ x : (Σ o, Fin (m o)), (r x.1 x.2 * ((L' D x).coeff D.E : ℚ)) • glam x.1
  have haff : ∀ D t, aD D t = ratAffineForm (gD D) t := by
    intro D t
    simp only [gD, ratAffineForm_sub, ratAffineForm_const, ratAffineForm_sum, ratAffineForm_smul,
      ← hglam, aD, R]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have hcont : ∀ D, Continuous (aD D) := fun D => by
    rw [show aD D = ratAffineForm (gD D) from funext (haff D)]
    exact continuous_ratAffineForm _
  have hpos₀ : ∀ D : DivisorOver ℂ sX, IsProper D.f → 0 < aD D t₀ := fun D hD => by
    have := hlog D hD t₀
    rw [hBRt₀] at this
    exact hklt.2.2.2 n D _ this
  -- a projective log resolution of `(X, B)`
  obtain ⟨W, π, hres, hπproj⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hX B
  obtain ⟨hW, -, -⟩ := hres.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : IsProper π := hres.isProper
  have hbir : IsBirationalMorphism π := hres.isBirationalMorphism
  let DF : MMP.Mori.PrimeDivisor W → DivisorOver ℂ sX := fun F => ⟨W, π, hW, hbir, F⟩
  have hDFp : ∀ F, IsProper (DF F).f := fun F => hres.isProper
  -- its exceptional prime divisors are finitely many
  obtain ⟨S, hS⟩ : ∃ S : Finset (MMP.Mori.PrimeDivisor W),
      ∀ F, (DF F).IsExceptional → F ∈ S := by
    have hmem : ∀ F, (DF F).IsExceptional → F.genericPoint ∈
        ((exceptionalSet π ⊔ B.supp.preimage π.continuous : TopologicalSpace.Closeds W) :
          Set W) := fun F hF =>
      Or.inl (MMP.Positivity.support_subset_exceptionalSet F hF
        (MMP.Flips.primeDivisor_genericPoint_mem_support F))
    rcases hres.isSNCSubset with h0 | ⟨s, hs, -⟩
    · refine ⟨∅, fun F hF => ?_⟩
      have := hmem F hF
      rw [h0] at this
      exact absurd this (by simp)
    · refine ⟨s, fun F hF => ?_⟩
      have := hmem F hF
      rw [← hs] at this
      obtain ⟨E', hE', hgen⟩ := Set.mem_iUnion₂.mp this
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE'
  -- the strict inequalities at `t₀` persist on a ball
  have hci : ∀ i, Continuous fun t => c t i := fun i => by
    show Continuous fun t : Fin p → ℝ => (b₀ i : ℝ) + ∑ j, t j * (w j i : ℝ)
    fun_prop
  have hev : ∀ᶠ t in 𝓝 t₀, (∀ i, 0 < c t i ∧ c t i < 1) ∧
      ∀ F ∈ S, (DF F).IsExceptional → 0 < aD (DF F) t := by
    refine Filter.eventually_and.2 ⟨Filter.eventually_all.2 fun i => ?_,
      (Filter.eventually_all_finset S).2 fun F _ => ?_⟩
    · have h1 : 0 < c t₀ i := by
        rw [ht₀]
        exact lt_of_le_of_ne (hB _) (Ne.symm (Finsupp.mem_support_iff.1 i.2))
      have h2 : c t₀ i < 1 := by
        rw [ht₀]
        exact hklt.2.1 _
      exact (((hci i).tendsto t₀).eventually (lt_mem_nhds h1)).and
        (((hci i).tendsto t₀).eventually (gt_mem_nhds h2))
    · by_cases hFe : (DF F).IsExceptional
      · exact (((hcont _).tendsto t₀).eventually (lt_mem_nhds (hpos₀ _ (hDFp F)))).mono
          fun t ht _ => ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hFe
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  -- the rational boundaries `B(q)` near `t₀` are lc
  have hQC : ∀ q, (Divisor.toQDivisor K + BQ q).IsQCartier := fun q =>
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination (by
      rw [map_add, QDivisor.toRDivisor_toQDivisor, hBQR]
      exact hVR _ (hcV _))
  have hpair : ∀ q : Fin p → ℚ, dist (fun j => (q j : ℝ)) t₀ < ε →
      MMP.Fourfold.IsPair sX (BQ q) := by
    intro q hq
    have hc := (hball hq).1
    refine ⟨inferInstance, inferInstance, ⟨hX, n, K, hK, hQC q⟩, fun Γ => ?_⟩
    rw [hBQcoeff]
    split_ifs with h
    · have := (hc ⟨Γ, h⟩).1
      rw [← hccast] at this
      exact_mod_cast this.le
    · exact le_rfl
  have hres' : ∀ t : Fin p → ℝ, (∀ i, c t i ≠ 0) → MMP.Mori.IsLogResolution sX (BR t) π := by
    intro t ht
    have hsupp : (BR t).supp = B.supp := by
      have : (BR t).support = B.support := by
        ext Γ
        rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hBRcoeff]
        split_ifs with h
        · exact ⟨fun _ => h, fun _ => ht _⟩
        · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩
      simp only [DivisorWithCoeffs.supp, this]
    exact { hres with isSNCSubset := by rw [hsupp]; exact hres.isSNCSubset }
  have hlc : ∀ q : Fin p → ℚ, dist (fun j => (q j : ℝ)) t₀ < ε →
      MMP.Intersection.IsLogCanonicalPair sX (BQ q) := by
    intro q hq
    have hc := (hball hq).1
    have hexc := (hball hq).2
    have hP := hpair q hq
    have hπq : MMP.Fourfold.IsLogResolution sX (BQ q) π :=
      ⟨by rw [hBQR]; exact hres' _ fun i => (hc i).1.ne', hπproj⟩
    obtain ⟨⟨BW, hBW, -⟩, -⟩ :=
      MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP.isPair hK π hW hbir
    refine (MMP.Fourfold.isLogCanonicalPair_iff_forall_coeff_le_one sX hP hπq hW hBW).2
      fun F => ?_
    have hd1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBW F) (hDFp F)
    rw [hBQR] at hd1
    by_cases hFe : (DF F).IsExceptional
    · have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hd1 (hlog (DF F) (hDFp F) _)
      have h2 := hexc F (hS F hFe) hFe
      have : ((BW.coeff F : ℚ) : ℝ) ≤ 1 := by
        push_cast at h1
        linarith
      exact_mod_cast this
    · obtain ⟨Q, -, hdQ⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
        ⟨hX, hK, hQC q⟩ (DF F) hFe
      have heq := neg_injective ((hBW F).eq hdQ)
      rw [heq, hBQcoeff]
      split_ifs with h
      · have := (hc ⟨Q, h⟩).2
        rw [← hccast] at this
        exact_mod_cast this.le
      · norm_num
  -- hence every log discrepancy is nonnegative on the ball
  have hnonneg : ∀ D : DivisorOver ℂ sX, IsProper D.f → ∀ t, dist t t₀ < ε → 0 ≤ aD D t := by
    intro D hD t ht
    refine nonneg_of_forall_ratCast (U := Metric.ball t₀ ε) Metric.isOpen_ball (hcont D)
      (fun q hq => ?_) ht
    have := hlog D hD (fun j => (q j : ℝ))
    rw [← hBQR] at this
    exact (hlc q hq).2.2 n D _ this
  -- a rational point of the hull of `t₀`, close to `t₀`, keeping `a(E j) ≤ 1`
  let g₁ : ι → (Fin p → ℚ) × ℚ := fun j => ((0, 1) : (Fin p → ℚ) × ℚ) - gD (E j)
  have hg₁ : ∀ j t, ratAffineForm (g₁ j) t = 1 - aD (E j) t := fun j t => by
    simp only [g₁, ratAffineForm_sub, ratAffineForm_const, ← haff]
    push_cast
    ring
  have haj : ∀ j, aD (E j) t₀ = a j := fun j => by
    have := hlog (E j) (ha j).2.1 t₀
    rw [hBRt₀] at this
    exact MMP.Threefold.Bridges.IsLogDiscrepancy.unique this (ha j)
  obtain ⟨q, hqU, hqI⟩ := exists_rat_mem_of_nonneg t₀ (Metric.ball_mem_nhds t₀ (half_pos hε))
    (Finset.univ.image g₁) (by
      intro f hf
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hf
      rw [hg₁, haj]
      linarith [ha1 j])
  replace hqU : dist (fun j => (q j : ℝ)) t₀ < ε / 2 := hqU
  have hq : dist (fun j => (q j : ℝ)) t₀ < ε := by linarith
  -- the midpoint argument: `B(q)` is klt
  have hklt' : ∀ D : DivisorOver ℂ sX, IsProper D.f → 0 < aD D (fun j => (q j : ℝ)) := by
    intro D hD
    rw [haff]
    exact ratAffineForm_pos_of_nonneg_ball _ (fun t ht => haff D t ▸ hnonneg D hD t ht)
      (haff D t₀ ▸ hpos₀ D hD) hqU
  refine ⟨BQ q, ⟨hpair q hq, fun n' D a₀ h₀ => ?_⟩, fun j =>
    ⟨aD (E j) (fun j => (q j : ℝ)), ?_, hklt' (E j) (ha j).2.1, ?_⟩⟩
  · rw [hBQR] at h₀
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique h₀ (hlog D h₀.2.1 _)]
    exact hklt' D h₀.2.1
  · rw [hBQR]
    exact hlog (E j) (ha j).2.1 _
  · have := hqI (g₁ j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rw [hg₁] at this
    linarith

end RationalApproximation

end MMP.RealExtractionNormalSource

namespace MMP.Fourfold

open MMP.Mori

/-- **Real extraction from a nonfactorial source.** Assume `P(n)`
(`MMP.Fourfold.ProjectiveFloorProgramInputs`). Let `X` be a normal projective complex variety of
dimension `n` with canonical divisor `K`, `B` an effective `ℝ`-divisor with `(X, B)` klt
(`MMP.Fourfold.IsRealKltPair`), and `E j` (`j ∈ ι`, finite) divisors over `X` with distinct
valuations, exceptional over `X`, with log discrepancies `a j ≤ 1`. Then there are a projective
birational morphism `p : V ⟶ X` from a `ℚ`-factorial normal projective variety and prime divisors
`F j` of `V` with `ord_{F j} = v(E j)`, `j ↦ F j` injective, whose range is exactly the set of
`p`-exceptional prime divisors, such that `B_V = p⁻¹_* B + ∑ j (1 - a j) F j` is effective and klt
and, for a canonical divisor `K_V` of `V` with `p_* K_V = K`, `K_V + B_V = p^*(K + B)`. -/
@[mmp "lem_fourfold_real_extraction_normal_source"]
public theorem exists_isQFactorial_extraction_of_isRealKltPair
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (n : ℕ) (hP : ProjectiveFloorProgramInputs n)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = n)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX n)
    (B : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hklt : IsRealKltPair sX B)
    {ι : Type*} [Fintype ι] (E : ι → DivisorOver ℂ sX)
    (hE : Function.Injective fun j => (E j).valuation) (hEx : ∀ j, (E j).IsExceptional)
    (a : ι → ℝ) (ha : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n B (E j) (a j))
    (ha1 : ∀ j, a j ≤ 1) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (hV : IsQFactorial (p ≫ sX)) (hp : IsBirationalMorphism p)
      (F : ι → MMP.Mori.PrimeDivisor V),
      MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) ∧ IsProjectiveMorphism p ∧
      (∀ j, (⟨V, p, hV.1, hp, F j⟩ : DivisorOver ℂ sX).valuation = (E j).valuation) ∧
      Function.Injective F ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) p.toRationalMap P ↔ P ∈ Set.range F) ∧
      (∀ P, 0 ≤ (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j)).coeff P) ∧
      IsRealKltPair (p ≫ sX) (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j)) ∧
      ∃ KV : Divisor V, KV.IsCanonicalDivisor (p ≫ sX) n ∧
        RationalMap.transformDivisor p.toRationalMap KV = K ∧
        MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor K B)
          (MMP.Flips.logCanonicalDivisor KV
            (inverseTransformDivisor p B + ∑ j, Finsupp.single (F j) (1 - a j))) := by
  classical
  have hXnv : IsNormalVariety ℂ sX := hklt.1
  haveI : MMP.Mori.IsVariety ℂ sX := hXnv.1
  haveI : CompactSpace X := hXnv.1.toQuasiCompact.compactSpace_of_compactSpace
  -- `K + B` is `ℝ`-Cartier for the given canonical divisor `K`
  have hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + B) := by
    obtain ⟨n', K', hK', m, r, C, hC, hcoef⟩ := hklt.2.2.1
    obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXnv hK hK'
    refine ⟨m + 1, Fin.snoc r 1, Fin.snoc C (principalDivisor φ), fun j => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using Divisor.isCartier_principalDivisor φ
      · simpa using hC j
    · simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
      refine Finsupp.ext fun Γ => ?_
      have h1 := hcoef Γ
      have h2 := congrArg (fun D : Divisor X => ((D.coeff Γ : ℤ) : ℝ)) hφ
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, Int.cast_sub] at h1 h2
      rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        MMP.Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, DivisorWithCoeffs.coeff_add,
        Divisor.coeff_toRDivisor, one_mul]
      rw [← h1, ← h2]
      change (K.coeff Γ : ℝ) + B.coeff Γ = ((K'.coeff Γ : ℤ) : ℝ) + B.coeff Γ +
        ((K.coeff Γ : ℝ) - (K'.coeff Γ : ℝ))
      ring
  -- a nearby rational klt boundary
  obtain ⟨Δ, hΔ, ha'⟩ := MMP.RealExtractionNormalSource.exists_isKltPair_isLogDiscrepancy_le_one
    hXnv hK hB hklt hKB E a ha ha1
  choose a' ha'log ha'pos ha'le using ha'
  -- the rational extraction
  set 𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))) :=
    Finset.univ.image fun j => (E j).valuation
  have h𝓔 : ∀ s ∈ 𝓔, MMP.Intersection.IsExceptionalValuation ℂ sX s ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sX Δ s a ∧ 0 < a ∧ a ≤ 1 := by
    intro s hs
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
    refine ⟨⟨E j, (ha j).2.1, rfl, ?_⟩, a' j, ⟨n, E j, (ha j).2.1, rfl, ha'log j⟩, ha'pos j,
      ha'le j⟩
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hXnv (E j)).1 (hEx j)
  obtain ⟨V, _, _, _, p, hp, hV, E', ΔV, hproj, hval, hinj, hexc, -⟩ :=
    hP.exists_crepant_extraction sX hX hdim hΔ 𝓔 h𝓔
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hproj
  let F : ι → MMP.Mori.PrimeDivisor V := fun j =>
    E' ⟨(E j).valuation, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  have hF : Function.Injective F := fun j j' h => hE (congrArg Subtype.val (hinj h))
  have hvalF : ∀ j, (⟨V, p, hV.1, hp, F j⟩ : DivisorOver ℂ sX).valuation = (E j).valuation :=
    fun j => hval _
  have hexcF : ∀ P : MMP.Mori.PrimeDivisor V,
      RationalMap.IsExceptional (X := V) p.toRationalMap P ↔ P ∈ Set.range F := by
    intro P
    rw [hexc P]
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 s.2
      exact ⟨j, congrArg E' (Subtype.ext hj)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, rfl⟩
  have hVproj : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) := by
    rw [MMP.Mori.isProjectiveVariety_iff] at hX ⊢
    exact ⟨hV.1.1, hproj.comp hX.2⟩
  exact ⟨V, ‹_›, ‹_›, ‹_›, p, hV, hp, F, hVproj, hproj, hvalF, hF, hexcF,
    MMP.RealExtractionNormalSource.nonneg_and_isRealKltPair_and_exists_isRCartierPullback hXnv hK
      hB hklt hKB E a ha ha1 hV.1 hp F hF hvalF hexcF⟩

end MMP.Fourfold
