module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Threefold.Contraction.RealKltElementaryStep
import MMP.AlgebraicGeometry.MMP.Flip.PicardNumber
import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalThreefoldFlips
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.Arithmetic
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialDiscrepancyIncrease
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Terminal real programs over a fixed birational base

Let `h : Y ⟶ X` be a projective birational morphism of projective normal complex threefolds,
with `Y` `ℚ`-factorial, and let `(Y, C)` be a real terminal pair with canonical divisor `K` such
that every prime component of `C` maps onto a prime divisor of `X`. Then every `(K + C)`-program
over `X` from `(Y, C)` — a sequence of divisorial contractions of `(K_i + C_i)`-negative extremal
rays of `NE̅(Y_i/X)` and of real flips of the small contractions of such rays, through projective
`ℚ`-factorial models over `X`, the boundaries being the successive birational transforms — has
finitely many steps and passes only through real terminal pairs; and there is such a program
which ends at a projective `ℚ`-factorial model `Y_n ⟶ X` with `K_n + C_n` nef over `X`.

## Main results

* `MMP.Fourfold.IsRealTerminalPair.terminates_of_isBirationalMorphism`.

## Implementation notes

The program is spelled out as data indexed as in `MMP.Fourfold.RelativeDltProgram`: models
`Y₀ = Y`, `Y_{i+1} = Yi i` over `X`, a number `n ∈ ℕ ∪ {∞}` of steps, and for `i < n` a
`(K_i + C_i)`-negative extremal ray `R_i` of `NE̅(Y_i/X)` (negativity through
`MMP.Flips.IsRIntersectionNumber`) with its contraction `f_i : Y_i ⟶ Z_i`, `g_i : Z_i ⟶ X`
over `X` (`MMP.Mori.IsRelativeContractionOfFace`, `MMP.Flips.IsNegativeExtremalContraction`),
followed by `f_i⁺ : Y_{i+1} ⟶ Z_i` over `X` which is an isomorphism when `f_i` is divisorial and
a real flip (`MMP.Fourfold.IsRealFlipStep`) otherwise; in both cases
`C_{i+1} = (f_i⁺)⁻¹_* (f_i)_* C_i`. A prime component `P` of `C` maps onto a prime divisor of `X`
when its transform `MMP.Mori.RationalMap.transformPrimeDivisor` under `h` is a prime divisor.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori MMP.Flips

namespace Proof_lem_fourfold_real_terminal_program_over_birational_base

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- `(i + 1 : ℕ∞) ≤ n` gives `(i : ℕ∞) < n`. -/
private theorem natCast_lt_of_succ_le {n : ℕ∞} {i : ℕ} (h : ((i + 1 : ℕ) : ℕ∞) ≤ n) :
    (i : ℕ∞) < n := by
  push_cast at h
  exact (ENat.add_one_le_iff (ENat.coe_ne_top i)).mp h

/-! ### Generic facts -/

/-- A morphism inducing isomorphisms on all rings of sections is left cancellable against
morphisms to an affine scheme. -/
private theorem eq_of_comp_eq_of_isIso_app {X Z : Scheme.{0}} {R : CommRingCat} (f : X ⟶ Z)
    (hf : ∀ U : Z.Opens, IsIso (f.app U)) {a b : Z ⟶ Spec R} (h : f ≫ a = f ≫ b) : a = b := by
  haveI : IsIso f.appTop := hf ⊤
  refine ext_of_isAffine ?_
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  exact (cancel_mono f.appTop).mp h'

/-- An `ℝ`-divisor which is `ℝ`-Cartier in the sense of `MMP.Fourfold.RDivisor.IsRCartier` is a
combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRCartier {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (h : RDivisor.IsRCartier D) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD⟩ := h
  refine ⟨m, r, L, hL, Finsupp.ext fun Γ => ?_⟩
  have h1 := MMP.Flips.coeff_sum_smul_toRDivisor r L Γ
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs] at h1
  exact (hD Γ).trans h1.symm

/-- A proper birational morphism `f⁺` onto a normal variety which maps points of coheight at
most one to points of coheight at most one is small. -/
private theorem isSmallMorphism_of_coheight_le_one {X1 Z : Scheme.{0}} [IsIntegral X1]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {s1 : X1 ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (h1 : IsNormalVariety ℂ s1) (hZ : IsNormalVariety ℂ sZ)
    (fp : X1 ⟶ Z) (hc : fp ≫ sZ = s1) [IsProper fp] (hb : IsBirationalMorphism fp)
    (hco : ∀ x : X1, Order.coheight x ≤ 1 → Order.coheight (fp x) ≤ 1) :
    IsSmallMorphism s1 sZ fp where
  isNormalVariety_source := h1
  isNormalVariety_target := hZ
  comp_eq := hc
  isProper := inferInstance
  isBirationalMorphism := hb
  two_le_codimension := MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => by
    by_contra hlt
    have hx1 : Order.coheight x ≤ 1 :=
      Order.le_of_lt_add_one (by rw [one_add_one_eq_two]; exact not_le.mp hlt)
    exact (MMP.Mori.mem_exceptionalSet.mp hx)
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hb (hco x hx1))

/-- The log discrepancy of a prime divisor `Q` of `X`, as the divisor `(X, 𝟙, Q)` over itself,
is `1 - coeff_Q B`, once `K_X + B` is an `ℝ`-Cartier combination. -/
private theorem isLogDiscrepancy_ofPrimeDivisor_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
      (1 - B.coeff Q) := by
  have h := MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω hK hKB Q
  have hv : (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation = Q.divisorialValuation :=
    Valuation.ext fun φ => by
      change Q.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
      rw [MMP.Mori.functionFieldMap_id_apply]
  have := MMP.Fourfold.isLogDiscrepancy_of_isDiscrepancy h (DivisorOver.ofPrimeDivisor ℂ hX Q)
    (inferInstanceAs (IsProper (𝟙 X))) hv
  rwa [← sub_eq_add_neg] at this

/-- A real terminal pair is a real klt pair. -/
private theorem isRealKltPair_of_isRealTerminalPair {Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {C : RDivisor Y} (hC : IsRealTerminalPair sY C) : IsRealKltPair sY C := by
  obtain ⟨⟨hYv, hcoef, hKC, -⟩, hterm⟩ := hC
  refine ⟨hYv, fun P => ?_, hKC, fun n E a ha => ?_⟩
  · by_cases hP : C.coeff P = 0
    · rw [hP]; norm_num
    · exact (hcoef P hP).2
  · by_cases hE : E.IsExceptional
    · exact zero_lt_one.trans (hterm n E a hE ha)
    · obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hYv hE
      obtain ⟨m, K, hK, hKR⟩ := hKC
      haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
      obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hYv hK
      have hmr : Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K = Divisor.toRDivisor K := by
        ext Γ
        simp [Divisor.toRDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
      rw [hmr] at hKR
      have hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + C) := by
        rw [hdiv]; exact isCartierCombination_of_isRCartier hKR
      have h2 := isLogDiscrepancy_ofPrimeDivisor_ph hYv hω0 (hdiv ▸ hK)
        hKB Q
      have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h2 hQ
      rw [heq]
      have hQ1 : C.coeff Q < 1 := by
        by_cases hP : C.coeff Q = 0
        · rw [hP]; norm_num
        · exact (hcoef Q hP).2
      linarith

/-! ### One step of the program -/

section Step

variable {X X0 X1 Z : Scheme.{0}} [IsIntegral X0] [CompactSpace X0] [IsLocallyNoetherian X0]
  [IsNormal X0] [IsIntegral X1] [CompactSpace X1] [IsLocallyNoetherian X1] [IsNormal X1]
  {sX : X ⟶ Spec (.of ℂ)} {s0 : X0 ⟶ Spec (.of ℂ)} {s1 : X1 ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} {π0 : X0 ⟶ X} {π1 : X1 ⟶ X} {K0 : Divisor X0} {C0 : RDivisor X0}
  {K1 : Divisor X1} {C1 : RDivisor X1} {R : Set (RelativeNumericalCurveClasses s0 π0)}
  {f : X0 ⟶ Z} {g : Z ⟶ X} {fp : X1 ⟶ Z}

/-- The data of one step: `f` is the contraction over `X` of a negative extremal ray, and `f⁺`
is either an isomorphism (`f` divisorial) or a real flip of `f`. -/
private theorem step_basic (hπ0 : π0 ≫ sX = s0) (hπ1 : π1 ≫ sX = s1)
    (hrc : IsRelativeContractionOfFace π0 R f g)
    (hne : IsNegativeExtremalContraction ℂ s0 sZ (logCanonicalDivisor K0 C0) f)
    (hfpg : fp ≫ g = π1)
    (hcase : ((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X0,
        (MMP.Mori.exceptionalSet f : Set X0) = E.support) ∧ IsIso fp ∧
        (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧ C1 = flipTransform f fp C0) ∨
      IsRealFlipStep s0 sZ s1 K0 C0 K1 C1 f fp) :
    IsBirationalMorphism f ∧ IsBirationalMorphism fp ∧ IsProper f ∧ IsProper fp ∧
      f ≫ sZ = s0 ∧ g ≫ sX = sZ ∧ fp ≫ sZ = s1 ∧ IsNormalVariety ℂ sZ ∧
      C1 = flipTransform f fp C0 ∧ (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧
      ∀ x : X1, Order.coheight x ≤ 1 → Order.coheight (fp x) ≤ 1 := by
  have hct := hne.isContraction
  haveI : IsNormal Z := hne.isNormalVariety_target.2
  have hfs : f ≫ sZ = s0 := hct.comp_eq
  have hgs : g ≫ sX = sZ := by
    refine eq_of_comp_eq_of_isIso_app f hct.isIso_app ?_
    rw [← Category.assoc, hrc.comp_eq, hπ0, hfs]
  have hfps : fp ≫ sZ = s1 := by rw [← hgs, ← Category.assoc, hfpg, hπ1]
  rcases hcase with ⟨⟨hfb, -⟩, hiso, hK1, hC1⟩ | hfl
  · refine ⟨hfb, isBirationalMorphism_of_isIso fp, hct.isProper, inferInstance, hfs, hgs, hfps,
      hne.isNormalVariety_target, hC1, hK1, fun x hx => ?_⟩
    have hx' : x ∉ MMP.Flips.exceptionalSet fp := fun hmem =>
      hmem ⟨⊤, trivial, inferInstance⟩
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hx']
    exact hx
  · have hsm := hfl.isSmall_flip
    have h2 := (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet
      hsm.toIsBirationalContraction).mp hsm
    refine ⟨hfl.isBirationalMorphism, hfl.isBirationalMorphism_flip, hct.isProper,
      hsm.isProper, hfs, hgs, hfps, hne.isNormalVariety_target, hfl.eq_flipTransform,
      hfl.isCanonicalDivisor_flip, fun x hx => ?_⟩
    have hx' : x ∉ MMP.Flips.exceptionalSet fp := fun hmem => by
      have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) x hmem
      have h21 := this.trans hx
      exact absurd h21 (by decide)
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hx']
    exact hx

/-- Along a step, every prime divisor `P'` of `X₁` comes from a prime divisor `P` of `X₀`:
`f(η_P) = f⁺(η_{P'})` is a point of coheight one of `Z`, the boundary coefficients agree and
`P'`, `P` have the same image in `X`. -/
private theorem step_corr (hπ0 : π0 ≫ sX = s0) (hπ1 : π1 ≫ sX = s1)
    (hrc : IsRelativeContractionOfFace π0 R f g)
    (hne : IsNegativeExtremalContraction ℂ s0 sZ (logCanonicalDivisor K0 C0) f)
    (hfpg : fp ≫ g = π1)
    (hcase : ((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X0,
        (MMP.Mori.exceptionalSet f : Set X0) = E.support) ∧ IsIso fp ∧
        (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧ C1 = flipTransform f fp C0) ∨
      IsRealFlipStep s0 sZ s1 K0 C0 K1 C1 f fp)
    (h1 : IsNormalVariety ℂ s1) (P' : MMP.Mori.PrimeDivisor X1) :
    ∃ P : MMP.Mori.PrimeDivisor X0, f P.genericPoint = fp P'.genericPoint ∧
      Order.coheight (fp P'.genericPoint) = 1 ∧ C1.coeff P' = C0.coeff P ∧
      π1 P'.genericPoint = π0 P.genericPoint := by
  obtain ⟨hfb, hfpb, hfP, hfpP, -, -, hfps, hZ, hC1, -, hco⟩ :=
    step_basic hπ0 hπ1 hrc hne hfpg hcase
  haveI := hfP
  haveI := hfpP
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hsm := isSmallMorphism_of_coheight_le_one h1 hZ fp hfps hfpb hco
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfb hsm P'
  have hPm : f Pm.genericPoint = Q.genericPoint := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hP'Q : fp P'.genericPoint = Q.genericPoint := map_genericPoint_eq_of_image_eq P' Q hPQ
  obtain ⟨P, hxP, hcoef⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfb hsm P' Pm.genericPoint (hPm.trans hP'Q.symm)
  have hfP' : f P.genericPoint = fp P'.genericPoint := by rw [← hxP, hPm, hP'Q]
  refine ⟨P, hfP', by rw [hP'Q, Q.coheight_genericPoint], ?_, ?_⟩
  · rw [hC1]; exact hcoef C0
  · rw [← hfpg, ← hrc.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hfP']

/-- Along a step, distinct prime divisors of `X₁` have distinct images in `Z`. -/
private theorem step_inj (hπ0 : π0 ≫ sX = s0) (hπ1 : π1 ≫ sX = s1)
    (hrc : IsRelativeContractionOfFace π0 R f g)
    (hne : IsNegativeExtremalContraction ℂ s0 sZ (logCanonicalDivisor K0 C0) f)
    (hfpg : fp ≫ g = π1)
    (hcase : ((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X0,
        (MMP.Mori.exceptionalSet f : Set X0) = E.support) ∧ IsIso fp ∧
        (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧ C1 = flipTransform f fp C0) ∨
      IsRealFlipStep s0 sZ s1 K0 C0 K1 C1 f fp)
    (h1 : IsNormalVariety ℂ s1) {P₁ P₂ : MMP.Mori.PrimeDivisor X1}
    (h : fp P₁.genericPoint = fp P₂.genericPoint) : P₁ = P₂ := by
  obtain ⟨-, hfpb, -, hfpP, -, -, -, hZ, -, -, -⟩ := step_basic hπ0 hπ1 hrc hne hfpg hcase
  obtain ⟨-, -, hc, -, -⟩ := step_corr hπ0 hπ1 hrc hne hfpg hcase h1 P₂
  haveI := hfpP
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hfpb.isDominant
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hQ : fp P₂.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm
  haveI := Q.isDiscreteValuationRing_localRing
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_of_valuationRing hfpb.functionFieldMap_bijective (h.trans hQ) hQ)

/-- The exceptional prime divisor of a divisorial contraction `f` onto a normal variety maps to a
point of coheight at least two. -/
private theorem two_le_coheight_map_genericPoint
    (hne : IsNegativeExtremalContraction ℂ s0 sZ (logCanonicalDivisor K0 C0) f)
    (hfb : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X0}
    (hE : (MMP.Mori.exceptionalSet f : Set X0) = E.support) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  have hZ := hne.isNormalVariety_target
  haveI : IsProper f := hne.isContraction.isProper
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  by_contra hlt
  have hx1 : Order.coheight (f E.genericPoint) ≤ 1 :=
    Order.le_of_lt_add_one (by rw [one_add_one_eq_two]; exact not_le.mp hlt)
  have hb := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb hx1
  have hmem : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X0) := by
    rw [hE]; exact MMP.Flips.primeDivisor_genericPoint_mem_support E
  exact (MMP.Mori.mem_exceptionalSet.mp hmem) hb

end Step

/-! ### Real terminality along the steps -/

/-- **A real flip of a real terminal pair is real terminal**: the transformed pair is real
canonical (`MMP.Fourfold.IsRealFlipStep.exists_isRealCanonicalPair_qDivisor`) and log
discrepancies do not decrease across the flip
(`MMP.Fourfold.IsRealFlipStep.exists_isLogDiscrepancy_le`). -/
private theorem isRealTerminalPair_of_isRealFlipStep {X0 X1 Z : Scheme.{0}} [IsIntegral X0]
    [CompactSpace X0] [IsLocallyNoetherian X0] [IsNormal X0] [IsIntegral X1] [CompactSpace X1]
    [IsLocallyNoetherian X1] [IsNormal X1] {s0 : X0 ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {s1 : X1 ⟶ Spec (.of ℂ)} {K0 : Divisor X0} {C0 : RDivisor X0} {K1 : Divisor X1}
    {C1 : RDivisor X1} {f : X0 ⟶ Z} {fp : X1 ⟶ Z}
    (hs : IsRealFlipStep s0 sZ s1 K0 C0 K1 C1 f fp) (hK : ∃ m : ℕ, K0.IsCanonicalDivisor s0 m)
    (hQ0 : IsQFactorial s0) (hQ1 : IsQFactorial s1)
    (hX0 : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ s0)
    (hX1 : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ s1)
    (hd0 : topologicalKrullDim X0 = 3) (hd1 : topologicalKrullDim X1 = 3)
    (hT : IsRealTerminalPair s0 C0) : IsRealTerminalPair s1 C1 := by
  have hcan := (hs.exists_isRealCanonicalPair_qDivisor hK hQ0 hQ1 hX0 hX1 hd0 hd1 hT.1).1
  have hZ := hs.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  refine ⟨hcan, fun n E' a' hE' ha' => ?_⟩
  obtain ⟨E, hEp, -, hpt, hle⟩ := hs.exists_isLogDiscrepancy_le hK E' ha'.2.1
  have hEx : E.IsExceptional := hs.isExceptional_of_map_eq E E' hpt hE'
  obtain ⟨m, hKm⟩ := hK
  have hXv := hs.isNegativeExtremalContraction.isNormalVariety_source
  haveI : LocallyOfFiniteType s0 := hXv.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hdiv⟩ := exists_divisorOfForm_eq hXv hKm
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hXv hω0 (hdiv ▸ hKm)
    (by rw [hdiv]; exact hs.isNegativeExtremalContraction.isCartierCombination) E hEp
  exact (hT.2 m E a hEx ha).trans_le (hle m n a a' ha ha').1

/-! ### Divisorial steps -/

private theorem isCartierCombination_of_isQFactorial_ph {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hq : IsQFactorial sX) (G : RDivisor X) : IsCartierCombination G :=
  isCartierCombination_of_isRCartier (hq.isRCartier G)

/-- An `ℝ`-Cartier combination is `ℝ`-Cartier in the coefficientwise sense. -/
private theorem isRCartier_of_isCartierCombination {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : RDivisor X} (hD : IsCartierCombination D) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  refine ⟨m, r, L, hL, fun Γ => ?_⟩
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor]

/-- On a `ℚ`-factorial variety, `K + B` is `ℝ`-Cartier for every canonical divisor `K`. -/
private theorem isRCartier_logCanonical_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hq : IsQFactorial sX) (K : Divisor X) (B : RDivisor X) :
    RDivisor.IsRCartier (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B) :=
  isRCartier_of_isCartierCombination (isCartierCombination_of_isQFactorial_ph hq _)

private theorem isDiscrepancy_of_isLogDiscrepancy_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) :
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B D.valuation (a - 1) :=
  MMP.Fourfold.isDiscrepancy_of_isLogDiscrepancy h.1 hK hKB (E := ⟨D, h.2.1⟩) h

private theorem hasNonemptyCenter_valuation_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (E : MMP.Flips.ProperDivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

private theorem isExceptional_iff_two_le_coheight_ph {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) :=
  MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D

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

private theorem exists_pullbackRationalPluriForms_eq_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (g : Y ⟶ X)
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

private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor_ph {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n :=
  hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

/-- An `f`-ample `ℝ`-divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian Z] [IsNormal Z]
    (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hf : f ≫ sZ = sX) {A : RDivisor X} (hA : IsRelativelyAmple f A) :
    IsRelativelyNef ℂ sX f A := by
  obtain ⟨m, r, L, -, hr, hL, rfl⟩ := hA
  have hc := (MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf).2.2.1
  refine ⟨m, r, L, fun j => (hL j).1, rfl, fun C hC x hx => ?_⟩
  obtain ⟨hL', d, -, hd, rfl⟩ := hx
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le
    (by exact_mod_cast (hc (L j) (hL j) (hL' j) C hC (d j) (hd j)).le)

/-- An `f`-anti-ample `ℝ`-divisor is negative on every curve contracted by `f`. -/
private theorem neg_of_isRelativelyAntiAmple {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian Z] [IsNormal Z]
    (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f]
    (hf : f ≫ sZ = sX) {L : RDivisor X} (hA : IsRelativelyAntiAmple f L) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L' : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX L r L' C x → x < 0 := by
  obtain ⟨m, r, Ls, hm, hr, hL, hLs⟩ := hA
  have hc := (MMP.Flips.relativelyAmple_basics sX sZ hXv hZv f hf).2.2.1
  have hL' : L = ∑ j, (-r j) • Divisor.toRDivisor (Ls j) := by
    rw [← neg_neg L, hLs]
    simp only [neg_smul, Finset.sum_neg_distrib]
  intro m' r' L' x hx
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C (fun j => -r j) Ls
    (fun j => (hL j).1) hL' hx]
  have hpos : 0 < ∑ j, r j * ((Ls j).degreeOn ℂ sX C.ι C.dim_le (hL j).1 : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (by
      exact_mod_cast hc _ (hL j) _ C hC _
        (MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX C _ _)))
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

private theorem pullbackRationalPluriForms_zero_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} (g : Y ⟶ X) [IsDominant g] {n : ℕ} :
    pullbackRationalPluriForms sX g (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have h := pullbackForms_smul (K' := Y.functionField) (k := ℂ) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- A partial isomorphism representing `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
    (S := CategoryTheory.Limits.terminal Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A representative `g'` of the inverse of a birational morphism `f` is a section of `f` on its
domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{0}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := CategoryTheory.Limits.terminal Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some {X Y : Scheme.{0}}
    [IsReduced X] [IsReduced Y] [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)]
    [IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme)] {f : Y ⟶ X}
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor g P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := H
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- **An inverse of a proper birational morphism is a morphism in codimension one** (FA 2.4.1):
an inverse `g` of a proper birational morphism `f : Y ⟶ X` onto a normal variety is a map over
`X`, hence defined in codimension one. -/
private theorem isMorphismInCodimOne_of_isInverse {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X) (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f]
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g) :
    MMP.Flips.RationalMap.IsMorphismInCodimOne g := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← CategoryTheory.Limits.terminal.comp_from sX]; infer_instance⟩
  obtain ⟨e, he, hinv⟩ := H
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) f
  have hover : MMP.Flips.RationalMap.IsOver (𝟙 X) f g := by
    rw [MMP.Flips.RationalMap.IsOver, ← hinv]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ f = X.homOfLE _ ≫ X.topIso.hom ≫ 𝟙 X
    rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
    simp
  exact MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX (𝟙 X) f _ hover

/-- Let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal, and `g` an
inverse of `f`. If `f` sends the generic point of a prime divisor `E` of `Y` to that of a prime
divisor `P` of `X`, then the strict transform of `P` under `g` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {g : X.RationalMap Y} (H : MMP.Mori.RationalMap.IsInverse f.toRationalMap g)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor g P = some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hX
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  have hcod := isMorphismInCodimOne_of_isInverse hX f hY H
  obtain ⟨e, he, he'⟩ := H
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp hcod
      (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    rw [codimension_eq_coheight,
      show TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

private theorem birationalInverseTransform_apply_of_genericPoint_eq_ph {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety ℂ (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal_of_isNormalVariety hX
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf hf.isInverse_inverse h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf.isInverse_inverse
        hP').symm.trans h)) D

private theorem birationalInverseTransform_apply_eq_zero_ph {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety ℂ sX) {f : Y ⟶ X} (hY : MMP.Mori.IsVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, f E.genericPoint ≠ P.genericPoint) :
    birationalInverseTransform f hf D E = 0 := by
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have : IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (X ↘ CategoryTheory.Limits.terminal Scheme) =
      sX ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ CategoryTheory.Limits.terminal Scheme) := by
    rw [show (Y ↘ CategoryTheory.Limits.terminal Scheme) =
      (f ≫ sX) ≫ (Spec (.of ℂ) ↘ CategoryTheory.Limits.terminal Scheme) from
        CategoryTheory.Limits.terminal.hom_ext _ _]
    infer_instance
  exact MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf.isInverse_inverse hP)) D

private theorem map_genericPoint_eq_of_valuation_comap_eq_ph {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY]
    (f : X ⟶ Y) [IsDominant f] (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sY)
    (hv : D.valuation.comap (functionFieldMap f) = D'.valuation) :
    f (D.f D.E.genericPoint) = D'.f D'.E.genericPoint := by
  refine MMP.Positivity.DivisorOver.eq_of_dominates sY D'.valuation (fun a => ?_) (fun a ha => ?_)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl) <;>
  rw [← hv, Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _
      ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- A closed point of the exceptional set of a birational contraction lies on a contracted
curve. -/
private theorem exists_properCurve_isContractedBy_of_mem {X Zs : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {L : RDivisor X} {f : X ⟶ Zs}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hneg : IsNegativeExtremalContraction ℂ sX sZs L f) (hb : IsBirationalMorphism f)
    {y : X} (hy : y ∈ (MMP.Mori.exceptionalSet f : Set X)) (hyc : IsClosed ({y} : Set X)) :
    ∃ Γ : ProperCurve sX, Γ.IsContractedBy f ∧ y ∈ closure ({Γ.point} : Set X) := by
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have : IsProper f := hneg.isContraction.isProper
  have : IsProper sX := isProper_of_isProjectiveMorphism sX hX.isProjective
  obtain ⟨Cs, hCc, hCi, hCd, hyC, w, hw⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hXv.1 hZv.1 f
      hneg.isContraction.comp_eq hb hneg.isContraction.isIso_app hyc hy
  have hgen := hCi.isGenericPoint_genericPoint_closure
  rw [hCc.closure_eq] at hgen
  have hη1 : topologicalKrullDim (curveSubschemeAt hCi.genericPoint) = 1 := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hgen.def, hCd]
  refine ⟨⟨hCi.genericPoint, isProperCurve_of_isProper sX hη1⟩, fun x hx => ?_, ?_⟩
  · change x ∈ closure {hCi.genericPoint} at hx
    rw [hgen.def] at hx
    have h1 : f x ∈ ({w} : Set Zs) := hw ▸ ⟨x, hx, rfl⟩
    have h2 : f hCi.genericPoint ∈ ({w} : Set Zs) := hw ▸ ⟨_, hgen.mem, rfl⟩
    exact h1.trans h2.symm
  · change y ∈ closure {hCi.genericPoint}
    rw [hgen.def]; exact hyC

/-- A morphism that is an isomorphism contracts no curve. -/
private theorem not_isContractedBy_of_isIso {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (f : X ⟶ Y) [IsIso f] (C : ProperCurve sX) : ¬ C.IsContractedBy f := by
  intro hC
  have hinj : Function.Injective f := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (asIso f))).injective
  have hsing : ∀ a b : C.scheme, a = b := fun a b => C.ι.isEmbedding.injective <| by
    have ha : C.ι a ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨a, rfl⟩
    have hb : C.ι b ∈ closure ({C.point} : Set X) := C.range_ι ▸ ⟨b, rfl⟩
    exact hinj ((hC _ ha).trans (hC _ hb).symm)
  haveI : Subsingleton C.scheme := ⟨hsing⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An `ℝ`-Cartier divisor is nef relative to an isomorphism. -/
private theorem isRelativelyNef_of_isIso {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (f : X ⟶ Y) [IsIso f] {D : RDivisor X}
    (hD : IsCartierCombination D) : IsRelativelyNef ℂ sX f D := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  exact ⟨m, r, L, hL, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDL,
    fun C hC => absurd hC (not_isContractedBy_of_isIso f C)⟩

/-- **A divisorial contraction of a prime with zero boundary coefficient keeps the pair real
terminal.** Let `f : X ⟶ Z` be a `(K + B)`-negative extremal contraction with exceptional set a
prime divisor `E`, `B.coeff E = 0`, and `f⁺ : X⁺ ⟶ Z` an isomorphism. Every exceptional divisor
over `X⁺` has log discrepancy at least that over `X` (FA 2.28, with the forms of `Z` pulled
back); if it is exceptional over `X` the latter exceeds one, and otherwise it is `E` itself,
whose log discrepancy `1` strictly increases since `K + B` is negative on the curves of `E`. -/
private theorem isRealTerminalPair_of_divisorial {X X' Zs : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sZs : Zs ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} {K' : Divisor X'}
    {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hneg : IsNegativeExtremalContraction ℂ sX sZs (logCanonicalDivisor K B) f)
    (hb : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) [IsIso fp] (hfps : fp ≫ sZs = sX')
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sX' m)
    (hBE : B.coeff E = 0) (hT : IsRealTerminalPair sX B) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hX'Q : IsQFactorial sX') :
    IsRealTerminalPair sX' (flipTransform f fp B) := by
  classical
  have hXv := hneg.isNormalVariety_source
  have hZv := hneg.isNormalVariety_target
  have hc := hneg.isContraction
  have hfs : f ≫ sZs = sX := hc.comp_eq
  subst hfs hfps
  haveI : IsIntegral Zs := hZv.1.toIsIntegral
  haveI : IsNormal Zs := hZv.2
  haveI : LocallyOfFiniteType sZs := hZv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZs := hZv.1.toQuasiCompact
  haveI : IsSeparated sZs := hZv.1.toIsSeparated
  haveI : IsLocallyNoetherian Zs := LocallyOfFiniteType.isLocallyNoetherian sZs
  haveI : IsProper f := hc.isProper
  have hX'v : IsNormalVariety ℂ (fp ≫ sZs) := hX'Q.1
  haveI : MMP.Mori.IsVariety ℂ sZs := hZv.1
  haveI : MMP.Mori.IsVariety ℂ (f ≫ sZs) := hXv.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZs) := hX'v.1
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  haveI : LocallyOfFiniteType (f ≫ sZs) := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZs) := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sZs) := hXv.1.toQuasiCompact
  haveI : QuasiCompact (fp ≫ sZs) := hX'v.1.toQuasiCompact
  have hbp : IsBirationalMorphism fp := isBirationalMorphism_of_isIso fp
  haveI : IsDominant f := hb.isDominant
  haveI : IsDominant fp := hbp.isDominant
  set B' := flipTransform f fp B with hB'
  -- the forms
  obtain ⟨m, hKm⟩ := hK
  have hdimX : topologicalKrullDim X = m := hKm.topologicalKrullDim_eq
  have hdimZ : topologicalKrullDim Zs = m :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs (f ≫ sZs) hb).trans
      hdimX
  have hdimX' : topologicalKrullDim X' = m :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs (fp ≫ sZs)
      hbp).symm.trans hdimZ
  obtain ⟨ωX, hωX0, hωX⟩ := exists_divisorOfForm_eq hXv hKm
  obtain ⟨ω, hω⟩ := exists_pullbackRationalPluriForms_eq_ph f hb.functionFieldMap_bijective hdimZ ωX
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hωX0 (hω ▸ pullbackRationalPluriForms_zero_ph f)
  set ω' := pullbackRationalPluriForms sZs fp ω with hω'
  have hω'0 : ω' ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' fp
    hbp.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimZ) hω0
  obtain ⟨m'', hK'm''⟩ := hK'
  have hmm' : m'' = m := by
    have := hK'm''.topologicalKrullDim_eq.symm.trans hdimX'
    exact_mod_cast this
  have hK'm : K'.IsCanonicalDivisor (fp ≫ sZs) m := hmm' ▸ hK'm''
  have hK'c : (divisorOfForm ω').IsCanonicalDivisor (fp ≫ sZs) m :=
    isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor_ph hX'v hK'm hω'0
  have hKX : divisorOfForm (pullbackRationalPluriForms sZs f ω) = K := by rw [hω, hωX]
  have hKmω : (divisorOfForm ωX).IsCanonicalDivisor (f ≫ sZs) m := hωX ▸ hKm
  have hKBc : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + B) := by
    rw [hωX]; exact hneg.isCartierCombination
  have hKB'c : IsCartierCombination (logCanonicalDivisor (divisorOfForm ω') B') :=
    isCartierCombination_of_isQFactorial_ph hX'Q _
  -- the boundaries as transforms
  set D : RDivisor Zs := RationalMap.transformDivisor (X := X) f.toRationalMap B with hD
  have hBX : birationalInverseTransform f hb D + (B - birationalInverseTransform f hb D) = B := by
    abel
  have hBY : birationalInverseTransform fp hbp D + (B' - birationalInverseTransform fp hbp D) =
      B' := by abel
  have hZsep : IsSeparated (Zs ↘ Limits.terminal Scheme) := by
    rw [show (Zs ↘ Limits.terminal Scheme) = sZs ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbrfp : ∀ x : X', fp x ∈ biregularLocus fp := fun x =>
    le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance) trivial
  -- every prime divisor of `X⁺` lies over a prime divisor of `Z` and one of `X`
  have hover : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ (Q : MMP.Mori.PrimeDivisor Zs)
      (P : MMP.Mori.PrimeDivisor X), fp P'.genericPoint = Q.genericPoint ∧
        f P.genericPoint = Q.genericPoint ∧ D Q = B P ∧ B' P' = B P := by
    intro P'
    have hco : Order.coheight (fp P'.genericPoint) = 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hbrfp _)).trans
        P'.coheight_genericPoint
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco with hQdef
    have hQ : Q.genericPoint = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have hQ' : MMP.Mori.PrimeDivisor.genericPoint Q = fp P'.genericPoint := hQ
    obtain ⟨P₀, hP₀, -, hD₀⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZv hXv hb Q
    refine ⟨Q, P₀, hQ.symm, hP₀, hD₀ B, ?_⟩
    rw [hB']
    haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q
    exact flipTransform_apply_of_map_genericPoint hb.functionFieldMap_bijective fp.surjective
      hP₀ hQ.symm (by rw [hQ']; exact hbrfp _) B
  have hEX : ∀ P : MMP.Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZs f P →
      (B - birationalInverseTransform f hb D).coeff P = 0 := by
    intro P _
    rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    simp only [DivisorWithCoeffs.coeff_apply]
    by_cases hQ : ∃ Q : MMP.Mori.PrimeDivisor Zs, f P.genericPoint = Q.genericPoint
    · obtain ⟨Q, hQ⟩ := hQ
      obtain ⟨P₀, hP₀, -, hD₀⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZv hXv hb Q
      haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q
      have hPP₀ : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_of_valuationRing hb.functionFieldMap_bijective hP₀ hQ)
      rw [birationalInverseTransform_apply_of_genericPoint_eq_ph hZv f hXv.1 hb D hQ, hD,
        hD₀ B, hPP₀]
    · rw [birationalInverseTransform_apply_eq_zero_ph hZv.1 hXv.1 hb D
        (fun Q hQ' => hQ ⟨Q, hQ'⟩)]
      have hPE : P.genericPoint ∈ E.support := by
        rw [← hE, SetLike.mem_coe, MMP.Mori.mem_exceptionalSet]
        intro hbr
        have hco := (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans
          P.coheight_genericPoint
        exact hQ ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
      have hEP := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
      rw [← hEP]
      simpa only [DivisorWithCoeffs.coeff_apply] using hBE
  have hEY : ∀ P : MMP.Mori.PrimeDivisor X', ¬ IsExceptionalPrimeDivisor sZs fp P →
      (B' - birationalInverseTransform fp hbp D).coeff P = 0 := by
    intro P' _
    rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    simp only [DivisorWithCoeffs.coeff_apply]
    obtain ⟨Q, P, hP'Q, -, hDQ, hB'P'⟩ := hover P'
    rw [birationalInverseTransform_apply_of_genericPoint_eq_ph hZv fp hX'v.1 hbp D hP'Q, hDQ,
      hB'P']
  have hAX : IsRelativelyNef ℂ (f ≫ sZs) f (-logCanonicalDivisor K
      (birationalInverseTransform f hb D + (B - birationalInverseTransform f hb D))) := by
    rw [hBX]
    exact isRelativelyNef_of_isRelativelyAmple hXv hZv f rfl hneg.isRelativelyAntiAmple
  have hAY : IsRelativelyNef ℂ (fp ≫ sZs) fp (logCanonicalDivisor (divisorOfForm ω')
      (birationalInverseTransform fp hbp D + (B' - birationalInverseTransform fp hbp D))) := by
    rw [hBY]; exact isRelativelyNef_of_isIso fp hKB'c
  -- the terminality inequality
  have hterm : ∀ (n : ℕ) (E' : DivisorOver ℂ (fp ≫ sZs)) (a' : ℝ), E'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy (fp ≫ sZs) n B' E' a' → 1 < a' := by
    intro n E' a' hE' ha'
    have hn : m = n := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha').symm.trans
        hdimX'
      exact_mod_cast this.symm
    subst hn
    have hE'p : IsProper E'.f := ha'.2.1
    set DZ := MMP.Mori.compDivisorOver fp hX'v hbp E' with hDZ
    have hDZp : IsProper DZ.f := by
      change IsProper (E'.f ≫ fp); infer_instance
    have hvZ : DZ.valuation = E'.valuation.comap (functionFieldMap fp) :=
      MMP.Mori.valuation_compDivisorOver fp hX'v hbp E'
    have hv := hasNonemptyCenter_valuation_ph (⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs)
    obtain ⟨D₁, hD₁, -⟩ :=
      MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZv.1 f hXv.1 hb
      (⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs)
    obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hXv hωX0 hKmω hKBc D₁.toDivisorOver D₁.isProper
    have hdX := isDiscrepancy_of_isLogDiscrepancy_ph ha hωX0 hKmω hKBc
    rw [hωX] at hdX
    have hdY := isDiscrepancy_of_isLogDiscrepancy_ph ha' hω'0 hK'c hKB'c
    have hcmp := isDiscrepancy_le_of_isRelativelyNef hZv hXv hX'v hb hbp hKX rfl hEX hEY hAX hAY
      hv hD₁ hvZ.symm
    have hle : a - 1 ≤ a' - 1 := hcmp.2.2 (a - 1) (a' - 1) (by rw [hBX]; exact hdX)
      (by rw [hBY]; exact hdY)
    by_cases hD₁ex : D₁.toDivisorOver.IsExceptional
    · have := hT.2 m D₁.toDivisorOver a hD₁ex ha
      linarith
    obtain ⟨Q, hQ⟩ := exists_valuation_eq_of_not_isExceptional hXv hD₁ex
    have haQ : a = 1 - B.coeff Q := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha
      (isLogDiscrepancy_ofPrimeDivisor_ph hXv hωX0 hKmω hKBc Q) hQ
    have hc1 : D₁.f D₁.E.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
    have hc2 : f (D₁.f D₁.E.genericPoint) = DZ.f DZ.E.genericPoint :=
      map_genericPoint_eq_of_valuation_comap_eq_ph f D₁.toDivisorOver DZ hD₁
    rw [hc1] at hc2
    by_cases hQE : Q = E
    · subst hQE
      rw [hBE, sub_zero] at haQ
      have hbgen : IsGenericPoint (DZ.f DZ.E.genericPoint)
          ((⟨DZ, hDZp⟩ : MMP.Flips.ProperDivisorOver ℂ sZs).center : Set Zs) := by
        change closure {DZ.f DZ.E.genericPoint} = DZ.f '' DZ.E.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← Set.image_singleton,
          DZ.f.isClosedMap.closure_image_eq_of_continuous DZ.f.continuous]
      have hiff := isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint hZv hXv hX'v hb hbp hKX rfl
        hEX hEY hAX hAY hv hD₁ hvZ.symm (Bv := ⟨DZ, hDZp⟩) rfl hbgen
        (by rw [hBX]; exact hdX) (by rw [hBY]; exact hdY)
      have hnt : ¬ IsNumericallyTrivialOverPoint ℂ (f ≫ sZs) f
          (logCanonicalDivisor K (birationalInverseTransform f hb D +
            (B - birationalInverseTransform f hb D))) (DZ.f DZ.E.genericPoint) := by
        rw [hBX, ← hc2]
        rintro ⟨-, U, hbU, hU⟩
        haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ sZs)
        have hGmem : Q.genericPoint ∈ Q.support := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        obtain ⟨y, ⟨hyE, hyU⟩, hyc⟩ := nonempty_inter_closedPoints
          (Z := (Q.support : Set X) ∩ f ⁻¹' (U : Set Zs)) ⟨_, hGmem, hbU⟩
          (Q.idealSheaf.support.isClosed.isLocallyClosed.inter
            (U.isOpen.preimage f.continuous).isLocallyClosed)
        have hyEx : y ∈ (MMP.Mori.exceptionalSet f : Set X) := hE ▸ hyE
        obtain ⟨Γ, hΓ, hyΓ⟩ := exists_properCurve_isContractedBy_of_mem hXp hneg hb hyEx
          (mem_closedPoints_iff.mp hyc)
        have hfy : f Γ.point = f y := (hΓ y hyΓ).symm
        have hyb : f y ∈ closure ({f Q.genericPoint} : Set Zs) := by
          rw [← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous f.continuous]
          refine ⟨y, ?_, rfl⟩
          rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        have hyc' : IsClosed ({f y} : Set Zs) := by
          rw [← Set.image_singleton]; exact f.isClosedMap _ (mem_closedPoints_iff.mp hyc)
        obtain ⟨mL, rL, LL, hLL, hLeq⟩ := hneg.isCartierCombination
        have hLeq' : logCanonicalDivisor K B = ∑ j, rL j • Divisor.toRDivisor (LL j) := by
          simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hLeq
        have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (f ≫ sZs) Γ rL LL hLL
        rw [← hLeq'] at hx
        have h0 := hU Γ hΓ (hfy ▸ hyU) (hfy ▸ hyb) (hfy ▸ hyc') _ _ _ _ hx
        have hlt := neg_of_isRelativelyAntiAmple hXv hZv f rfl hneg.isRelativelyAntiAmple Γ hΓ _ _ _
          _ hx
        linarith
      have hne : a - 1 ≠ a' - 1 := fun heq => hnt (hiff.mp heq).1
      have hlt : a - 1 < a' - 1 := lt_of_le_of_ne hle hne
      linarith
    · exfalso
      have hηQ : Q.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := by
        rw [hE]
        intro hmem
        exact hQE (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem).symm
      have hbr : f Q.genericPoint ∈ biregularLocus f := by
        by_contra h; exact hηQ (MMP.Mori.mem_exceptionalSet.mpr h)
      have hco : Order.coheight (f Q.genericPoint) = 1 :=
        (MMP.Positivity.coheight_map_of_mem_biregularLocus f hbr).trans Q.coheight_genericPoint
      have hco' : Order.coheight (E'.f E'.E.genericPoint) = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hbrfp _)]
        change Order.coheight ((E'.f ≫ fp) E'.E.genericPoint) = 1
        rw [show (E'.f ≫ fp) E'.E.genericPoint = DZ.f DZ.E.genericPoint from rfl, ← hc2, hco]
      have h2 := (isExceptional_iff_two_le_coheight_ph hX'v E').mp hE'
      rw [hco'] at h2
      exact absurd h2 (by decide)
  refine ⟨⟨hX'v, fun P' hP' => ?_,
    ⟨m, K', hK'm, isRCartier_logCanonical_of_isQFactorial hX'Q K' B'⟩,
    fun n E' a' hE' ha' => (hterm n E' a' hE' ha').le⟩, hterm⟩
  obtain ⟨Q, P, -, -, -, hB'P'⟩ := hover P'
  simp only [DivisorWithCoeffs.coeff_apply] at hP' ⊢
  rw [hB'P'] at hP' ⊢
  exact hT.1.2.1 P (by simpa only [DivisorWithCoeffs.coeff_apply] using hP')

/-! ### Finitely many divisorial steps -/

/-- Let `S i ⊆ α i` be sets with `S 0` finite and injections `φ i : α (i + 1) → α i` mapping
`S (i + 1)` into `S i`. If at every `i` with `D i` some point of `S i` is missed by `φ i`, then
`D i` holds for only finitely many `i`. -/
private theorem exists_forall_not_of_injective {α : ℕ → Type*} (S : ∀ i, Set (α i))
    (hS0 : (S 0).Finite) (φ : ∀ i, α (i + 1) → α i) (hφ : ∀ i, Function.Injective (φ i))
    (hmap : ∀ i, ∀ x ∈ S (i + 1), φ i x ∈ S i) (D : ℕ → Prop)
    (hD : ∀ i, D i → ∃ y ∈ S i, ∀ x, φ i x ≠ y) : ∃ i₀, ∀ i, i₀ ≤ i → ¬ D i := by
  have himg : ∀ i, φ i '' S (i + 1) ⊆ S i := fun i => by
    rintro _ ⟨x, hx, rfl⟩; exact hmap i x hx
  have hfin : ∀ i, (S i).Finite := by
    intro i
    induction i with
    | zero => exact hS0
    | succ i ih => exact Set.Finite.of_finite_image (ih.subset (himg i)) (hφ i).injOn
  have hle : ∀ i, (S (i + 1)).ncard ≤ (S i).ncard := fun i => by
    rw [← Set.ncard_image_of_injective _ (hφ i)]
    exact Set.ncard_le_ncard (himg i) (hfin i)
  have hlt : ∀ i, D i → (S (i + 1)).ncard < (S i).ncard := fun i hi => by
    obtain ⟨y, hy, hny⟩ := hD i hi
    rw [← Set.ncard_image_of_injective _ (hφ i)]
    refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨himg i, fun h => ?_⟩) (hfin i)
    rw [← h] at hy
    obtain ⟨x, -, hx⟩ := hy
    exact hny x hx
  have hanti : ∀ i j, i ≤ j → (S j).ncard ≤ (S i).ncard := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact (hle j).trans ih
  by_contra hcon
  push Not at hcon
  have key : ∀ m : ℕ, ∃ i, (S i).ncard + m ≤ (S 0).ncard := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hij, hDj⟩ := hcon i
      refine ⟨j + 1, ?_⟩
      have h1 := hlt j hDj
      have h2 := hanti i j hij
      omega
  obtain ⟨i, hi⟩ := key ((S 0).ncard + 1)
  omega

/-- Only finitely many prime divisors are exceptional for a proper birational morphism `h` onto
a normal integral scheme. -/
private theorem finite_setOf_two_le_coheight {Y X : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (h : Y ⟶ X) [IsProper h] (hb : IsBirationalMorphism h) :
    {P : MMP.Mori.PrimeDivisor Y | 2 ≤ Order.coheight (h P.genericPoint)}.Finite := by
  haveI : AlgebraicGeometry.IsNoetherian Y :=
    @AlgebraicGeometry.IsNoetherian.mk Y inferInstance inferInstance
  have hη : h (genericPoint Y) ∈ biregularLocus h := by
    refine MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal h hb ?_
    haveI := hb.isDominant
    have h1 := (genericPoint_spec Y).image h.continuous
    rw [Set.image_univ, h.denseRange.closure_range] at h1
    rw [((genericPoint_spec X).eq h1).symm,
      Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z]
    exact zero_le_one
  refine (MMP.Mori.finite_setOf_genericPoint_mem (T := (MMP.Mori.exceptionalSet h : Set Y))
    (MMP.Mori.exceptionalSet h).isClosed fun y hy h0 => ?_).subset fun P hP => ?_
  · have hy' : y = genericPoint Y := by
      have hsp : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
      exact (Specializes.antisymm
        (show y ⤳ genericPoint Y from (Order.coheight_eq_zero.1 h0) hsp) hsp).eq
    exact (MMP.Mori.mem_exceptionalSet.mp hy) (hy' ▸ hη)
  · by_contra hn
    apply (show ¬ 2 ≤ Order.coheight (h P.genericPoint) from ?_) hP
    have hb' : h P.genericPoint ∈ biregularLocus h := by
      by_contra hb''
      exact hn (MMP.Mori.mem_exceptionalSet.mpr hb'')
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus h hb', P.coheight_genericPoint]
    decide

/-- The image under a birational morphism of a prime divisor whose transform is a prime divisor
has coheight one. -/
private theorem coheight_map_eq_one_of_transformPrimeDivisor_eq_some {Y X : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (h : Y ⟶ X)
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor X}
    (hPQ : RationalMap.transformPrimeDivisor (X := Y) h.toRationalMap P = some Q) :
    Order.coheight (h P.genericPoint) = 1 := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hX
  rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff h P Q).mp hPQ,
    Q.coheight_genericPoint]

/-- A quasi-projective variety projective over a projective variety is projective. -/
private theorem isProjectiveVariety_of_comp {Z X : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsVariety ℂ sZ)
    {g : Z ⟶ X} (hg : IsProjectiveMorphism g) (hgs : g ≫ sX = sZ) :
    MMP.Mori.IsProjectiveVariety ℂ sZ :=
  (MMP.Mori.isProjectiveVariety_iff ℂ sZ).mpr ⟨hZ, hgs ▸ hg.comp hX.isProjective⟩

section StepInv

variable {X X0 X1 Z : Scheme.{0}} [IsIntegral X0] [CompactSpace X0] [IsLocallyNoetherian X0]
  [IsNormal X0] [IsIntegral X1] [CompactSpace X1] [IsLocallyNoetherian X1] [IsNormal X1]
  {sX : X ⟶ Spec (.of ℂ)} {s0 : X0 ⟶ Spec (.of ℂ)} {s1 : X1 ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} {π0 : X0 ⟶ X} {π1 : X1 ⟶ X} {K0 : Divisor X0} {C0 : RDivisor X0}
  {K1 : Divisor X1} {C1 : RDivisor X1} {R : Set (RelativeNumericalCurveClasses s0 π0)}
  {f : X0 ⟶ Z} {g : Z ⟶ X} {fp : X1 ⟶ Z}

/-- **The invariants of the program at the next model.** If `(X₀, C₀)` is a real terminal
`ℚ`-factorial threefold pair over `X` whose boundary components map to prime divisors of `X`,
then so is `(X₁, C₁)` after one step. -/
private theorem step_inv (hπ0 : π0 ≫ sX = s0) (hπ1 : π1 ≫ sX = s1)
    (hrc : IsRelativeContractionOfFace π0 R f g)
    (hne : IsNegativeExtremalContraction ℂ s0 sZ (logCanonicalDivisor K0 C0) f)
    (hfpg : fp ≫ g = π1)
    (hcase : ((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X0,
        (MMP.Mori.exceptionalSet f : Set X0) = E.support) ∧ IsIso fp ∧
        (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧ C1 = flipTransform f fp C0) ∨
      IsRealFlipStep s0 sZ s1 K0 C0 K1 C1 f fp)
    (hp0 : MMP.Mori.IsProjectiveVariety ℂ s0) (hq0 : IsQFactorial s0)
    (hp1 : MMP.Mori.IsProjectiveVariety ℂ s1) (hq1 : IsQFactorial s1)
    (hd : topologicalKrullDim X0 = 3) (hdX : topologicalKrullDim X = 3)
    (hXv : MMP.Mori.IsVariety ℂ sX)
    (hK0 : ∃ m : ℕ, K0.IsCanonicalDivisor s0 m) (hT : IsRealTerminalPair s0 C0)
    (hJ : ∀ P : MMP.Mori.PrimeDivisor X0, C0.coeff P ≠ 0 →
      Order.coheight (π0 P.genericPoint) = 1) :
    topologicalKrullDim X1 = 3 ∧ (∃ m : ℕ, K1.IsCanonicalDivisor s1 m) ∧
      IsRealTerminalPair s1 C1 ∧
      ∀ P' : MMP.Mori.PrimeDivisor X1, C1.coeff P' ≠ 0 →
        Order.coheight (π1 P'.genericPoint) = 1 := by
  obtain ⟨hfb, hfpb, -, -, -, hgs, hfps, hZ, hC1, hK1, -⟩ :=
    step_basic hπ0 hπ1 hrc hne hfpg hcase
  have h1v : IsNormalVariety ℂ s1 := ⟨hp1.toIsVariety, inferInstance⟩
  have h0v : IsNormalVariety ℂ s0 := hne.isNormalVariety_source
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ s0 := h0v.1
  haveI : MMP.Mori.IsVariety ℂ s1 := h1v.1
  have hdZ : topologicalKrullDim Z = topologicalKrullDim X0 :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s0 hfb
  have hd1 : topologicalKrullDim X1 = 3 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s1 hfpb, hdZ, hd]
  have hcorr := step_corr hπ0 hπ1 hrc hne hfpg hcase h1v
  have hJ1 : ∀ P' : MMP.Mori.PrimeDivisor X1, C1.coeff P' ≠ 0 →
      Order.coheight (π1 P'.genericPoint) = 1 := fun P' hP' => by
    obtain ⟨P, -, -, hcoef, hπ⟩ := hcorr P'
    rw [hπ]; exact hJ P (hcoef ▸ hP')
  refine ⟨hd1, hK1, ?_, hJ1⟩
  rcases hcase with ⟨⟨-, E, hE⟩, hiso, -, -⟩ | hfl
  · haveI := hiso
    have hE2 := two_le_coheight_map_genericPoint hne hfb hE
    have hCE : C0.coeff E = 0 := by
      by_contra hne0
      have h1 := hJ E hne0
      have h2 : Order.coheight (f E.genericPoint) ≤ Order.coheight (g (f E.genericPoint)) :=
        MMP.Flips.coheight_le_coheight_map sX sZ hXv hZ.1 g hgs (hdZ.trans (hd.trans hdX.symm)) _
      have h3 : g (f E.genericPoint) = π0 E.genericPoint := by
        rw [← hrc.comp_eq, Scheme.Hom.comp_apply]
      rw [h3, h1] at h2
      exact absurd (hE2.trans h2) (by decide)
    rw [hC1]
    exact isRealTerminalPair_of_divisorial hne hfb hE hfps hK0 hK1 hCE hT hp0 hq1
  · haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s0 := hp0
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s1 := hp1
    exact isRealTerminalPair_of_isRealFlipStep hfl hK0 hq0 hq1
      (IsProjectiveVariety.isQuasiProjectiveVariety ℂ s0)
      (IsProjectiveVariety.isQuasiProjectiveVariety ℂ s1) hd hd1 hT

end StepInv

/-- The target of a dominant morphism of finite type from an integral scheme over `ℂ` has
dimension at most that of the source. -/
private theorem topologicalKrullDim_le_of_isDominant {Z X : Scheme.{0}} [IsIntegral Z]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (q : Z ⟶ X) [LocallyOfFiniteType q]
    [IsDominant q] : topologicalKrullDim X ≤ topologicalKrullDim Z := by
  have e := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range q ℂ (q ≫ sX) sX rfl
  rw [q.denseRange.closure_range,
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq] at e
  rw [e]
  haveI : Nonempty (q.fiber (q.base (genericPoint Z))) :=
    ⟨q.asFiber (genericPoint Z)⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (q.fiber (q.base (genericPoint Z))) :=
    haveI : Nonempty (TopologicalSpace.IrreducibleCloseds (q.fiber (q.base (genericPoint Z)))) :=
      ⟨.closureSingleton (q.asFiber (genericPoint Z))⟩
    Order.krullDim_nonneg
  exact le_add_of_nonneg_left h0

/-! ### Relative contractions as absolute contractions -/

private theorem residueFieldDegree_pos_ph {V T : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} [IsSeparated sT] [LocallyOfFiniteType sT] (u : V ⟶ T)
    (hu : u ≫ sT = sV) (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) :
    0 < residueFieldDegree u Γ.point := by
  have hnc := Oai4C1.not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve ℂ (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve ℂ (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
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

/-- A relative 1-cycle pushes forward to zero. -/
private theorem pushforward_eq_zero_of_mem_relativeOneCycles {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} [IsSeparated sS] (π : X ⟶ S)
    (hπ : π ≫ sS = sX) {Z : OneCycle ℝ sX} (hZ : Z ∈ relativeOneCycles sX π) :
    OneCycle.pushforward ℝ sX sS π Z = 0 := by
  rw [relativeOneCycles, Finsupp.mem_supported] at hZ
  rw [OneCycle.pushforward, Finsupp.linearCombination_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  have := ProperCurve.pushforward_cycle_eq_zero_of_isContractedBy ℝ π hπ C (hZ hC)
  rw [OneCycle.pushforward_cycle] at this
  simp only [this, smul_zero]

/-- Over a projective base `S`, a curve numerically equivalent to a relative 1-cycle is contracted:
otherwise an ample divisor of `S` would have positive degree on its push-forward. -/
private theorem isContractedBy_of_numericalClass_eq {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (π : X ⟶ S)
    (hπ : π ≫ sS = sX) (C : ProperCurve sX) {Z : OneCycle ℝ sX}
    (hZ : Z ∈ relativeOneCycles sX π)
    (hCZ : OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX Z) :
    C.IsContractedBy π := by
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sS := hS.toIsVariety.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  by_contra hnc
  obtain ⟨H, hH⟩ := MMP.Mori.IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sS)
  have hpos := MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hS.toIsVariety H hH
    ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩
  have heq := (OneCycle.numericalClass_eq_iff.mp hCZ)
    ((Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf H))
  rw [← OneCycle.degree_pushforward π hπ, ← OneCycle.degree_pushforward π hπ,
    pushforward_eq_zero_of_mem_relativeOneCycles π hπ hZ, map_zero, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (Oai4C1.isProperCurve_map π hπ C hnc)] at heq
  have hd := residueFieldDegree_pos_ph π hπ C hnc
  have : OneCycle.degree ℝ sS (MMP.CartierDivisor.sheaf H)
      (Finsupp.single ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩
        (residueFieldDegree π C.point : ℝ)) =
      (residueFieldDegree π C.point : ℝ) *
        (degreeOn ℂ sS (ProperCurve.ι ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩)
          (ProperCurve.dim_le _) (MMP.CartierDivisor.sheaf H) : ℝ) := by
    rw [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul]
    rfl
  rw [this] at heq
  have : (0 : ℝ) < (residueFieldDegree π C.point : ℝ) *
      (degreeOn ℂ sS (ProperCurve.ι ⟨π C.point, Oai4C1.isProperCurve_map π hπ C hnc⟩)
        (ProperCurve.dim_le _) (MMP.CartierDivisor.sheaf H) : ℝ) :=
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast hpos)
  linarith

/-- **The relative contraction of a ray over a projective base is the absolute contraction of
its image** in `N₁(X)`, which is an extremal ray of `NE̅(X)`. -/
private theorem isContractionOfFace_image_relativeToAbsolute {X S Zs : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZs) {π : X ⟶ S} (hπ : π ≫ sS = sX)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sX π :
      Set (RelativeNumericalCurveClasses sX π)) R)
    {f : X ⟶ Zs} {g : Zs ⟶ S} (hcont : IsRelativeContractionOfFace π R f g)
    (hfs : f ≫ sZs = sX) :
    IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (relativeToAbsolute sX π '' R) ∧
      IsContractionOfFace ℂ sX sZs (relativeToAbsolute sX π '' R) f := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  have hray := isExtremalRay_image_relativeToAbsolute sX sS π hπ hR
  have hinj : Function.Injective (relativeToAbsolute sX π) :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX π).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX π)
  refine ⟨hray, hX, hZp, hfs, hray.1, fun C => ⟨fun hC => ?_, fun hC => ?_⟩, hcont.isIso_app⟩
  · have hCπ : C.IsContractedBy π := fun z hz => by
      rw [← hcont.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]
    exact ⟨C.relativeClass π hCπ, (hcont.isContractedBy_iff C hCπ).mp hC, rfl⟩
  · obtain ⟨r, hr, hrC⟩ := hC
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π r
    have hCπ : C.IsContractedBy π :=
      isContractedBy_of_numericalClass_eq hS π hπ C Z.2 hrC.symm
    refine (hcont.isContractedBy_iff C hCπ).mpr ?_
    have : C.relativeClass π hCπ = relativeNumericalClass sX π Z :=
      hinj (hrC.symm ▸ rfl)
    rw [this]; exact hr

/-- The open-immersion exceptional set lies in the exceptional set. -/
private theorem flips_exceptionalSet_subset {X Y : Scheme.{0}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := fun y hy =>
  MMP.Mori.mem_exceptionalSet.mpr fun hb => hy ⟨f ⁻¹ᵁ biregularLocus f, hb, by
    haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    rw [← morphismRestrict_ι]
    infer_instance⟩

/-- **Trichotomy for the relative contraction of an extremal ray** of a `ℚ`-factorial projective
variety over a projective base: it is of fibre type, divisorial, or small. -/
private theorem trichotomy_of_isRelativeContractionOfFace {X S Zs : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZs) {π : X ⟶ S} (hπ : π ≫ sS = sX)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sX π :
      Set (RelativeNumericalCurveClasses sX π)) R)
    {f : X ⟶ Zs} {g : Zs ⟶ S} (hcont : IsRelativeContractionOfFace π R f g)
    (hfs : f ≫ sZs = sX) (hZv : IsNormalVariety ℂ sZs) :
    topologicalKrullDim Zs < topologicalKrullDim X ∨
      (IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X,
        (MMP.Mori.exceptionalSet f : Set X) = E.support) ∨
      MMP.Flips.IsSmall ℂ sZs sX f := by
  obtain ⟨hray, hcf⟩ :=
    isContractionOfFace_image_relativeToAbsolute hX hS hZp hπ hR hcont hfs
  rcases (IsContractionOfFace.trichotomy_of_isExtremalRay hXQ hray hcf).1 with h | h | h
  · exact Or.inl h.dim_lt
  · exact Or.inr (Or.inl ⟨h.isBirationalMorphism, h.exists_primeDivisor⟩)
  · refine Or.inr (Or.inr ?_)
    haveI : IsNormal Zs := hZv.2
    have hb := h.isBirationalMorphism
    haveI : IsProper (f ≫ sZs) := by
      rw [hfs]; exact isProper_of_isProjectiveMorphism sX hX.isProjective
    haveI : IsSeparated sZs := hZv.1.toIsSeparated
    have hfp : IsProper f := IsProper.of_comp f sZs
    have hbc : MMP.Flips.IsBirationalContraction ℂ sZs sX f :=
      { isVariety_target := hZv.1
        isVariety_source := hX.toIsVariety
        comp_eq := hfs
        isProper := hfp
        isIso_app := hcf.isIso_app
        dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sX := sZs)
          (sX' := sX) (haveI := hZv.1; haveI := hX.toIsVariety; hb)).symm }
    refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
    refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => ?_
    exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h.two_le_codimension x
      (flips_exceptionalSet_subset f hx)

/-! ### Stages of a program over `X` -/

section Stages

/-- A model of a program over `X`: a normal integral scheme over `ℂ` and over `X`, with a
canonical divisor and a real boundary. -/
private structure Stage (X : Scheme.{0}) where
  Y : Scheme.{0}
  [isIntegral : IsIntegral Y]
  [compactSpace : CompactSpace Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  sY : Y ⟶ Spec (.of ℂ)
  πY : Y ⟶ X
  K : Divisor Y
  C : RDivisor Y

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-- The data of one step from a model `s`: the next model, the ray, its contraction and the
morphism from the next model to the contraction target. -/
private structure StepData {X : Scheme.{0}} (s : Stage X) where
  t : Stage X
  R : Set (RelativeNumericalCurveClasses s.sY s.πY)
  Zs : Scheme.{0}
  sZs : Zs ⟶ Spec (.of ℂ)
  f : s.Y ⟶ Zs
  g : Zs ⟶ X
  fp : t.Y ⟶ Zs

/-- The models obtained from `s0` by iterating a choice of steps. -/
private noncomputable def Stage.seq {X : Scheme.{0}} (s0 : Stage X)
    (next : (s : Stage X) → StepData s) : ℕ → Stage X
  | 0 => s0
  | i + 1 => (next (Stage.seq s0 next i)).t

/-- The rays of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progR {X : Scheme.{0}} (s0 : Stage X)
    (next : (s : Stage X) → StepData s) :
    ∀ i, Set (RelativeNumericalCurveClasses
      (modelStr s0.sY (fun j => (Stage.seq s0 next (j + 1)).sY) i)
      (modelMap s0.πY (fun j => (Stage.seq s0 next (j + 1)).πY) i))
  | 0 => (next s0).R
  | i + 1 => (next (Stage.seq s0 next (i + 1))).R

/-- The contractions of the iterated sequence of steps, indexed as the models of a program. -/
private noncomputable def Stage.progF {X : Scheme.{0}} (s0 : Stage X)
    (next : (s : Stage X) → StepData s) :
    ∀ i, modelSeq s0.Y (fun j => (Stage.seq s0 next (j + 1)).Y) i ⟶
      (next (Stage.seq s0 next i)).Zs
  | 0 => (next s0).f
  | i + 1 => (next (Stage.seq s0 next (i + 1))).f

end Stages

attribute [local instance] Stage.isIntegral Stage.compactSpace Stage.isLocallyNoetherian
  Stage.isNormal

/-- The invariants of the models of the program: projective `ℚ`-factorial threefolds over `X`,
dominating `X`, with a canonical divisor, real terminal, and with every boundary component
mapping onto a prime divisor of `X`. -/
private abbrev IsGoodModel {X Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (πY : Y ⟶ X) (K : Divisor Y) (C : RDivisor Y) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsQFactorial sY ∧ πY ≫ sX = sY ∧
    topologicalKrullDim Y = 3 ∧ (∃ m : ℕ, K.IsCanonicalDivisor sY m) ∧
    IsRealTerminalPair sY C ∧
    (∀ P : MMP.Mori.PrimeDivisor Y, C.coeff P ≠ 0 → Order.coheight (πY P.genericPoint) = 1) ∧
    IsDominant πY

/-- One step of a program over `X`: a negative extremal ray of `NE̅(Y/X)`, its contraction, and
a divisorial contraction or a real flip. -/
private abbrev IsProgramStep {X Y Y' Zs : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (sY : Y ⟶ Spec (.of ℂ)) (sY' : Y' ⟶ Spec (.of ℂ)) (sZs : Zs ⟶ Spec (.of ℂ))
    (πY : Y ⟶ X) (πY' : Y' ⟶ X) (K : Divisor Y) (C : RDivisor Y) (K' : Divisor Y')
    (C' : RDivisor Y') (R : Set (RelativeNumericalCurveClasses sY πY)) (f : Y ⟶ Zs)
    (g : Zs ⟶ X) (fp : Y' ⟶ Zs) : Prop :=
  IsExtremalRay ℝ (relativeClosedConeOfCurves sY πY :
      Set (RelativeNumericalCurveClasses sY πY)) R ∧
    (∀ (Γ : ProperCurve sY) (hΓ : Γ.IsContractedBy πY),
      Γ.relativeClass πY hΓ ∈ R →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber ℂ sY (logCanonicalDivisor K C) r L Γ x → x < 0) ∧
    IsRelativeContractionOfFace πY R f g ∧
    IsNegativeExtremalContraction ℂ sY sZs (logCanonicalDivisor K C) f ∧
    fp ≫ g = πY' ∧
    (((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor Y,
          (MMP.Mori.exceptionalSet f : Set Y) = E.support) ∧
        IsIso fp ∧ (∃ m : ℕ, K'.IsCanonicalDivisor sY' m) ∧ C' = flipTransform f fp C) ∨
      IsRealFlipStep sY sZs sY' K C K' C' f fp)

/-- **A step from a good model which is not nef.** Lemma
`MMP.Fourfold.IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef` gives a
negative extremal ray over `X` and its contraction; it is not of fibre type, since its target
dominates the threefold `X`, so it is divisorial or small, and the next model is the target of
the divisorial contraction or the real flip. The next model is again good. -/
private theorem exists_programStep {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdimX : topologicalKrullDim X = 3) {sY : Y ⟶ Spec (.of ℂ)} {πY : Y ⟶ X} {K : Divisor Y}
    {C : RDivisor Y} (hgood : IsGoodModel sX sY πY K C)
    (hnef : ¬ IsRelativelyNef ℂ sY πY (logCanonicalDivisor K C)) :
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : CompactSpace Y') (_ : IsLocallyNoetherian Y')
      (_ : IsNormal Y') (sY' : Y' ⟶ Spec (.of ℂ)) (πY' : Y' ⟶ X) (K' : Divisor Y')
      (C' : RDivisor Y') (R : Set (RelativeNumericalCurveClasses sY πY)) (Zs : Scheme.{0})
      (sZs : Zs ⟶ Spec (.of ℂ)) (f : Y ⟶ Zs) (g : Zs ⟶ X) (fp : Y' ⟶ Zs),
      IsGoodModel sX sY' πY' K' C' ∧ IsProgramStep sY sY' sZs πY πY' K C K' C' R f g fp := by
  obtain ⟨hYp, hYQ, hπ, hdim, hK, hT, hJ, hdom⟩ := hgood
  have hYv := hYQ.1
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have hC0 : 0 ≤ C := fun P => by
    by_cases hP : C.coeff P = 0
    · exact hP.ge
    · exact (hT.1.2.1 P hP).1.le
  obtain ⟨R, Zs, _, _, _, sZs, f, g, hR, hRneg, hcont, hZp, hneg, hdivQ, hsmall⟩ :=
    IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef hYp hX hπ hYQ hdim hK
      hC0 (isRealKltPair_of_isRealTerminalPair hT) hnef
  have hZv := hneg.isNormalVariety_target
  haveI : QuasiCompact sZs := hZv.1.toQuasiCompact
  haveI : CompactSpace Zs := QuasiCompact.compactSpace_of_compactSpace sZs
  have hct := hneg.isContraction
  have hfs : f ≫ sZs = sY := hct.comp_eq
  have hgs : g ≫ sX = sZs := by
    refine eq_of_comp_eq_of_isIso_app f hct.isIso_app ?_
    rw [← Category.assoc, hcont.comp_eq, hπ, hfs]
  haveI : IsDominant (f ≫ g) := hcont.comp_eq ▸ hdom
  haveI : IsDominant g := IsDominant.of_comp f g
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hcont.isProjectiveMorphism
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  rcases trichotomy_of_isRelativeContractionOfFace hYp hYQ hX hZp hπ hR hcont hfs hZv with
    hfib | hdiv | hsm
  · exfalso
    have hle := topologicalKrullDim_le_of_isDominant sX g
    rw [hdim, ← hdimX] at hfib
    exact absurd (hfib.trans_le hle) (lt_irrefl _)
  · obtain ⟨hZQ, -⟩ := hdivQ hdiv
    have hdZ : topologicalKrullDim Zs = 3 := by
      haveI : MMP.Mori.IsVariety ℂ sZs := hZv.1
      haveI : MMP.Mori.IsVariety ℂ sY := hYv.1
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZs sY hdiv.1, hdim]
    obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZs hZv hdZ
    have hstep : IsProgramStep sY sZs sZs πY g K C K' (flipTransform f (𝟙 Zs) C) R f g
        (𝟙 Zs) := ⟨hR, hRneg, hcont, hneg, Category.id_comp g,
          Or.inl ⟨hdiv, inferInstance, ⟨3, hK'⟩, rfl⟩⟩
    obtain ⟨hd', hK'', hT', hJ'⟩ := step_inv hπ hgs hcont hneg (Category.id_comp g) hstep.2.2.2.2.2
      hYp hYQ hZp hZQ hdim hdimX hX.toIsVariety hK hT hJ
    exact ⟨Zs, inferInstance, inferInstance, inferInstance, inferInstance, sZs, g, K',
      flipTransform f (𝟙 Zs) C, R, Zs, sZs, f, g, 𝟙 Zs,
      ⟨hZp, hZQ, hgs, hd', hK'', hT', hJ', inferInstance⟩, hstep⟩
  · obtain ⟨Y', _, _, _, _, sY', K', fp, hfl, hY'p, hY'Q, -, -⟩ := hsmall hsm
    have hfps : fp ≫ sZs = sY' := hfl.isSmall_flip.comp_eq
    have hπ' : (fp ≫ g) ≫ sX = sY' := by rw [Category.assoc, hgs, hfps]
    have hstep : IsProgramStep sY sY' sZs πY (fp ≫ g) K C K' (flipTransform f fp C) R f g fp :=
      ⟨hR, hRneg, hcont, hneg, rfl, Or.inr hfl⟩
    obtain ⟨hd', hK'', hT', hJ'⟩ := step_inv hπ hπ' hcont hneg rfl hstep.2.2.2.2.2
      hYp hYQ hY'p hY'Q hdim hdimX hX.toIsVariety hK hT hJ
    haveI := hfl.isBirationalMorphism_flip.isDominant
    exact ⟨Y', inferInstance, inferInstance, inferInstance, inferInstance, sY', fp ≫ g, K',
      flipTransform f fp C, R, Zs, sZs, f, g, fp,
      ⟨hY'p, hY'Q, hπ', hd', hK'', hT', hJ', inferInstance⟩, hstep⟩

private theorem solution
    {Y X : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sY : Y ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} {h : Y ⟶ X} {K : Divisor Y}
    {C : RDivisor Y}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hh : h ≫ sX = sY) (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hdimX : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : IsRealTerminalPair sY C)
    (hCX : ∀ P : MMP.Mori.PrimeDivisor Y, C.coeff P ≠ 0 →
      ∃ Q : MMP.Mori.PrimeDivisor X, RationalMap.transformPrimeDivisor h.toRationalMap P = some Q) :
    (∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
      [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ X) (KY : ∀ i, Divisor (Yi i))
      (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ X) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap h πY i ≫ sX = modelStr sY sYi i) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap h πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap h πY i)),
            Γ.relativeClass (modelMap h πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap h πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) →
      n ≠ ⊤ ∧
        ∀ i : ℕ, (i : ℕ∞) ≤ n → IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i)) ∧
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ X)
      (KY : ∀ i, Divisor (Yi i)) (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ X) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap h πY i ≫ sX = modelStr sY sYi i) ∧
      (∀ i < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap h πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap h πY i)),
            Γ.relativeClass (modelMap h πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap h πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap h πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq C CY n)) := by
  have hXv : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hJ0 : ∀ P : MMP.Mori.PrimeDivisor Y, C.coeff P ≠ 0 →
      Order.coheight (h P.genericPoint) = 1 := fun P hP => by
    obtain ⟨Q, hQ⟩ := hCX P hP
    exact coheight_map_eq_one_of_transformPrimeDivisor_eq_some hXv h hQ
  have huniv :
      ∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
        [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
        [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ X) (KY : ∀ i, Divisor (Yi i))
        (CY : ∀ i, RDivisor (Yi i))
        (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i)))
        (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
        (g : ∀ i, Zi i ⟶ X) (fp : ∀ i, Yi i ⟶ Zi i),
        (∀ i : ℕ, (i : ℕ∞) ≤ n →
          MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
            modelMap h πY i ≫ sX = modelStr sY sYi i) →
        (∀ i : ℕ, (i : ℕ∞) < n →
          IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap h πY i) :
              Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i))) (R i) ∧
            (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap h πY i)),
              Γ.relativeClass (modelMap h πY i) hΓ ∈ R i →
              ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
                IsRIntersectionNumber ℂ (modelStr sY sYi i)
                  (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
            IsRelativeContractionOfFace (modelMap h πY i) (R i) (f i) (g i) ∧
            IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
              (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
            fp i ≫ g i = πY i ∧
            (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                  (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
                IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
                CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
              IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
                (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) →
        n ≠ ⊤ ∧
          ∀ i : ℕ, (i : ℕ∞) ≤ n → IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i) := by
    intro n Yi sYi _ _ _ _ πY KY CY R Zi sZi f g fp hmod hstep
    -- the invariants along the program
    have hinv : ∀ i : ℕ, (i : ℕ∞) ≤ n →
        topologicalKrullDim (modelSeq Y Yi i) = 3 ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sY sYi i) m (divisorSeq K KY i)) ∧
        IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i) ∧
        ∀ P : MMP.Mori.PrimeDivisor (modelSeq Y Yi i), (divisorSeq C CY i).coeff P ≠ 0 →
          Order.coheight (modelMap h πY i P.genericPoint) = 1 := by
      intro i
      induction i with
      | zero => exact fun _ => ⟨hdim, hK, hC, hJ0⟩
      | succ i ih =>
        intro hi
        have hlt := natCast_lt_of_succ_le hi
        obtain ⟨hd, hKi, hT, hJ⟩ := ih hlt.le
        obtain ⟨hp0, hq0, hc0⟩ := hmod i hlt.le
        obtain ⟨hp1, hq1, hc1⟩ := hmod (i + 1) hi
        obtain ⟨-, -, hrc, hne, hfpg, hcase⟩ := hstep i hlt
        exact step_inv hc0 hc1 hrc hne hfpg hcase hp0 hq0 hp1 hq1 hd hdimX hX.toIsVariety hKi hT hJ
    refine ⟨?_, fun i hi => (hinv i hi).2.2.1⟩
    intro hn
    subst hn
    have hlt : ∀ i : ℕ, (i : ℕ∞) < ⊤ := ENat.coe_lt_top
    have hle : ∀ i : ℕ, (i : ℕ∞) ≤ ⊤ := fun _ => le_top
    -- the prime divisors of `Y_{i+1}` come from those of `Y_i`
    have hcorr : ∀ (i : ℕ) (P' : MMP.Mori.PrimeDivisor (Yi i)),
        ∃ P : MMP.Mori.PrimeDivisor (modelSeq Y Yi i), f i P.genericPoint = fp i P'.genericPoint ∧
          Order.coheight (fp i P'.genericPoint) = 1 ∧
          (CY i).coeff P' = (divisorSeq C CY i).coeff P ∧
          πY i P'.genericPoint = modelMap h πY i P.genericPoint := fun i P' => by
      obtain ⟨-, -, hc0⟩ := hmod i (hle i)
      obtain ⟨hp1, -, hc1⟩ := hmod (i + 1) (hle _)
      obtain ⟨-, -, hrc, hne, hfpg, hcase⟩ := hstep i (hlt i)
      exact step_corr hc0 hc1 hrc hne hfpg hcase ⟨hp1.toIsVariety, inferInstance⟩ P'
    choose φ hφ using hcorr
    have hφinj : ∀ i, Function.Injective (φ i) := fun i P₁ P₂ h12 => by
      obtain ⟨-, -, hc0⟩ := hmod i (hle i)
      obtain ⟨hp1, -, hc1⟩ := hmod (i + 1) (hle _)
      obtain ⟨-, -, hrc, hne, hfpg, hcase⟩ := hstep i (hlt i)
      refine step_inj hc0 hc1 hrc hne hfpg hcase ⟨hp1.toIsVariety, inferInstance⟩ ?_
      have h12' := congrArg (fun P => (f i) P.genericPoint) h12
      exact (hφ i P₁).1.symm.trans (h12'.trans (hφ i P₂).1)
    -- the prime divisors exceptional over `X` are finitely many and drop at divisorial steps
    haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
    obtain ⟨i₀, hi₀⟩ := exists_forall_not_of_injective
      (α := fun i => MMP.Mori.PrimeDivisor (modelSeq Y Yi i))
      (fun i => {P | 2 ≤ Order.coheight (modelMap h πY i P.genericPoint)})
      (finite_setOf_two_le_coheight h hhb) φ hφinj
      (fun i x hx => by
        change 2 ≤ Order.coheight (modelMap h πY i (φ i x).genericPoint)
        rw [← (hφ i x).2.2.2]
        exact hx)
      (fun i => (IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
          (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
        IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
        CY i = flipTransform (f i) (fp i) (divisorSeq C CY i))
      (fun i hD => by
        obtain ⟨⟨hfb, E, hE⟩, -, -, -⟩ := hD
        obtain ⟨-, -, hc0⟩ := hmod i (hle i)
        obtain ⟨-, -, hc1⟩ := hmod (i + 1) (hle _)
        obtain ⟨-, -, hrc, hne, hfpg, hcase⟩ := hstep i (hlt i)
        obtain ⟨-, -, -, -, -, hgs, -, hZ, -⟩ := step_basic hc0 hc1 hrc hne hfpg hcase
        have hE2 := two_le_coheight_map_genericPoint hne hfb hE
        refine ⟨E, ?_, fun x hx => ?_⟩
        · haveI : MMP.Mori.IsVariety ℂ (sZi i) := hZ.1
          haveI : MMP.Mori.IsVariety ℂ (modelStr sY sYi i) := hne.isNormalVariety_source.1
          have hdZ : topologicalKrullDim (Zi i) = topologicalKrullDim (modelSeq Y Yi i) :=
            MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sZi i)
              (modelStr sY sYi i) hfb
          have h2 := MMP.Flips.coheight_le_coheight_map sX (sZi i) hX.toIsVariety hZ.1 (g i) hgs
            (hdZ.trans ((hinv i (hle i)).1.trans hdimX.symm)) (f i E.genericPoint)
          have h3 : g i (f i E.genericPoint) = modelMap h πY i E.genericPoint := by
            rw [← hrc.comp_eq, Scheme.Hom.comp_apply]
          rw [h3] at h2
          exact hE2.trans h2
        · have h1 := (hφ i x).2.1
          rw [← (hφ i x).1, hx] at h1
          rw [h1] at hE2
          exact absurd hE2 (by decide))
    -- after `i₀` every step is a flip
    have hflip : ∀ j : ℕ, IsRealFlipStep (modelStr sY sYi (i₀ + j)) (sZi (i₀ + j))
        (sYi (i₀ + j)) (divisorSeq K KY (i₀ + j)) (divisorSeq C CY (i₀ + j)) (KY (i₀ + j))
        (CY (i₀ + j)) (f (i₀ + j)) (fp (i₀ + j)) := fun j => by
      obtain ⟨-, -, -, -, -, hcase⟩ := hstep (i₀ + j) (hlt _)
      exact hcase.resolve_left (hi₀ (i₀ + j) (Nat.le_add_right _ _))
    have hZproj : ∀ j : ℕ, MMP.Mori.IsProjectiveVariety ℂ (sZi (i₀ + j)) := fun j => by
      obtain ⟨-, -, hc0⟩ := hmod (i₀ + j) (hle _)
      obtain ⟨-, -, hc1⟩ := hmod (i₀ + j + 1) (hle _)
      obtain ⟨-, -, hrc, hne, hfpg, hcase⟩ := hstep (i₀ + j) (hlt _)
      obtain ⟨-, -, -, -, -, hgs, -⟩ := step_basic hc0 hc1 hrc hne hfpg hcase
      exact isProjectiveVariety_of_comp hX (hflip j).isQuasiProjectiveVariety_target.toIsVariety
        hrc.isProjectiveMorphism hgs
    -- the infinite flip tail
    let σ : RealFlipSequence (modelStr sY sYi i₀) (divisorSeq K KY i₀) (divisorSeq C CY i₀) :=
      { n := ⊤
        Y := fun j => Yi (i₀ + j)
        sY := fun j => sYi (i₀ + j)
        isIntegral := fun _ => inferInstance
        compactSpace := fun _ => inferInstance
        isLocallyNoetherian := fun _ => inferInstance
        isNormal := fun _ => inferInstance
        KY := fun j => KY (i₀ + j)
        BY := fun j => CY (i₀ + j)
        Z := fun j => Zi (i₀ + j)
        sZ := fun j => sZi (i₀ + j)
        f := fun j => match j with
          | 0 => f i₀
          | j + 1 => f (i₀ + j + 1)
        fp := fun j => fp (i₀ + j)
        isCanonicalDivisor := (hinv i₀ (hle _)).2.1
        isQFactorial := fun j _ => match j with
          | 0 => (hmod i₀ (hle _)).2.1
          | j + 1 => (hmod (i₀ + j + 1) (hle _)).2.1
        isQuasiProjectiveVariety := fun j _ => match j with
          | 0 => by
            haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (modelStr sY sYi i₀) :=
              (hmod i₀ (hle _)).1
            exact (show AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (modelStr sY sYi i₀) from
              IsProjectiveVariety.isQuasiProjectiveVariety ℂ _)
          | j + 1 => by
            haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (sYi (i₀ + j)) :=
              (hmod (i₀ + j + 1) (hle _)).1
            exact (show AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (sYi (i₀ + j)) from
              IsProjectiveVariety.isQuasiProjectiveVariety ℂ _)
        dim_eq := fun j _ => match j with
          | 0 => (hinv i₀ (hle _)).1
          | j + 1 => (hinv (i₀ + j + 1) (hle _)).1
        isRealFlipStep := fun j _ => match j with
          | 0 => hflip 0
          | j + 1 => hflip (j + 1) }
    exact RealFlipSequence.n_ne_top_of_isRealCanonicalPair σ
      (fun j _ => match j with
        | 0 => (hinv i₀ (hle _)).2.2.1.1
        | j + 1 => (hinv (i₀ + j + 1) (hle _)).2.2.1.1)
      (fun j _ => match j with
        | 0 => (hmod i₀ (hle _)).1
        | j + 1 => (hmod (i₀ + j + 1) (hle _)).1)
      (fun j _ => hZproj j) rfl
  refine ⟨huniv, ?_⟩
  classical
  haveI : IsDominant h := hhb.isDominant
  let s0 : Stage X := ⟨Y, sY, h, K, C⟩
  have hgood0 : IsGoodModel sX sY h K C := ⟨hY, hYQ, hh, hdim, hK, hC, hJ0, inferInstance⟩
  let Pr : Stage X → Prop := fun s => IsGoodModel sX s.sY s.πY s.K s.C
  let cond : Stage X → Prop := fun s =>
    Pr s ∧ ¬ IsRelativelyNef ℂ s.sY s.πY (logCanonicalDivisor s.K s.C)
  let Q : (s : Stage X) → StepData s → Prop := fun s d =>
    IsGoodModel sX d.t.sY d.t.πY d.t.K d.t.C ∧
      IsProgramStep s.sY d.t.sY d.sZs s.πY d.t.πY s.K s.C d.t.K d.t.C d.R d.f d.g d.fp
  have hex : ∀ s : Stage X, cond s → ∃ d : StepData s, Q s d := by
    rintro s ⟨hs, hnef⟩
    obtain ⟨Y', _, _, _, _, sY', πY', K', C', R, Zs, sZs, f, g, fp, hY', hst⟩ :=
      exists_programStep hX hdimX hs hnef
    exact ⟨⟨⟨Y', sY', πY', K', C'⟩, R, Zs, sZs, f, g, fp⟩, hY', hst⟩
  let next : (s : Stage X) → StepData s := fun s =>
    if hc : cond s then (hex s hc).choose else ⟨s, ∅, X, sX, s.πY, 𝟙 X, s.πY⟩
  have hnext : ∀ s : Stage X, cond s → Q s (next s) := by
    intro s hc
    simp only [next, dif_pos hc]
    exact (hex s hc).choose_spec
  have hnext' : ∀ s : Stage X, ¬ cond s → (next s).t = s := by
    intro s hc
    simp only [next, dif_neg hc]
  have hPr : ∀ i, Pr (Stage.seq s0 next i) := by
    intro i
    induction i with
    | zero => exact hgood0
    | succ i ih =>
      change Pr (next (Stage.seq s0 next i)).t
      by_cases hc : cond (Stage.seq s0 next i)
      · exact (hnext _ hc).1
      · rwa [hnext' _ hc]
  have hmod : ∀ i : ℕ,
      MMP.Mori.IsProjectiveVariety ℂ (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sY) i) ∧
      IsQFactorial (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sY) i) ∧
      modelMap h (fun j => (Stage.seq s0 next (j + 1)).πY) i ≫ sX =
        modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sY) i := by
    intro i
    cases i with
    | zero => exact ⟨hY, hYQ, hh⟩
    | succ i => exact ⟨(hPr (i + 1)).1, (hPr (i + 1)).2.1, (hPr (i + 1)).2.2.1⟩
  have hstepi : ∀ i : ℕ, cond (Stage.seq s0 next i) →
      IsProgramStep (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sY) i)
        (Stage.seq s0 next (i + 1)).sY (next (Stage.seq s0 next i)).sZs
        (modelMap h (fun j => (Stage.seq s0 next (j + 1)).πY) i)
        (Stage.seq s0 next (i + 1)).πY
        (divisorSeq K (fun j => (Stage.seq s0 next (j + 1)).K) i)
        (divisorSeq C (fun j => (Stage.seq s0 next (j + 1)).C) i)
        (Stage.seq s0 next (i + 1)).K (Stage.seq s0 next (i + 1)).C
        (Stage.progR s0 next i) (Stage.progF s0 next i) (next (Stage.seq s0 next i)).g
        (next (Stage.seq s0 next i)).fp := by
    intro i hi
    cases i <;> exact (hnext _ hi).2
  have hnefi : ∀ i : ℕ, IsRelativelyNef ℂ (Stage.seq s0 next i).sY (Stage.seq s0 next i).πY
      (logCanonicalDivisor (Stage.seq s0 next i).K (Stage.seq s0 next i).C) →
      IsRelativelyNef ℂ (modelStr sY (fun j => (Stage.seq s0 next (j + 1)).sY) i)
        (modelMap h (fun j => (Stage.seq s0 next (j + 1)).πY) i)
        (logCanonicalDivisor (divisorSeq K (fun j => (Stage.seq s0 next (j + 1)).K) i)
          (divisorSeq C (fun j => (Stage.seq s0 next (j + 1)).C) i)) := by
    intro i hi
    cases i <;> exact hi
  have hfin : ∃ i, IsRelativelyNef ℂ (Stage.seq s0 next i).sY (Stage.seq s0 next i).πY
      (logCanonicalDivisor (Stage.seq s0 next i).K (Stage.seq s0 next i).C) := by
    by_contra hno
    simp only [not_exists] at hno
    exact (huniv ⊤ (fun j => (Stage.seq s0 next (j + 1)).Y)
      (fun j => (Stage.seq s0 next (j + 1)).sY) (fun j => (Stage.seq s0 next (j + 1)).πY)
      (fun j => (Stage.seq s0 next (j + 1)).K) (fun j => (Stage.seq s0 next (j + 1)).C)
      (Stage.progR s0 next) (fun i => (next (Stage.seq s0 next i)).Zs)
      (fun i => (next (Stage.seq s0 next i)).sZs) (Stage.progF s0 next)
      (fun i => (next (Stage.seq s0 next i)).g) (fun i => (next (Stage.seq s0 next i)).fp)
      (fun i _ => hmod i) (fun i _ => hstepi i ⟨hPr i, hno i⟩)).1 rfl
  exact ⟨Nat.find hfin, fun j => (Stage.seq s0 next (j + 1)).Y,
    fun j => (Stage.seq s0 next (j + 1)).sY, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun j => (Stage.seq s0 next (j + 1)).πY,
    fun j => (Stage.seq s0 next (j + 1)).K, fun j => (Stage.seq s0 next (j + 1)).C,
    Stage.progR s0 next, fun i => (next (Stage.seq s0 next i)).Zs,
    fun i => (next (Stage.seq s0 next i)).sZs, Stage.progF s0 next,
    fun i => (next (Stage.seq s0 next i)).g, fun i => (next (Stage.seq s0 next i)).fp,
    fun i _ => hmod i, fun i hi => hstepi i ⟨hPr i, Nat.find_min hfin hi⟩,
    hnefi _ (Nat.find_spec hfin)⟩

end

end Proof_lem_fourfold_real_terminal_program_over_birational_base

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Terminal real programs over a birational base.** Let `h : Y ⟶ X` be a projective birational
morphism of projective normal complex threefolds, `Y` `ℚ`-factorial with canonical divisor `K`,
and `(Y, C)` a real terminal pair every prime component of which maps onto a prime divisor of
`X`. Then every `(K + C)`-program over `X` from `(Y, C)` is finite and passes only through real
terminal pairs, and some such program ends at a projective `ℚ`-factorial model with `K_n + C_n`
nef over `X`. -/
@[mmp "lem_fourfold_real_terminal_program_over_birational_base"]
public theorem IsRealTerminalPair.terminates_of_isBirationalMorphism
    {Y X : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sY : Y ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)} {h : Y ⟶ X} {K : Divisor Y}
    {C : RDivisor Y}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hh : h ≫ sX = sY) (hhp : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hYQ : IsQFactorial sY) (hdim : topologicalKrullDim Y = 3)
    (hdimX : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n) (hC : IsRealTerminalPair sY C)
    (hCX : ∀ P : MMP.Mori.PrimeDivisor Y, C.coeff P ≠ 0 →
      ∃ Q : MMP.Mori.PrimeDivisor X, RationalMap.transformPrimeDivisor h.toRationalMap P = some Q) :
    (∀ (n : ℕ∞) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Yi i)] [∀ i, CompactSpace (Yi i)] [∀ i, IsLocallyNoetherian (Yi i)]
      [∀ i, IsNormal (Yi i)] (πY : ∀ i, Yi i ⟶ X) (KY : ∀ i, Divisor (Yi i))
      (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ X) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap h πY i ≫ sX = modelStr sY sYi i) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap h πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap h πY i)),
            Γ.relativeClass (modelMap h πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap h πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) →
      n ≠ ⊤ ∧
        ∀ i : ℕ, (i : ℕ∞) ≤ n → IsRealTerminalPair (modelStr sY sYi i) (divisorSeq C CY i)) ∧
    ∃ (n : ℕ) (Yi : ℕ → Scheme.{0}) (sYi : ∀ i, Yi i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Yi i)) (_ : ∀ i, CompactSpace (Yi i))
      (_ : ∀ i, IsLocallyNoetherian (Yi i)) (_ : ∀ i, IsNormal (Yi i)) (πY : ∀ i, Yi i ⟶ X)
      (KY : ∀ i, Divisor (Yi i)) (CY : ∀ i, RDivisor (Yi i))
      (R : ∀ i, Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i)))
      (Zi : ℕ → Scheme.{0}) (sZi : ∀ i, Zi i ⟶ Spec (.of ℂ)) (f : ∀ i, modelSeq Y Yi i ⟶ Zi i)
      (g : ∀ i, Zi i ⟶ X) (fp : ∀ i, Yi i ⟶ Zi i),
      (∀ i ≤ n,
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sY sYi i) ∧ IsQFactorial (modelStr sY sYi i) ∧
          modelMap h πY i ≫ sX = modelStr sY sYi i) ∧
      (∀ i < n,
        IsExtremalRay ℝ (relativeClosedConeOfCurves (modelStr sY sYi i) (modelMap h πY i) :
            Set (RelativeNumericalCurveClasses (modelStr sY sYi i) (modelMap h πY i))) (R i) ∧
          (∀ (Γ : ProperCurve (modelStr sY sYi i)) (hΓ : Γ.IsContractedBy (modelMap h πY i)),
            Γ.relativeClass (modelMap h πY i) hΓ ∈ R i →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq Y Yi i)) (x : ℝ),
              IsRIntersectionNumber ℂ (modelStr sY sYi i)
                (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) r L Γ x → x < 0) ∧
          IsRelativeContractionOfFace (modelMap h πY i) (R i) (f i) (g i) ∧
          IsNegativeExtremalContraction ℂ (modelStr sY sYi i) (sZi i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq C CY i)) (f i) ∧
          fp i ≫ g i = πY i ∧
          (((IsBirationalMorphism (f i) ∧ ∃ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq Y Yi i)) = E.support) ∧
              IsIso (fp i) ∧ (∃ m : ℕ, (KY i).IsCanonicalDivisor (sYi i) m) ∧
              CY i = flipTransform (f i) (fp i) (divisorSeq C CY i)) ∨
            IsRealFlipStep (modelStr sY sYi i) (sZi i) (sYi i) (divisorSeq K KY i)
              (divisorSeq C CY i) (KY i) (CY i) (f i) (fp i))) ∧
      IsRelativelyNef ℂ (modelStr sY sYi n) (modelMap h πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq C CY n)) :=
  Proof_lem_fourfold_real_terminal_program_over_birational_base.solution hY hX hh hhp hhb hYQ
    hdim hdimX hK hC hCX

end MMP.Fourfold
