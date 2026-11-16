module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalOverBirationalBase
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.DltLogResolutionCriterion
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Crepant real terminal models of projective real klt threefolds

Let `(X, B)` be a klt pair with an effective real boundary `B` on a normal projective complex
threefold `X`. Then there is a projective birational morphism `h : Y ⟶ X` from a `ℚ`-factorial
variety `Y` and an effective real boundary `B_Y` on `Y` with `K_Y + B_Y = h^*(K_X + B)` such that
`(Y, B_Y)` is real terminal.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_isRealTerminalPair_crepant`: the crepant terminal model.

## Implementation notes

The equality `K_Y + B_Y = h^*(K_X + B)`, with `K_Y = div(h^*ω)` for the rational top form `ω`
defining `K_X`, is recorded prime by prime on `Y`: for every prime divisor `F` of `Y`, regarded
as the divisor `(Y, h, F)` over `X`, the log discrepancy `a(F, X, B)`
(`MMP.Intersection.IsLogDiscrepancy`) is `1 - coeff_F(B_Y)`. This is the convention of
`MMP.Mori.IsCrepantBoundary`, and it determines `B_Y`.

## References

* [OAI4] the fourfold source, *Projective real klt threefolds have crepant terminal models*.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace Proof_thm_fourfold_real_klt_crepant_terminal_model

section

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The set of exceptional divisorial valuations of `k(X)` with `a(v, X, B) ≤ 1`. -/
private def lowSet (sX : X ⟶ Spec (.of ℂ)) (B : RDivisor X) :
    Set (Valuation X.functionField ℤᵐ⁰) :=
  {v | ∃ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ),
    E.IsExceptional ∧ E.valuation = v ∧ MMP.Intersection.IsLogDiscrepancy sX n B E a ∧ a ≤ 1}

/-- The valuations of `k(X)` realized by a prime divisor of `Y`, for `h : Y ⟶ X`. -/
private def realized {Y : Scheme.{0}} (h : Y ⟶ X) (hY : IsNormalVariety ℂ (h ≫ sX))
    (hh : IsBirationalMorphism h) : Set (Valuation X.functionField ℤᵐ⁰) :=
  {v | ∃ F : MMP.Mori.PrimeDivisor Y, (⟨Y, h, hY, hh, F⟩ : DivisorOver ℂ sX).valuation = v}

/-- `(Y, h, B_Y)` is a crepant model of `(X, B)`: `h` is projective, `B_Y` effective and
`a(F, X, B) = 1 - coeff_F B_Y` for every prime divisor `F` of `Y`. -/
private def IsCrepantModel (B : RDivisor X) {Y : Scheme.{0}} (h : Y ⟶ X)
    (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h) (BY : RDivisor Y) : Prop :=
  IsProjectiveMorphism h ∧ (∀ P, 0 ≤ BY.coeff P) ∧
    ∀ F : MMP.Mori.PrimeDivisor Y,
      MMP.Intersection.IsLogDiscrepancy sX 3 B ⟨Y, h, hY, hh, F⟩ (1 - BY.coeff F)

/-! ### Presentations of `K_X + B` -/

/-- A canonical divisor of a threefold is one in degree three. -/
private theorem eq_three_of_isCanonicalDivisor {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) (hdim : topologicalKrullDim Y = 3) : n = 3 := by
  have := hK.topologicalKrullDim_eq
  rw [hdim] at this
  exact_mod_cast this.symm

/-- A klt pair `(X, B)` on a threefold has a presentation `div(ω) + B = ∑ rᵢ Cᵢ` by Cartier
divisors `Cᵢ`, with `div(ω)` a canonical divisor. -/
private theorem exists_presentation (hdim : topologicalKrullDim X = 3) {B : RDivisor X}
    (hB : IsRealKltPair sX B) :
    ∃ (ω : RationalPluriForms sX 3 1) (m : ℕ) (r : Fin m → ℝ) (C : Fin m → Divisor X),
      ω ≠ 0 ∧ (∃ K : Divisor X, K.IsCanonicalDivisor sX 3 ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω) ∧
      (∀ i, (C i).IsCartier) ∧
      ∀ Γ : MMP.Mori.PrimeDivisor X,
        (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ) := by
  obtain ⟨hXn, -, ⟨n, K, hK, ⟨m, r, C, hC, hsum⟩⟩, -⟩ := hB
  obtain rfl := eq_three_of_isCanonicalDivisor hK hdim
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  refine ⟨ω, m, r, C, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, hC, fun Γ => ?_⟩
  rw [hω Γ, ← hsum Γ]
  rfl

/-- With a presentation `div(ω) + B = ∑ rᵢ Cᵢ`, the log discrepancy of a prime divisor `F` of a
proper birational model `h : Y ⟶ X` is `1 + ord_F(h^*ω) - ∑ rᵢ coeff_F(h^*Cᵢ)`. -/
private theorem isLogDiscrepancy_of_presentation (hXn : IsNormalVariety ℂ sX) {B : RDivisor X}
    {ω : RationalPluriForms sX 3 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (hω0 : ω ≠ 0)
    (hK : ∃ K : Divisor X, K.IsCanonicalDivisor sX 3 ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ))
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ X)
    (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h) [IsProper h]
    (C' : Fin m → Divisor Y) (hC' : ∀ i, ∃ hB, (C i).IsPullback h hB (C' i))
    (F : MMP.Mori.PrimeDivisor Y) :
    MMP.Intersection.IsLogDiscrepancy sX 3 B ⟨Y, h, hY, hh, F⟩
      (1 + ((⟨Y, h, hY, hh, F⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) -
        ∑ i, r i * ((C' i).coeff F : ℝ)) :=
  ⟨hXn, ‹_›, ω, hω0, hK, m, r, C, C', hC, hsum, hC', rfl⟩

/-- The coefficients of the boundary of a crepant model, in terms of a presentation. -/
private theorem coeff_eq_of_isCrepantModel (hXn : IsNormalVariety ℂ sX) {B : RDivisor X}
    {ω : RationalPluriForms sX 3 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (hω0 : ω ≠ 0)
    (hK : ∃ K : Divisor X, K.IsCanonicalDivisor sX 3 ∧ ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    (hC : ∀ i, (C i).IsCartier)
    (hsum : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * ((C i).coeff Γ : ℝ))
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {h : Y ⟶ X}
    {hY : IsNormalVariety ℂ (h ≫ sX)} {hh : IsBirationalMorphism h} {BY : RDivisor Y}
    (hc : IsCrepantModel (sX := sX) B h hY hh BY)
    (C' : Fin m → Divisor Y) (hC' : ∀ i, ∃ hB, (C i).IsPullback h hB (C' i))
    (F : MMP.Mori.PrimeDivisor Y) :
    BY.coeff F = ∑ i, r i * ((C' i).coeff F : ℝ) -
      ((⟨Y, h, hY, hh, F⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) := by
  haveI := isProper_of_isProjectiveMorphism h hc.1
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hc.2.2 F)
    (isLogDiscrepancy_of_presentation hXn hω0 hK hC hsum h hY hh C' hC' F)
  linarith

/-- The trivial crepant model `(X, 𝟙, B)`. -/
private theorem exists_isCrepantModel_id (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sX B) :
    ∃ (hY : IsNormalVariety ℂ (𝟙 X ≫ sX)) (hh : IsBirationalMorphism (𝟙 X)),
      IsCrepantModel (sX := sX) B (𝟙 X) hY hh B := by
  have hXn : IsNormalVariety ℂ sX := hB.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨ω, m, r, C, hω0, hK, hC, hsum⟩ := exists_presentation hdim hB
  have hY : IsNormalVariety ℂ (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  have hh : IsBirationalMorphism (𝟙 X) := isBirationalMorphism_of_isIso _
  refine ⟨hY, hh, MMP.isProjectiveMorphism_of_isClosedImmersion _, hB0,
    fun F => ?_⟩
  choose C' hC' using fun i =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have h1 := isLogDiscrepancy_of_presentation hXn hω0 hK hC hsum (𝟙 X) hY hh C'
    (fun i => ⟨_, hC' i⟩) F
  convert h1 using 1
  have hc : ∀ i, (C' i).coeff F = (C i).coeff F := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) F F rfl (hC i) (hC' i)
  have ho : (⟨X, 𝟙 X, hY, hh, F⟩ : DivisorOver ℂ sX).ordPullback ω = F.ordForm ω :=
    MMP.Mori.DivisorOver.ordPullback_ofPrimeDivisor hXn hdim F ω
  simp only [hc, ho, ← hsum F]
  ring

/-! ### General facts on models -/

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsQFactorial sY) (D : RDivisor Y) :
    MMP.Flips.IsCartierCombination D := by
  classical
  choose n hn hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨_, fun j => D (e.symm j) / n (e.symm j),
    fun j => ((n (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1,
    fun j => hc _, ?_⟩
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / n P) •
      Divisor.toRDivisor (((n P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hn0 : (n P : ℝ) ≠ 0 := by exact_mod_cast (hn P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hn0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  have hD : D = ∑ j, (fun j => D (e.symm j) / n (e.symm j)) j •
      Divisor.toRDivisor ((fun j => ((n (e.symm j) : ℕ) : ℤ) •
        (Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1 : Divisor Y)) j) := by
    rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / n P) •
        Divisor.toRDivisor (((n P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
          Divisor Y)))]
    rw [Finset.sum_coe_sort D.support (fun P => (D P / n P) •
        Divisor.toRDivisor (((n P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
    simp_rw [hterm]
    exact (Finsupp.sum_single D).symm
  simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hD

/-- Equal `ℝ`-Cartier divisors are numerically equivalent. -/
private theorem isNumericallyEquivalentOver_of_eq {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) {N₁ N₂ : RDivisor Y}
    (h : N₁ = N₂) (hN : MMP.Flips.IsCartierCombination N₁) :
    MMP.Flips.IsNumericallyEquivalentOver ℂ sY f N₁ N₂ := by
  subst h
  exact ⟨hN, hN, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ h₁ h₂ =>
    (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sY C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩

/-- Nefness of `K + C` over a base does not depend on the canonical divisor `K` in its linear
equivalence class. -/
private theorem isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent {Y Z : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] {π : Y ⟶ Z} {K K' : Divisor Y} {C : RDivisor Y}
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY π (MMP.Flips.logCanonicalDivisor K C))
    (hKK : K'.LinearlyEquivalent K) :
    MMP.Flips.IsRelativelyNef ℂ sY π (MMP.Flips.logCanonicalDivisor K' C) := by
  obtain ⟨φ, hφ⟩ := hKK
  set T : Divisor Y := K' - K with hTdef
  have hT0 : T.LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero]; exact hφ⟩
  have hTc : T.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hT0 Divisor.isCartier_zero
  obtain ⟨m, r, L, hL, hD, hpos⟩ := hnef
  refine ⟨m + 1, Fin.cons 1 r, Fin.cons T L, fun j => ?_, ?_, fun Γ hΓ x hx => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) j
    · exact hTc
    · exact hL i
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, one_smul]
    simp only [Fin.cons_succ]
    rw [← hD, MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, hTdef, map_sub]
    abel
  · obtain ⟨hL', d, hDeq, hd, rfl⟩ := hx
    have hd0 : d 0 = 0 := by
      obtain ⟨C', ν, hν, hdim, hdeq⟩ := hd 0
      haveI := hν.isFinite
      haveI : IsProper ((ν ≫ Γ.ι) ≫ sY) := by rw [Category.assoc]; infer_instance
      rw [hdeq]
      exact MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sY (ν ≫ Γ.ι) hdim (hL' 0)
        hT0
    have hx := hpos Γ hΓ (∑ j : Fin m, r j * d j.succ)
      ⟨hL, fun j => d j.succ, hD, fun j => hd j.succ, rfl⟩
    rw [Fin.sum_univ_succ, hd0]
    simpa using hx

/-- A prime divisor of a proper birational model that is not exceptional maps onto a prime
divisor. -/
private theorem exists_genericPoint_eq_of_not_isExceptionalPrimeDivisor {W Y : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) {p : W ⟶ Y}
    (hW : IsNormalVariety ℂ (p ≫ sY)) [IsProper p] (hp : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (hP : ¬ MMP.Flips.IsExceptionalPrimeDivisor sY p P) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, p P.genericPoint = Q.genericPoint := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : MMP.Mori.IsVariety ℂ sY := hY.1
  haveI : MMP.Mori.IsVariety ℂ (p ≫ sY) := hW.1
  have hdim : topologicalKrullDim W = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hp).symm
  have h1 : 1 ≤ Order.coheight (p P.genericPoint) := by
    have := MMP.Flips.coheight_le_coheight_map sY (p ≫ sY) hY.1 hW.1 p rfl hdim P.genericPoint
    rwa [P.coheight_genericPoint] at this
  have h2 : Order.coheight (p P.genericPoint) ≤ 1 := by
    by_contra! h2
    exact hP (MMP.Fourfold.Oai4C1.Negativity.isExceptionalPrimeDivisor_of_two_le_coheight hY p hW
      hp P (Order.add_one_le_of_lt h2))
  have hco : Order.coheight (p P.genericPoint) = 1 := le_antisymm h2 h1
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- A divisor over a normal variety is exceptional exactly when its center has codimension at
least two. -/
private theorem divisorOver_isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
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
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- Valuations over `X` of prime divisors of models `π : Y' ⟶ Y`, `h : Y ⟶ X`, with
`π(η_F) = η_G`, agree. -/
private theorem valuation_eq_of_map_genericPoint_eq {Y Y' : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {h : Y ⟶ X} (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h)
    {π : Y' ⟶ Y} (hπ : IsBirationalMorphism π) (hY' : IsNormalVariety ℂ ((π ≫ h) ≫ sX))
    (hπh : IsBirationalMorphism (π ≫ h)) (F : MMP.Mori.PrimeDivisor Y')
    (G : MMP.Mori.PrimeDivisor Y) (hFG : π F.genericPoint = G.genericPoint) :
    (⟨Y', π ≫ h, hY', hπh, F⟩ : DivisorOver ℂ sX).valuation =
      (⟨Y, h, hY, hh, G⟩ : DivisorOver ℂ sX).valuation := by
  haveI := hh.isDominant
  haveI := hπ.isDominant
  haveI := hπh.isDominant
  have hval := MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint π
    hπ.functionFieldMap_bijective.2 F G hFG
  refine Valuation.ext fun t => ?_
  change F.valuationOver (π ≫ h) t = G.valuationOver h t
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    ← MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply π h rfl t,
    ← PrimeDivisor.valuationOver_apply, hval]

/-- Conversely, equal valuations over `X` force `π(η_F) = η_G`. -/
private theorem map_genericPoint_eq_of_valuation_eq {Y Y' : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    {h : Y ⟶ X} (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h)
    {π : Y' ⟶ Y} (hπ : IsBirationalMorphism π) (hY' : IsNormalVariety ℂ ((π ≫ h) ≫ sX))
    (hπh : IsBirationalMorphism (π ≫ h)) (F : MMP.Mori.PrimeDivisor Y')
    (G : MMP.Mori.PrimeDivisor Y)
    (hv : (⟨Y', π ≫ h, hY', hπh, F⟩ : DivisorOver ℂ sX).valuation =
      (⟨Y, h, hY, hh, G⟩ : DivisorOver ℂ sX).valuation) :
    π F.genericPoint = G.genericPoint := by
  haveI := hh.isDominant
  haveI := hπ.isDominant
  haveI := hπh.isDominant
  have hW : IsNormalVariety ℂ (π ≫ h ≫ sX) := by rw [← Category.assoc]; exact hY'
  have hv' : (⟨Y', π, hW, hπ, F⟩ : DivisorOver ℂ (h ≫ sX)).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hY G).valuation := by
    refine Valuation.ext fun t => ?_
    obtain ⟨s, rfl⟩ := hh.functionFieldMap_bijective.2 t
    have h1 := congrArg (fun v : Valuation X.functionField ℤᵐ⁰ => v s) hv
    change F.valuationOver (π ≫ h) s = G.valuationOver h s at h1
    change F.valuationOver π (functionFieldMap h s) =
      G.valuationOver (𝟙 Y) (functionFieldMap h s)
    rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
      ← MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply π h rfl s] at *
    rw [functionFieldMap_id_apply]
    exact h1
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv'

/-- Relative nefness only depends on the structure morphism through its value. -/
private theorem isRelativelyNef_congr {Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    {s s' : Y ⟶ Spec (.of ℂ)} [QuasiCompact s] [QuasiCompact s'] (hs : s = s') {f : Y ⟶ Z}
    {D : RDivisor Y} (h : MMP.Flips.IsRelativelyNef ℂ s f D) :
    MMP.Flips.IsRelativelyNef ℂ s' f D := by
  subst hs
  exact h

/-- A prime divisor exceptional over the base of a proper birational morphism maps to a point of
coheight at least two. -/
private theorem two_le_coheight_of_isExceptionalPrimeDivisor {W Y : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] [CompactSpace Y] {p : W ⟶ Y} {P : MMP.Mori.PrimeDivisor W}
    (hP : MMP.Flips.IsExceptionalPrimeDivisor sY p P) :
    2 ≤ Order.coheight (p P.genericPoint) := by
  obtain ⟨_, _, _, hexc⟩ := hP
  obtain ⟨n, hYdim⟩ := MMP.Fourfold.Oai4C1.Negativity.exists_topologicalKrullDim_eq_natCast sY
  unfold MMP.Flips.ProperDivisorOver.IsExceptional at hexc
  rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hYdim] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (p P.genericPoint)
  rw [hYdim] at hd
  exact (MMP.Fourfold.Oai4C1.Negativity.withBot_add_two_le_iff hd).mp hexc

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 3)
    (f : Y ⟶ X) (hf : IsBirationalMorphism f) {ω : RationalPluriForms sX 3 1} (hω : ω ≠ 0) :
    haveI := hf.isDominant
    pullbackRationalPluriForms sX f ω ≠ 0 := by
  haveI := hf.isDominant
  exact MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero f
    hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdim) hω

section DisjointTransforms

universe u

open CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor

/-- A projective morphism (in the sense of `Proj` of a graded algebra) onto a scheme which is
H-projective over a field is H-projective. -/
private theorem isProjectiveMorphism_of_isProjective' {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (hsZ : IsProjectiveMorphism sZ) (f : Y ⟶ Z) (hf : IsProjective f) :
    IsProjectiveMorphism f := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sZ _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hsZ).1)
  haveI := hL
  exact isProjectiveMorphism_of_isProjective f L hLa hf

/-- The support of the birational transform `f⁻¹_* D`, or `∅` when it is undefined. -/
private noncomputable def tsupp {X Y : Scheme.{u}} (f : Y ⟶ X) (D : MMP.Mori.PrimeDivisor X) :
    Set Y :=
  ((inverseTransformPrimeDivisor f D).map fun E => (E.support : Set Y)).getD ∅

private theorem tsupp_eq {X Y : Scheme.{u}} {f : Y ⟶ X} {D : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : inverseTransformPrimeDivisor f D = some E) :
    tsupp f D = E.support := by
  simp [tsupp, h]

/-- The number of irreducible components of the pairwise intersections of the transforms. -/
private noncomputable def measure {X Y : Scheme.{u}} (𝒟 : Finset (MMP.Mori.PrimeDivisor X))
    (f : Y ⟶ X) : ℕ :=
  ∑ p ∈ 𝒟.offDiag, (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard

/-- A point lies on a prime divisor exactly when it specializes its generic point. -/
private theorem mem_support_iff_specializes {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y)
    {x : Y} : x ∈ (E.support : Set Y) ↔ E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

private theorem genericPoint_mem_support {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y) :
    E.genericPoint ∈ (E.support : Set Y) :=
  (mem_support_iff_specializes E).2 le_rfl

/-- A variety over a field is a Noetherian topological space. -/
private theorem noetherianSpace_of_isVariety {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : MMP.Mori.IsVariety k s) : NoetherianSpace Y := by
  have : LocallyOfFiniteType s := h.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  infer_instance

private theorem mem_support_sum_single {Y : Scheme.{u}} {s : Finset (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} (hF : F ∈ s) :
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support := by
  classical
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hF]

/-- The prime divisors of the support of `Δ` lie in `Supp Δ`. -/
private theorem support_subset_supp_of_mem {X : Scheme.{u}} {Δ : RDivisor X}
    {D : MMP.Mori.PrimeDivisor X} (hD : D ∈ Δ.support) :
    (D.support : Set X) ⊆ Δ.supp :=
  DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hD)

/-- For a log resolution `f` of `(X, Δ)` and a family `s` of prime divisors whose union is
`Ex(f) ∪ f⁻¹(Supp Δ)`, the transform of a component of `Δ` belongs to `s`. -/
private theorem mem_of_iUnion_eq {X Y : Scheme.{u}} {Δ : RDivisor X} {f : Y ⟶ X}
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hs : (⋃ F ∈ s, (F.support : Set Y)) =
      ↑(exceptionalSet f ⊔ Δ.supp.preimage f.continuous))
    {D : MMP.Mori.PrimeDivisor X} (hD : D ∈ Δ.support) {E : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E) : E ∈ s := by
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hE).1
  have hmem : E.genericPoint ∈ ⋃ F ∈ s, (F.support : Set Y) := by
    rw [hs]
    right
    change f E.genericPoint ∈ (Δ.supp : Set X)
    rw [hη]
    exact support_subset_supp_of_mem hD (genericPoint_mem_support D)
  obtain ⟨F, hF, hEF⟩ := Set.mem_iUnion₂.mp hmem
  have := F.eq_genericPoint_of_mem_support hEF E.coheight_genericPoint
  rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_injective this]

/-- For a log resolution `f` of `(X, Δ)`, the transform of a component of `Δ` is a component of
the snc divisor `Ex(f) ∪ f⁻¹(Supp Δ)`. -/
private theorem exists_snc_family {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {Δ : RDivisor X} {f : Y ⟶ X}
    (hf : IsLogResolution sX Δ f) {D : MMP.Mori.PrimeDivisor X}
    (hD : D ∈ Δ.support) {E : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y),
      (⋃ F ∈ s, (F.support : Set Y)) =
        ↑(exceptionalSet f ⊔ Δ.supp.preimage f.continuous) ∧
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ F ∈ s, Finsupp.single F (1 : ℤ)) ∧ E ∈ s := by
  rcases hf.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · have := mem_of_iUnion_eq (s := ∅) (by rw [h0]; simp) hD hE
    simp at this
  exact ⟨s, hs, hsnc, mem_of_iUnion_eq hs hD hE⟩

/-- If every element of `S` is related to some element of the finite set `T`, and no two
distinct elements of `S` are related to a common one, then `#S ≤ #T`. -/
private theorem ncard_le_of_rel {α β : Type*} {S : Set α} {T : Set β} (hT : T.Finite)
    (R : α → β → Prop) (hex : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (huniq : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') :
    S.ncard ≤ T.ncard := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  obtain ⟨b₀, -, -⟩ := hex a₀ ha₀
  haveI : Nonempty β := ⟨b₀⟩
  choose! φ hφT hφR using hex
  exact Set.ncard_le_ncard_of_injOn φ hφT
    (fun a ha a' ha' he => huniq a ha a' ha' _ (hφT a ha) (hφR a ha) (he ▸ hφR a' ha')) hT

/-- The strict version of `ncard_le_of_rel`, when some element of `T` is related to nothing. -/
private theorem ncard_lt_of_rel {α β : Type*} {S : Set α} {T : Set β} (hT : T.Finite)
    (R : α → β → Prop) (hex : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (huniq : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') {b₀ : β} (hb₀ : b₀ ∈ T)
    (hR : ∀ a ∈ S, ¬ R a b₀) :
    S.ncard < T.ncard := by
  refine lt_of_le_of_lt (ncard_le_of_rel (hT.diff) R (fun a ha => ?_)
    (fun a ha a' ha' b hb => huniq a ha a' ha' b hb.1)) (Set.ncard_diff_singleton_lt_of_mem hb₀ hT)
  obtain ⟨b, hb, hab⟩ := hex a ha
  exact ⟨b, ⟨hb, fun h => hR a ha (Set.mem_singleton_iff.mp h ▸ hab)⟩, hab⟩

/-- An irreducible component of a closed set is closed. -/
private theorem isClosed_of_mem_componentsOf {T : Type*} [TopologicalSpace T] {D C : Set T}
    (hD : IsClosed D) (hC : C ∈ componentsOf D) : IsClosed C :=
  closure_subset_iff_isClosed.mp
    (hC.2 ⟨hC.1.1.closure, closure_minimal hC.1.2 hD⟩ subset_closure)

/-- An irreducible component of a closed subset of a scheme has a generic point. -/
private theorem exists_isGenericPoint_of_mem_componentsOf {Y : Scheme.{u}} {D C : Set Y}
    (hD : IsClosed D) (hC : C ∈ componentsOf D) : ∃ ζ, IsGenericPoint ζ C := by
  have h := hC.1.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_componentsOf hD hC).closure_eq] at h
  exact ⟨_, h⟩

/-- A point of the biregular locus of `h` lies in the image of `h`. -/
private theorem exists_eq_of_mem_biregularLocus' {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) {y : Y}
    (hy : y ∈ biregularLocus h) : ∃ x, h x = y := by
  set V := biregularLocus h
  have : IsIso (h ∣_ V) := isBiregular_biregularLocus h
  obtain ⟨p, hp⟩ := (asIso (h ∣_ V)).hom.homeomorph.surjective ⟨y, hy⟩
  refine ⟨(h ⁻¹ᵁ V).ι p, ?_⟩
  have e : V.ι ((h ∣_ V) p) = h ((h ⁻¹ᵁ V).ι p) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  rw [← e]
  exact congrArg Subtype.val hp

/-- `h` maps a birational transform `h⁻¹_* A` into `A`. -/
private theorem map_mem_of_inverseTransform {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {A : MMP.Mori.PrimeDivisor Y} {A' : MMP.Mori.PrimeDivisor Y'}
    (hA : inverseTransformPrimeDivisor h A = some A') {x : Y'}
    (hx : x ∈ (A'.support : Set Y')) : h x ∈ (A.support : Set Y) := by
  rw [mem_support_iff_specializes] at hx ⊢
  have := h.base.hom.map_specializes hx
  rwa [(MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hA).1] at this

/-- Over the biregular locus of `h`, the preimage of `A` lies in `h⁻¹_* A`. -/
private theorem mem_of_inverseTransform {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {A : MMP.Mori.PrimeDivisor Y} {A' : MMP.Mori.PrimeDivisor Y'}
    (hA : inverseTransformPrimeDivisor h A = some A') {x : Y'}
    (hx : h x ∈ (A.support : Set Y)) (hxV : h x ∈ biregularLocus h) :
    x ∈ (A'.support : Set Y') := by
  obtain ⟨h1, h2⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hA
  rw [mem_support_iff_specializes] at hx ⊢
  exact MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h h2 hxV (h1 ▸ hx)

/-- **The components of an intersection of transforms lie over the old ones.** Let
`h : Y' ⟶ Y` be an isomorphism over the complement of a closed set `W` with
`h⁻¹(W) = E`, and let `A' = h⁻¹_* A`, `B' = h⁻¹_* B`. If no irreducible component of `A' ∩ B'`
has its generic point on `E`, then `A' ∩ B'` has at most as many irreducible components as
`A ∩ B`, and strictly fewer when `W` is one of the components of `A ∩ B`. -/
private theorem ncard_componentsOf_inter_le {Y Y' : Scheme.{u}} [NoetherianSpace Y]
    (h : Y' ⟶ Y) {W : Set Y} (hWcl : IsClosed W) {E : Set Y'} (hE : E = h ⁻¹' W)
    (hV : ∀ y ∉ W, y ∈ biregularLocus h) {A B : MMP.Mori.PrimeDivisor Y}
    {A' B' : MMP.Mori.PrimeDivisor Y'} (hA : inverseTransformPrimeDivisor h A = some A')
    (hB : inverseTransformPrimeDivisor h B = some B')
    (hgen : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support), ∀ ζ, IsGenericPoint ζ C →
      ζ ∉ E) :
    (componentsOf ((A'.support : Set Y') ∩ B'.support)).ncard ≤
      (componentsOf ((A.support : Set Y) ∩ B.support)).ncard ∧
    (W ∈ componentsOf ((A.support : Set Y) ∩ B.support) →
      (componentsOf ((A'.support : Set Y') ∩ B'.support)).ncard <
        (componentsOf ((A.support : Set Y) ∩ B.support)).ncard) := by
  have hcl : IsClosed ((A.support : Set Y) ∩ B.support) :=
    A.idealSheaf.support.isClosed.inter B.idealSheaf.support.isClosed
  have hcl' : IsClosed ((A'.support : Set Y') ∩ B'.support) :=
    A'.idealSheaf.support.isClosed.inter B'.idealSheaf.support.isClosed
  have hfin := finite_componentsOf hcl
  let R : Set Y' → Set Y → Prop := fun C K => ∃ ζ, IsGenericPoint ζ C ∧ h ζ ∈ K
  have hex : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∃ K ∈ componentsOf ((A.support : Set Y) ∩ B.support), R C K := by
    intro C hC
    obtain ⟨ζ, hζ⟩ := exists_isGenericPoint_of_mem_componentsOf hcl' hC
    have hζC : ζ ∈ (A'.support : Set Y') ∩ B'.support := hC.1.2 hζ.mem
    obtain ⟨K, hK, hζK⟩ := exists_mem_componentsOf (D := (A.support : Set Y) ∩ B.support)
      ⟨map_mem_of_inverseTransform hA hζC.1, map_mem_of_inverseTransform hB hζC.2⟩
    exact ⟨K, hK, ζ, hζ, hζK⟩
  have huniq : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∀ C' ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∀ K ∈ componentsOf ((A.support : Set Y) ∩ B.support), R C K → R C' K → C = C' := by
    intro C hC C' hC' K hK ⟨ζ, hζ, hζK⟩ ⟨ζ', hζ', hζ'K⟩
    obtain ⟨κ, hκ⟩ := exists_isGenericPoint_of_mem_componentsOf hcl hK
    have hκA : κ ∈ (A.support : Set Y) ∩ B.support := hK.1.2 hκ.mem
    -- the generic point of `K` lies off `W`
    have hζW : h ζ ∉ W := fun hw => hgen C hC ζ hζ (hE ▸ hw)
    have hζ'W : h ζ' ∉ W := fun hw => hgen C' hC' ζ' hζ' (hE ▸ hw)
    have hκζ : κ ⤳ h ζ := hκ.specializes hζK
    have hκζ' : κ ⤳ h ζ' := hκ.specializes hζ'K
    have hκW : κ ∉ W := fun hw => hζW (hκζ.mem_closed hWcl hw)
    obtain ⟨ξ, hξ⟩ := exists_eq_of_mem_biregularLocus' h (hV κ hκW)
    have hξV : h ξ ∈ biregularLocus h := hξ ▸ hV κ hκW
    have hξζ : ξ ⤳ ζ := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h hξV
      (hV _ hζW) (hξ ▸ hκζ)
    have hξζ' : ξ ⤳ ζ' := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h hξV
      (hV _ hζ'W) (hξ ▸ hκζ')
    have hξAB : ξ ∈ (A'.support : Set Y') ∩ B'.support :=
      ⟨mem_of_inverseTransform hA (hξ ▸ hκA.1) hξV, mem_of_inverseTransform hB (hξ ▸ hκA.2) hξV⟩
    have hsub : closure {ξ} ⊆ (A'.support : Set Y') ∩ B'.support :=
      closure_minimal (Set.singleton_subset_iff.mpr hξAB) hcl'
    have key : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support), ∀ ζ,
        IsGenericPoint ζ C → ξ ⤳ ζ → C = closure {ξ} := by
      intro C hC ζ hζ hξζ
      have hle : C ⊆ closure {ξ} := by
        rw [← hζ.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξζ))
          isClosed_closure
      exact le_antisymm hle (hC.2 ⟨isIrreducible_singleton.closure, hsub⟩ hle)
    rw [key C hC ζ hζ hξζ, key C' hC' ζ' hζ' hξζ']
  refine ⟨ncard_le_of_rel hfin R hex huniq, fun hW => ncard_lt_of_rel hfin R hex huniq hW ?_⟩
  rintro C hC ⟨ζ, hζ, hζW⟩
  exact hgen C hC ζ hζ (hE ▸ hζW)

/-- The generic point of a closed irreducible set of codimension `n` has coheight `n`. -/
private theorem coheight_eq_of_isGenericPoint {Y : Scheme.{u}} {ζ : Y} {C : Set Y}
    (hζ : IsGenericPoint ζ C) {n : ℕ} (h : closedsCodimension (Closeds.closure C) = n) :
    Order.coheight ζ = n := by
  rw [← MMP.Flips.codimension_closureSingleton, ← closedsCodimension_coe, ← h]
  congr 1
  ext1
  rw [Closeds.coe_closure, ← hζ.def, closure_closure]
  rfl

/-- Distinct prime divisors have distinct birational transforms. -/
private theorem inverseTransformPrimeDivisor_ne {X Y : Scheme.{u}} {f : Y ⟶ X}
    {D D' : MMP.Mori.PrimeDivisor X} {E E' : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E)
    (hE' : inverseTransformPrimeDivisor f D' = some E') (hD : D ≠ D') : E ≠ E' := by
  rintro rfl
  exact hD (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE).1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1))

/-- **The exceptional set of a blow-up-like morphism.** If `h : Y' ⟶ Y` is an isomorphism off
`W`, the preimage `h⁻¹(W)` is a prime divisor `E`, and the generic point of `E` maps to a point
of coheight two, then `Ex(h) = E`. -/
private theorem coe_exceptionalSet_eq_support {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) {W : Set Y}
    {E : MMP.Mori.PrimeDivisor Y'} (hE : (E.support : Set Y') = h ⁻¹' W)
    (hV : ∀ y ∉ W, y ∈ biregularLocus h) (hcoh : Order.coheight (h E.genericPoint) = 2) :
    (exceptionalSet h : Set Y') = E.support := by
  refine subset_antisymm (fun y hy => hE ▸ not_not.mp fun hyW => hy (hV _ hyW)) fun y hy => ?_
  have hεEx : E.genericPoint ∈ (exceptionalSet h : Set Y') := fun hεV => by
    have := MMP.Positivity.coheight_map_of_mem_biregularLocus h hεV
    rw [hcoh, E.coheight_genericPoint] at this
    exact absurd this (by decide)
  exact ((mem_support_iff_specializes E).mp hy).mem_closed (exceptionalSet h).isClosed hεEx

/-- **No codimension-two stratum lies in a third component.** Let `∑_{F ∈ s} F` be an snc
divisor on a smooth variety and `A`, `B`, `E` three distinct members of `s`. Then the generic
point of an irreducible component of `A ∩ B`, which has codimension two, does not lie on `E`:
at a point of `A ∩ B ∩ E` the local ring has dimension at least three. -/
private theorem genericPoint_notMem_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (hsm : IsSmoothScheme sY) (s : Finset (MMP.Mori.PrimeDivisor Y))
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ F ∈ s, Finsupp.single F (1 : ℤ)))
    {A B E : MMP.Mori.PrimeDivisor Y} (hA : A ∈ s) (hB : B ∈ s) (hE : E ∈ s)
    (hAB : A ≠ B) (hAE : A ≠ E) (hBE : B ≠ E)
    {C : Set Y} (hC : C ∈ componentsOf ((A.support : Set Y) ∩ B.support)) {ζ : Y}
    (hζ : IsGenericPoint ζ C) : ζ ∉ (E.support : Set Y) := by
  classical
  intro hζE
  let S : s → MMP.Mori.PrimeDivisor Y := Subtype.val
  have hSNC : DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)) := by
    rwa [Finset.sum_coe_sort s (fun P => Finsupp.single P (1 : ℤ))]
  let ja : s := ⟨A, hA⟩
  let jb : s := ⟨B, hB⟩
  let J : Finset s := {ja, jb}
  have hjab : ja ≠ jb := fun h => hAB (congrArg Subtype.val h)
  have hJ : J.card = 2 := Finset.card_pair hjab
  have hinter : (⋂ j ∈ J, ((S j).support : Set Y)) = (A.support : Set Y) ∩ B.support := by
    simp [J, S, ja, jb]
  obtain ⟨-, hcodim, -⟩ := blowUp_snc_stratum sY hY hsm S Subtype.val_injective hSNC J hJ.ge
    ⟨C, hinter ▸ hC⟩
  have hcoh : Order.coheight ζ = 2 := coheight_eq_of_isGenericPoint hζ (by rw [hcodim, hJ])
  obtain ⟨n, z, j, hz, hj, -⟩ := hsnc.2 ζ
  have hn : n = 2 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  have hζAB : ζ ∈ (A.support : Set Y) ∩ B.support := hC.1.2 hζ.mem
  let a : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨A, mem_support_sum_single hA, hζAB.1⟩
  let b : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨B, mem_support_sum_single hB, hζAB.2⟩
  let e : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨E, mem_support_sum_single hE, hζE⟩
  have hab : j a ≠ j b := fun h => hAB (congrArg Subtype.val (hj h))
  have hae : j a ≠ j e := fun h => hAE (congrArg Subtype.val (hj h))
  have hbe : j b ≠ j e := fun h => hBE (congrArg Subtype.val (hj h))
  have h1 := (j a).isLt
  have h2 := (j b).isLt
  have h3 := (j e).isLt
  have hab' := Fin.val_ne_of_ne hab
  have hae' := Fin.val_ne_of_ne hae
  have hbe' := Fin.val_ne_of_ne hbe
  omega

/-- The inductive invariant: `f` is a log resolution of `(X, Δ)` from a variety, and every
component of `Δ` has a birational transform under `f`. -/
private def Good {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (Δ : RDivisor X) (f : Y ⟶ X) : Prop :=
  IsLogResolution sX Δ f ∧ MMP.Mori.IsVariety k (f ≫ sX) ∧
    (∀ D ∈ Δ.support, ∃ E, inverseTransformPrimeDivisor f D = some E) ∧ IsProjectiveMorphism f

private theorem good_initial {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (Δ : RDivisor X) (hX : IsNormalVariety k sX) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Good sX Δ f := by
  obtain ⟨Y, g, hg, hgp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hX Δ
  have hYv : MMP.Mori.IsVariety k (g ≫ sX) :=
    (hg.toIsSmoothResolution.isNormalVariety hX).1.1
  have : IsProper g := hg.isProper
  refine ⟨Y, g, hg, hYv, fun D _ => ?_, hgp⟩
  have hV : D.genericPoint ∈ biregularLocus g := by
    by_contra hV
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      (two_le_closedsCodimension_compl_biregularLocus sX g (hY := hX.1) (hX := hYv) hg.isBirationalMorphism)
      D.genericPoint hV
    rw [D.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨E, hE, -⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some D hV
  exact ⟨E, hE⟩

private theorem exists_step {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (Δ : RDivisor X) (hsX : IsProjectiveMorphism sX) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Good sX Δ f)
    (hpos : 0 < measure Δ.support f) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Good sX Δ f' ∧
      measure Δ.support f' < measure Δ.support f := by
  classical
  obtain ⟨hfl, hYv, hτ, hfp⟩ := hf
  haveI := noetherianSpace_of_isVariety hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsProper f := hfl.isProper
  have hgen : ∀ {D : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y},
      inverseTransformPrimeDivisor f D = some E →
        f E.genericPoint = D.genericPoint ∧ f E.genericPoint ∈ biregularLocus f :=
    fun h => MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h
  -- a pair of transforms that meet, and a component `W` of their intersection
  obtain ⟨⟨D₁, D₂⟩, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨hD₁, hD₂, hD₁₂⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨E₁, hE₁⟩ := hτ D₁ hD₁
  obtain ⟨E₂, hE₂⟩ := hτ D₂ hD₂
  simp only [tsupp_eq hE₁, tsupp_eq hE₂] at hne
  obtain ⟨W, hW⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨s, hs, hsnc, hE₁s⟩ := exists_snc_family hfl hD₁ hE₁
  have hE₂s := mem_of_iUnion_eq hs hD₂ hE₂
  have hE₁₂ : E₁ ≠ E₂ := inverseTransformPrimeDivisor_ne hE₁ hE₂ hD₁₂
  have hcl₁₂ : IsClosed ((E₁.support : Set Y) ∩ E₂.support) :=
    E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed
  have hWcl : IsClosed W := isClosed_of_mem_componentsOf hcl₁₂ hW
  -- the blow-up of `W`
  let S : s → MMP.Mori.PrimeDivisor Y := Subtype.val
  have hSNC : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ j, Finsupp.single (S j) (1 : ℤ)) := by
    rwa [Finset.sum_coe_sort s (fun P => Finsupp.single P (1 : ℤ))]
  let j₁ : s := ⟨E₁, hE₁s⟩
  let j₂ : s := ⟨E₂, hE₂s⟩
  let J : Finset s := {j₁, j₂}
  have hj₁₂ : j₁ ≠ j₂ := fun h => hE₁₂ (congrArg Subtype.val h)
  have hJ : J.card = 2 := Finset.card_pair hj₁₂
  have hinter : (⋂ j ∈ J, ((S j).support : Set Y)) = (E₁.support : Set Y) ∩ E₂.support := by
    simp [J, S, j₁, j₂]
  let Wc : componentsOf (⋂ j ∈ J, ((S j).support : Set Y)) := ⟨W, hinter ▸ hW⟩
  have key := blowUp_snc_stratum (f ≫ sX) hYv hfl.isSmoothScheme S Subtype.val_injective hSNC J
    hJ.ge Wc
  dsimp only at key
  have hIsupp : ((componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) Wc).support : Set Y) =
      W := by
    change ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure W)).support : Set Y) = W
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hWcl.closure_eq]
  generalize componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) Wc = I at key hIsupp
  obtain ⟨-, hcodim, hBsm, hiso, E, S', hEI, -, hS'tr, hS'inj, hS'E, hsnc', himg, -⟩ := key
  set h := blowUpToBase I with hhdef
  have hEsupp : (E.support : Set (blowUp I)) = h ⁻¹' W := by
    rw [← hIsupp]
    change ((E.idealSheaf).support : Set (blowUp I)) = _
    rw [hEI, Scheme.IdealSheafData.support_comap]
    rfl
  have hVh : ∀ y ∉ W, y ∈ biregularLocus h := fun y hy =>
    le_biregularLocus hiso (show y ∉ (I.support : Set Y) by rwa [hIsupp])
  have hirr : IsIrreducible (I.support : Set Y) := hIsupp ▸ hW.1.1
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    have e : (⟨((⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) : Set Y),
        (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y).isClosed⟩ : Closeds Y) =
        Closeds.closure W := by
      ext1
      exact hIsupp.trans hWcl.closure_eq.symm
    rw [← closedsCodimension_coe, e, hcodim, hJ]
    norm_num
  haveI : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have hbir : IsBirationalMorphism h :=
    MMP.Threefold.Resolution.isBirationalMorphism_blowUpToBase I hirr hc1
  have hI0 := MMP.Threefold.Resolution.ne_bot_of_one_le_codimension I hirr hc1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYv
  obtain ⟨hY'v, hproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (f ≫ sX) I hI0
  haveI : IsProper h := hproj.isProper
  -- the generic point of the exceptional divisor lies over the generic point of `W`
  have hj₁J : j₁ ∈ J := by simp [J]
  have hεW : closure {h E.genericPoint} = W := by
    apply subset_antisymm
    · refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hWcl
      have := genericPoint_mem_support E
      rwa [hEsupp] at this
    · intro w hw
      have hw' : w ∈ (Wc : Set Y) := hw
      rw [← himg j₁ hj₁J] at hw'
      obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hw'
      exact specializes_iff_mem_closure.mp
        (h.base.hom.map_specializes ((mem_support_iff_specializes E).mp hy))
  have hcohε : Order.coheight (h E.genericPoint) = 2 :=
    coheight_eq_of_isGenericPoint hεW (by rw [hcodim, hJ])
  have hExh : (exceptionalSet h : Set (blowUp I)) = E.support :=
    coe_exceptionalSet_eq_support h hEsupp hVh hcohε
  -- the boundary `Δ' = ∑_{T ∈ s} T` on `Y`
  let Δ' : RDivisor Y := ∑ T ∈ s, Finsupp.single T (1 : ℝ)
  have hsuppΔ' : (Δ'.supp : Set Y) = ⋃ T ∈ s, (T.support : Set Y) := by
    have : Δ'.support = s := by
      ext F
      simp [Δ', Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [DivisorWithCoeffs.coe_supp, this]
  -- the new snc divisor
  let s' : Finset (MMP.Mori.PrimeDivisor (blowUp I)) := insert E (Finset.univ.image S')
  have hEimg : E ∉ Finset.univ.image S' := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hS'E
  have hS's : ∀ j, S' j ∈ s' := fun j =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hEs' : E ∈ s' := Finset.mem_insert_self _ _
  have hsnc's : DivisorWithCoeffs.IsSNC (h ≫ f ≫ sX)
      (∑ F ∈ s', Finsupp.single F (1 : ℤ)) := by
    have : (∑ P ∈ s', Finsupp.single P (1 : ℤ) : Divisor (blowUp I)) =
        Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ) := by
      rw [Finset.sum_insert hEimg, Finset.sum_image fun i _ j _ h => hS'inj h]
    rwa [this]
  have hunion : (⋃ F ∈ s', (F.support : Set (blowUp I))) =
      ↑(exceptionalSet h ⊔ Δ'.supp.preimage h.continuous) := by
    ext y
    rw [Set.mem_iUnion₂]
    change (∃ F, ∃ (_ : F ∈ s'), y ∈ (F.support : Set (blowUp I))) ↔
      y ∈ (exceptionalSet h : Set (blowUp I)) ∨ h y ∈ (Δ'.supp : Set Y)
    rw [hExh, hsuppΔ']
    constructor
    · rintro ⟨F, hF, hyF⟩
      rcases Finset.mem_insert.mp hF with rfl | hF
      · exact Or.inl hyF
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hF
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨j.1, j.2, map_mem_of_inverseTransform (hS'tr j) hyF⟩)
    · rintro (hy | hy)
      · exact ⟨E, hEs', hy⟩
      · obtain ⟨T, hT, hyT⟩ := Set.mem_iUnion₂.mp hy
        by_cases hyE : y ∈ (E.support : Set (blowUp I))
        · exact ⟨E, hEs', hyE⟩
        · have hyW : h y ∉ W := fun hw => hyE (hEsupp ▸ hw)
          exact ⟨S' ⟨T, hT⟩, hS's _,
            mem_of_inverseTransform (hS'tr ⟨T, hT⟩) hyT (hVh _ hyW)⟩
  -- `h` is a log resolution of `(Y, Δ')`
  have hlogh : IsLogResolution (f ≫ sX) Δ' h := by
    refine ⟨⟨inferInstance, hbir, hBsm⟩, ?_, Or.inr ⟨s', hunion, hsnc's⟩⟩
    intro W' hW'
    let EI := IrreducibleCloseds.closureSingleton E.genericPoint
    have hEI : (EI : Set (blowUp I)) = E.support :=
      (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
    have h1 : (W' : Set (blowUp I)) ⊆ E.support := hExh ▸ hW'.1
    have h2 : EI ≤ W' := hW'.2 (show (EI : Set (blowUp I)) ⊆ exceptionalSet h by
      rw [hEI, ← hExh]) (show (W' : Set (blowUp I)) ⊆ EI by rw [hEI]; exact h1)
    have h3 : W' ≤ EI := fun x hx => by
      rw [← SetLike.mem_coe, hEI]; exact h1 hx
    rw [le_antisymm h3 h2]
    exact E.codimension_one
  have hΔ'le : exceptionalSet f ⊔ Δ.supp.preimage f.continuous ≤
      Δ'.supp := by
    intro y hy
    rw [← SetLike.mem_coe, hsuppΔ', hs]
    exact hy
  -- `h ≫ f` is an isomorphism over `V_f ∖ f(W)`
  let V : X.Opens := biregularLocus f ⊓ ⟨(f '' W)ᶜ, (f.isClosedMap W hWcl).isOpen_compl⟩
  have hVbir : IsBiregular (h ≫ f) V := by
    unfold IsBiregular
    rw [morphismRestrict_comp]
    have h1 : IsIso (f ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have h2 : IsIso (h ∣_ f ⁻¹ᵁ V) := isBiregular_iff_le_biregularLocus.mpr
      (fun y hy => hVh y (fun hyW => hy.2 ⟨y, hyW, rfl⟩))
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1
  -- the transforms under `h ≫ f`
  have htr : ∀ D ∈ Δ.support, ∀ A, inverseTransformPrimeDivisor f D = some A → ∀ hA : A ∈ s,
      inverseTransformPrimeDivisor (h ≫ f) D = some (S' ⟨A, hA⟩) := by
    intro D hD A hA hAs
    have hηD : D.genericPoint ∈ V := by
      refine ⟨(hgen hA).1 ▸ (hgen hA).2, ?_⟩
      rintro ⟨w, hwW, hw⟩
      have hwV : f w ∈ biregularLocus f := hw ▸ (hgen hA).1 ▸ (hgen hA).2
      have hw' : f w = f A.genericPoint := hw.trans (hgen hA).1.symm
      have hwA : w = A.genericPoint := Inseparable.eq <|
        (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hwV (hgen hA).2
          (hw' ▸ le_rfl)).antisymm
        (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f (hgen hA).2 hwV
          (hw' ▸ le_rfl))
      have hAW := hW.1.2 (hwA ▸ hwW)
      have e₁ := E₁.eq_genericPoint_of_mem_support hAW.1 A.coheight_genericPoint
      have e₂ := E₂.eq_genericPoint_of_mem_support hAW.2 A.coheight_genericPoint
      exact hE₁₂ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (e₁.symm.trans e₂))
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        (hS'tr ⟨A, hAs⟩)
    have hη : (h ≫ f) (S' ⟨A, hAs⟩).genericPoint = D.genericPoint := by
      rw [Scheme.Hom.comp_apply, h1]
      exact (hgen hA).1
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
      (hη ▸ le_biregularLocus hVbir hηD)
  -- the invariant holds for `h ≫ f`
  have hgood : Good sX Δ (h ≫ f) := by
    refine ⟨hfl.comp hΔ'le hlogh, ?_, fun D hD => ?_, ?_⟩
    · rwa [Category.assoc]
    · obtain ⟨A, hA⟩ := hτ D hD
      exact ⟨_, htr D hD A hA (mem_of_iUnion_eq hs hD hA)⟩
    · exact (isProjectiveMorphism_of_isProjective' (f ≫ sX) (hfp.comp hsX) h hproj).comp hfp
  refine ⟨blowUp I, h ≫ f, hgood, ?_⟩
  -- the number of components drops
  have hpair : ∀ p ∈ Δ.support.offDiag,
      (componentsOf (tsupp (h ≫ f) p.1 ∩ tsupp (h ≫ f) p.2)).ncard ≤
        (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard ∧
      (p = (D₁, D₂) → (componentsOf (tsupp (h ≫ f) p.1 ∩ tsupp (h ≫ f) p.2)).ncard <
        (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard) := by
    rintro ⟨Da, Db⟩ hpab
    obtain ⟨hDa, hDb, hDab⟩ := Finset.mem_offDiag.mp hpab
    obtain ⟨A, hA⟩ := hτ Da hDa
    obtain ⟨B, hB⟩ := hτ Db hDb
    have hAs := mem_of_iUnion_eq hs hDa hA
    have hBs := mem_of_iUnion_eq hs hDb hB
    have hAB : A ≠ B := inverseTransformPrimeDivisor_ne hA hB hDab
    have hA' := htr Da hDa A hA hAs
    have hB' := htr Db hDb B hB hBs
    simp only [tsupp_eq hA, tsupp_eq hB, tsupp_eq hA', tsupp_eq hB']
    have hneq : S' ⟨A, hAs⟩ ≠ S' ⟨B, hBs⟩ := fun e => hAB (congrArg Subtype.val (hS'inj e))
    obtain ⟨hle, hlt⟩ := ncard_componentsOf_inter_le h hWcl hEsupp hVh (hS'tr ⟨A, hAs⟩)
      (hS'tr ⟨B, hBs⟩) (fun C hC ζ hζ => genericPoint_notMem_of_isSNC (h ≫ f ≫ sX) hY'v hBsm s'
        hsnc's (hS's _) (hS's _) hEs' hneq (hS'E _) (hS'E _) hC hζ)
    refine ⟨hle, fun hp => ?_⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have e₁ : A = E₁ := Option.some_injective _ (hA.symm.trans hE₁)
    have e₂ : B = E₂ := Option.some_injective _ (hB.symm.trans hE₂)
    subst e₁ e₂
    exact hlt hW
  unfold measure
  exact Finset.sum_lt_sum (fun p hp => (hpair p hp).1) ⟨(D₁, D₂), hp, (hpair _ hp).2 rfl⟩

/-- Iterating `exists_step`: some model satisfying the invariant has pairwise disjoint
transforms. -/
private theorem exists_good_measure_eq_zero {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (Δ : RDivisor X) (hsX : IsProjectiveMorphism sX) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Good sX Δ f) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Good sX Δ f' ∧ measure Δ.support f' = 0 := by
  induction hn : measure Δ.support f using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨Y, f, hf, hn⟩
    · obtain ⟨Y', f', hf', hlt⟩ := exists_step sX Δ hsX f hf (hn ▸ hpos)
      exact ih _ (hn ▸ hlt) f' hf' rfl

private theorem final {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (Δ : RDivisor X) {Y : Scheme.{u}} (f : Y ⟶ X) (hf : Good sX Δ f)
    (h0 : measure Δ.support f = 0) :
    IsLogResolution sX Δ f ∧
      (∀ D ∈ Δ.support, ∀ E : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor f D = some E →
        IsSmoothScheme (E.idealSheaf.subschemeι ≫ f ≫ sX)) ∧
      ∀ D ∈ Δ.support, ∀ D' ∈ Δ.support, D ≠ D' → ∀ E E' : MMP.Mori.PrimeDivisor Y,
        inverseTransformPrimeDivisor f D = some E → inverseTransformPrimeDivisor f D' = some E' →
          Disjoint (E.support : Set Y) E'.support := by
  classical
  obtain ⟨hf, hYv, -, -⟩ := hf
  have := noetherianSpace_of_isVariety hYv
  refine ⟨hf, fun D hD E hE => ?_, fun D hD D' hD' hDD' E E' hE hE' => ?_⟩
  · obtain ⟨s, -, hsnc, hEs⟩ := exists_snc_family hf hD hE
    exact hsnc.1 E (mem_support_sum_single hEs)
  · have hterm := (Finset.sum_eq_zero_iff.mp h0) (D, D')
      (Finset.mem_offDiag.mpr ⟨hD, hD', hDD'⟩)
    simp only [tsupp_eq hE, tsupp_eq hE'] at hterm
    have hcl : IsClosed ((E.support : Set Y) ∩ E'.support) :=
      E.idealSheaf.support.isClosed.inter E'.idealSheaf.support.isClosed
    rw [Set.ncard_eq_zero (finite_componentsOf hcl)] at hterm
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
    rwa [hterm] at hW

end DisjointTransforms

/-! ### Log resolutions with disjoint boundary transforms -/

/-- **Projective log resolutions with disjoint boundary transforms.** A normal complex variety
`Y` with an `ℝ`-divisor `D` has a projective log resolution `p : U ⟶ Y` on which the
birational transforms of the components of `D` exist and are pairwise disjoint. -/
private theorem exists_isLogResolution_disjoint {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY)
    (hsY : IsProjectiveMorphism sY) (D : RDivisor Y) :
    ∃ (U : Scheme.{0}) (p : U ⟶ Y), IsProjectiveMorphism p ∧ MMP.Mori.IsLogResolution sY D p ∧
      MMP.Mori.IsVariety ℂ (p ≫ sY) ∧
      (∃ s : Finset (MMP.Mori.PrimeDivisor U),
        DivisorWithCoeffs.IsSNC (p ≫ sY) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) ∧
        ∀ Q ∈ D.support, ∀ P, inverseTransformPrimeDivisor p Q = some P → P ∈ s) ∧
      ∀ Q ∈ D.support, ∀ Q' ∈ D.support, Q ≠ Q' → ∀ P P' : MMP.Mori.PrimeDivisor U,
        inverseTransformPrimeDivisor p Q = some P → inverseTransformPrimeDivisor p Q' = some P' →
          Disjoint (P.support : Set U) P'.support := by
  classical
  obtain ⟨U₀, g, hg⟩ := good_initial sY D hY
  obtain ⟨U, p, hp, h0⟩ := exists_good_measure_eq_zero sY D hsY g hg
  obtain ⟨hlog, -, hdisj⟩ := final sY D p hp h0
  obtain ⟨-, hUv, -, hpp⟩ := hp
  refine ⟨U, p, hpp, hlog, hUv, ?_, hdisj⟩
  rcases hlog.isSNCSubset with h0' | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, fun Q hQ P hP => ?_⟩
    · haveI : Smooth (p ≫ sY) := hlog.isSmoothScheme.smooth
      simpa using DivisorWithCoeffs.isSNC_zero (R := ℤ) (p ≫ sY)
    · exact mem_of_iUnion_eq (s := ∅) (by rw [h0']; simp) hQ hP
  · exact ⟨s, hsnc, fun Q hQ P hP => mem_of_iUnion_eq hs hQ hP⟩

/-! ### Terminal boundaries on smooth varieties -/

open Classical in
/-- Sums over the prime divisors of a finite set, written through `Fin`. -/
private theorem sum_equivFin_mul_single {U : Scheme.{0}} (S : Finset (MMP.Mori.PrimeDivisor U))
    (c : MMP.Mori.PrimeDivisor U → ℝ) (Γ : MMP.Mori.PrimeDivisor U) :
    ∑ i : Fin S.card, c (S.equivFin.symm i) *
        (((Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor U) (1 : ℤ)) Γ : ℤ) : ℝ) =
      if Γ ∈ S then c Γ else 0 := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => c x *
    (((Finsupp.single (x : MMP.Mori.PrimeDivisor U) (1 : ℤ)) Γ : ℤ) : ℝ))]
  rw [Finset.sum_coe_sort S (fun x => c x * (((Finsupp.single x (1 : ℤ)) Γ : ℤ) : ℝ))]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single Γ]
    · simp
    · exact fun b _ hb => by simp [hb]
    · exact fun h' => absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

/-- A positive lower bound for the snc discrepancy formula when no two of the components meet. -/
private theorem zero_lt_inf_snc_bound {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ S, c i < 1) (P Q : ι → ι → Prop)
    (hPQ : ∀ i ∈ S, ∀ j ∈ S, P i j → Q i j → False) :
    (0 : EReal) < (⨅ (i ∈ S) (j ∈ S) (_ : P i j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  obtain ⟨δ, hδ, hδ1, hδc⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i ∈ S, δ ≤ 1 - c i := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨1, one_pos, le_rfl, by simp⟩
    · obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image (fun i => 1 - c i) hS
      exact ⟨min (1 - c i₀) 1, lt_min (sub_pos.mpr (hc i₀ hi₀)) one_pos, min_le_right _ _,
        fun i hi => (min_le_left _ _).trans (hmin i hi)⟩
  refine lt_of_lt_of_le (b := (((δ : ℚ) : ℝ) : EReal))
    (EReal.coe_lt_coe_iff.mpr (by exact_mod_cast hδ)) (le_inf (le_inf ?_ ?_) ?_)
  · exact le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun h1 h2 =>
      (hPQ i hi j hj h1 h2).elim
  · exact le_iInf₂ fun i hi => EReal.coe_le_coe_iff.mpr (by exact_mod_cast hδc i hi)
  · have : (((δ : ℚ) : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by exact_mod_cast hδ1)
    simpa using this

/-- **A valuative bound from orders near the centre.** If `ord_Γ(g) ≥ coeff_Γ(C)` along every
prime divisor `Γ` through the centre of `F`, for a Cartier divisor `C` with pull-back `C'`, then
`v_F(g) ≤ exp (-coeff_F(C'))`. -/
private theorem valuation_le_exp_of_isPullback {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} {F : DivisorOver ℂ sU}
    {C : Divisor U} (hC : C.IsCartier) {g : U.functionField}
    (hg : ∀ Γ : MMP.Mori.PrimeDivisor U, F.f F.E.genericPoint ∈ Γ.support →
      Γ.divisorialValuation g ≤ WithZero.exp (-C.coeff Γ)) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      F.valuation g ≤ WithZero.exp (-C'.coeff F.E) := by
  intro C' hCs hC'
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  set x := F.f F.E.genericPoint with hx
  obtain ⟨V, hxV, φ, hφ⟩ := hC x
  let Z0 : irreducibleComponents U := MMP.Mori.pointComponent x
  set h := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions U) with hhdef
  have hh : h ≠ 0 := (φ.isUnit.map _).ne_zero
  have hcoef := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hC' hφ F.E hxV Z0
  have hordh : ∀ Γ : MMP.Mori.PrimeDivisor U, x ∈ Γ.support →
      U.ord h Γ.genericPoint = C.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ ⟨x, hΓ, hxV⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    rw [show Γ.component = Z0 from
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _]
  have hg' : g * h ^ (-1 : ℤ) ≠ 0 := mul_ne_zero hg0 (zpow_ne_zero _ hh)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor U, x ∈ Γ.support →
      0 ≤ U.ord (g * h ^ (-1 : ℤ)) Γ.genericPoint := by
    intro Γ hΓ
    have h1 := hg Γ hΓ
    rw [Γ.divisorialValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h1
    rw [Scheme.ord_mul hg0 (zpow_ne_zero _ hh), MMP.Mori.ord_zpow _ hh, hordh Γ hΓ]
    omega
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hg' hord
  have hY0 := MMP.Threefold.Mori.Helpers.ord_functionFieldMap_nonneg F hg' r hr
  have hfg : functionFieldMap F.f g ≠ 0 := (map_ne_zero _).mpr hg0
  have hfh : functionFieldMap F.f h ≠ 0 := (map_ne_zero _).mpr hh
  rw [map_mul, map_zpow₀, Scheme.ord_mul hfg (zpow_ne_zero _ hfh), MMP.Mori.ord_zpow _ hfh]
    at hY0
  change F.E.divisorialValuation (functionFieldMap F.f g) ≤ _
  rw [F.E.divisorialValuation_eq_exp_neg_ord hfg, WithZero.exp_le_exp, hcoef, ← hhdef]
  omega

/-- The pull-back of an effective Cartier divisor along a divisor over `U` has a nonnegative
coefficient along it. -/
private theorem coeff_isPullback_nonneg {U : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} {F : DivisorOver ℂ sU} {C : Divisor U}
    (hC : C.IsCartier) (hC0 : ∀ Γ : MMP.Mori.PrimeDivisor U, 0 ≤ C.coeff Γ) :
    haveI := F.isLocallyNoetherian
    haveI := F.isNormal
    ∀ (C' : Divisor F.Y) (hCs : ∀ Z : irreducibleComponents F.Y,
        F.f (componentGenericPoint F.Y Z) ∉ C.supp), C.IsPullback F.f hCs C' →
      0 ≤ C'.coeff F.E := by
  intro C' hCs hC'
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  have hn := hC'.zsmul hC (-1)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp F.f _)
  have h1 := valuation_le_exp_of_isPullback (F := F) (hC.zsmul (-1)) (g := 1) (fun Γ _ => by
      rw [map_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul, neg_one_mul, neg_neg,
        ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hC0 Γ) _ _ hn
  rwa [map_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul, neg_one_mul, neg_neg,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at h1

/-- The log discrepancy of a divisor `E` over a smooth threefold `U` with respect to
`∑_{P ∈ S} c_P P`, through fixed pull-backs: it is affine in the coefficients `c_P`, with
nonnegative slopes `-coeff_E(P')`. -/
private theorem exists_isLogDiscrepancy_sum_single {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} (hUn : IsNormalVariety ℂ sU)
    (hsm : IsSmoothScheme sU) {K : Divisor U} {ω : RationalPluriForms sU 3 1} (hω0 : ω ≠ 0)
    (hK : K.IsCanonicalDivisor sU 3) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    (S : Finset (MMP.Mori.PrimeDivisor U)) (E : DivisorOver ℂ sU) (hE : IsProper E.f) :
    ∃ (k : ℝ) (t : MMP.Mori.PrimeDivisor U → ℝ), (∀ P, 0 ≤ t P) ∧
      ∀ c : MMP.Mori.PrimeDivisor U → ℝ,
        MMP.Intersection.IsLogDiscrepancy sU 3 (∑ P ∈ S, Finsupp.single P (c P)) E
          (k - ∑ P ∈ S, c P * t P) := by
  classical
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sU)
  have hcart : ∀ D : Divisor U, D.IsCartier := isCartier_of_isSmoothScheme hsm
  obtain ⟨K', hK'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hcart K)
  choose P' hP' using fun P : MMP.Mori.PrimeDivisor U =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f
      (hcart (Finsupp.single P (1 : ℤ)))
  refine ⟨1 + (E.ordPullback ω : ℝ) - (K'.coeff E.E : ℝ), fun P => ((P' P).coeff E.E : ℝ),
    fun P => ?_, fun c => ?_⟩
  · show (0 : ℝ) ≤ ((P' P).coeff E.E : ℝ)
    exact_mod_cast coeff_isPullback_nonneg (F := E) (hcart _) (fun Γ => by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
      split_ifs <;> norm_num) _ _ (hP' P)
  set e := S.equivFin
  refine ⟨hUn, hE, ω, hω0, ⟨K, hK, hKω⟩, S.card + 1, Fin.cons 1 (fun j => c (e.symm j)),
    Fin.cons K (fun j => (Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor U) 1 : Divisor U)),
    Fin.cons K' (fun j => P' (e.symm j)), fun i => hcart _, fun Γ => ?_, fun i => ?_, ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul, DivisorWithCoeffs.coeff_apply]
    rw [sum_equivFin_mul_single S c Γ]
    have hKΓ := hKω Γ
    rw [DivisorWithCoeffs.coeff_apply] at hKΓ
    rw [hKΓ]
    congr 1
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  · refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨_, hK'⟩
    · exact ⟨_, hP' _⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
    rw [Equiv.sum_comp e.symm (fun x : S => c x * ((P' x).coeff E.E : ℝ)),
      Finset.sum_coe_sort S (fun x => c x * ((P' x).coeff E.E : ℝ))]
    ring

/-- On a smooth threefold, an effective `ℝ`-divisor with coefficients less than one whose
components are pairwise disjoint and part of an snc divisor is real terminal. -/
private theorem isRealTerminalPair_of_isSNC {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} (hU : MMP.Mori.IsVariety ℂ sU)
    (hsm : IsSmoothScheme sU) (hdim : topologicalKrullDim U = 3)
    (s : Finset (MMP.Mori.PrimeDivisor U))
    (hsnc : DivisorWithCoeffs.IsSNC sU (∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    {C : RDivisor U} (hCs : C.support ⊆ s) (hC0 : ∀ P, 0 ≤ C.coeff P)
    (hC1 : ∀ P, C.coeff P < 1)
    (hdisj : ∀ P ∈ C.support, ∀ P' ∈ C.support, P ≠ P' →
      Disjoint (P.support : Set U) P'.support) :
    IsRealTerminalPair sU C := by
  classical
  have hUn : IsNormalVariety ℂ sU := ⟨hU, inferInstance⟩
  haveI : MMP.Mori.IsVariety ℂ sU := hU
  haveI : LocallyOfFiniteType sU := hU.toLocallyOfFiniteType
  haveI : QuasiCompact sU := hU.toQuasiCompact
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace sU
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sU hsm hdim
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hUn hK
  set S := C.support with hSdef
  have hCS : C = ∑ P ∈ S, Finsupp.single P (C.coeff P) := (Finsupp.sum_single C).symm
  -- rational coefficients `C ≤ q < 1` on the support
  choose q hq1 hq2 using fun P => exists_rat_btwn (hC1 P)
  set Cq : QDivisor U := ∑ P ∈ S, Finsupp.single P (q P) with hCqdef
  have hCqc : ∀ P, Cq.coeff P = if P ∈ S then q P else 0 := by
    intro P
    simp [hCqdef, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply,
      eq_comm]
  have hCqR : QDivisor.toRDivisor Cq = ∑ P ∈ S, Finsupp.single P ((q P : ℚ) : ℝ) := by
    ext P
    rw [QDivisor.coeff_toRDivisor, hCqc]
    by_cases h : P ∈ S <;>
      simp [h, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply,
        eq_comm]
  have hCqsupp : Cq.support ⊆ S := by
    intro P hP
    by_contra hPS
    exact Finsupp.mem_support_iff.mp hP (by rw [← DivisorWithCoeffs.coeff_apply, hCqc,
      if_neg hPS])
  have hSs : (∑ E ∈ S, Finsupp.single E (1 : ℤ) : Divisor U).support ⊆
      (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor U).support := by
    intro P hP
    have hPS : P ∈ S := by
      by_contra hPS
      apply Finsupp.mem_support_iff.mp hP
      simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hPS]
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hCs hPS]
  have hsncS := hsnc.of_support_subset hSs
  -- the terminal inequality
  have hterm : ∀ (n : ℕ) (E : DivisorOver ℂ sU) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sU n C E a → 1 < a := by
    intro n E a hE ha
    obtain ⟨k, t, ht0, hkt⟩ := exists_isLogDiscrepancy_sum_single hUn hsm hω0 hK
      (fun Γ => (hω Γ).symm) S E ha.2.1
    have hkC := hkt (C.coeff ·)
    rw [← hCS] at hkC
    have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hkC
    have hlog₂ : MMP.Intersection.IsLogDiscrepancy sU 3 (QDivisor.toRDivisor Cq) E
        (k - ∑ P ∈ S, ((q P : ℚ) : ℝ) * t P) := hCqR ▸ hkt (fun P => ((q P : ℚ) : ℝ))
    have hPair : MMP.Mori.IsPair sU Cq :=
      ⟨hUn, 3, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPair hK E
    have hab := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hlog₂
    have hle := MMP.Mori.discrep_le hE ha'
    have hformula := MMP.Mori.discrep_eq_of_isSNC sU hUn hsm (by norm_num) hK S hCqsupp hsncS
      (fun P hP => by rw [hCqc, if_pos hP]; exact_mod_cast (hq2 P).le)
    have hpos := zero_lt_inf_snc_bound S Cq.coeff
      (fun P hP => by rw [hCqc, if_pos hP]; exact_mod_cast hq2 P) (fun E F => E ≠ F)
      (fun E F => ((E.support : Set U) ∩ F.support).Nonempty)
      (fun P hP P' hP' hne hmeet => Set.disjoint_iff_inter_eq_empty.mp
        (hdisj P hP P' hP' hne) ▸ hmeet |>.ne_empty rfl)
    rw [← hformula] at hpos
    have h0 : (0 : EReal) < ((a' : ℝ) : EReal) := hpos.trans_le hle
    have h0' : (0 : ℝ) < a' := by exact_mod_cast h0
    have hmono : ∑ P ∈ S, C.coeff P * t P ≤ ∑ P ∈ S, ((q P : ℚ) : ℝ) * t P :=
      Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_right (hq1 P).le (ht0 P)
    rw [e1]
    linarith
  -- `K + C` is `ℝ`-Cartier
  have hUQ : IsQFactorial sU := ⟨hUn, fun D => ⟨1, one_pos, isCartier_of_isSmoothScheme hsm _⟩⟩
  obtain ⟨m, r, L, hL, hKC⟩ := isCartierCombination_of_isQFactorial hUQ
    (Divisor.toRDivisor K + C)
  refine ⟨⟨hUn, fun P hP => ⟨lt_of_le_of_ne (hC0 P) (Ne.symm hP), hC1 P⟩, ⟨3, K, hK,
    m, r, L, hL, fun Γ => ?_⟩, fun n E a hE ha => (hterm n E a hE ha).le⟩, hterm⟩
  have := congrArg (fun D : RDivisor U => D.coeff Γ) hKC
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor] at this
  rw [← this]
  rfl

/-! ### The terminal program over a model -/

/-- **Running the terminal program over `Y`.** From a real terminal pair `(U, C)` on a
projective birational model `p : U ⟶ Y`, every component of `C` mapping onto a prime divisor of
`Y`, the terminal program over `Y` ends at a projective birational model `π : Y' ⟶ Y` with
`(Y', C')` real terminal and `K_{Y'} + C'` nef over `Y`; along the way the coefficient of a prime
divisor of `Y'` over a prime divisor `G` of `Y` is that of the prime divisor of `U` over `G`. -/
private theorem exists_isRelativelyNef_model {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hYp : MMP.Mori.IsProjectiveVariety ℂ sY) (hdimY : topologicalKrullDim Y = 3)
    {U : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    (p : U ⟶ Y) (hUp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sY)) (hpp : IsProjectiveMorphism p)
    (hpb : IsBirationalMorphism p) (hUQ : IsQFactorial (p ≫ sY))
    (hdimU : topologicalKrullDim U = 3) {K : Divisor U}
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor (p ≫ sY) n) {C : RDivisor U}
    (hC : IsRealTerminalPair (p ≫ sY) C)
    (hCX : ∀ P : MMP.Mori.PrimeDivisor U, C.coeff P ≠ 0 →
      ∃ Q : MMP.Mori.PrimeDivisor Y, RationalMap.transformPrimeDivisor p.toRationalMap P = some Q) :
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : CompactSpace Y') (_ : IsLocallyNoetherian Y')
      (_ : IsNormal Y') (π : Y' ⟶ Y) (K' : Divisor Y') (C' : RDivisor Y'),
      IsProjectiveMorphism π ∧ IsBirationalMorphism π ∧
      MMP.Mori.IsProjectiveVariety ℂ (π ≫ sY) ∧ IsQFactorial (π ≫ sY) ∧
      (∃ n : ℕ, K'.IsCanonicalDivisor (π ≫ sY) n) ∧ IsRealTerminalPair (π ≫ sY) C' ∧
      MMP.Flips.IsRelativelyNef ℂ (π ≫ sY) π (MMP.Flips.logCanonicalDivisor K' C') ∧
      ∀ (P' : MMP.Mori.PrimeDivisor Y') (G : MMP.Mori.PrimeDivisor Y),
        π P'.genericPoint = G.genericPoint →
          ∃ P : MMP.Mori.PrimeDivisor U, p P.genericPoint = G.genericPoint ∧
            C'.coeff P' = C.coeff P := by
  obtain ⟨hall, n, Yi, sYi, i1, i2, i3, i4, πY, KY, CY, R, Zi, sZi, f, g, fp, hmodels, hsteps,
    hnefn⟩ := IsRealTerminalPair.terminates_of_isBirationalMorphism hUp hYp rfl hpp hpb hUQ hdimU
      hdimY hK hC hCX
  haveI : IsSeparated (Y ↘ ⊤_ Scheme) :=
    MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety (s := sY) ⟨hYp.toIsVariety,
      inferInstance⟩
  -- the models over `Y` are projective and birational, and coefficients are tracked
  have key : ∀ i ≤ n, IsProjectiveMorphism (modelMap p πY i) ∧
      IsBirationalMorphism (modelMap p πY i) ∧
      ∀ (P' : MMP.Mori.PrimeDivisor (modelSeq U Yi i)) (G : MMP.Mori.PrimeDivisor Y),
        modelMap p πY i P'.genericPoint = G.genericPoint →
          ∃ P : MMP.Mori.PrimeDivisor U, p P.genericPoint = G.genericPoint ∧
            (divisorSeq C CY i).coeff P' = C.coeff P := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨hpp, hpb, fun P' G hG => ⟨P', hG, rfl⟩⟩
    | succ i ih =>
      intro hi
      obtain ⟨hpi, hbi, htri⟩ := ih (Nat.le_of_succ_le hi)
      obtain ⟨-, -, hcontr, hnec, hfpg, hcase⟩ := hsteps i (Nat.lt_of_succ_le hi)
      have hZ := hnec.isNormalVariety_target
      haveI : IsIntegral (Zi i) := hZ.1.toIsIntegral
      haveI : IsNormal (Zi i) := hZ.2
      haveI : LocallyOfFiniteType (sZi i) := hZ.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian (Zi i) := LocallyOfFiniteType.isLocallyNoetherian (sZi i)
      haveI : IsSeparated (Zi i ↘ ⊤_ Scheme) :=
        MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZ
      haveI : IsProper (f i) := hnec.isContraction.isProper
      haveI : IsProper (g i) := isProper_of_isProjectiveMorphism _ hcontr.isProjectiveMorphism
      have hfb : IsBirationalMorphism (f i) ∧ IsBirationalMorphism (fp i) ∧
          IsProjectiveMorphism (fp i) ∧ CY i = flipTransform (f i) (fp i) (divisorSeq C CY i) := by
        rcases hcase with ⟨⟨hfb, -⟩, hfpiso, -, hCY⟩ | hflip
        · exact ⟨hfb, isBirationalMorphism_of_isIso _,
            MMP.isProjectiveMorphism_of_isClosedImmersion _, hCY⟩
        · exact ⟨hflip.isBirationalMorphism, hflip.isBirationalMorphism_flip,
            hflip.isProjectiveMorphism_flip, hflip.eq_flipTransform⟩
      obtain ⟨hfb, hfpb, hfpp, hCY⟩ := hfb
      haveI : IsProper (fp i) := isProper_of_isProjectiveMorphism _ hfpp
      haveI := hfb.isDominant
      haveI := hfpb.isDominant
      have hgb : IsBirationalMorphism (g i) :=
        MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left (f i) (g i) hfb
          (hcontr.comp_eq ▸ hbi)
      refine ⟨?_, ?_, fun (P' : MMP.Mori.PrimeDivisor (Yi i)) G hG => ?_⟩
      · show IsProjectiveMorphism (πY i)
        rw [← hfpg]
        exact hfpp.comp hcontr.isProjectiveMorphism
      · show IsBirationalMorphism (πY i)
        rw [← hfpg]
        exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfpb hgb
      have hG' : g i (fp i P'.genericPoint) = G.genericPoint := by
        have hG0 : πY i P'.genericPoint = G.genericPoint := hG
        rw [← hfpg, Scheme.Hom.comp_apply] at hG0
        exact hG0
      obtain ⟨Q, hQ, -⟩ :=
        MMP.Fourfold.Oai4C1.BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hgb hG'
      obtain ⟨Pm, -, hPm⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := f i) Q
        (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus (f i) hfb Q)
      have := Q.isDiscreteValuationRing_localRing
      have hcoef : (CY i).coeff P' = (divisorSeq C CY i).coeff Pm := by
        rw [hCY]
        exact MMP.Fourfold.flipTransform_apply_of_map_genericPoint
          hfb.functionFieldMap_bijective (fp i).surjective hPm hQ.symm
          (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus (fp i) hfpb Q) _
      have hPmG : modelMap p πY i Pm.genericPoint = G.genericPoint := by
        rw [← hcontr.comp_eq, Scheme.Hom.comp_apply, hPm, hQ, hG']
      obtain ⟨P, hP, hPc⟩ := htri Pm G hPmG
      exact ⟨P, hP, hcoef.trans hPc⟩
  obtain ⟨hπp, hπb, htr⟩ := key n le_rfl
  obtain ⟨hpv, hpq, hcomp⟩ := hmodels n le_rfl
  have hfin := (hall n Yi sYi πY KY CY R Zi sZi f g fp (fun i hi => hmodels i (by exact_mod_cast hi))
    (fun i hi => hsteps i (by exact_mod_cast hi))).2 n le_rfl
  have hKn : ∃ m : ℕ,
      MMP.Mori.Divisor.IsCanonicalDivisor (modelStr (p ≫ sY) sYi n) m (divisorSeq K KY n) := by
    rcases n with _ | n
    · exact hK
    · obtain ⟨-, -, -, -, -, hcase⟩ := hsteps n (Nat.lt_succ_self n)
      rcases hcase with ⟨-, -, hKY, -⟩ | hflip
      · exact hKY
      · exact hflip.isCanonicalDivisor_flip
  refine ⟨modelSeq U Yi n, inferInstance, inferInstance, inferInstance, inferInstance,
    modelMap p πY n, divisorSeq K KY n, divisorSeq C CY n, hπp, hπb, ?_, ?_, ?_, ?_, ?_, htr⟩
  · rwa [hcomp]
  · rwa [hcomp]
  · rwa [hcomp]
  · rwa [hcomp]
  · haveI : QuasiCompact (modelMap p πY n ≫ sY) := by rw [hcomp]; infer_instance
    exact isRelativelyNef_congr hcomp.symm hnefn

/-- **One round of the construction.** From a crepant model `(Y, h, B_Y)` of `(X, B)`: a
projective log resolution `p : U ⟶ Y` with smooth disjoint boundary transforms, on which
`C = p⁻¹_* B_Y` is real terminal; the relative terminal program of `(U, C)` over `Y`, ending at
`h_Y : Y' ⟶ Y` with `K_{Y'} + C'` nef over `Y`; by negativity
`E = K_{Y'} + C' - h_Y^*(K_Y + B_Y) ≤ 0`, so `B_{Y'} = C' - E ≥ 0` is crepant. If `(Y', B_{Y'})`
is not terminal then `E ≠ 0`, and a component of `E` is a new member of `lowSet sX B`. -/
private theorem exists_isCrepantModel_step (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sX B)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ X)
    (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h) (BY : RDivisor Y)
    (hc : IsCrepantModel (sX := sX) B h hY hh BY) :
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : IsLocallyNoetherian Y') (_ : IsNormal Y')
      (h' : Y' ⟶ X) (hh' : IsBirationalMorphism h') (hY' : IsQFactorial (h' ≫ sX))
      (BY' : RDivisor Y'),
      IsCrepantModel (sX := sX) B h' hY'.1 hh' BY' ∧
      realized (sX := sX) h hY hh ⊆ realized (sX := sX) h' hY'.1 hh' ∧
      (IsRealTerminalPair (h' ≫ sX) BY' ∨
        ∃ v ∈ lowSet sX B, v ∈ realized (sX := sX) h' hY'.1 hh' ∧
          v ∉ realized (sX := sX) h hY hh) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hB.1
  haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨ω, m, r, C, hω0, hK, hC, hsum⟩ := exists_presentation hdim hB
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hc.1
  haveI : IsDominant h := hh.isDominant
  haveI : MMP.Mori.IsVariety ℂ (h ≫ sX) := hY.1
  haveI : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (h ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (h ≫ sX)
  have hYp : MMP.Mori.IsProjectiveVariety ℂ (h ≫ sX) :=
    @AlgebraicGeometry.IsProjectiveVariety.mk _ _ _ _ hY.1 (hc.1.comp hX.isProjective)
  have hdimY : topologicalKrullDim Y = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (h ≫ sX) hh).symm.trans
      hdim
  have hBY1 : ∀ P, BY.coeff P < 1 := fun P => by
    have := hB.2.2.2 3 _ _ (hc.2.2 P)
    linarith
  -- the log resolution `p : U ⟶ Y`
  obtain ⟨U, p, hpp, hlog, hUv, ⟨s, hsnc, hs⟩, hdisj⟩ := exists_isLogResolution_disjoint hY hYp.isProjective BY
  haveI : MMP.Mori.IsVariety ℂ (p ≫ h ≫ sX) := hUv
  haveI : IsIntegral U := hUv.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ h ≫ sX) := hUv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (p ≫ h ≫ sX)
  haveI : QuasiCompact (p ≫ h ≫ sX) := hUv.toQuasiCompact
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (p ≫ h ≫ sX)
  have hUsm : IsSmoothScheme (p ≫ h ≫ sX) := hlog.isSmoothScheme
  haveI : Smooth (p ≫ h ≫ sX) := hUsm.smooth
  haveI : IsNormal (Spec (.of ℂ)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal U := AlgebraicGeometry.isNormal_of_smooth (p ≫ h ≫ sX)
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  have hpb : IsBirationalMorphism p := hlog.isBirationalMorphism
  haveI : IsDominant p := hpb.isDominant
  have hUp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ h ≫ sX) :=
    @AlgebraicGeometry.IsProjectiveVariety.mk _ _ _ _ hUv (hpp.comp hYp.isProjective)
  have hdimU : topologicalKrullDim U = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (h ≫ sX) (p ≫ h ≫ sX)
      hpb).symm.trans hdimY
  have hUQ : IsQFactorial (p ≫ h ≫ sX) :=
    ⟨⟨hUv, inferInstance⟩, fun D => ⟨1, one_pos, isCartier_of_isSmoothScheme hUsm _⟩⟩
  obtain ⟨KU, hKU⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ h ≫ sX) hUsm hdimU
  -- the boundary `C₀ = p⁻¹_* B_Y`
  set C₀ : RDivisor U := inverseTransformDivisor p BY with hC₀def
  have hC₀ : ∀ (P : MMP.Mori.PrimeDivisor U) (Q : MMP.Mori.PrimeDivisor Y),
      p P.genericPoint = Q.genericPoint → C₀.coeff P = BY.coeff Q := fun P Q hPQ =>
    MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint hPQ
      (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hpb Q) BY
  have hC₀ne : ∀ P : MMP.Mori.PrimeDivisor U, C₀.coeff P ≠ 0 →
      ∃ Q ∈ BY.support, inverseTransformPrimeDivisor p Q = some P := by
    intro P hP
    by_cases hex : ∃ Q, inverseTransformPrimeDivisor p Q = some P
    · obtain ⟨Q, hQ⟩ := hex
      have hQP :=
        (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1
      refine ⟨Q, ?_, hQ⟩
      rw [hC₀ P Q hQP] at hP
      exact Finsupp.mem_support_iff.mpr hP
    · push Not at hex
      exact absurd (MMP.Fourfold.Oai4C1.mapPrimeDivisors_apply_eq_zero hex BY) hP
  have hC₀Q : ∀ P : MMP.Mori.PrimeDivisor U, C₀.coeff P ≠ 0 →
      ∃ Q ∈ BY.support, inverseTransformPrimeDivisor p Q = some P ∧ C₀.coeff P = BY.coeff Q :=
    fun P hP => by
      obtain ⟨Q, hQs, hQ⟩ := hC₀ne P hP
      exact ⟨Q, hQs, hQ, hC₀ P Q
        (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1⟩
  have hterm : IsRealTerminalPair (p ≫ h ≫ sX) C₀ := by
    refine isRealTerminalPair_of_isSNC hUv hUsm hdimU s hsnc (fun P hP => ?_) (fun P => ?_)
      (fun P => ?_) (fun P hP P' hP' hne => ?_)
    · obtain ⟨Q, hQs, hQ, -⟩ := hC₀Q P (Finsupp.mem_support_iff.mp hP)
      exact hs Q hQs P hQ
    · by_cases h0 : C₀.coeff P = 0
      · exact h0.symm.le
      · obtain ⟨Q, -, -, hQ⟩ := hC₀Q P h0
        rw [hQ]
        exact hc.2.1 Q
    · by_cases h0 : C₀.coeff P = 0
      · simp [h0]
      · obtain ⟨Q, -, -, hQ⟩ := hC₀Q P h0
        rw [hQ]
        exact hBY1 Q
    · obtain ⟨Q, hQs, hQ, -⟩ := hC₀Q P (Finsupp.mem_support_iff.mp hP)
      obtain ⟨Q', hQ's, hQ', -⟩ := hC₀Q P' (Finsupp.mem_support_iff.mp hP')
      refine hdisj Q hQs Q' hQ's (fun hQQ => hne ?_) P P' hQ hQ'
      subst hQQ
      exact Option.some_injective _ (hQ.symm.trans hQ')
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hY
  have hCX : ∀ P : MMP.Mori.PrimeDivisor U, C₀.coeff P ≠ 0 →
      ∃ Q : MMP.Mori.PrimeDivisor Y,
        RationalMap.transformPrimeDivisor p.toRationalMap P = some Q := by
    intro P hP
    obtain ⟨Q, -, hQ⟩ := hC₀ne P hP
    exact ⟨Q, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P Q).mpr
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1⟩
  -- the terminal program over `Y`
  obtain ⟨Y', i1, i2, i3, i4, π, K', C', hπp, hπb, hY'p, hY'Q, hK', hC'term, hnef, htrack⟩ :=
    exists_isRelativelyNef_model hYp hdimY p hUp hpp hpb hUQ hdimU ⟨_, hKU⟩ hterm hCX
  set h' : Y' ⟶ X := π ≫ h with hh'def
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπp
  haveI : IsDominant π := hπb.isDominant
  have hh' : IsBirationalMorphism h' :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hπb hh
  haveI : IsDominant h' := hh'.isDominant
  have hh'p : IsProjectiveMorphism h' := hπp.comp hc.1
  haveI : IsProper h' := isProper_of_isProjectiveMorphism h' hh'p
  have hassoc : h' ≫ sX = π ≫ h ≫ sX := Category.assoc _ _ _
  have hY'Q' : IsQFactorial (h' ≫ sX) := hassoc ▸ hY'Q
  have hY'n : IsNormalVariety ℂ (h' ≫ sX) := hY'Q'.1
  have hY'n' : IsNormalVariety ℂ (π ≫ h ≫ sX) := hY'Q.1
  haveI : MMP.Mori.IsVariety ℂ (h' ≫ sX) := hY'n.1
  haveI : LocallyOfFiniteType (h' ≫ sX) := hY'n.1.toLocallyOfFiniteType
  haveI : QuasiCompact (h' ≫ sX) := hY'n.1.toQuasiCompact
  haveI : MMP.Mori.IsVariety ℂ (π ≫ h ≫ sX) := hY'n'.1
  haveI : QuasiCompact (π ≫ h ≫ sX) := hY'n'.1.toQuasiCompact
  have hdimY' : topologicalKrullDim Y' = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (h' ≫ sX) hh').symm.trans
      hdim
  -- pull-backs of the presentation
  choose CY hCY using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant h (hC i)
  have hCYc : ∀ i, (CY i).IsCartier := fun i => (hCY i).isCartier (hC i)
  choose CY' hCY' using fun i =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant π (hCYc i)
  have hCY'c : ∀ i, (CY' i).IsCartier := fun i => (hCY' i).isCartier (hCYc i)
  have hCY'h : ∀ i, ∃ hB, (C i).IsPullback h' hB (CY' i) := fun i =>
    ⟨_, MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hCY i) (hCY' i)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp h' (C i))⟩
  set L : RDivisor Y := ∑ i, r i • Divisor.toRDivisor (CY i) with hLdef
  set L' : RDivisor Y' := ∑ i, r i • Divisor.toRDivisor (CY' i) with hL'def
  set K'' : Divisor Y' := divisorOfForm (pullbackRationalPluriForms sX h' ω) with hK''def
  set BY' : RDivisor Y' := L' - Divisor.toRDivisor K'' with hBY'def
  have hBYc : ∀ F, BY'.coeff F = ∑ i, r i * ((CY' i).coeff F : ℝ) -
      ((⟨Y', h', hY'n, hh', F⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) := by
    intro F
    rw [hBY'def, DivisorWithCoeffs.coeff_sub, hL'def, MMP.Flips.coeff_sum_smul_toRDivisor,
      Divisor.coeff_toRDivisor, hK''def, coeff_divisorOfForm]
    rfl
  have hcrep : ∀ F, MMP.Intersection.IsLogDiscrepancy sX 3 B ⟨Y', h', hY'n, hh', F⟩
      (1 - BY'.coeff F) := by
    intro F
    convert isLogDiscrepancy_of_presentation hXn hω0 hK hC hsum h' hY'n hh' CY' hCY'h F using 1
    rw [hBYc]
    ring
  -- the negativity lemma over `Y`
  obtain ⟨n', hK'n⟩ := hK'
  obtain rfl := eq_three_of_isCanonicalDivisor hK'n hdimY'
  have hK'n' : K'.IsCanonicalDivisor (h' ≫ sX) 3 := hassoc ▸ hK'n
  have hτ0 : pullbackRationalPluriForms sX h' ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hdim h' hh' hω0
  have hKlin : K''.LinearlyEquivalent K' := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY'n hK'n' hτ0
  set M : RDivisor Y' := MMP.Flips.logCanonicalDivisor K'' C' with hMdef
  have hMnef : MMP.Flips.IsRelativelyNef ℂ (h' ≫ sX) π M :=
    isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent
      (isRelativelyNef_congr hassoc.symm hnef) hKlin
  have hMc := isCartierCombination_of_isQFactorial hY'Q' M
  set Bn : RDivisor Y' := L' - M with hBndef
  have hBnc := isCartierCombination_of_isQFactorial hY'Q' Bn
  have hLc : MMP.Flips.IsCartierCombination L :=
    ⟨m, r, CY, hCYc, by simp only [hLdef, MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hL'c : MMP.Flips.IsCartierCombination L' :=
    ⟨m, r, CY', hCY'c, by simp only [hL'def, MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hL' : MMP.Flips.IsRCartierPullback π L L' :=
    ⟨m, r, CY, CY', hCYc, rfl, fun i => ⟨_, hCY' i⟩, rfl⟩
  have hBG0 : ∀ P : MMP.Mori.PrimeDivisor Y',
      ¬ MMP.Flips.IsExceptionalPrimeDivisor (h ≫ sX) π P → Bn.coeff P = 0 := by
    intro P hP
    obtain ⟨G, hG⟩ := exists_genericPoint_eq_of_not_isExceptionalPrimeDivisor hY hY'n' hπb P hP
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hπb hG
    have e1 : L'.coeff P = L.coeff G := MMP.Fourfold.coeff_eq_of_isRCartierPullback P G hG hL'
    have e2 : L.coeff G = BY.coeff G +
        ((⟨Y, h, hY, hh, G⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) := by
      rw [coeff_eq_of_isCrepantModel hXn hω0 hK hC hsum hc CY (fun i => ⟨_, hCY i⟩) G, hLdef,
        MMP.Flips.coeff_sum_smul_toRDivisor]
      ring
    have e3 : (K''.coeff P : ℝ) =
        ((⟨Y, h, hY, hh, G⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) := by
      have hv := valuation_eq_of_map_genericPoint_eq hY hh hπb hY'n hh' P G hG
      have := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hXn hdim hv ω
      rw [← this, hK''def, coeff_divisorOfForm]
      rfl
    have e4 : C'.coeff P = BY.coeff G := by
      obtain ⟨P₀, hP₀, hc'⟩ := htrack P G hG
      rw [hc', hC₀ P₀ G hP₀]
    rw [hBndef, hMdef, MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, e1, e2, e3, e4]
    ring
  have hnum : MMP.Flips.IsNumericallyEquivalentOver ℂ (h' ≫ sX) π L' (M + Bn) :=
    isNumericallyEquivalentOver_of_eq (h' ≫ sX) π (by rw [hBndef]; abel) hL'c
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ (h ≫ sX)
    (h' ≫ sX) hY hY'n π hassoc.symm hπb hLc hL' hMc hMnef hBnc
    (fun P hP => (hBG0 P hP).symm.le) hnum
  have hC'0 : ∀ P, 0 ≤ C'.coeff P := fun P => by
    by_cases h0 : C'.coeff P = 0
    · exact h0.symm.le
    · exact (hC'term.1.2.1 P h0).1.le
  have hBYeq : ∀ P, BY'.coeff P = Bn.coeff P + C'.coeff P := fun P => by
    rw [hBY'def, hBndef, hMdef, MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add]
    ring
  have hBYge : ∀ P, C'.coeff P ≤ BY'.coeff P := fun P => by
    rw [hBYeq]
    linarith [heff P]
  refine ⟨Y', i1, i3, i4, h', hh', hY'Q', BY', ⟨hh'p, fun P => (hC'0 P).trans (hBYge P), hcrep⟩,
    ?_, ?_⟩
  · rintro v ⟨G, rfl⟩
    obtain ⟨F, -, hF⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some
      (g := π) G (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus π hπb G)
    exact ⟨F, valuation_eq_of_map_genericPoint_eq hY hh hπb hY'n hh' F G hF⟩
  by_cases hEq : ∀ P, BY'.coeff P = C'.coeff P
  · left
    rw [Finsupp.ext hEq, hassoc]
    exact hC'term
  · right
    push Not at hEq
    obtain ⟨F, hF⟩ := hEq
    have hFexc : MMP.Flips.IsExceptionalPrimeDivisor (h ≫ sX) π F := by
      by_contra hne
      apply hF
      rw [hBYeq, hBG0 F hne, zero_add]
    have h2 : 2 ≤ Order.coheight (π F.genericPoint) :=
      two_le_coheight_of_isExceptionalPrimeDivisor hFexc
    refine ⟨_, ⟨3, ⟨Y', h', hY'n, hh', F⟩, 1 - BY'.coeff F, ?_, rfl, hcrep F, by
      linarith [hC'0 F, hBYge F]⟩, ⟨F, rfl⟩, ?_⟩
    · exact (divisorOver_isExceptional_iff_two_le_coheight hXn _).mpr <| h2.trans <|
        MMP.Flips.coheight_le_coheight_map sX (h ≫ sX) hXn.1 hY.1 h rfl
          (hdimY.trans hdim.symm) (π F.genericPoint)
    · rintro ⟨G, hG⟩
      have := map_genericPoint_eq_of_valuation_eq hY hh hπb hY'n hh' F G hG.symm
      rw [this, G.coheight_genericPoint] at h2
      exact absurd h2 (by decide)

/-- Iterating `exists_isCrepantModel_step`: from any crepant model there is a `ℚ`-factorial real
terminal one, by strong induction on the number `n` of members of the finite set `lowSet sX B`
not yet realized. -/
private theorem exists_terminal_of_isCrepantModel (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sX B) (n : ℕ) :
    ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ X)
      (hY : IsNormalVariety ℂ (h ≫ sX)) (hh : IsBirationalMorphism h) (BY : RDivisor Y),
      IsCrepantModel (sX := sX) B h hY hh BY →
      (lowSet sX B \ realized (sX := sX) h hY hh).ncard = n →
      ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : IsLocallyNoetherian Y') (_ : IsNormal Y')
        (h' : Y' ⟶ X) (hh' : IsBirationalMorphism h') (hY' : IsQFactorial (h' ≫ sX))
        (BY' : RDivisor Y'),
        IsCrepantModel (sX := sX) B h' hY'.1 hh' BY' ∧ IsRealTerminalPair (h' ≫ sX) BY' := by
  have hfin : (lowSet sX B).Finite := hB.finite_setOf_isLogDiscrepancy_le_one
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ _ h hY hh BY hc hn
    obtain ⟨Y', i1, i2, i3, h', hh', hY', BY', hc', hsub, hterm | ⟨v, hvS, hv', hv⟩⟩ :=
      exists_isCrepantModel_step hX hdim hB0 hB h hY hh BY hc
    · exact ⟨Y', i1, i2, i3, h', hh', hY', BY', hc', hterm⟩
    · refine ih _ ?_ h' hY'.1 hh' BY' hc' rfl
      rw [← hn]
      exact Set.ncard_lt_ncard ⟨Set.diff_subset_diff_right hsub,
        fun hle => (hle ⟨hvS, hv⟩).2 hv'⟩ hfin.diff

/-- **Crepant real terminal models.** -/
private theorem solution
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (h : Y ⟶ X) (hh : IsBirationalMorphism h) (hY : IsQFactorial (h ≫ sX)) (BY : RDivisor Y),
      IsProjectiveMorphism h ∧ (∀ P, 0 ≤ BY.coeff P) ∧
      (∀ F : MMP.Mori.PrimeDivisor Y,
        MMP.Intersection.IsLogDiscrepancy sX 3 B ⟨Y, h, hY.1, hh, F⟩ (1 - BY.coeff F)) ∧
      IsRealTerminalPair (h ≫ sX) BY := by
  obtain ⟨hY0, hh0, hc0⟩ := exists_isCrepantModel_id hX hdim hB0 hB
  obtain ⟨Y, i1, i2, i3, h, hh, hY, BY, ⟨hp, hBY, hld⟩, hterm⟩ :=
    exists_terminal_of_isCrepantModel hX hdim hB0 hB _ (𝟙 X) hY0 hh0 B hc0 rfl
  exact ⟨Y, i1, i2, i3, h, hh, hY, BY, hp, hBY, hld, hterm⟩

end

end Proof_thm_fourfold_real_klt_crepant_terminal_model

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Crepant real terminal models.** Let `X` be a normal projective complex threefold and `B` an
effective real boundary with `(X, B)` klt. Then there are a projective birational morphism
`h : Y ⟶ X` from a `ℚ`-factorial normal variety `Y` (over `ℂ` through `h`) and an effective
`ℝ`-divisor `B_Y` on `Y` such that `K_Y + B_Y = h^*(K_X + B)`, that is,
`a(F, X, B) = 1 - coeff_F B_Y` for every prime divisor `F` of `Y`, and `(Y, B_Y)` is real
terminal. -/
@[mmp "thm_fourfold_real_klt_crepant_terminal_model"]
public theorem IsRealKltPair.exists_isRealTerminalPair_crepant
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (h : Y ⟶ X) (hh : IsBirationalMorphism h) (hY : IsQFactorial (h ≫ sX)) (BY : RDivisor Y),
      IsProjectiveMorphism h ∧ (∀ P, 0 ≤ BY.coeff P) ∧
      (∀ F : MMP.Mori.PrimeDivisor Y,
        MMP.Intersection.IsLogDiscrepancy sX 3 B ⟨Y, h, hY.1, hh, F⟩ (1 - BY.coeff F)) ∧
      IsRealTerminalPair (h ≫ sX) BY :=
  Proof_thm_fourfold_real_klt_crepant_terminal_model.solution hX hdim hB0 hB

end MMP.Fourfold
