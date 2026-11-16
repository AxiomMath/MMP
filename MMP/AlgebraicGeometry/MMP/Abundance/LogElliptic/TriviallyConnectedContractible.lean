module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.DescendedBundleAmple
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.MMP.ConeTheorem.NefNullFaceRay
import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContractionLineBundle
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorial
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionKlt
import MMP.AlgebraicGeometry.MMP.Threefold.DivisorialContractionQFactorial
import MMP.AlgebraicGeometry.Divisor.BirationalPushforwardSections
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.NormalWeilDivisorInvertible
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.HFlopExistence
import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
import MMP.AlgebraicGeometry.MMP.Flip.FlopTriviallyConnected
import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurves
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.Analysis.Complex.CauchyOsgoodLaurent
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# A trivially connected prime divisor becomes contractible after trivial flops

Let `(X, Δ_X)` satisfy the assumptions of the abundance theorem FA 15.4, and suppose that
`L = K_X + Δ_X` is not eventually free and composed of a pencil. If `D` is an `L`-trivially
connected prime divisor on `X`, then after finitely many flops of `(K + Δ)`-trivial flop data
`X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` the strict transform `D_m` of `D` is the exceptional locus of a
birational contraction `c : X_m ⟶ X'`. Moreover `K_{X_m} + Δ_m ∼_ℚ c^*(K_{X'} + Δ')` with
`Δ' = c_* Δ_m`, `ρ(X') = ρ(X) - 1`, and `(X', Δ')` again satisfies the assumptions of FA 15.4.

The models are built one at a time. On a model `X_i` satisfying the assumptions of 15.4, with
`D_i` trivially connected, there is a `(K + Δ_i)`-null, `D_i`-negative extremal ray `R`; its
contraction is either divisorial, with exceptional locus `D_i`, which ends the chain, or small,
in which case the `D_i`-flop exists and the flopped model satisfies the same conditions. A
sequence of such flops is finite.

## Main results

* `MMP.Flips.exists_trivialFlop_chain_projective_of_isTriviallyConnected`: the chain, with all
  models satisfying the assumptions of 15.4 and all flop bases projective, given the termination
  of `H`-flops.
* `MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_hFlopSequencesTerminate`:
  FA 15.9, given the termination of `H`-flops.

## Implementation notes

Stated over ℂ: its flop inputs
(lem_fourfold_projective_effective_divisor_flop_exists,
lem_fourfold_projective_effective_divisor_flops_terminate,
lem_fourfold_fa15_projective_flop_trivial_connected_preserved) are available over ℂ only.

The termination of `H`-flops on projective klt threefolds is the hypothesis
`MMP.Flips.HFlopSequencesTerminate`, whose statement is that of
`MMP.Fourfold.hFlopSequence_length_lt_top`.

The chain is built by recursion on the models: each model carries its canonical divisor, its
boundary and the transform of `D`, which stays a prime divisor. Once a model admits the final
divisorial contraction the recursion repeats it; termination of `H`-flops shows that some model
does. The models of the statement are `MMP.Fourfold.modelSeq`, with `X_{i+1} = Y i`.

The statement of FA 15.9 is the source's, over `ℂ`; the divisorial and small cases of the
contraction of the null ray are the two branches of the step.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-- **Termination of `H`-flops on a projective klt complex threefold** (FA 6.8, used in 15.9), as
a proposition: every sequence of `H`-flops with respect to `K + B`, crepant for `K + B`, of
contractions of relative Picard number one onto projective varieties, starting from a
`ℚ`-factorial projective klt threefold with `H ≥ 0` `ℚ`-Cartier and staying projective and
`ℚ`-factorial, has finite length. -/
def HFlopSequencesTerminate : Prop :=
  ∀ (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) [∀ i, LocallyOfFiniteType (sY i)]
    (K : ∀ i, Divisor (Y i)) (B H : ∀ i, QDivisor (Y i))
    (_ : MMP.Mori.IsProjectiveVariety ℂ (sY 0)) (_ : topologicalKrullDim (Y 0) = 3)
    (_ : IsQFactorial (sY 0)) (_ : (B 0).IsEffective)
    (_ : Mori.IsKltPair (sY 0) 3 (K 0) (B 0))
    (_ : (H 0).IsEffective) (_ : (H 0).IsQCartier)
    (n : ℕ∞) (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ Z i) (fp : ∀ i, Y (i + 1) ⟶ Z i) (g : ∀ i, (Y i).RationalMap (Y (i + 1)))
    (_ : ∀ i : ℕ, (i : ℕ∞) ≤ n → MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (_ : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (sY i))
    (_ : ∀ i : ℕ, (i : ℕ∞) ≤ n → (K i).IsCanonicalDivisor (sY i) 3)
    (_ : ∀ i : ℕ, (i : ℕ∞) < n →
      IsHFlop ℂ (sY i) (sZ i) (sY (i + 1)) 3 (K i) (QDivisor.toRDivisor (B i)) (H i) (f i) (fp i)
        (g i))
    (_ : ∀ i : ℕ, (i : ℕ∞) < n → Flips.relativePicardNumber (sY i) (f i) = 1)
    (_ : ∀ i : ℕ, (i : ℕ∞) < n → MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (_ : ∀ i : ℕ, (i : ℕ∞) < n →
      IsNumericallyTrivialOver ℂ (sY (i + 1)) (fp i)
        (logCanonicalDivisor (K (i + 1)) (QDivisor.toRDivisor (B (i + 1)))))
    (_ : ∀ i : ℕ, (i : ℕ∞) < n → B (i + 1) = Mori.RationalMap.transformDivisor (g i) (B i))
    (_ : ∀ i : ℕ, (i : ℕ∞) < n → H (i + 1) = Mori.RationalMap.transformDivisor (g i) (H i)),
    n < ⊤

end MMP.Flips

end

section

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.FourfoldProofs.Fa15TriviallyConnectedBecomesContractibleProof

/-- A model of the chain: a scheme over `ℂ` with a canonical divisor, a boundary and a prime
divisor. -/
private structure ChainState : Type 1 where
  Y : Scheme.{0}
  isIntegral : IsIntegral Y
  compactSpace : CompactSpace Y
  isLocallyNoetherian : IsLocallyNoetherian Y
  isNormal : IsNormal Y
  sY : Y ⟶ Spec (.of ℂ)
  locallyOfFiniteType : LocallyOfFiniteType sY
  quasiCompact : QuasiCompact sY
  K : Divisor Y
  Δ : QDivisor Y
  P : Mori.PrimeDivisor Y

attribute [instance] ChainState.isIntegral ChainState.compactSpace ChainState.isLocallyNoetherian
  ChainState.isNormal ChainState.locallyOfFiniteType ChainState.quasiCompact

/-- The invariant of the chain: the model satisfies the assumptions of 15.4, `K + Δ` is not
eventually free and composed of a pencil, `P` is trivially connected, and the Picard number is
`ρ`. -/
private structure ChainState.Inv (ρ : ℕ∞) (s : ChainState) : Prop where
  hA : SatisfiesAbundanceAssumptions ℂ s.sY s.K s.Δ
  hL : ¬ IsEventuallyFreePencil ℂ s.sY (Divisor.toQDivisor s.K + s.Δ)
  hD : IsTriviallyConnected ℂ s.sY 3 s.K s.Δ (Finsupp.single s.P 1)
  hρ : picardNumber s.sY = ρ

/-- The final divisorial contraction of the chain at the model `s`. -/
private def ChainState.IsFinal (s : ChainState) : Prop :=
  ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : s.Y ⟶ X')
    (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
    (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
    IsBirationalContraction ℂ sX' s.sY c ∧ IsBirationalMorphism c ∧
    Flips.exceptionalSet c =
      (DivisorWithCoeffs.supp (Finsupp.single s.P 1 : Divisor s.Y) : Set s.Y) ∧
    (∃ (hc : ∀ Z : irreducibleComponents s.Y,
        c (componentGenericPoint s.Y Z) ∉
          (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
            Mori.RationalMap.transformDivisor c.toRationalMap s.Δ).supp)
        (B : QDivisor s.Y),
      (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
          Mori.RationalMap.transformDivisor c.toRationalMap s.Δ).IsPullback c hc B ∧
        (Divisor.toQDivisor s.K + s.Δ).QLinearlyEquivalent B) ∧
    picardNumber sX' + 1 = picardNumber s.sY ∧
    SatisfiesAbundanceAssumptions ℂ sX' (Mori.RationalMap.transformDivisor c.toRationalMap s.K)
      (Mori.RationalMap.transformDivisor c.toRationalMap s.Δ)

/-- The data of one flop `X_i ⤏ X_{i+1}` of the chain, over the base `T`. -/
private structure Edge (s : ChainState) : Type 1 where
  s' : ChainState
  T : Scheme.{0}
  isIntegral : IsIntegral T
  compactSpace : CompactSpace T
  isLocallyNoetherian : IsLocallyNoetherian T
  isNormal : IsNormal T
  sT : T ⟶ Spec (.of ℂ)
  locallyOfFiniteType : LocallyOfFiniteType sT
  φ : s.Y ⟶ T
  φp : s'.Y ⟶ T
  p : s.Y.RationalMap s'.Y

attribute [instance] Edge.isIntegral Edge.compactSpace Edge.isLocallyNoetherian Edge.isNormal
  Edge.locallyOfFiniteType

/-- The properties of a flop of the chain: a `(K + Δ)`-trivial flop which is a `D`-flop, with the
divisors transformed along it. -/
private structure Edge.IsFlop {s : ChainState} (e : Edge s) : Prop where
  isTrivialFlop : IsTrivialFlop ℂ s.sY e.s'.sY e.sT 3 s.K s.Δ e.φ e.φp e.p
  K_eq : e.s'.K = Mori.RationalMap.transformDivisor e.p s.K
  Δ_eq : e.s'.Δ = flopDivisor e.p s.Δ
  P_eq : (Finsupp.single e.s'.P 1 : Divisor e.s'.Y) =
    Mori.RationalMap.transformDivisor e.p (Finsupp.single s.P 1 : Divisor s.Y)
  isProjectiveVariety_base : Mori.IsProjectiveVariety ℂ e.sT
  isHFlop : IsHFlop ℂ s.sY e.sT e.s'.sY 3 s.K (QDivisor.toRDivisor s.Δ)
    (Divisor.toQDivisor (Finsupp.single s.P 1 : Divisor s.Y)) e.φ e.φp e.p
  relativePicardNumber_eq : Flips.relativePicardNumber s.sY e.φ = 1
  isNumericallyTrivialOver_flop : IsNumericallyTrivialOver ℂ e.s'.sY e.φp
    (logCanonicalDivisor e.s'.K (QDivisor.toRDivisor e.s'.Δ))

private theorem toRDivisor_smul {X : Scheme.{0}} (q : ℚ) (D : QDivisor X) :
    QDivisor.toRDivisor (q • D) = (q : ℝ) • QDivisor.toRDivisor D := by
  ext E
  change (((q • D) E : ℚ) : ℝ) = (q : ℝ) * ((D E : ℚ) : ℝ)
  rw [Finsupp.smul_apply, smul_eq_mul, Rat.cast_mul]

private theorem isEffective_toQDivisor {X : Scheme.{0}} {D : Divisor X} (hD : D.IsEffective) :
    (Divisor.toQDivisor D).IsEffective := fun E => by
  change (0 : ℚ) ≤ ((D E : ℤ) : ℚ)
  exact_mod_cast hD E

private theorem isEffective_single {X : Scheme.{0}} (P : Mori.PrimeDivisor X) :
    DivisorWithCoeffs.IsEffective (Finsupp.single P (1 : ℤ) : Divisor X) := fun E => by
  change (0 : ℤ) ≤ Finsupp.single P 1 E
  by_cases h : P = E <;> simp [Finsupp.single_apply, h]

/-- **Step 1 of FA 15.9: a null negative extremal ray.** On a model satisfying the assumptions of
15.4 with `L = K + Δ` not eventually free and composed of a pencil and `P` trivially connected,
there are a rational `ε > 0` with `(X, Δ + εP)` klt and a `(K + Δ + εP)`-negative extremal ray
`R` on which `L` vanishes. -/
private theorem exists_isNegativeExtremalRayOf {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] {K : Divisor Y} {Δ : QDivisor Y}
    {P : Mori.PrimeDivisor Y} (hA : SatisfiesAbundanceAssumptions ℂ sY K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sY (Divisor.toQDivisor K + Δ))
    (hD : IsTriviallyConnected ℂ sY 3 K Δ (Finsupp.single P 1)) :
    ∃ ε : ℚ, 0 < ε ∧
      IsKawamataLogTerminal sY 3 K
        (QDivisor.toRDivisor (Δ + ε • Divisor.toQDivisor (Finsupp.single P 1))) ∧
      ∃ R : Set (NumericalCurveClasses sY),
        IsNegativeExtremalRayOf sY
          (Divisor.toQDivisor K + (Δ + ε • Divisor.toQDivisor (Finsupp.single P 1))) R ∧
        ∀ u ∈ R, QDivisor.curveForm sY (Divisor.toQDivisor K + Δ) hA.isQCartier u = 0 := by
  have hQ : IsQFactorial sY := hA.isQFactorial
  obtain ⟨D', hD'e, d, m, hd, hm, M, hM, hlin, hnsub, hmeet⟩ :=
    (isEventuallyFreePencil_or_exists_mem_linearSystem_of_isTriviallyConnected sY
      hA.isProjectiveVariety hQ 3 K Δ hA.isNef hA.exists_two_le_h0 P hD).resolve_left hL
  set E : QDivisor Y := Divisor.toQDivisor (Finsupp.single P 1) with hEdef
  have hEq : E.IsQCartier := isQCartier_of_isQFactorial sY hQ E
  have hD'q : (Divisor.toQDivisor D').IsQCartier := isQCartier_of_isQFactorial sY hQ _
  have hdm : ((d : ℤ) • E + Divisor.toQDivisor D').QLinearlyEquivalent
      ((m : ℤ) • (Divisor.toQDivisor K + Δ)) := by
    have h := hlin.qLinearlyEquivalent
    rwa [map_add, map_zsmul, hM] at h
  obtain ⟨C, -, hLC, hEC⟩ := exists_intersectionNumber_neg_of_isTriviallyConnected sY 3 K Δ P hD
    hA.isQCartier hEq (Divisor.toQDivisor D') hD'q
    (DivisorWithCoeffs.isEffective_iff_nonneg.mp (isEffective_toQDivisor hD'e)) d m hd hm hdm
    (by rwa [Divisor.supp_toQDivisor]) (by rwa [Divisor.supp_toQDivisor])
  obtain ⟨ε₀, hε₀, hk⟩ := exists_pos_forall_isKawamataLogTerminal_add_smul sY 3 K Δ E
    hA.isKawamataLogTerminal (isEffective_toQDivisor (isEffective_single P)) hEq
  obtain ⟨ε, hε, hεlt⟩ := exists_rat_btwn hε₀
  have hε' : (0 : ℚ) < ε := by exact_mod_cast hε
  have hklt : IsKawamataLogTerminal sY 3 K (QDivisor.toRDivisor (Δ + ε • E)) := by
    rw [map_add, toRDivisor_smul]
    exact hk ε hε.le hεlt
  have hΘq : (Divisor.toQDivisor K + (Δ + ε • E)).IsQCartier := isQCartier_of_isQFactorial sY hQ _
  have hnef : QDivisor.IsNefOnCurves sY (Divisor.toQDivisor K + Δ) := by
    refine ⟨hA.isQCartier, fun C' => ?_⟩
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    obtain ⟨hq, hC'⟩ := hA.isNef
    exact_mod_cast hC' C'.scheme C'.ι C'.dim_eq
  have hz : OneCycle.numericalClass sY (C.cycle ℝ) ∈ closedConeOfCurves sY :=
    coneOfCurves_le_closedConeOfCurves sY (Submodule.subset_span ⟨C, rfl⟩)
  have hLz : QDivisor.curveForm sY (Divisor.toQDivisor K + Δ) hnef.1
      (OneCycle.numericalClass sY (C.cycle ℝ)) = 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, hLC, Rat.cast_zero]
  have hKz : QDivisor.curveForm sY (Divisor.toQDivisor K + (Δ + ε • E)) hΘq
      (OneCycle.numericalClass sY (C.cycle ℝ)) < 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    have hεE : (ε • E).IsQCartier := isQCartier_of_isQFactorial sY hQ _
    have h1 : Divisor.toQDivisor K + (Δ + ε • E) = (Divisor.toQDivisor K + Δ) + ε • E :=
      (add_assoc _ _ _).symm
    have h2 := MMP.Mori.QDivisor.intersectionNumber_add' ℂ sY C.ι C.dim_le
      (Divisor.toQDivisor K + Δ) (ε • E) hA.isQCartier hεE (h1 ▸ hΘq)
    have h3 := MMP.Mori.QDivisor.intersectionNumber_smul ℂ sY C.ι C.dim_le ε E hEq hεE
    have h4 : (Divisor.toQDivisor K + (Δ + ε • E)).intersectionNumber ℂ sY C.ι C.dim_le hΘq =
        ((Divisor.toQDivisor K + Δ) + ε • E).intersectionNumber ℂ sY C.ι C.dim_le
          (h1 ▸ hΘq) := by
      congr 1
    rw [h4, h2, h3, hLC, zero_add]
    have : ε * E.intersectionNumber ℂ sY C.ι C.dim_le hEq < 0 := mul_neg_of_pos_of_neg hε' hEC
    exact_mod_cast this
  obtain ⟨R, hR, hRL⟩ :=
    hklt.exists_isNegativeExtremalRayOf_of_curveForm_eq_zero hΘq hA.isProjectiveVariety hnef hz
      hLz hKz
  exact ⟨ε, hε', hklt, R, hR, hRL⟩

/-- On a projective variety the class `[C] ∈ N₁(X)` of a proper curve is nonzero: an ample
invertible sheaf has positive degree on `C`. -/
private theorem numericalClass_cycle_ne_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (C : ProperCurve sX) :
    OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  have hproj : IsProjectiveMorphism sX := ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sX
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sX hproj.isHQuasiProjective)
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := inferInstance
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy sX L
    (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX L hLa) C
    (fun _ _ => Subsingleton.elim _ _)
  intro h0
  have h := OneCycle.mem_numericallyTrivial.mp ((Submodule.Quotient.mk_eq_zero _).mp h0) L
  rw [OneCycle.degree_cycle] at h
  have : (0 : ℝ) < (degreeOn ℂ sX C.ι C.dim_le L : ℝ) := by exact_mod_cast hpos
  exact this.ne' h

private theorem supp_single_one {X : Scheme.{0}} (P : Mori.PrimeDivisor X) :
    (DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X) : Set X) = P.support := by
  classical
  ext x
  simp only [DivisorWithCoeffs.coe_supp, Set.mem_iUnion]
  refine ⟨?_, fun hx => ⟨P, by simp, hx⟩⟩
  rintro ⟨E, hE, hx⟩
  rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hE
  split_ifs at hE with h
  · exact h ▸ hx
  · exact absurd rfl hE

/-- **Step 1 of FA 15.9: the contraction of a null negative extremal ray.** In the setting of
`exists_isNegativeExtremalRayOf`, the ray `R` has a contraction `c : X ⟶ Z` onto a projective
variety, with `ρ(Z) + 1 = ρ(X)` and with Cartier divisors trivial on `R` descending to `Z`; every
proper curve contracted by `c` is `L`-null, `P`-negative and contained in `P`. -/
private theorem exists_isContractionOfRay {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] {K : Divisor Y} {Δ : QDivisor Y}
    {P : Mori.PrimeDivisor Y} (hA : SatisfiesAbundanceAssumptions ℂ sY K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sY (Divisor.toQDivisor K + Δ))
    (hD : IsTriviallyConnected ℂ sY 3 K Δ (Finsupp.single P 1)) :
    ∃ ε : ℚ, 0 < ε ∧
      IsKawamataLogTerminal sY 3 K
        (QDivisor.toRDivisor (Δ + ε • Divisor.toQDivisor (Finsupp.single P 1))) ∧
      ∃ R : Set (NumericalCurveClasses sY),
        IsNegativeExtremalRayOf sY
          (Divisor.toQDivisor K + (Δ + ε • Divisor.toQDivisor (Finsupp.single P 1))) R ∧
        (∀ u ∈ R, QDivisor.curveForm sY (Divisor.toQDivisor K + Δ) hA.isQCartier u = 0) ∧
      ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (c : Y ⟶ Z),
        IsContractionOfRay sY sZ R c ∧ MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        picardNumber sZ + 1 = picardNumber sY ∧
        (∀ M : Y.CartierDivisor,
          (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
            (KCartierDivisor.ofCartier ℝ M) u = 0) →
          ∃ (MR : Z.CartierDivisor)
            (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
            MMP.Intersection.LinearlyEquivalent M
              (MMP.CartierDivisor.pullback c MR hMR)) ∧
        ∀ C : ProperCurve sY, C.IsContractedBy c →
          (Divisor.toQDivisor K + Δ).intersectionNumber ℂ sY C.ι C.dim_le hA.isQCartier = 0 ∧
          (∃ hE : (Divisor.toQDivisor (Finsupp.single P 1)).IsQCartier,
            (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber ℂ sY C.ι C.dim_le hE
              < 0) ∧
          C.point ∈ P.support := by
  have hQ : IsQFactorial sY := hA.isQFactorial
  obtain ⟨ε, hε, hklt, R, hR, hRL⟩ := exists_isNegativeExtremalRayOf hA hL hD
  obtain ⟨Z, sZ, c, hc, hZ, hρ, hdesc⟩ := hklt.exists_isContractionOfRay hA.isProjectiveVariety hR
  refine ⟨ε, hε, hklt, R, hR, hRL, Z, sZ, c, hc, hZ, hρ, hdesc, fun C hC => ?_⟩
  set E : QDivisor Y := Divisor.toQDivisor (Finsupp.single P 1) with hEdef
  have hEq : E.IsQCartier := isQCartier_of_isQFactorial sY hQ E
  have hεE : (ε • E).IsQCartier := isQCartier_of_isQFactorial sY hQ _
  have hmem := (hc.isContractedBy_iff C).mp hC
  have hne := numericalClass_cycle_ne_zero hA.isProjectiveVariety C
  obtain ⟨hΘq, -, hneg⟩ := hR
  have h1 := hneg _ hmem hne
  have h2 := hRL _ hmem
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at h1 h2
  have hLC : (Divisor.toQDivisor K + Δ).intersectionNumber ℂ sY C.ι C.dim_le hA.isQCartier = 0 := by
    exact_mod_cast h2
  have h1' : Divisor.toQDivisor K + (Δ + ε • E) = (Divisor.toQDivisor K + Δ) + ε • E :=
    (add_assoc _ _ _).symm
  have h3 : (Divisor.toQDivisor K + (Δ + ε • E)).intersectionNumber ℂ sY C.ι C.dim_le hΘq =
      ((Divisor.toQDivisor K + Δ) + ε • E).intersectionNumber ℂ sY C.ι C.dim_le
        (h1' ▸ hΘq) := by
    congr 1
  rw [h3, MMP.Mori.QDivisor.intersectionNumber_add' ℂ sY C.ι C.dim_le
      (Divisor.toQDivisor K + Δ) (ε • E) hA.isQCartier hεE (h1' ▸ hΘq),
    MMP.Mori.QDivisor.intersectionNumber_smul ℂ sY C.ι C.dim_le ε E hEq hεE, hLC,
    zero_add] at h1
  have hEC : E.intersectionNumber ℂ sY C.ι C.dim_le hEq < 0 := by
    have h1'' : ε * E.intersectionNumber ℂ sY C.ι C.dim_le hEq < 0 := by exact_mod_cast h1
    exact neg_of_mul_neg_right h1'' hε.le
  refine ⟨hLC, ⟨hEq, hEC⟩, ?_⟩
  by_contra hCP
  have hCE : C.point ∉ E.supp := by
    rw [hEdef, Divisor.supp_toQDivisor]
    change C.point ∉ (DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor Y) : Set Y)
    rwa [supp_single_one]
  have h0 : 0 ≤ E := DivisorWithCoeffs.isEffective_iff_nonneg.mp
    (isEffective_toQDivisor (isEffective_single P))
  exact absurd hEC (not_lt.mpr
    (intersectionNumber_nonneg_and_eq_zero_iff sY E hEq h0 C hCE).1)

/-- **The exceptional set lies in a closed set containing the contracted curves.** For a proper
birational morphism `c : Y ⟶ Z` of varieties with `c_* 𝒪_Y = 𝒪_Z`, `Y` proper, if every proper
curve contracted by `c` lies in a closed set `S`, then so does `Ex(c)`: every closed point of
`Ex(c)` lies on a contracted curve, and closed points are dense in `Ex(c)`. -/
private theorem exceptionalSet_subset_of_forall_isContractedBy {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsVariety ℂ sY)
    (hZ : MMP.Mori.IsVariety ℂ sZ) [IsProper sY] (c : Y ⟶ Z) (hcs : c ≫ sZ = sY) [IsProper c]
    (hb : IsBirationalMorphism c) (hO : ∀ U : Z.Opens, IsIso (c.app U)) {S : Set Y}
    (hS : IsClosed S) (h : ∀ C : ProperCurve sY, C.IsContractedBy c → C.point ∈ S) :
    (Mori.exceptionalSet c : Set Y) ⊆ S := by
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [← closure_inter_closedPoints (Mori.exceptionalSet c).isClosed]
  refine closure_minimal ?_ hS
  rintro x ⟨hx, hxc⟩
  obtain ⟨C, hCc, hCi, hCd, hxC, y, hy⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hY hZ c hcs hb hO
      hxc hx
  obtain ⟨η, hη⟩ := QuasiSober.sober hCi hCc
  have hηx : η ⤳ x := hη.specializes hxC
  have hηne : η ∉ ({x} : Set Y) := by
    intro hηx'
    have hC : C = {x} := by
      rw [← hη.def, Set.mem_singleton_iff.mp hηx', (hxc : IsClosed ({x} : Set Y)).closure_eq]
    rw [hC] at hCd
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set Y)
    rw [hCd] at h0
    exact absurd h0 (by decide)
  obtain ⟨y₁, hηy₁, hy₁x, -, hy₁⟩ :=
    MMP.Fourfold.exists_isProperCurve_of_specializes sY hηx hxc hxc rfl hηne
  have hcl : closure {y₁} ⊆ C := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hCc
    rw [← hη.def]
    exact specializes_iff_mem_closure.mp hηy₁
  have hfib : ∀ x' ∈ closure ({y₁} : Set Y), c x' = y := fun x' hx' => by
    have : c x' ∈ c '' C := ⟨x', hcl hx', rfl⟩
    rwa [hy] at this
  have hy₁S := h ⟨y₁, hy₁⟩ fun x' hx' =>
    (hfib x' hx').trans (hfib y₁ (subset_closure rfl)).symm
  exact hy₁x.mem_closed hS hy₁S

set_option backward.isDefEq.respectTransparency.types false in
/-- A proper morphism `c` with `c_* 𝒪 = 𝒪` whose fibre over `c y` is `{y}` is an isomorphism over
a neighbourhood of `c y`: by Zariski's main theorem it is finite there, and a finite morphism
with `c_* 𝒪 = 𝒪` is an isomorphism. -/
private theorem mem_biregularLocus_of_preimage_singleton_eq {Y Z : Scheme.{0}} (c : Y ⟶ Z)
    [IsProper c] (hO : ∀ U : Z.Opens, IsIso (c.app U)) {y : Y} (hFy : c ⁻¹' {c y} = {y}) :
    c y ∈ biregularLocus c := by
  obtain ⟨V, hyV, hV⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton c (c y)
      (by rw [hFy]; exact Set.finite_singleton y)
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset (x := c y) (U := V) hyV
  have e := morphismRestrictRestrict c V (V.ι ⁻¹ᵁ U)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr (show U ≤ V from hUV)] at e
  have hfin : AlgebraicGeometry.IsFinite (c ∣_ U) :=
    (CategoryTheory.MorphismProperty.arrow_mk_iso_iff @AlgebraicGeometry.IsFinite e).mp
      inferInstance
  have : IsAffine U := hU
  have hbir : IsBiregular c U := by
    change CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme (c ∣_ U)
    rw [HasAffineProperty.iff_of_isAffine
      (P := CategoryTheory.MorphismProperty.isomorphisms AlgebraicGeometry.Scheme)]
    refine ⟨isAffine_of_isAffineHom (c ∣_ U), ?_⟩
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hO _)
      (Y.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage c U ⊤)).op).isIso_hom
  exact le_biregularLocus hbir hyU

/-- For a proper morphism `c` of schemes locally of finite type over `ℂ` with `c_* 𝒪 = 𝒪`, the
exceptional set of FA (the points near which `c` is not an open immersion) is the exceptional set
`Y ∖ c⁻¹(V_c)`. If `c` is an open immersion near a closed point `x`, then `{x}` is open and
closed in the connected fibre through `x`, which is therefore `{x}`, so `c` is an isomorphism over
a neighbourhood of `c x`; both sets are closed, and closed points are dense in them. -/
private theorem exceptionalSet_eq_mori_exceptionalSet {Y Z : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (c : Y ⟶ Z) [IsProper c] (hO : ∀ U : Z.Opens, IsIso (c.app U)) :
    Flips.exceptionalSet c = (Mori.exceptionalSet c : Set Y) := by
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  refine subset_antisymm (fun x hx hxM => ?_) ?_
  · refine hx ⟨c ⁻¹ᵁ biregularLocus c, by simpa using hxM, ?_⟩
    have : IsIso (c ∣_ biregularLocus c) := isBiregular_biregularLocus c
    rw [← morphismRestrict_ι]
    infer_instance
  rw [← closure_inter_closedPoints (Mori.exceptionalSet c).isClosed]
  refine closure_minimal ?_ (Flips.isClosed_exceptionalSet c)
  rintro x ⟨hxM, hxc⟩ hx
  obtain ⟨W, hxW, hW⟩ := hx
  apply hxM
  change c x ∈ biregularLocus c
  refine mem_biregularLocus_of_preimage_singleton_eq c hO ?_
  have hinj : Set.InjOn c (W : Set Y) := fun a ha b hb hab => by
    have := (W.ι ≫ c).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab
    exact congrArg Subtype.val this
  set F := c ⁻¹' {c x}
  have hFW : ∀ y ∈ F, y ∈ W → y = x := fun y hyF hyW => hinj hyW hxW hyF
  have hFc : _root_.IsConnected F := c.isConnected_preimage_singleton_of_isIso_app hO _
  refine (Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun y hyF => ?_⟩)
  by_contra hyx
  have hyW : y ∉ W := fun h => hyx (hFW y hyF h)
  obtain ⟨z, hzF, hzW, hzx⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected
    (W : Set Y)ᶜ {x} W.isOpen.isClosed_compl (hxc : IsClosed ({x} : Set Y))
    (fun a ha => by
      by_cases haW : a ∈ W
      · exact Or.inr (hFW a ha haW)
      · exact Or.inl haW)
    ⟨y, hyF, hyW⟩ ⟨x, rfl, rfl⟩
  exact hzW (Set.mem_singleton_iff.mp hzx ▸ hxW)

set_option backward.isDefEq.respectTransparency.types false in
/-- **The contraction of a ray whose curves lie in a prime divisor is birational.** If every
proper curve contracted by the contraction `c : Y ⟶ Z` of an extremal ray lies in the prime
divisor `P`, then `c` is not of fibre type, so it is birational. -/
private theorem isBirationalMorphism_of_forall_isContractedBy {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hdim : topologicalKrullDim Y = 3)
    {c : Y ⟶ Z} (hc : MMP.Fourfold.IsContraction sY sZ c) (P : Mori.PrimeDivisor Y)
    (h : ∀ C : ProperCurve sY, C.IsContractedBy c → C.point ∈ P.support) :
    IsBirationalMorphism c := by
  have hYv : MMP.Mori.IsVariety ℂ sY := hY.toIsVariety
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  haveI : IsProper sY := isProper_of_isProjectiveMorphism _ hY.isProjective
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  obtain ⟨hZv, -⟩ := hc.isNormalVariety_target
  haveI : IsIntegral Z := hZv.toIsIntegral
  have hPc : IsClosed P.support := by
    rw [← supp_single_one]; exact DivisorWithCoeffs.isClosed_supp _
  -- a closed point outside `P`
  obtain ⟨y, hyP, hyc⟩ := nonempty_inter_closedPoints (Z := P.supportᶜ)
    ⟨genericPoint Y, AlgebraicGeometry.PrimeDivisor.genericPoint_notMem_support P⟩
    hPc.isOpen_compl.isLocallyClosed
  have hyc' : IsClosed ({y} : Set Y) := hyc
  set F := c.base ⁻¹' {c y} with hF
  have hcy : IsClosed ({c y} : Set Z) := Set.image_singleton (f := c) ▸ c.isClosedMap _ hyc'
  have hFcl : IsClosed F := hcy.preimage c.continuous
  have hFc : _root_.IsConnected F := c.isConnected_preimage_singleton_of_isIso_app hc.isIso_app _
  -- the fibre through `y` is `{y}`
  have hFy : F = {y} := by
    by_contra hne
    have hsub : ¬ F ⊆ {y} := fun hs => hne (hs.antisymm (by simp [hF]))
    obtain ⟨η, hηF, hηy, hηs⟩ : ∃ η ∈ F, η ∉ ({y} : Set Y) ∧ η ⤳ y := by
      set T := F \ {y}
      have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hFcl
      by_cases hdis : (closure T ∩ {y}).Nonempty
      · obtain ⟨s, hsT, hsS⟩ := hdis
        obtain ⟨Zs, hZfin, hZcl, hZirr, hZeq⟩ :=
          TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
            (isClosed_closure : IsClosed (closure T))
        have hsub' : closure T ⊆ ⋃₀ {t ∈ Zs | (t ∩ T).Nonempty} := by
          refine closure_minimal (fun x hx => ?_) ?_
          · have : x ∈ ⋃₀ Zs := hZeq ▸ subset_closure hx
            obtain ⟨z, hz, hxz⟩ := this
            exact ⟨z, ⟨hz, x, hxz, hx⟩, hxz⟩
          · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
        obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
        obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
        have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
        refine ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hyc' hζS),
          ?_⟩
        rw [Set.mem_singleton_iff.mp hsS] at hsz
        exact hζ.specializes hsz
      · obtain ⟨x, hxF, hxS⟩ := Set.not_subset.mp hsub
        obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
          isClosed_closure hyc' (fun a ha => by
            by_cases haS : a ∈ ({y} : Set Y)
            · exact Or.inr haS
            · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
          ⟨x, hxF, subset_closure (show x ∈ T from ⟨hxF, hxS⟩)⟩
          ⟨y, by simp [hF], rfl⟩
        exact (hdis ⟨w, hwT, hwS⟩).elim
    obtain ⟨y₁, hηy₁, hy₁y, -, hy₁⟩ :=
      MMP.Fourfold.exists_isProperCurve_of_specializes sY hηs hyc' hyc' rfl hηy
    have hcl : closure ({y₁} : Set Y) ⊆ F :=
      closure_minimal (Set.singleton_subset_iff.mpr (hηy₁.mem_closed hFcl hηF)) hFcl
    have hy₁P := h ⟨y₁, hy₁⟩ fun x' hx' =>
      (show c x' = c y from hcl hx').trans (show c y₁ = c y from hcl (subset_closure rfl)).symm
    exact hyP (hy₁y.mem_closed hPc hy₁P)
  -- so `c` is finite, hence an isomorphism, over a neighbourhood of `c y`
  have hbir : c y ∈ biregularLocus c :=
    mem_biregularLocus_of_preimage_singleton_eq c hc.isIso_app hFy
  have : IsIso (c ∣_ biregularLocus c) := isBiregular_biregularLocus c
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE c _ _ ⟨y, hbir⟩ ⟨c y, hbir⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- On an integral Noetherian normal scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (A : Y.CartierDivisor) :
    ∃ w : Divisor Y, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian Y := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (Y.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (Y.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- The order of the principal Cartier divisor `div(f)` along a prime divisor `P` is `ord_P f`. -/
private theorem isOrderAlong_div {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (f : Y.functionFieldˣ) (P : Mori.PrimeDivisor Y) :
    MMP.Intersection.IsOrderAlong (MMP.Intersection.principalDivisor
        (Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom f))
      (MMP.Intersection.primeDivisorSubvariety P)
      (P.ord (Units.map MMP.Intersection.functionFieldToRationalFunctions.toMonoidHom f)) := by
  set c := Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := Y) ⊤).toMonoidHom f
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier (MMP.Intersection.principalDivisor c)
  have hat : MMP.Intersection.IsLocalEquationAt (MMP.Intersection.principalDivisor c)
      P.genericPoint (Y.totalQuotientSheaf.presheaf.germ ⊤ P.genericPoint trivial
        (MMP.CartierDivisorSheaf.ofFunctionField ⊤ (f : Y.functionField))) :=
    ⟨⊤, trivial, c, MMP.Intersection.isLocalEquationOn_principalDivisor c, rfl⟩
  have h1 := MMP.Intersection.ord_eq_coeff_of_isLocalEquationAt hw P rfl hat
  erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    at h1
  have h2 : P.ord (Units.map MMP.Intersection.functionFieldToRationalFunctions.toMonoidHom f) =
      Scheme.ord (f : Y.functionField) P.genericPoint := by
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    congr 1
    exact MMP.Intersection.evalFF_functionFieldToRationalFunctions P.component _
  rw [h2, h1]
  exact hw P

/-- The degree form on `N₁(X)` of an invertible sheaf depends only on its isomorphism class. -/
private theorem numericalCurveClasses_degree_eq_of_iso {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {L L' : Y.Modules} [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L'] (e : L ≅ L') :
    NumericalCurveClasses.degree sY L = NumericalCurveClasses.degree sY L' := by
  have h : OneCycle.degree ℝ sY L = OneCycle.degree ℝ sY L' := by
    rw [OneCycle.degree, OneCycle.degree]
    congr 2
    funext C
    exact congrArg _ (degreeOn_eq_of_iso ℂ sY C.ι C.dim_le e)
  refine LinearMap.ext fun u => ?_
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sY u
  rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass, h]

/-- Regarding a divisor as a `ℚ`-divisor commutes with the birational transform. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{0}} (f : X.RationalMap Y)
    (D : Divisor X) :
    Mori.RationalMap.transformDivisor f (Divisor.toQDivisor D) =
      Divisor.toQDivisor (Mori.RationalMap.transformDivisor f D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single P n =>
    have h : ∀ {Z : Scheme.{0}} (E : Mori.PrimeDivisor Z) (r : ℤ),
        Divisor.toQDivisor (Finsupp.single E r) = Finsupp.single E (r : ℚ) := by
      intro Z E r
      ext E'
      change ((Finsupp.single E r E' : ℤ) : ℚ) = Finsupp.single E (r : ℚ) E'
      by_cases hE : E = E' <;> simp [Finsupp.single_apply, hE]
    rw [h, Mori.RationalMap.transformDivisor_single, Mori.RationalMap.transformDivisor_single]
    rcases Mori.RationalMap.transformPrimeDivisor f P with _ | E
    · simp
    · simp [h]

/-- Isomorphic divisorial sheaves on a normal integral Noetherian scheme give linearly equivalent
divisors. -/
private theorem linearlyEquivalent_of_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {D D' : Divisor Y}
    (e : D.divisorialSheaf ≅ D'.divisorialSheaf) : D.LinearlyEquivalent D' :=
  MMP.Threefold.Mori.CanonUniq.linearlyEquivalent_of_iso (U := ⊤) (fun _ => trivial)
    ((Scheme.Modules.restrictFunctor (⊤ : Y.Opens).ι).mapIso e)

/-- **Step 2 of FA 15.9: the adjoint descends.** In the divisorial case, `K + Δ` is
`ℚ`-linearly equivalent to the pull-back of `K' + Δ'`, `K' = c_* K`, `Δ' = c_* Δ`: a Cartier
multiple `r(K + Δ)` is trivial on `R`, so it is `c^* M_R` (`hdesc`), and `c_*(r(K + Δ)) = M_R`. -/
private theorem exists_isPullback_of_exceptionalSet_eq
    {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ} (hε : 0 < ε)
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R)
    (hRL : ∀ u ∈ R, QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + s.Δ) hs.hA.isQCartier u = 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {c : s.Y ⟶ Z}
    (hc : IsContractionOfRay s.sY sZ R c) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hρ : picardNumber sZ + 1 = picardNumber s.sY)
    (hdesc : ∀ M : s.Y.CartierDivisor,
      (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ M) u = 0) →
      ∃ (MR : Z.CartierDivisor)
        (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
        MMP.Intersection.LinearlyEquivalent M
          (MMP.CartierDivisor.pullback c MR hMR))
    (hcurves : ∀ C : ProperCurve s.sY, C.IsContractedBy c →
      (Divisor.toQDivisor s.K + s.Δ).intersectionNumber ℂ s.sY C.ι C.dim_le hs.hA.isQCartier = 0 ∧
      (∃ hE : (Divisor.toQDivisor (Finsupp.single s.P 1)).IsQCartier,
        (Divisor.toQDivisor (Finsupp.single s.P 1)).intersectionNumber ℂ s.sY C.ι C.dim_le hE
          < 0) ∧
      C.point ∈ s.P.support)
    (hb : IsBirationalMorphism c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) = s.P.support) [IsIntegral Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ] :
    ∃ (hc' : ∀ Z' : irreducibleComponents s.Y,
        c (componentGenericPoint s.Y Z') ∉
          (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
            Mori.RationalMap.transformDivisor c.toRationalMap s.Δ).supp)
        (B : QDivisor s.Y),
      (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
          Mori.RationalMap.transformDivisor c.toRationalMap s.Δ).IsPullback c hc' B ∧
        (Divisor.toQDivisor s.K + s.Δ).QLinearlyEquivalent B := by
  have hYp := hs.hA.isProjectiveVariety
  have hZv : MMP.Mori.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : IsDominant c := hb.isDominant
  set B : QDivisor s.Y := Divisor.toQDivisor s.K + s.Δ with hBdef
  have hBq : B.IsQCartier := hs.hA.isQCartier
  set m₀ : ℕ := B.cartierIndex hBq with hm₀def
  have hm₀ : 0 < m₀ := QDivisor.cartierIndex_pos hBq
  set D₀ : Divisor s.Y := (B.cartierIndexSMul hBq : Divisor s.Y) with hD₀def
  have hD₀ : Divisor.toQDivisor D₀ = (m₀ : ℤ) • B := QDivisor.toQDivisor_cartierIndexSMul B hBq
  have hD₀c : D₀.IsCartier := (B.cartierIndexSMul hBq).2
  haveI := hD₀c.isInvertibleModule_divisorialSheaf
  -- a Cartier divisor `M` in Fulton's sense with `𝒪(M) ≅ 𝒪(m₀ (K + Δ))`
  obtain ⟨M, ⟨eM⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D₀.divisorialSheaf
  -- `M` is trivial on `R`
  have hMR0 : ∀ u ∈ R, NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ M) u = 0 := by
    intro u hu
    have h0 := hRL u hu
    have hform : QDivisor.curveForm s.sY B hBq u =
        ((1 / (m₀ : ℚ) : ℚ) : ℝ) * NumericalCurveClasses.degree s.sY D₀.divisorialSheaf u := by
      rw [QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
        Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index (by simp)]
      rfl
    rw [hform] at h0
    have hm₀' : ((1 / (m₀ : ℚ) : ℚ) : ℝ) ≠ 0 := by
      have : (0 : ℚ) < 1 / (m₀ : ℚ) := by positivity
      exact_mod_cast this.ne'
    rw [NumericalCurveClasses.intersectionNumber_ofCartier,
      ← numericalCurveClasses_degree_eq_of_iso eM]
    exact (mul_eq_zero.mp h0).resolve_left hm₀'
  obtain ⟨MR, hMR, hlin⟩ := hdesc M hMR0
  obtain ⟨g, hg⟩ := MMP.Intersection.mem_principalSubgroup_iff.mp
    (MMP.Intersection.linearlyEquivalent_equivalence.symm hlin)
  have hbij := MMP.CartierDivisorSheaf.ofFunctionField_bijective (X := s.Y) ⊤
    ⟨genericPoint s.Y, trivial⟩
  set f : s.Y.functionFieldˣ :=
    Units.map (RingEquiv.ofBijective _ hbij).symm.toMonoidHom g with hfdef
  have hf : MMP.CartierDivisor.pullback c MR hMR = M + MMP.Intersection.principalDivisor
      (Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := s.Y) ⊤).toMonoidHom f) := by
    have hgf : Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := s.Y) ⊤).toMonoidHom f =
        g := Units.ext ((RingEquiv.ofBijective _ hbij).apply_symm_apply (g : _))
    rw [hgf, hg, add_sub_cancel]
  -- the Weil divisor `G` of `M_R` on `Z`, and its pull-back `G'`
  obtain ⟨G, hG⟩ := exists_isWeilDivisorOfCartier MR
  have hGc : G.IsCartier := hG.isCartier
  have hBG := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' c G
  obtain ⟨G', hG'⟩ := hGc.exists_isPullback hBG
  -- the Weil divisors of `M` and `c^* M_R`
  obtain ⟨wM, hwM⟩ := exists_isWeilDivisorOfCartier M
  obtain ⟨wP, hwP⟩ := exists_isWeilDivisorOfCartier
    (MMP.CartierDivisor.pullback c MR hMR)
  have h1 : D₀.LinearlyEquivalent wM :=
    linearlyEquivalent_of_divisorialSheaf_iso (eM ≪≫ hwM.sheafIsoDivisorialSheaf)
  haveI := hGc.isInvertibleModule_divisorialSheaf
  have h2 : wP.LinearlyEquivalent G' :=
    linearlyEquivalent_of_divisorialSheaf_iso (hwP.sheafIsoDivisorialSheaf.symm ≪≫
      MMP.CartierDivisor.pullbackSheafIso c MR hMR ≪≫
      (Scheme.Modules.pullback c).mapIso hG.sheafIsoDivisorialSheaf ≪≫
      (hG'.divisorialSheafIso (hBc := hGc)).symm)
  set φf := Units.map MMP.Intersection.functionFieldToRationalFunctions.toMonoidHom f
  have h3 : wP = wM + principalDivisor φf := by
    refine Finsupp.ext fun P => ?_
    have hP := hwP P
    rw [hf] at hP
    have := hP.unique ((hwM P).add (isOrderAlong_div f P))
    change wP.coeff P = (wM + principalDivisor φf).coeff P
    rw [this, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have h4 : D₀.LinearlyEquivalent G' := by
    refine h1.trans (Divisor.LinearlyEquivalent.trans ?_ h2)
    refine ⟨φf⁻¹, ?_⟩
    rw [h3, Mori.principalDivisor_inv]
    abel
  obtain ⟨φ, hφ⟩ := h4
  obtain ⟨ψ, hψ, hψeq⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hb φ
  -- `m₀ (K + Δ)` is the pull-back of the Cartier divisor `H = G + div ψ`
  set H : Divisor Z := G + principalDivisor ψ with hHdef
  have hHc : H.IsCartier := hGc.add (Divisor.isCartier_principalDivisor ψ)
  have hBH := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' c H
  have hpH : H.IsPullback c hBH D₀ := by
    have := hG'.add hGc (Divisor.isCartier_principalDivisor ψ) hBH
      (Divisor.isPullback_principalDivisor ψ hψ)
    rw [hψeq, ← hφ, add_sub_cancel] at this
    exact this
  -- push-forward: `c_* (m₀ (K + Δ)) = H`
  have hZn : IsNormalVariety ℂ sZ := hc.isNormalVariety_target
  have hYn : IsNormalVariety ℂ (c ≫ sZ) := by
    rw [hc.comp_eq]
    exact ⟨hYp.toIsVariety, inferInstance⟩
  have hTH : Mori.RationalMap.transformDivisor c.toRationalMap D₀ = H :=
    MMP.Positivity.transformDivisor_of_isPullback_divisor hZn hYn hb hHc hpH
  set B' : QDivisor Z :=
    Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
    Mori.RationalMap.transformDivisor c.toRationalMap s.Δ with hB'def
  have hHB' : Divisor.toQDivisor H = (m₀ : ℤ) • B' := by
    rw [← hTH, ← transformDivisor_toQDivisor, hD₀, map_zsmul, hBdef, map_add,
      transformDivisor_toQDivisor]
  have hB'q : B'.IsQCartier :=
    ⟨(m₀ : ℤ), by exact_mod_cast hm₀.ne', H, hHB', hHc⟩
  have hc' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' c B'
  have hpb := QDivisor.isPullback_pullback hB'q hc'
  have hBeq : B'.pullback hB'q hc' = B := by
    obtain ⟨D'', hD'', hpD''⟩ := hpb m₀ hm₀ H hHB' hHc
    have hD''eq : D'' = D₀ := hpD''.eq hHc hpH
    rw [hD''eq, hD₀] at hD''
    exact smul_right_injective _ (by exact_mod_cast hm₀.ne' : (m₀ : ℤ) ≠ 0) hD''.symm
  exact ⟨hc', B, hBeq ▸ hpb, QDivisor.QLinearlyEquivalent.refl _⟩

/-- A birational morphism whose exceptional set is a prime divisor `P` has no transform of `P`:
`P` is exceptional over the target. -/
private theorem transformPrimeDivisor_eq_none_of_exceptionalSet_eq {Y Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {c : Y ⟶ Z} [IsProper c]
    (hY : IsNormalVariety ℂ (c ≫ sZ)) (hb : IsBirationalMorphism c) {P : Mori.PrimeDivisor Y}
    (hP : Flips.exceptionalSet c = (P.support : Set Y)) :
    Mori.RationalMap.transformPrimeDivisor c.toRationalMap P = none := by
  have hexcP : IsExceptionalPrimeDivisor sZ c P := by
    refine ⟨hY, hb, inferInstance, ?_⟩
    refine (ProperDivisorOver.support_subset_exceptionalSet_iff hZ _).mp ?_
    change (P.support : Set Y) ⊆ Flips.exceptionalSet c
    rw [hP]
  have := hZ.1.toIsIntegral
  have := hZ.1.toLocallyOfFiniteType
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI : IsIntegral Y := hY.1.toIsIntegral
  rcases h : Mori.RationalMap.transformPrimeDivisor (X := Y) c.toRationalMap P with _ | Q
  · rfl
  exfalso
  have hgQ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff c P Q).mp h
  obtain ⟨hY', hb', hp', hexc⟩ := hexcP
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint] at hexc
  change topologicalKrullDim (closure {c P.genericPoint} : Set Z) + 2 ≤ _ at hexc
  have hdim := topologicalKrullDim_closure_singleton_add_coheight sZ (c P.genericPoint)
  have hn := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ sZ (c P.genericPoint)
  rw [hgQ, Q.coheight_genericPoint] at hdim
  rw [hgQ] at hexc hn
  rw [← hdim, hn] at hexc
  generalize (Stacks.Chow.relativeDimension _ _ _).toNat = m at hexc
  push_cast at hexc
  have := Nat.cast_le.mp (WithBot.coe_le_coe.mp hexc)
  simp only at this
  omega

/-- **The klt part of Step 2 of FA 15.9.** In the divisorial case, `(X', Δ')`, `Δ' = c_* Δ`,
`K' = c_* K`, is a klt `ℚ`-factorial pair: the contraction is a `(K + Δ + εP)`-negative
divisorial contraction (KM 3.43(1), `MMP.Mori.IsDivisorialContraction.isKltPair_transformDivisor`)
and `c_* P = 0`. -/
private theorem isKltPair_transformDivisor_of_exceptionalSet_eq
    {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ} (hε : 0 < ε)
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {c : s.Y ⟶ Z}
    (hc : IsContractionOfRay s.sY sZ R c) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hb : IsBirationalMorphism c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) = s.P.support) [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] :
    Mori.IsKltPair sZ 3 (Mori.RationalMap.transformDivisor c.toRationalMap s.K)
      (Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) := by
  classical
  have hYp := hs.hA.isProjectiveVariety
  have hYn : IsNormalVariety ℂ s.sY := hs.hA.isQFactorial.1
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hdiv : IsDivisorialContraction ℂ s.sY sZ R c :=
    { isNormalVariety := hYn
      isExtremalRay := hR.2.1
      isContractionOfFace :=
        { isProjectiveVariety_source := hYp
          isProjectiveVariety_target := hZ
          comp_eq := hc.comp_eq
          isExtremalFace := hR.2.1.1
          isContractedBy_iff := hc.isContractedBy_iff
          isIso_app := hc.isIso_app }
      isBirationalMorphism := hb
      exists_primeDivisor := ⟨s.P, hEx⟩ }
  set Θ : QDivisor s.Y := s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1) with hΘdef
  have hΘ0 : 0 ≤ Θ := fun E => by
    have := (hklt.1.isBoundary E).1
    change (0 : ℝ) ≤ ((Θ E : ℚ) : ℝ) at this
    exact_mod_cast this
  have hkltM : Mori.IsKltPair s.sY 3 s.K Θ :=
    (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair s.sY 3 s.K Θ hYn hklt.2.1
      hklt.1.isBoundary (isQCartier_of_isQFactorial s.sY hs.hA.isQFactorial _)).1 hklt
  have hZn : IsNormalVariety ℂ sZ := hc.isNormalVariety_target
  have hnone : Mori.RationalMap.transformPrimeDivisor c.toRationalMap s.P = none :=
    transformPrimeDivisor_eq_none_of_exceptionalSet_eq hZn (by rw [hc.comp_eq]; exact hYn) hb
      (by rw [exceptionalSet_eq_mori_exceptionalSet (sY := s.sY) c hc.isIso_app, hEx])
  have hΘt : Mori.RationalMap.transformDivisor c.toRationalMap Θ =
      Mori.RationalMap.transformDivisor c.toRationalMap s.Δ := by
    rw [hΘdef, map_add, MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one,
      Finsupp.smul_single, Mori.RationalMap.transformDivisor_single_of_eq_none hnone, add_zero]
  have := MMP.Mori.IsDivisorialContraction.isKltPair_transformDivisor hs.hA.isQFactorial hR hdiv
    (Or.inl hΘ0) hkltM
  rwa [hΘt] at this

private theorem eq_of_isIso_morphismRestrict {A Z : Scheme.{0}} (h : A ⟶ Z) (V : Z.Opens)
    [IsIso (h ∣_ V)] {x y : A} (hx : h x ∈ V) (hy : h y ∈ V) (hxy : h x = h y) : x = y := by
  have h₁ : (h ∣_ V) ⟨x, show x ∈ h ⁻¹ᵁ V from hx⟩ = (h ∣_ V) ⟨y, show y ∈ h ⁻¹ᵁ V from hy⟩ :=
    Subtype.ext ((morphismRestrict_base_coe h V ⟨x, show x ∈ h ⁻¹ᵁ V from hx⟩).trans
      (hxy.trans (morphismRestrict_base_coe h V ⟨y, show y ∈ h ⁻¹ᵁ V from hy⟩).symm))
  exact congrArg Subtype.val ((h ∣_ V).isOpenEmbedding.injective h₁)

/-- **Steps 2 and 4 of FA 15.9: the target satisfies the assumptions of 15.4.** In the divisorial
case, `X'` is a projective `ℚ`-factorial threefold
(`MMP.Flips.IsKawamataLogTerminal.isQFactorial_of_isContractionOfRay`),
`(X', Δ')` is klt (discrepancies do not decrease under the `(K + Δ + εP)`-negative divisorial
contraction), `K' + Δ'` is nef (every curve of `X'` is the image of a curve of `X`), the linear
systems `|m(K + Δ)|` and `|m(K' + Δ')|` have the same dimension (`c_* 𝒪 = 𝒪`), and the log
elliptic fibration of `X`, restricted to the complement of the closure of the image of `P`, is
one on `X'`. -/
private theorem satisfiesAbundanceAssumptions_of_exceptionalSet_eq
    {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ} (hε : 0 < ε)
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R)
    (hRL : ∀ u ∈ R, QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + s.Δ) hs.hA.isQCartier u = 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {c : s.Y ⟶ Z}
    (hc : IsContractionOfRay s.sY sZ R c) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hρ : picardNumber sZ + 1 = picardNumber s.sY)
    (hdesc : ∀ M : s.Y.CartierDivisor,
      (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ M) u = 0) →
      ∃ (MR : Z.CartierDivisor)
        (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
        MMP.Intersection.LinearlyEquivalent M
          (MMP.CartierDivisor.pullback c MR hMR))
    (hcurves : ∀ C : ProperCurve s.sY, C.IsContractedBy c →
      (Divisor.toQDivisor s.K + s.Δ).intersectionNumber ℂ s.sY C.ι C.dim_le hs.hA.isQCartier = 0 ∧
      (∃ hE : (Divisor.toQDivisor (Finsupp.single s.P 1)).IsQCartier,
        (Divisor.toQDivisor (Finsupp.single s.P 1)).intersectionNumber ℂ s.sY C.ι C.dim_le hE
          < 0) ∧
      C.point ∈ s.P.support)
    (hb : IsBirationalMorphism c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) = s.P.support) [IsIntegral Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [LocallyOfFiniteType sZ] [QuasiCompact sZ] :
    SatisfiesAbundanceAssumptions ℂ sZ (Mori.RationalMap.transformDivisor c.toRationalMap s.K)
      (Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) := by
  classical
  have hYp := hs.hA.isProjectiveVariety
  have hZv : MMP.Mori.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : MMP.Mori.IsVariety ℂ s.sY := hYp.toIsVariety
  haveI : MMP.Mori.IsVariety ℂ sZ := hZv
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hZn : IsNormalVariety ℂ sZ := hc.isNormalVariety_target
  have hQ : IsQFactorial sZ :=
    IsKawamataLogTerminal.isQFactorial_of_isContractionOfRay hklt hYp hs.hA.isQFactorial hR hc hb
      ⟨s.P, hEx⟩
  have hkltM := isKltPair_transformDivisor_of_exceptionalSet_eq hs hε hklt hR hc hZ hb hEx
  have hΔ0 : 0 ≤ s.Δ := fun E => by
    have := (hs.hA.isBoundary E).1
    change (0 : ℝ) ≤ ((s.Δ E : ℚ) : ℝ) at this
    exact_mod_cast this
  have hB : IsBoundary (QDivisor.toRDivisor
      (Mori.RationalMap.transformDivisor c.toRationalMap s.Δ)) := fun E => by
    refine ⟨?_, ?_⟩
    · have := Mori.RationalMap.transformDivisor_nonneg c.toRationalMap hΔ0 E
      change (0 : ℝ) ≤ (((Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) E : ℚ) : ℝ)
      exact_mod_cast this
    · have h := hkltM.2.2 E
      change Int.floor ((Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) E) ≤ 0 at h
      have := Int.floor_le_iff.mp h
      change (((Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) E : ℚ) : ℝ) ≤ 1
      have : (Mori.RationalMap.transformDivisor c.toRationalMap s.Δ) E < 1 := by
        exact_mod_cast this
      exact_mod_cast this.le
  have hYn' : IsNormalVariety ℂ (c ≫ sZ) := by rw [hc.comp_eq]; exact hs.hA.isQFactorial.1
  refine
    { isProjectiveVariety := hZ
      isQFactorial := hQ
      dim_eq := ?_
      isBoundary := hB
      isKawamataLogTerminal :=
        (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sZ 3 _ _ hZn hkltM.1.2.1 hB
          hkltM.1.2.2).2 hkltM
      isNef := ?_
      exists_two_le_h0 := ?_
      exists_isLogEllipticFiberSpace := ?_ }
  · rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sY hb]
    exact hs.hA.dim_eq
  · -- (15.4.1): `K + Δ ∼_ℚ c^*(K' + Δ')` is nef, and nefness descends along `c`
    haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
    haveI : Surjective c := ⟨hc.surjective⟩
    obtain ⟨hc', B, hpull, hlin⟩ :=
      exists_isPullback_of_exceptionalSet_eq hs hε hklt hR hRL hc hZ hρ hdesc hcurves hb hEx
    have hBn : QDivisor.IsNef ℂ s.sY B :=
      QDivisor.isNef_of_qLinearlyEquivalent (isQCartier_of_isQFactorial s.sY hs.hA.isQFactorial)
        hlin hs.hA.isNef
    exact QDivisor.isNef_of_isPullback_of_surjective c hc.comp_eq
      (isQCartier_of_isQFactorial sZ hQ _) hpull hBn
  · -- (15.4.2): sections of `m(K + Δ)` push forward to sections of `m(K' + Δ')`
    haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
    have h := exists_two_le_h0_transformDivisor hZn hYn' hb hQ.2
      (L := Divisor.toQDivisor s.K + s.Δ) (by rw [hc.comp_eq]; exact hs.hA.exists_two_le_h0)
    rwa [map_add, MMP.Mori.transformDivisor_toQDivisor hZn hYn' hb] at h
  · -- (15.4.3): the fibration, restricted over the complement of the closure of the image of `P`,
    -- avoids `P = Ex(c)`, where `c` is an isomorphism
    obtain ⟨U, hU, W, sW, fU, hfU⟩ := hs.hA.exists_isLogEllipticFiberSpace
    have hnd := MMP.Flips.not_dense_image_of_isTriviallyConnected s.sY hs.hA U hU sW fU hfU s.P
      hs.hD
    let W₀ : W.Opens := ⟨(closure (fU '' (U.ι ⁻¹' (s.P.support : Set s.Y))))ᶜ,
      isClosed_closure.isOpen_compl⟩
    have hW₀ : (W₀ : Set W).Nonempty :=
      Set.nonempty_compl.mpr fun h => hnd (dense_iff_closure_eq.mpr h)
    set V := biregularLocus c with hVdef
    haveI hViso : IsIso (c ∣_ V) := isBiregular_biregularLocus c
    have hnotP : ∀ x : (fU ⁻¹ᵁ W₀).toScheme, U.ι x.1 ∉ (s.P.support : Set s.Y) := by
      intro x hx
      exact x.2 (subset_closure ⟨x.1, hx, rfl⟩)
    have hrange : Set.range ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) ⊆ Set.range (c ⁻¹ᵁ V).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      by_contra hx
      have hmem : ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) x ∈ (Mori.exceptionalSet c : Set s.Y) := hx
      rw [hEx] at hmem
      exact hnotP x hmem
    let a := IsOpenImmersion.lift (c ⁻¹ᵁ V).ι ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) hrange
    have ha : a ≫ (c ⁻¹ᵁ V).ι = (fU ⁻¹ᵁ W₀).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion (a ≫ (c ⁻¹ᵁ V).ι) := by rw [ha]; infer_instance
    haveI : IsOpenImmersion a := IsOpenImmersion.of_comp a (c ⁻¹ᵁ V).ι
    let j : (fU ⁻¹ᵁ W₀).toScheme ⟶ Z := (fU ⁻¹ᵁ W₀).ι ≫ U.ι ≫ c
    have hj' : a ≫ (c ∣_ V) ≫ V.ι = j := by
      rw [morphismRestrict_ι, ← Category.assoc, ha, Category.assoc]
    haveI : IsOpenImmersion j := by rw [← hj']; infer_instance
    have hj : j ≫ sZ = (fU ⁻¹ᵁ W₀).ι ≫ U.ι ≫ s.sY := by
      simp only [j, Category.assoc, hc.comp_eq]
    have hcoeff : ∀ Q : Mori.PrimeDivisor (fU ⁻¹ᵁ W₀).toScheme,
        (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
            Mori.RationalMap.transformDivisor c.toRationalMap s.Δ).coeff
            (OpenWeilRestriction.primeDivisorMap j Q) =
          (Divisor.toQDivisor (DivisorWithCoeffs.restrict U.ι s.K) +
            DivisorWithCoeffs.restrict U.ι s.Δ).coeff
              (OpenWeilRestriction.primeDivisorMap (fU ⁻¹ᵁ W₀).ι Q) := by
      intro Q
      rw [MMP.Flips.restrict_ι_eq_restrictOpen U s.K, MMP.Flips.restrict_ι_eq_restrictOpen U s.Δ]
      set E := OpenWeilRestriction.primeDivisorMap U.ι
        (OpenWeilRestriction.primeDivisorMap (fU ⁻¹ᵁ W₀).ι Q) with hE
      have hEgen : E.genericPoint = U.ι ((fU ⁻¹ᵁ W₀).ι Q.genericPoint) := by
        rw [hE, OpenWeilRestriction.genericPoint_primeDivisorMap,
          OpenWeilRestriction.genericPoint_primeDivisorMap]
      have hQgen : (OpenWeilRestriction.primeDivisorMap j Q).genericPoint = c E.genericPoint := by
        rw [OpenWeilRestriction.genericPoint_primeDivisorMap, hEgen]
        rfl
      obtain ⟨E₀, hE₀, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
        hZn hYn' hb (OpenWeilRestriction.primeDivisorMap j Q)
      have hEV : c E.genericPoint ∈ V := by
        by_contra hc0
        have : E.genericPoint ∈ (Mori.exceptionalSet c : Set s.Y) := hc0
        rw [hEx, hEgen] at this
        exact hnotP Q.genericPoint this
      have hE₀Q : c E₀.genericPoint = c E.genericPoint := hE₀.trans hQgen
      have hE₀E : E₀ = E :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_isIso_morphismRestrict c V (by rw [hE₀Q]; exact hEV) hEV hE₀Q)
      rw [← MMP.Mori.transformDivisor_toQDivisor hZn hYn' hb, ← map_add]
      change (Mori.RationalMap.transformDivisor c.toRationalMap (Divisor.toQDivisor s.K + s.Δ))
        (OpenWeilRestriction.primeDivisorMap j Q) = _
      rw [htr, hE₀E]
      rfl
    obtain ⟨U', hU', fU', hfU'⟩ := MMP.Flips.IsLogEllipticFiberSpace.exists_of_isOpenImmersion hfU
      W₀ hW₀ hZn hkltM.1.2.1 hkltM.1.2.2 hB j hj hcoeff
    exact ⟨U', hU', W₀.toScheme, W₀.ι ≫ sW, fU', hfU'⟩

/-- **Step 2 of FA 15.9: the divisorial case.** If the contraction `c` of the null negative ray
has exceptional set `P`, then `c` is the final contraction of the chain: `X'` is a projective
`ℚ`-factorial threefold, `(X', c_* Δ)` is klt with `K + Δ ∼_ℚ c^*(K' + Δ')`, the conditions
(15.4.1)–(15.4.3) pass to `X'`, and `ρ(X') + 1 = ρ(X)`. -/
private theorem isFinal_of_exceptionalSet_eq
    {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ} (hε : 0 < ε)
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R)
    (hRL : ∀ u ∈ R, QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + s.Δ) hs.hA.isQCartier u = 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {c : s.Y ⟶ Z}
    (hc : IsContractionOfRay s.sY sZ R c) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hρ : picardNumber sZ + 1 = picardNumber s.sY)
    (hdesc : ∀ M : s.Y.CartierDivisor,
      (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ M) u = 0) →
      ∃ (MR : Z.CartierDivisor)
        (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
        MMP.Intersection.LinearlyEquivalent M
          (MMP.CartierDivisor.pullback c MR hMR))
    (hcurves : ∀ C : ProperCurve s.sY, C.IsContractedBy c →
      (Divisor.toQDivisor s.K + s.Δ).intersectionNumber ℂ s.sY C.ι C.dim_le hs.hA.isQCartier = 0 ∧
      (∃ hE : (Divisor.toQDivisor (Finsupp.single s.P 1)).IsQCartier,
        (Divisor.toQDivisor (Finsupp.single s.P 1)).intersectionNumber ℂ s.sY C.ι C.dim_le hE
          < 0) ∧
      C.point ∈ s.P.support)
    (hb : IsBirationalMorphism c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) = s.P.support) : s.IsFinal := by
  have hYp := hs.hA.isProjectiveVariety
  have hZv : MMP.Mori.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZv.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hc.isNormalVariety_target.2
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : MMP.Mori.IsVariety ℂ s.sY := hYp.toIsVariety
  haveI : MMP.Mori.IsVariety ℂ sZ := hZv
  have hbc : IsBirationalContraction ℂ sZ s.sY c :=
    { isVariety_target := hZv
      isVariety_source := hYp.toIsVariety
      comp_eq := hc.comp_eq
      isProper := inferInstance
      isIso_app := hc.isIso_app
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sY hb).symm }
  refine ⟨Z, sZ, c, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hbc, hb, ?_,
    exists_isPullback_of_exceptionalSet_eq hs hε hklt hR hRL hc hZ hρ hdesc hcurves hb hEx, hρ,
    satisfiesAbundanceAssumptions_of_exceptionalSet_eq hs hε hklt hR hRL hc hZ hρ hdesc hcurves hb
      hEx⟩
  rw [exceptionalSet_eq_mori_exceptionalSet (sY := s.sY) c hc.isIso_app, hEx, supp_single_one]

/-! ### Step 3: the small case -/

/-- A point of a closed set properly contained in a prime divisor `P` is a proper specialization of
the generic point of `P`, so it has coheight at least two. -/
private theorem two_le_coheight_of_mem_of_ssubset {Y : Scheme.{0}} {P : Mori.PrimeDivisor Y}
    {S : Set Y} (hS : IsClosed S) (hSP : S ⊂ P.support) {y : Y} (hy : y ∈ S) :
    2 ≤ Order.coheight y := by
  have hyP : y ∈ P.support := hSP.1 hy
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyP
  have hηy : P.genericPoint ⤳ y := specializes_iff_mem_closure.mpr hyP
  have hne : P.genericPoint ≠ y := by
    rintro rfl
    apply hSP.2
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hy)
  have hle : y ≤ P.genericPoint := hηy
  have hlt : y < P.genericPoint :=
    lt_of_le_not_ge hle fun h => hne (Specializes.antisymm hηy h).eq
  have h := Order.coheight_add_one_le hlt
  rwa [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h

/-- A `ℚ`-Cartier divisor of degree `0` on every curve contracted by `f` is numerically
`f`-trivial. -/
private theorem isNumericallyTrivialOver_of_intersectionNumber_eq_zero {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    {f : X ⟶ Y} {L : QDivisor X} (hL : L.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      L.intersectionNumber ℂ sX C.ι C.dim_le hL = 0) :
    IsNumericallyTrivialOver ℂ sX f (QDivisor.toRDivisor L) := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hL.exists_pos
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpres : QDivisor.toRDivisor L = ∑ j : Fin 1, (fun _ => 1 / (m : ℝ)) j •
      Divisor.toRDivisor ((fun _ => E) j) := by
    ext P
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor]
    have h1 := congrArg (fun D : QDivisor X => D.coeff P) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at h1
    have h3 : ((E.coeff P : ℤ) : ℝ) = (m : ℝ) * (L.coeff P : ℝ) := by exact_mod_cast h1
    rw [h3, smul_eq_mul]
    field_simp
  refine ⟨⟨1, fun _ => 1 / (m : ℝ), fun _ => E, fun _ => hEc, by
      rw [hpres]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C (fun _ => 1 / (m : ℝ))
      (fun _ => E) (fun _ => hEc) hpres h₁,
    MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) (fun j => j.elim0) (by simp) h₂]
  have h0 := h C hC
  rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le L hL hm E hEc hE] at h0
  have hd : E.degreeOn ℂ sX C.ι C.dim_le hEc = 0 := by
    rcases div_eq_zero_iff.mp h0 with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 (by exact_mod_cast hm.ne')
  simp [hd]

/-- The pull-back of a Cartier divisor has degree `0` on every curve contracted by the morphism. -/
private theorem degreeOn_eq_zero_of_isPullback_of_isContractedBy {V W : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} [QuasiCompact sV] [CompactSpace V]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] [IsSeparated sW] [LocallyOfFiniteType sW] {u : V ⟶ W} (hu : u ≫ sW = sV)
    {M : Divisor W} (hM : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ M.supp}
    {MV : Divisor V} (hp : M.IsPullback u hB MV) (C : ProperCurve sV) (hC : C.IsContractedBy u) :
    MV.degreeOn ℂ sV C.ι C.dim_le (hp.isCartier hM) = 0 := by
  have := hM.isInvertibleModule_divisorialSheaf
  have := (hp.isCartier hM).isInvertibleModule_divisorialSheaf
  rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sV C.ι C.dim_le (hp.divisorialSheafIso (hBc := hM))]
  exact C.degree_pullback_eq_zero_of_isContractedBy u hu hC M.divisorialSheaf

/-- **The Picard number is preserved by a flop**: for small contractions `f : X ⟶ Z` and
`f⁺ : X⁺ ⟶ Z` of `ℚ`-factorial projective varieties, `X` and `X⁺` are isomorphic over the open
set of `Z` over which both `f` and `f⁺` are isomorphisms, whose preimages have complements of
codimension two. -/
private theorem picardNumber_eq_of_isSmall {X X' Zs : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Zs] [IsLocallyNoetherian Zs] [IsNormal Zs] {sX : X ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {sZs : Zs ⟶ Spec (.of ℂ)} {f : X ⟶ Zs} {fp : X' ⟶ Zs}
    (hsm : IsSmall ℂ sZs sX f) (hsm' : IsSmall ℂ sZs sX' fp) (hXQ : IsQFactorial sX)
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hX'Q : IsQFactorial sX')
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') : picardNumber sX' = picardNumber sX := by
  haveI : LocallyOfFiniteType sX := hXp.toIsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'p.toIsVariety.toLocallyOfFiniteType
  have hfs : f ≫ sZs = sX := hsm.comp_eq
  have hfps : fp ≫ sZs = sX' := hsm'.comp_eq
  have hcodim : ∀ {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] {u : Y ⟶ Zs},
      IsSmall ℂ sZs sY u → 2 ≤ closedsCodimension (Mori.exceptionalSet u) := by
    intro Y sY _ u hu
    haveI := hu.isProper
    have h := (isSmall_iff_two_le_closedsCodimension_exceptionalSet hu.toIsBirationalContraction).mp
      hu
    have e : exceptionalCloseds u = Mori.exceptionalSet u :=
      TopologicalSpace.Closeds.ext (exceptionalSet_eq_mori_exceptionalSet (sY := sY) u hu.isIso_app)
    rwa [e] at h
  set U : Zs.Opens := biregularLocus f ⊓ biregularLocus fp with hU
  haveI hUf : IsIso (f ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI hUfp : IsIso (fp ∣_ U) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hmem : ∀ {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] {u : Y ⟶ Zs},
      IsSmall ℂ sZs sY u → ∀ y : Y, Order.coheight y ≤ 1 → u y ∈ U := by
    intro Y sY _ u hu y hy
    haveI := hu.isProper
    have hb : u y ∈ biregularLocus u := by
      by_contra hn
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet (hcodim hu)
        (mem_exceptionalSet.mpr hn)
      exact absurd (this.trans hy) (by decide)
    have hco : Order.coheight (u y) ≤ 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus u hb).trans_le hy
    haveI : IsProper f := hsm.isProper
    haveI : IsProper fp := hsm'.isProper
    exact ⟨MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f
        (IsSmall.isBirationalMorphism sZs sX hsm) hco,
      MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp
        (IsSmall.isBirationalMorphism sZs sX' hsm') hco⟩
  set V : TopologicalSpace.Closeds X := (f ⁻¹ᵁ U).compl with hV
  set W : TopologicalSpace.Closeds X' := (fp ⁻¹ᵁ U).compl with hW
  have hVc : V.compl = f ⁻¹ᵁ U := by ext x; simp [V]
  have hWc : W.compl = fp ⁻¹ᵁ U := by ext x; simp [W]
  have hcod : ∀ {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] {u : Y ⟶ Zs},
      IsSmall ℂ sZs sY u → 2 ≤ closedsCodimension (u ⁻¹ᵁ U).compl := by
    intro Y sY _ u hu
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro y hy
    by_contra h
    exact hy (hmem hu y (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using h)))
  let e : Scheme.Opens.toScheme (X := X) V.compl ≅ Scheme.Opens.toScheme (X := X') W.compl :=
    X.isoOfEq hVc ≪≫ asIso (f ∣_ U) ≪≫ (asIso (fp ∣_ U)).symm ≪≫ X'.isoOfEq hWc.symm
  have he : e.hom ≫ Scheme.Opens.ι (X := X') W.compl ≫ sX' =
      Scheme.Opens.ι (X := X) V.compl ≫ sX := by
    simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      Scheme.isoOfEq_hom_ι_assoc]
    rw [← hfps, ← hfs, ← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
  exact (picardNumber_eq_of_isoInCodimOne sX sX' hXQ hXp hX'Q hX'p V W (hcod hsm) (hcod hsm')
    e he).symm

section Nef

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY]
  [LocallyOfFiniteType sY]

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy, Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism over `ℂ` which does not contract a proper curve has positive residue degree at
its generic point. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve ℂ (φ ≫ sY) := hφ ▸ inferInstance
  have : IsIntegral φ.image := MMP.Mori.isIntegral_image φ
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
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
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- A proper curve `C` of `Y` is not a point: its closure is not a singleton. -/
private theorem not_isContractedBy_of_image_closure_eq {g : X ⟶ Y} {Γ : ProperCurve sX}
    {C : ProperCurve sY} (h : g '' closure {Γ.point} = closure {C.point}) :
    ¬ Γ.IsContractedBy g := by
  intro hc
  have hsub : closure ({C.point} : Set Y) ⊆ {g Γ.point} := by
    rw [← h]
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hr : ∀ t, curveSubschemeAtι C.point t = g Γ.point := fun t => by
    have ht : curveSubschemeAtι C.point t ∈ closure {C.point} :=
      range_curveSubschemeAtι C.point ▸ ⟨t, rfl⟩
    exact hsub ht
  have : Subsingleton (curveSubschemeAt C.point) :=
    ⟨fun a b => (curveSubschemeAtι C.point).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h1 := C.dim_eq
  have h0 : topologicalKrullDim (curveSubschemeAt C.point) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [show ProperCurve.scheme C = curveSubschemeAt C.point from rfl, h1] at *
  norm_num at h0

end Nef

/-- Two closed integral curves with the same image carry the same degree. -/
private theorem degreeOn_eq_of_range_eq {X C C' : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (i : C ⟶ X) (i' : C' ⟶ X) [IsClosedImmersion i]
    [IsClosedImmersion i'] [IsReduced C] [IsReduced C'] [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)]
    (h : Set.range i = Set.range i') (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    MMP.Mori.degreeOn ℂ sX i hdim L = MMP.Mori.degreeOn ℂ sX i' hdim' L := by
  have hker : i'.ker = i.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range, h]
  haveI := IsClosedImmersion.isIso_lift i' i hker
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sX i i' hdim hdim'
    (asIso (IsClosedImmersion.lift i' i hker.le)) (IsClosedImmersion.lift_fac _ _ _) L

/-- An integral closed curve of a proper scheme has the same image as a proper curve. -/
private theorem exists_properCurve_range_eq {Y C : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsProper sY] (i : C ⟶ Y) [IsClosedImmersion i] [IsIntegral C]
    (hC : topologicalKrullDim C = 1) :
    ∃ CY : ProperCurve sY, Set.range i = Set.range CY.ι := by
  have hr : Set.range i = closure {i (genericPoint C)} := by
    rw [← Set.image_univ, ← (genericPoint_spec C).def, ← Set.image_singleton,
      i.isClosedEmbedding.closure_image_eq]
  have hdim : topologicalKrullDim (curveSubschemeAt (i (genericPoint C))) = 1 := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, ← hr, ← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (i.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  refine ⟨⟨_, isProperCurve_of_isProper sY hdim⟩, ?_⟩
  rw [hr]
  exact (ProperCurve.range_ι (⟨_, isProperCurve_of_isProper sY hdim⟩ : ProperCurve sY)).symm

/-- **Nefness through the base of a crepant flop** (FA 15.9, Step 3, (15.4.1)). Let
`c : X ⟶ T` be surjective and `g : Y ⟶ T` a morphism of projective varieties, and `M` a Cartier
divisor on `T` with `c^* M = r L_X`, `g^* M = r L_Y`, `r > 0`. If `L_X` is nef, then so is
`L_Y`: `M` is nonnegative on every curve of `T`, which is the image of a curve of `X`, and
`(L_Y · C) = [k(C) : k(g(C))] (M · g(C)) / r`. -/
private theorem isNef_of_isPullback {X Y T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [QuasiCompact sY]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    {c : X ⟶ T} {g : Y ⟶ T} (hcs : c ≫ sT = sX) (hgs : g ≫ sT = sY) [IsProper c] [Surjective c]
    {M : Divisor T} (hM : M.IsCartier) {r : ℕ} (hr : 0 < r) {LX : QDivisor X} {LY : QDivisor Y}
    (hLX : LX.IsNef ℂ sX)
    {hBX : ∀ Z : irreducibleComponents X, c (componentGenericPoint X Z) ∉ M.supp}
    {MX : Divisor X} (hpX : M.IsPullback c hBX MX) (hMX : Divisor.toQDivisor MX = (r : ℤ) • LX)
    {hBY : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ M.supp}
    {MY : Divisor Y} (hpY : M.IsPullback g hBY MY) (hMY : Divisor.toQDivisor MY = (r : ℤ) • LY) :
    LY.IsNef ℂ sY := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  have hTv := hT.toIsVariety
  haveI : IsSeparated sT := hTv.toIsSeparated
  haveI : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY.isProjective
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  -- `M` is nonnegative on the proper curves of `T`
  have hA : ∀ CT : ProperCurve sT, 0 ≤ CT.degree ℂ M.divisorialSheaf := by
    intro CT
    obtain ⟨Γ, hΓ⟩ := ProperCurve.exists_image_closure_eq_of_surjective hX.toIsVariety hTv c hcs CT
    have hpt : c Γ.point = CT.point := by
      have h1 : closure {c Γ.point} = closure {CT.point} := by
        rw [← hΓ, ← Set.image_singleton, c.isClosedMap.closure_image_eq_of_continuous c.continuous]
      exact (inseparable_iff_closure_eq.mpr h1).eq
    have hpos := residueFieldDegree_pos_of_not_isContractedBy c hcs Γ
      (not_isContractedBy_of_image_closure_eq hΓ)
    have hMXc := hpX.isCartier hM
    haveI := hMXc.isInvertibleModule_divisorialSheaf
    have h1 : MX.degreeOn ℂ sX Γ.ι Γ.dim_le hMXc =
        Γ.degree ℂ ((Scheme.Modules.pullback c).obj M.divisorialSheaf) := by
      rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sX Γ.ι Γ.dim_le
        (hpX.divisorialSheafIso (hBc := hM))]
      rfl
    have hCT : IsProperCurve sT (c Γ.point) := hpt ▸ CT.isProperCurve
    have h2 := Γ.degree_pullback c hcs M.divisorialSheaf
    rw [dif_pos hCT] at h2
    have hCTeq : (⟨c Γ.point, hCT⟩ : ProperCurve sT) = CT := ProperCurve.ext hpt
    rw [hCTeq] at h2
    have h3 : (0 : ℚ) ≤ MX.degreeOn ℂ sX Γ.ι Γ.dim_le hMXc := by
      have hn := (QDivisor.isNef_iff LX hLX.1).mp hLX Γ.scheme Γ.ι Γ.dim_eq
      rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sX Γ.ι _ LX hLX.1 hr MX hMXc hMX] at hn
      rcases div_nonneg_iff.mp hn with h | h
      · exact h.1
      · exact absurd h.2 (not_le.mpr hr')
    have h3' : (0 : ℤ) ≤ MX.degreeOn ℂ sX Γ.ι Γ.dim_le hMXc := by exact_mod_cast h3
    rw [h1, h2] at h3'
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hpos)).mp h3'
  -- the pull-back of `M` to `Y` is nonnegative on every closed curve
  have hMYc := hpY.isCartier hM
  haveI := hMYc.isInvertibleModule_divisorialSheaf
  have hLYq : LY.IsQCartier := ⟨r, by exact_mod_cast hr.ne', ⟨MY, hMY, hMYc⟩⟩
  refine (QDivisor.isNef_iff LY hLYq).mpr fun C i _ _ _ hC => ?_
  obtain ⟨CY, hCY⟩ := exists_properCurve_range_eq sY i hC
  rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sY i hC.le LY hLYq hr MY hMYc hMY]
  refine div_nonneg ?_ hr'.le
  have h1 : MY.degreeOn ℂ sY i hC.le hMYc =
      CY.degree ℂ ((Scheme.Modules.pullback g).obj M.divisorialSheaf) := by
    rw [Divisor.degreeOn, degreeOn_eq_of_range_eq sY i CY.ι hCY hC.le CY.dim_le,
      degreeOn_eq_of_iso ℂ sY CY.ι CY.dim_le (hpY.divisorialSheafIso (hBc := hM))]
    rfl
  rw [h1, CY.degree_pullback g hgs M.divisorialSheaf]
  split_ifs with h
  · exact_mod_cast mul_nonneg (by positivity) (hA _)
  · simp

/-- A finite sum of vectors of a convex cone lying in an extremal face has all its summands in
the face. -/
private theorem mem_of_sum_mem_isExtremalFace {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N R : Set V} (hR : IsExtremalFace ℝ N R) (hN0 : (0 : V) ∈ N)
    (hNadd : ∀ u ∈ N, ∀ v ∈ N, u + v ∈ N) {ι : Type*} (s : Finset ι) (z : ι → V)
    (hz : ∀ i ∈ s, z i ∈ N) (hs : ∑ i ∈ s, z i ∈ R) : ∀ i ∈ s, z i ∈ R := by
  classical
  revert hz hs
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro hz hs
    rw [Finset.sum_insert ha] at hs
    have hsN : ∑ i ∈ s, z i ∈ N :=
      Finset.sum_induction _ (· ∈ N) (fun a b ha hb => hNadd a ha b hb) hN0 fun i hi =>
        hz i (Finset.mem_insert_of_mem hi)
    obtain ⟨h1, h2⟩ := hR.2.2.2 _ (hz a (Finset.mem_insert_self a s)) _ hsN hs
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · exact ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) h2 i hi

/-- **Negative extremal rays of a klt pair are spanned by curves.** -/
private theorem exists_properCurve_mem_of_isExtremalRay {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety ℂ sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ u ∈ R, u ≠ 0 →
      QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 u < 0) :
    ∃ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R ∧
      OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  obtain ⟨S, -, -, hNE⟩ := MMP.Mori.exists_countable_isRationalCurve_closedConeOfCurves_eq hklt hΔ
  obtain ⟨hface, v, hv0, hRv⟩ := hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hvN : v ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := hface.1 hvR
  rw [hNE] at hvN
  obtain ⟨w, hw, y, hy, hwy⟩ := Set.mem_add.mp hvN
  have hcl : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ closedConeOfCurves sX :=
    fun C => coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  have hhull : PointedCone.hull ℝ
      ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' S) ≤
        closedConeOfCurves sX := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨C, -, rfl⟩
    exact hcl C
  have hyN : y ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := hhull hy
  obtain ⟨hwR, hyR⟩ := hface.2.2.2 w hw.1 y hyN (hwy ▸ hvR)
  have hw0 : w = 0 := by
    by_contra h
    exact absurd hw.2 (not_le.mpr (hneg w hwR h))
  rw [hw0, zero_add] at hwy
  subst hwy
  obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hy
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum ▸ hv0)
  have hmem := mem_of_sum_mem_isExtremalFace hface (closedConeOfCurves sX).zero_mem
    (fun u hu v hv => (closedConeOfCurves sX).add_mem hu hv) Finset.univ
    (fun i => c i • (g i : NumericalCurveClasses sX))
    (fun i _ => Submodule.smul_mem (closedConeOfCurves sX) (c i)
      (hhull (Submodule.subset_span (g i).2)))
    (hsum ▸ hyR) i (Finset.mem_univ i)
  obtain ⟨C, -, hC⟩ := (g i).2
  replace hC : OneCycle.numericalClass sX (C.cycle ℝ) = g i := hC
  have hc0 : (c i : ℝ) ≠ 0 := by
    intro h0
    apply hi
    rw [show c i = 0 from NNReal.coe_eq_zero.mp h0, zero_smul]
  refine ⟨C, ?_, ?_⟩
  · rw [hC]
    have h := hface.2.1.2 _ hmem ((c i : ℝ))⁻¹ (inv_pos.mpr (lt_of_le_of_ne (c i).2 (Ne.symm hc0)))
    rwa [show c i • (g i : NumericalCurveClasses sX) =
        ((c i : ℝ)) • (g i : NumericalCurveClasses sX) from rfl,
      smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
  · rw [hC]
    intro h0
    apply hi
    rw [h0, smul_zero]

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, between integral schemes,
with `f : X ⟶ T` an isomorphism in codimension one and `g : Y ⟶ T` proper birational onto the
normal `T`, sends every prime divisor `P` of `X` to a prime divisor of `Y`, the inverse transform
along `g` of the transform of `P` along `f`. -/
private theorem exists_transformPrimeDivisor_eq_some {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) (P : MMP.Mori.PrimeDivisor X) :
    ∃ (DT : MMP.Mori.PrimeDivisor T) (DY : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor f.toRationalMap P = some DT ∧
      inverseTransformPrimeDivisor g DT = some DY ∧
      RationalMap.transformPrimeDivisor ρ P = some DY ∧ g DY.genericPoint = f P.genericPoint := by
  classical
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hf
  -- the generic point of a prime divisor avoids every closed subset of codimension `≥ 2`
  have avoid : ∀ Z : TopologicalSpace.Closeds X, 2 ≤ closedsCodimension Z →
      ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∉ Z := by
    intro Z hZ P hP
    have hsub : ((irreducibleSetEquivPoints (α := X)).symm P.genericPoint : Set X) ⊆ Z :=
      Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)
    have h2 := le_closedsCodimension_iff.mp hZ _ hsub
    rw [codimension_eq_coheight, Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  have e : ∀ p : (g ⁻¹ᵁ biregularLocus g).toScheme,
      (biregularLocus g).ι ((g ∣_ biregularLocus g) p) = g ((g ⁻¹ᵁ biregularLocus g).ι p) :=
    fun p => by rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hξ1 : Order.coheight P.genericPoint = 1 := P.coheight_genericPoint
  -- `f` is an isomorphism near the generic point of `P`
  have hξV : P.genericPoint ∈ V.compl := avoid V hV P
  let U : X.Opens := V.compl
  let U' : T.Opens := W.compl
  let p : U.toScheme := ⟨P.genericPoint, hξV⟩
  have hfp : U'.ι (f.resLE U' U hle p) = f P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  have hT1 : Order.coheight (f P.genericPoint) = 1 := by
    rw [← hfp, Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding,
      Topology.IsOpenEmbedding.coheight_eq _ (f.resLE U' U hle).isOpenEmbedding,
      ← Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding]
    exact hξ1
  let DT : MMP.Mori.PrimeDivisor T :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f P.genericPoint) hT1
  have hDT : MMP.Mori.PrimeDivisor.genericPoint DT = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hT1
  have h1 : RationalMap.transformPrimeDivisor f.toRationalMap P = some DT :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P DT).mpr hDT.symm
  -- the point of `Y` over `f(η_P)`
  have htB : f P.genericPoint ∈ biregularLocus g :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hT1.le
  obtain ⟨q, hq⟩ := (g ∣_ biregularLocus g).surjective ⟨f P.genericPoint, htB⟩
  have hgq : g q.1 = f P.genericPoint := by
    have := e q
    rw [hq] at this
    exact this.symm
  have hy1 : Order.coheight q.1 = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (show g q.1 ∈ _ from hgq ▸ htB),
      hgq, hT1]
  let DY : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne q.1 hy1
  have hDY : MMP.Mori.PrimeDivisor.genericPoint DY = q.1 :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have h2 : inverseTransformPrimeDivisor g DT = some DY :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (by rw [hDY, hgq, hDT]) (by rw [hDY, hgq]; exact htB)
  -- `ρ` is defined at `η_P` and sends it to that point
  have hξd : P.genericPoint ∈ RationalMap.dom ρ := by
    by_contra h
    exact avoid (RationalMap.dom ρ).compl hρc P h
  obtain ⟨g', hξg', hg'⟩ := RationalMap.definedAt_iff.mp hξd
  have hy' : g (g'.hom ⟨P.genericPoint, hξg'⟩) = f P.genericPoint :=
    MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq (g := g'.compHom g)
      (g' := f.toPartialMap) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg']; exact hρ)
      hξg' trivial
  have hy'y : g'.hom ⟨P.genericPoint, hξg'⟩ = q.1 := by
    have hm1 : g'.hom ⟨P.genericPoint, hξg'⟩ ∈ g ⁻¹ᵁ biregularLocus g := by
      change g _ ∈ biregularLocus g
      rw [hy']
      exact htB
    have : (⟨_, hm1⟩ : (g ⁻¹ᵁ biregularLocus g).toScheme) = q := by
      apply (g ∣_ biregularLocus g).isOpenEmbedding.injective
      apply (biregularLocus g).ι.isOpenEmbedding.injective
      exact (e _).trans ((hy'.trans hgq.symm).trans (e q).symm)
    exact congrArg Subtype.val this
  have h3 : RationalMap.transformPrimeDivisor ρ P = some DY := by
    refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr
      ⟨RationalMap.definedAt_iff.mpr ⟨g', hξg', hg'⟩, ?_⟩
    have hc : RationalMap.transform ρ P.idealSheaf.support = DY.idealSheaf.support := by
      apply SetLike.coe_injective
      rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hξg', hy'y, ← hDY]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure DY).symm
    have := DY.integral
    rw [RationalMap.transformIdeal, hc, MMP.Positivity.vanishingIdeal_support_of_isReduced]
  exact ⟨DT, DY, h1, h2, h3, by rw [hDY, hgq]⟩

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, between integral schemes,
with `f : X ⟶ T` an isomorphism in codimension one and `g : Y ⟶ T` proper birational onto the
normal `T`, transforms divisors as `g⁻¹_* ∘ f_*`. -/
private theorem transformDivisor_eq_inverseTransformDivisor {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor ρ D =
      inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap D) := by
  classical
  have : (RationalMap.transformDivisor ρ : DivisorWithCoeffs R X →+ _) =
      (inverseTransformDivisor g).comp (RationalMap.transformDivisor f.toRationalMap) := by
    refine Finsupp.addHom_ext fun P r => ?_
    obtain ⟨DT, DY, h1, h2, h3, -⟩ := exists_transformPrimeDivisor_eq_some hg hf hρ hρc P
    rw [AddMonoidHom.comp_apply, RationalMap.transformDivisor_single_of_eq_some h3,
      RationalMap.transformDivisor_single_of_eq_some h1,
      inverseTransformDivisor_single_of_eq_some h2]
  exact DFunLike.congr_fun this D

/-- A `ℚ`-divisor `B` with a Cartier multiple `T = nB` whose pull-back is `nB'` is `ℚ`-Cartier with
pull-back `B'`. -/
private theorem isQCartier_and_isPullback_of_zsmul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {B : QDivisor X} {B' : QDivisor Y} {n : ℕ} (hn : 0 < n) {T : Divisor X}
    (hTB : Divisor.toQDivisor T = (n : ℤ) • B) (hTc : T.IsCartier) {D' : Divisor Y}
    {hT : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ T.supp}
    (hTp : T.IsPullback f hT D') (hD' : Divisor.toQDivisor D' = (n : ℤ) • B') :
    B.IsQCartier ∧ ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp,
      B.IsPullback f hB B' := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQC : B.IsQCartier := ⟨n, hn', T, hTB, hTc⟩
  have hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp := fun Z hZ =>
    hT Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hn' hTB])
  refine ⟨hQC, hB, ?_⟩
  have hG := QDivisor.isPullback_pullback hQC hB
  obtain ⟨D'', hD'', hp⟩ := hG n hn T hTB hTc
  rw [hp.eq hTc hTp, hD'] at hD''
  have : B.pullback hQC hB = B' := by
    ext P
    have := congrArg (fun G : QDivisor Y => G.coeff P) hD''
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact (mul_left_cancel₀ (by exact_mod_cast hn') this).symm
  exact this ▸ hG

/-- **(15.4.2) passes to the flopped model** (FA 15.9, Step 3). Let `c : X ⟶ T` be the flopping
contraction and `g : X⁺ ⟶ T` the flop, with a Cartier divisor `M` on `T`, `M = r c_*(K + Δ)`,
whose pull-back to `X⁺` is `r (K⁺ + Δ⁺)`. Both adjoint divisors are then pull-backs of the
`ℚ`-Cartier divisor `c_*(K + Δ)` of the base, and sections of `m(K + Δ)` push forward to `T` and
pull back to `X⁺`. -/
private theorem exists_two_le_h0_of_isPullback {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ)
    {Z Y' : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    [CompactSpace Y'] (hY' : MMP.Mori.IsProjectiveVariety ℂ sY') {c : s.Y ⟶ Z} [IsProper c]
    (hcs : c ≫ sZ = s.sY) (hb : IsBirationalMorphism c) {g : Y' ⟶ Z} (hgs : g ≫ sZ = sY')
    [IsDominant g] [QuasiCompact g] {K' : Divisor Y'} {Δ' : QDivisor Y'} {r : ℕ} (hr : 0 < r)
    {M : Divisor Z}
    (hM : Divisor.toQDivisor M = (r : ℤ) •
      (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
        flopBaseDivisor c s.Δ))
    (hMc : M.IsCartier)
    {hBY : ∀ W : irreducibleComponents Y', g (componentGenericPoint Y' W) ∉ M.supp}
    {MY : Divisor Y'} (hpY : M.IsPullback g hBY MY)
    (hMY : Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor K' + Δ')) :
    ∃ m : ℕ, 0 < m ∧ ∃ M' : Divisor Y',
      Divisor.toQDivisor M' = (m : ℤ) • (Divisor.toQDivisor K' + Δ') ∧ M'.IsCartier ∧
        2 ≤ M'.h0 ℂ sY' := by
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : IsProper sY' := isProper_of_isProjectiveMorphism _ hY'.isProjective
  have hYn : IsNormalVariety ℂ (c ≫ sZ) := by rw [hcs]; exact hs.hA.isQFactorial.1
  have hL : Mori.RationalMap.transformDivisor c.toRationalMap (Divisor.toQDivisor s.K + s.Δ) =
      Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap s.K) +
        flopBaseDivisor c s.Δ := by
    rw [map_add, transformDivisor_toQDivisor]
    rfl
  obtain ⟨hLq, hLB, hpull⟩ := isQCartier_and_isPullback_of_zsmul hr (hL ▸ hM) hMc hpY hMY
  exact exists_two_le_h0_of_isPullback_transformDivisor hZn hYn hb g hgs hLq hpull
    (by rw [hcs]; exact hs.hA.exists_two_le_h0)

/-- **(15.4.3) passes to the flopped model** (FA 15.9, Step 4). Let `c : X ⟶ T` be the small
flopping contraction, with exceptional set properly contained in `P`, and `g : X⁺ ⟶ T` its flip
with respect to `P`. The flip is an isomorphism over the biregular locus `V` of `c`, so the log
elliptic fibration of `X`, restricted over the complement of the closure of the image of `P`, lies
over `V` and maps isomorphically onto an open set of `X⁺`, where the adjoint divisors agree. -/
private theorem exists_isLogEllipticFiberSpace_of_isFlip {ρ : ℕ∞} {s : ChainState}
    (hs : s.Inv ρ) {Z Y' : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)}
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    [LocallyOfFiniteType sY'] [IsSeparated (Y' ↘ Limits.terminal Scheme)] [IsIntegral Z]
    [IsLocallyNoetherian Z]
    [IsNormal Z] [IsSeparated (Z ↘ Limits.terminal Scheme)] {c : s.Y ⟶ Z} (hcs : c ≫ sZ = s.sY)
    (hsmall : IsSmall ℂ sZ s.sY c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) ⊂ s.P.support) {g : Y' ⟶ Z} [IsProper g]
    (hgb : IsBirationalMorphism g) (hgs : g ≫ sZ = sY') {p : s.Y.RationalMap Y'}
    (hEq : (Divisor.toQDivisor (Finsupp.single s.P 1 : Divisor s.Y)).IsQCartier)
    (hflip : IsFlip ℂ s.sY sZ sY'
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single s.P 1 : Divisor s.Y))) c g p)
    (hklt : IsKawamataLogTerminal sY' 3 (Mori.RationalMap.transformDivisor p s.K)
      (QDivisor.toRDivisor (flopDivisor p s.Δ)))
    (hLq : (Divisor.toQDivisor (Mori.RationalMap.transformDivisor p s.K) +
      flopDivisor p s.Δ).IsQCartier) :
    ∃ (U : Y'.Opens) (_ : (U : Set Y').Nonempty) (W : Scheme.{0})
      (sW : W ⟶ Spec (.of ℂ)) (fU : U.toScheme ⟶ W),
      IsLogEllipticFiberSpace ℂ (U.ι ≫ sY') sW 3
        (DivisorWithCoeffs.restrict U.ι (Mori.RationalMap.transformDivisor p s.K))
        (DivisorWithCoeffs.restrict U.ι (flopDivisor p s.Δ)) fU := by
  haveI : IsProper c := hflip.isContraction.isProper
  obtain ⟨U, hU, W, sW, fU, hfU⟩ := hs.hA.exists_isLogEllipticFiberSpace
  have hnd := MMP.Flips.not_dense_image_of_isTriviallyConnected s.sY hs.hA U hU sW fU hfU s.P
    hs.hD
  let W₀ : W.Opens := ⟨(closure (fU '' (U.ι ⁻¹' (s.P.support : Set s.Y))))ᶜ,
    isClosed_closure.isOpen_compl⟩
  have hW₀ : (W₀ : Set W).Nonempty :=
    Set.nonempty_compl.mpr fun h => hnd (dense_iff_closure_eq.mpr h)
  set V := biregularLocus c with hVdef
  haveI hViso : IsIso (c ∣_ V) := isBiregular_biregularLocus c
  have hnotP : ∀ x : (fU ⁻¹ᵁ W₀).toScheme, U.ι x.1 ∉ (s.P.support : Set s.Y) := by
    intro x hx
    exact x.2 (subset_closure ⟨x.1, hx, rfl⟩)
  have hrange : Set.range ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) ⊆ Set.range (c ⁻¹ᵁ V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hx
    have hmem : ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) x ∈ (Mori.exceptionalSet c : Set s.Y) := hx
    exact hnotP x (hEx.subset hmem)
  let a := IsOpenImmersion.lift (c ⁻¹ᵁ V).ι ((fU ⁻¹ᵁ W₀).ι ≫ U.ι) hrange
  have ha : a ≫ (c ⁻¹ᵁ V).ι = (fU ⁻¹ᵁ W₀).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (a ≫ (c ⁻¹ᵁ V).ι) := by rw [ha]; infer_instance
  haveI : IsOpenImmersion a := IsOpenImmersion.of_comp a (c ⁻¹ᵁ V).ι
  -- the flip is an isomorphism over `V`
  have hdisj : Disjoint (V : Set Z) (c '' Flips.exceptionalSet c) := by
    rw [Set.disjoint_left]
    rintro _ hW ⟨y, hy, rfl⟩
    refine hy ⟨c ⁻¹ᵁ V, hW, ?_⟩
    rw [← morphismRestrict_ι]
    infer_instance
  haveI hgV : IsIso (g ∣_ V) :=
    IsFlip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hEq hflip V hdisj
  let j : (fU ⁻¹ᵁ W₀).toScheme ⟶ Y' := a ≫ (c ∣_ V) ≫ inv (g ∣_ V) ≫ (g ⁻¹ᵁ V).ι
  haveI : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hjg : j ≫ g = (fU ⁻¹ᵁ W₀).ι ≫ U.ι ≫ c := by
    simp only [j, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι, ← Category.assoc, ha,
      Category.assoc]
  have hj : j ≫ sY' = (fU ⁻¹ᵁ W₀).ι ≫ U.ι ≫ s.sY := by
    rw [← hgs, ← Category.assoc, hjg, Category.assoc, Category.assoc, hcs]
  have htr := fun P => exists_transformPrimeDivisor_eq_some hgb hsmall.exists_isIso
    hflip.isModificationOf.2 hflip.isMorphismInCodimOne P
  have hcoeff : ∀ Q : Mori.PrimeDivisor (fU ⁻¹ᵁ W₀).toScheme,
      (Divisor.toQDivisor (Mori.RationalMap.transformDivisor p s.K) + flopDivisor p s.Δ).coeff
          (OpenWeilRestriction.primeDivisorMap j Q) =
        (Divisor.toQDivisor (DivisorWithCoeffs.restrict U.ι s.K) +
          DivisorWithCoeffs.restrict U.ι s.Δ).coeff
            (OpenWeilRestriction.primeDivisorMap (fU ⁻¹ᵁ W₀).ι Q) := by
    intro Q
    rw [MMP.Flips.restrict_ι_eq_restrictOpen U s.K, MMP.Flips.restrict_ι_eq_restrictOpen U s.Δ]
    set E := OpenWeilRestriction.primeDivisorMap U.ι
      (OpenWeilRestriction.primeDivisorMap (fU ⁻¹ᵁ W₀).ι Q) with hE
    have hEgen : E.genericPoint = U.ι ((fU ⁻¹ᵁ W₀).ι Q.genericPoint) := by
      rw [hE, OpenWeilRestriction.genericPoint_primeDivisorMap,
        OpenWeilRestriction.genericPoint_primeDivisorMap]
    have hEV : c E.genericPoint ∈ V := by
      by_contra hc0
      have : E.genericPoint ∈ (Mori.exceptionalSet c : Set s.Y) := hc0
      rw [hEgen] at this
      exact hnotP Q.genericPoint (hEx.subset this)
    obtain ⟨-, DY, -, -, hpE, hgDY⟩ := htr E
    -- the transform of `E` is the prime divisor of `X⁺` through `j(η_Q)`
    have hjQ : g (j Q.genericPoint) = c E.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hjg, hEgen]
      rfl
    have hDY : DY = OpenWeilRestriction.primeDivisorMap j Q := by
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact eq_of_isIso_morphismRestrict g V (by rw [hgDY]; exact hEV) (by rw [hjQ]; exact hEV)
        (hgDY.trans hjQ.symm)
    have hpF : ∀ F : Mori.PrimeDivisor s.Y,
        Mori.RationalMap.transformPrimeDivisor p F = some DY → F = E := by
      intro F hF
      obtain ⟨-, DF, -, -, hpF', hgDF⟩ := htr F
      rw [hpF'] at hF
      cases Option.some.inj hF
      have hcF : c F.genericPoint = c E.genericPoint := hgDF.symm.trans hgDY
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_isIso_morphismRestrict c V (by rw [hcF]; exact hEV) hEV hcF)
    have hL : Divisor.toQDivisor (Mori.RationalMap.transformDivisor p s.K) + flopDivisor p s.Δ =
        Mori.RationalMap.transformDivisor p (Divisor.toQDivisor s.K + s.Δ) := by
      rw [map_add, transformDivisor_toQDivisor]
      rfl
    rw [hL, ← hDY]
    change DivisorWithCoeffs.mapPrimeDivisors (Mori.RationalMap.transformPrimeDivisor p)
      (Divisor.toQDivisor s.K + s.Δ) DY = _
    rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hpE hpF]
    rfl
  obtain ⟨U', hU', fU', hfU'⟩ := MMP.Flips.IsLogEllipticFiberSpace.exists_of_isOpenImmersion hfU
    W₀ hW₀ hklt.1.1 hklt.2.1 hLq hklt.1.2 j hj hcoeff
  exact ⟨U', hU', W₀.toScheme, W₀.ι ≫ sW, fU', hfU'⟩

/-- The extremal ray `R` is spanned by the class of a proper curve: by the cone theorem for the
klt pair `(X, Δ + εP)`. -/
private theorem exists_properCurve_eq_span {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ}
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R) :
    ∃ C₀ : ProperCurve s.sY, OneCycle.numericalClass s.sY (C₀.cycle ℝ) ∈ R ∧
      R = {u | ∃ a : ℝ, 0 ≤ a ∧ a • OneCycle.numericalClass s.sY (C₀.cycle ℝ) = u} := by
  set Θ := s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1) with hΘ
  have hQ : IsQFactorial s.sY := hs.hA.isQFactorial
  have hΘq : (Divisor.toQDivisor s.K + Θ).IsQCartier := isQCartier_of_isQFactorial s.sY hQ _
  have hkltM : MMP.Mori.IsKltPair s.sY 3 s.K Θ :=
    (isKawamataLogTerminal_iff_isKltPair s.sY 3 s.K Θ hklt.1.1 hklt.2.1 hklt.1.2 hΘq).mp hklt
  have hΘe : Θ.IsEffective := fun E => by
    have h := (hklt.1.2 E).1
    rw [QDivisor.coeff_toRDivisor] at h
    exact_mod_cast h
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s.sY := hs.hA.isProjectiveVariety
  obtain ⟨hq, hray, hneg⟩ := hR
  obtain ⟨C₀, hC₀R, hC₀0⟩ := exists_properCurve_mem_of_isExtremalRay hkltM hΘe hray hneg
  refine ⟨C₀, hC₀R, ?_⟩
  obtain ⟨-, v, -, hRv⟩ := hray
  have hC := hC₀R
  rw [hRv] at hC
  obtain ⟨a, ha, hav⟩ := hC
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hC₀0 (by rw [← hav, zero_smul])
  rw [hRv]
  ext u
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b / a, div_nonneg hb ha, by rw [← hav, smul_smul, div_mul_cancel₀ b ha0]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b * a, mul_nonneg hb ha, by rw [← hav, smul_smul]⟩

/-- **Step 3 of FA 15.9: the small case.** If the contraction `c` of the null negative ray has
exceptional set properly contained in `P`, then `c` is small and the `P`-flop of `c` exists; it is
a `(K + Δ)`-trivial flop and the flopped model satisfies the invariant of the chain. -/
private theorem exists_isFlop_of_exceptionalSet_ssubset
    {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) {ε : ℚ} (hε : 0 < ε)
    (hklt : IsKawamataLogTerminal s.sY 3 s.K
      (QDivisor.toRDivisor (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))))
    {R : Set (NumericalCurveClasses s.sY)}
    (hR : IsNegativeExtremalRayOf s.sY
      (Divisor.toQDivisor s.K + (s.Δ + ε • Divisor.toQDivisor (Finsupp.single s.P 1))) R)
    (hRL : ∀ u ∈ R, QDivisor.curveForm s.sY (Divisor.toQDivisor s.K + s.Δ) hs.hA.isQCartier u = 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {c : s.Y ⟶ Z}
    (hc : IsContractionOfRay s.sY sZ R c) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hρ : picardNumber sZ + 1 = picardNumber s.sY)
    (hdesc : ∀ M : s.Y.CartierDivisor,
      (∀ u ∈ R, NumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ M) u = 0) →
      ∃ (MR : Z.CartierDivisor)
        (hMR : ¬ Set.range c ⊆ MMP.Intersection.cartierSupport MR),
        MMP.Intersection.LinearlyEquivalent M
          (MMP.CartierDivisor.pullback c MR hMR))
    (hcurves : ∀ C : ProperCurve s.sY, C.IsContractedBy c →
      (Divisor.toQDivisor s.K + s.Δ).intersectionNumber ℂ s.sY C.ι C.dim_le hs.hA.isQCartier = 0 ∧
      (∃ hE : (Divisor.toQDivisor (Finsupp.single s.P 1)).IsQCartier,
        (Divisor.toQDivisor (Finsupp.single s.P 1)).intersectionNumber ℂ s.sY C.ι C.dim_le hE
          < 0) ∧
      C.point ∈ s.P.support)
    (hb : IsBirationalMorphism c)
    (hEx : (Mori.exceptionalSet c : Set s.Y) ⊂ s.P.support) :
    ∃ e : Edge s, e.IsFlop ∧ e.s'.Inv ρ := by
  have hYp := hs.hA.isProjectiveVariety
  have hQ : IsQFactorial s.sY := hs.hA.isQFactorial
  have hZv : MMP.Mori.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZv.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hc.isNormalVariety_target.2
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  haveI : Surjective c := ⟨hc.surjective⟩
  haveI : MMP.Mori.IsVariety ℂ s.sY := hYp.toIsVariety
  haveI : MMP.Mori.IsVariety ℂ sZ := hZv
  have hbc : IsBirationalContraction ℂ sZ s.sY c :=
    { isVariety_target := hZv
      isVariety_source := hYp.toIsVariety
      comp_eq := hc.comp_eq
      isProper := inferInstance
      isIso_app := hc.isIso_app
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sY hb).symm }
  set E : QDivisor s.Y := Divisor.toQDivisor (Finsupp.single s.P 1) with hEdef
  have hEq : E.IsQCartier := isQCartier_of_isQFactorial s.sY hQ E
  -- the ray is spanned by a contracted curve, so `ρ(X/Z) = 1` and `c` is not an isomorphism
  obtain ⟨C₀, hC₀R, hspan⟩ := exists_properCurve_eq_span hs hklt hR
  have hC₀ : C₀.IsContractedBy c := (hc.isContractedBy_iff C₀).mpr hC₀R
  have hρ1 : Flips.relativePicardNumber s.sY c = 1 :=
    relativePicardNumber_eq_one_of_isContractionOfRay hR ⟨C₀, hspan⟩ hc
  have hni : ¬ IsIso c := by
    intro hiso
    have hsub : closure ({C₀.point} : Set s.Y) ⊆ {C₀.point} := fun x hx =>
      c.isOpenEmbedding.injective (hC₀ x hx)
    have hr : ∀ t, curveSubschemeAtι C₀.point t = C₀.point := fun t => by
      have ht : curveSubschemeAtι C₀.point t ∈ closure {C₀.point} :=
        range_curveSubschemeAtι C₀.point ▸ ⟨t, rfl⟩
      exact hsub ht
    have : Subsingleton (curveSubschemeAt C₀.point) :=
      ⟨fun a b => (curveSubschemeAtι C₀.point).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
    have h1 := C₀.dim_eq
    have h0 : topologicalKrullDim (curveSubschemeAt C₀.point) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [show ProperCurve.scheme C₀ = curveSubschemeAt C₀.point from rfl, h1] at *
    norm_num at h0
  -- `c` is small: its exceptional set is a proper closed subset of the prime divisor `P`
  have hExeq : Flips.exceptionalSet c = (Mori.exceptionalSet c : Set s.Y) :=
    exceptionalSet_eq_mori_exceptionalSet (sY := s.sY) c hc.isIso_app
  have hsmall : IsSmall ℂ sZ s.sY c := by
    refine (isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro y hy
    have hy' : y ∈ (Mori.exceptionalSet c : Set s.Y) := hExeq ▸ hy
    exact two_le_coheight_of_mem_of_ssubset (Mori.exceptionalSet c).isClosed hEx hy'
  -- `K + Δ` is numerically `c`-trivial and `-P` is `c`-ample
  have hRK : QDivisor.toRDivisor (Divisor.toQDivisor s.K + s.Δ) =
      logCanonicalDivisor s.K (QDivisor.toRDivisor s.Δ) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  have htrivQ : IsNumericallyTrivialOver ℂ s.sY c
      (QDivisor.toRDivisor (Divisor.toQDivisor s.K + s.Δ)) :=
    isNumericallyTrivialOver_of_intersectionNumber_eq_zero hs.hA.isQCartier
      fun C hC => (hcurves C hC).1
  have htriv : IsNumericallyTrivialOver ℂ s.sY c
      (logCanonicalDivisor s.K (QDivisor.toRDivisor s.Δ)) := hRK ▸ htrivQ
  have hnegEq : ((-1 : ℚ) • E).IsQCartier := isQCartier_of_isQFactorial s.sY hQ _
  have hHf : IsRelativelyAntiAmple c (QDivisor.toRDivisor E) := by
    have h := (isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one s.sY sZ
      hQ.1 hc.isNormalVariety_target c hbc.toIsContraction
      (IsProjectiveMorphism.isProjective hc.isProjectiveMorphism) hρ1 C₀ hC₀ ((-1 : ℚ) • E)
      hnegEq).mpr ?_
    · change IsRelativelyAmple c (-QDivisor.toRDivisor E)
      rwa [toRDivisor_smul, Rat.cast_neg, Rat.cast_one, neg_one_smul] at h
    · obtain ⟨hE', hEC⟩ := (hcurves C₀ hC₀).2.1
      rw [MMP.Mori.QDivisor.intersectionNumber_smul ℂ s.sY C₀.ι C₀.dim_le (-1) E hE' hnegEq]
      linarith
  -- the `P`-flop
  have hΔe : s.Δ.IsEffective := fun E' => by
    have h := (hs.hA.isBoundary E').1
    rw [QDivisor.coeff_toRDivisor] at h
    exact_mod_cast h
  have hkltΔ : MMP.Mori.IsKltPair s.sY 3 s.K s.Δ :=
    (isKawamataLogTerminal_iff_isKltPair s.sY 3 s.K s.Δ hQ.1
      hs.hA.isKawamataLogTerminal.2.1 hs.hA.isBoundary hs.hA.isQCartier).mp
      hs.hA.isKawamataLogTerminal
  obtain ⟨Y', _, _, _, _, sY', g, p, hHF, hY'p, hgp, hY'Q, -, hkltY'⟩ :=
    exists_isHFlop_of_isKltPair hYp hQ hZ (DivisorWithCoeffs.isEffective_iff_nonneg.mp hΔe)
      hkltΔ (DivisorWithCoeffs.isEffective_iff_nonneg.mp (isEffective_toQDivisor
        (isEffective_single s.P))) hEq hsmall hc.isProjectiveMorphism hni hρ1 htriv hHf
  have hY'v : MMP.Mori.IsVariety ℂ sY' := hY'p.toIsVariety
  haveI : LocallyOfFiniteType sY' := hY'v.toLocallyOfFiniteType
  haveI : QuasiCompact sY' := hY'v.toQuasiCompact
  have hflip := hHF.2.2.2.2.2
  have hgsmall : IsSmall ℂ sZ sY' g := hflip.isSmall
  haveI : IsProper g := hflip.isProper
  have hgb : IsBirationalMorphism g := IsSmall.isBirationalMorphism sZ sY' hgsmall
  have : IsSeparated (Y' ↘ Limits.terminal Scheme) := by
    haveI := hY'v.toIsSeparated
    rw [show (Y' ↘ Limits.terminal Scheme) = sY' ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    haveI := hZv.toIsSeparated
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  -- the transform along the flop is `g⁻¹_* ∘ c_*`
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R s.Y),
      RationalMap.transformDivisor p D =
        inverseTransformDivisor g (RationalMap.transformDivisor c.toRationalMap D) :=
    fun D => transformDivisor_eq_inverseTransformDivisor hgb hsmall.exists_isIso
      hflip.isModificationOf.2 hflip.isMorphismInCodimOne D
  obtain ⟨-, P', -, -, hP', -⟩ := exists_transformPrimeDivisor_eq_some hgb hsmall.exists_isIso
    hflip.isModificationOf.2 hflip.isMorphismInCodimOne s.P
  have hPeq : RationalMap.transformDivisor p (Finsupp.single s.P (1 : ℤ)) =
      Finsupp.single P' 1 :=
    RationalMap.transformDivisor_single_of_eq_some hP' 1
  -- the projective trivial-flop bundle
  obtain ⟨-, ⟨r, hr, M, hM, hMc, ⟨MX, hBX, hMX, hpbX⟩, ⟨MY, hBY, hMY, hpbY⟩⟩, hkltY, -, -,
      hpencil⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne hYp hY'p hZ hc.comp_eq
      hgsmall.comp_eq hb hgb hsmall.exists_isIso hgsmall.exists_isIso
      hs.hA.isKawamataLogTerminal htrivQ
  have hK' : inverseTransformDivisor g (RationalMap.transformDivisor c.toRationalMap s.K) =
      RationalMap.transformDivisor p s.K := (htr s.K).symm
  have hΔ' : inverseTransformDivisor g (flopBaseDivisor c s.Δ) = flopDivisor p s.Δ :=
    (htr s.Δ).symm
  have hP'' : inverseTransformDivisor g
      (RationalMap.transformDivisor c.toRationalMap (Finsupp.single s.P (1 : ℤ))) =
      Finsupp.single P' 1 := by
    rw [← htr, hPeq]
  rw [hK', hΔ'] at hkltY hpencil hMY
  have hDY := IsTriviallyConnected.transform_of_isIsoInCodimOne hYp hY'p hZ hc.comp_eq
    hgsmall.comp_eq hb hgb hsmall.exists_isIso hgsmall.exists_isIso
    hs.hA.isKawamataLogTerminal htrivQ hs.hA.isNef hs.hD
  simp only at hDY
  rw [hK', hΔ', hP''] at hDY
  -- `K⁺ + Δ⁺` is numerically `g`-trivial
  have hLq :
      (Divisor.toQDivisor (RationalMap.transformDivisor p s.K) + flopDivisor p s.Δ).IsQCartier :=
    isQCartier_of_isQFactorial sY' hY'Q _
  have htrivY : IsNumericallyTrivialOver ℂ sY' g
      (logCanonicalDivisor (RationalMap.transformDivisor p s.K)
        (QDivisor.toRDivisor (flopDivisor p s.Δ))) := by
    have h := isNumericallyTrivialOver_of_intersectionNumber_eq_zero (f := g) hLq fun C hC => by
      rw [MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sY' C.ι C.dim_le _ hLq hr MY
        (hpbY.isCartier hMc) hMY,
        degreeOn_eq_zero_of_isPullback_of_isContractedBy hgsmall.comp_eq hMc hpbY C hC]
      simp
    rwa [map_add, QDivisor.toRDivisor_toQDivisor] at h
  -- the new model and the flop
  let s' : ChainState := ⟨Y', inferInstance, inferInstance, inferInstance, inferInstance, sY',
    inferInstance, inferInstance, RationalMap.transformDivisor p s.K, flopDivisor p s.Δ, P'⟩
  let e : Edge s := ⟨s', Z, inferInstance, inferInstance, inferInstance, inferInstance, sZ,
    inferInstance, c, g, p⟩
  have he : e.IsFlop :=
    { isTrivialFlop := ⟨IsHFlop.isTrivialFlopDatum ℂ s.sY sY' sZ hHF, hflip.isModificationOf.2⟩
      K_eq := rfl
      Δ_eq := rfl
      P_eq := hPeq.symm
      isProjectiveVariety_base := hZ
      isHFlop := hHF
      relativePicardNumber_eq := hρ1
      isNumericallyTrivialOver_flop := htrivY }
  refine ⟨e, he, ?_⟩
  haveI : Surjective g := hgsmall.toIsBirationalContraction.surjective_and_isBirational.1
  exact
    { hA :=
        { isProjectiveVariety := hY'p
          isQFactorial := hY'Q
          dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sY'
            hgb).symm.trans
              ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sY hb).trans
                hs.hA.dim_eq)
          isBoundary := hkltY.1.2
          isKawamataLogTerminal := hkltY
          isNef := isNef_of_isPullback hYp hY'p hZ hc.comp_eq hgsmall.comp_eq hMc hr hs.hA.isNef
            hpbX hMX hpbY hMY
          exists_two_le_h0 := exists_two_le_h0_of_isPullback hs hZ hc.isNormalVariety_target hY'p
            hc.comp_eq hb hgsmall.comp_eq hr hM hMc hpbY hMY
          exists_isLogEllipticFiberSpace := exists_isLogEllipticFiberSpace_of_isFlip hs hc.comp_eq
            hsmall hEx hgb hgsmall.comp_eq hEq hflip hkltY hLq }
      hL := fun h => hs.hL (hpencil.mpr h)
      hD := hDY
      hρ := (picardNumber_eq_of_isSmall hsmall hgsmall hQ hYp hY'Q hY'p).trans hs.hρ }

/-- **One step of the chain** (FA 15.9, Steps 1–4): on a model satisfying the invariant, either
the final divisorial contraction exists, or a flop to a model satisfying the invariant. -/
private theorem step {ρ : ℕ∞} {s : ChainState} (hs : s.Inv ρ) :
    s.IsFinal ∨ ∃ e : Edge s, e.IsFlop ∧ e.s'.Inv ρ := by
  obtain ⟨ε, hε, hklt, R, hR, hRL, Z, sZ, c, hc, hZ, hρ, hdesc, hcurves⟩ :=
    exists_isContractionOfRay hs.hA hs.hL hs.hD
  have hYp := hs.hA.isProjectiveVariety
  have hb : IsBirationalMorphism c :=
    isBirationalMorphism_of_forall_isContractedBy hYp hs.hA.dim_eq hc.toIsContraction s.P
      fun C hC => (hcurves C hC).2.2
  haveI : IsProper s.sY := isProper_of_isProjectiveMorphism _ hYp.isProjective
  haveI : IsProper c := isProper_of_isProjectiveMorphism _ hc.isProjectiveMorphism
  have hEx : (Mori.exceptionalSet c : Set s.Y) ⊆ s.P.support :=
    exceptionalSet_subset_of_forall_isContractedBy hYp.toIsVariety hZ.toIsVariety c hc.comp_eq hb
      hc.isIso_app (by rw [← supp_single_one]; exact DivisorWithCoeffs.isClosed_supp _)
      fun C hC => (hcurves C hC).2.2
  by_cases heq : (Mori.exceptionalSet c : Set s.Y) = s.P.support
  · exact Or.inl (isFinal_of_exceptionalSet_eq hs hε hklt hR hRL hc hZ hρ hdesc hcurves hb heq)
  · exact Or.inr (exists_isFlop_of_exceptionalSet_ssubset hs hε hklt hR hRL hc hZ hρ hdesc hcurves
      hb (Set.ssubset_iff_subset_ne.mpr ⟨hEx, heq⟩))

/-- The trivial edge from a model to itself, used after the chain has stopped. -/
private noncomputable def idEdge (s : ChainState) : Edge s where
  s' := s
  T := s.Y
  isIntegral := inferInstance
  compactSpace := inferInstance
  isLocallyNoetherian := inferInstance
  isNormal := inferInstance
  sT := s.sY
  locallyOfFiniteType := inferInstance
  φ := 𝟙 _
  φp := 𝟙 _
  p := Scheme.Hom.toRationalMap (𝟙 s.Y)

open Classical in
/-- The next edge of the chain: the flop given by `step` when the chain has not stopped. -/
private noncomputable def next {ρ : ℕ∞} (s : {s : ChainState // s.Inv ρ}) : Edge s.1 :=
  if h : s.1.IsFinal then idEdge s.1 else Classical.choose ((step s.2).resolve_left h)

private theorem next_inv {ρ : ℕ∞} (s : {s : ChainState // s.Inv ρ}) : (next s).s'.Inv ρ := by
  unfold next
  split_ifs with h
  · exact s.2
  · exact (Classical.choose_spec ((step s.2).resolve_left h)).2

private theorem next_isFlop {ρ : ℕ∞} (s : {s : ChainState // s.Inv ρ}) (h : ¬ s.1.IsFinal) :
    (next s).IsFlop := by
  unfold next
  rw [dif_neg h]
  exact (Classical.choose_spec ((step s.2).resolve_left h)).1

/-- The models of the chain. -/
private noncomputable def seq {ρ : ℕ∞} (s₀ : {s : ChainState // s.Inv ρ}) :
    ℕ → {s : ChainState // s.Inv ρ}
  | 0 => s₀
  | i + 1 => ⟨(next (seq s₀ i)).s', next_inv _⟩

/-- **Termination of the chain**: the chain stops at some model. -/
private theorem exists_isFinal (hterm : HFlopSequencesTerminate) {ρ : ℕ∞}
    (s₀ : {s : ChainState // s.Inv ρ}) : ∃ m, (seq s₀ m).1.IsFinal := by
  by_contra hne
  push Not at hne
  let S : ℕ → ChainState := fun i => (seq s₀ i).1
  have hinv : ∀ i, (S i).Inv ρ := fun i => (seq s₀ i).2
  have hflop : ∀ i, (next (seq s₀ i)).IsFlop := fun i => next_isFlop _ (hne i)
  have hkltP : ∀ i, Mori.IsKltPair (S i).sY 3 (S i).K (S i).Δ := fun i =>
    (isKawamataLogTerminal_iff_isKltPair (S i).sY 3 (S i).K (S i).Δ
      (hinv i).hA.isQFactorial.1 (hinv i).hA.isKawamataLogTerminal.2.1 (hinv i).hA.isBoundary
      (hinv i).hA.isQCartier).mp (hinv i).hA.isKawamataLogTerminal
  have hlt := hterm (fun i => (S i).Y) (fun i => (S i).sY) (fun i => (S i).K) (fun i => (S i).Δ)
    (fun i => Divisor.toQDivisor (Finsupp.single (S i).P 1))
    (hinv 0).hA.isProjectiveVariety (hinv 0).hA.dim_eq (hinv 0).hA.isQFactorial
    (fun E => by simpa using ((hinv 0).hA.isBoundary E).1) (hkltP 0)
    (fun E => by
      change (0 : ℚ) ≤ ((Finsupp.single (S 0).P (1 : ℤ) E : ℤ) : ℚ)
      by_cases hE : (S 0).P = E <;> simp [Finsupp.single_apply, hE])
    (by
      obtain ⟨m, hm, hc⟩ := (hinv 0).hA.isQFactorial.2 (Finsupp.single (S 0).P 1)
      exact ⟨m, by omega, by rw [← map_zsmul]; exact QDivisor.isCartierDivisor_toQDivisor.mpr hc⟩)
    ⊤ (fun i => (next (seq s₀ i)).T) (fun i => (next (seq s₀ i)).sT)
    (fun i => (next (seq s₀ i)).φ) (fun i => (next (seq s₀ i)).φp)
    (fun i => (next (seq s₀ i)).p)
    (fun i _ => (hinv i).hA.isProjectiveVariety) (fun i _ => (hinv i).hA.isQFactorial)
    (fun i _ => (hinv i).hA.isKawamataLogTerminal.2.1)
    (fun i _ => (hflop i).isHFlop) (fun i _ => (hflop i).relativePicardNumber_eq)
    (fun i _ => (hflop i).isProjectiveVariety_base)
    (fun i _ => (hflop i).isNumericallyTrivialOver_flop)
    (fun i _ => (hflop i).Δ_eq)
    (fun i _ => by
      change Divisor.toQDivisor (Finsupp.single (next (seq s₀ i)).s'.P 1) = _
      rw [(hflop i).P_eq]
      exact (transformDivisor_toQDivisor _ _).symm)
  exact lt_irrefl _ hlt

end MMP.FourfoldProofs.Fa15TriviallyConnectedBecomesContractibleProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold MMP.FourfoldProofs.Fa15TriviallyConnectedBecomesContractibleProof

/-- **The FA 15.9 chain of trivial flops, with its projective models** (FA 15.9). Let `(X, Δ)`
satisfy the assumptions of FA 15.4 over `ℂ`, with `K + Δ` not eventually free and composed of a
pencil, and let `D` be a `(K + Δ)`-trivially connected prime divisor. Assume that sequences of
`H`-flops on projective klt threefolds terminate (`MMP.Flips.HFlopSequencesTerminate`).

Then there are `m : ℕ` and a chain `X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` (`X_{i+1} = Y i`) with prime divisors
`P i` on `Y i`, such that for `i < m`:
* `(Y i, ΔY i)` satisfies the assumptions of 15.4, `K + ΔY i` is not eventually free and composed
  of a pencil, `P i` is trivially connected and `ρ(Y i) = ρ(X)`;
* the `i`-th step is the flop `p i` of the `(K_i + Δ_i)`-trivial flop datum
  `(φ i : X_i ⟶ T i, φp i : Y i ⟶ T i)` over a projective base `T i`, with `φ i` of relative
  Picard number one; `K`, `Δ` and `D` are transformed along `p i`.
Finally `D_m` is the exceptional set of a birational contraction `c : X_m ⟶ X'` with
`K_m + Δ_m ∼_ℚ c^*(K' + Δ')`, `ρ(X') + 1 = ρ(X)`, and `(X', Δ')` satisfying the assumptions of
15.4. -/
public theorem exists_trivialFlop_chain_projective_of_isTriviallyConnected
    (hterm : HFlopSequencesTerminate)
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X}
    (hA : SatisfiesAbundanceAssumptions ℂ sX K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ))
    {D : Mori.PrimeDivisor X} (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (m : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (_ : ∀ i, LocallyOfFiniteType (sY i)) (_ : ∀ i, QuasiCompact (sY i))
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, QDivisor (Y i)) (P : ∀ i, Mori.PrimeDivisor (Y i))
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (T i)) (_ : ∀ i, CompactSpace (T i))
      (_ : ∀ i, IsLocallyNoetherian (T i)) (_ : ∀ i, IsNormal (T i))
      (_ : ∀ i, LocallyOfFiniteType (sT i))
      (φ : ∀ i, modelSeq X Y i ⟶ T i) (φp : ∀ i, Y i ⟶ T i)
      (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i < m, SatisfiesAbundanceAssumptions ℂ (sY i) (KY i) (ΔY i) ∧
        ¬ IsEventuallyFreePencil ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i) ∧
        IsTriviallyConnected ℂ (sY i) 3 (KY i) (ΔY i) (Finsupp.single (P i) 1) ∧
        picardNumber (sY i) = picardNumber sX) ∧
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = Mori.RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        (Finsupp.single (P i) 1 : Divisor (Y i)) = Mori.RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) (fun j => Finsupp.single (P j) 1) i) ∧
        Mori.IsProjectiveVariety ℂ (sT i) ∧
        Flips.relativePicardNumber (modelStr sX sY i) (φ i) = 1) ∧
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : modelSeq X Y m ⟶ X')
        (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
        IsBirationalContraction ℂ sX' (modelStr sX sY m) c ∧ IsBirationalMorphism c ∧
        exceptionalSet c =
          (DivisorWithCoeffs.supp (divisorSeq (Finsupp.single D 1 : Divisor X)
            (fun j => Finsupp.single (P j) 1) m) : Set (modelSeq X Y m)) ∧
        (∃ (hc : ∀ Z : irreducibleComponents (modelSeq X Y m),
            c (componentGenericPoint (modelSeq X Y m) Z) ∉
              (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap
                (divisorSeq K KY m)) +
                Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp)
            (B : QDivisor (modelSeq X Y m)),
          (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap
              (divisorSeq K KY m)) +
              Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).IsPullback
            c hc B ∧
            (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent B) ∧
        picardNumber sX' + 1 = picardNumber sX ∧
        SatisfiesAbundanceAssumptions ℂ sX'
          (Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m))
          (Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)) := by
  classical
  let s₀ : {s : ChainState // s.Inv (picardNumber sX)} :=
    ⟨⟨X, inferInstance, inferInstance, inferInstance, inferInstance, sX, inferInstance,
      inferInstance, K, Δ, D⟩, ⟨hA, hL, hD, rfl⟩⟩
  have hex := exists_isFinal hterm s₀
  obtain ⟨m, hm, hmin⟩ : ∃ m, (seq s₀ m).1.IsFinal ∧ ∀ i < m, ¬ (seq s₀ i).1.IsFinal :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hflop : ∀ i < m, (next (seq s₀ i)).IsFlop := fun i hi => next_isFlop _ (hmin i hi)
  refine ⟨m, fun i => (seq s₀ (i + 1)).1.Y, fun i => (seq s₀ (i + 1)).1.sY,
    fun i => inferInstance, fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance, fun i => inferInstance,
    fun i => (seq s₀ (i + 1)).1.K, fun i => (seq s₀ (i + 1)).1.Δ, fun i => (seq s₀ (i + 1)).1.P,
    fun i => (next (seq s₀ i)).T, fun i => (next (seq s₀ i)).sT,
    fun i => inferInstance, fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance,
    fun i => match i with
      | 0 => (next (seq s₀ 0)).φ
      | j + 1 => (next (seq s₀ (j + 1))).φ,
    fun i => (next (seq s₀ i)).φp,
    fun i => match i with
      | 0 => (next (seq s₀ 0)).p
      | j + 1 => (next (seq s₀ (j + 1))).p, ?_, ?_, ?_⟩
  · intro i _
    have h := (seq s₀ (i + 1)).2
    exact ⟨h.hA, h.hL, h.hD, h.hρ⟩
  · intro i hi
    have h := hflop i hi
    cases i with
    | zero => exact ⟨h.isTrivialFlop, h.K_eq, h.Δ_eq, h.P_eq, h.isProjectiveVariety_base,
        h.relativePicardNumber_eq⟩
    | succ j => exact ⟨h.isTrivialFlop, h.K_eq, h.Δ_eq, h.P_eq, h.isProjectiveVariety_base,
        h.relativePicardNumber_eq⟩
  · have hρ := (seq s₀ m).2.hρ
    clear hmin hflop
    cases m with
    | zero =>
      obtain ⟨X', sX', c, i₁, i₂, i₃, i₄, i₅, i₆, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hm
      exact ⟨X', sX', c, i₁, i₂, i₃, i₄, i₅, i₆, h₁, h₂, h₃, h₄, h₅.trans hρ, h₆⟩
    | succ j =>
      obtain ⟨X', sX', c, i₁, i₂, i₃, i₄, i₅, i₆, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hm
      exact ⟨X', sX', c, i₁, i₂, i₃, i₄, i₅, i₆, h₁, h₂, h₃, h₄, h₅.trans hρ, h₆⟩

/-- **A trivially connected prime divisor becomes contractible** (FA 15.9), given the termination
of `H`-flops (`MMP.Flips.HFlopSequencesTerminate`). Let `(X, Δ)` satisfy the assumptions of
FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over `ℂ`, with `K + Δ` not eventually free and
composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`). Let `D` be a prime divisor on `X`
which is `(K + Δ)`-trivially connected (`MMP.Flips.IsTriviallyConnected`).

Then there are `m : ℕ` and a chain `X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` of flops `p_i` of
`(K_i + Δ_i)`-trivial flop data (`MMP.Flips.IsTrivialFlop`), with `X_{i+1} = Y i`. Here
`K_{i+1}`, `Δ_{i+1} = MMP.Flips.flopDivisor p_i Δ_i` and `D_{i+1}` are the birational
transforms along `p_i`. There is also a birational contraction `c : X_m ⟶ X'`
(`MMP.Flips.IsBirationalContraction`, so `c_* 𝒪_{X_m} = 𝒪_{X'}`) whose exceptional set
(`MMP.Flips.exceptionalSet`) is `Supp D_m`. With `K' = c_* K_m` and `Δ' = c_* Δ_m`, the following
hold: `K_m + Δ_m` is `ℚ`-linearly equivalent to the pull-back `c^*(K' + Δ')`,
`ρ(X') + 1 = ρ(X)`, and `(X', Δ')` satisfies the assumptions of FA 15.4. -/
public theorem IsTriviallyConnected.exists_isBirationalContraction_of_hFlopSequencesTerminate
    (hterm : HFlopSequencesTerminate)
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X}
    (hA : SatisfiesAbundanceAssumptions ℂ sX K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ))
    {D : Mori.PrimeDivisor X} (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (m : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, QDivisor (Y i)) (DY : ∀ i, Divisor (Y i))
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ)) (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = Mori.RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = Mori.RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i)) ∧
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : modelSeq X Y m ⟶ X')
        (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
        IsBirationalContraction ℂ sX' (modelStr sX sY m) c ∧ IsBirationalMorphism c ∧
        exceptionalSet c =
          ((divisorSeq (Finsupp.single D 1 : Divisor X) DY m).supp : Set (modelSeq X Y m)) ∧
        (∃ (hc : ∀ Z : irreducibleComponents (modelSeq X Y m),
            c (componentGenericPoint (modelSeq X Y m) Z) ∉
              (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap
                (divisorSeq K KY m)) +
                Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp)
            (B : QDivisor (modelSeq X Y m)),
          (Divisor.toQDivisor (Mori.RationalMap.transformDivisor c.toRationalMap
              (divisorSeq K KY m)) +
              Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).IsPullback
            c hc B ∧
            (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent B) ∧
        picardNumber sX' + 1 = picardNumber sX ∧
        SatisfiesAbundanceAssumptions ℂ sX'
          (Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m))
          (Mori.RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)) := by
  obtain ⟨m, Y, sY, i₁, i₂, i₃, i₄, -, -, KY, ΔY, P, T, sT, -, -, -, -, -, φ, φp, p, -, hflop,
    hfin⟩ := exists_trivialFlop_chain_projective_of_isTriviallyConnected hterm hA hL hD
  exact ⟨m, Y, sY, i₁, i₂, i₃, i₄, KY, ΔY, fun j => Finsupp.single (P j) 1, T, sT, φ, φp, p,
    fun i hi => ⟨(hflop i hi).1, (hflop i hi).2.1, (hflop i hi).2.2.1, (hflop i hi).2.2.2.1⟩,
    hfin⟩

end MMP.Flips

end
