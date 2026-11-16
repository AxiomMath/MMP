module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
public import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
public import MMP.AlgebraicGeometry.MMP.Fourfold.RealDltElementaryStep
public import MMP.AlgebraicGeometry.MMP.Fourfold.RealLcNefThreshold
public import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Flip.ProcedureDatumExistence
public import MMP.AlgebraicGeometry.MMP.Flip.ProcedureDivisorSpan
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelAmplePerturbation
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.FiniteGeography
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Morphisms.CurveFactorization
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Termination of the real klt fourfold program with scaling over a birational base

Let `π : X ⟶ Z` be a projective birational morphism of normal projective complex varieties, with
`X` a `ℚ`-factorial fourfold, and let `B, C ≥ 0` be real `ℝ`-Cartier divisors on `X` such that
`(X, B + C)` is klt and `K_X + B + C` is nef over `Z`. The `(K_X + B)`-program over `Z` with
scaling of `C` runs as follows. At a model `(X_i, B_i, C_i)` let
`λ_i = min {t ≥ 0 | K_{X_i} + B_i + t C_i is nef over Z}` be the nef threshold. If `λ_i > 0`,
contract over `Z` a `(K_{X_i} + B_i)`-negative extremal ray on which `K_{X_i} + B_i + λ_i C_i` is
numerically trivial; a divisorial contraction gives the next model, a small one is replaced by
its flip, and `B_{i+1}`, `C_{i+1}` are the birational transforms. The program stops when
`K_{X_i} + B_i` is nef over `Z`. Since every model is birational to `Z` over `Z`, no contraction
of fibre type occurs.

The theorem: such a program exists and reaches a model whose adjoint `K + B` is nef over `Z`,
and every such program has finitely many steps.

## Main results

* `MMP.Fourfold.exists_scalingProgram_and_finite_of_isBirationalMorphism`

## Implementation notes

The models are indexed as in `MMP.Fourfold.RelativeDltProgram`: `X₀ = X`, `X_{i+1} = Y i`
(`MMP.Fourfold.modelSeq`), with structure morphisms `MMP.Fourfold.modelStr` over `ℂ`,
`MMP.Fourfold.modelMap` over `Z`, and divisors `MMP.Fourfold.divisorSeq`; the number of steps
is `n ∈ ℕ ∪ {∞}`, and only the data indexed by `i ≤ n` (models) and `i < n` (steps) are
constrained. Every model `X_i`, `i ≤ n`, is a `ℚ`-factorial projective variety over `Z` with a
canonical divisor `K_i` and `(X_i, B_i)` klt. Step `i` is a contraction `f_i : X_i ⟶ W_i` onto a
projective variety over `Z` (by `g_i`) which is a `(K_i + B_i)`-negative extremal contraction
(`MMP.Flips.IsNegativeExtremalContraction`: `-(K_i + B_i)` is `f_i`-ample and
`ρ(X_i/W_i) = 1`), with `K_i + B_i + λ_i C_i` numerically trivial over `W_i`, followed by
`f_i⁺ : X_{i+1} ⟶ W_i` and `φ_i : X_i ⤏ X_{i+1}`: either `f_i` is divisorial and `f_i⁺` an
isomorphism, or `(f_i⁺, φ_i)` is the flip of the small `f_i` (`MMP.Flips.IsFlip`). The
`ℝ`-divisors `B_{i+1}`, `C_{i+1}` are the transforms `(φ_i)_* B_i`, `(φ_i)_* C_i`. The scaling
threshold is the least `t ≥ 0` with `K_i + B_i + t C_i` nef over `Z`; the relative nef cone is
closed, so the infimum is attained.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.31
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_real_birational_fourfold_scaling_termination

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Numerical helpers -/

section Numerical

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- If `ρ(X/W) = 1`, some proper curve is contracted by `f`. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one {W : Scheme.{0}}
    (f : X ⟶ W) (hρ : MMP.Flips.relativePicardNumber sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  have hfin : Module.finrank ℝ (MMP.Flips.RelativeNumericalDivisorClasses sX f) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  haveI := Module.finite_of_finrank_eq_succ hfin
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp (by rw [hfin]; exact one_pos)
  obtain ⟨δ, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors] at hv
  push Not at hv
  obtain ⟨C, hC, -⟩ := hv
  exact ⟨C, hC⟩

/-- A divisor whose negative is `f`-ample has negative intersection number, computed with any
presentation, on every proper curve contracted by `f`. -/
private theorem isRIntersectionNumber_neg_of_isRelativelyAntiAmple {W : Scheme.{0}}
    (f : X ⟶ W) {L : RDivisor X} (hL : IsRelativelyAntiAmple f L) (Γ : ProperCurve sX)
    (hΓ : Γ.IsContractedBy f) {m : ℕ} (r : Fin m → ℝ) (Ls : Fin m → Divisor X) (x : ℝ)
    (hx : IsRIntersectionNumber k sX L r Ls Γ x) : x < 0 := by
  obtain ⟨m', a, A, hm, ha, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hLeq' : L = ∑ j, (-a j) • Divisor.toRDivisor (A j) := by
    have hL' : L = -(-L) := (neg_neg L).symm
    rw [hL', hLeq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX Γ (fun j => -a j) A hAc
  rw [← hLeq'] at hy
  rw [(IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hx hy]
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j => by
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) Γ hΓ
  have hsum : 0 < ∑ j, a j * ((A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- The adjoint of a negative extremal contraction `f : X ⟶ W` over `Z` is not nef over `Z`. -/
private theorem not_isRelativelyNef_of_isNegativeExtremalContraction {W Z : Scheme.{0}}
    {sW : W ⟶ Spec (.of k)} {E : RDivisor X} {f : X ⟶ W} {g : W ⟶ Z} {π : X ⟶ Z}
    (hf : IsNegativeExtremalContraction k sX sW E f) (hfg : f ≫ g = π) :
    ¬ IsRelativelyNef k sX π E := by
  rintro ⟨m, r, L, hL, hE, hnef⟩
  obtain ⟨Γ, hΓ⟩ := exists_isContractedBy_of_relativePicardNumber_eq_one f
    hf.relativePicardNumber_eq_one
  have hΓπ : Γ.IsContractedBy π := fun x hx => by
    rw [← hfg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ x hx]
  have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX Γ r L hL
  rw [← hE] at hx
  exact (hnef Γ hΓπ _ hx).not_gt
    (isRIntersectionNumber_neg_of_isRelativelyAntiAmple f hf.isRelativelyAntiAmple Γ hΓ r L _ hx)

/-- The pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {D : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f D G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  refine ⟨m, r, L', fun j => ?_, rfl⟩
  obtain ⟨hB, hp⟩ := hpb j
  exact hp.isCartier (hL j)

/-- Nefness over `g ≫ h` implies nefness over `g`: a curve contracted by `g` is contracted by
`g ≫ h`. -/
private theorem IsRelativelyNef.of_comp {Y S : Scheme.{0}} {g : X ⟶ Y} {h : Y ⟶ S}
    {D : RDivisor X} (hD : IsRelativelyNef k sX (g ≫ h) D) : IsRelativelyNef k sX g D := by
  obtain ⟨m, r, L, hL, hDeq, hnef⟩ := hD
  exact ⟨m, r, L, hL, hDeq, fun C hC x hx => hnef C (fun y hy => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC y hy]) x hx⟩

/-- A divisor nef over `g` has nonnegative intersection number, computed with any presentation, on
every curve contracted by `g`. -/
private theorem IsRelativelyNef.nonneg {Y : Scheme.{0}} {g : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef k sX g D) {C : ProperCurve sX} (hC : C.IsContractedBy g) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber k sX D r L C x) :
    0 ≤ x := by
  obtain ⟨m', r', L', hL', hD', hn⟩ := h
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hD'] at e
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx e]
  exact hn C hC _ e

/-- Nefness does not depend on how the structure morphism is written. -/
private theorem IsRelativelyNef.of_eq_structure {Y : Scheme.{0}} {s s' : X ⟶ Spec (.of k)}
    (hs : s = s') [QuasiCompact s'] {g : X ⟶ Y} {D : RDivisor X}
    (hD : IsRelativelyNef k s g D) : IsRelativelyNef k s' g D := by
  subst hs
  exact hD

/-- A sum of divisors nef over `g` is nef over `g`. -/
private theorem IsRelativelyNef.add {Y : Scheme.{0}} {g : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef k sX g D₁) (h₂ : IsRelativelyNef k sX g D₂) :
    IsRelativelyNef k sX g (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂, hn₂⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂,
    Fin.addCases (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i), ?_,
    fun C hC x hx => ?_⟩
  · rw [Fin.sum_univ_add, hD₁, hD₂]
    simp only [Fin.append_left, Fin.append_right]
  · have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
    have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
    rw [← hD₁] at e₁
    rw [← hD₂] at e₂
    have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ _ _ 1 1 e₁ e₂
    simp only [one_smul, one_mul] at hsum
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hsum]
    exact add_nonneg (hn₁ C hC _ e₁) (hn₂ C hC _ e₂)

/-- A nonnegative multiple of a divisor nef over `g` is nef over `g`. -/
private theorem IsRelativelyNef.smul {Y : Scheme.{0}} {g : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef k sX g D) {a : ℝ} (ha : 0 ≤ a) : IsRelativelyNef k sX g (a • D) := by
  obtain ⟨m, r, L, hL, hD, hn⟩ := h
  have hD' : a • D = ∑ j, (a • r) j • Divisor.toRDivisor (L j) := by
    rw [hD, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul]
  refine ⟨m, a • r, L, hL, hD', fun C hC x hx => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (a • r) L hL
  rw [← hD'] at e
  have e0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
  rw [← hD] at e0
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx e]
  have h0 := hn C hC _ e0
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_nonneg ha h0

/-- **Nefness descends along a surjection.** Let `q : V ⟶ Y` be a proper surjective morphism of
schemes of finite type over `k` and `G = q^*D` the pull-back of an `ℝ`-Cartier divisor `D`. If
`G` is nef over `q ≫ π`, then `D` is nef over `π`: every curve `C` contracted by `π` is the image
of a curve `C'` contracted by `q ≫ π`, and `G · C' = [k(C') : k(C)] (D · C)`. -/
private theorem IsRelativelyNef.of_isRCartierPullback {V Y S : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsLocallyNoetherian Y] [IsNormal Y]
    {sV : V ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sV] [QuasiCompact sV]
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsSeparated sY] (q : V ⟶ Y) [IsProper q]
    [Surjective q] (hq : q ≫ sY = sV) (π : Y ⟶ S) {D : RDivisor Y} {G : RDivisor V}
    (hG : IsRCartierPullback q D G) (hnef : IsRelativelyNef k sV (q ≫ π) G) :
    IsRelativelyNef k sY π D := by
  obtain ⟨m, r, L, L', hL, hD, hpb, hG'⟩ := hG
  refine ⟨m, r, L, hL, hD, fun C hC x hx => ?_⟩
  obtain ⟨C', hC'q, hdeg⟩ := MMP.Fourfold.exists_properCurve_map_eq sV sY q hq C
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hpb j).2.isCartier (hL j)
  have hC'π : C'.IsContractedBy (q ≫ π) := fun y hy => by
    have hy' : q y ∈ closure (q '' ({C'.point} : Set V)) :=
      image_closure_subset_closure_image q.continuous ⟨y, hy, rfl⟩
    rw [Set.image_singleton, hC'q] at hy'
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC _ hy', hC'q]
  have hx' := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sV C' r L' hL'c
  rw [← hG'] at hx'
  have hpos := IsRelativelyNef.nonneg hnef hC'π hx'
  have hx0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sY C r L hL
  rw [← hD] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hx0]
  have hmul : ∀ j, ((L' j).degreeOn k sV C'.ι C'.dim_le (hL'c j) : ℝ) =
      (residueFieldDegree q C'.point : ℝ) * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) :=
    fun j => MMP.Fourfold.degreeOn_eq_mul_of_isPullback q hq (hL j) (hpb j).2 (hL'c j) C' C hC'q
  simp only [hmul, mul_left_comm (r _), ← Finset.mul_sum] at hpos
  have he : (0 : ℝ) < residueFieldDegree q C'.point := by exact_mod_cast Nat.pos_of_ne_zero hdeg
  exact (mul_nonneg_iff_of_pos_left he).mp hpos

end Numerical

/-! ### Programs with scaling -/

section Program

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (K : Divisor X) (B C : RDivisor X)
  {Y : ℕ → Scheme.{0}} (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
  [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
  (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
  (lam : ℕ → ℝ) {W : ℕ → Scheme.{0}} (sW : ∀ i, W i ⟶ Spec (.of ℂ))
  (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
  (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))

/-- The conditions on the `i`-th model of a `(K + B)`-program over `Z`. -/
private def IsModelAt (i : ℕ) : Prop :=
  modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        ∀ P, 0 ≤ (divisorSeq B BY i).coeff P

/-- The conditions on the `i`-th step of a `(K + B)`-program over `Z` with scaling of `C`. -/
private def IsStepAt (i : ℕ) : Prop :=
  IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)

end Program

/-! ### Rational maps over a birational base -/

section OverBase

/-- **Rational maps into a model of a birational base are unique.** Two rational maps
`φ, φ' : X₁ ⤏ X₂` agreeing after a proper birational morphism `π₂ : X₂ ⟶ S` onto a normal scheme,
with `φ.compHom π₂` dominant, are equal: on a dense open where both are defined they agree after
`π₂`, hence agree. -/
private theorem rationalMap_eq_of_compHom_eq {X₁ X₂ S : Scheme.{0}} [IsIntegral X₁]
    [IsIntegral X₂] [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] {π₂ : X₂ ⟶ S}
    [IsProper π₂] (hπ₂ : IsBirationalMorphism π₂) {π₁ : X₁ ⟶ S} [IsDominant π₁]
    {φ φ' : X₁.RationalMap X₂} (h : φ.compHom π₂ = π₁.toRationalMap)
    (h' : φ'.compHom π₂ = π₁.toRationalMap) : φ = φ' := by
  obtain ⟨g, rfl⟩ := φ.exists_rep
  obtain ⟨g', rfl⟩ := φ'.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff] at h h'
  obtain ⟨U, hU, hUl, _hUr, hUe⟩ := h
  obtain ⟨U', hU', hU'l, _hU'r, hU'e⟩ := h'
  have hUl' : U ≤ g.domain := hUl
  have hU'l' : U' ≤ g'.domain := hU'l
  have hUe' : X₁.homOfLE hUl' ≫ g.hom ≫ π₂ = U.ι ≫ π₁ := by
    have := hUe
    change X₁.homOfLE hUl' ≫ g.hom ≫ π₂ =
      X₁.homOfLE (le_top : U ≤ ⊤) ≫ X₁.topIso.hom ≫ π₁ at this
    rw [this, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  have hU'e' : X₁.homOfLE hU'l' ≫ g'.hom ≫ π₂ = U'.ι ≫ π₁ := by
    have := hU'e
    change X₁.homOfLE hU'l' ≫ g'.hom ≫ π₂ =
      X₁.homOfLE (le_top : U' ≤ ⊤) ≫ X₁.topIso.hom ≫ π₁ at this
    rw [this, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  have hd : Dense ((U ⊓ U' : X₁.Opens) : Set X₁) := by
    simpa using hU.inter_of_isOpen_left hU' U.isOpen
  have hl : U ⊓ U' ≤ g.domain := inf_le_left.trans hUl'
  have hr : U ⊓ U' ≤ g'.domain := inf_le_right.trans hU'l'
  refine ⟨U ⊓ U', hd, hl, hr, ?_⟩
  haveI hne : Nonempty (U ⊓ U' : X₁.Opens) := by
    obtain ⟨x, hx⟩ := hd.nonempty
    exact ⟨⟨x, hx⟩⟩
  have e₁ : X₁.homOfLE hl ≫ g.hom ≫ π₂ = (U ⊓ U').ι ≫ π₁ := by
    rw [← X₁.homOfLE_homOfLE (inf_le_left : U ⊓ U' ≤ U) hUl', Category.assoc, hUe',
      X₁.homOfLE_ι_assoc]
  have e₂ : X₁.homOfLE hr ≫ g'.hom ≫ π₂ = (U ⊓ U').ι ≫ π₁ := by
    rw [← X₁.homOfLE_homOfLE (inf_le_right : U ⊓ U' ≤ U') hU'l', Category.assoc, hU'e',
      X₁.homOfLE_ι_assoc]
  haveI : IsDominant (U ⊓ U').ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hd⟩
  haveI : IsDominant ((X₁.homOfLE hl ≫ g.hom) ≫ π₂) := by
    rw [Category.assoc, e₁]; infer_instance
  have key : X₁.homOfLE hl ≫ g.hom = X₁.homOfLE hr ≫ g'.hom :=
    MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hπ₂ (by rw [Category.assoc, Category.assoc, e₁, e₂])
  exact key

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- **A modification onto a model without exceptional divisors extracts none.** Let
`φ : X₁ ⤏ X₂` be a modification of `f₁ : X₁ ⟶ V` into `f₂ : X₂ ⟶ V`, proper birational morphisms
of normal varieties, where `f₂` sends the generic point of every prime divisor of `X₂` to the
generic point of a prime divisor of `V`. Then every prime divisor of `X₂` is the transform of a
prime divisor of `X₁`. -/
private theorem exists_transformPrimeDivisor_eq_some_of_isModificationOf
    {X₁ X₂ V : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) (hV : IsNormalVariety ℂ sV)
    {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hf₁s : f₁ ≫ sV = s₁) (hf₂s : f₂ ≫ sV = s₂)
    [IsProper f₁] [IsProper f₂] (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (hf₂c : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ Q : MMP.Mori.PrimeDivisor V, f₂ F.genericPoint = Q.genericPoint)
    {φ : X₁.RationalMap X₂} (hφ : IsModificationOf f₁ f₂ φ) (F : MMP.Mori.PrimeDivisor X₂) :
    ∃ R : MMP.Mori.PrimeDivisor X₁, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F := by
  obtain ⟨Q, hQ⟩ := hf₂c F
  obtain ⟨R, hR, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hV
      (by rw [hf₁s]; exact hX₁) hf₁ Q
  obtain ⟨W, p, q, hWv, hWsm, hp, hq, hpb, hqb, ⟨ψ, hψinv, hψ⟩, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model s₁ s₂ sV hX₁ hX₂ hV.1 f₁ f₂ hf₁s hf₂s φ hφ
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI := hWv.toIsSeparated
  haveI : IsSeparated p := IsSeparated.of_comp p s₁
  haveI : IsSeparated (f₂ ≫ sV) := by rw [hf₂s]; infer_instance
  haveI : IsSeparated f₂ := IsSeparated.of_comp f₂ sV
  haveI := hf₂.isDominant
  obtain ⟨RW, hRW, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁
      ⟨hWv, inferInstance⟩ hpb R
  refine ⟨R, (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hψinv q hψ R RW
    hRW F).mpr ?_⟩
  have h1 : f₂ (q RW.genericPoint) = Q.genericPoint := by
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, hRW, hR]
  have := Q.isDiscreteValuationRing_localRing
  exact MMP.Fourfold.eq_of_map_eq_of_valuationRing hf₂.functionFieldMap_bijective h1 hQ

end OverBase

/-! ### Transport across one step -/

section StepTransport

/-- The rational map of a morphism, composed with a morphism. -/
private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨⊤, dense_univ, le_rfl, le_rfl, ?_⟩
  simp [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom, Scheme.Hom.toPartialMap]

/-- **A rational map over a birational base through a common model.** Let `q₁ : W ⟶ X₁`,
`q₂ : W ⟶ X₂` with `q₁ ≫ π₁ = q₂ ≫ π₂` over `S`, where `π₂` is proper birational onto a normal
scheme, and let `h` be an inverse of `q₁`. Every rational map `φ : X₁ ⤏ X₂` over `S` is
`q₂ ∘ h`. -/
private theorem compHom_eq_of_isInverse_of_isOver {X₁ X₂ W S : Scheme.{0}} [IsIntegral X₁]
    [IsIntegral X₂] [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] [IsReduced W]
    [IsSeparated (X₁ ↘ ⊤_ Scheme)] {q₁ : W ⟶ X₁} {q₂ : W ⟶ X₂} {π₁ : X₁ ⟶ S} {π₂ : X₂ ⟶ S}
    [IsProper π₂] [IsDominant π₁] (hπ₂ : IsBirationalMorphism π₂) (hcomm : q₁ ≫ π₁ = q₂ ≫ π₂)
    {h : X₁.RationalMap W} (hinv : MMP.Mori.RationalMap.IsInverse q₁.toRationalMap h)
    {φ : X₁.RationalMap X₂} (hφ : MMP.Flips.RationalMap.IsOver π₁ π₂ φ) : h.compHom q₂ = φ := by
  refine rationalMap_eq_of_compHom_eq hπ₂ (π₁ := π₁) ?_ hφ
  rw [MMP.Fourfold.Oai4C1.Main.compHom_compHom, ← hcomm,
    ← MMP.Fourfold.Oai4C1.Main.compHom_compHom, MMP.Fourfold.Crepant.compHom_eq_of_isInverse hinv,
    toRationalMap_compHom, Category.id_comp]

/-- **Nefness over the base survives a step.** Let `φ : X₁ ⤏ X₂` be a modification of
`f₁ : X₁ ⟶ V` into `f₂ : X₂ ⟶ V`, with `X₁`, `X₂` `ℚ`-factorial and `X₂ ⟶ V` contracting no
divisor, and let `g : V ⟶ Z`. If `N` is `ℝ`-Cartier, numerically trivial over `V` and nef over
`Z`, then `φ_* N` is nef over `Z`: on a common model the two pull-backs agree, and nefness passes
up along one side and down along the other. -/
private theorem isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver
    {X₁ X₂ V Z : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [CompactSpace X₁] [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂] [CompactSpace X₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    (hX₁ : IsQFactorial s₁) (hX₁p : MMP.Mori.IsProjectiveVariety ℂ s₁) (hX₂ : IsQFactorial s₂)
    (hX₂p : MMP.Mori.IsProjectiveVariety ℂ s₂) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hVn : IsNormalVariety ℂ sV) {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hf₁s : f₁ ≫ sV = s₁)
    (hf₂s : f₂ ≫ sV = s₂) (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (hf₂c : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ Q : MMP.Mori.PrimeDivisor V, f₂ F.genericPoint = Q.genericPoint)
    {φ : X₁.RationalMap X₂} (hφ : IsModificationOf f₁ f₂ φ) (g : V ⟶ Z) {N : RDivisor X₁}
    (htriv : IsNumericallyTrivialOver ℂ s₁ f₁ N) (hnef : IsRelativelyNef ℂ s₁ (f₁ ≫ g) N) :
    IsRelativelyNef ℂ s₂ (f₂ ≫ g) (MMP.Mori.RationalMap.transformDivisor φ N) := by
  haveI := hVn.1
  haveI := hVn.1.toIsSeparated
  haveI := hX₁p.toIsVariety.toIsSeparated
  haveI := hX₂p.toIsVariety.toIsSeparated
  haveI : IsProper s₁ := isProper_of_isProjectiveMorphism s₁ hX₁p.isProjective
  haveI : IsProper s₂ := isProper_of_isProjectiveMorphism s₂ hX₂p.isProjective
  haveI : IsProper (f₁ ≫ sV) := by rw [hf₁s]; infer_instance
  haveI : IsProper (f₂ ≫ sV) := by rw [hf₂s]; infer_instance
  haveI : IsProper f₁ := IsProper.of_comp f₁ sV
  haveI : IsProper f₂ := IsProper.of_comp f₂ sV
  haveI := hf₁.isDominant
  have hX₁n : IsNormalVariety ℂ s₁ := ⟨hX₁p.toIsVariety, inferInstance⟩
  have hX₂n : IsNormalVariety ℂ s₂ := ⟨hX₂p.toIsVariety, inferInstance⟩
  obtain ⟨W, r, p', hWn, -, hcomm, hr, hrb, hp', hp'b⟩ :=
    MMP.Fourfold.exists_common_model_over sV f₁ f₂ hf₁ hf₂ (by rw [hf₁s]; exact hX₁n)
      (by rw [hf₂s]; exact hX₂n)
  rw [hf₂s] at hWn
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (p' ≫ s₂) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ s₂)
  haveI : QuasiCompact (p' ≫ s₂) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p' ≫ s₂)
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr
  haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'
  haveI := hrb.isDominant
  haveI := hp'b.isDominant
  haveI : Surjective p' :=
    surjective_of_isDominant_of_isClosed_range p' p'.isClosedMap.isClosed_range
  have hrs : r ≫ s₁ = p' ≫ s₂ := by rw [← hf₁s, ← Category.assoc, hcomm, Category.assoc, hf₂s]
  set h := hrb.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h := hrb.isInverse_inverse
  haveI := isSeparated_terminal_of s₁
  have hψ : h.compHom p' = φ :=
    compHom_eq_of_isInverse_of_isOver hf₂ hcomm hinv hφ.2
  have hφE : ∀ F : MMP.Mori.PrimeDivisor X₂, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F :=
    fun F hF => by
      obtain ⟨R, hR⟩ := exists_transformPrimeDivisor_eq_some_of_isModificationOf hX₁n hX₂n hVn
        hf₁s hf₂s hf₁ hf₂ hf₂c hφ F
      exact hF R hR
  obtain ⟨htriv₂, hpb⟩ := MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq
    s₁ s₂ sV hX₁ hX₁p hX₂ hX₂p hVp f₁ f₂ hf₁s hf₂s hφ.1 hφ.2 hφE htriv
  obtain ⟨GN, hGN, -⟩ := MMP.Flips.existsUnique_isRCartierPullback r htriv.1
  obtain ⟨GN', hGN', -⟩ := MMP.Flips.existsUnique_isRCartierPullback p' htriv₂.1
  have heq : GN = GN' := hpb W (p' ≫ s₂) r p' h hWn hrs rfl hr hrb hp' hp'b hinv hψ GN GN' hGN hGN'
  have hnefW : IsRelativelyNef ℂ (r ≫ s₁) (r ≫ f₁ ≫ g) GN :=
    MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) (f₁ ≫ g) (r ≫ f₁ ≫ g) r
      (Category.comp_id _) hnef hGN
  have hnefW' : IsRelativelyNef ℂ (p' ≫ s₂) (p' ≫ f₂ ≫ g) GN' := by
    rw [← heq]
    have e : p' ≫ f₂ ≫ g = r ≫ f₁ ≫ g := by rw [← Category.assoc, ← hcomm, Category.assoc]
    rw [e]
    exact IsRelativelyNef.of_eq_structure hrs hnefW
  exact IsRelativelyNef.of_isRCartierPullback p' rfl (f₂ ≫ g) hGN' hnefW'

end StepTransport

/-! ### Transforms through a common model -/

section TransformThroughModel

/-- **Transforms through a common model.** Let `r : W ⟶ X₁` and `q : W ⟶ X₂` be proper birational
morphisms of normal varieties, `h` an inverse of `r` and `φ = q ∘ h`. If `φ⁻¹` contracts no prime
divisor, then `φ_* r_* D = q_* D` for every divisor `D` on `W`: at a prime divisor `F` of `X₂`,
both sides are the coefficient of `D` along the strict transform of `F` in `W`. -/
private theorem transformDivisor_transformDivisor_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r] [IsProper q]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ R : MMP.Mori.PrimeDivisor X₁, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap D := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  have hW₂ : IsNormalVariety ℂ (q ≫ s₂) := hrq ▸ hW
  refine Finsupp.ext fun F => ?_
  obtain ⟨R₀, hR₀⟩ := hφE F
  obtain ⟨RW, hRW, -, hRWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R₀
  obtain ⟨FW, hFW, -, hFWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₂ hW₂ hqb F
  have := F.isDiscreteValuationRing_localRing
  -- every prime divisor of `X₁` with transform `F` has strict transform `F_W`
  have hkey : ∀ R' : MMP.Mori.PrimeDivisor X₁,
      MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F → R' = R₀ := by
    intro R' hR'
    obtain ⟨R'W, hR'W, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
    have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
      R'W hR'W F).mp hR'
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    have h3 : R'W.genericPoint = RW.genericPoint :=
      MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hR'W.symm.trans ((congrArg r h3).trans hRW))
  have hRF : RW = FW := by
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h2 hFW)
  change DivisorWithCoeffs.mapPrimeDivisors _ _ F = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR₀ hkey, hRWc, hFWc, hRF]

/-- **Canonical divisors across a modification.** Let `φ : X₁ ⤏ X₂` be a modification of
`f₁ : X₁ ⟶ V` into `f₂ : X₂ ⟶ V`, proper birational morphisms of normal complex varieties, where
`f₂` contracts no prime divisor. Then `φ_* K₁` is linearly equivalent to every canonical divisor
`K₂` of `X₂`, for every canonical divisor `K₁` of `X₁`: on a smooth common model `W`, `K₁` is the
push-forward of a canonical divisor `K_W`, and `φ_* K₁` is the push-forward of `K_W` to `X₂`. -/
private theorem linearlyEquivalent_transformDivisor_of_isCanonicalDivisor
    {X₁ X₂ V : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [CompactSpace X₁] [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂] [CompactSpace X₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) (hV : IsNormalVariety ℂ sV)
    {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hf₁s : f₁ ≫ sV = s₁) (hf₂s : f₂ ≫ sV = s₂)
    [IsProper f₁] [IsProper f₂] (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (hf₂c : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ Q : MMP.Mori.PrimeDivisor V, f₂ F.genericPoint = Q.genericPoint)
    {φ : X₁.RationalMap X₂} (hφ : IsModificationOf f₁ f₂ φ) {n m : ℕ} {K₁ : Divisor X₁}
    {K₂ : Divisor X₂} (hK₁ : K₁.IsCanonicalDivisor s₁ n) (hK₂ : K₂.IsCanonicalDivisor s₂ m) :
    Divisor.LinearlyEquivalent (MMP.Mori.RationalMap.transformDivisor φ K₁) K₂ := by
  have hφE := exists_transformPrimeDivisor_eq_some_of_isModificationOf hX₁ hX₂ hV hf₁s hf₂s hf₁
    hf₂ hf₂c hφ
  obtain ⟨W, p, q, hWv, hWsm, hp, hq, hpb, hqb, ⟨ψ, hψinv, hψ⟩, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model s₁ s₂ sV hX₁ hX₂ hV.1 f₁ f₂ hf₁s hf₂s φ hφ
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI : QuasiCompact (p ≫ s₁) := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ s₁)
  haveI : LocallyOfFiniteType (p ≫ s₁) := hWv.toLocallyOfFiniteType
  haveI := hWv
  have hpq : p ≫ s₁ = q ≫ s₂ := by
    rw [← hf₁s, ← hf₂s, ← Category.assoc, hcomm, Category.assoc]
  have hWn : IsNormalVariety ℂ (p ≫ s₁) := ⟨hWv, inferInstance⟩
  have hWn' : IsNormalVariety ℂ (q ≫ s₂) := hpq ▸ hWn
  haveI : LocallyOfFiniteType (q ≫ s₂) := hWn'.1.toLocallyOfFiniteType
  haveI := hWn'.1
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI := hX₁.1
  haveI := hX₂.1
  haveI : LocallyOfFiniteType s₁ := hX₁.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s₂ := hX₂.1.toLocallyOfFiniteType
  have hdW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₁ (p ≫ s₁) hpb).symm.trans
      hK₁.1
  have hd₂ : topologicalKrullDim X₂ = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s₂ (q ≫ s₂) hqb).trans hdW
  obtain rfl : m = n := by exact_mod_cast hK₂.1.symm.trans hd₂
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ s₁) hWsm hdW
  obtain ⟨KW, hKW, hKWe⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hX₁ hWn hpb hK₁ hK₀
  have hKW' : KW.IsCanonicalDivisor (q ≫ s₂) m := hpq ▸ hKW
  have hq' := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hX₂ hWn' hqb hK₂ hKW'
  rw [← hKWe, transformDivisor_transformDivisor_of_isInverse hX₁ hX₂ hWn hpq hpb hqb hψinv hψ hφE]
  exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor s₂ hX₂ hq' hK₂

/-- **Push-forwards through a model of a modification.** Let `φ : X₁ ⤏ X₂` be a modification of
`f₁ : X₁ ⟶ V` into `f₂ : X₂ ⟶ V`, proper birational morphisms of normal complex varieties, where
`f₂` contracts no prime divisor, and let `q₁ : W ⟶ X₁`, `q₂ : W ⟶ X₂` be proper birational with
`q₁ ≫ f₁ = q₂ ≫ f₂`. Then `q₂_* G = φ_* q₁_* G` for every divisor `G` on `W`. -/
private theorem transformDivisor_eq_transformDivisor_of_isModificationOf
    {X₁ X₂ V W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) (hV : IsNormalVariety ℂ sV)
    {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hf₁s : f₁ ≫ sV = s₁) (hf₂s : f₂ ≫ sV = s₂)
    [IsProper f₁] [IsProper f₂] (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (hf₂c : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ Q : MMP.Mori.PrimeDivisor V, f₂ F.genericPoint = Q.genericPoint)
    {φ : X₁.RationalMap X₂} (hφ : IsModificationOf f₁ f₂ φ) {q₁ : W ⟶ X₁} {q₂ : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (q₁ ≫ s₁)) [IsProper q₁] [IsProper q₂]
    (hq₁b : IsBirationalMorphism q₁) (hq₂b : IsBirationalMorphism q₂)
    (hcomm : q₁ ≫ f₁ = q₂ ≫ f₂) {R : Type} [AddCommMonoid R] (G : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor q₂.toRationalMap G =
      MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor q₁.toRationalMap G) := by
  haveI := hX₁.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := hf₁.isDominant
  have hq : q₁ ≫ s₁ = q₂ ≫ s₂ := by
    rw [← hf₁s, ← hf₂s, ← Category.assoc, hcomm, Category.assoc]
  set h := hq₁b.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse q₁.toRationalMap h := hq₁b.isInverse_inverse
  have hψ : h.compHom q₂ = φ :=
    compHom_eq_of_isInverse_of_isOver hf₂ hcomm hinv hφ.2
  have hφE := exists_transformPrimeDivisor_eq_some_of_isModificationOf hX₁ hX₂ hV hf₁s hf₂s hf₁
    hf₂ hf₂c hφ
  exact (transformDivisor_transformDivisor_of_isInverse hX₁ hX₂ hW hq hq₁b hq₂b hinv hψ hφE
    G).symm

/-- **Strict transforms through a common model are unique.** In the setting of
`transformDivisor_transformDivisor_of_isInverse`, two prime divisors of `X₁` with the same
transform `F` coincide: their strict transforms on `W` both map to the generic point of `F`. -/
private theorem eq_of_transformPrimeDivisor_eq_some_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ) {F : MMP.Mori.PrimeDivisor X₂} {R R' : MMP.Mori.PrimeDivisor X₁}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    (hR' : MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F) : R = R' := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated (q ≫ s₂) := by rw [← hrq]; infer_instance
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  obtain ⟨RW, hRW, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R
  obtain ⟨R'W, hR'W, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
  have := F.isDiscreteValuationRing_localRing
  have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R
    RW hRW F).mp hR
  have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
    R'W hR'W F).mp hR'
  have h3 : RW.genericPoint = R'W.genericPoint :=
    MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hRW.symm.trans ((congrArg r h3).trans hR'W))

/-- A rational map composed with the identity. -/
private theorem rationalMap_compHom_id {X Y : Scheme.{0}} (f : X.RationalMap Y) :
    f.compHom (𝟙 Y) = f := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]

/-- **Prime divisors over the target lie over the source.** In the setting of
`transformDivisor_eq_transformDivisor_of_isModificationOf`, a prime divisor of `W` over a prime
divisor of `X₂` lies over a prime divisor of `X₁`: the prime divisor of `X₂` is the transform of a
prime divisor of `X₁`, whose strict transform on `W` is the given one. -/
private theorem exists_primeDivisor_apply_eq_of_isModificationOf
    {X₁ X₂ V W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) (hV : IsNormalVariety ℂ sV)
    {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hf₁s : f₁ ≫ sV = s₁) (hf₂s : f₂ ≫ sV = s₂)
    [IsProper f₁] [IsProper f₂] (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (hf₂c : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ Q : MMP.Mori.PrimeDivisor V, f₂ F.genericPoint = Q.genericPoint)
    {φ : X₁.RationalMap X₂} (hφ : IsModificationOf f₁ f₂ φ) {q₁ : W ⟶ X₁} {q₂ : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (q₁ ≫ s₁)) [IsProper q₁] [IsProper q₂]
    (hq₁b : IsBirationalMorphism q₁) (hq₂b : IsBirationalMorphism q₂)
    (hcomm : q₁ ≫ f₁ = q₂ ≫ f₂) (P : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor X₂)
    (hPF : q₂ P.genericPoint = F.genericPoint) :
    ∃ R : MMP.Mori.PrimeDivisor X₁, q₁ P.genericPoint = R.genericPoint := by
  haveI := hX₁.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₂
  haveI := hf₁.isDominant
  have hq : q₁ ≫ s₁ = q₂ ≫ s₂ := by
    rw [← hf₁s, ← hf₂s, ← Category.assoc, hcomm, Category.assoc]
  set h := hq₁b.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse q₁.toRationalMap h := hq₁b.isInverse_inverse
  have hψ : h.compHom q₂ = φ :=
    compHom_eq_of_isInverse_of_isOver hf₂ hcomm hinv hφ.2
  obtain ⟨R, hR⟩ := exists_transformPrimeDivisor_eq_some_of_isModificationOf hX₁ hX₂ hV hf₁s hf₂s
    hf₁ hf₂ hf₂c hφ F
  obtain ⟨RW, hRW, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hq₁b R
  have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse q₁ hq₁b hinv q₂ hψ R RW
    hRW F).mp hR
  have := F.isDiscreteValuationRing_localRing
  haveI : IsSeparated (q₂ ≫ s₂) := by rw [← hq]; exact hW.1.toIsSeparated
  haveI : IsSeparated q₂ := IsSeparated.of_comp q₂ s₂
  haveI := hq₂b.isDominant
  have h2 : RW.genericPoint = P.genericPoint :=
    MMP.Fourfold.eq_of_map_eq_of_valuationRing hq₂b.functionFieldMap_bijective h1 hPF
  exact ⟨R, by rw [← h2]; exact hRW⟩

/-- The birational transform of divisors commutes with regarding a divisor as an
`ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℤ),
      Divisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Int.castAddHom ℝ))
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · simp
    · simp [hs]

/-- The birational transform of `ℝ`-divisors is `ℝ`-linear. -/
private theorem transformDivisor_smul {X Y : Scheme.{0}} (φ : X.RationalMap Y) (c : ℝ)
    (D : RDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (c • D) =
      c • MMP.Mori.RationalMap.transformDivisor φ D := by
  exact (MMP.Mori.RationalMap.transformDivisorₗ ℝ φ).map_smul c D

/-- The transform of `K + D` is `φ_* K + φ_* D`. -/
private theorem transformDivisor_logCanonicalDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (K : Divisor X) (D : RDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (logCanonicalDivisor K D) =
      logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ D) := by
  rw [logCanonicalDivisor, map_add, transformDivisor_toRDivisor, logCanonicalDivisor]

end TransformThroughModel

/-! ### The negativity step -/

section NegativityStep

/-- Linearly equivalent divisors differ by a divisor linearly equivalent to zero. -/
private theorem linearlyEquivalent_sub_zero {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D D' : Divisor X} (h : D.LinearlyEquivalent D') :
    (D - D').LinearlyEquivalent 0 := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [sub_zero]; exact hu⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is an `ℝ`-linear combination of Cartier
divisors. -/
private theorem isCartierCombination_of_isQFactorial {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD⟩ := MMP.Fourfold.IsQFactorial.isRCartier hX D
  refine ⟨m, r, L, hL, Finsupp.ext fun P => ?_⟩
  rw [Finset.sum_apply']
  refine (hD P).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp [DivisorWithCoeffs.mapCoeffs, DivisorWithCoeffs.coeff]

/-- The negative of a divisor whose negative is `f`-ample is `f`-nef. -/
private theorem isRelativelyNef_neg_of_isRelativelyAntiAmple {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (f : X ⟶ W) {L : RDivisor X} (hL : IsRelativelyAntiAmple f L)
    (hLc : IsCartierCombination L) : IsRelativelyNef k sX f (-L) := by
  obtain ⟨m, r, Ls, hLs, hLeq⟩ := hLc
  have hLeq' : L = ∑ j, r j • Divisor.toRDivisor (Ls j) := hLeq
  have hneg : -L = ∑ j, (-r) j • Divisor.toRDivisor (Ls j) := by
    rw [hLeq']
    simp [neg_smul, Finset.sum_neg_distrib]
  refine ⟨m, -r, Ls, hLs, hneg, fun C hC x hx => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r Ls hLs
  rw [← hLeq'] at e
  have hlt := isRIntersectionNumber_neg_of_isRelativelyAntiAmple f hL C hC r Ls _ e
  have e' := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (-r) Ls hLs
  rw [← hneg] at e'
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx e']
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  linarith

/-- **`f_* f^* D = D`** for the `ℝ`-Cartier pull-back along a proper birational morphism of
normal varieties. -/
private theorem transformDivisor_of_isRCartierPullback {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {D : RDivisor Y} {G : RDivisor X} (hG : IsRCartierPullback f D G) :
    MMP.Mori.RationalMap.transformDivisor f.toRationalMap G = D := by
  obtain ⟨m, r, L, L', hL, hD, hpb, rfl⟩ := hG
  rw [hD, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hp⟩ := hpb j
  rw [transformDivisor_smul, transformDivisor_toRDivisor,
    MMP.Positivity.transformDivisor_of_isPullback_divisor hY hX hf (hL j) hp]

/-- **The negativity step.** Let `q₁ : W ⟶ X₁` and `q₂ : W ⟶ X₂` with `q₁ ≫ f₁ = q₂ ≫ f₂`, where
`q₂` is projective birational, and let `G_i = q_i^* D_i`. If `-D₁` is `f₁`-nef, `D₂` is
`f₂`-nef and `q₂_* G₁ = D₂`, then `G₁ - G₂` is effective: `-(G₁ - G₂)` is `q₂`-nef and
`q₂_*(G₁ - G₂) = 0`, so the negativity lemma applies. -/
private theorem nonneg_sub_of_isRCartierPullback_of_isRelativelyNef
    {X₁ X₂ V W : Scheme.{0}} [IsLocallyNoetherian X₁] [IsNormal X₁] [IsLocallyNoetherian X₂]
    [IsNormal X₂] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)} [IsSeparated s₁] [LocallyOfFiniteType s₁]
    [QuasiCompact s₁] [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    (hX₂ : IsNormalVariety ℂ s₂) {sW : W ⟶ Spec (.of ℂ)} [QuasiCompact sW]
    (hW : IsNormalVariety ℂ sW)
    {q₁ : W ⟶ X₁} {q₂ : W ⟶ X₂} [IsProper q₁] [IsProper q₂] (hq₁ : q₁ ≫ s₁ = sW)
    (hq₂ : q₂ ≫ s₂ = sW) (hq₂p : IsProjectiveMorphism q₂) (hq₂b : IsBirationalMorphism q₂)
    {f₁ : X₁ ⟶ V} {f₂ : X₂ ⟶ V} (hcomm : q₁ ≫ f₁ = q₂ ≫ f₂)
    {D₁ : RDivisor X₁} {D₂ : RDivisor X₂} {G₁ G₂ : RDivisor W}
    (hG₁ : IsRCartierPullback q₁ D₁ G₁) (hG₂ : IsRCartierPullback q₂ D₂ G₂)
    (hnef₁ : IsRelativelyNef ℂ s₁ f₁ (-D₁)) (hnef₂ : IsRelativelyNef ℂ s₂ f₂ D₂)
    (hpush : MMP.Mori.RationalMap.transformDivisor q₂.toRationalMap G₁ = D₂) :
    ∀ P, 0 ≤ (G₁ - G₂).coeff P := by
  haveI : QuasiCompact (q₁ ≫ s₁) := by rw [hq₁]; infer_instance
  haveI : QuasiCompact (q₂ ≫ s₂) := by rw [hq₂]; infer_instance
  have hWn : IsNormalVariety ℂ (q₂ ≫ s₂) := hq₂ ▸ hW
  -- `-G₁ = q₁^*(-D₁)` is nef over `q₂`
  have hG₁' : IsRCartierPullback q₁ (-D₁) (-G₁) := by
    have := MMP.Fourfold.isRCartierPullback_smul (-1) hG₁
    simpa only [neg_one_smul] using this
  have hn₁ : IsRelativelyNef ℂ sW q₂ (-G₁) := by
    have := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback f₂ f₁ q₂ q₁ hcomm.symm hnef₁ hG₁'
    exact IsRelativelyNef.of_eq_structure hq₁ this
  have hn₂ : IsRelativelyNef ℂ sW q₂ G₂ := by
    have := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback f₂ f₂ q₂ q₂ rfl hnef₂ hG₂
    exact IsRelativelyNef.of_eq_structure hq₂ this
  have hc : IsCartierCombination (G₁ - G₂) :=
    MMP.Flips.isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hG₁)
      (isCartierCombination_of_isRCartierPullback hG₂)
  have hneg : IsRelativelyNef ℂ sW q₂ (-(G₁ - G₂)) := by
    rw [neg_sub, sub_eq_add_neg]
    exact IsRelativelyNef.add hn₂ hn₁
  have hpush' : (MMP.Mori.RationalMap.transformDivisor q₂.toRationalMap (G₁ - G₂)).IsEffective := by
    rw [map_sub, hpush, transformDivisor_of_isRCartierPullback hX₂ hWn hq₂b hG₂, sub_self]
    exact fun P => le_rfl
  have := MMP.Flips.isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ s₂ sW hX₂
    hW q₂ hq₂ hq₂p hq₂b hc hneg hpush'
  exact this

/-- An `f`-ample divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (f : X ⟶ W) {L : RDivisor X} (hL : IsRelativelyAmple f L) :
    IsRelativelyNef k sX f L := by
  obtain ⟨m, a, A, -, ha, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  refine ⟨m, a, A, hAc, hLeq, fun C hC x hx => ?_⟩
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C a A hAc
  rw [← hLeq] at hy
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hy]
  refine Finset.sum_nonneg fun j _ => mul_nonneg (ha j).le ?_
  exact_mod_cast (degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) C hC).le

/-- Intersection numbers do not see a divisor linearly equivalent to zero. -/
private theorem isRIntersectionNumber_eq_of_linearlyEquivalent_zero {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (C : ProperCurve sX) {D : RDivisor X} {L₀ : Divisor X}
    (h : L₀.LinearlyEquivalent 0) {m m' : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X} {x y : ℝ}
    (hx : IsRIntersectionNumber k sX D r L C x)
    (hy : IsRIntersectionNumber k sX (D + Divisor.toRDivisor L₀) r' L' C y) : y = x := by
  have hc : L₀.IsCartier := Divisor.IsCartier.of_linearlyEquivalent h Divisor.isCartier_zero
  have hz := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => L₀) (fun _ => hc)
  have e : Divisor.toRDivisor L₀ = ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ := by simp
  rw [← e] at hz
  have hz' := hz
  have hz0 := MMP.Flips.eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent h C hz'
  simp only [one_mul] at hz0
  have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 1 1 hx hz'
  simp only [one_smul, one_mul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hy hsum, hz0, add_zero]

/-- A real multiple of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_smul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (hD : IsCartierCombination D) (c : ℝ) : IsCartierCombination (c • D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  refine ⟨m, c • r, L, hL, ?_⟩
  rw [Finset.smul_sum]
  simp only [Pi.smul_apply, smul_smul, smul_eq_mul]

/-- Every intersection number of the zero divisor vanishes. -/
private theorem eq_zero_of_isRIntersectionNumber_zero {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX 0 r L C x) : x = 0 := by
  have h0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 0 => (0 : ℝ))
    (fun _ => 0) (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h0

/-- A real multiple of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_smul {k : Type} [Field k] {X W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ W} {N : RDivisor X}
    (hN : MMP.Flips.IsNumericallyTrivialOver k sX f N) (t : ℝ) :
    MMP.Flips.IsNumericallyTrivialOver k sX f (t • N) := by
  refine ⟨isCartierCombination_smul hN.1 t, hN.2.1,
    fun Γ hΓ _ _ _ x₁ _ _ _ x₂ hx₁ hx₂ => ?_⟩
  obtain ⟨_, _, _, y, hy⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hN.1 Γ
  obtain ⟨_, _, _, z, hz⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hN.2.1 Γ
  have hy0 : y = z := hN.2.2 Γ hΓ _ _ _ _ _ _ _ _ hy hz
  have hz0 := eq_zero_of_isRIntersectionNumber_zero Γ hz
  have hsm := (IsRIntersectionNumber.eq_and_linear k sX Γ).2 _ _ _ _ _ _ _ _ t 0 hy hz
  simp only [zero_smul, add_zero] at hsm
  rw [(IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hx₁ hsm,
    eq_zero_of_isRIntersectionNumber_zero Γ hx₂, hy0, hz0]
  ring

/-- The negative of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_neg {k : Type} [Field k] {X W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ W} {N : RDivisor X}
    (hN : MMP.Flips.IsNumericallyTrivialOver k sX f N) :
    MMP.Flips.IsNumericallyTrivialOver k sX f (-N) := by
  simpa using isNumericallyTrivialOver_smul hN (-1)

/-- **Nefness between a nef divisor and a numerically trivial one.** If `A` is `f`-nef and
`A + λ D ≡_f 0` with `λ > 0`, then `A + t D` is `f`-nef for every `0 ≤ t ≤ λ`. -/
private theorem isRelativelyNef_add_smul_of_isNumericallyTrivialOver {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ W} {A D : RDivisor X}
    (hA : IsRelativelyNef k sX f A) (hD : IsCartierCombination D) {lam t : ℝ} (hlam : 0 < lam)
    (ht0 : 0 ≤ t) (htl : t ≤ lam)
    (hN : MMP.Flips.IsNumericallyTrivialOver k sX f (A + lam • D)) :
    IsRelativelyNef k sX f (A + t • D) := by
  have hAc : IsCartierCombination A := by
    obtain ⟨m, r, L, hL, hAeq, -⟩ := hA
    exact ⟨m, r, L, hL, hAeq⟩
  obtain ⟨m, r, L, hL, hpres⟩ :=
    MMP.Flips.isCartierCombination_add hAc (isCartierCombination_smul hD t)
  refine ⟨m, r, L, hL, hpres, fun Γ hΓ x hx => ?_⟩
  obtain ⟨_, _, _, a, ha⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hAc Γ
  obtain ⟨_, _, _, c, hc⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hD Γ
  have ha0 : 0 ≤ a := IsRelativelyNef.nonneg hA hΓ ha
  have hsum := (IsRIntersectionNumber.eq_and_linear k sX Γ).2 _ _ _ _ _ _ _ _ 1 t ha hc
  have hsuml := (IsRIntersectionNumber.eq_and_linear k sX Γ).2 _ _ _ _ _ _ _ _ 1 lam ha hc
  rw [one_smul] at hsum hsuml
  obtain ⟨_, _, _, z, hz⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hN.2.1 Γ
  have h0 : 1 * a + lam * c = z := hN.2.2 Γ hΓ _ _ _ _ _ _ _ _ hsuml hz
  rw [eq_zero_of_isRIntersectionNumber_zero Γ hz] at h0
  rw [(IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hx hsum]
  have hc0 : c ≤ 0 := by nlinarith
  nlinarith [mul_le_mul_of_nonpos_right htl hc0]

/-- A numerically trivial divisor is nef. -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ W} {N : RDivisor X}
    (hN : MMP.Flips.IsNumericallyTrivialOver k sX f N) : IsRelativelyNef k sX f N := by
  obtain ⟨m, r, L, hL, hpres⟩ := hN.1
  refine ⟨m, r, L, hL, hpres, fun Γ hΓ x hx => ?_⟩
  obtain ⟨_, _, _, z, hz⟩ := MMP.Flips.exists_isRIntersectionNumber (k := k) hN.2.1 Γ
  rw [hN.2.2 Γ hΓ _ _ _ _ _ _ _ _ hx hz, eq_zero_of_isRIntersectionNumber_zero Γ hz]

end NegativityStep

/-! ### Log minimal models extracting no divisor -/

section LogMinimal

/-- A rational map `φ⁻¹` contracts no prime divisor of the target exactly when every prime divisor
of the target is the transform of a prime divisor of the source. -/
private theorem exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (F : MMP.Mori.PrimeDivisor Y) :
    ∃ R : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F := by
  by_contra h
  push Not at h
  exact hφE F h

/-- **A log minimal model extracting no divisor is a nef weak model.** Let `φ : X ⤏ Y` be a log
minimal model of `(X/Z, Δ)` with `X` projective and `ℚ`-factorial, such that `φ⁻¹` contracts no
prime divisor. Then the canonical divisor and boundary of the model are the transforms `φ_* K` and
`φ_* Δ`, and `φ` is a nef weak model of `(X, Δ)` over `Z`. -/
private theorem IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sY]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ : RDivisor X} {KY : Divisor Y}
    {ΔY : RDivisor Y} {φ : X.RationalMap Y}
    (h : IsRealLogMinimalModel sX sY sZ π πY K Δ KY ΔY φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) :
    KY = MMP.Mori.RationalMap.transformDivisor φ K ∧
      ΔY = MMP.Mori.RationalMap.transformDivisor φ Δ ∧
      IsNefWeakModel sX sY sZ π πY K Δ φ := by
  have hXn : IsNormalVariety ℂ sX := h.isRealLcPair.1
  have hYn : IsNormalVariety ℂ sY := h.isNormalVariety_model
  have hΔ : ΔY = MMP.Mori.RationalMap.transformDivisor φ Δ := by
    refine Finsupp.ext fun F => ?_
    have := h.coeff_boundary F
    rw [if_neg (hφE F), add_zero] at this
    exact this
  obtain ⟨W, iW, lW, nW, sW, p, q, hh, GX, GY, hR⟩ := h.exists_resolution
  have hK : KY = MMP.Mori.RationalMap.transformDivisor φ K := by
    obtain ⟨n, KW, -, hp, hq⟩ := hR.exists_canonicalDivisor
    haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
    haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
    have hWn : IsNormalVariety ℂ (p ≫ sX) := by
      rw [hR.comp_eq_left]; exact ⟨hR.isVariety, inferInstance⟩
    rw [← hp, transformDivisor_transformDivisor_of_isInverse hXn hYn hWn
      (hR.comp_eq_left.trans hR.comp_eq_right.symm) hR.isBirationalMorphism_left
      hR.isBirationalMorphism_right hR.isInverse hR.compHom_eq
      (exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional hφE), hq]
  refine ⟨hK, hΔ, ?_⟩
  exact
    { isNormalVariety_source := hXn
      isProjectiveVariety_source := hX
      comp_eq_source := h.comp_eq
      isCanonicalDivisor := h.isCanonicalDivisor
      isCartierCombination := isCartierCombination_of_isQFactorial hXq _
      isNormalVariety_target := hYn
      isProjectiveVariety_target := h.isProjectiveVariety_model
      comp_eq_target := h.comp_eq_model
      isBirational := h.isBirational
      isOver := h.isOver
      not_isInverseExceptional := hφE
      isRelativelyNef := by rw [← hK, ← hΔ]; exact h.isRelativelyNef
      exists_resolution := ⟨W, iW, lW, nW, sW, p, q, hh, hR.isVariety, hR.isSmoothScheme,
        hR.comp_eq_left, hR.comp_eq_right, hR.isProjectiveMorphism_left,
        hR.isProjectiveMorphism_right, hR.isBirationalMorphism_left,
        hR.isBirationalMorphism_right, hR.isInverse, hR.compHom_eq, GX, GY,
        hR.isRCartierPullback_left, by rw [← hK, ← hΔ]; exact hR.isRCartierPullback_right,
        hR.effective, hR.isExceptional⟩ }

end LogMinimal

/-! ### Klt pairs on nef weak models -/

section KltTransfer

/-- **Pull-backs along a composite.** If `G = f^*D` and `G'` is the pull-back of `D` along
`r ≫ f`, then `G'` is the pull-back of `G` along `r`. -/
private theorem isRCartierPullback_of_isRCartierPullback_comp {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {f : Y ⟶ X} {r : W ⟶ Y} [IsDominant r] [IsDominant (r ≫ f)] {D : RDivisor X}
    {G' : RDivisor W} {G₀ : RDivisor Y} (hG : MMP.Flips.IsRCartierPullback f D G₀)
    (hG' : MMP.Flips.IsRCartierPullback (r ≫ f) D G') :
    MMP.Flips.IsRCartierPullback r G₀ G' := by
  obtain ⟨m, c, L, L', hL, hD, hpb, rfl⟩ := hG
  choose hB hp using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hp j).isCartier (hL j)
  let L'' : Fin m → Divisor W := fun j => (L' j).pullback (hL'c j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j))
  have hp'' : ∀ j, (L' j).IsPullback r
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j)) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  have hcomp : MMP.Flips.IsRCartierPullback (r ≫ f) D (∑ j, c j • Divisor.toRDivisor (L'' j)) :=
    ⟨m, c, L, L'', hL, hD, fun j =>
      ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (r ≫ f) (L j),
        MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hp j) (hp'' j) _⟩, rfl⟩
  rw [MMP.Flips.IsRCartierPullback.eq (r ≫ f) hG' hcomp]
  exact ⟨m, c, L', L'', hL'c, rfl, fun j => ⟨_, hp'' j⟩, rfl⟩

/-- The push-forward along a composite of proper birational morphisms is the composite of the
push-forwards. -/
private theorem transformDivisor_comp_of_isBirationalMorphism {X W V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {p : W ⟶ X} {r : V ⟶ W}
    (hW : IsNormalVariety ℂ (p ≫ sX)) (hV : IsNormalVariety ℂ (r ≫ p ≫ sX)) [IsProper p]
    [IsProper r] (hpb : IsBirationalMorphism p) (hrb : IsBirationalMorphism r)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R V) :
    MMP.Mori.RationalMap.transformDivisor p.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor (r ≫ p).toRationalMap D := by
  haveI := hX.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := hW.1.toIsSeparated
  haveI := isSeparated_terminal_of (p ≫ sX)
  haveI : IsProper (r ≫ p) := inferInstance
  have hrpb : IsBirationalMorphism (r ≫ p) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hrb hpb
  set h := hrb.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h := hrb.isInverse_inverse
  have hψ : h.compHom (r ≫ p) = p.toRationalMap := by
    rw [← MMP.Fourfold.Oai4C1.Main.compHom_compHom, MMP.Fourfold.Crepant.compHom_eq_of_isInverse
        hinv,
      toRationalMap_compHom, Category.id_comp]
  have hE : ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ P : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P =
        some F := by
    intro F
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hW hpb F
    exact ⟨P, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P F).mpr hP⟩
  have hV' : IsNormalVariety ℂ (r ≫ p ≫ sX) := hV
  exact transformDivisor_transformDivisor_of_isInverse hW hX (by rwa [← Category.assoc] at hV' ⊢)
    (by rw [Category.assoc]) hrb hrpb hinv hψ hE D

/-- **The log discrepancy of a prime divisor of a model.** If `K_M = div(ω)` and `K_W = div(f^*ω)`
on a model `f : W ⟶ M`, the log discrepancy of a prime divisor `E` of `W` with respect to
`(M, Δ)` is `1 + coeff_E K_W - coeff_E f^*(K_M + Δ)`. -/
private theorem isLogDiscrepancy_of_isRCartierPullback {M W : Scheme.{0}} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM]
    {KM : Divisor M} {ΔM : RDivisor M} {f : W ⟶ M} [IsProper f] [IsDominant f] {G : RDivisor W}
    {e : ℕ} (hMn : IsNormalVariety ℂ sM) (hKM : KM.IsCanonicalDivisor sM e)
    (hWnf : IsNormalVariety ℂ (f ≫ sM)) (hfb : IsBirationalMorphism f) {KW : Divisor W}
    (ω : MMP.Mori.RationalPluriForms sM e 1) (hω0 : ω ≠ 0) (hωK : MMP.Mori.divisorOfForm ω = KM)
    (hωW : MMP.Mori.divisorOfForm (MMP.Mori.pullbackRationalPluriForms sM f ω) = KW)
    (hG : MMP.Flips.IsRCartierPullback f (logCanonicalDivisor KM ΔM) G)
    (E' : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sM e ΔM ⟨W, f, hWnf, hfb, E'⟩
      (1 + (KW.coeff E' : ℝ) - G.coeff E') := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hMn, inferInstanceAs (IsProper f), ω, hω0, ⟨KM, hKM, fun Γ => by
    rw [← hωK]; exact MMP.Mori.coeff_divisorOfForm ω Γ⟩, m, r, L, L', hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor M => D.coeff Γ) hD
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, ← hωK, MMP.Mori.coeff_divisorOfForm]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hωW, MMP.Mori.coeff_divisorOfForm]
    rfl

/-- **A nef weak model of a klt pair is klt.** Let `φ : X ⤏ Y` be a nef weak model over `Z` of
the klt pair `(X, Δ)`, with `Y` `ℚ`-factorial. Then `(Y, φ_* Δ)` is klt: a divisor `E` over `Y`
is realized on a common smooth model `V` of its own model and of the resolution `W` of `φ`, and
with compatible canonical divisors `K_V` there,
`a(E; Y, φ_* Δ) - a(E; X, Δ) = coeff_E (p^*(K_X + Δ) - q^*(K_Y + φ_* Δ)) ≥ 0`. -/
private theorem isRealKltPair_transformDivisor_of_isNefWeakModel
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sY] [IsSeparated sZ]
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ : RDivisor X} {φ : X.RationalMap Y}
    (N : IsNefWeakModel sX sY sZ π πY K Δ φ) (hYq : IsQFactorial sY)
    {KY : Divisor Y} {m : ℕ} (hKY : KY.IsCanonicalDivisor sY m) (hklt : IsRealKltPair sX Δ) :
    IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ Δ) := by
  classical
  have hXn : IsNormalVariety ℂ sX := N.isNormalVariety_source
  have hYn : IsNormalVariety ℂ sY := N.isNormalVariety_target
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := isSeparated_terminal_of sY
  haveI := hYn.1
  obtain ⟨W, iW, lW, nW, sW, p, q, h, hWv, hWsm, hp, hq, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, heff, -⟩ := N.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWnp : IsNormalVariety ℂ (p ≫ sX) := by rw [hp]; exact ⟨hWv, inferInstance⟩
  have hWnq : IsNormalVariety ℂ (q ≫ sY) := by rw [hq]; exact ⟨hWv, inferInstance⟩
  have hφE := exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    N.not_isInverseExceptional
  refine ⟨hYn, fun F => ?_, ⟨m, KY, hKY, MMP.Fourfold.IsQFactorial.isRCartier hYq _⟩,
    fun e E a ha => ?_⟩
  · -- coefficients below one
    obtain ⟨R, hR⟩ := hφE F
    have hc : (MMP.Mori.RationalMap.transformDivisor φ Δ).coeff F = Δ.coeff R :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR (fun R' hR' =>
        eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hR' hR) Δ
    rw [hc]
    exact hklt.2.1 R
  · -- log discrepancies
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI : IsProper E.f := ha.2.1
    obtain ⟨V, r, p', hVn, hVsm, hcomm, hrp, hrb, hp'p, hp'b⟩ :=
      MMP.Fourfold.exists_common_model_over sY E.f q E.isBirationalMorphism hqb E.isNormalVariety
        hWnq
    haveI := hVn.1.toIsIntegral
    haveI := hVn.2
    haveI : LocallyOfFiniteType (p' ≫ q ≫ sY) := hVn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ q ≫ sY)
    haveI : QuasiCompact (p' ≫ q ≫ sY) := hVn.1.toQuasiCompact
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p' ≫ q ≫ sY)
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hrp
    haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'p
    haveI := hp'b.isDominant
    haveI := hrb.isDominant
    set α : V ⟶ X := p' ≫ p with hαdef
    set β : V ⟶ Y := p' ≫ q with hβdef
    have hαb : IsBirationalMorphism α := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hpb
    have hβb : IsBirationalMorphism β := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hqb
    haveI := hαb.isDominant
    haveI := hβb.isDominant
    have hαs : α ≫ sX = p' ≫ q ≫ sY := by
      simp only [hαdef, Category.assoc, hp, hq]
    have hVα : IsNormalVariety ℂ (α ≫ sX) := by rw [hαs]; exact hVn
    have hVβ : IsNormalVariety ℂ (β ≫ sY) := by rw [hβdef, Category.assoc]; exact hVn
    haveI : LocallyOfFiniteType (α ≫ sX) := hVα.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (β ≫ sY) := hVβ.1.toLocallyOfFiniteType
    -- the strict transform of `E` on `V`
    obtain ⟨E'', hE''⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq E β hVβ
      hβb r hrb (by rw [hcomm])
    -- compatible canonical divisors on `V`
    obtain ⟨n₀, hK⟩ := N.isCanonicalDivisor
    haveI := hXn.1
    haveI : MMP.Mori.IsVariety ℂ (α ≫ sX) := hVα.1
    have hdV : topologicalKrullDim V = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (α ≫ sX) hαb).symm.trans
        hK.1
    have hsmα : IsSmoothScheme (α ≫ sX) := by rw [hαs]; exact hVsm
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (α ≫ sX) hsmα hdV
    obtain ⟨KV, hKV, hKVα⟩ :=
      MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hVα hαb hK hK₀
    -- `β_* K_V = φ_* K`
    have hp'n : IsNormalVariety ℂ (p' ≫ p ≫ sX) := by rw [← Category.assoc]; exact hVα
    have hp'q : IsNormalVariety ℂ (p' ≫ q ≫ sY) := hVn
    have hKVβ : MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV =
        MMP.Mori.RationalMap.transformDivisor φ K := by
      rw [← transformDivisor_comp_of_isBirationalMorphism hYn hWnq hp'q hqb hp'b,
        ← transformDivisor_transformDivisor_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hφE, transformDivisor_comp_of_isBirationalMorphism hXn hWnp hp'n hpb hp'b]
      change MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor α.toRationalMap KV) = _
      rw [hKVα]
    -- canonical forms
    obtain ⟨ω, hω0, hωK, hωV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn
      hVα hαb hK hKV hKVα
    haveI : MMP.Mori.IsVariety ℂ (β ≫ sY) := hVβ.1
    have hdY : topologicalKrullDim Y = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (β ≫ sY) hβb).trans hdV
    obtain rfl : m = n₀ := by exact_mod_cast hKY.1.symm.trans hdY
    have hKV' : KV.IsCanonicalDivisor (β ≫ sY) m := by
      have e : β ≫ sY = α ≫ sX := by rw [hαs, hβdef, Category.assoc]
      rw [e]; exact hKV
    have hKYc := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn hVβ hβb hKY hKV'
    obtain ⟨ωY, hωY0, hωYK, hωYV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq
      hYn hVβ hβb hKYc hKV' rfl
    -- pull-backs of the adjoints to `V`
    obtain ⟨Gα, hGα, -⟩ := MMP.Flips.existsUnique_isRCartierPullback α N.isCartierCombination
    have hGZc : IsCartierCombination (logCanonicalDivisor
        (MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV)
        (MMP.Mori.RationalMap.transformDivisor φ Δ)) :=
      isCartierCombination_of_isQFactorial hYq _
    obtain ⟨Gβ, hGβ, -⟩ := MMP.Flips.existsUnique_isRCartierPullback β hGZc
    have hGα' : MMP.Flips.IsRCartierPullback p' GY Gα :=
      isRCartierPullback_of_isRCartierPullback_comp hGY hGα
    have hGβ' : MMP.Flips.IsRCartierPullback p' GZ Gβ :=
      isRCartierPullback_of_isRCartierPullback_comp (by rw [hKVβ]; exact hGZ) hGβ
    have hWq : IsQFactorial sW :=
      ⟨⟨hWv, inferInstance⟩, fun D => ⟨1, one_pos, by
        simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D⟩⟩
    have hdiff : MMP.Flips.IsRCartierPullback p' (GY - GZ) (Gα - Gβ) := by
      have h1 := MMP.Fourfold.isRCartierPullback_smul (-1) hGβ'
      simp only [neg_one_smul] at h1
      have := MMP.Fourfold.isRCartierPullback_add hGα' h1
      simpa only [← sub_eq_add_neg] using this
    have hpos : 0 ≤ Gα - Gβ := (MMP.Fourfold.isEffective_of_isRCartierPullback p'
      (MMP.Fourfold.IsQFactorial.isRCartier hWq _) (fun P => heff P)).2 _ hdiff
    -- the two log discrepancies
    have hDY := isLogDiscrepancy_of_isRCartierPullback hYn hKYc hVβ hβb ωY hωY0 hωYK hωYV hGβ E''
    have hDX := isLogDiscrepancy_of_isRCartierPullback hXn hK hVα hαb ω hω0 hωK hωV hGα E''
    have ha' := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hDY hE''.symm
    have hX0 := hklt.2.2.2 _ _ _ hDX
    have hE : 0 ≤ (Gα - Gβ).coeff E'' := hpos E''
    rw [DivisorWithCoeffs.coeff_sub] at hE
    rw [ha']
    linarith

end KltTransfer

/-! ### Composites of the steps of a program -/

section Composite

variable {X : Scheme.{0}} {Y : ℕ → Scheme.{0}}

/-- Partial isomorphisms `X ⤏ X_i` representing the composites of chosen representatives `b i` of
the steps `X_i ⤏ X_{i+1}`. -/
private noncomputable def compositePartialIso (b : ∀ i, (modelSeq X Y i).PartialIso (Y i)) :
    ∀ i, X.PartialIso (modelSeq X Y i)
  | 0 => Scheme.PartialIso.refl X
  | i + 1 => (compositePartialIso b i).trans (b i)

/-- **Composites of birational steps.** If every step `φ_i : X_i ⤏ X_{i+1}` is birational, there
are composites `ψ_i : X ⤏ X_i` with `ψ_0 = id` and `ψ_{i+1} = φ_i ∘ ψ_i`, computed on representing
partial isomorphisms. -/
private theorem exists_composites (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i))
    (hφ : ∀ i, MMP.Mori.RationalMap.IsBirational (φ i)) :
    ∃ ψ : ∀ i, X.RationalMap (modelSeq X Y i), ψ 0 = Scheme.RationalMap.id X ∧
      ∀ i, ∃ (a : X.PartialIso (modelSeq X Y i)) (b : (modelSeq X Y i).PartialIso (Y i)),
        a.toRationalMap = ψ i ∧ b.toRationalMap = φ i ∧ (a.trans b).toRationalMap = ψ (i + 1) := by
  choose b hb using hφ
  refine ⟨fun i => (compositePartialIso b i).toRationalMap, ?_, fun i =>
    ⟨compositePartialIso b i, b i, rfl, hb i, rfl⟩⟩
  rfl

/-- A partial isomorphism over `S` has rational map over `S`. -/
private theorem isOver_toRationalMap_of_isOver {X Y S : Scheme.{0}} {sX : X ⟶ S} {sY : Y ⟶ S}
    {e : X.PartialIso Y} (he : e.IsOver sX sY) :
    MMP.Flips.RationalMap.IsOver sX sY e.toRationalMap := by
  change (e.toPartialMap.compHom sY).toRationalMap = sX.toRationalMap
  rw [Scheme.Hom.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom, Scheme.Hom.toPartialMap,
    Scheme.PartialIso.toPartialMap]
  change (X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ sY) = X.homOfLE le_top ≫ X.topIso.hom ≫ sX
  rw [Category.assoc, he, Scheme.homOfLE_rfl, Category.id_comp, Scheme.topIso_hom,
    Scheme.homOfLE_ι_assoc]

/-- A representative of a rational map over a separated `S` is a partial isomorphism over `S`. -/
private theorem isOver_of_isOver_toRationalMap {X Y S : Scheme.{0}} [IsReduced X]
    [IsSeparated (S ↘ ⊤_ Scheme)] {sX : X ⟶ S} {sY : Y ⟶ S} {e : X.PartialIso Y}
    (he : MMP.Flips.RationalMap.IsOver sX sY e.toRationalMap) : e.IsOver sX sY := by
  have h1 : (e.toPartialMap.compHom sY).equiv sX.toPartialMap :=
    Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp h1
  change (e.iso.hom ≫ e.target.ι) ≫ sY = e.source.ι ≫ sX at h2
  rw [Category.assoc] at h2
  exact h2

end Composite

/-! ### Uniqueness of ample log minimal models -/

section AmpleModel

/-- A divisor which is `f`-ample has positive intersection number, computed with any
presentation, on every proper curve contracted by `f`. -/
private theorem isRIntersectionNumber_pos_of_isRelativelyAmple {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (f : X ⟶ W) {L : RDivisor X} (hL : IsRelativelyAmple f L)
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f) {m : ℕ} (r : Fin m → ℝ)
    (Ls : Fin m → Divisor X) (x : ℝ) (hx : IsRIntersectionNumber k sX L r Ls Γ x) : 0 < x := by
  obtain ⟨m', a, A, hm, ha, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX Γ a A hAc
  rw [← hLeq] at hy
  rw [(IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hx hy]
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j => by
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) Γ hΓ
  exact Finset.sum_pos (fun j _ => mul_pos (ha j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

/-- The base morphism of a nef weak model over a birational base is birational. -/
private theorem IsNefWeakModel.isBirationalMorphism_base {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [QuasiCompact sY] [IsSeparated sZ] {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X}
    {Δ : RDivisor X} {φ : X.RationalMap Y} (N : IsNefWeakModel sX sY sZ π πY K Δ φ)
    (hπb : IsBirationalMorphism π) : IsBirationalMorphism πY := by
  obtain ⟨W, iW, lW, nW, sW, p, q, h, hWv, -, hp, hq, -, -, hpb, hqb, hinv, hcomp, -⟩ :=
    N.exists_resolution
  haveI := hpb.isDominant
  haveI := isSeparated_terminal_of sZ
  have e := MMP.Fourfold.comp_eq_comp_of_isOver π πY N.isOver p q h hinv hcomp
  haveI : LocallyOfFiniteType sY := N.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (πY ≫ sZ) := by rw [N.comp_eq_target]; infer_instance
  haveI : LocallyOfFiniteType πY := LocallyOfFiniteType.of_comp (f := πY) (g := sZ) inferInstance
  exact MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left q πY hqb
    (e ▸ MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hpb hπb)

/-- **Two log minimal models of one pair, one with ample adjoint, are isomorphic over the base.**
Let `φ₁ : X ⤏ Y₁` and `φ₂ : X ⤏ Y₂` be log minimal models of `(X/Z, Δ)` extracting no divisor,
over a birational base, with `K_{Y₂} + Δ₂` ample over `Z`. On a common model `W` the pulled-back
adjoints agree, so `Y₁ ⤏ Y₂` is a morphism `g` by rigidity: a curve contracted on `Y₁` has degree
zero against the pulled-back ample adjoint. Both models contract the same prime divisors of `X`,
by the strict positivity of the comparison at contracted divisors, so `g` contracts no divisor;
then the pull-back of the push-forward of an ample divisor `H` of `Y₁` is `H`, which is `g`-ample,
and `g` is an isomorphism. -/
private theorem exists_iso_of_isRealLogMinimalModel_of_isRelativelyAmple
    {X Z Y₁ Y₂ : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsNormal Y₁] [CompactSpace Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₂] [IsNormal Y₂] [CompactSpace Y₂]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {s₁ : Y₁ ⟶ Spec (.of ℂ)}
    {s₂ : Y₂ ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {π : X ⟶ Z} {π₁ : Y₁ ⟶ Z} {π₂ : Y₂ ⟶ Z} (hπb : IsBirationalMorphism π)
    {K : Divisor X} {Δ : RDivisor X}
    {K₁ : Divisor Y₁} {Δ₁ : RDivisor Y₁} {K₂ : Divisor Y₂} {Δ₂ : RDivisor Y₂}
    {φ₁ : X.RationalMap Y₁} {φ₂ : X.RationalMap Y₂}
    (h₁ : IsRealLogMinimalModel sX s₁ sZ π π₁ K Δ K₁ Δ₁ φ₁)
    (h₂ : IsRealLogMinimalModel sX s₂ sZ π π₂ K Δ K₂ Δ₂ φ₂)
    (hφ₁E : ∀ F : MMP.Mori.PrimeDivisor Y₁, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ₁ F)
    (hφ₂E : ∀ F : MMP.Mori.PrimeDivisor Y₂, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ₂ F)
    (hamp : IsRelativelyAmple π₂ (logCanonicalDivisor K₂ Δ₂)) :
    ∃ e : Y₁ ≅ Y₂, e.hom ≫ π₂ = π₁ := by
  classical
  have hY₁p := h₁.isProjectiveVariety_model
  have hY₂p := h₂.isProjectiveVariety_model
  haveI : QuasiCompact s₁ := hY₁p.toIsVariety.toQuasiCompact
  haveI : QuasiCompact s₂ := hY₂p.toIsVariety.toQuasiCompact
  haveI : IsSeparated s₁ := hY₁p.toIsVariety.toIsSeparated
  haveI : IsSeparated s₂ := hY₂p.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType s₁ := hY₁p.toIsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s₂ := hY₂p.toIsVariety.toLocallyOfFiniteType
  haveI := hZn.1.toIsIntegral
  haveI := hZn.2
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hZn.1
  obtain ⟨hK₁, hΔ₁, N₁⟩ :=
    IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional hX hXq h₁ hφ₁E
  obtain ⟨hK₂, hΔ₂, N₂⟩ :=
    IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional hX hXq h₂ hφ₂E
  subst hK₁ hΔ₁ hK₂ hΔ₂
  have hπ₁b := IsNefWeakModel.isBirationalMorphism_base N₁ hπb
  have hπ₂b := IsNefWeakModel.isBirationalMorphism_base N₂ hπb
  have hπs : π ≫ sZ = sX := h₁.comp_eq
  have hπ₁s : π₁ ≫ sZ = s₁ := h₁.comp_eq_model
  have hπ₂s : π₂ ≫ sZ = s₂ := h₂.comp_eq_model
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper s₁ := isProper_of_isProjectiveMorphism _ hY₁p.isProjective
  haveI : IsProper s₂ := isProper_of_isProjectiveMorphism _ hY₂p.isProjective
  haveI : IsProper (π ≫ sZ) := by rw [hπs]; infer_instance
  haveI : IsProper (π₁ ≫ sZ) := by rw [hπ₁s]; infer_instance
  haveI : IsProper (π₂ ≫ sZ) := by rw [hπ₂s]; infer_instance
  haveI : IsProper π := IsProper.of_comp π sZ
  haveI : IsProper π₁ := IsProper.of_comp π₁ sZ
  haveI : IsProper π₂ := IsProper.of_comp π₂ sZ
  have hXn : IsNormalVariety ℂ sX := h₁.isRealLcPair.1
  have hY₁n : IsNormalVariety ℂ s₁ := h₁.isNormalVariety_model
  have hY₂n : IsNormalVariety ℂ s₂ := h₂.isNormalVariety_model
  -- the resolution of `φ₂` carrying the strict positivity at contracted divisors
  obtain ⟨W₂, iW₂, lW₂, nW₂, sW₂, p₂, q₂, h₂', GX₂, GY₂, hR₂, hpos₂⟩ := h₂.exists_resolution_pos
  haveI := isProper_of_isProjectiveMorphism p₂ hR₂.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q₂ hR₂.isProjectiveMorphism_right
  have hW₂n : IsNormalVariety ℂ (p₂ ≫ π ≫ sZ) := by
    rw [hπs, hR₂.comp_eq_left]; exact ⟨hR₂.isVariety, inferInstance⟩
  -- a common smooth model `W` of `X`, `Y₁`, `Y₂` and `W₂` over `Z`
  let T : Bool × Bool → Scheme.{0} := fun s => match s with
    | (true, true) => X
    | (true, false) => Y₁
    | (false, true) => Y₂
    | (false, false) => W₂
  let F : ∀ s, T s ⟶ Z := fun s => match s with
    | (true, true) => π
    | (true, false) => π₁
    | (false, true) => π₂
    | (false, false) => p₂ ≫ π
  haveI hFp : ∀ s, IsProper (F s) := fun s => match s with
    | (true, true) => inferInstanceAs (IsProper π)
    | (true, false) => inferInstanceAs (IsProper π₁)
    | (false, true) => inferInstanceAs (IsProper π₂)
    | (false, false) => inferInstanceAs (IsProper (p₂ ≫ π))
  have hFb : ∀ s, IsBirationalMorphism (F s) := fun s => match s with
    | (true, true) => hπb
    | (true, false) => hπ₁b
    | (false, true) => hπ₂b
    | (false, false) => MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hR₂.isBirationalMorphism_left hπb
  have hFn : ∀ s, IsNormalVariety ℂ (F s ≫ sZ) := fun s => match s with
    | (true, true) => by change IsNormalVariety ℂ (π ≫ sZ); rw [hπs]; exact hXn
    | (true, false) => by change IsNormalVariety ℂ (π₁ ≫ sZ); rw [hπ₁s]; exact hY₁n
    | (false, true) => by change IsNormalVariety ℂ (π₂ ≫ sZ); rw [hπ₂s]; exact hY₂n
    | (false, false) => by
        change IsNormalVariety ℂ ((p₂ ≫ π) ≫ sZ); rw [Category.assoc]; exact hW₂n
  obtain ⟨W, w, hWn, hwb, g, -, hwp, hg, -, -⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_smooth_projective_model sZ F hFb hFn
      (κ := Empty) Empty.elim (fun j => j.elim)
  set g₀ : W ⟶ X := g (true, true) with hg₀def
  set g₁ : W ⟶ Y₁ := g (true, false) with hg₁def
  set g₂ : W ⟶ Y₂ := g (false, true) with hg₂def
  set r : W ⟶ W₂ := g (false, false) with hrdef
  have hg₀w : g₀ ≫ π = w := (hg (true, true)).1
  have hg₁w : g₁ ≫ π₁ = w := (hg (true, false)).1
  have hg₂w : g₂ ≫ π₂ = w := (hg (false, true)).1
  have hrw : r ≫ p₂ ≫ π = w := (hg (false, false)).1
  have hg₀p : IsProjectiveMorphism g₀ := (hg (true, true)).2.1
  have hg₁p : IsProjectiveMorphism g₁ := (hg (true, false)).2.1
  have hg₂p : IsProjectiveMorphism g₂ := (hg (false, true)).2.1
  have hg₀b : IsBirationalMorphism g₀ := (hg (true, true)).2.2
  have hg₁b : IsBirationalMorphism g₁ := (hg (true, false)).2.2
  have hg₂b : IsBirationalMorphism g₂ := (hg (false, true)).2.2
  have hrb : IsBirationalMorphism r := (hg (false, false)).2.2
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI := isProper_of_isProjectiveMorphism g₀ hg₀p
  haveI := isProper_of_isProjectiveMorphism g₁ hg₁p
  haveI := isProper_of_isProjectiveMorphism g₂ hg₂p
  haveI := hg₀b.isDominant
  haveI := hg₁b.isDominant
  haveI := hg₂b.isDominant
  haveI := hrb.isDominant
  haveI := hπb.isDominant
  haveI := hwb.isDominant
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  have hg₀s : g₀ ≫ sX = w ≫ sZ := by rw [← hπs, ← Category.assoc, hg₀w]
  have hg₁s : g₁ ≫ s₁ = w ≫ sZ := by rw [← hπ₁s, ← Category.assoc, hg₁w]
  have hg₂s : g₂ ≫ s₂ = w ≫ sZ := by rw [← hπ₂s, ← Category.assoc, hg₂w]
  -- `h = g₀⁻¹`, and `g_i ∘ h = φ_i`
  set h := hg₀b.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse g₀.toRationalMap h := hg₀b.isInverse_inverse
  haveI := isSeparated_terminal_of sX
  have hψ : ∀ {Y' : Scheme.{0}} [IsIntegral Y'] (π' : Y' ⟶ Z) [IsProper π'],
      IsBirationalMorphism π' → ∀ (g' : W ⟶ Y') {φ' : X.RationalMap Y'}, g' ≫ π' = w →
        MMP.Flips.RationalMap.IsOver π π' φ' → h.compHom g' = φ' := by
    intro Y' _ π' _ hπ' g' φ' hg' hφ'
    exact compHom_eq_of_isInverse_of_isOver hπ' (hg₀w.trans hg'.symm) hinv hφ'
  have hψ₁ : h.compHom g₁ = φ₁ := hψ π₁ hπ₁b g₁ hg₁w N₁.isOver
  have hψ₂ : h.compHom g₂ = φ₂ := hψ π₂ hπ₂b g₂ hg₂w N₂.isOver
  -- the pulled-back adjoints agree
  obtain ⟨D₁, hD₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₁
    (isCartierCombination_of_isQFactorial h₁.isQFactorial
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)))
  obtain ⟨D₂, hD₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₂
    (isCartierCombination_of_isQFactorial h₂.isQFactorial
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ K)
        (MMP.Mori.RationalMap.transformDivisor φ₂ Δ)))
  have hcomm₁₂' : g₁ ≫ π₁ = g₂ ≫ π₂ := hg₁w.trans hg₂w.symm
  have hDD : D₁ = D₂ := (N₁.eq_of_isRCartierPullback_and_isNefModelEquivalent N₂).1 (w ≫ sZ)
    g₁ g₂ h hWn.1 hg₁s hg₂s hg₁p hg₂p hg₁b hg₂b hψ₁ hψ₂ hD₁ hD₂
  -- rigidity: a morphism `gg : Y₁ ⟶ Y₂` with `g₁ ≫ gg = g₂`
  haveI : IsProper w := isProper_of_isProjectiveMorphism w hwp
  haveI : IsProper (w ≫ sZ) := inferInstance
  haveI : IsSeparated (π₂ ≫ sZ) := by rw [hπ₂s]; infer_instance
  haveI : IsSeparated π₂ := IsSeparated.of_comp π₂ sZ
  have hcurve : ∀ C : Set W, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
      (g₁.base '' C).Subsingleton → (g₂.base '' C).Subsingleton := by
    intro C hCc hCi hCd hC1
    by_contra hns
    set x := hCi.genericPoint with hxdef
    have hxC : closure ({x} : Set W) = C := hCi.isGenericPoint_genericPoint hCc
    have hΓp : IsProperCurve (w ≫ sZ) x := MMP.Mori.isProperCurve_of_isProper _ (by
      rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hxC]; exact hCd)
    let Γ : ProperCurve (w ≫ sZ) := ⟨x, hΓp⟩
    have hΓ₁ : Γ.IsContractedBy g₁ := fun y hy =>
      hC1 ⟨y, hxC ▸ hy, rfl⟩ ⟨x, hxC ▸ subset_closure rfl, rfl⟩
    have hΓ₂ : ¬ Γ.IsContractedBy g₂ := fun hc => hns (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← hxC] at ha hb
      exact (hc a ha).trans (hc b hb).symm)
    let Γ₂ : ProperCurve s₂ := ⟨g₂ x, MMP.Fourfold.Oai4C1.isProperCurve_map g₂ hg₂s Γ hΓ₂⟩
    have hΓ₂c : Γ₂.IsContractedBy π₂ := MMP.Fourfold.Oai4C1.isContractedBy_map g₂ hg₂s π₂ Γ hΓ₂
      (fun y hy => by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
          ← Scheme.Hom.comp_apply, ← hcomm₁₂', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
          hΓ₁ y hy])
    -- `D₂ · Γ = [k(Γ) : k(Γ₂)] (A₂ · Γ₂) > 0`
    obtain ⟨m, c, L, L', hL, hAL, hpb, hDL⟩ := hD₂
    have hL'c : ∀ j, (L' j).IsCartier := fun j => (hpb j).2.isCartier (hL j)
    have hx₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (w ≫ sZ) Γ c L' hL'c
    rw [← hDL] at hx₂
    have hmul : ∀ j, ((L' j).degreeOn ℂ (w ≫ sZ) Γ.ι Γ.dim_le (hL'c j) : ℝ) =
        (residueFieldDegree g₂ Γ.point : ℝ) *
          ((L j).degreeOn ℂ s₂ Γ₂.ι Γ₂.dim_le (hL j) : ℝ) := fun j =>
      MMP.Fourfold.degreeOn_eq_mul_of_isPullback g₂ hg₂s (hL j) (hpb j).2 (hL'c j) Γ Γ₂ rfl
    have hA := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ s₂ Γ₂ c L hL
    rw [← hAL] at hA
    have hApos := isRIntersectionNumber_pos_of_isRelativelyAmple π₂ hamp Γ₂ hΓ₂c c L _ hA
    have hd := MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy g₂ hg₂s Γ hΓ₂
    -- `D₁ · Γ = 0`
    obtain ⟨m₁, c₁, L₁, L₁', hL₁, -, hpb₁, hDL₁⟩ := hD₁
    have hL₁'c : ∀ j, (L₁' j).IsCartier := fun j => (hpb₁ j).2.isCartier (hL₁ j)
    have hx₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (w ≫ sZ) Γ c₁ L₁' hL₁'c
    rw [← hDL₁, hDD] at hx₁
    have h0 : ∀ j, (L₁' j).degreeOn ℂ (w ≫ sZ) Γ.ι Γ.dim_le (hL₁'c j) = 0 := fun j =>
      MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_zero g₁ hg₁s (hL₁ j) (hpb₁ j).2 Γ hΓ₁
    have heq := (IsRIntersectionNumber.eq_and_linear ℂ (w ≫ sZ) Γ).1 _ _ _ _ _ _ _ hx₁ hx₂
    simp only [h0, Int.cast_zero, mul_zero, Finset.sum_const_zero, hmul] at heq
    have hpos : 0 < ∑ j, c j * ((residueFieldDegree g₂ Γ.point : ℝ) *
        ((L j).degreeOn ℂ s₂ Γ₂.ι Γ₂.dim_le (hL j) : ℝ)) := by
      simp only [mul_left_comm (c _), ← Finset.mul_sum]
      exact mul_pos (by exact_mod_cast hd) hApos
    linarith
  obtain ⟨gg, hgg, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isBirationalMorphism_of_forall_curve
    s₁ hY₁n.1 (sX := π₁) (sY := π₂) g₁ (by rw [hg₁s]; exact hWn.1) hg₁b g₂ hcomm₁₂' hcurve
  have hggs : gg ≫ s₂ = s₁ := AlgebraicGeometry.ext_of_isDominant g₁ (by
    rw [← Category.assoc, hgg, hg₂s, hg₁s])
  have hggπ : gg ≫ π₂ = π₁ := AlgebraicGeometry.ext_of_isDominant_of_isSeparated sZ
    (by rw [Category.assoc, hπ₂s, hggs, hπ₁s]) g₁ (by rw [← Category.assoc, hgg, hg₂w, hg₁w])
  haveI : LocallyOfFiniteType (gg ≫ s₂) := by rw [hggs]; infer_instance
  haveI : LocallyOfFiniteType gg := LocallyOfFiniteType.of_comp (f := gg) (g := s₂) inferInstance
  haveI : IsProper (gg ≫ s₂) := by rw [hggs]; infer_instance
  haveI : IsProper gg := IsProper.of_comp gg s₂
  have hggb : IsBirationalMorphism gg :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left g₁ gg hg₁b (hgg ▸ hg₂b)
  haveI := hggb.isDominant
  -- `gg` contracts no prime divisor
  have hWg₀ : IsNormalVariety ℂ (g₀ ≫ sX) := by rw [hg₀s]; exact hWn
  have hWg₁ : IsNormalVariety ℂ (g₁ ≫ s₁) := by rw [hg₁s]; exact hWn
  obtain ⟨GX, hGX, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₀
    (isCartierCombination_of_isQFactorial hXq (logCanonicalDivisor K Δ))
  have hsmall : ∀ F : MMP.Mori.PrimeDivisor Y₁,
      ∃ F' : MMP.Mori.PrimeDivisor Y₂, gg F.genericPoint = F'.genericPoint := by
    intro F
    obtain ⟨P, hP⟩ := exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional hφ₁E F
    obtain ⟨PW, hPW, hPWiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWg₀ hg₀b P
    have hF : g₁ PW.genericPoint = F.genericPoint :=
      (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse g₀ hg₀b hinv g₁ hψ₁ P PW hPW
        F).mp hP
    obtain ⟨g', hg', hPg, hg'P⟩ := MMP.Fourfold.exists_rep_apply_eq_of_isInverse g₀ hg₀b hinv P PW
        hPW
    by_cases hco : Order.coheight (g₂ PW.genericPoint) ≤ 1
    · obtain ⟨F', hF', -⟩ :=
        MMP.Fourfold.exists_primeDivisor_of_coheight_le_one g₂ hg₂b.functionFieldMap_bijective PW
            hco
      exact ⟨F', by rw [← hF, ← Scheme.Hom.comp_apply, hgg, hF']⟩
    exfalso
    -- `P` is contracted by `φ₂`
    have hexc : MMP.Mori.RationalMap.IsExceptional φ₂ P := by
      by_contra hne
      have := MMP.Fourfold.SamePrimes.coheight_apply_le_one_of_not_isExceptional g₂ g'
        (by rw [Scheme.RationalMap.compHom_toRationalMap, hg', hψ₂]) hPg hne
      rw [hg'P] at this
      exact hco this
    -- the strict transform of `P` on `W₂`, where the comparison is positive
    have hW₂p : IsNormalVariety ℂ (p₂ ≫ sX) := by
      rw [hR₂.comp_eq_left]; exact ⟨hR₂.isVariety, inferInstance⟩
    obtain ⟨P₂, hP₂, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hXn hW₂p hR₂.isBirationalMorphism_left P
    haveI : IsSeparated sW₂ := hR₂.isVariety.toIsSeparated
    haveI := isSeparated_terminal_of sW₂
    haveI : IsSeparated (p₂ ≫ sX) := by rw [hR₂.comp_eq_left]; infer_instance
    haveI : IsSeparated p₂ := IsSeparated.of_comp p₂ sX
    have hP₂h : MMP.Mori.RationalMap.transformPrimeDivisor h₂' P = some P₂ :=
      (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse p₂ hR₂.isBirationalMorphism_left
        hR₂.isInverse (𝟙 W₂) (rationalMap_compHom_id h₂') P P₂ hP₂ P₂).mpr rfl
    have hpos := hpos₂ P hexc P₂ hP₂h
    -- transfer to `W` through `r : W ⟶ W₂`
    have hrp : r ≫ p₂ = g₀ := by
      haveI : IsDominant ((r ≫ p₂) ≫ π) := by rw [Category.assoc, hrw]; infer_instance
      exact MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hπb (by rw [Category.assoc, hrw, hg₀w])
    haveI := hR₂.isBirationalMorphism_left.isDominant
    haveI := isSeparated_terminal_of sZ
    have hpq₂ : p₂ ≫ π = q₂ ≫ π₂ := MMP.Fourfold.comp_eq_comp_of_isOver π π₂ h₂.isOver p₂ q₂ h₂'
      hR₂.isInverse hR₂.compHom_eq
    have hrq : r ≫ q₂ = g₂ := by
      haveI : IsDominant ((r ≫ q₂) ≫ π₂) := by
        rw [Category.assoc, ← hpq₂, hrw]; infer_instance
      exact MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hπ₂b
        (by rw [Category.assoc, ← hpq₂, hrw, hg₂w])
    haveI : IsDominant (r ≫ p₂) := by rw [hrp]; infer_instance
    haveI : IsDominant (r ≫ q₂) := by rw [hrq]; infer_instance
    have hGXr : MMP.Flips.IsRCartierPullback r GX₂ GX :=
      isRCartierPullback_of_isRCartierPullback_comp hR₂.isRCartierPullback_left
        (by rw [hrp]; exact hGX)
    have hGYr : MMP.Flips.IsRCartierPullback r GY₂ D₂ :=
      isRCartierPullback_of_isRCartierPullback_comp hR₂.isRCartierPullback_right
        (by rw [hrq]; exact hD₂)
    have := P.isDiscreteValuationRing_localRing
    have hrP : r PW.genericPoint = P₂.genericPoint :=
      MMP.Fourfold.eq_of_map_eq_of_valuationRing
        hR₂.isBirationalMorphism_left.functionFieldMap_bijective
        (by rw [← Scheme.Hom.comp_apply, hrp, hPW]) hP₂
    have := P₂.isDiscreteValuationRing_localRing
    haveI : ValuationRing (W₂.presheaf.stalk (r PW.genericPoint)) := by
      rw [hrP]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing r hrb.functionFieldMap_bijective
      PW.genericPoint
    have c1 : GX.coeff PW = GX₂.coeff P₂ := MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P₂ hrP
        hGXr
    have c2 : D₂.coeff PW = GY₂.coeff P₂ := MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P₂ hrP
        hGYr
    -- on the other side the comparison vanishes at `P_W`, which `φ₁` keeps
    haveI := hPWiso
    have c3 : GX.coeff PW = (logCanonicalDivisor K Δ).coeff P :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P hPW hGX
    have := F.isDiscreteValuationRing_localRing
    haveI : ValuationRing (Y₁.presheaf.stalk (g₁ PW.genericPoint)) := by
      rw [hF]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g₁ hg₁b.functionFieldMap_bijective
      PW.genericPoint
    have c4 : D₁.coeff PW = (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)).coeff F :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW F hF hD₁
    have c5 : (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)).coeff F =
        (logCanonicalDivisor K Δ).coeff P := by
      rw [← transformDivisor_logCanonicalDivisor]
      exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP
        (fun R hR => eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hY₁n hWg₀
          (hg₀s.trans hg₁s.symm) hg₀b hg₁b hinv hψ₁ hR hP) _
    rw [DivisorWithCoeffs.coeff_sub, ← c1, ← c2, ← hDD, c3, c4, c5, sub_self] at hpos
    exact lt_irrefl _ hpos
  -- `gg` is an isomorphism: the pull-back of the push-forward of an ample `H` is `H`
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s₁ := hY₁p
  obtain ⟨H, hHc, -, hHa⟩ := MMP.Mori.exists_isCartier_isEffective_isAmple s₁
  have hHr : MMP.Flips.IsRelativelyAmpleCartier gg H :=
    MMP.Flips.isRelativelyAmpleCartier_of_isRelativelyAmple hHc
      (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf gg hHc hHa)
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback gg
    (isCartierCombination_of_isQFactorial h₂.isQFactorial
      (MMP.Mori.RationalMap.transformDivisor gg.toRationalMap (Divisor.toRDivisor H)))
  have hGH : G = Divisor.toRDivisor H := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨F', hF'⟩ := hsmall F
    have := F'.isDiscreteValuationRing_localRing
    haveI : ValuationRing (Y₂.presheaf.stalk (gg F.genericPoint)) := by rw [hF']; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing gg hggb.functionFieldMap_bijective
      F.genericPoint
    have c1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback F F' hF' hG
    obtain ⟨E, hE, -, hEc⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hY₂n (by rw [hggs]; exact hY₁n) hggb F'
    haveI : IsSeparated gg := inferInstance
    have hEF : E = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.eq_of_map_eq_of_valuationRing hggb.functionFieldMap_bijective hE hF')
    change G.coeff F = (Divisor.toRDivisor H).coeff F
    rw [c1]
    change MMP.Mori.RationalMap.transformDivisor gg.toRationalMap (Divisor.toRDivisor H) F' = _
    rw [hEc, hEF]
    rfl
  have hamp' : MMP.Flips.IsRelativelyAmple gg G := by
    rw [hGH]
    exact ⟨1, fun _ => 1, fun _ => H, le_rfl, fun _ => one_pos, fun _ => hHr, by simp⟩
  haveI : IsNoetherian Y₁ := ⟨⟩
  haveI := MMP.Flips.isIso_of_isRelativelyAmple_of_isRCartierPullback gg hggb hG hamp'
  exact ⟨asIso gg, hggπ⟩

end AmpleModel

/-! ### A basis of `N¹(X/Z)` inside the boundary, and a rational polytope -/

section BasisShift

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {K : Divisor X} {B C : RDivisor X}

/-- A divisor supported on a finite set `s` is the sum of its coefficients along `s`. -/
private theorem eq_sum_single_of_support_subset {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {Θ : RDivisor X} {s : Finset (MMP.Mori.PrimeDivisor X)}
    (hs : Θ.support ⊆ s) :
    Θ = ∑ j : s, Finsupp.single j.1 (Θ.coeff j.1) := by
  classical
  refine Finsupp.ext fun W => ?_
  have h := MMP.Fourfold.coeff_sum_single (fun j : s => j.1) (fun j => Θ.coeff j.1) W
  rw [DivisorWithCoeffs.coeff_apply] at h
  rw [h]
  by_cases hW : W ∈ s
  · rw [Fintype.sum_eq_single ⟨W, hW⟩ (fun j hj => if_neg fun h' => hj (Subtype.ext h')),
      if_pos rfl]
    rfl
  · rw [Finset.sum_eq_zero fun (j : s) _ => if_neg fun (h' : j.1 = W) => hW (h' ▸ j.2)]
    by_contra h0
    exact hW (hs (Finsupp.mem_support_iff.mpr h0))

/-- **Klt pairs on a `ℚ`-factorial variety are convex**: if `(X, Θ₀)` and `(X, Θ₁)` are klt, so is
`(X, (1 - s) Θ₀ + s Θ₁)` for `0 ≤ s ≤ 1`. -/
private theorem isRealKltPair_segment {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {Θ₀ Θ₁ : RDivisor X} (h₀ : IsRealKltPair sX Θ₀) (h₁ : IsRealKltPair sX Θ₁) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsRealKltPair sX ((1 - s) • Θ₀ + s • Θ₁) := by
  classical
  set t := Θ₀.support ∪ Θ₁.support
  let p : t → MMP.Mori.PrimeDivisor X := Subtype.val
  have e₀ := eq_sum_single_of_support_subset (Θ := Θ₀) (s := t) Finset.subset_union_left
  have e₁ := eq_sum_single_of_support_subset (Θ := Θ₁) (s := t) Finset.subset_union_right
  have hΘ : (1 - s) • Θ₀ + s • Θ₁ = ∑ j : t, Finsupp.single (p j)
      ((1 - s) * Θ₀.coeff j.1 + s * Θ₁.coeff j.1) := by
    conv_lhs => rw [e₀, e₁]
    simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← Finset.sum_add_distrib,
      ← Finsupp.single_add]
    rfl
  choose m hm hmc using fun j : t => hQ.2 (Finsupp.single (p j) (1 : ℤ))
  have hconv := MMP.Fourfold.convex_setOf_lt_isLogDiscrepancy (k := ℂ) (sX := sX) p m hm hmc 0 (fun
      _ => True)
  have hy₀ : (fun j : t => Θ₀.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      True → MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D a →
        0 < a} := fun n D a _ ha => h₀.2.2.2 n D a (e₀ ▸ ha)
  have hy₁ : (fun j : t => Θ₁.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      True → MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D a →
        0 < a} := fun n D a _ ha => h₁.2.2.2 n D a (e₁ ▸ ha)
  have hy := hconv hy₀ hy₁ (sub_nonneg.2 hs1) hs0 (by ring)
  obtain ⟨n, K, hK, -⟩ := h₀.2.2.1
  refine ⟨h₀.1, fun P => ?_, ⟨n, K, hK, ?_⟩, fun n' D a ha => ?_⟩
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul, smul_eq_mul]
    have ha := h₀.2.1 P
    have hb := h₁.2.1 P
    by_cases h1 : s = 1
    · subst h1; simpa using hb
    · nlinarith [mul_lt_mul_of_pos_left ha (sub_pos.2 (lt_of_le_of_ne hs1 h1)),
        mul_le_mul_of_nonneg_left hb.le hs0]
  · rw [hΘ]
    exact MMP.Fourfold.isRCartier_add_sum_single hQ K p _
  · refine hy n' D a trivial ?_
    rw [hΘ] at ha
    convert ha using 3

/-- **Finitely many prime divisors span `N¹(X/Z)`.** For a projective birational morphism
`π : X ⟶ Z` of normal projective complex varieties with `X` `ℚ`-factorial, there is a finite set
`S` of prime divisors of `X` such that every `ℝ`-Cartier divisor is numerically equivalent over
`Z` to an `ℝ`-divisor supported on `S`: the components of the strict transform of the divisor of
a procedure datum for `(Z, 0, 𝟙)` and the finitely many `π`-exceptional prime divisors. -/
private theorem exists_finset_isNumericallyEquivalentOver {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π) (hXq : IsQFactorial sX) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor X), ∀ D : RDivisor X, IsCartierCombination D →
      ∃ G : RDivisor X, (∀ P, G.coeff P ≠ 0 → P ∈ S) ∧
        IsNumericallyEquivalentOver ℂ sX π D G := by
  classical
  haveI : IsLocallyNoetherian Z := hZn.1.toLocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZn.2
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπp
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hZq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sZ :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sZ hZ
  -- a procedure datum for `(Z, 0, 𝟙)`
  have hbd : IsBoundary (0 : RDivisor Z) := fun E => by simp
  
  have hsm : IsSmall ℂ sZ sZ (𝟙 Z) :=
    { isVariety_target := hZn.1
      isVariety_source := hZn.1
      comp_eq := Category.id_comp sZ
      isProper := inferInstance
      isIso_app := fun _ => inferInstance
      dim_eq := rfl
      exists_isIso := ⟨⊥, ⊥, le_closedsCodimension_iff_le_coheight.mpr (by simp),
        le_closedsCodimension_iff_le_coheight.mpr (by simp), le_rfl, by
          simp only [Scheme.Hom.resLE_id, Scheme.homOfLE_rfl]
          infer_instance⟩ }
  obtain ⟨P₀⟩ := ProcedureDatum.nonempty (D := (0 : RDivisor Z)) hZn hbd hsm
    (isProjectiveMorphism_id _) hZq
  -- the `π`-exceptional prime divisors are finitely many
  have hinv : MMP.Mori.RationalMap.IsInverse π.toRationalMap hπb.inverse := hπb.isInverse_inverse
  have hfa := MMP.Flips.RationalMap.finite_setOf_isInverseExceptional hZn hXn hπb.inverse
      hπb.isBirational_inverse
    (MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hZn π (hπ ▸ hXn.1) hπb)
  have hexc : ∀ E, IsExceptionalPrimeDivisor sZ π E →
      E ∈ hfa.1.toFinset := fun E hE => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hfa.2 π inferInstance hπ hinv]
    exact hE
  refine ⟨(birationalInverseTransform π hπb P₀.H').support ∪ hfa.1.toFinset, fun D hD => ?_⟩
  obtain ⟨G, hG, hDG⟩ := P₀.exists_isNumericallyEquivalentOver_of_isQFactorial hXq hπ hπb hD
  refine ⟨G, fun P hP => ?_, hDG⟩
  rcases hG P hP with h | h
  · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h)
  · exact Finset.mem_union_right _ (hexc P h)

/-- A numerical intersection number of a real combination `∑ⱼ wⱼ Dⱼ` of `ℝ`-Cartier divisors
with known intersection numbers `xⱼ` with a curve is `∑ⱼ wⱼ xⱼ`. -/
private theorem exists_isRIntersectionNumber_sum {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (Γ : ProperCurve sX) {κ : Type} (s : Finset κ) (D : κ → RDivisor X) (x : κ → ℝ)
    (hx : ∀ j, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber k sX (D j) r L Γ (x j)) (w : κ → ℝ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber k sX (∑ j ∈ s, w j • D j) r L Γ (∑ j ∈ s, w j * x j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0,
      by simp⟩
  | insert a s ha ih =>
    obtain ⟨m₁, r₁, L₁, h₁⟩ := hx a
    obtain ⟨m₂, r₂, L₂, h₂⟩ := ih
    have h := (IsRIntersectionNumber.eq_and_linear k sX Γ).2 _ _ r₁ L₁ r₂ L₂ _ _ (w a) 1 h₁ h₂
    rw [one_smul, one_mul] at h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨_, _, _, h⟩

/-- **A basis of `N¹(X/W)` inside a spanning family.** If the classes of finitely many Cartier
divisors `vⱼ` span `N¹(X/W)` (every `ℝ`-Cartier divisor is numerically equivalent over `W` to a
real combination of the `vⱼ`), some subfamily `v ∘ a` is a basis: it still spans, and a real
combination of it which is numerically trivial over `W` is trivial. -/
private theorem exists_basis_of_isNumericallyEquivalentOver {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (π : X ⟶ W) {N : ℕ} (v : Fin N → Divisor X) (hv : ∀ j, (v
        j).IsCartier)
    (hspan : ∀ D : RDivisor X, IsCartierCombination D → ∃ c : Fin N → ℝ,
      IsNumericallyEquivalentOver k sX π D (∑ j, c j • Divisor.toRDivisor (v j))) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → Fin N),
      (∀ D : RDivisor X, IsCartierCombination D → ∃ u : ι → ℝ,
        IsNumericallyEquivalentOver k sX π D (∑ i, u i • Divisor.toRDivisor (v (a i)))) ∧
      ∀ u : ι → ℝ,
        IsNumericallyTrivialOver k sX π (∑ i, u i • Divisor.toRDivisor (v (a i))) → u = 0 := by
  classical
  -- intersection numbers of the `vⱼ`
  have hvc : ∀ j, IsCartierCombination (Divisor.toRDivisor (v j)) := fun j =>
    ⟨1, fun _ => 1, fun _ => v j, fun _ => hv j, by
      simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  choose mv rv Lv deg hdeg using fun j (Γ : ProperCurve sX) =>
    MMP.Flips.exists_isRIntersectionNumber (k := k) (hvc j) Γ
  have hcomb : ∀ w : Fin N → ℝ, IsCartierCombination (∑ j, w j • Divisor.toRDivisor (v j)) :=
    fun w => ⟨N, w, v, hv, by simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hnum : ∀ (w : Fin N → ℝ) (Γ : ProperCurve sX), ∃ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X), IsRIntersectionNumber k sX (∑ j, w j • Divisor.toRDivisor (v j))
        r L Γ (∑ j, w j * deg j Γ) := fun w Γ =>
    exists_isRIntersectionNumber_sum Γ Finset.univ _ _ (fun j => ⟨_, _, _, hdeg j Γ⟩) w
  -- the degree map and its kernel
  let Φ : (Fin N → ℝ) →ₗ[ℝ] ({Γ : ProperCurve sX // Γ.IsContractedBy π} → ℝ) :=
    LinearMap.pi fun Γ => ∑ j, deg j Γ.1 • LinearMap.proj j
  have hΦ : ∀ w Γ, Φ w Γ = ∑ j, w j * deg j Γ.1 := fun w Γ => by
    simp [Φ, mul_comm]
  -- numerically trivial combinations lie in the kernel
  have htriv : ∀ w : Fin N → ℝ,
      IsNumericallyTrivialOver k sX π (∑ j, w j • Divisor.toRDivisor (v j)) → Φ w = 0 := by
    intro w hw
    funext Γ
    obtain ⟨m, r, L, h⟩ := hnum w Γ.1
    have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
        (Fin.elim0 : Fin 0 → Divisor X) Γ.1 0 :=
      ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
    rw [hΦ, Pi.zero_apply]
    exact hw.2.2 Γ.1 Γ.2 _ _ _ _ _ _ _ _ h h0
  -- equal degrees give numerical equivalence
  have hequiv : ∀ (D : RDivisor X) (c w : Fin N → ℝ),
      IsNumericallyEquivalentOver k sX π D (∑ j, c j • Divisor.toRDivisor (v j)) →
      Φ c = Φ w →
      IsNumericallyEquivalentOver k sX π D (∑ j, w j • Divisor.toRDivisor (v j)) := by
    intro D c w hD hcw
    refine ⟨hD.1, hcomb w, fun Γ hΓ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    obtain ⟨_, _, _, hc⟩ := hnum c Γ
    obtain ⟨_, _, _, hw⟩ := hnum w Γ
    rw [hD.2.2 Γ hΓ _ _ _ _ _ _ _ _ h₁ hc,
      (IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ h₂ hw]
    have := congrFun hcw ⟨Γ, hΓ⟩
    rwa [hΦ, hΦ] at this
  -- a basis of the quotient among the classes of the `vⱼ`
  let f : Fin N → (Fin N → ℝ) ⧸ LinearMap.ker Φ := fun j => (LinearMap.ker Φ).mkQ (Pi.single j 1)
  have hf : Submodule.span ℝ (Set.range f) = ⊤ := by
    have : Set.range f = (LinearMap.ker Φ).mkQ '' Set.range (Pi.basisFun ℝ (Fin N)) := by
      rw [← Set.range_comp]
      congr 1
      funext j
      simp [f, Pi.basisFun_apply]
    rw [this, Submodule.span_image, (Pi.basisFun ℝ (Fin N)).span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, -, hspan', hli⟩ := exists_linearIndependent' ℝ f
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  let wU : (κ → ℝ) → Fin N → ℝ := fun u => ∑ i, u i • Pi.single (a i) 1
  have hwU : ∀ u : κ → ℝ, ∑ j, wU u j • Divisor.toRDivisor (v j) =
      ∑ i, u i • Divisor.toRDivisor (v (a i)) := fun u => by
    simp only [wU, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp
  have hmk : ∀ u : κ → ℝ, (LinearMap.ker Φ).mkQ (wU u) = ∑ i, u i • f (a i) := fun u => by
    simp [wU, f, map_sum, map_smul]
  refine ⟨κ, inferInstance, a, fun D hD => ?_, fun u hu => ?_⟩
  · obtain ⟨c, hc⟩ := hspan D hD
    have hmem : (LinearMap.ker Φ).mkQ c ∈ Submodule.span ℝ (Set.range (f ∘ a)) := by
      rw [hspan', hf]; exact Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨u, ?_⟩
    rw [← hwU]
    refine hequiv D c (wU u) hc ?_
    have h1 : (LinearMap.ker Φ).mkQ (wU u) = (LinearMap.ker Φ).mkQ c := by
      rw [hmk, ← hu]; rfl
    have h2 := LinearMap.mem_ker.mp ((Submodule.Quotient.eq _).mp h1)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  · rw [← hwU] at hu
    have h0 := htriv _ hu
    have h1 : (LinearMap.ker Φ).mkQ (wU u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h0
    rw [hmk] at h1
    exact funext (Fintype.linearIndependent_iff.mp hli u h1)

open Filter Topology in
/-- **Klt survives a small effective perturbation.** If `(X, Θ)` is klt with `Θ` effective and
`T` is effective, then `(X, Θ + t T)` is klt for all small `t ≥ 0`. -/
private theorem exists_isRealKltPair_add_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX) {Θ T : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hT : ∀ P, 0 ≤ T.coeff P)
    (hk : IsRealKltPair sX Θ) :
    ∃ t₀ > 0, ∀ t : ℝ, 0 ≤ t → t < t₀ → IsRealKltPair sX (Θ + t • T) := by
  classical
  set s := Θ.support ∪ T.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : ℝ → s → ℝ := fun t j => Θ.coeff j.1 + t * T.coeff j.1
  have hrep : ∀ t : ℝ, Θ + t • T = ∑ j, Finsupp.single (p j) (y t j) := fun t => by
    have hsub : (Θ + t • T).support ⊆ s := fun P hP => by
      by_contra h
      rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at h
      exact (Finsupp.mem_support_iff.mp hP) (by simp [h.1, h.2])
    rw [eq_sum_single_of_support_subset hsub]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  have hcont : Continuous y :=
    continuous_pi fun j => continuous_const.add (continuous_id.mul continuous_const)
  have htend : Tendsto y (𝓝[≥] 0) (𝓝[Set.Ici 0] (y 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t (ht : 0 ≤ t) j =>
        add_nonneg (hΘ _) (mul_nonneg ht (hT _))⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (htend.eventually hev)
  exact ⟨u, hu, fun t ht0 htu => by rw [hrep]; exact hsub ⟨ht0, htu⟩⟩

/-- **Cartier multiples of a spanning set of primes.** On a `ℚ`-factorial variety, if every
`ℝ`-Cartier divisor is numerically equivalent over `W` to one supported on the finite set `S`, then
finitely many Cartier divisors supported on `S` (multiples of its members) span `N¹(X/W)`. -/
private theorem exists_cartier_spanning {k : Type} [Field k] {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {π : X ⟶ W}
    (hQ : IsQFactorial sX) (S : Finset (MMP.Mori.PrimeDivisor X))
    (hS : ∀ D : RDivisor X, IsCartierCombination D → ∃ G : RDivisor X,
      (∀ P, G.coeff P ≠ 0 → P ∈ S) ∧ IsNumericallyEquivalentOver k sX π D G) :
    ∃ (N : ℕ) (v : Fin N → Divisor X), (∀ j, (v j).IsCartier) ∧
      (∀ j P, (v j).coeff P ≠ 0 → P ∈ S) ∧
      ∀ D : RDivisor X, IsCartierCombination D → ∃ c : Fin N → ℝ,
        IsNumericallyEquivalentOver k sX π D (∑ j, c j • Divisor.toRDivisor (v j)) := by
  classical
  let e := S.equivFin
  let q : Fin S.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j).1
  choose m hm hmc using fun j => hQ.2 (Finsupp.single (q j) (1 : ℤ))
  let v : Fin S.card → Divisor X := fun j => (m j : ℤ) • Finsupp.single (q j) 1
  have hvP : ∀ j P, (v j).coeff P = if q j = P then (m j : ℤ) else 0 := fun j P => by
    simp [v, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
  refine ⟨S.card, v, hmc, fun j P hP => ?_, fun D hD => ?_⟩
  · rw [hvP] at hP
    split_ifs at hP with h
    · exact h ▸ (e.symm j).2
    · exact absurd rfl hP
  · obtain ⟨G, hGS, hDG⟩ := hS D hD
    refine ⟨fun j => G.coeff (q j) / m j, ?_⟩
    convert hDG using 1
    refine (Finsupp.ext fun P => ?_).symm
    change G.coeff P = (∑ j, (G.coeff (q j) / m j) • Divisor.toRDivisor (v j)).coeff P
    rw [show (∑ j, (G.coeff (q j) / m j) • Divisor.toRDivisor (v j)).coeff P =
        ∑ j, G.coeff (q j) / m j * (v j).coeff P by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]; rfl]
    simp_rw [hvP]
    by_cases hP : P ∈ S
    · rw [Fintype.sum_eq_single (e ⟨P, hP⟩) fun j hj => ?_]
      · have : q (e ⟨P, hP⟩) = P := by simp [q]
        rw [if_pos this, this]
        have hm0 : (m (e ⟨P, hP⟩) : ℝ) ≠ 0 := by exact_mod_cast (hm _).ne'
        push_cast
        field_simp
      · rw [if_neg, Int.cast_zero, mul_zero]
        intro h
        apply hj
        rw [← e.apply_symm_apply j]
        congr 1
        exact Subtype.ext h
    · have hG0 : G.coeff P = 0 := by
        by_contra h
        exact hP (hGS P h)
      rw [hG0, Finset.sum_eq_zero fun j _ => ?_]
      rw [if_neg, Int.cast_zero, mul_zero]
      intro h
      exact hP (h ▸ (e.symm j).2)

/-- **A crepant shift over a birational base.** Over a birational base every `ℝ`-divisor `D`
becomes effective after adding an effective divisor numerically trivial over the base: by relative
Kodaira, `-∑_{P ∈ Supp D} P ∼_ℚ H + E - c f^*T₀` with `H, E ≥ 0`, so `T' = ∑ P + H + E` is
effective, `ℚ`-linearly equivalent to a pull-back, hence `≡_f 0`, and has coefficient at least one
along `Supp D`; take `T = N T'` with `N = ∑ |D_P|`. -/
private theorem exists_isNumericallyTrivialOver_isEffective_add {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : MMP.Mori.IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hfb : IsBirationalMorphism f) (D : RDivisor X) :
    ∃ T : RDivisor X, T.IsEffective ∧ MMP.Flips.IsNumericallyTrivialOver ℂ sX f T ∧
      (D + T).IsEffective := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : IsIntegral Z := hZ.toIsIntegral
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sZ) := by rw [hf]; exact hX.toIsVariety.toLocallyOfFiniteType
    exact LocallyOfFiniteType.of_comp this
  haveI : QuasiCompact f := by
    have : QuasiCompact (f ≫ sZ) := by rw [hf]; infer_instance
    exact QuasiCompact.of_comp f sZ
  set S := D.support
  set S₀ : QDivisor X := ∑ P ∈ S, Finsupp.single P (1 : ℚ)
  have hG : (-S₀).IsRelativelyBig f :=
    MMP.Mori.QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage hX hZ hf
      (MMP.Fourfold.isBirationalMorphism_toImage f hfb)
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hXQ _)
  obtain ⟨H, E, -, hHe, hEe, c, T₀, T₀', w, hT, hw, hlin⟩ :=
    MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback sX sZ hXQ f hf hG
  set TX : QDivisor X := S₀ + H + E
  have hTX : TX.QLinearlyEquivalent (c • Divisor.toQDivisor w) := by
    obtain ⟨m, hm, φ, hφ⟩ := hlin.symm
    refine ⟨m, hm, φ, ?_⟩
    rw [← hφ]
    congr 1
    simp only [TX]
    abel
  have htriv := MMP.Fourfold.isNumericallyTrivialOver_of_qLinearlyEquivalent_smul_weilDivisor sX sZ
    hX hXQ hZ hZn f hf hfb hT hw hTX
  have hS₀ : ∀ P, S₀.coeff P = if P ∈ S then 1 else 0 := fun P => by
    simp [S₀, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hTX0 : ∀ P, 0 ≤ (TX.coeff P : ℝ) := fun P => by
    have h1 := hHe P
    have h2 := hEe P
    have h3 : 0 ≤ S₀.coeff P := by rw [hS₀]; split_ifs <;> norm_num
    simp only [TX, DivisorWithCoeffs.coeff_add]
    exact_mod_cast add_nonneg (add_nonneg h3 h1) h2
  have hTX1 : ∀ P ∈ S, (1 : ℝ) ≤ (TX.coeff P : ℝ) := fun P hP => by
    have h1 := hHe P
    have h2 := hEe P
    simp only [TX, DivisorWithCoeffs.coeff_add, hS₀, if_pos hP]
    exact_mod_cast (by linarith : (1 : ℚ) ≤ 1 + H.coeff P + E.coeff P)
  set N : ℝ := ∑ P ∈ S, |D P|
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨N • QDivisor.toRDivisor TX, fun P => ?_, isNumericallyTrivialOver_smul htriv N,
    fun P => ?_⟩
  · rw [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, smul_eq_mul]
    exact mul_nonneg hN0 (hTX0 P)
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor,
      smul_eq_mul]
    by_cases hP : P ∈ S
    · have hle : |D P| ≤ N := Finset.single_le_sum (f := fun P => |D P|)
        (fun _ _ => abs_nonneg _) hP
      have h1 := hTX1 P hP
      have h2 := neg_abs_le (D P)
      rw [DivisorWithCoeffs.coeff_apply]
      nlinarith
    · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hP, zero_add]
      exact mul_nonneg hN0 (hTX0 P)

/-- **A basis of `N¹(X/Z)` and a crepant shift.** There are Cartier divisors `H_i` whose classes
form a basis of `N¹(X/Z)` and an effective `ℝ`-Cartier divisor `T ≡_Z 0` such that every
`(X, B + T + t C)`, `0 ≤ t ≤ 1`, is klt and every component of every `H_i` has coefficient at least
`δ > 0` in `B + T`. -/
private theorem exists_basis_shift (hπ : π ≫ sZ = sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π) (hXq : IsQFactorial sX)
    (hK : K.IsCanonicalDivisor sX 4) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsRealKltPair sX (B + C)) :
    ∃ (ι : Type) (_ : Fintype ι) (H : ι → Divisor X) (T : RDivisor X),
      (∀ i, (H i).IsCartier) ∧
      (∀ D : RDivisor X, IsCartierCombination D →
        ∃ u : ι → ℝ, IsNumericallyEquivalentOver ℂ sX π D (∑ i, u i • Divisor.toRDivisor (H i))) ∧
      (∀ u : ι → ℝ,
        IsNumericallyTrivialOver ℂ sX π (∑ i, u i • Divisor.toRDivisor (H i)) → u = 0) ∧
      IsNumericallyTrivialOver ℂ sX π T ∧ (∀ P, 0 ≤ T.coeff P) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsRealKltPair sX (B + T + t • C)) ∧
      ∃ δ > 0, ∀ i P, (H i).coeff P ≠ 0 → δ ≤ (B + T).coeff P := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  -- a basis of `N¹(X/Z)` among Cartier multiples of finitely many primes `S`
  obtain ⟨S, hS⟩ := exists_finset_isNumericallyEquivalentOver hπ hX hZ hZn hπp hπb hXq
  obtain ⟨N, v, hv, hvS, hvspan⟩ := exists_cartier_spanning (π := π) hXq S hS
  obtain ⟨ι, hι, a, hspan, hind⟩ := exists_basis_of_isNumericallyEquivalentOver π v hv hvspan
  -- an effective `T' ≡_Z 0` with coefficient at least one along `S`
  obtain ⟨T', hT'0, hT'triv, hT'S⟩ := exists_isNumericallyTrivialOver_isEffective_add sX sZ hX
    hXq hZ hZn π hπ hπb (-(∑ P ∈ S, Finsupp.single P (1 : ℝ)))
  have hT'1 : ∀ P ∈ S, 1 ≤ T'.coeff P := fun P hP => by
    have := hT'S P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_neg] at this
    have h1 : (∑ Q ∈ S, Finsupp.single Q (1 : ℝ) : RDivisor X).coeff P = 1 := by
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, hP]
    linarith
  -- klt for a small multiple of `T'` at both ends of the segment
  have hBC : ∀ P, 0 ≤ (B + C).coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_add]; linarith [hB P, hC P]
  have hBklt : IsRealKltPair sX B := IsRealKltPair.of_le hXq (fun P => by
    rw [DivisorWithCoeffs.coeff_add]; linarith [hC P]) hklt
  obtain ⟨t₀, ht₀, h₀⟩ := exists_isRealKltPair_add_smul sX hXqp hXq hB hT'0 hBklt
  obtain ⟨t₁, ht₁, h₁⟩ := exists_isRealKltPair_add_smul sX hXqp hXq hBC hT'0 hklt
  set t := min t₀ t₁ / 2 with ht
  have htpos : 0 < t := by positivity
  have ht₀' : t < t₀ := by linarith [min_le_left t₀ t₁]
  have ht₁' : t < t₁ := by linarith [min_le_right t₀ t₁]
  refine ⟨ι, hι, fun i => v (a i), t • T', fun i => hv _, hspan, hind,
    isNumericallyTrivialOver_smul hT'triv t, fun P => ?_, fun s hs0 hs1 => ?_,
    t, htpos, fun i P hP => ?_⟩
  · rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact mul_nonneg htpos.le (hT'0 P)
  · have heq : B + t • T' + s • C = (1 - s) • (B + t • T') + s • (B + C + t • T') := by module
    rw [heq]
    exact isRealKltPair_segment hXq (h₀ t htpos.le ht₀') (h₁ t htpos.le ht₁') hs0 hs1
  · have hPS := hvS (a i) P hP
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    nlinarith [hB P, hT'1 P hPS]

/-- A rational box around a nonnegative point: finitely many nonnegative rational vectors within
`δ` of `x` whose convex hull contains every nonnegative vector within `δ / 2` of `x`. -/
private theorem exists_rat_box {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ k, 0 ≤ x k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : Finset (ι → ℚ), (∀ v ∈ V, ∀ k, (0 : ℚ) ≤ v k ∧ |(v k : ℝ) - x k| < δ) ∧
      ∀ y : ι → ℝ, (∀ k, 0 ≤ y k ∧ |y k - x k| < δ / 2) →
        y ∈ convexHull ℝ ((fun v : ι → ℚ => fun k => (v k : ℝ)) '' (V : Set (ι → ℚ))) := by
  classical
  choose a ha using fun k => exists_rat_btwn (show x k - δ < x k - δ / 2 by linarith)
  choose b hb using fun k => exists_rat_btwn (show x k + δ / 2 < x k + δ by linarith)
  set a' : ι → ℚ := fun k => max (a k) 0
  let V : Finset (ι → ℚ) := Fintype.piFinset fun k => {a' k, b k}
  refine ⟨V, fun v hv k => ?_, fun y hy => ?_⟩
  · have hvk := Fintype.mem_piFinset.mp hv k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvk
    rcases hvk with h | h <;> rw [h]
    · refine ⟨le_max_right _ _, ?_⟩
      simp only [a', Rat.cast_max, Rat.cast_zero]
      rw [abs_lt]
      constructor
      · have := (ha k).1; have := le_max_left ((a k : ℝ)) 0; linarith
      · rcases le_total ((a k : ℝ)) 0 with h0 | h0
        · rw [max_eq_right h0]; linarith [hx k]
        · rw [max_eq_left h0]; linarith [(ha k).2]
    · refine ⟨?_, ?_⟩
      · have h1 : (0 : ℝ) < b k := by linarith [(hb k).1, hx k]
        exact_mod_cast h1.le
      · rw [abs_lt]; constructor <;> linarith [(hb k).1, (hb k).2]
  · have himage : ((fun v : ι → ℚ => fun k => (v k : ℝ)) '' (V : Set (ι → ℚ))) =
        Set.univ.pi fun k => {((a' k : ℚ) : ℝ), ((b k : ℚ) : ℝ)} := by
      ext z
      simp only [Set.mem_image, Finset.mem_coe, V, Fintype.mem_piFinset, Finset.mem_insert,
        Finset.mem_singleton, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩ k
        rcases hv k with h | h <;> simp [h]
      · intro hz
        refine ⟨fun k => if z k = (a' k : ℝ) then a' k else b k, fun k => ?_, funext fun k => ?_⟩
        · by_cases h : z k = (a' k : ℝ) <;> simp [h]
        · by_cases h : z k = (a' k : ℝ)
          · simp [h]
          · simp only [h, if_false]
            rcases hz k with h' | h'
            · exact absurd h' h
            · exact h'.symm
    rw [himage, convexHull_pi]
    intro k _
    show y k ∈ convexHull ℝ {((a' k : ℚ) : ℝ), ((b k : ℚ) : ℝ)}
    rw [convexHull_pair, segment_eq_Icc]
    · obtain ⟨hy0, hyx⟩ := hy k
      rw [abs_lt] at hyx
      constructor
      · simp only [a', Rat.cast_max, Rat.cast_zero]
        exact max_le (by linarith [(ha k).2]) hy0
      · linarith [(hb k).1]
    · simp only [a', Rat.cast_max, Rat.cast_zero]
      exact max_le (by linarith [(ha k).2, (hb k).1]) (by linarith [(hb k).1, hx k])

/-- On the support of `Θ`, the perturbation `Θ + ∑ uᵢ Dᵢ` by divisors supported there is the sum of
its coefficients along the support. -/
private theorem add_sum_smul_eq_sum_single {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Θ : RDivisor X) {ι : Type}
    [Fintype ι] (D : ι → RDivisor X) (hD0 : ∀ i W, W ∉ Θ.support → (D i).coeff W = 0)
    (u : ι → ℝ) :
    Θ + ∑ i, u i • D i = ∑ j : Θ.support, Finsupp.single j.1
      (Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1) := by
  classical
  refine Finsupp.ext fun W => ?_
  have h := MMP.Fourfold.coeff_sum_single (fun j : Θ.support => j.1)
    (fun j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1) W
  rw [DivisorWithCoeffs.coeff_apply] at h
  rw [h, Finsupp.add_apply, Finset.sum_apply']
  by_cases hW : W ∈ Θ.support
  · rw [Fintype.sum_eq_single ⟨W, hW⟩ (fun j hj => if_neg fun h' => hj (Subtype.ext h')),
      if_pos rfl]
    simp [DivisorWithCoeffs.coeff_apply]
  · rw [Finset.sum_eq_zero fun (j : Θ.support) _ => if_neg fun (h' : j.1 = W) => hW (h' ▸ j.2)]
    have h1 : Θ W = 0 := Finsupp.notMem_support_iff.mp hW
    have h2 : ∀ i, (D i) W = 0 := fun i => hD0 i W hW
    simp [h1, h2]

open Filter Topology in
/-- **A rational klt polytope around a perturbed boundary.** For an effective klt boundary `Θ`
and divisors `Dᵢ` supported where `Θ` has coefficients at least `δ > 0`, there are finitely many
effective klt `ℚ`-divisors whose convex hull contains `Θ + ∑ uᵢ Dᵢ` for all small `u`. -/
private theorem exists_finset_isKltPair_convexHull {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX)
    {Θ : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hk : IsRealKltPair sX Θ)
    {ι : Type} [Fintype ι] (D : ι → RDivisor X) {δ : ℝ} (hδ : 0 < δ)
    (hDδ : ∀ i P, (D i).coeff P ≠ 0 → δ ≤ Θ.coeff P) :
    ∃ (V : Finset (QDivisor X)) (ε : ℝ), 0 < ε ∧ (∀ E ∈ V, ∀ P, 0 ≤ E.coeff P) ∧
      (∀ E ∈ V, IsKltPair sX E) ∧ ∀ u : ι → ℝ, (∀ i, |u i| < ε) →
        Θ + ∑ i, u i • D i ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
  classical
  let s := Θ.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : (ι → ℝ) → s → ℝ := fun u j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1
  have hD0 : ∀ i W, W ∉ s → (D i).coeff W = 0 := fun i W hW => by
    by_contra h
    have := hDδ i W h
    have h0 : Θ.coeff W = 0 := Finsupp.notMem_support_iff.mp hW
    linarith
  have hrep : ∀ u, Θ + ∑ i, u i • D i = ∑ j, Finsupp.single (p j) (y u j) :=
    add_sum_smul_eq_sum_single Θ D hD0
  have hcont : Continuous y := by
    refine continuous_pi fun j => continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_apply i).mul continuous_const
  have hx0 : ∀ j, 0 < y 0 j := fun j => by
    have : Θ.coeff j.1 ≠ 0 := Finsupp.mem_support_iff.mp j.2
    simpa [y] using lt_of_le_of_ne (hΘ j.1) (Ne.symm this)
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  obtain ⟨U, hUo, hxU, hU⟩ := mem_nhdsWithin.mp hev
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo (y 0) hxU
  obtain ⟨V', hV'1, hV'2⟩ := exists_rat_box (y 0) (fun j => (hx0 j).le) hr
  -- the linear map from coordinates to divisors
  let L : (s → ℝ) →ₗ[ℝ] RDivisor X :=
    { toFun := fun z => ∑ j, Finsupp.single (p j) (z j)
      map_add' := fun a b => by
        simp only [Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, Finsupp.smul_single, Finset.smul_sum, RingHom.id_apply] }
  let F : (s → ℚ) → QDivisor X := fun v => ∑ j, Finsupp.single (p j) (v j)
  have hFL : ∀ v, QDivisor.toRDivisor (F v) = L (fun j => (v j : ℝ)) := fun v => by
    refine Finsupp.ext fun W => ?_
    change ((∑ j, Finsupp.single (p j) (v j) : QDivisor X).coeff W : ℝ) =
      (∑ j, Finsupp.single (p j) ((v j : ℝ)) : RDivisor X).coeff W
    rw [MMP.Fourfold.coeff_sum_single, MMP.Fourfold.coeff_sum_single]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hall : ∀ᶠ u in 𝓝 (0 : ι → ℝ), ∀ j, 0 < y u j ∧ |y u j - y 0 j| < r / 2 := by
    refine eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun u => y u j) 0 :=
      ((continuous_apply j).comp hcont).continuousAt
    have h1 := hc.eventually (lt_mem_nhds (hx0 j))
    have h2 := hc.eventually (Metric.ball_mem_nhds (y 0 j) (half_pos hr))
    filter_upwards [h1, h2] with u hu1 hu2
    exact ⟨hu1, by rw [← Real.dist_eq]; exact hu2⟩
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨V'.image F, ε, hε, ?_, ?_, ?_⟩
  · intro E hE P
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    simp only [F]
    rw [MMP.Fourfold.coeff_sum_single]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [(hV'1 v hv j).1]
  · intro E hE
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    have hnn : ∀ P, 0 ≤ (F v).coeff P := fun P => by
      simp only [F]
      rw [MMP.Fourfold.coeff_sum_single]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [(hV'1 v hv j).1]
    refine MMP.Fourfold.isKltPair_of_isRealKltPair hQ hnn ?_
    rw [hFL]
    refine hU ⟨hball ((dist_pi_lt_iff hr).mpr fun j => ?_), fun j => ?_⟩
    · rw [Real.dist_eq]; exact (hV'1 v hv j).2
    · show (0 : ℝ) ≤ (v j : ℝ)
      exact_mod_cast (hV'1 v hv j).1
  · intro u hu
    have hd : dist u 0 < ε := (dist_pi_lt_iff hε).mpr fun i => by
      simpa [Real.dist_eq] using hu i
    have hyu := hεh hd
    have hmem := hV'2 (y u) fun j => ⟨(hyu j).1.le, (hyu j).2⟩
    rw [hrep u]
    change L (y u) ∈ _
    have himg : QDivisor.toRDivisor '' ((V'.image F : Finset (QDivisor X)) : Set (QDivisor X)) =
        L '' ((fun v : s → ℚ => fun j => (v j : ℝ)) '' (V' : Set (s → ℚ))) := by
      rw [Finset.coe_image, Set.image_image, Set.image_image]
      exact Set.image_congr fun v _ => hFL v
    rw [himg, ← LinearMap.image_convexHull]
    exact Set.mem_image_of_mem L hmem

/-- **A rational klt polytope around the scaled segment.** For a finite family of Cartier
divisors `H_i` supported where `B + T` has coefficients at least `δ > 0`, with every
`(X, B + T + t C)`, `0 ≤ t ≤ 1`, klt, there are finitely many effective klt `ℚ`-divisors whose
convex hull contains every `B + T + t C + ∑ u_i H_i` with `0 ≤ t ≤ 1` and `|u_i| < ε₁`. -/
private theorem exists_polytope (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {T : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hT0 : ∀ P, 0 ≤ T.coeff P) (hTklt : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsRealKltPair sX (B + T + t • C))
    {ι : Type} [Fintype ι] (H : ι → Divisor X) {δ : ℝ} (hδ : 0 < δ)
    (hHδ : ∀ i P, (H i).coeff P ≠ 0 → δ ≤ (B + T).coeff P) :
    ∃ (V : Finset (QDivisor X)) (ε₁ : ℝ), 0 < ε₁ ∧ (∀ D ∈ V, ∀ P, 0 ≤ D.coeff P) ∧
      (∀ D ∈ V, IsKltPair sX D) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ u : ι → ℝ, (∀ i, |u i| < ε₁) →
        B + T + t • C + ∑ i, u i • Divisor.toRDivisor (H i) ∈
          convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
  classical
  have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  have hle : ∀ c : ℝ, 0 ≤ c → ∀ P, (B + T).coeff P ≤ (B + T + c • C).coeff P := fun c hc P => by
    rw [DivisorWithCoeffs.coeff_add (B + T), DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    nlinarith [mul_nonneg hc (hC P)]
  have hnn : ∀ c : ℝ, 0 ≤ c → ∀ P, 0 ≤ (B + T + c • C).coeff P := fun c hc P => by
    refine le_trans ?_ (hle c hc P)
    rw [DivisorWithCoeffs.coeff_add]
    linarith [hB P, hT0 P]
  have hHc : ∀ c : ℝ, 0 ≤ c → ∀ i P, (Divisor.toRDivisor (H i)).coeff P ≠ 0 →
      δ ≤ (B + T + c • C).coeff P := fun c hc i P hP =>
    (hHδ i P (fun h0 => hP (by rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero]))).trans
      (hle c hc P)
  obtain ⟨V₀, ε₀, hε₀, hV₀n, hV₀k, hV₀⟩ := exists_finset_isKltPair_convexHull sX hXqp hXq
    (hnn 0 le_rfl) (hTklt 0 le_rfl zero_le_one) (fun i => Divisor.toRDivisor (H i)) hδ
    (hHc 0 le_rfl)
  obtain ⟨V₁, ε₁, hε₁, hV₁n, hV₁k, hV₁⟩ := exists_finset_isKltPair_convexHull sX hXqp hXq
    (hnn 1 zero_le_one) (hTklt 1 zero_le_one le_rfl) (fun i => Divisor.toRDivisor (H i)) hδ
    (hHc 1 zero_le_one)
  refine ⟨V₀ ∪ V₁, min ε₀ ε₁, lt_min hε₀ hε₁,
    fun D hD => (Finset.mem_union.mp hD).elim (hV₀n D) (hV₁n D),
    fun D hD => (Finset.mem_union.mp hD).elim (hV₀k D) (hV₁k D), fun t ht0 ht1 u hu => ?_⟩
  have hsub : ∀ W : Finset (QDivisor X), W ⊆ V₀ ∪ V₁ →
      convexHull ℝ (QDivisor.toRDivisor '' (W : Set (QDivisor X))) ⊆
        convexHull ℝ (QDivisor.toRDivisor '' ((V₀ ∪ V₁ : Finset (QDivisor X)) :
          Set (QDivisor X))) := fun W hW =>
    convexHull_mono (Set.image_mono (by exact_mod_cast hW))
  have h₀ := hsub V₀ Finset.subset_union_left
    (hV₀ u fun i => (hu i).trans_le (min_le_left _ _))
  have h₁ := hsub V₁ Finset.subset_union_right
    (hV₁ u fun i => (hu i).trans_le (min_le_right _ _))
  have heq : B + T + t • C + ∑ i, u i • Divisor.toRDivisor (H i) =
      (1 - t) • (B + T + (0 : ℝ) • C + ∑ i, u i • Divisor.toRDivisor (H i)) +
        t • (B + T + (1 : ℝ) • C + ∑ i, u i • Divisor.toRDivisor (H i)) := by
    module
  rw [heq]
  exact (convex_convexHull ℝ _) h₀ h₁ (sub_nonneg.2 ht1) ht0 (by ring)

end BasisShift

/-! ### An infinite program with scaling -/

section InfiniteProgram

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {K : Divisor X} {B C : RDivisor X}
  {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)}
  [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
  {πY : ∀ i, Y i ⟶ Z} {KY : ∀ i, Divisor (Y i)} {BY CY : ∀ i, RDivisor (Y i)}
  {lam : ℕ → ℝ} {W : ℕ → Scheme.{0}} {sW : ∀ i, W i ⟶ Spec (.of ℂ)}
  {f : ∀ i, modelSeq X Y i ⟶ W i} {g : ∀ i, W i ⟶ Z} {fp : ∀ i, Y i ⟶ W i}
  {φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)} {N : ℕ∞}

/-- From `i < N` in `ℕ∞`, `i + 1 ≤ N`. -/
private theorem coe_succ_le_of_lt {i : ℕ} {N : ℕ∞} (h : (i : ℕ∞) < N) : ((i + 1 : ℕ) : ℕ∞) ≤ N := by
  rw [Nat.cast_succ]
  exact Order.add_one_le_of_lt h

/-- From `j < n ≤ N`, `j < N` in `ℕ∞`. -/
private theorem coe_lt_of_lt_of_le {j n : ℕ} {N : ℕ∞} (h : j < n) (hn : (n : ℕ∞) ≤ N) :
    (j : ℕ∞) < N :=
  lt_of_lt_of_le (by exact_mod_cast h) hn

/-- From `j ≤ n ≤ N`, `j ≤ N` in `ℕ∞`. -/
private theorem coe_le_of_le_of_le {j n : ℕ} {N : ℕ∞} (h : j ≤ n) (hn : (n : ℕ∞) ≤ N) :
    (j : ℕ∞) ≤ N :=
  le_trans (by exact_mod_cast h) hn

/-- The two morphisms of every step are birational, and the step is a modification of `f_i`
into `f_i⁺`. -/
private theorem step_isBirationalMorphism
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ) (hi
        : (i : ℕ∞) < N) :
    IsBirationalMorphism (f i) ∧ IsBirationalMorphism (fp i) ∧
      IsModificationOf (f i) (fp i) (φ i) := by
  rcases (hS i hi).2.2.2.2.2.2.1 with ⟨hb, -, hiso, hmod⟩ | hflip
  · exact ⟨hb, isBirationalMorphism_of_isIso _, hmod⟩
  · exact ⟨hflip.isSmall_source.isBirationalMorphism, hflip.isSmall.isBirationalMorphism,
      hflip.isModificationOf⟩

/-- The first scaling threshold is at most one, since `K + B + C` is nef over `Z`. -/
private theorem lam_zero_le_one
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hN : (0 : ℕ∞) < N)
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) : lam 0 ≤ 1 :=
  (hS 0 hN).1.2 ⟨zero_le_one, by
    change IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + (1 : ℝ) • C))
    rwa [one_smul]⟩

/-- Every scaling threshold is positive: at threshold zero `K_i + B_i` would be nef over `Z`,
which the `(K_i + B_i)`-negative extremal contraction `f_i` over `Z` forbids. -/
private theorem lam_pos
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ) (hi
        : (i : ℕ∞) < N) :
    0 < lam i := by
  obtain ⟨hlam, -, hfg, -, hneg, -⟩ := hS i hi
  refine lt_of_le_of_ne hlam.1.1 fun h0 => ?_
  have hnef := hlam.1.2
  rw [← h0, zero_smul, add_zero] at hnef
  exact not_isRelativelyNef_of_isNegativeExtremalContraction hneg hfg hnef

/-- The structure morphisms of a step commute: `f_i`, `g_i` and `f_i⁺` are morphisms of complex
varieties. -/
private theorem step_comp_eq
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ) (hi
        : (i : ℕ∞) < N) :
    f i ≫ sW i = modelStr sX sY i ∧ g i ≫ sZ = sW i ∧ fp i ≫ sW i = sY i := by
  obtain ⟨-, -, hfg, hfpg, hneg, -⟩ := hS i hi
  have hfs : f i ≫ sW i = modelStr sX sY i := hneg.isContraction.comp_eq
  haveI := hneg.isNormalVariety_target.1.toIsIntegral
  haveI := (step_isBirationalMorphism hS i hi).1.isDominant
  have hgs : g i ≫ sZ = sW i := by
    refine AlgebraicGeometry.ext_of_isDominant (f i) ?_
    rw [← Category.assoc, hfg, hfs]
    exact (hM i hi.le).1
  refine ⟨hfs, hgs, ?_⟩
  have hπY : πY i ≫ sZ = sY i := (hM (i + 1) (coe_succ_le_of_lt hi)).1
  rw [← hgs, ← Category.assoc, hfpg, hπY]

/-- `f_i⁺` sends the generic point of every prime divisor to that of a prime divisor: it is an
isomorphism or a small contraction. -/
private theorem step_exists_primeDivisor
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ) (hi
        : (i : ℕ∞) < N)
    (F : MMP.Mori.PrimeDivisor (Y i)) :
    ∃ Q : MMP.Mori.PrimeDivisor (W i), fp i F.genericPoint = Q.genericPoint := by
  rcases (hS i hi).2.2.2.2.2.2.1 with ⟨-, -, hiso, -⟩ | hflip
  · exact MMP.Flips.exists_primeDivisor_map_genericPoint_eq (fp i) ⊤ F (by simp)
  · exact MMP.Flips.exists_primeDivisor_map_genericPoint_eq_of_isSmall hflip.isSmall F

/-- The models of a program over a birational base are birational over it. -/
private theorem isBirationalMorphism_modelMap
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hZn : IsNormalVariety ℂ sZ) (hπb : IsBirationalMorphism π) (i : ℕ) (hi : (i : ℕ∞) ≤ N) :
    IsBirationalMorphism (modelMap π πY i) := by
  haveI := hZn.1.toIsIntegral
  induction i with
  | zero => exact hπb
  | succ j ih =>
    have hj : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_succ_self j) hi
    obtain ⟨hf, hfp, -⟩ := step_isBirationalMorphism hS j hj
    obtain ⟨-, hgs, -⟩ := step_comp_eq hM hS j hj
    haveI := (hS j hj).2.2.2.2.1.isNormalVariety_target.1.toIsIntegral
    haveI : LocallyOfFiniteType (sW j) :=
      (hS j hj).2.2.2.2.1.isNormalVariety_target.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (g j ≫ sZ) := by rw [hgs]; infer_instance
    haveI : LocallyOfFiniteType (g j) := LocallyOfFiniteType.of_comp (f := g j) (g := sZ)
        inferInstance
    have hfg := (hS j hj).2.2.1
    have hg : IsBirationalMorphism (g j) :=
      MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left (f j) (g j) hf (hfg ▸ ih hj.le)
    change IsBirationalMorphism (πY j)
    rw [← (hS j hj).2.2.2.1]
    exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfp hg

/-- The scaling thresholds are nonincreasing. -/
private theorem lam_succ_le
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ)
    (hi1 : ((i + 1 : ℕ) : ℕ∞) < N) :
    lam (i + 1) ≤ lam i := by
  have hi : (i : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_succ_self i) hi1.le
  refine (hS (i + 1) hi1).1.2 ⟨(hS i hi).1.1.1, ?_⟩
  change IsRelativelyNef ℂ (sY i) (πY i) (logCanonicalDivisor (KY i) (BY i + lam i • CY i))
  obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS i hi
  obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS i hi
  have hfpc := step_exists_primeDivisor hS i hi
  obtain ⟨hlam, hWp, hfg, hfpg, hneg, htriv, -, hBY, hCY⟩ := hS i hi
  obtain ⟨-, hXp, hXq, ⟨n, hK⟩, -⟩ := hM i hi.le
  obtain ⟨-, hYp, hYq, ⟨m, hKY⟩, -⟩ := hM (i + 1) hi1.le
  change MMP.Mori.IsProjectiveVariety ℂ (sY i) at hYp
  change IsQFactorial (sY i) at hYq
  change Divisor.IsCanonicalDivisor (sY i) m (KY i) at hKY
  have hWn : IsNormalVariety ℂ (sW i) := hneg.isNormalVariety_target
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (sW i) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (W i) := LocallyOfFiniteType.isLocallyNoetherian (sW i)
  haveI : IsProper (f i) := hneg.isContraction.isProper
  haveI : IsProper (sY i) := isProper_of_isProjectiveMorphism _ hYp.isProjective
  haveI : IsSeparated (sW i) := hWn.1.toIsSeparated
  haveI : IsProper (fp i ≫ sW i) := by rw [hfps]; infer_instance
  haveI : IsProper (fp i) := IsProper.of_comp (fp i) (sW i)
  have hnef := hlam.1.2
  rw [← hfg] at hnef
  have h1 := isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver hXq hXp hYq hYp hWp hWn
    hfs hfps hf hfp hfpc hφ (g i) htriv hnef
  rw [hfpg, transformDivisor_logCanonicalDivisor, map_add, transformDivisor_smul, ← hBY,
    ← hCY] at h1
  have hX : IsNormalVariety ℂ (modelStr sX sY i) := ⟨hXp.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety ℂ (sY i) := ⟨hYp.toIsVariety, inferInstance⟩
  have hlin := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf hfp
    hfpc hφ hK hKY
  have h2 := MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero h1
    (L₀ := MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq K KY i) - KY i)
    (linearlyEquivalent_sub_zero hlin)
  convert h2 using 1
  simp only [logCanonicalDivisor, map_sub]
  abel

/-- Canonical divisors on the models of a program, compatible along its steps:
`K'_0 = K` and `K'_{i+1} = φ_{i*} K'_i`. -/
private noncomputable def compatibleCanonical (K : Divisor X)
    (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)) : ∀ i, Divisor (modelSeq X Y i)
  | 0 => K
  | i + 1 => MMP.Mori.RationalMap.transformDivisor (φ i) (compatibleCanonical K φ i)

/-- The compatible canonical divisors are canonical divisors, linearly equivalent to the given
ones: each step is a modification over its base which contracts no divisor of the target. -/
private theorem compatibleCanonical_spec
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (i : ℕ)
    (hi : (i : ℕ∞) ≤ N) :
    Divisor.LinearlyEquivalent (compatibleCanonical K φ i) (divisorSeq K KY i) ∧
      ∃ n : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) n (compatibleCanonical K φ i) := by
  induction i with
  | zero => exact ⟨Divisor.LinearlyEquivalent.refl _, (hM 0 hi).2.2.2.1⟩
  | succ j ih =>
    have hj : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_succ_self j) hi
    obtain ⟨-, ⟨n, hn⟩⟩ := ih hj.le
    obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS j hj
    obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS j hj
    have hneg := (hS j hj).2.2.2.2.1
    have hWn : IsNormalVariety ℂ (sW j) := hneg.isNormalVariety_target
    haveI := hWn.1.toIsIntegral
    haveI := hWn.2
    haveI : LocallyOfFiniteType (sW j) := hWn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
    haveI : IsProper (f j) := hneg.isContraction.isProper
    haveI : IsSeparated (sW j) := hWn.1.toIsSeparated
    have hYp : MMP.Mori.IsProjectiveVariety ℂ (sY j) := (hM (j + 1) hi).2.1
    haveI : IsProper (sY j) := isProper_of_isProjectiveMorphism _ hYp.isProjective
    haveI : IsProper (fp j ≫ sW j) := by rw [hfps]; infer_instance
    haveI : IsProper (fp j) := IsProper.of_comp (fp j) (sW j)
    have hX : IsNormalVariety ℂ (modelStr sX sY j) := ⟨(hM j hj.le).2.1.toIsVariety, inferInstance⟩
    have hY : IsNormalVariety ℂ (sY j) := ⟨hYp.toIsVariety, inferInstance⟩
    obtain ⟨m, hm⟩ := (hM (j + 1) hi).2.2.2.1
    change Divisor.IsCanonicalDivisor (sY j) m (KY j) at hm
    have hlin := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf
      hfp (step_exists_primeDivisor hS j hj) hφ hn hm
    exact ⟨hlin, m, hm.of_linearlyEquivalent hlin⟩

/-- **The adjoints across one step.** With the compatible canonical divisors `K'_i`, the adjoint
`D_i = K'_i + B_i` is `ℝ`-Cartier, `-D_i` is `f_i`-nef, `D_{i+1}` is `f_i⁺`-nef,
`φ_{i*} D_i = D_{i+1}`, and some curve contracted by `f_i` has `D_i · Γ < 0`. -/
private theorem step_adjoint_spec
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (j : ℕ) (hj
        : (j : ℕ∞) < N) :
    IsCartierCombination
        (logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j)) ∧
      IsRelativelyNef ℂ (modelStr sX sY j) (f j)
        (-logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j)) ∧
      IsRelativelyNef ℂ (sY j) (fp j)
        (logCanonicalDivisor (compatibleCanonical K φ (j + 1)) (divisorSeq B BY (j + 1))) ∧
      MMP.Mori.RationalMap.transformDivisor (φ j)
          (logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j)) =
        logCanonicalDivisor (compatibleCanonical K φ (j + 1)) (divisorSeq B BY (j + 1)) ∧
      ∃ Γ : ProperCurve (modelStr sX sY j), Γ.IsContractedBy (f j) ∧
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor (modelSeq X Y j)) (x : ℝ),
          IsRIntersectionNumber ℂ (modelStr sX sY j)
            (logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j)) r L Γ x →
            x < 0 := by
  obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS j hj
  obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS j hj
  obtain ⟨-, -, -, -, hneg, -, hcase, hBY, -⟩ := hS j hj
  have hWn : IsNormalVariety ℂ (sW j) := hneg.isNormalVariety_target
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (sW j) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
  haveI : IsProper (f j) := hneg.isContraction.isProper
  haveI : IsSeparated (sW j) := hWn.1.toIsSeparated
  have hXp : MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY j) := (hM j hj.le).2.1
  have hYp : MMP.Mori.IsProjectiveVariety ℂ (sY j) := (hM (j + 1) (coe_succ_le_of_lt hj)).2.1
  haveI : QuasiCompact (modelStr sX sY j) := hXp.toIsVariety.toQuasiCompact
  haveI : QuasiCompact (sY j) := hYp.toIsVariety.toQuasiCompact
  haveI : IsProper (sY j) := isProper_of_isProjectiveMorphism _ hYp.isProjective
  haveI : IsProper (fp j ≫ sW j) := by rw [hfps]; infer_instance
  haveI : IsProper (fp j) := IsProper.of_comp (fp j) (sW j)
  have hX : IsNormalVariety ℂ (modelStr sX sY j) := ⟨hXp.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety ℂ (sY j) := ⟨hYp.toIsVariety, inferInstance⟩
  have hfpc := step_exists_primeDivisor hS j hj
  obtain ⟨hKK, n, hKc⟩ := compatibleCanonical_spec hM hS j hj.le
  obtain ⟨n₀, hK₀⟩ := (hM j hj.le).2.2.2.1
  obtain ⟨m, hm⟩ := (hM (j + 1) (coe_succ_le_of_lt hj)).2.2.2.1
  change Divisor.IsCanonicalDivisor (sY j) m (KY j) at hm
  -- the correction `K'_j - K_j ∼ 0`
  have hL₀ : Divisor.LinearlyEquivalent (compatibleCanonical K φ j - divisorSeq K KY j) 0 :=
    linearlyEquivalent_sub_zero hKK
  set N := logCanonicalDivisor (divisorSeq K KY j) (divisorSeq B BY j) with hNdef
  have hDN : logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j) =
      N + Divisor.toRDivisor (compatibleCanonical K φ j - divisorSeq K KY j) := by
    simp only [hNdef, logCanonicalDivisor, map_sub]
    abel
  refine ⟨isCartierCombination_of_isQFactorial (hM j hj.le).2.2.1 _, ?_, ?_, ?_, ?_⟩
  · -- `-D_j` is `f_j`-nef
    have h1 := isRelativelyNef_neg_of_isRelativelyAntiAmple (sX := modelStr sX sY j) (f j)
      hneg.isRelativelyAntiAmple hneg.isCartierCombination
    have h2 := MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero h1 hL₀
    rw [hDN, neg_add, ← sub_eq_add_neg]
    exact h2
  · -- `D_{j+1}` is `f_j⁺`-nef
    have hc : IsCartierCombination
        (logCanonicalDivisor (compatibleCanonical K φ (j + 1)) (divisorSeq B BY (j + 1))) :=
      isCartierCombination_of_isQFactorial (hM (j + 1) (coe_succ_le_of_lt hj)).2.2.1 _
    rcases hcase with ⟨-, -, hiso, -⟩ | hflip
    · have h1 := MMP.Flips.isRelativelyNef_id (sY j) hc
      rw [← IsIso.hom_inv_id (fp j)] at h1
      exact IsRelativelyNef.of_comp h1
    · have hA := isRelativelyNef_of_isRelativelyAmple (sX := sY j) (fp j)
        hflip.isRelativelyAmple_transform
      rw [transformDivisor_logCanonicalDivisor, ← hBY] at hA
      have hl1 := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf
        hfp hfpc hφ hK₀ hm
      have hl2 := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf
        hfp hfpc hφ hKc hm
      have hL₁ : Divisor.LinearlyEquivalent
          (MMP.Mori.RationalMap.transformDivisor (φ j) (divisorSeq K KY j) -
            MMP.Mori.RationalMap.transformDivisor (φ j) (compatibleCanonical K φ j)) 0 :=
        linearlyEquivalent_sub_zero (hl1.trans hl2.symm)
      have h2 := MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero hA hL₁
      convert h2 using 1
      change logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ j)
        (compatibleCanonical K φ j)) (BY j) = _
      simp only [logCanonicalDivisor, map_sub]
      abel
  · rw [transformDivisor_logCanonicalDivisor, ← hBY]
    rfl
  · obtain ⟨Γ, hΓ⟩ := exists_isContractedBy_of_relativePicardNumber_eq_one (f j)
      hneg.relativePicardNumber_eq_one
    refine ⟨Γ, hΓ, fun m r L x hx => ?_⟩
    obtain ⟨m', r', L', hL', hN'⟩ := hneg.isCartierCombination
    have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (modelStr sX sY j) Γ r' L' hL'
    have hN'' : N = ∑ i, r' i • Divisor.toRDivisor (L' i) := hN'
    rw [← hN''] at hy
    have hlt := isRIntersectionNumber_neg_of_isRelativelyAntiAmple (f j)
      hneg.isRelativelyAntiAmple Γ hΓ r' L' _ hy
    rw [hDN] at hx
    rw [isRIntersectionNumber_eq_of_linearlyEquivalent_zero Γ hL₀ hy hx]
    exact hlt

/-- **The adjoints at a level `t ≤ λ_j` across one step.** For `0 ≤ t ≤ λ_j`, with
`D^t_j = K'_j + B_j + t C_j`: `-D^t_j` is `f_j`-nef, `D^t_{j+1}` is `f_j⁺`-nef and
`φ_{j*} D^t_j = D^t_{j+1}`. Indeed `K'_j + B_j + λ_j C_j ≡ 0` over `W_j` on both sides of the
step, while `-(K'_j + B_j)` is `f_j`-nef and `K'_{j+1} + B_{j+1}` is `f_j⁺`-nef. -/
private theorem step_level_spec
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) (j : ℕ) (hj
        : (j : ℕ∞) < N) {t : ℝ}
    (ht0 : 0 ≤ t) (htl : t ≤ lam j) :
    IsRelativelyNef ℂ (modelStr sX sY j) (f j)
        (-logCanonicalDivisor (compatibleCanonical K φ j)
          (divisorSeq B BY j + t • divisorSeq C CY j)) ∧
      IsRelativelyNef ℂ (sY j) (fp j)
        (logCanonicalDivisor (compatibleCanonical K φ (j + 1))
          (divisorSeq B BY (j + 1) + t • divisorSeq C CY (j + 1))) ∧
      MMP.Mori.RationalMap.transformDivisor (φ j)
          (logCanonicalDivisor (compatibleCanonical K φ j)
            (divisorSeq B BY j + t • divisorSeq C CY j)) =
        logCanonicalDivisor (compatibleCanonical K φ (j + 1))
          (divisorSeq B BY (j + 1) + t • divisorSeq C CY (j + 1)) := by
  have hlj : 0 < lam j := lam_pos hS j hj
  obtain ⟨-, hn₁, hn₂, -, -⟩ := step_adjoint_spec hM hS j hj
  obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS j hj
  obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS j hj
  obtain ⟨-, hWp, -, -, hneg, htriv, -, hBY, hCY⟩ := hS j hj
  have hWn : IsNormalVariety ℂ (sW j) := hneg.isNormalVariety_target
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (sW j) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
  haveI : IsProper (f j) := hneg.isContraction.isProper
  haveI : IsSeparated (sW j) := hWn.1.toIsSeparated
  have hXp : MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY j) := (hM j hj.le).2.1
  have hYp : MMP.Mori.IsProjectiveVariety ℂ (sY j) := (hM (j + 1) (coe_succ_le_of_lt hj)).2.1
  haveI : QuasiCompact (modelStr sX sY j) := hXp.toIsVariety.toQuasiCompact
  haveI : QuasiCompact (sY j) := hYp.toIsVariety.toQuasiCompact
  haveI : IsProper (sY j) := isProper_of_isProjectiveMorphism _ hYp.isProjective
  haveI : IsProper (fp j ≫ sW j) := by rw [hfps]; infer_instance
  haveI : IsProper (fp j) := IsProper.of_comp (fp j) (sW j)
  have hX : IsNormalVariety ℂ (modelStr sX sY j) := ⟨hXp.toIsVariety, inferInstance⟩
  have hY : IsNormalVariety ℂ (sY j) := ⟨hYp.toIsVariety, inferInstance⟩
  have hfpc := step_exists_primeDivisor hS j hj
  obtain ⟨hKK, n, hKc⟩ := compatibleCanonical_spec hM hS j hj.le
  obtain ⟨n₀, hK₀⟩ := (hM j hj.le).2.2.2.1
  obtain ⟨m, hm⟩ := (hM (j + 1) (coe_succ_le_of_lt hj)).2.2.2.1
  change Divisor.IsCanonicalDivisor (sY j) m (KY j) at hm
  have hCj : IsCartierCombination (divisorSeq C CY j) :=
    isCartierCombination_of_isQFactorial (hM j hj.le).2.2.1 _
  have hCj1 : IsCartierCombination (divisorSeq C CY (j + 1)) :=
    isCartierCombination_of_isQFactorial (hM (j + 1) (coe_succ_le_of_lt hj)).2.2.1 _
  -- the transform at level `t`
  have htr : ∀ s : ℝ, MMP.Mori.RationalMap.transformDivisor (φ j)
      (logCanonicalDivisor (compatibleCanonical K φ j)
        (divisorSeq B BY j + s • divisorSeq C CY j)) =
      logCanonicalDivisor (compatibleCanonical K φ (j + 1))
        (divisorSeq B BY (j + 1) + s • divisorSeq C CY (j + 1)) := fun s => by
    rw [transformDivisor_logCanonicalDivisor, map_add, transformDivisor_smul, ← hBY, ← hCY]
    rfl
  refine ⟨?_, ?_, htr t⟩
  · -- `K'_j + B_j + λ_j C_j ≡ 0` over `W_j`
    have hL₀ : Divisor.LinearlyEquivalent (divisorSeq K KY j - compatibleCanonical K φ j) 0 :=
      linearlyEquivalent_sub_zero hKK.symm
    have hN := MMP.Flips.IsNumericallyTrivialOver.sub_of_linearlyEquivalent_zero htriv hL₀
    have hN' := isNumericallyTrivialOver_neg hN
    have e₁ : -logCanonicalDivisor (compatibleCanonical K φ j)
        (divisorSeq B BY j + t • divisorSeq C CY j) =
        -logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j) +
          t • -divisorSeq C CY j := by
      simp only [logCanonicalDivisor, smul_neg]; abel
    have e₂ : -(logCanonicalDivisor (divisorSeq K KY j)
        (divisorSeq B BY j + lam j • divisorSeq C CY j) -
          Divisor.toRDivisor (divisorSeq K KY j - compatibleCanonical K φ j)) =
        -logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j) +
          lam j • -divisorSeq C CY j := by
      simp only [logCanonicalDivisor, map_sub, smul_neg]; abel
    rw [e₂] at hN'
    rw [e₁]
    exact isRelativelyNef_add_smul_of_isNumericallyTrivialOver hn₁
      (by simpa using isCartierCombination_smul hCj (-1)) hlj ht0 htl hN'
  · -- transport of `K_j + B_j + λ_j C_j ≡ 0` across the step
    have hφE : ∀ F : MMP.Mori.PrimeDivisor (Y j),
        ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ j) F := fun F hF => by
      obtain ⟨R, hR⟩ := exists_transformPrimeDivisor_eq_some_of_isModificationOf hX hY hWn hfs
        hfps hf hfp hfpc hφ F
      exact hF R hR
    have hNY := (MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq
      (modelStr sX sY j) (sY j) (sW j) (hM j hj.le).2.2.1 hXp (hM (j + 1) (coe_succ_le_of_lt
          hj)).2.2.1 hYp hWp (f j) (fp j)
      hfs hfps hφ.1 hφ.2 hφE htriv).1
    rw [transformDivisor_logCanonicalDivisor, map_add, transformDivisor_smul, ← hBY, ← hCY] at hNY
    have hl1 := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf
      hfp hfpc hφ hK₀ hm
    have hl2 := linearlyEquivalent_transformDivisor_of_isCanonicalDivisor hX hY hWn hfs hfps hf
      hfp hfpc hφ hKc hm
    have hL₁ : Divisor.LinearlyEquivalent
        (MMP.Mori.RationalMap.transformDivisor (φ j) (divisorSeq K KY j) -
          MMP.Mori.RationalMap.transformDivisor (φ j) (compatibleCanonical K φ j)) 0 :=
      linearlyEquivalent_sub_zero (hl1.trans hl2.symm)
    have hN := MMP.Flips.IsNumericallyTrivialOver.sub_of_linearlyEquivalent_zero hNY hL₁
    have e₂ : logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ j) (divisorSeq K KY j))
        (BY j + lam j • CY j) - Divisor.toRDivisor
          (MMP.Mori.RationalMap.transformDivisor (φ j) (divisorSeq K KY j) -
            MMP.Mori.RationalMap.transformDivisor (φ j) (compatibleCanonical K φ j)) =
        logCanonicalDivisor (compatibleCanonical K φ (j + 1)) (divisorSeq B BY (j + 1)) +
          lam j • divisorSeq C CY (j + 1) := by
      change _ = logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ j)
        (compatibleCanonical K φ j)) (BY j) + lam j • CY j
      simp only [logCanonicalDivisor, map_sub]; abel
    rw [e₂] at hN
    have e₁ : logCanonicalDivisor (compatibleCanonical K φ (j + 1))
        (divisorSeq B BY (j + 1) + t • divisorSeq C CY (j + 1)) =
        logCanonicalDivisor (compatibleCanonical K φ (j + 1)) (divisorSeq B BY (j + 1)) +
          t • divisorSeq C CY (j + 1) := by
      simp only [logCanonicalDivisor]; abel
    have h := isRelativelyNef_add_smul_of_isNumericallyTrivialOver hn₂ hCj1 hlj ht0 htl hN
    convert h using 2
    exact e₁

/-- The morphisms of the models to the base are proper. -/
private theorem isProper_modelMap
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i) (hZ :
        MMP.Mori.IsProjectiveVariety ℂ sZ)
    (i : ℕ) (hi : (i : ℕ∞) ≤ N) : IsProper (modelMap π πY i) := by
  haveI : IsProper (modelStr sX sY i) :=
    isProper_of_isProjectiveMorphism _ (hM i hi).2.1.isProjective
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsProper (modelMap π πY i ≫ sZ) := by rw [(hM i hi).1]; infer_instance
  exact IsProper.of_comp _ sZ

/-- The base `g_i : W_i ⟶ Z` of a step is proper and birational. -/
private theorem step_g_spec
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπb : IsBirationalMorphism π) (j : ℕ) (hj : (j : ℕ∞) < N) :
    IsProper (g j) ∧ IsBirationalMorphism (g j) := by
  haveI := hZn.1.toIsIntegral
  obtain ⟨hf, -, -⟩ := step_isBirationalMorphism hS j hj
  obtain ⟨-, hgs, -⟩ := step_comp_eq hM hS j hj
  have hWn := (hS j hj).2.2.2.2.1.isNormalVariety_target
  haveI := hWn.1.toIsIntegral
  haveI : LocallyOfFiniteType (sW j) := hWn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g j ≫ sZ) := by rw [hgs]; infer_instance
  haveI : LocallyOfFiniteType (g j) := LocallyOfFiniteType.of_comp (f := g j) (g := sZ)
      inferInstance
  haveI : IsProper (sW j) := isProper_of_isProjectiveMorphism _ (hS j hj).2.1.isProjective
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsProper (g j ≫ sZ) := by rw [hgs]; infer_instance
  refine ⟨IsProper.of_comp _ sZ, ?_⟩
  exact MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left (f j) (g j) hf
    ((hS j hj).2.2.1 ▸ isBirationalMorphism_modelMap hM hS hZn hπb j hj.le)

/-- **A common model of the first `n + 1` models.** There is a smooth projective model
`w : W ⟶ Z` with projective birational morphisms `q_j : W ⟶ X_j` over `Z` for `j ≤ n`, such that
`q_j ≫ f_j = q_{j+1} ≫ f_j⁺`, the push-forwards satisfy `q_{j+1*} = φ_{j*} ∘ q_{j*}`, and every
prime divisor of `W` mapping onto a prime divisor of `X_n` maps onto a prime divisor of each
`X_j`. -/
private theorem exists_chainModel
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπb : IsBirationalMorphism π) (n : ℕ) (hn : (n : ℕ∞) ≤ N) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (w : W ⟶ Z) (q : ∀ j, j ≤ n → (W ⟶ modelSeq X Y j)),
      IsNormalVariety ℂ (w ≫ sZ) ∧ IsSmoothScheme (w ≫ sZ) ∧ IsBirationalMorphism w ∧
      (∀ j (hj : j ≤ n), q j hj ≫ modelMap π πY j = w ∧ IsProjectiveMorphism (q j hj) ∧
        IsBirationalMorphism (q j hj)) ∧
      (∀ j (hj : j + 1 ≤ n), q j (Nat.le_of_succ_le hj) ≫ f j = q (j + 1) hj ≫ fp j) ∧
      (∀ j (hj : j + 1 ≤ n) {R : Type} [AddCommMonoid R] (H : DivisorWithCoeffs R W),
        MMP.Mori.RationalMap.transformDivisor (q (j + 1) hj).toRationalMap H =
          MMP.Mori.RationalMap.transformDivisor (φ j)
            (MMP.Mori.RationalMap.transformDivisor (q j (Nat.le_of_succ_le hj)).toRationalMap H)) ∧
      (∀ (P : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor (modelSeq X Y n)),
        q n le_rfl P.genericPoint = F.genericPoint → ∀ j (hj : j ≤ n),
          ∃ F' : MMP.Mori.PrimeDivisor (modelSeq X Y j), q j hj P.genericPoint = F'.genericPoint)
              := by
  haveI := hZn.1
  haveI := hZn.2
  haveI := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  have hjN : ∀ j : Fin (n + 1), (j.val : ℕ∞) ≤ N :=
    fun j => coe_le_of_le_of_le (Nat.lt_succ_iff.mp j.2) hn
  haveI hprop : ∀ j : Fin (n + 1), IsProper (modelMap π πY j.val) :=
    fun j => isProper_modelMap hM hZ j.val (hjN j)
  have hnv : ∀ j : ℕ, j ≤ n → IsNormalVariety ℂ (modelStr sX sY j) :=
    fun j hj => ⟨(hM j (coe_le_of_le_of_le hj hn)).2.1.toIsVariety, inferInstance⟩
  obtain ⟨Wm, w, hWn, hwb, q, hsm, -, hq, -, -⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_smooth_projective_model sZ
      (fun j : Fin (n + 1) => modelMap π πY j.val)
      (fun j => isBirationalMorphism_modelMap hM hS hZn hπb j.val (hjN j))
      (fun j => by rw [(hM j.val (hjN j)).1]; exact hnv j.val (Nat.lt_succ_iff.mp j.2)) (κ :=
          Empty) Empty.elim
      (fun j => j.elim)
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Wm := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace Wm := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI := hwb.isDominant
  set qq : ∀ j : ℕ, j ≤ n → (Wm ⟶ modelSeq X Y j) :=
    fun j hj => q ⟨j, Nat.lt_succ_of_le hj⟩ with hqqdef
  have hqq : ∀ j (hj : j ≤ n), qq j hj ≫ modelMap π πY j = w :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).1
  have hqqs : ∀ j (hj : j ≤ n), qq j hj ≫ modelStr sX sY j = w ≫ sZ := fun j hj => by
    rw [← (hM j (coe_le_of_le_of_le hj hn)).1, ← Category.assoc, hqq j hj]
  have hqqp : ∀ j (hj : j ≤ n), IsProjectiveMorphism (qq j hj) :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).2.1
  have hqqb : ∀ j (hj : j ≤ n), IsBirationalMorphism (qq j hj) :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).2.2
  have hqqP : ∀ j (hj : j ≤ n), IsProper (qq j hj) :=
    fun j hj => isProper_of_isProjectiveMorphism _ (hqqp j hj)
  have hWj : ∀ j (hj : j ≤ n), IsNormalVariety ℂ (qq j hj ≫ modelStr sX sY j) :=
    fun j hj => by rw [hqqs j hj]; exact hWn
  have hcomm : ∀ j (hj : j + 1 ≤ n),
      qq j (Nat.le_of_succ_le hj) ≫ f j = qq (j + 1) hj ≫ fp j := by
    intro j hj
    have hjN' : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_of_succ_le hj) hn
    obtain ⟨hgP, hgb⟩ := step_g_spec hM hS hZ hZn hπb j hjN'
    haveI := hgP
    haveI := (hS j hjN').2.2.2.2.1.isNormalVariety_target.1.toIsIntegral
    haveI : IsDominant ((qq j (Nat.le_of_succ_le hj) ≫ f j) ≫ g j) := by
      rw [Category.assoc, (hS j hjN').2.2.1, hqq j (Nat.le_of_succ_le hj)]; infer_instance
    refine MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hgb ?_
    rw [Category.assoc, (hS j hjN').2.2.1, hqq j (Nat.le_of_succ_le hj)]
    calc w = (show Wm ⟶ Y j from qq (j + 1) hj) ≫ (fp j ≫ g j) := by
          rw [(hS j hjN').2.2.2.1]; exact (hqq (j + 1) hj).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hstepdata : ∀ j, j + 1 ≤ n →
      IsNormalVariety ℂ (sW j) ∧ IsProper (f j) ∧ IsProper (fp j) := by
    intro j hj
    have hjN' : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_of_succ_le hj) hn
    obtain ⟨-, -, hfps⟩ := step_comp_eq hM hS j hjN'
    have hneg := (hS j hjN').2.2.2.2.1
    have hWnj : IsNormalVariety ℂ (sW j) := hneg.isNormalVariety_target
    haveI : IsSeparated (sW j) := hWnj.1.toIsSeparated
    haveI : IsProper (sY j) := isProper_of_isProjectiveMorphism _
      (hM (j + 1) (coe_succ_le_of_lt hjN')).2.1.isProjective
    haveI : IsProper (fp j ≫ sW j) := by rw [hfps]; infer_instance
    exact ⟨hWnj, hneg.isContraction.isProper, IsProper.of_comp (fp j) (sW j)⟩
  have hpush : ∀ j (hj : j + 1 ≤ n) {R : Type} [AddCommMonoid R] (H : DivisorWithCoeffs R Wm),
      MMP.Mori.RationalMap.transformDivisor (qq (j + 1) hj).toRationalMap H =
        MMP.Mori.RationalMap.transformDivisor (φ j)
          (MMP.Mori.RationalMap.transformDivisor (qq j (Nat.le_of_succ_le hj)).toRationalMap H) :=
              by
    intro j hj R _ H
    have hjN' : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_of_succ_le hj) hn
    obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS j hjN'
    obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS j hjN'
    obtain ⟨hWnj, hfP, hfpP⟩ := hstepdata j hj
    haveI := hWnj.1.toIsIntegral
    haveI := hWnj.2
    haveI : LocallyOfFiniteType (sW j) := hWnj.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
    haveI := hfP
    haveI := hfpP
    haveI := hqqP j (Nat.le_of_succ_le hj)
    haveI : IsProper (show Wm ⟶ Y j from qq (j + 1) hj) := hqqP (j + 1) hj
    exact transformDivisor_eq_transformDivisor_of_isModificationOf (hnv j (Nat.le_of_succ_le hj))
      (show IsNormalVariety ℂ (sY j) from hnv (j + 1) hj) hWnj
      hfs hfps hf hfp (step_exists_primeDivisor hS j hjN') hφ (hWj j (Nat.le_of_succ_le hj))
      (hqqb j (Nat.le_of_succ_le hj)) (hqqb (j + 1) hj) (hcomm j hj) H
  -- prime divisors of `W` over prime divisors of `X_n` lie over prime divisors of every `X_j`
  haveI : IsSeparated (w ≫ sZ) := hWn.1.toIsSeparated
  have hdown : ∀ (P : MMP.Mori.PrimeDivisor Wm) (F : MMP.Mori.PrimeDivisor (modelSeq X Y n)),
      qq n le_rfl P.genericPoint = F.genericPoint → ∀ j (hj : j ≤ n),
        ∃ F' : MMP.Mori.PrimeDivisor (modelSeq X Y j), qq j hj P.genericPoint = F'.genericPoint :=
            by
    intro P F hPF j hj
    refine Nat.decreasingInduction
      (motive := fun j hj => ∃ F' : MMP.Mori.PrimeDivisor (modelSeq X Y j),
        qq j hj P.genericPoint = F'.genericPoint) (fun j hjn ih => ?_) ⟨F, hPF⟩ hj
    have hjn : j + 1 ≤ n := hjn
    obtain ⟨F₂, hF₂⟩ := ih
    have hjN' : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_of_succ_le hjn) hn
    obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hS j hjN'
    obtain ⟨hfs, -, hfps⟩ := step_comp_eq hM hS j hjN'
    obtain ⟨hWnj, hfP, hfpP⟩ := hstepdata j hjn
    haveI := hWnj.1.toIsIntegral
    haveI := hWnj.2
    haveI : LocallyOfFiniteType (sW j) := hWnj.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
    haveI := hfP
    haveI := hfpP
    haveI := hqqP j (Nat.le_of_succ_le hjn)
    haveI : IsProper (show Wm ⟶ Y j from qq (j + 1) hjn) := hqqP (j + 1) hjn
    exact exists_primeDivisor_apply_eq_of_isModificationOf (hnv j (Nat.le_of_succ_le hjn))
      (show IsNormalVariety ℂ (sY j) from hnv (j + 1) hjn) hWnj hfs hfps hf hfp
      (step_exists_primeDivisor hS j hjN') hφ (hWj j (Nat.le_of_succ_le hjn))
      (hqqb j (Nat.le_of_succ_le hjn)) (hqqb (j + 1) hjn) (hcomm j hjn) P F₂ hF₂
  exact ⟨Wm, inferInstance, inferInstance, inferInstance, inferInstance, w, qq, hWn, hsm, hwb,
    fun j hj => ⟨hqq j hj, hqqp j hj, hqqb j hj⟩, hcomm, hpush, hdown⟩

/-- The thresholds are antitone. -/
private theorem lam_le_of_le
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i) {j n : ℕ}
    (h : j ≤ n) (hn : (n : ℕ∞) < N) : lam n ≤ lam j := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hjm ih =>
    exact (lam_succ_le hM hS m hn).trans (ih (coe_lt_of_lt_of_le (Nat.lt_succ_self m) hn.le))

/-- The composites `ψ_i : X ⤏ X_i` of the steps are rational maps over `Z`. -/
private theorem composite_isOver
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hZn : IsNormalVariety ℂ sZ) {ψ : ∀ i, X.RationalMap (modelSeq X Y i)}
    (hψ0 : ψ 0 = Scheme.RationalMap.id X)
    (hψ : ∀ i, ∃ (a : X.PartialIso (modelSeq X Y i)) (b : (modelSeq X Y i).PartialIso (Y i)),
      a.toRationalMap = ψ i ∧ b.toRationalMap = φ i ∧ (a.trans b).toRationalMap = ψ (i + 1))
    (i : ℕ) (hi : (i : ℕ∞) ≤ N) : MMP.Flips.RationalMap.IsOver π (modelMap π πY i) (ψ i) := by
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI := isSeparated_terminal_of sZ
  induction i with
  | zero =>
    exact (congrArg (fun r : X.RationalMap X => r.compHom π) hψ0).trans
      (Scheme.RationalMap.id_compHom π)
  | succ i ih =>
    have hi' : (i : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_succ_self i) hi
    obtain ⟨a, b, ha, hb, hab⟩ := hψ i
    have ha' : a.IsOver π (modelMap π πY i) := isOver_of_isOver_toRationalMap (ha ▸ ih hi'.le)
    have hWn := (hS i hi').2.2.2.2.1.isNormalVariety_target
    haveI : IsSeparated (sW i) := hWn.1.toIsSeparated
    haveI := isSeparated_terminal_of (sW i)
    have hb₁ : b.IsOver (f i) (fp i) :=
      isOver_of_isOver_toRationalMap (hb ▸ (step_isBirationalMorphism hS i hi').2.2.2)
    have hb' : b.IsOver (modelMap π πY i) (πY i) := by
      have e : b.iso.hom ≫ b.target.ι ≫ (fp i ≫ g i) = b.source.ι ≫ (f i ≫ g i) := by
        rw [← Category.assoc, ← Category.assoc, Category.assoc b.iso.hom, hb₁,
          Category.assoc]
      rw [(hS i hi').2.2.2.1, (hS i hi').2.2.1] at e
      exact e
    rw [← hab]
    exact isOver_toRationalMap_of_isOver (ha'.trans hb')

/-- **The models are nef weak models of the source at their own level.** Let `T` be an
`ℝ`-Cartier divisor numerically trivial over `Z`. The composite `ψ_n : X ⤏ X_n` extracts no
divisor, transforms `K`, `B`, `C` to `K'_n`, `B_n`, `C_n`, and is a nef weak model over `Z` of
`(X, B + T + λ_n C)`: every earlier step is negative or crepant for this adjoint, since
`λ_n ≤ λ_j`, and on one common model the pulled-back adjoints decrease along the program. -/
private theorem isNefWeakModel_composite
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hπ : π ≫ sZ = sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπb : IsBirationalMorphism π) (hXq : IsQFactorial sX) (hK : K.IsCanonicalDivisor sX 4)
    {ψ : ∀ i, X.RationalMap (modelSeq X Y i)} (hψ0 : ψ 0 = Scheme.RationalMap.id X)
    (hψ : ∀ i, ∃ (a : X.PartialIso (modelSeq X Y i)) (b : (modelSeq X Y i).PartialIso (Y i)),
      a.toRationalMap = ψ i ∧ b.toRationalMap = φ i ∧ (a.trans b).toRationalMap = ψ (i + 1))
    {T : RDivisor X} (hT : MMP.Flips.IsNumericallyTrivialOver ℂ sX π T) (n : ℕ)
    (hn : (n : ℕ∞) ≤ N) {t : ℝ} (ht0 : 0 ≤ t) (htl : ∀ j < n, t ≤ lam j)
    (htnef : IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
      (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n + t • divisorSeq C CY n))) :
    (∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ψ n) F) ∧
      MMP.Mori.RationalMap.transformDivisor (ψ n) K = compatibleCanonical K φ n ∧
      MMP.Mori.RationalMap.transformDivisor (ψ n) B = divisorSeq B BY n ∧
      MMP.Mori.RationalMap.transformDivisor (ψ n) C = divisorSeq C CY n ∧
      IsNefWeakModel sX (modelStr sX sY n) sZ π (modelMap π πY n) K (B + T + t • C) (ψ n) := by
  classical
  haveI := hZn.1.toIsIntegral
  haveI := hZn.2
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI := isSeparated_terminal_of sZ
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hnv : ∀ j : ℕ, j ≤ n → IsNormalVariety ℂ (modelStr sX sY j) :=
    fun j hj => ⟨(hM j (coe_le_of_le_of_le hj hn)).2.1.toIsVariety, inferInstance⟩
  have hXn : IsNormalVariety ℂ sX := hnv 0 (Nat.zero_le n)
  obtain ⟨Wm, iW, lW, nW, cW, w, q, hWn, hsm, hwb, hq, hcomm, hpush, hdown⟩ :=
    exists_chainModel hM hS hZ hZn hπb n hn
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  have hqs : ∀ j (hj : j ≤ n), q j hj ≫ modelStr sX sY j = w ≫ sZ := fun j hj => by
    rw [← (hM j (coe_le_of_le_of_le hj hn)).1, ← Category.assoc, (hq j hj).1]
  have hqP : ∀ j (hj : j ≤ n), IsProper (q j hj) :=
    fun j hj => isProper_of_isProjectiveMorphism _ (hq j hj).2.1
  have hWj : ∀ j (hj : j ≤ n), IsNormalVariety ℂ (q j hj ≫ modelStr sX sY j) :=
    fun j hj => by rw [hqs j hj]; exact hWn
  set q₀ : Wm ⟶ X := q 0 (Nat.zero_le n) with hq₀def
  set qn : Wm ⟶ modelSeq X Y n := q n le_rfl with hqndef
  have hq₀b : IsBirationalMorphism q₀ := (hq 0 _).2.2
  have hqnb : IsBirationalMorphism qn := (hq n le_rfl).2.2
  haveI : IsProper q₀ := hqP 0 _
  haveI : IsProper qn := hqP n le_rfl
  haveI := hq₀b.isDominant
  haveI := hqnb.isDominant
  haveI := hπb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := isProper_modelMap hM hZ n hn
  -- `ψ_n = q_n ∘ q₀⁻¹`
  set h := hq₀b.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse q₀.toRationalMap h := hq₀b.isInverse_inverse
  have hψn : h.compHom qn = ψ n :=
    compHom_eq_of_isInverse_of_isOver (q₁ := q₀) (π₁ := π)
      (isBirationalMorphism_modelMap hM hS hZn hπb n hn)
      ((hq 0 (Nat.zero_le n)).1.trans (hq n le_rfl).1.symm) hinv (composite_isOver hM hS hZn hψ0 hψ n hn)
  have hYn := hnv n le_rfl
  haveI := hYn.1.toIsSeparated
  haveI := isSeparated_terminal_of (modelStr sX sY n)
  -- `ψ_n` extracts no divisor
  have hE : ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y n),
      ∃ R : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor (ψ n) R = some F :=
          by
    intro F
    obtain ⟨FW, hFW, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hYn (hWj n le_rfl) hqnb F
    obtain ⟨R, hR⟩ := hdown FW F hFW 0 (Nat.zero_le n)
    exact ⟨R, (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse q₀ hq₀b hinv qn hψn R
      FW hR F).mpr hFW⟩
  have hψE : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ψ n) F := fun F hF => by
    obtain ⟨R, hR⟩ := hE F
    exact hF R hR
  have hTW : ∀ {R : Type} [AddCommMonoid R] (H : DivisorWithCoeffs R Wm),
      MMP.Mori.RationalMap.transformDivisor (ψ n)
          (MMP.Mori.RationalMap.transformDivisor q₀.toRationalMap H) =
        MMP.Mori.RationalMap.transformDivisor qn.toRationalMap H := fun H =>
    transformDivisor_transformDivisor_of_isInverse hXn hYn (hWj 0 (Nat.zero_le n))
      ((hqs 0 _).trans (hqs n le_rfl).symm) hq₀b hqnb hinv hψn hE H
  -- push-forwards along the chain
  have hchain : ∀ {R : Type} [AddCommMonoid R] (H : DivisorWithCoeffs R Wm)
      (Dseq : ∀ j, DivisorWithCoeffs R (modelSeq X Y j)),
      MMP.Mori.RationalMap.transformDivisor q₀.toRationalMap H = Dseq 0 →
      (∀ j, j < n → Dseq (j + 1) = MMP.Mori.RationalMap.transformDivisor (φ j) (Dseq j)) →
      ∀ j (hj : j ≤ n), MMP.Mori.RationalMap.transformDivisor (q j hj).toRationalMap H = Dseq j :=
          by
    intro R _ H Dseq h0 hstep j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      rw [hpush j hj H, ih (Nat.le_of_succ_le hj), hstep j hj]
  -- lifts of `K`, `B`, `C` to `W`
  have hdW : topologicalKrullDim Wm = (4 : ℕ) := by
    haveI := hXn.1
    haveI : MMP.Mori.IsVariety ℂ (q₀ ≫ sX) := (hWj 0 (Nat.zero_le n)).1
    haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (q₀ ≫ sX)
      hq₀b).symm.trans hK.1
  haveI : MMP.Mori.IsVariety ℂ (q₀ ≫ sX) := (hWj 0 (Nat.zero_le n)).1
  have hsm₀ : IsSmoothScheme (q₀ ≫ sX) := by
    have e : q₀ ≫ sX = w ≫ sZ := hqs 0 (Nat.zero_le n)
    rw [e]; exact hsm
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (q₀ ≫ sX) hsm₀ hdW
  haveI : LocallyOfFiniteType (q₀ ≫ sX) := (hWj 0 (Nat.zero_le n)).1.toLocallyOfFiniteType
  obtain ⟨KW, -, hKW⟩ := MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn
    (hWj 0 (Nat.zero_le n)) hq₀b hK hK₀
  obtain ⟨BW, hBW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hXq B)
  obtain ⟨CW, hCW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hXq C)
  have hBW₀ := transformDivisor_of_isRCartierPullback hXn (hWj 0 (Nat.zero_le n)) hq₀b hBW
  have hCW₀ := transformDivisor_of_isRCartierPullback hXn (hWj 0 (Nat.zero_le n)) hq₀b hCW
  have hKn : MMP.Mori.RationalMap.transformDivisor (ψ n) K = compatibleCanonical K φ n :=
    calc MMP.Mori.RationalMap.transformDivisor (ψ n) K
        = MMP.Mori.RationalMap.transformDivisor (ψ n)
            (MMP.Mori.RationalMap.transformDivisor q₀.toRationalMap KW) := by rw [hKW]
      _ = MMP.Mori.RationalMap.transformDivisor qn.toRationalMap KW := hTW KW
      _ = compatibleCanonical K φ n :=
          hchain KW (compatibleCanonical K φ) hKW (fun j _ => rfl) n le_rfl
  have hBn : MMP.Mori.RationalMap.transformDivisor (ψ n) B = divisorSeq B BY n :=
    calc MMP.Mori.RationalMap.transformDivisor (ψ n) B
        = MMP.Mori.RationalMap.transformDivisor (ψ n)
            (MMP.Mori.RationalMap.transformDivisor q₀.toRationalMap BW) := by rw [hBW₀]
      _ = MMP.Mori.RationalMap.transformDivisor qn.toRationalMap BW := hTW BW
      _ = divisorSeq B BY n :=
          hchain BW (divisorSeq B BY) hBW₀ (fun j hj => (hS j (coe_lt_of_lt_of_le hj
              hn)).2.2.2.2.2.2.2.1) n le_rfl
  have hCn : MMP.Mori.RationalMap.transformDivisor (ψ n) C = divisorSeq C CY n :=
    calc MMP.Mori.RationalMap.transformDivisor (ψ n) C
        = MMP.Mori.RationalMap.transformDivisor (ψ n)
            (MMP.Mori.RationalMap.transformDivisor q₀.toRationalMap CW) := by rw [hCW₀]
      _ = MMP.Mori.RationalMap.transformDivisor qn.toRationalMap CW := hTW CW
      _ = divisorSeq C CY n :=
          hchain CW (divisorSeq C CY) hCW₀ (fun j hj => (hS j (coe_lt_of_lt_of_le hj
              hn)).2.2.2.2.2.2.2.2) n le_rfl
  refine ⟨hψE, hKn, hBn, hCn, ?_⟩
  -- the level-`λ_n` adjoints along the program decrease on `W`
  set D : ∀ j, RDivisor (modelSeq X Y j) := fun j =>
    logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j + t • divisorSeq C CY j)
    with hDdef
  have hGex : ∀ j (hj : j ≤ n), ∃ G : RDivisor Wm, MMP.Flips.IsRCartierPullback (q j hj) (D j) G :=
    fun j hj => by
      haveI := (hq j hj).2.2.isDominant
      exact (MMP.Flips.existsUnique_isRCartierPullback (q j hj)
        (isCartierCombination_of_isQFactorial (hM j (coe_le_of_le_of_le hj hn)).2.2.1 _)).exists
  choose G hG using hGex
  have hqD : ∀ j (hj : j ≤ n),
      MMP.Mori.RationalMap.transformDivisor (q j hj).toRationalMap (G j hj) = D j := fun j hj =>
    haveI := hqP j hj
    transformDivisor_of_isRCartierPullback (hnv j hj) (hWj j hj) (hq j hj).2.2 (hG j hj)
  have hstep0 : ∀ j (hj : j + 1 ≤ n),
      MMP.Mori.RationalMap.transformDivisor (q (j + 1) hj).toRationalMap
        (G j (Nat.le_of_succ_le hj) - G (j + 1) hj) = 0 := by
    intro j hj
    rw [map_sub, hpush j hj, hqD j _, (step_level_spec hM hS j
      (coe_lt_of_lt_of_le (Nat.lt_of_succ_le hj) hn) ht0 (htl j (by omega))).2.2,
      hqD (j + 1) hj, sub_self]
  have hstep : ∀ j (hj : j + 1 ≤ n) P,
      0 ≤ (G j (Nat.le_of_succ_le hj) - G (j + 1) hj).coeff P := by
    intro j hj
    have hjN' : (j : ℕ∞) < N := coe_lt_of_lt_of_le (Nat.lt_of_succ_le hj) hn
    obtain ⟨hn₁, hn₂, htr⟩ := step_level_spec hM hS j hjN' ht0 (htl j (by omega))
    have hMj := hM j hjN'.le
    have hMj1 := hM (j + 1) (coe_succ_le_of_lt hjN')
    haveI : QuasiCompact (modelStr sX sY j) := hMj.2.1.toIsVariety.toQuasiCompact
    haveI : QuasiCompact (modelStr sX sY (j + 1)) := hMj1.2.1.toIsVariety.toQuasiCompact
    haveI : IsSeparated (modelStr sX sY j) := hMj.2.1.toIsVariety.toIsSeparated
    haveI : IsSeparated (modelStr sX sY (j + 1)) := hMj1.2.1.toIsVariety.toIsSeparated
    haveI : LocallyOfFiniteType (modelStr sX sY j) := hMj.2.1.toIsVariety.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (modelStr sX sY (j + 1)) :=
      hMj1.2.1.toIsVariety.toLocallyOfFiniteType
    haveI := hqP j (Nat.le_of_succ_le hj)
    haveI := hqP (j + 1) hj
    exact nonneg_sub_of_isRCartierPullback_of_isRelativelyNef (hnv (j + 1) hj) hWn
      (hqs j (Nat.le_of_succ_le hj)) (hqs (j + 1) hj) (hq (j + 1) hj).2.1 (hq (j + 1) hj).2.2
      (hcomm j hj) (hG j (Nat.le_of_succ_le hj)) (hG (j + 1) hj) hn₁ hn₂
      (by rw [hpush j hj, hqD j (Nat.le_of_succ_le hj), htr])
  have hmono : ∀ m (hm : m ≤ n) P, 0 ≤ (G 0 (Nat.zero_le n) - G m hm).coeff P := by
    intro m
    induction m with
    | zero => intro hm P; simp
    | succ m ih =>
      intro hm P
      have h1 := ih (Nat.le_of_succ_le hm) P
      have h2 := hstep m hm P
      simp only [DivisorWithCoeffs.coeff_sub] at h1 h2 ⊢
      linarith
  have hexc : ∀ P : MMP.Mori.PrimeDivisor Wm,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY n) qn P →
        (G 0 (Nat.zero_le n) - G n le_rfl).coeff P = 0 := by
    intro P hP
    obtain ⟨F, hF, -, -⟩ :=
        MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
      hYn qn (hWj n le_rfl) hqnb P hP
    have hzero : ∀ j (hj : j + 1 ≤ n),
        (G j (Nat.le_of_succ_le hj) - G (j + 1) hj).coeff P = 0 := by
      intro j hj
      obtain ⟨F', hF'⟩ := hdown P F hF (j + 1) hj
      haveI := hqP (j + 1) hj
      obtain ⟨E, hE, -, hEc⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} (hnv (j + 1) hj)
          (hWj (j + 1) hj) (hq (j + 1) hj).2.2 F'
      have := F'.isDiscreteValuationRing_localRing
      haveI : IsSeparated (modelStr sX sY (j + 1)) :=
        (hM (j + 1) (coe_le_of_le_of_le hj hn)).2.1.toIsVariety.toIsSeparated
      haveI : IsSeparated (q (j + 1) hj ≫ modelStr sX sY (j + 1)) := by
        rw [hqs (j + 1) hj]; exact hWn.1.toIsSeparated
      haveI : IsSeparated (q (j + 1) hj) := IsSeparated.of_comp _ (modelStr sX sY (j + 1))
      haveI := (hq (j + 1) hj).2.2.isDominant
      have hEP : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (MMP.Fourfold.eq_of_map_eq_of_valuationRing (hq (j + 1) hj).2.2.functionFieldMap_bijective
          hE hF')
      have h1 := hEc (G j (Nat.le_of_succ_le hj) - G (j + 1) hj)
      rw [hstep0 j hj, hEP] at h1
      exact h1.symm
    have htel : ∀ m (hm : m ≤ n), (G 0 (Nat.zero_le n) - G m hm).coeff P = 0 := by
      intro m
      induction m with
      | zero => intro hm; simp
      | succ m ih =>
        intro hm
        have h1 := ih (Nat.le_of_succ_le hm)
        have h2 := hzero m hm
        simp only [DivisorWithCoeffs.coeff_sub] at h1 h2 ⊢
        linarith
    exact htel n le_rfl
  -- the numerically trivial `T` has equal pull-backs on both sides
  have hψbir : MMP.Mori.RationalMap.IsBirational (ψ n) := by
    obtain ⟨a, -, ha, -⟩ := hψ n
    exact ⟨a, ha⟩
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : QuasiCompact (modelStr sX sY n) := (hM n hn).2.1.toIsVariety.toQuasiCompact
  obtain ⟨hTn, hTpb⟩ := MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq
    sX (modelStr sX sY n) sZ hXq hX (hM n hn).2.2.1 (hM n hn).2.1 hZ π (modelMap π πY n) hπ
    (hM n hn).1
    hψbir (composite_isOver hM hS hZn hψ0 hψ n hn) hψE hT
  obtain ⟨TW, hTW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀ hT.1
  obtain ⟨TWn, hTWn, -⟩ := MMP.Flips.existsUnique_isRCartierPullback qn hTn.1
  have hTT : TW = TWn := hTpb Wm (w ≫ sZ) q₀ qn h hWn (hqs 0 _) (hqs n le_rfl) (hq 0 _).2.1 hq₀b
    (hq n le_rfl).2.1 hqnb hinv hψn TW TWn hTW hTWn
  have htrΔ : MMP.Mori.RationalMap.transformDivisor (ψ n) (B + T + t • C) =
      divisorSeq B BY n + MMP.Mori.RationalMap.transformDivisor (ψ n) T + t • divisorSeq C CY n :=
          by
    rw [map_add, map_add, transformDivisor_smul, hBn, hCn]
  have hGY : MMP.Flips.IsRCartierPullback q₀ (logCanonicalDivisor K (B + T + t • C))
      (G 0 (Nat.zero_le n) + TW) := by
    have e : logCanonicalDivisor K (B + T + t • C) = logCanonicalDivisor K (B + t • C) + T := by
      simp only [logCanonicalDivisor]; abel
    rw [e]
    exact MMP.Fourfold.isRCartierPullback_add (hG 0 (Nat.zero_le n)) hTW
  have hGZ : MMP.Flips.IsRCartierPullback qn
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
        (MMP.Mori.RationalMap.transformDivisor (ψ n) (B + T + t • C))) (G n le_rfl + TWn) := by
    have e : logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
        (MMP.Mori.RationalMap.transformDivisor (ψ n) (B + T + t • C)) =
        D n + MMP.Mori.RationalMap.transformDivisor (ψ n) T := by
      rw [hKn, htrΔ]; simp only [hDdef, logCanonicalDivisor]; abel
    rw [e]
    exact MMP.Fourfold.isRCartierPullback_add (hG n le_rfl) hTWn
  have hdiff : G 0 (Nat.zero_le n) + TW - (G n le_rfl + TWn) =
      G 0 (Nat.zero_le n) - G n le_rfl := by
    rw [hTT]; abel
  refine
    { isNormalVariety_source := hXn
      isProjectiveVariety_source := hX
      comp_eq_source := hπ
      isCanonicalDivisor := ⟨4, hK⟩
      isCartierCombination := isCartierCombination_of_isQFactorial hXq _
      isNormalVariety_target := hYn
      isProjectiveVariety_target := (hM n hn).2.1
      comp_eq_target := (hM n hn).1
      isBirational := hψbir
      isOver := composite_isOver hM hS hZn hψ0 hψ n hn
      not_isInverseExceptional := hψE
      isRelativelyNef := ?_
      exists_resolution := ⟨Wm, iW, lW, nW, w ≫ sZ, q₀, qn, h, hWn.1, hsm, hqs 0 _,
        hqs n le_rfl, (hq 0 _).2.1, (hq n le_rfl).2.1, hq₀b, hqnb, hinv, hψn,
        G 0 (Nat.zero_le n) + TW, G n le_rfl + TWn, hGY, hGZ,
        fun P => by rw [hdiff]; exact hmono n le_rfl P,
        fun P hP => by
          rw [hdiff] at hP
          by_contra hne
          exact hP (hexc P hne)⟩ }
  -- the adjoint of the model is nef over `Z`
  rw [hKn, htrΔ]
  obtain ⟨hKK, -⟩ := compatibleCanonical_spec hM hS n hn
  have hL₀ : Divisor.LinearlyEquivalent (divisorSeq K KY n - compatibleCanonical K φ n) 0 :=
    linearlyEquivalent_sub_zero hKK.symm
  have h1 := MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero htnef hL₀
  have h2 := IsRelativelyNef.add h1 (isRelativelyNef_of_isNumericallyTrivialOver hTn)
  convert h2 using 2
  simp only [logCanonicalDivisor, map_sub]
  abel

/-- **A program never returns to an earlier model.** If `X_i ≅ X_{i'}` over `Z` with `i < i'`,
then on a common model the discrepancy comparison of the `(K + B)`-negative steps `i, …, i' - 1`
would be both zero and nonzero. -/
private theorem false_of_iso_modelSeq
    (hM : ∀ i : ℕ, IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hπ : π ≫ sZ = sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπb : IsBirationalMorphism π) {i i' : ℕ} (hii' : i < i')
    (e : modelSeq X Y i ≅ modelSeq X Y i') (he : e.hom ≫ modelMap π πY i' = modelMap π πY i) :
    False := by
  have hMb : ∀ i : ℕ, (i : ℕ∞) ≤ (⊤ : ℕ∞) → IsModelAt sX sZ π K B sY πY KY BY i :=
    fun i _ => hM i
  have hSb : ∀ i : ℕ, (i : ℕ∞) < (⊤ : ℕ∞) →
      IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i := fun i _ => hS i
  -- the adjoints `D_j = K'_j + B_j`
  set D : ∀ j, RDivisor (modelSeq X Y j) :=
    fun j => logCanonicalDivisor (compatibleCanonical K φ j) (divisorSeq B BY j) with hDdef
  haveI := hZn.1
  haveI := hZn.2
  haveI := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI hprop : ∀ j : Fin (i' + 1), IsProper (modelMap π πY j.val) :=
    fun j => isProper_modelMap hMb hZ j.val le_top
  have hnv : ∀ j : ℕ, IsNormalVariety ℂ (modelStr sX sY j) :=
    fun j => ⟨(hM j).2.1.toIsVariety, inferInstance⟩
  obtain ⟨Wm, w, hWn, hwb, q, -, -, hq, -, -⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_smooth_projective_model sZ
      (fun j : Fin (i' + 1) => modelMap π πY j.val)
      (fun j => isBirationalMorphism_modelMap hMb hSb hZn hπb j.val le_top)
      (fun j => by rw [(hM j.val).1]; exact hnv j.val) (κ := Empty) Empty.elim
      (fun j => j.elim)
  haveI := hWn.1.toIsIntegral
  haveI := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Wm := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hWn.1.toQuasiCompact
  haveI : CompactSpace Wm := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI := hwb.isDominant
  -- the morphisms `q_j : W ⟶ X_j`
  set qq : ∀ j : ℕ, j ≤ i' → (Wm ⟶ modelSeq X Y j) :=
    fun j hj => q ⟨j, Nat.lt_succ_of_le hj⟩ with hqqdef
  have hqq : ∀ j (hj : j ≤ i'), qq j hj ≫ modelMap π πY j = w :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).1
  have hqqs : ∀ j (hj : j ≤ i'), qq j hj ≫ modelStr sX sY j = w ≫ sZ := fun j hj => by
    rw [← (hM j).1, ← Category.assoc, hqq j hj]
  have hqqp : ∀ j (hj : j ≤ i'), IsProjectiveMorphism (qq j hj) :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).2.1
  have hqqb : ∀ j (hj : j ≤ i'), IsBirationalMorphism (qq j hj) :=
    fun j hj => (hq ⟨j, Nat.lt_succ_of_le hj⟩).2.2
  have hqqP : ∀ j (hj : j ≤ i'), IsProper (qq j hj) :=
    fun j hj => isProper_of_isProjectiveMorphism _ (hqqp j hj)
  have hWj : ∀ j (hj : j ≤ i'), IsNormalVariety ℂ (qq j hj ≫ modelStr sX sY j) :=
    fun j hj => by rw [hqqs j hj]; exact hWn
  -- the pulled-back adjoints `G_j = q_j^* D_j`
  have hGex : ∀ j (hj : j ≤ i'), ∃ G : RDivisor Wm, IsRCartierPullback (qq j hj) (D j) G := by
    intro j hj
    haveI := (hqqb j hj).isDominant
    exact (MMP.Flips.existsUnique_isRCartierPullback (qq j hj)
      (step_adjoint_spec hMb hSb j (ENat.coe_lt_top j)).1).exists
  choose G hG using hGex
  -- the step diagrams on `W`
  have hcomm : ∀ j (hj : j + 1 ≤ i'),
      qq j (Nat.le_of_succ_le hj) ≫ f j = qq (j + 1) hj ≫ fp j := by
    intro j hj
    obtain ⟨hgP, hgb⟩ := step_g_spec hMb hSb hZ hZn hπb j (ENat.coe_lt_top j)
    haveI := hgP
    haveI := (hS j).2.2.2.2.1.isNormalVariety_target.1.toIsIntegral
    haveI : IsDominant ((qq j (Nat.le_of_succ_le hj) ≫ f j) ≫ g j) := by
      rw [Category.assoc, (hS j).2.2.1, hqq j (Nat.le_of_succ_le hj)]; infer_instance
    refine MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hgb ?_
    rw [Category.assoc, (hS j).2.2.1, hqq j (Nat.le_of_succ_le hj)]
    calc w = (show Wm ⟶ Y j from qq (j + 1) hj) ≫ (fp j ≫ g j) := by
          rw [(hS j).2.2.2.1]; exact (hqq (j + 1) hj).symm
      _ = _ := (Category.assoc _ _ _).symm
  -- push-forwards through `W`
  have hpush : ∀ j (hj : j + 1 ≤ i') (H : RDivisor Wm),
      MMP.Mori.RationalMap.transformDivisor (qq (j + 1) hj).toRationalMap H =
        MMP.Mori.RationalMap.transformDivisor (φ j)
          (MMP.Mori.RationalMap.transformDivisor (qq j (Nat.le_of_succ_le hj)).toRationalMap H) :=
              by
    intro j hj H
    obtain ⟨hf, hfp, hφ⟩ := step_isBirationalMorphism hSb j (ENat.coe_lt_top j)
    obtain ⟨hfs, -, hfps⟩ := step_comp_eq hMb hSb j (ENat.coe_lt_top j)
    have hneg := (hS j).2.2.2.2.1
    have hWnj : IsNormalVariety ℂ (sW j) := hneg.isNormalVariety_target
    haveI := hWnj.1.toIsIntegral
    haveI := hWnj.2
    haveI : LocallyOfFiniteType (sW j) := hWnj.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (W j) := LocallyOfFiniteType.isLocallyNoetherian (sW j)
    haveI : IsProper (f j) := hneg.isContraction.isProper
    haveI : IsSeparated (sW j) := hWnj.1.toIsSeparated
    haveI : IsProper (sY j) := isProper_of_isProjectiveMorphism _ (hM (j + 1)).2.1.isProjective
    haveI : IsProper (fp j ≫ sW j) := by rw [hfps]; infer_instance
    haveI : IsProper (fp j) := IsProper.of_comp (fp j) (sW j)
    haveI := hqqP j (Nat.le_of_succ_le hj)
    haveI : IsProper (show Wm ⟶ Y j from qq (j + 1) hj) := hqqP (j + 1) hj
    exact transformDivisor_eq_transformDivisor_of_isModificationOf (hnv j)
      (show IsNormalVariety ℂ (sY j) from hnv (j + 1)) hWnj
      hfs hfps hf hfp (step_exists_primeDivisor hSb j (ENat.coe_lt_top j)) hφ (hWj j
          (Nat.le_of_succ_le hj))
      (hqqb j (Nat.le_of_succ_le hj)) (hqqb (j + 1) hj) (hcomm j hj) H
  have hqD : ∀ j (hj : j ≤ i'),
      MMP.Mori.RationalMap.transformDivisor (qq j hj).toRationalMap (G j hj) = D j := fun j hj =>
    haveI := hqqP j hj
    transformDivisor_of_isRCartierPullback (hnv j) (hWj j hj) (hqqb j hj) (hG j hj)
  -- (1) each step: `G_j - G_{j+1} ≥ 0`
  have hstep : ∀ j (hj : j + 1 ≤ i') P,
      0 ≤ (G j (Nat.le_of_succ_le hj) - G (j + 1) hj).coeff P := by
    intro j hj
    obtain ⟨-, hn₁, hn₂, htr, -⟩ := step_adjoint_spec hMb hSb j (ENat.coe_lt_top j)
    haveI : QuasiCompact (modelStr sX sY j) := (hM j).2.1.toIsVariety.toQuasiCompact
    haveI : QuasiCompact (modelStr sX sY (j + 1)) := (hM (j + 1)).2.1.toIsVariety.toQuasiCompact
    haveI : IsSeparated (modelStr sX sY j) := (hM j).2.1.toIsVariety.toIsSeparated
    haveI : IsSeparated (modelStr sX sY (j + 1)) := (hM (j + 1)).2.1.toIsVariety.toIsSeparated
    haveI : LocallyOfFiniteType (modelStr sX sY j) := (hM j).2.1.toIsVariety.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (modelStr sX sY (j + 1)) :=
      (hM (j + 1)).2.1.toIsVariety.toLocallyOfFiniteType
    haveI := hqqP j (Nat.le_of_succ_le hj)
    haveI := hqqP (j + 1) hj
    exact nonneg_sub_of_isRCartierPullback_of_isRelativelyNef (hnv (j + 1)) hWn
      (hqqs j (Nat.le_of_succ_le hj)) (hqqs (j + 1) hj) (hqqp (j + 1) hj) (hqqb (j + 1) hj)
      (hcomm j hj) (hG j (Nat.le_of_succ_le hj)) (hG (j + 1) hj) hn₁ hn₂
      (by rw [hpush j hj, hqD j (Nat.le_of_succ_le hj), htr])
  -- (2) `q_{j*} G_i = D_j` for `i ≤ j ≤ i'`
  have hchain : ∀ m, i ≤ m → ∀ (hm : m ≤ i'),
      MMP.Mori.RationalMap.transformDivisor (qq m hm).toRationalMap (G i hii'.le) = D m := by
    intro m him
    induction m, him using Nat.le_induction with
    | base => intro hm; exact hqD i hm
    | succ m hmi ih =>
      intro hm
      have := hpush m hm (G i hii'.le)
      rw [ih (Nat.le_of_succ_le hm)] at this
      rw [this]
      exact (step_adjoint_spec hMb hSb m (ENat.coe_lt_top m)).2.2.2.1
  -- (3) `G_{i+1} - G_m ≥ 0` for `i + 1 ≤ m ≤ i'`
  have hmono : ∀ m, i + 1 ≤ m → ∀ (hm : m ≤ i') P, 0 ≤ (G (i + 1) hii' - G m hm).coeff P := by
    intro m him
    induction m, him using Nat.le_induction with
    | base => intro hm P; simp
    | succ m hmi ih =>
      intro hm P
      have h1 := ih (Nat.le_of_succ_le hm) P
      have h2 := hstep m hm P
      simp only [DivisorWithCoeffs.coeff_sub] at h1 h2 ⊢
      linarith
  -- (4) the isomorphism `e`: `G_{i'} - G_i ≥ 0`
  have hiso : ∀ P, 0 ≤ (G i' le_rfl - G i hii'.le).coeff P := by
    haveI : QuasiCompact (modelStr sX sY i) := (hM i).2.1.toIsVariety.toQuasiCompact
    haveI : QuasiCompact (modelStr sX sY i') := (hM i').2.1.toIsVariety.toQuasiCompact
    haveI : IsSeparated (modelStr sX sY i) := (hM i).2.1.toIsVariety.toIsSeparated
    haveI : IsSeparated (modelStr sX sY i') := (hM i').2.1.toIsVariety.toIsSeparated
    haveI : LocallyOfFiniteType (modelStr sX sY i) :=
      (hM i).2.1.toIsVariety.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (modelStr sX sY i') :=
      (hM i').2.1.toIsVariety.toLocallyOfFiniteType
    have hce : qq i hii'.le ≫ e.hom = qq i' le_rfl ≫ 𝟙 _ := by
      haveI := isProper_modelMap hMb hZ i' le_top
      haveI : IsDominant ((qq i hii'.le ≫ e.hom) ≫ modelMap π πY i') := by
        rw [Category.assoc, he, hqq i hii'.le]; infer_instance
      refine MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq
        (isBirationalMorphism_modelMap hMb hSb hZn hπb i' le_top) ?_
      rw [Category.assoc, he, hqq i hii'.le, Category.comp_id, hqq i' le_rfl]
    have hGi : IsRCartierPullback (qq i hii'.le) (-D i) (-G i hii'.le) := by
      have := MMP.Fourfold.isRCartierPullback_smul (-1) (hG i hii'.le)
      simpa only [neg_one_smul] using this
    have hGi' : IsRCartierPullback (qq i' le_rfl) (-D i') (-G i' le_rfl) := by
      have := MMP.Fourfold.isRCartierPullback_smul (-1) (hG i' le_rfl)
      simpa only [neg_one_smul] using this
    have hn₁ : IsRelativelyNef ℂ (modelStr sX sY i) e.hom (-(-D i)) := by
      rw [neg_neg]
      have h1 := MMP.Flips.isRelativelyNef_id (modelStr sX sY i) (step_adjoint_spec hMb hSb i
          (ENat.coe_lt_top i)).1
      rw [← e.hom_inv_id] at h1
      exact IsRelativelyNef.of_comp h1
    have hn₂ : IsRelativelyNef ℂ (modelStr sX sY i') (𝟙 _) (-D i') :=
      MMP.Flips.isRelativelyNef_id (modelStr sX sY i')
        (isCartierCombination_of_isQFactorial (hM i').2.2.1 _)
    have hp : MMP.Mori.RationalMap.transformDivisor (qq i' le_rfl).toRationalMap
        (-G i hii'.le) = -D i' := by
      rw [map_neg, hchain i' hii'.le le_rfl]
    haveI := hqqP i hii'.le
    haveI := hqqP i' le_rfl
    have := nonneg_sub_of_isRCartierPullback_of_isRelativelyNef (hnv i') hWn
      (hqqs i hii'.le) (hqqs i' le_rfl) (hqqp i' le_rfl) (hqqb i' le_rfl) hce hGi hGi' hn₁ hn₂ hp
    intro P
    have h := this P
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_neg] at h ⊢
    linarith
  -- (5) hence `G_i = G_{i+1}`
  have hGeq : G (i + 1) hii' = G i hii'.le := by
    refine Finsupp.ext fun P => ?_
    have h1 := hstep i hii' P
    have h2 := hmono i' hii' le_rfl P
    have h3 := hiso P
    simp only [DivisorWithCoeffs.coeff_sub] at h1 h2 h3
    change (G (i + 1) hii').coeff P = (G i hii'.le).coeff P
    linarith
  -- (6) a curve contracted by `f_i` lifted to `W`
  obtain ⟨-, -, hn₂, -, Γ, hΓ, hneg⟩ := step_adjoint_spec hMb hSb i (ENat.coe_lt_top i)
  haveI := (hqqb i hii'.le).isDominant
  haveI := hqqP i hii'.le
  haveI := hqqP (i + 1) hii'
  haveI : Surjective (qq i hii'.le) := surjective_of_isDominant_of_isClosed_range _
    (qq i hii'.le).isClosedMap.isClosed_range
  haveI : QuasiCompact (modelStr sX sY i) := (hM i).2.1.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType (modelStr sX sY i) := (hM i).2.1.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated (modelStr sX sY i) := (hM i).2.1.toIsVariety.toIsSeparated
  haveI : QuasiCompact (sY i) := (hM (i + 1)).2.1.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType (sY i) := (hM (i + 1)).2.1.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated (sY i) := (hM (i + 1)).2.1.toIsVariety.toIsSeparated
  haveI : QuasiCompact (qq (i + 1) hii' ≫ sY i) := by
    change QuasiCompact (qq (i + 1) hii' ≫ modelStr sX sY (i + 1)); rw [hqqs (i + 1) hii']
    infer_instance
  obtain ⟨C', hC'q, hdeg⟩ := MMP.Fourfold.exists_properCurve_map_eq (w ≫ sZ) (modelStr sX sY i)
    (qq i hii'.le) (hqqs i hii'.le) Γ
  obtain ⟨m, r, L, L', hL, hDL, hpb, hGL⟩ := hG i hii'.le
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hpb j).2.isCartier (hL j)
  have hx' := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (w ≫ sZ) C' r L' hL'c
  rw [← hGL] at hx'
  have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (modelStr sX sY i) Γ r L hL
  rw [← hDL] at hx
  have hxneg := hneg _ _ _ _ hx
  have hmul : ∀ j, ((L' j).degreeOn ℂ (w ≫ sZ) C'.ι C'.dim_le (hL'c j) : ℝ) =
      (residueFieldDegree (qq i hii'.le) C'.point : ℝ) *
        ((L j).degreeOn ℂ (modelStr sX sY i) Γ.ι Γ.dim_le (hL j) : ℝ) := fun j =>
    MMP.Fourfold.degreeOn_eq_mul_of_isPullback (qq i hii'.le) (hqqs i hii'.le) (hL j) (hpb j).2
        (hL'c j)
      C' Γ hC'q
  haveI : IsProper (show Wm ⟶ Y i from qq (i + 1) hii') := hqqP (i + 1) hii'
  have hnefW := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 (W i)) (fp i)
    (qq i hii'.le ≫ f i) (show Wm ⟶ Y i from qq (i + 1) hii')
    (by rw [Category.comp_id]; exact hcomm i hii') hn₂ (hG (i + 1) hii')
  have hnefW' : IsRelativelyNef ℂ (w ≫ sZ) (qq i hii'.le ≫ f i) (G i hii'.le) := by
    rw [← hGeq]
    exact IsRelativelyNef.of_eq_structure (hqqs (i + 1) hii') hnefW
  have hC'c : C'.IsContractedBy (qq i hii'.le ≫ f i) := fun y hy => by
    have hy' : qq i hii'.le y ∈ closure (qq i hii'.le '' ({C'.point} : Set Wm)) :=
      image_closure_subset_closure_image (qq i hii'.le).continuous ⟨y, hy, rfl⟩
    rw [Set.image_singleton, hC'q] at hy'
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ _ hy', hC'q]
  have hpos := IsRelativelyNef.nonneg hnefW' hC'c hx'
  simp only [hmul, mul_left_comm (r _), ← Finset.mul_sum] at hpos
  have hd : (0 : ℝ) < residueFieldDegree (qq i hii'.le) C'.point := by
    exact_mod_cast Nat.pos_of_ne_zero hdeg
  have := (mul_nonneg_iff_of_pos_left hd).mp hpos
  linarith

/-- The transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {X₁ X₂ : Scheme.{0}} (φ' : X₁.RationalMap X₂)
    {D : RDivisor X₁} (hD : ∀ P, 0 ≤ D.coeff P) (Q : MMP.Mori.PrimeDivisor X₂) :
    0 ≤ (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q := by
  classical
  revert hD
  induction D using Finsupp.induction with
  | zero => intro _; simp
  | single_add a b D ha hb ih =>
    intro hD
    have hDa : D a = 0 := Finsupp.notMem_support_iff.mp ha
    have hD' : ∀ P, 0 ≤ DivisorWithCoeffs.coeff D P := fun P => by
      by_cases hP : P = a
      · subst hP; change 0 ≤ D P; rw [hDa]
      · have := hD P
        change 0 ≤ (Finsupp.single a b + D) P at this
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hP), zero_add] at this
        exact this
    have hb0 : 0 ≤ b := by
      have := hD a
      change 0 ≤ (Finsupp.single a b + D) a at this
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, hDa, add_zero] at this
    rw [map_add, DivisorWithCoeffs.coeff_add]
    refine add_nonneg ?_ (ih hD')
    rw [MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ' a with _ | F
    · simp
    · change 0 ≤ (Finsupp.single F b) Q
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb0]

open Filter Topology in
/-- A real boundary perturbed along divisors supported where its coefficients are at least
`δ > 0` stays effective and klt for small perturbations. -/
private theorem exists_isRealKltPair_add_sum_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX)
    {Θ : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hk : IsRealKltPair sX Θ)
    {ι : Type} [Fintype ι] (D : ι → RDivisor X) {δ : ℝ} (hδ : 0 < δ)
    (hDδ : ∀ i P, (D i).coeff P ≠ 0 → δ ≤ Θ.coeff P) :
    ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (Θ + ∑ i, u i • D i).coeff P) ∧ IsRealKltPair sX (Θ + ∑ i, u i • D i) := by
  classical
  let s := Θ.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : (ι → ℝ) → s → ℝ := fun u j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1
  have hD0 : ∀ i W, W ∉ s → (D i).coeff W = 0 := fun i W hW => by
    by_contra h
    have := hDδ i W h
    have h0 : Θ.coeff W = 0 := Finsupp.notMem_support_iff.mp hW
    linarith
  have hrep : ∀ u, Θ + ∑ i, u i • D i = ∑ j, Finsupp.single (p j) (y u j) :=
    add_sum_smul_eq_sum_single Θ D hD0
  have hcont : Continuous y := by
    refine continuous_pi fun j => continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_apply i).mul continuous_const
  have hpos : ∀ᶠ u in 𝓝 (0 : ι → ℝ), ∀ j, 0 < y u j := by
    refine eventually_all.2 fun j => ?_
    have hj : 0 < y 0 j := by
      have : Θ.coeff j.1 ≠ 0 := Finsupp.mem_support_iff.mp j.2
      simpa [y] using lt_of_le_of_ne (hΘ j.1) (Ne.symm this)
    exact ((continuous_apply j).comp hcont).continuousAt.eventually (lt_mem_nhds hj)
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  have htend : Filter.Tendsto y (𝓝 0) (𝓝[Set.Ici 0] (y 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt,
      hpos.mono fun u hu => fun j => (hu j).le⟩
  have hall : ∀ᶠ u in 𝓝 (0 : ι → ℝ), (∀ j, 0 < y u j) ∧
      IsRealKltPair sX (∑ j, Finsupp.single (p j) (y u j)) := hpos.and (htend.eventually hev)
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hd : dist u 0 < ε := (dist_pi_lt_iff hε).mpr fun i => by
    simpa [Real.dist_eq] using hu i
  obtain ⟨h1, h2⟩ := hεh hd
  rw [hrep u]
  refine ⟨fun P => ?_, h2⟩
  rw [MMP.Fourfold.coeff_sum_single]
  exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [(h1 j).le]

/-- A component of a transform comes from a component of the divisor. -/
private theorem exists_of_transformDivisor_coeff_ne_zero {X₁ X₂ : Scheme.{0}}
    (φ' : X₁.RationalMap X₂) {D : RDivisor X₁} {Q : MMP.Mori.PrimeDivisor X₂}
    (h : (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q ≠ 0) :
    ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q ∧ D.coeff P ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  apply h
  clear h
  revert hne
  induction D using Finsupp.induction with
  | zero => intro _; simp
  | single_add a b D ha hb ih =>
    intro hne
    have hDa : D a = 0 := Finsupp.notMem_support_iff.mp ha
    have hD' : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q →
        DivisorWithCoeffs.coeff D P = 0 := fun P hP => by
      have := hne P hP
      change (Finsupp.single a b + D) P = 0 at this
      by_cases hPa : P = a
      · subst hPa; exact hDa
      · rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hPa), zero_add] at this
        exact this
    rw [map_add, DivisorWithCoeffs.coeff_add, ih hD', add_zero,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases hta : MMP.Mori.RationalMap.transformPrimeDivisor φ' a with _ | F
    · simp
    · change (Finsupp.single F b) Q = 0
      rw [Finsupp.single_apply]
      split_ifs with hFQ
      · subst hFQ
        have := hne a hta
        change (Finsupp.single a b + D) a = 0 at this
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, hDa, add_zero] at this
      · rfl

/-- The coefficient of an effective divisor along `P` is at most that of its transform along the
transform of `P`. -/
private theorem coeff_le_transformDivisor_coeff {X₁ X₂ : Scheme.{0}} (φ' : X₁.RationalMap X₂)
    {D : RDivisor X₁} (hD : ∀ P, 0 ≤ D.coeff P) {P : MMP.Mori.PrimeDivisor X₁}
    {Q : MMP.Mori.PrimeDivisor X₂} (hPQ : MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q)
        :
    D.coeff P ≤ (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q := by
  classical
  have hsplit : D = Finsupp.single P (D P) + D.erase P := (Finsupp.single_add_erase P D).symm
  have hE : ∀ W, 0 ≤ DivisorWithCoeffs.coeff (D.erase P) W := fun W => by
    change 0 ≤ (D.erase P) W
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hD W
  have key : (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q =
      D P + (MMP.Mori.RationalMap.transformDivisor φ' (D.erase P)).coeff Q := by
    conv_lhs => rw [hsplit]
    rw [map_add, DivisorWithCoeffs.coeff_add,
      MMP.Mori.RationalMap.transformDivisor_single_of_eq_some hPQ]
    change (Finsupp.single Q (D P)) Q + _ = _
    simp
  rw [key]
  change D P ≤ _
  linarith [transformDivisor_nonneg φ' hE Q]

/-- **The neighbourhood of the boundary.** For small perturbations `u` along the basis, the
perturbed boundary `B + T + λ_n C + ∑ u_i H_i` and its transform to `X_n` are effective and
klt. -/
private theorem exists_nbhd
    (hM : ∀ i : ℕ, IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    {ψ : ∀ i, X.RationalMap (modelSeq X Y i)} {T : RDivisor X} (hT0 : ∀ P, 0 ≤ T.coeff P)
    {ι : Type} [Fintype ι] (H : ι → Divisor X) {δ : ℝ} (hδ : 0 < δ)
    (hHδ : ∀ i P, (H i).coeff P ≠ 0 → δ ≤ (B + T).coeff P) (n : ℕ)
    (hklt : IsRealKltPair sX (B + T + lam n • C))
    (hψE : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ψ n) F)
    (hNW : IsNefWeakModel sX (modelStr sX sY n) sZ π (modelMap π πY n) K (B + T + lam n • C)
      (ψ n)) :
    ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i)).coeff P) ∧
      IsRealKltPair sX (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i)) ∧
      (∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor (ψ n)
        (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i))).coeff Q) ∧
      IsRealKltPair (modelStr sX sY n) (MMP.Mori.RationalMap.transformDivisor (ψ n)
        (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i))) := by
  classical
  have hl0 : 0 ≤ lam n := (hS n).1.1.1
  set Θ := B + T + lam n • C with hΘdef
  have hΘ0 : ∀ P, 0 ≤ Θ.coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
    have := hB P; have := hT0 P; have := hC P
    positivity
  have hBTΘ : ∀ P, (B + T).coeff P ≤ Θ.coeff P := fun P => by
    rw [hΘdef, DivisorWithCoeffs.coeff_add (B + T), DivisorWithCoeffs.coeff_smul]
    have := hC P
    rw [smul_eq_mul]
    nlinarith [mul_nonneg hl0 this]
  have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_isRealKltPair_add_sum_smul sX hXqp hXq hΘ0 hklt
    (fun i => Divisor.toRDivisor (H i)) hδ (fun i P hP => (hHδ i P (by
      intro h0; apply hP; rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero])).trans (hBTΘ P))
  -- the model side
  have hYp : MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY n) := (hM n).2.1
  have hYq : IsQFactorial (modelStr sX sY n) := (hM n).2.2.1
  obtain ⟨m, hKY⟩ := (hM n).2.2.2.1
  have hYqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (modelStr sX sY n) :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _ hYp
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact (modelStr sX sY n) := inferInstance
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  have hkltY := isRealKltPair_transformDivisor_of_isNefWeakModel hNW hYq hKY hklt
  have hΘ0Y : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor (ψ n) Θ).coeff Q :=
    transformDivisor_nonneg (ψ n) hΘ0
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_isRealKltPair_add_sum_smul (modelStr sX sY n) hYqp hYq hΘ0Y
    hkltY (fun i => MMP.Mori.RationalMap.transformDivisor (ψ n) (Divisor.toRDivisor (H i))) hδ
    (fun i Q hQ => by
      obtain ⟨P, hPQ, hP⟩ := exists_of_transformDivisor_coeff_ne_zero (ψ n) hQ
      refine ((hHδ i P ?_).trans (hBTΘ P)).trans (coeff_le_transformDivisor_coeff (ψ n) hΘ0 hPQ)
      intro h0; apply hP; rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero])
  have hlin : ∀ u : ι → ℝ, MMP.Mori.RationalMap.transformDivisor (ψ n)
      (Θ + ∑ i, u i • Divisor.toRDivisor (H i)) =
      MMP.Mori.RationalMap.transformDivisor (ψ n) Θ + ∑ i, u i •
        MMP.Mori.RationalMap.transformDivisor (ψ n) (Divisor.toRDivisor (H i)) := fun u => by
    rw [map_add, map_sum]
    simp only [transformDivisor_smul]
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun u hu => ?_⟩
  obtain ⟨a₁, a₂⟩ := h₁ u fun i => (hu i).trans_le (min_le_left _ _)
  obtain ⟨b₁, b₂⟩ := h₂ u fun i => (hu i).trans_le (min_le_right _ _)
  rw [hlin]
  exact ⟨a₁, a₂, b₁, b₂⟩

/-- **No infinite program with scaling.** -/
private theorem false_of_forall_isStepAt
    (hM : ∀ i : ℕ, IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hBk : ∀ i : ℕ, IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i))
    (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π)
    (hXq : IsQFactorial sX) (hK : K.IsCanonicalDivisor sX 4)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) : False := by
  have hMb : ∀ i : ℕ, (i : ℕ∞) ≤ (⊤ : ℕ∞) → IsModelAt sX sZ π K B sY πY KY BY i :=
    fun i _ => hM i
  have hSb : ∀ i : ℕ, (i : ℕ∞) < (⊤ : ℕ∞) →
      IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i := fun i _ => hS i
  classical
  -- the composites of the steps
  obtain ⟨ψ, hψ0, hψ⟩ := exists_composites φ (fun i => (step_isBirationalMorphism hSb i
      (ENat.coe_lt_top i)).2.2.1)
  -- a basis of `N¹(X/Z)` inside a crepant shift of the boundary, and a rational polytope
  obtain ⟨ι, _, H, T, hHc, hspan, hind, hT, hT0, hTklt, δ, hδ, hHδ⟩ :=
    exists_basis_shift hπ hX hZ hZn hπp hπb hXq hK hB hC hklt
  obtain ⟨V, ε₁, hε₁, hV0, hVklt, hVhull⟩ := exists_polytope hX hXq hB hC hT0 hTklt H hδ hHδ
  -- the finitely many log minimal models of the polytope
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  obtain ⟨N, Yg, iYg, cYg, lYg, nYg, sYg, πg, KYg, φg, hg, hcov⟩ :=
    MMP.Fourfold.exists_finite_isRealLogMinimalModel_of_mem_convexHull (KX := K) V hX hZ hZn hπ hπp
      hπb (by rw [hK.1]; rfl) hXq ⟨4, hK⟩ hV0 hVklt
  -- the boundaries of the program are effective
  have hBn : ∀ i, ∀ P, 0 ≤ (divisorSeq B BY i).coeff P := by
    intro i
    induction i with
    | zero => exact hB
    | succ i ih =>
      intro P
      rw [show divisorSeq B BY (i + 1) = BY i from rfl, (hS i).2.2.2.2.2.2.2.1]
      exact transformDivisor_nonneg _ ih P
  -- every model is an ample log minimal model of a perturbed source pair
  have hmodel : ∀ n, ∃ u : ι → ℝ, (∀ i, |u i| < ε₁) ∧
      IsRealLogMinimalModel sX (modelStr sX sY n) sZ π (modelMap π πY n) K
        (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i))
        (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
        (MMP.Mori.RationalMap.transformDivisor (ψ n)
          (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i))) (ψ n) ∧
      IsRelativelyAmple (modelMap π πY n)
        (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ n) K)
          (MMP.Mori.RationalMap.transformDivisor (ψ n)
            (B + T + lam n • C + ∑ i, u i • Divisor.toRDivisor (H i)))) := by
    intro n
    obtain ⟨hψE, -, -, -, hNW⟩ :=
      isNefWeakModel_composite hMb hSb hπ hX hZ hZn hπb hXq hK hψ0 hψ hT n le_top
        (lam_pos hSb n (ENat.coe_lt_top n)).le
        (fun j hj => lam_le_of_le hMb hSb hj.le (ENat.coe_lt_top n)) (hS n).1.1.2
    have hl0 : 0 < lam n := lam_pos hSb n (ENat.coe_lt_top n)
    have hl1 : lam n ≤ 1 := (lam_le_of_le hMb hSb (Nat.zero_le n) (ENat.coe_lt_top n)).trans
        (lam_zero_le_one hSb (ENat.coe_lt_top 0) hnef)
    have hkltn := hTklt (lam n) hl0.le hl1
    obtain ⟨ε₀, hε₀, hnb⟩ := exists_nbhd hM hS hX hXq hZ hB hC hT0 H hδ hHδ n hkltn hψE hNW
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    exact exists_isRealLogMinimalModel_isRelativelyAmple_of_isNefWeakModel sX sZ hZ π hπ hπp hX hXq
      K ⟨4, hK⟩ H hHc hspan hind n Y sY πY W sW f g fp φ ψ
      (fun i _ => ⟨(hM i).1, (hM i).2.1⟩)
      (fun i _ => ⟨(hS i).2.1, (hS i).2.2.1, (hS i).2.2.2.1, divisorSeq K KY i, divisorSeq B BY i,
        (hM i).2.2.2.1, hBn i, hBk i, (hS i).2.2.2.2.1, (hS i).2.2.2.2.2.2.1⟩)
      hψ0 (fun i _ => hψ i) (hM n).2.2.1 (B + T + lam n • C) hkltn hNW ⟨ε₀, hε₀, hnb⟩ ε₁ hε₁
  choose u hu using hmodel
  -- the geography model of each perturbed pair
  have hgeo : ∀ n, ∃ j, IsRealLogMinimalModel sX (sYg j) sZ π (πg j) K
      (B + T + lam n • C + ∑ i, u n i • Divisor.toRDivisor (H i)) (KYg j)
      (MMP.Mori.RationalMap.transformDivisor (φg j)
        (B + T + lam n • C + ∑ i, u n i • Divisor.toRDivisor (H i))) (φg j) := by
    intro n
    have hl0 : 0 < lam n := lam_pos hSb n (ENat.coe_lt_top n)
    have hl1 : lam n ≤ 1 := (lam_le_of_le hMb hSb (Nat.zero_le n) (ENat.coe_lt_top n)).trans
        (lam_zero_le_one hSb (ENat.coe_lt_top 0) hnef)
    obtain ⟨j, hj, -⟩ := hcov _ (hVhull (lam n) hl0.le hl1 (u n) (hu n).1)
    exact ⟨j, hj⟩
  choose J hJ using hgeo
  -- every model is isomorphic over `Z` to one of finitely many
  have hiso : ∀ n, ∃ e : Yg (J n) ≅ modelSeq X Y n, e.hom ≫ modelMap π πY n = πg (J n) := by
    intro n
    haveI := iYg (J n)
    haveI := cYg (J n)
    haveI := lYg (J n)
    haveI := nYg (J n)
    haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
    obtain ⟨hψE, -, -, -, -⟩ :=
      isNefWeakModel_composite hMb hSb hπ hX hZ hZn hπb hXq hK hψ0 hψ hT n le_top
        (lam_pos hSb n (ENat.coe_lt_top n)).le
        (fun j hj => lam_le_of_le hMb hSb hj.le (ENat.coe_lt_top n)) (hS n).1.1.2
    exact exists_iso_of_isRealLogMinimalModel_of_isRelativelyAmple hX hXq hZ hZn hπb (hJ n)
      (hu n).2.1 (hg (J n)).2.2.2.2.2.2 hψE (hu n).2.2
  -- two of them are isomorphic, which the program forbids
  obtain ⟨n, n', hne, hJJ⟩ := Finite.exists_ne_map_eq_of_infinite J
  wlog hlt : n < n' generalizing n n'
  · exact this n' n hne.symm hJJ.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  obtain ⟨e, he⟩ := hiso n
  obtain ⟨e', he'⟩ : ∃ e' : Yg (J n) ≅ modelSeq X Y n', e'.hom ≫ modelMap π πY n' = πg (J n) := by
    rw [hJJ]; exact hiso n'
  refine false_of_iso_modelSeq hM hS hπ hZ hZn hπb hlt (e.symm ≪≫ e') ?_
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he', ← he, Iso.inv_hom_id_assoc]

/-- The zero divisor is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_zero' {k : Type} [Field k] {X₁ W₁ : Scheme.{0}}
    {s₁ : X₁ ⟶ Spec (.of k)} [QuasiCompact s₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    (f₁ : X₁ ⟶ W₁) : MMP.Flips.IsNumericallyTrivialOver k s₁ f₁ (0 : RDivisor X₁) :=
  ⟨⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun Γ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
      (eq_zero_of_isRIntersectionNumber_zero Γ h₁).trans
        (eq_zero_of_isRIntersectionNumber_zero Γ h₂).symm⟩

/-- **The boundaries of a program are klt.** The `n`-th model is a nef weak model of
`(X, B + t C)` for a level `t ≤ λ_j`, `j < n`, at which its adjoint is nef, and `(X, B + t C)` is
klt for `t ≤ 1`; so `(X_n, B_n + t C_n)` is klt, hence `(X_n, B_n)`. -/
private theorem isRealKltPair_divisorSeq
    (hM : ∀ i : ℕ, (i : ℕ∞) ≤ N → IsModelAt sX sZ π K B sY πY KY BY i)
    (hS : ∀ i : ℕ, (i : ℕ∞) < N → IsStepAt sX π K B C sY πY KY BY CY lam sW f g fp φ i)
    (hφb : ∀ i, MMP.Mori.RationalMap.IsBirational (φ i))
    (hπ : π ≫ sZ = sX) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hπb : IsBirationalMorphism π) (hXq : IsQFactorial sX) (hK : K.IsCanonicalDivisor sX 4)
    (hC : ∀ P, 0 ≤ C.coeff P) (hklt : IsRealKltPair sX (B + C))
    (n : ℕ) (hn : (n : ℕ∞) ≤ N) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (htl : ∀ j < n, t ≤ lam j)
    (htnef : IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
      (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n + t • divisorSeq C CY n))) :
    IsRealKltPair (modelStr sX sY n) (divisorSeq B BY n) := by
  classical
  obtain ⟨ψ, hψ0, hψ⟩ := exists_composites φ hφb
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  have hT := isNumericallyTrivialOver_zero' (k := ℂ) (s₁ := sX) π
  obtain ⟨-, -, hBn, hCn, hNW⟩ :=
    isNefWeakModel_composite hM hS hπ hX hZ hZn hπb hXq hK hψ0 hψ hT n hn ht0 htl htnef
  have hkltX : IsRealKltPair sX (B + 0 + t • C) := by
    refine IsRealKltPair.of_le hXq (fun P => ?_) hklt
    rw [add_zero, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    nlinarith [hC P]
  have hMn := hM n hn
  haveI : QuasiCompact (modelStr sX sY n) := hMn.2.1.toIsVariety.toQuasiCompact
  obtain ⟨m, hKn⟩ := hMn.2.2.2.1
  have h := isRealKltPair_transformDivisor_of_isNefWeakModel hNW hMn.2.2.1 hKn hkltX
  rw [map_add, map_add, map_zero, add_zero, transformDivisor_smul, hBn, hCn] at h
  refine IsRealKltPair.of_le hMn.2.2.1 (fun P => ?_) h
  have hCn0 : 0 ≤ (divisorSeq C CY n).coeff P := by
    rw [← hCn]; exact transformDivisor_nonneg _ hC P
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  nlinarith

end InfiniteProgram

/-! ### Existence of a program with scaling -/

section ExistenceProgram

/-- An effective klt pair is dlt: take the empty open set as the snc locus. -/
private theorem isRealDltPair_of_isRealKltPair {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : RDivisor X}
    (hB : ∀ P, 0 ≤ B.coeff P) (h : IsRealKltPair sX B) : IsRealDltPair sX B := by
  have hempty : IsEmpty ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens) :=
    ⟨fun x => x.2 (by trivial)⟩
  refine ⟨⟨h.1, hB, h.2.2.1, fun n E a ha => (h.2.2.2 n E a ha).le⟩, fun P => (h.2.1 P).le, ⊤,
    ?_, ?_, fun n D _ a ha => h.2.2.2 n D a ha⟩
  · refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
    exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens)) x
  · refine ⟨fun E _ => ?_, fun x => ?_⟩
    · exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens))
        (AlgebraicGeometry.PrimeDivisor.genericPoint E)
    · exact isEmptyElim (α := ((⊤ : TopologicalSpace.Closeds X).compl : X.Opens)) x

/-- **Log canonical pairs on a `ℚ`-factorial variety are convex**. -/
private theorem isRealLcPair_segment {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {Θ₀ Θ₁ : RDivisor X} (h₀ : IsRealLcPair sX Θ₀) (h₁ : IsRealLcPair sX Θ₁) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsRealLcPair sX ((1 - s) • Θ₀ + s • Θ₁) := by
  classical
  set t := Θ₀.support ∪ Θ₁.support
  let p : t → MMP.Mori.PrimeDivisor X := Subtype.val
  have e₀ := eq_sum_single_of_support_subset (Θ := Θ₀) (s := t) Finset.subset_union_left
  have e₁ := eq_sum_single_of_support_subset (Θ := Θ₁) (s := t) Finset.subset_union_right
  have hΘ : (1 - s) • Θ₀ + s • Θ₁ = ∑ j : t, Finsupp.single (p j)
      ((1 - s) * Θ₀.coeff j.1 + s * Θ₁.coeff j.1) := by
    conv_lhs => rw [e₀, e₁]
    simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← Finset.sum_add_distrib,
      ← Finsupp.single_add]
    rfl
  choose m hm hmc using fun j : t => hQ.2 (Finsupp.single (p j) (1 : ℤ))
  obtain ⟨n, K, hK, -⟩ := h₀.2.2.1
  refine ⟨h₀.1, fun P => ?_, ⟨n, K, hK, ?_⟩, fun n' D a ha => ?_⟩
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul, smul_eq_mul]
    have := h₀.2.1 P
    have := h₁.2.1 P
    have := sub_nonneg.2 hs1
    positivity
  · rw [hΘ]
    exact MMP.Fourfold.isRCartier_add_sum_single hQ K p _
  · by_contra hneg
    push Not at hneg
    have hconv := MMP.Fourfold.convex_setOf_lt_isLogDiscrepancy (k := ℂ) (sX := sX) p m hm hmc
      a (fun _ => True)
    have hy₀ : (fun j : t => Θ₀.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX)
        (a' : ℝ), True → MMP.Intersection.IsLogDiscrepancy sX n
          (∑ i, Finsupp.single (p i) (y i)) D a' → a < a'} :=
      fun n D a' _ ha' => hneg.trans_le (h₀.2.2.2 n D a' (e₀ ▸ ha'))
    have hy₁ : (fun j : t => Θ₁.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX)
        (a' : ℝ), True → MMP.Intersection.IsLogDiscrepancy sX n
          (∑ i, Finsupp.single (p i) (y i)) D a' → a < a'} :=
      fun n D a' _ ha' => hneg.trans_le (h₁.2.2.2 n D a' (e₁ ▸ ha'))
    have hy := hconv hy₀ hy₁ (sub_nonneg.2 hs1) hs0 (by ring)
    rw [hΘ] at ha
    have := hy n' D a trivial (by convert ha using 3)
    exact lt_irrefl a this

/-- The degree of the class of a contracted curve. -/
private theorem degree_relativeClass' {k : Type} [Field k] {X W : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ W} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    RelativeNumericalCurveClasses.degree sX f L (C.relativeClass f hC) = C.degree k L := by
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  exact OneCycle.degree_cycle ℝ L C

/-- **From degrees on classes to intersection numbers.** If every Cartier presentation of `D`
has linear form `φ` on the class of a contracted curve `C`, every intersection number of `D`
with `C` satisfies the same relation. -/
private theorem isRIntersectionNumber_of_degree {X W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ W} {D :
        RDivisor X}
    (C : ProperCurve sX) (hC : C.IsContractedBy f) (P : ℝ → Prop)
    (hD : ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
      D = ∑ i, c i • Divisor.toRDivisor (M i) →
      P (∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf (C.relativeClass f hC))))
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX D r L C x) : P x := by
  obtain ⟨hL, d, hDeq, hd, rfl⟩ := hx
  have h := hD m r L hL hDeq
  have e : (∑ j, r j * (d j : ℝ)) = ∑ j, r j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX f (L j).divisorialSheaf (C.relativeClass f hC)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    haveI := (hL j).isInvertibleModule_divisorialSheaf
    rw [degree_relativeClass', ProperCurve.degree_divisorialSheaf C (L j) (hL j),
      (hd j).eq_degreeOn]
  rw [e]
  exact h

/-- A dominant morphism of integral varieties over `k` does not raise dimension in the target:
`dim B ≤ dim A`. -/
private theorem topologicalKrullDim_le_of_isDominant {k : Type} [Field k] {A B : Scheme.{0}}
    [IsIntegral A] [IsIntegral B] {sA : A ⟶ Spec (.of k)} {sB : B ⟶ Spec (.of k)}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (g : A ⟶ B) [IsDominant g]
    (hg : g ≫ sB = sA) : topologicalKrullDim B ≤ topologicalKrullDim A := by
  subst hg
  rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sB,
    MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (g ≫ sB)]
  letI := functionFieldAlgebra sB
  letI := functionFieldAlgebra (g ≫ sB)
  letI := functionFieldMapAlgebra g
  haveI := isScalarTower_functionFieldMap sB g
  have h := trdeg_le_of_injective
    (IsScalarTower.toAlgHom k B.functionField A.functionField) (RingHom.injective _)
  haveI := essFiniteType_functionField (sX := g ≫ sB)
  have hfin : Algebra.trdeg k A.functionField < Cardinal.aleph0 :=
    trdeg_lt_aleph0 (K := k) (L := A.functionField)
  exact_mod_cast Cardinal.toNat_le_toNat h hfin

/-- If `K + B + t C` is nef over `Z` and null on a contracted curve on which `C` is positive,
then `t` is the nef threshold of `C`. -/
private theorem isLeast_of_null {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (hXq : IsQFactorial sX) {π : X ⟶ Z} {K : Divisor X}
    {B C : RDivisor X} {t : ℝ} (ht : 0 ≤ t)
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + t • C)))
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy π)
    (hnull : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX (logCanonicalDivisor K (B + t • C)) r L Γ x → x = 0)
    (hpos : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX C r L Γ x → 0 < x) :
    IsLeast {s : ℝ | 0 ≤ s ∧ IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + s • C))} t := by
  refine ⟨⟨ht, hnef⟩, fun s ⟨_, hsnef⟩ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, r, L, hL, hD, hnn⟩ := hsnef
  have hx := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX Γ r L hL
  rw [← hD] at hx
  have hx0 := hnn Γ hΓ _ hx
  obtain ⟨_, _, _, y, hy⟩ := MMP.Flips.exists_isRIntersectionNumber (k := ℂ)
    (isCartierCombination_of_isQFactorial hXq C) Γ
  have hy0 := hpos _ _ _ _ hy
  have hlin := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ _ _ _ _ _ _ 1 (t - s) hx hy
  have heq : (1 : ℝ) • logCanonicalDivisor K (B + s • C) + (t - s) • C =
      logCanonicalDivisor K (B + t • C) := by
    simp only [logCanonicalDivisor, one_smul, sub_smul]
    abel
  rw [heq] at hlin
  have := hnull _ _ _ _ hlin
  nlinarith

/-- A divisor which is null on every curve contracted by `f` is numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_of_null {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {f : X ⟶ W} {N : RDivisor X} (hN : IsCartierCombination N)
    (hnull : ∀ Γ : ProperCurve sX, Γ.IsContractedBy f →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber ℂ sX N r L Γ x → x = 0) :
    IsNumericallyTrivialOver ℂ sX f N :=
  ⟨hN, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun Γ hΓ _ _ _ _ _ _ _ _ h₁ h₂ =>
      (hnull Γ hΓ _ _ _ _ h₁).trans (eq_zero_of_isRIntersectionNumber_zero Γ h₂).symm⟩

/-- A morphism with `f_* 𝒪_X = 𝒪_Y` onto an integral scheme is dominant: a nonempty open of `Y`
missing the image of `f` would have `Γ(Y, V) ≅ Γ(X, ∅) = 0`. -/
private theorem isDominant_of_isIso_app {X Y : Scheme.{0}} [IsIntegral Y] (p : X ⟶ Y)
    (hp : ∀ U : Y.Opens, IsIso (p.app U)) : IsDominant p := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨y, hy⟩ => ?_⟩
  by_contra hempty
  let V' : Y.Opens := ⟨V, hV⟩
  have hbot : p ⁻¹ᵁ V' = ⊥ := TopologicalSpace.Opens.ext <| Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => hempty ⟨p x, hx, x, rfl⟩
  have : Subsingleton Γ(X, p ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(Y, V') := (ConcreteCategory.bijective_of_isIso (p.app V')).1.subsingleton
  have h10 := congrArg (Y.presheaf.germ V' y hy).hom (Subsingleton.elim (1 : Γ(Y, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- **Contractions over a birational base are birational.** If `f : X ⟶ W` is a contraction of
projective varieties and `f ≫ h = π` with `π : X ⟶ Z` birational onto a variety, then `f` is
birational and `h ≫ s_Z = s_W`. -/
private theorem isBirationalMorphism_of_isContraction {X W Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ W}
    {h : W ⟶ Z} {π : X ⟶ Z} (hc : IsContraction ℂ sW sX f) (hfh : f ≫ h = π)
    (hπ : π ≫ sZ = sX) (hπb : IsBirationalMorphism π) (hZ : MMP.Mori.IsVariety ℂ sZ) :
    IsBirationalMorphism f ∧ h ≫ sZ = sW := by
  haveI : IsIntegral W := hc.isVariety_target.toIsIntegral
  haveI : IsIntegral Z := hZ.toIsIntegral
  haveI : LocallyOfFiniteType sW := hc.isVariety_target.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hc.isVariety_source.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  haveI : IsDominant f := isDominant_of_isIso_app f hc.isIso_app
  haveI : IsDominant π := hπb.isDominant
  haveI : IsDominant (f ≫ h) := by rw [hfh]; infer_instance
  haveI : IsDominant h := IsDominant.of_comp f h
  have hhs : h ≫ sZ = sW :=
    ext_of_isDominant f (by rw [← Category.assoc, hfh, hπ, hc.comp_eq])
  have h1 : topologicalKrullDim W ≤ topologicalKrullDim X :=
    topologicalKrullDim_le_of_isDominant f hc.comp_eq
  have h2 : topologicalKrullDim Z ≤ topologicalKrullDim W :=
    topologicalKrullDim_le_of_isDominant h hhs
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ
  haveI : MMP.Mori.IsVariety ℂ sX := hc.isVariety_source
  have h3 : topologicalKrullDim Z = topologicalKrullDim X :=
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hπb
  refine ⟨?_, hhs⟩
  exact (IsBirationalContraction.surjective_and_isBirational (k := ℂ)
    ⟨hc, (le_antisymm h1 (h3 ▸ h2)).symm⟩).2

/-- A birational morphism `f : X ⟶ W` is a modification of `f` into `𝟙_W`. -/
private theorem isModificationOf_id_of_isBirationalMorphism {X W : Scheme.{0}} (f : X ⟶ W)
    (hfb : IsBirationalMorphism f) : IsModificationOf f (𝟙 W) f.toRationalMap :=
  ⟨hfb, by rw [MMP.Flips.RationalMap.IsOver, toRationalMap_compHom, Category.comp_id]⟩

/-- The push-forward of a canonical divisor along a birational contraction onto a normal variety
is a canonical divisor. -/
private theorem isCanonicalDivisor_transformDivisor_of_isContraction {X W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {f : X ⟶ W} (hc : IsContraction ℂ sW sX f)
    (hXn : IsNormalVariety ℂ sX) (hWn : IsNormalVariety ℂ sW) (hfb : IsBirationalMorphism f)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sW n
      (MMP.Mori.RationalMap.transformDivisor f.toRationalMap K) := by
  haveI := hc.isProper
  haveI := hfb.isDominant
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ sW := hWn.1
  haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
  have hdim : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW sX hfb).trans hK.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sW hWn hdim
  have hsrc : IsNormalVariety ℂ (f ≫ sW) := hc.comp_eq ▸ hXn
  haveI : LocallyOfFiniteType (f ≫ sW) := by rw [hc.comp_eq]; infer_instance
  have hK' : K.IsCanonicalDivisor (f ≫ sW) n := hc.comp_eq ▸ hK
  exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hWn hsrc hfb hK₀ hK'

/-- A step of an extremal real flip sequence is a flip `φ = (f⁺)⁻¹ ∘ f` of `f` with respect to
`K + B`, which transforms divisors as `(f⁺)⁻¹_* f_*`. -/
private theorem exists_isFlip_of_isRealFlipStep {X W X' : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {f : X ⟶ W} {fp : X' ⟶ W} {K : Divisor X}
    {B : RDivisor X} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hstep : IsRealFlipStep sX sW sX' K B (flipTransform f fp K) (flipTransform f fp B) f fp)
    (hsmall : IsSmall ℂ sW sX f) :
    ∃ φ : X.RationalMap X', IsFlip ℂ sX sW sX' (logCanonicalDivisor K B) f fp φ ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  classical
  have hneg := hstep.isNegativeExtremalContraction
  have hsm' := hstep.isSmall_flip
  obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := hstep.exists_opens_isIso
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : IsProper fp := hsm'.isProper
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = sW ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsSeparated sX' := hsm'.isVariety_source.toIsSeparated
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := by
    rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  obtain ⟨em, hm⟩ := hstep.isBirationalMorphism
  obtain ⟨ep, hp⟩ := hstep.isBirationalMorphism_flip
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 W) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 W) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver f fp := h1.trans h2.symm
  have hover : MMP.Flips.RationalMap.IsOver f fp e.toRationalMap := by
    rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
    change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
      X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
    rw [Category.assoc, H]
    simp
  have hmod : IsModificationOf f fp e.toRationalMap := ⟨⟨e, rfl⟩, hover⟩
  have hXn : IsNormalVariety ℂ (f ≫ sW) := hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      MMP.Mori.RationalMap.transformDivisor e.toRationalMap D = flipTransform f fp D :=
    fun D => MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict
      hneg.isNormalVariety_target hXn hstep.isBirationalMorphism V hXV hX'V hover D
  have hKB : MMP.Mori.RationalMap.transformDivisor e.toRationalMap (logCanonicalDivisor K B) =
      logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B) := by
    rw [transformDivisor_logCanonicalDivisor, htr, htr]
  have hamp := hstep.isRelativelyAmple_flip
  refine ⟨e.toRationalMap,
    { isNormalVariety_source := hneg.isNormalVariety_source
      isNormalVariety_target := hneg.isNormalVariety_target
      isNormalVariety_flip := ⟨hsm'.isVariety_source, inferInstance⟩
      isContraction := hneg.isContraction
      isCartierCombination := hneg.isCartierCombination
      isRelativelyAntiAmple := hneg.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver
        hneg.isNormalVariety_source f fp _ hover
      isSmall := hsm'
      isCartierCombination_transform := by
        rw [hKB]
        obtain ⟨m, r, L, -, -, hL, hD⟩ := hamp
        exact ⟨m, r, L, fun j => (hL j).1, hD⟩
      isRelativelyAmple_transform := by rw [hKB]; exact hamp
      isSmall_source := hsmall }, htr⟩

/-- **FA 6.5 for the biregular exceptional set.** For a divisorial extremal contraction the
biregular exceptional set `X ∖ φ⁻¹(V_φ)` is the prime divisor of FA 6.5: it contains the
exceptional set `Ex(φ)` of points where `φ` is not locally an open immersion, and each of its
closed points lies on a curve `C` contracted by `φ`, which meets no open set on which `φ` is an
open immersion, since `C` would be a single point there. -/
private theorem exists_primeDivisor_moriExceptionalSet_eq_support_of_not_isSmall' {k : Type}
    [Field k] {V W : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsLocallyNoetherian V] [IsNormal V] (hV : IsQFactorial sV) (hW : IsNormalVariety k sW)
    (φ : V ⟶ W) (hφ : IsBirationalContraction k sW sV φ) (hφp : IsProjectiveMorphism φ)
    (hρ : MMP.Flips.relativePicardNumber sV φ = 1) (hs : ¬ IsSmall k sW sV φ) :
    ∃ F : MMP.Mori.PrimeDivisor V, (MMP.Mori.exceptionalSet φ : Set V) = F.support := by
  obtain ⟨F, hF⟩ := MMP.Flips.exists_primeDivisor_exceptionalSet_eq_support_of_not_isSmall sV sW
    hV hW φ hφ hφp hρ hs
  refine ⟨F, ?_⟩
  rw [← hF]
  haveI : IsIntegral V := hV.1.1.toIsIntegral
  haveI := hφ.isProper
  haveI : LocallyOfFiniteType sV := hV.1.1.toLocallyOfFiniteType
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hbir := hφ.surjective_and_isBirational.2
  refine subset_antisymm ?_ fun y hy => ?_
  · rw [← closure_inter_closedPoints (MMP.Mori.exceptionalSet φ).isClosed]
    refine closure_minimal (fun x ⟨hx, hxc⟩ => ?_) (MMP.Flips.isClosed_exceptionalSet φ)
    obtain ⟨C, hCc, hCi, hCd, hxC, y, hy⟩ :=
      MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hV.1.1 hW.1 φ
        hφ.comp_eq hbir hφ.isIso_app (mem_closedPoints_iff.mp hxc) hx
    by_contra hxF
    obtain ⟨U, hxU, hU⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hxF
    have hsub : C ∩ (U : Set V) ⊆ {x} := fun z ⟨hzC, hzU⟩ => by
      have h1 : φ z ∈ φ '' C := ⟨z, hzC, rfl⟩
      have h2 : φ x ∈ φ '' C := ⟨x, hxC, rfl⟩
      rw [hy] at h1 h2
      have := (U.ι ≫ φ).isOpenEmbedding.injective (a₁ := ⟨z, hzU⟩) (a₂ := ⟨x, hxU⟩)
        (h1.trans h2.symm)
      exact congrArg Subtype.val this
    have hCx : C ⊆ {x} :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hCi.2 U.isOpen ⟨x, hxC, hxU⟩).trans
        ((closure_mono hsub).trans (mem_closedPoints_iff.mp hxc).closure_subset)
    have : Subsingleton C := Set.Subsingleton.coe_sort fun a ha b hb =>
      (hCx ha).trans (hCx hb).symm
    have : DiscreteTopology C := ⟨Subsingleton.elim _ _⟩
    exact absurd (hCd ▸ topologicalKrullDim_zero_of_discreteTopology C) (by decide)
  · by_contra hyM
    apply hy
    have : IsIso (φ ∣_ biregularLocus φ) := MMP.Mori.isBiregular_biregularLocus φ
    refine ⟨φ ⁻¹ᵁ biregularLocus φ, ?_, ?_⟩
    · by_contra h
      exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
    · rw [← morphismRestrict_ι]
      infer_instance

/-- A model of a program over `Z`: a normal integral locally noetherian quasi-compact scheme over
`ℂ` and over `Z`, with a canonical divisor and two real divisors. -/
private structure Model (Z : Scheme.{0}) where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  s : X ⟶ Spec (.of ℂ)
  π : X ⟶ Z
  K : Divisor X
  B : RDivisor X
  C : RDivisor X

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

/-- The nef levels `{t ≥ 0 | K + B + t C is nef over Z}` of a model. -/
private def Model.nefLevels {Z : Scheme.{0}} (M : Model Z) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K (M.B + t • M.C))}

/-- A model is *good at level `μ`*: a projective `ℚ`-factorial fourfold birational over `Z`
with canonical divisor `K`, `B, C ≥ 0`, `(X, B)` dlt, `μ > 0`, `(X, B + μ C)` lc and
`K + B + μ C` nef over `Z`. -/
private def Model.Good {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) (μ : ℝ) : Prop :=
  M.π ≫ sZ = M.s ∧ MMP.Mori.IsProjectiveVariety ℂ M.s ∧ IsQFactorial M.s ∧
    M.K.IsCanonicalDivisor M.s 4 ∧ (∀ P, 0 ≤ M.B.coeff P) ∧ (∀ P, 0 ≤ M.C.coeff P) ∧ 0 < μ ∧
    IsRealDltPair M.s M.B ∧ IsRealLcPair M.s (M.B + μ • M.C) ∧
    IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K (M.B + μ • M.C)) ∧
    IsBirationalMorphism M.π

/-- The data of one step of a program with scaling out of a model `M`: the threshold `t`, the
contraction `f : M ⟶ W` over `Z` (by `g`), the next model `M'` with `f⁺ : M' ⟶ W` and the
birational map `φ : M ⤏ M'`. -/
private structure StepOut {Z : Scheme.{0}} (M : Model Z) where
  t : ℝ
  W : Scheme.{0}
  sW : W ⟶ Spec (.of ℂ)
  f : M.X ⟶ W
  g : W ⟶ Z
  M' : Model Z
  fp : M'.X ⟶ W
  φ : M.X.RationalMap M'.X

/-- The conditions on a step: `t` is the nef threshold, `f` is a `(K + B)`-negative extremal
contraction over `Z` onto a projective variety, null for `K + B + t C`; the step is a divisorial
contraction or a flip, the next model is good at level `t`, and the boundaries are the birational
transforms. -/
private def StepOut.IsStep {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {M : Model Z}
    (o : StepOut M) : Prop :=
  IsLeast M.nefLevels o.t ∧ MMP.Mori.IsProjectiveVariety ℂ o.sW ∧ o.f ≫ o.g = M.π ∧
    o.fp ≫ o.g = o.M'.π ∧
    IsNegativeExtremalContraction ℂ M.s o.sW (logCanonicalDivisor M.K M.B) o.f ∧
    IsNumericallyTrivialOver ℂ M.s o.f (logCanonicalDivisor M.K (M.B + o.t • M.C)) ∧
    ((IsBirationalMorphism o.f ∧
        (∃ E : MMP.Mori.PrimeDivisor M.X,
          (MMP.Mori.exceptionalSet o.f : Set M.X) = E.support) ∧
        IsIso o.fp ∧ IsModificationOf o.f o.fp o.φ) ∨
      IsFlip ℂ M.s o.sW o.M'.s (logCanonicalDivisor M.K M.B) o.f o.fp o.φ) ∧
    o.M'.B = MMP.Mori.RationalMap.transformDivisor o.φ M.B ∧
    o.M'.C = MMP.Mori.RationalMap.transformDivisor o.φ M.C ∧
    o.M'.Good sZ o.t

/-- **The step out of a good model whose adjoint is not nef.** The nef threshold `t ∈ (0, μ]`
of `C` comes with a `(K + B)`-negative extremal ray null for `K + B + t C`; its contraction is
birational (the base is birational over `Z`), hence divisorial or small (FA 6.5), and the
divisorial contraction or the flip gives the next model, good at level `t`. -/
private theorem exists_stepOut {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {M : Model Z} {μ : ℝ} (hM : M.Good sZ μ)
    (hnot : ¬ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B)) :
    ∃ o : StepOut M, o.IsStep sZ := by
  classical
  obtain ⟨hπ, hproj, hq, hK4, hB, hC, hμ, hdlt, hlc, hnefμ, hπb⟩ := hM
  haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
  haveI : QuasiCompact M.s := hproj.toIsVariety.toQuasiCompact
  have hXn : IsNormalVariety ℂ M.s := hq.1
  -- the nef threshold and its ray
  obtain ⟨l, hl0, hlμ, hnefl, hKBc, -, R, hR, hnull, hneg, hpos⟩ :=
    exists_isExtremalRay_nef_threshold_of_isRealLcPair hproj hZ hπ hq hK4 hB hC hμ hlc hnefμ hnot
  -- a presentation of `K + B`, negative on `R`
  have hneg' : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor M.X) (hL : ∀ j, (L j).IsCartier),
      logCanonicalDivisor M.K M.B = ∑ j, r j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 → ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree M.s M.π (L j).divisorialSheaf u) < 0 := by
    obtain ⟨m, r, L, hL, hD⟩ := hKBc
    have heq : logCanonicalDivisor M.K M.B = ∑ j, r j • Divisor.toRDivisor (L j) := by
      refine Finsupp.ext fun P => ?_
      change (logCanonicalDivisor M.K M.B).coeff P = (∑ j, r j • Divisor.toRDivisor (L j)).coeff P
      rw [show logCanonicalDivisor M.K M.B = Divisor.toRDivisor M.K + M.B from rfl, hD P]
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
      rfl
    exact ⟨m, r, L, hL, heq, fun u hu hu0 => hneg m r L hL heq u hu hu0⟩
  have hdim : topologicalKrullDim M.X = 4 := by rw [hK4.1]; rfl
  -- the elementary step of the ray
  obtain ⟨W, iW, cW, lW, nW, sW, f, h, hcontr, hWproj, hnegext, -, hdiv, hsmall⟩ :=
    IsRealDltPair.exists_isRelativeContractionOfFace_of_isExtremalRay hproj hZ hπ hq hdim
      ⟨4, hK4⟩ hdlt hR hneg'
  have hcomm : f ≫ h = M.π := hcontr.comp_eq
  obtain ⟨hfb, hhs⟩ := isBirationalMorphism_of_isContraction hnegext.isContraction hcomm hπ hπb
    hZ.toIsVariety
  have hWn : IsNormalVariety ℂ sW := hnegext.isNormalVariety_target
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ sZ) := by rw [hhs]; infer_instance
  haveI : LocallyOfFiniteType h := LocallyOfFiniteType.of_comp (f := h) (g := sZ) inferInstance
  have hhb : IsBirationalMorphism h :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left f h hfb (hcomm ▸ hπb)
  -- curves contracted by `f` are contracted by `π`, with class in `R`
  have hRf : ∀ Γ : ProperCurve M.s, Γ.IsContractedBy f →
      ∃ hΓ : Γ.IsContractedBy M.π, Γ.relativeClass M.π hΓ ∈ R := by
    intro Γ hΓ
    have hΓπ : Γ.IsContractedBy M.π := by
      rw [← hcomm]
      intro x hx
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ x hx]
    exact ⟨hΓπ, (hcontr.isContractedBy_iff Γ hΓπ).mp hΓ⟩
  have hnullC : ∀ (Γ : ProperCurve M.s) (hΓ : Γ.IsContractedBy M.π),
      Γ.relativeClass M.π hΓ ∈ R → ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor M.X) (x : ℝ),
        IsRIntersectionNumber ℂ M.s (logCanonicalDivisor M.K (M.B + l • M.C)) r L Γ x →
          x = 0 :=
    fun Γ hΓ hΓR m r L x hx => isRIntersectionNumber_of_degree Γ hΓ (· = 0)
      (fun n c N hN hD => hnull n c N hN hD _ hΓR) hx
  -- a contracted curve
  obtain ⟨Γ, hΓ⟩ :=
    exists_isContractedBy_of_relativePicardNumber_eq_one f hnegext.relativePicardNumber_eq_one
  obtain ⟨hΓπ, hΓR⟩ := hRf Γ hΓ
  have hΓ0 : Γ.relativeClass M.π hΓπ ≠ 0 := by
    intro h0
    obtain ⟨m', r', L', hL', hN'⟩ := hnegext.isCartierCombination
    have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ M.s Γ r' L' hL'
    have hN'' : logCanonicalDivisor M.K M.B = ∑ i, r' i • Divisor.toRDivisor (L' i) := by
      rw [hN']
      simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    rw [← hN''] at hy
    have hlt := isRIntersectionNumber_neg_of_isRelativelyAntiAmple f
      hnegext.isRelativelyAntiAmple Γ hΓ r' L' _ hy
    have h00 := isRIntersectionNumber_of_degree Γ hΓπ (· = 0)
      (fun n c N hN _ => by simp [h0]) hy
    exact (lt_irrefl _ (h00 ▸ hlt))
  have hposC : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor M.X) (x : ℝ),
      IsRIntersectionNumber ℂ M.s M.C r L Γ x → 0 < x :=
    fun m r L x hx => isRIntersectionNumber_of_degree Γ hΓπ (0 < ·)
      (fun n c N hN hD => hpos n c N hN hD _ hΓR hΓ0) hx
  have hleast : IsLeast M.nefLevels l :=
    isLeast_of_null hq hl0.le hnefl Γ hΓπ (hnullC Γ hΓπ hΓR) hposC
  have htriv : IsNumericallyTrivialOver ℂ M.s f (logCanonicalDivisor M.K (M.B + l • M.C)) :=
    isNumericallyTrivialOver_of_null (isCartierCombination_of_isQFactorial hq _)
      fun Γ' hΓ' m r L x hx => by
        obtain ⟨hΓ'π, hΓ'R⟩ := hRf Γ' hΓ'
        exact hnullC Γ' hΓ'π hΓ'R m r L x hx
  -- `(X, B + l C)` is lc
  have hlcl : IsRealLcPair M.s (M.B + l • M.C) := by
    have h := isRealLcPair_segment hq hdlt.1 hlc (s := l / μ) (by positivity)
      ((div_le_one hμ).2 hlμ)
    convert h using 1
    rw [smul_add, smul_smul, div_mul_cancel₀ l hμ.ne']
    module
  have hlin : ∀ (φ : M.X.RationalMap W) , MMP.Mori.RationalMap.transformDivisor φ (M.B + l • M.C) =
      MMP.Mori.RationalMap.transformDivisor φ M.B +
        l • MMP.Mori.RationalMap.transformDivisor φ M.C := fun φ => by
    rw [map_add, transformDivisor_smul]
  by_cases hsm : IsSmall ℂ sW M.s f
  · -- the flip
    obtain ⟨X', iI, iC, iL, iN, sX', fp, hstep, hX'proj, hX'q, hX'dim, hX'dlt, -, hX'⟩ :=
      hsmall hsm
    obtain ⟨φ, hflip, htr⟩ := exists_isFlip_of_isRealFlipStep hWproj hstep hsm
    have hsm' := hstep.isSmall_flip
    obtain ⟨hlc', hnef'⟩ := hX' (M.B + l • M.C) hlcl hnefl (hnullC)
    let M' : Model Z :=
      { X := X', s := sX', π := fp ≫ h,
        K := MMP.Mori.RationalMap.transformDivisor φ M.K,
        B := MMP.Mori.RationalMap.transformDivisor φ M.B,
        C := MMP.Mori.RationalMap.transformDivisor φ M.C }
    have hlinφ : MMP.Mori.RationalMap.transformDivisor φ (M.B + l • M.C) =
        M'.B + l • M'.C := by
      rw [map_add, transformDivisor_smul]
    rw [← htr, hlinφ] at hlc'
    rw [← htr, ← htr, hlinφ] at hnef'
    obtain ⟨m, hm⟩ := hstep.isCanonicalDivisor_flip
    have hm4 : m = 4 := by
      have := hm.1.symm.trans hX'dim
      exact_mod_cast this
    subst hm4
    rw [← htr] at hm hX'dlt
    have hfpb : IsBirationalMorphism fp := hsm'.isBirationalMorphism
    refine ⟨⟨l, W, sW, f, h, M', fp, φ⟩, hleast, hWproj, hcomm, rfl, hnegext, htriv,
      Or.inr hflip, rfl, rfl, ?_⟩
    refine ⟨?_, hX'proj, hX'q, hm, fun P => transformDivisor_nonneg φ hB P,
      fun P => transformDivisor_nonneg φ hC P, hl0, hX'dlt, hlc', hnef', ?_⟩
    · change (fp ≫ h) ≫ sZ = sX'
      rw [Category.assoc, hhs, hsm'.comp_eq]
    · exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hfpb hhb
  · -- the divisorial contraction
    haveI : IsProper f := hnegext.isContraction.isProper
    haveI : MMP.Mori.IsVariety ℂ sW := hWn.1
    haveI : MMP.Mori.IsVariety ℂ M.s := hXn.1
    have hbc : IsBirationalContraction ℂ sW M.s f :=
      ⟨hnegext.isContraction,
        (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW M.s hfb).symm⟩
    have hfp : IsProjectiveMorphism f := by
      haveI : IsSeparated sW := hWn.1.toIsSeparated
      refine IsProjectiveMorphism.of_comp f sW ?_
      rw [hnegext.isContraction.comp_eq]
      exact hproj.isProjective
    obtain ⟨E, hE⟩ := exists_primeDivisor_moriExceptionalSet_eq_support_of_not_isSmall'
      M.s sW hq hWn f hbc hfp hnegext.relativePicardNumber_eq_one hsm
    obtain ⟨hWq, hWdlt, hW'⟩ := hdiv ⟨hfb, E, hE⟩
    obtain ⟨hlc', hnef'⟩ := hW' (M.B + l • M.C) hlcl hnefl hnullC
    rw [hlin] at hlc' hnef'
    let M' : Model Z :=
      { X := W, s := sW, π := h,
        K := MMP.Mori.RationalMap.transformDivisor f.toRationalMap M.K,
        B := MMP.Mori.RationalMap.transformDivisor f.toRationalMap M.B,
        C := MMP.Mori.RationalMap.transformDivisor f.toRationalMap M.C }
    refine ⟨⟨l, W, sW, f, h, M', 𝟙 W, f.toRationalMap⟩, hleast, hWproj, hcomm,
      Category.id_comp h, hnegext, htriv,
      Or.inl ⟨hfb, ⟨E, hE⟩, inferInstance, isModificationOf_id_of_isBirationalMorphism f hfb⟩,
      rfl, rfl, ?_⟩
    exact ⟨hhs, hWproj, hWq,
      isCanonicalDivisor_transformDivisor_of_isContraction hnegext.isContraction hXn hWn hfb hK4,
      fun P => transformDivisor_nonneg _ hB P, fun P => transformDivisor_nonneg _ hC P, hl0,
      hWdlt, hlc', hnef', hhb⟩

/-- The step which does nothing. -/
private def StepOut.trivial {Z : Scheme.{0}} (M : Model Z) : StepOut M :=
  ⟨0, M.X, M.s, 𝟙 _, M.π, M, 𝟙 _, Scheme.RationalMap.id M.X⟩

open Classical in
/-- The chosen step out of a model. -/
private noncomputable def advance {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) :
    StepOut M :=
  if h : ∃ o : StepOut M, o.IsStep sZ then h.choose else StepOut.trivial M

private theorem advance_spec {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {M : Model Z} {μ : ℝ} (hM : M.Good sZ μ)
    (hnot : ¬ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B)) :
    (advance sZ M).IsStep sZ := by
  have h := exists_stepOut hZ hM hnot
  rw [advance, dif_pos h]
  exact h.choose_spec

/-- The birational map of the chosen step is birational. -/
private theorem advance_isBirational {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) :
    MMP.Mori.RationalMap.IsBirational (advance sZ M).φ := by
  classical
  by_cases h : ∃ o : StepOut M, o.IsStep sZ
  · rw [advance, dif_pos h]
    obtain ⟨-, -, -, -, -, -, hc, -⟩ := h.choose_spec
    rcases hc with ⟨-, -, -, hmod⟩ | hflip
    · exact hmod.1
    · exact hflip.isModificationOf.1
  · rw [advance, dif_neg h]
    exact MMP.Mori.RationalMap.isBirational_id

/-- The models of the chosen program with scaling. -/
private noncomputable def models {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) :
    ℕ → Model Z
  | 0 => M₀
  | i + 1 => (advance sZ (models sZ M₀ i)).M'

/-- The levels of the chosen program: `1`, then the thresholds. -/
private noncomputable def levels {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) :
    ℕ → ℝ
  | 0 => 1
  | i + 1 => (advance sZ (models sZ M₀ i)).t

/-- The adjoint `K + B` of a model is nef over `Z`. -/
private def Model.IsNef {Z : Scheme.{0}} (M : Model Z) : Prop :=
  IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B)

private theorem good_models {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {M₀ : Model Z} (h₀ : M₀.Good sZ 1) :
    ∀ i, (∀ j < i, ¬ (models sZ M₀ j).IsNef) → (models sZ M₀ i).Good sZ (levels sZ M₀ i)
  | 0, _ => h₀
  | i + 1, h => by
    have hi := good_models hZ h₀ i fun j hj => h j (Nat.lt_succ_of_lt hj)
    exact (advance_spec hZ hi (h i (Nat.lt_succ_self i))).2.2.2.2.2.2.2.2.2

/-- The models after the first, as a family `Y`. -/
private noncomputable abbrev progY {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) (i : ℕ) :
    Scheme.{0} :=
  (models sZ M₀ (i + 1)).X

/-- The contractions of the chosen program, on `X₀ = X, X₁ = Y₀, …`. -/
private noncomputable def progF {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) :
    ∀ i, modelSeq M₀.X (progY sZ M₀) i ⟶ (advance sZ (models sZ M₀ i)).W
  | 0 => (advance sZ (models sZ M₀ 0)).f
  | j + 1 => (advance sZ (models sZ M₀ (j + 1))).f

/-- The birational maps of the chosen program. -/
private noncomputable def progφ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) :
    ∀ i, (modelSeq M₀.X (progY sZ M₀) i).RationalMap (progY sZ M₀ i)
  | 0 => (advance sZ (models sZ M₀ 0)).φ
  | j + 1 => (advance sZ (models sZ M₀ (j + 1))).φ

/-- A good model of the chosen program satisfies the conditions on the models. -/
private theorem isModelAt_prog {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z)
    (i : ℕ) {μ : ℝ} (h : (models sZ M₀ i).Good sZ μ) :
    IsModelAt (X := M₀.X) (Y := progY sZ M₀) M₀.s sZ M₀.π M₀.K M₀.B (fun i => (models sZ M₀ (i +
        1)).s)
      (fun i => (models sZ M₀ (i + 1)).π) (fun i => (models sZ M₀ (i + 1)).K)
      (fun i => (models sZ M₀ (i + 1)).B) i := by
  cases i with
  | zero => exact ⟨h.1, h.2.1, h.2.2.1, ⟨4, h.2.2.2.1⟩, h.2.2.2.2.1⟩
  | succ j => exact ⟨h.1, h.2.1, h.2.2.1, ⟨4, h.2.2.2.1⟩, h.2.2.2.2.1⟩

/-- A chosen step of the program satisfies the conditions on the steps. -/
private theorem isStepAt_prog {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z)
    (i : ℕ) (h : (advance sZ (models sZ M₀ i)).IsStep sZ) :
    IsStepAt (X := M₀.X) (Y := progY sZ M₀) M₀.s M₀.π M₀.K M₀.B M₀.C (fun i => (models sZ M₀ (i +
        1)).s)
      (fun i => (models sZ M₀ (i + 1)).π) (fun i => (models sZ M₀ (i + 1)).K)
      (fun i => (models sZ M₀ (i + 1)).B) (fun i => (models sZ M₀ (i + 1)).C)
      (fun i => (advance sZ (models sZ M₀ i)).t) (fun i => (advance sZ (models sZ M₀ i)).sW)
      (progF sZ M₀) (fun i => (advance sZ (models sZ M₀ i)).g)
      (fun i => (advance sZ (models sZ M₀ i)).fp) (progφ sZ M₀) i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  cases i with
  | zero => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  | succ j => exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The adjoint of a model of the chosen program, as a model of the program. -/
private theorem isNef_prog {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z)
    (i : ℕ) (h : (models sZ M₀ i).IsNef) :
    IsRelativelyNef ℂ (modelStr (X := M₀.X) (Y := progY sZ M₀) M₀.s (fun i => (models sZ M₀ (i +
        1)).s) i)
      (modelMap (X := M₀.X) (Y := progY sZ M₀) M₀.π (fun i => (models sZ M₀ (i + 1)).π) i)
      (logCanonicalDivisor (divisorSeq (X := M₀.X) (Y := progY sZ M₀) M₀.K (fun i => (models sZ M₀
          (i + 1)).K) i)
        (divisorSeq (X := M₀.X) (Y := progY sZ M₀) M₀.B (fun i => (models sZ M₀ (i + 1)).B) i)) :=
            by
  cases i with
  | zero => exact h
  | succ j => exact h

/-- The level adjoint of a good model of the chosen program is nef. -/
private theorem isNef_level_prog {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z)
    (i : ℕ) {μ : ℝ} (h : (models sZ M₀ i).Good sZ μ) :
    IsRelativelyNef ℂ (modelStr (X := M₀.X) (Y := progY sZ M₀) M₀.s (fun i => (models sZ M₀ (i +
        1)).s) i)
      (modelMap (X := M₀.X) (Y := progY sZ M₀) M₀.π (fun i => (models sZ M₀ (i + 1)).π) i)
      (logCanonicalDivisor (divisorSeq (X := M₀.X) (Y := progY sZ M₀) M₀.K (fun i => (models sZ M₀
          (i + 1)).K) i)
        (divisorSeq (X := M₀.X) (Y := progY sZ M₀) M₀.B (fun i => (models sZ M₀ (i + 1)).B) i +
          μ • divisorSeq (X := M₀.X) (Y := progY sZ M₀) M₀.C (fun i => (models sZ M₀ (i + 1)).C)
              i)) := by
  cases i with
  | zero => exact h.2.2.2.2.2.2.2.2.2.1
  | succ j => exact h.2.2.2.2.2.2.2.2.2.1

/-- The birational maps of the chosen program are birational. -/
private theorem progφ_isBirational {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z)
    (i : ℕ) :
    MMP.Mori.RationalMap.IsBirational (progφ sZ M₀ i) := by
  cases i with
  | zero => exact advance_isBirational sZ _
  | succ j => exact advance_isBirational sZ _

end ExistenceProgram

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

private theorem finite_of_isScalingProgram
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 4)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) :
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤  := by
  intro n Y sY _ _ _ _ πY KY BY CY lam W sW f g fp φ hM hS hn
  subst hn
  have hBn : ∀ i, ∀ P, 0 ≤ (divisorSeq B BY i).coeff P := by
    intro i
    induction i with
    | zero => exact hB
    | succ i ih =>
      intro P
      rw [show divisorSeq B BY (i + 1) = BY i from rfl,
        (hS i (ENat.coe_lt_top i)).2.2.2.2.2.2.2.1]
      exact transformDivisor_nonneg _ ih P
  exact false_of_forall_isStepAt
    (fun i => ⟨(hM i le_top).1, (hM i le_top).2.1, (hM i le_top).2.2.1, (hM i le_top).2.2.2.1,
      hBn i⟩)
    (fun i => hS i (ENat.coe_lt_top i)) (fun i => (hM i le_top).2.2.2.2)
    hπ hX hZ hZn hπp hπb hXq hK hB hC hBc hCc hklt hnef

private theorem exists_scalingProgram
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 4)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) :
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n))) := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  let M₀ : Model Z := { X := X, s := sX, π := π, K := K, B := B, C := C }
  have hBk : IsRealKltPair sX B := IsRealKltPair.of_le hXq (fun P => by
    rw [DivisorWithCoeffs.coeff_add]; linarith [hC P]) hklt
  have hBC : ∀ P, 0 ≤ (B + C).coeff P := fun P => by
    rw [DivisorWithCoeffs.coeff_add]; linarith [hB P, hC P]
  have h₀ : M₀.Good sZ 1 := by
    refine ⟨hπ, hX, hXq, hK, hB, hC, one_pos, isRealDltPair_of_isRealKltPair hB hBk, ?_, ?_, hπb⟩
    · rw [one_smul]
      exact ⟨hklt.1, hBC, hklt.2.2.1, fun n E a ha => (hklt.2.2.2 n E a ha).le⟩
    · rw [one_smul]; exact hnef
  -- the levels are at most one and decrease
  have hlev : ∀ i, (∀ j < i, ¬ (models sZ M₀ j).IsNef) →
      levels sZ M₀ i ≤ 1 ∧ ∀ j < i, levels sZ M₀ i ≤ (advance sZ (models sZ M₀ j)).t := by
    intro i
    induction i with
    | zero => intro _; exact ⟨le_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ i ih =>
      intro h
      obtain ⟨ih1, ih2⟩ := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
      have hgi := good_models hZ h₀ i fun j hj => h j (Nat.lt_succ_of_lt hj)
      have hst := advance_spec hZ hgi (h i (Nat.lt_succ_self i))
      have hti : (advance sZ (models sZ M₀ i)).t ≤ levels sZ M₀ i :=
        hst.1.2 ⟨hgi.2.2.2.2.2.2.1.le, hgi.2.2.2.2.2.2.2.2.2.1⟩
      refine ⟨hti.trans ih1, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hti.trans (ih2 j hj)
      · exact le_rfl
  by_cases hfin : ∃ n, (models sZ M₀ n).IsNef
  · -- the program stops at the first nef model
    set n := Nat.find hfin with hndef
    have hn : (models sZ M₀ n).IsNef := Nat.find_spec hfin
    have hlt : ∀ j < n, ¬ (models sZ M₀ j).IsNef := fun j hj => Nat.find_min hfin hj
    have hgood : ∀ i ≤ n, (models sZ M₀ i).Good sZ (levels sZ M₀ i) :=
      fun i hi => good_models hZ h₀ i fun j hj => hlt j (by omega)
    have hMb : ∀ i : ℕ, (i : ℕ∞) ≤ (n : ℕ∞) → IsModelAt (X := M₀.X) (Y := progY sZ M₀) M₀.s sZ
        M₀.π M₀.K M₀.B (fun i => (models sZ M₀ (i + 1)).s) (fun i => (models sZ M₀ (i + 1)).π)
        (fun i => (models sZ M₀ (i + 1)).K) (fun i => (models sZ M₀ (i + 1)).B) i :=
      fun i hi => isModelAt_prog sZ M₀ i (hgood i (by exact_mod_cast hi))
    have hSb : ∀ i : ℕ, (i : ℕ∞) < (n : ℕ∞) → IsStepAt (X := M₀.X) (Y := progY sZ M₀) M₀.s M₀.π
        M₀.K M₀.B M₀.C (fun i => (models sZ M₀ (i + 1)).s) (fun i => (models sZ M₀ (i + 1)).π)
        (fun i => (models sZ M₀ (i + 1)).K) (fun i => (models sZ M₀ (i + 1)).B)
        (fun i => (models sZ M₀ (i + 1)).C) (fun i => (advance sZ (models sZ M₀ i)).t)
        (fun i => (advance sZ (models sZ M₀ i)).sW) (progF sZ M₀)
        (fun i => (advance sZ (models sZ M₀ i)).g) (fun i => (advance sZ (models sZ M₀ i)).fp)
        (progφ sZ M₀) i := fun i hi => by
      have hi' : i < n := by exact_mod_cast hi
      exact isStepAt_prog sZ M₀ i (advance_spec hZ (hgood i hi'.le) (hlt i hi'))
    have hlevn := fun i (hi : i ≤ n) => hlev i fun j hj => hlt j (by omega)
    refine ⟨n, progY sZ M₀, fun i => (models sZ M₀ (i + 1)).s, fun i => inferInstance,
      fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
      fun i => (models sZ M₀ (i + 1)).π, fun i => (models sZ M₀ (i + 1)).K,
      fun i => (models sZ M₀ (i + 1)).B, fun i => (models sZ M₀ (i + 1)).C,
      fun i => (advance sZ (models sZ M₀ i)).t, fun i => (advance sZ (models sZ M₀ i)).W,
      fun i => (advance sZ (models sZ M₀ i)).sW, progF sZ M₀,
      fun i => (advance sZ (models sZ M₀ i)).g, fun i => (advance sZ (models sZ M₀ i)).fp,
      progφ sZ M₀, fun i hi => ?_, fun i hi => hSb i (by exact_mod_cast hi),
      isNef_prog sZ M₀ n hn⟩
    have hMi := hMb i (by exact_mod_cast hi)
    refine ⟨hMi.1, hMi.2.1, hMi.2.2.1, hMi.2.2.2.1, ?_⟩
    exact isRealKltPair_divisorSeq hMb hSb (progφ_isBirational sZ M₀) hπ hX hZ hZn hπb hXq hK hC
      hklt i (by exact_mod_cast hi) (hgood i hi).2.2.2.2.2.2.1.le (hlevn i hi).1 (hlevn i hi).2
      (isNef_level_prog sZ M₀ i (hgood i hi))
  · -- an infinite program is impossible
    push Not at hfin
    exfalso
    have hgood : ∀ i, (models sZ M₀ i).Good sZ (levels sZ M₀ i) :=
      fun i => good_models hZ h₀ i fun j _ => hfin j
    have hMb : ∀ i : ℕ, (i : ℕ∞) ≤ (⊤ : ℕ∞) → IsModelAt (X := M₀.X) (Y := progY sZ M₀) M₀.s sZ
        M₀.π M₀.K M₀.B (fun i => (models sZ M₀ (i + 1)).s) (fun i => (models sZ M₀ (i + 1)).π)
        (fun i => (models sZ M₀ (i + 1)).K) (fun i => (models sZ M₀ (i + 1)).B) i :=
      fun i _ => isModelAt_prog sZ M₀ i (hgood i)
    have hSb : ∀ i : ℕ, (i : ℕ∞) < (⊤ : ℕ∞) → IsStepAt (X := M₀.X) (Y := progY sZ M₀) M₀.s M₀.π
        M₀.K M₀.B M₀.C (fun i => (models sZ M₀ (i + 1)).s) (fun i => (models sZ M₀ (i + 1)).π)
        (fun i => (models sZ M₀ (i + 1)).K) (fun i => (models sZ M₀ (i + 1)).B)
        (fun i => (models sZ M₀ (i + 1)).C) (fun i => (advance sZ (models sZ M₀ i)).t)
        (fun i => (advance sZ (models sZ M₀ i)).sW) (progF sZ M₀)
        (fun i => (advance sZ (models sZ M₀ i)).g) (fun i => (advance sZ (models sZ M₀ i)).fp)
        (progφ sZ M₀) i :=
      fun i _ => isStepAt_prog sZ M₀ i (advance_spec hZ (hgood i) (hfin i))
    have hlevi := fun i => hlev i fun j _ => hfin j
    exact false_of_forall_isStepAt (fun i => hMb i le_top) (fun i => hSb i (ENat.coe_lt_top i))
      (fun i => isRealKltPair_divisorSeq hMb hSb (progφ_isBirational sZ M₀) hπ hX hZ hZn hπb hXq
        hK hC hklt i le_top (hgood i).2.2.2.2.2.2.1.le (hlevi i).1 (hlevi i).2
        (isNef_level_prog sZ M₀ i (hgood i)))
      hπ hX hZ hZn hπp hπb hXq hK hB hC hBc hCc hklt hnef

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 4)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) :
    -- existence of a program with scaling, ending with a nef adjoint
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n))) ∧
    -- finiteness of every program with scaling
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤  :=
  ⟨exists_scalingProgram sX sZ π hπ hX hZ hZn hπp hπb hXq K hK B C hB hC hBc hCc hklt hnef,
    finite_of_isScalingProgram sX sZ π hπ hX hZ hZn hπp hπb hXq K hK B C hB hC hBc hCc hklt hnef⟩

end Proof_thm_fourfold_real_birational_fourfold_scaling_termination

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Real klt fourfold program with scaling over a birational base.** Let `π : X ⟶ Z` be a
projective birational morphism of projective complex varieties, `Z` normal and `X` a
`ℚ`-factorial fourfold with canonical divisor `K`, and let `B, C ≥ 0` be `ℝ`-Cartier divisors with
`(X, B + C)` klt and `K + B + C` nef over `Z`. Then there is a `(K + B)`-program over `Z` with
scaling of `C` with finitely many steps whose last model has `K_n + B_n` nef over `Z`, and every
`(K + B)`-program over `Z` with scaling of `C` has finitely many steps. -/
@[mmp "thm_fourfold_real_birational_fourfold_scaling_termination"]
public theorem exists_scalingProgram_and_finite_of_isBirationalMorphism
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hZn : IsNormalVariety ℂ sZ) (hπp : IsProjectiveMorphism π) (hπb : IsBirationalMorphism π)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 4)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C))) :
    -- existence of a program with scaling, ending with a nef adjoint
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
        (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n))) ∧
    -- finiteness of every program with scaling
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤ :=
        by revert X Z sX sZ π hπ hX hZ hZn hπp hπb hXq K hK B C hB hC hBc hCc hklt hnef; first | exact Proof_thm_fourfold_real_birational_fourfold_scaling_termination.solution | exact Proof_thm_fourfold_real_birational_fourfold_scaling_termination.solution _ | exact Proof_thm_fourfold_real_birational_fourfold_scaling_termination.solution _ _ | exact Proof_thm_fourfold_real_birational_fourfold_scaling_termination.solution _ _ _ | exact Proof_thm_fourfold_real_birational_fourfold_scaling_termination.solution _ _ _ _

end MMP.Fourfold

