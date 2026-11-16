module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.KltFlipTermination
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipPreservesCanonical

/-!
# Termination of effective-divisor flops on a projective klt threefold

Let `(X, B)` be an effective klt pair with `ℚ`-boundary on a normal projective `ℚ`-factorial
complex threefold and let `H ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor on `X`. Every sequence of
`H`-flops with respect to `K_X + B` (FA 6.8), crepant for `K_X + B`, whose models stay projective
and `ℚ`-factorial, is finite. For a fixed small rational `ε > 0` every such flop is a flip for
`K + B + εH`, so this reduces to the termination of projective klt threefold flips.

## Main results

* `MMP.Fourfold.hFlopSequence_length_lt_top`: such a sequence of `H`-flops has finite length.

## Implementation notes

The sequence is given by its models `(X_i, K_i, B_i, H_i)` for `i ∈ ℕ`, of which the first
`n + 1` are used (`n ∈ ℕ ∪ {∞}` steps), with `(X_0, B_0, H_0) = (X, B, H)`. The `i`-th step is a
diagram `X_i ⟶ Z_i ⟵ X_{i+1}` with birational map `g_i : X_i ⤏ X_{i+1}`, which is an
`H_i`-flop with respect to `K_i + B_i` (`MMP.Flips.IsHFlop`) of a contraction of relative Picard
number one onto a projective variety `Z_i`, with `K_{i+1} + B_{i+1}` numerically trivial over
`Z_i` (crepancy), and `B_{i+1} = g_{i*} B_i`, `H_{i+1} = g_{i*} H_i`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.8, 15.9
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_fourfold_projective_effective_divisor_flops_terminate

open MMP MMP.Mori MMP.Flips MMP.Fourfold

section Numerical

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A real combination `a D₁ + b D₂` of `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_smul_add_smul {D₁ D₂ : RDivisor X}
    (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂) (a b : ℝ) :
    IsCartierCombination (a • D₁ + b • D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append (a • r₁) (b • r₂), Fin.append L₁ L₂, fun j => ?_, ?_⟩
  · refine Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier) (fun i => ?_)
      (fun i => ?_) j
    · simpa using hL₁ i
    · simpa using hL₂ i
  · simp [Fin.sum_univ_add, Finset.smul_sum, smul_smul]

/-- The empty presentation of `0` computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every value of `0 · C` is zero. -/
private theorem eq_zero_of_isRIntersectionNumber_zero (C : ProperCurve sX) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX 0 r L C x) : x = 0 :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ x 0 h (isRIntersectionNumber_zero C)

/-- The intersection numbers of `N` with a curve `C` exist as soon as `C` carries one value of
an intersection number with a Cartier divisor (a normalization of `C`). -/
private theorem exists_isRIntersectionNumber (C : ProperCurve sX) {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d)
    {D : RDivisor X} (hD : IsCartierCombination D) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L' : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX D r L' C x := by
  obtain ⟨C', ν, hν, hdim, -⟩ := h
  obtain ⟨m, r, L', hL', hD⟩ := hD
  exact ⟨m, r, L', _, hL', fun j => _, by simpa only [toRDivisor_eq_mapCoeffs] using hD,
    fun j => ⟨C', ν, hν, hdim, rfl⟩, rfl⟩

/-- A real combination of numerically `f`-trivial divisors is numerically `f`-trivial. -/
private theorem isNumericallyTrivialOver_smul_add_smul {f : X ⟶ Y} {T₁ T₂ : RDivisor X}
    (h₁ : IsNumericallyTrivialOver k sX f T₁) (h₂ : IsNumericallyTrivialOver k sX f T₂)
    (a b : ℝ) : IsNumericallyTrivialOver k sX f (a • T₁ + b • T₂) := by
  refine ⟨isCartierCombination_smul_add_smul h₁.1 h₂.1 a b, h₁.2.1,
    fun C hC m r L x m' r' L' x' hx hx' => ?_⟩
  rw [eq_zero_of_isRIntersectionNumber_zero C hx']
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨hL, d, -, -, rfl⟩ := hx
    simp
  · obtain ⟨hL, d, -, hd, -⟩ := id hx
    obtain ⟨m₁, r₁, L₁, x₁, hx₁⟩ := exists_isRIntersectionNumber C (hd ⟨0, hm⟩) h₁.1
    obtain ⟨m₂, r₂, L₂, x₂, hx₂⟩ := exists_isRIntersectionNumber C (hd ⟨0, hm⟩) h₂.1
    have e₁ := h₁.2.2 C hC _ _ _ _ _ _ _ _ hx₁ (isRIntersectionNumber_zero C)
    have e₂ := h₂.2.2 C hC _ _ _ _ _ _ _ _ hx₂ (isRIntersectionNumber_zero C)
    have hl := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ r₁ L₁ r₂ L₂ x₁ x₂ a b hx₁ hx₂
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hl, e₁, e₂]
    ring

/-- Adding a numerically trivial divisor does not change the numerical class. -/
private theorem isNumericallyEquivalentOver_add_of_isNumericallyTrivialOver {f : X ⟶ Y}
    {A T : RDivisor X} (hA : IsCartierCombination A) (hT : IsNumericallyTrivialOver k sX f T) :
    IsNumericallyEquivalentOver k sX f (A + T) A := by
  refine ⟨by simpa using isCartierCombination_smul_add_smul hA hT.1 1 1, hA,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have hl := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ r₁ L₁ r₂ L₂ x₁ x₂ 1 (-1) h₁ h₂
  rw [show (1 : ℝ) • (A + T) + (-1 : ℝ) • A = T by module] at hl
  have := hT.2.2 C hC _ _ _ _ _ _ _ _ hl (isRIntersectionNumber_zero C)
  linarith

/-- A Cartier divisor linearly equivalent to `0` is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_of_linearlyEquivalent_zero [CompactSpace X]
    {f : X ⟶ Y} {L₀ : Divisor X} (hc : L₀.IsCartier) (h0 : L₀.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver k sX f (Divisor.toRDivisor L₀) := by
  refine ⟨⟨1, fun _ => 1, fun _ => L₀, fun _ => hc, by simp [toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C _ m r L x m' r' L' x' hx hx' => ?_⟩
  rw [eq_zero_of_isRIntersectionNumber_zero C hx']
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨hL, d, -, -, rfl⟩ := hx
    simp
  · obtain ⟨hL, d, -, hd, -⟩ := id hx
    obtain ⟨C', ν, hν, hdim, -⟩ := hd ⟨0, hm⟩
    have hν' := hν.isFinite
    have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    have h1 : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => L₀) C 0 :=
      ⟨fun _ => hc, fun _ => 0, by simp, fun _ => ⟨C', ν, hν, hdim,
        (MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX _ hdim hc h0).symm⟩,
        by simp⟩
    exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1

end Numerical

/-- A positive multiple of an `f`-ample `ℝ`-divisor is `f`-ample. -/
private theorem isRelativelyAmple_smul {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {A : RDivisor Y} (hA : IsRelativelyAmple f A) {c : ℝ}
    (hc : 0 < c) : IsRelativelyAmple f (c • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  exact ⟨m, c • r, L, hm, fun j => mul_pos hc (hr j), hL, by
    simp [Finset.smul_sum, smul_smul]⟩

/-- An `f`-ample `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyAmple {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) : IsCartierCombination A := by
  obtain ⟨m, r, L, -, -, hL, rfl⟩ := hA
  exact ⟨m, r, L, fun j => (hL j).1, by simp [toRDivisor_eq_mapCoeffs]⟩

/-- **Ampleness is numerical**: adding an `f`-numerically trivial divisor to an `f`-ample one
keeps it `f`-ample. -/
private theorem isRelativelyAmple_add_of_isNumericallyTrivialOver {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) (hX : IsNormalVariety k sX)
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [QuasiCompact sY]
    [IsLocallyNoetherian X] [IsNormal X] {f : Y ⟶ X} [IsProper f] (hf : f ≫ sX = sY)
    {A T : RDivisor Y} (hA : IsRelativelyAmple f A) (hT : IsNumericallyTrivialOver k sY f T) :
    IsRelativelyAmple f (A + T) := by
  obtain ⟨-, -, -, hproj, -, hnum⟩ := relativelyAmple_basics sY sX hY hX f hf
  obtain ⟨m, r, L, hm, -, hL, -⟩ := id hA
  exact hnum (hproj ⟨L ⟨0, hm⟩, hL _⟩) _ _
    (isNumericallyEquivalentOver_add_of_isNumericallyTrivialOver
      (isCartierCombination_of_isRelativelyAmple hA) hT) hA

/-- Changing coefficients commutes with the birational transform. -/
private theorem transformDivisor_mapCoeffsAddMonoidHom {X Y : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S] (g : X.RationalMap Y) (φ : R →+ S)
    (D : DivisorWithCoeffs R X) :
    Mori.RationalMap.transformDivisor g (DivisorWithCoeffs.mapCoeffsAddMonoidHom φ D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom φ (Mori.RationalMap.transformDivisor g D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [Mori.RationalMap.transformDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom,
      Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      DivisorWithCoeffs.mapPrimeDivisors_single]
    cases Mori.RationalMap.transformPrimeDivisor g E <;> simp [Finsupp.mapRange_single]

/-- `(q • D)` regarded as an `ℝ`-divisor is `q • D`. -/
private theorem toRDivisor_smul {X : Scheme.{0}} (q : ℚ) (D : QDivisor X) :
    QDivisor.toRDivisor (q • D) = (q : ℝ) • QDivisor.toRDivisor D :=
  DivisorWithCoeffs.ext' fun E => by
    simp [DivisorWithCoeffs.coeff_smul]

/-- `K + (B + εH) = (K + B) + εH` as `ℝ`-divisors. -/
private theorem logCanonicalDivisor_add_smul {X : Scheme.{0}} (K : Divisor X) (B H : QDivisor X)
    (ε : ℚ) :
    logCanonicalDivisor K (QDivisor.toRDivisor (B + ε • H)) =
      logCanonicalDivisor K (QDivisor.toRDivisor B) + (ε : ℝ) • QDivisor.toRDivisor H := by
  rw [logCanonicalDivisor, logCanonicalDivisor, map_add, toRDivisor_smul, add_assoc]

/-- **An `H`-flop crepant for `K + B` is a flip for `K + B + εH`.** On the source,
`-(K + B + εH) = ε(-H) - (K + B)` is `f`-ample since `K + B` is `f`-trivial; on the flipped side,
`g_*(K + B + εH) = εg_*H + (K' + B') + (g_*K - K')` is `f⁺`-ample since `K' + B'` is
`f⁺`-trivial by crepancy and `g_*K - K'` is principal. -/
private theorem isFlip_of_isHFlop {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] [QuasiCompact sX]
    {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX']
    {K : Divisor X} {B H : QDivisor X} {K' : Divisor X'} {B' : QDivisor X'}
    {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}
    (hK : K.IsCanonicalDivisor sX 3) (hK' : K'.IsCanonicalDivisor sX' 3)
    (hflop : IsHFlop ℂ sX sZ sX' 3 K (QDivisor.toRDivisor B) H f fp g)
    (hcrep : IsNumericallyTrivialOver ℂ sX' fp
      (logCanonicalDivisor K' (QDivisor.toRDivisor B')))
    (hB : B' = Mori.RationalMap.transformDivisor g B) {ε : ℚ} (hε : 0 < ε) :
    IsFlip ℂ sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor (B + ε • H))) f fp g := by
  obtain ⟨-, hHQ, -, hnt, hanti, hF⟩ := hflop
  set E := logCanonicalDivisor K (QDivisor.toRDivisor (B + ε • H))
  have hX := hF.isNormalVariety_source
  have hZ := hF.isNormalVariety_target
  have hX'v := hF.isNormalVariety_flip
  haveI : IsProper f := hF.isContraction.isProper
  haveI : IsProper fp := hF.isProper
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  -- the source side
  have hanti' : IsRelativelyAmple f (-E) := by
    convert isRelativelyAmple_add_of_isNumericallyTrivialOver hX hZ hF.isContraction.comp_eq
      (isRelativelyAmple_smul hanti hε') (isNumericallyTrivialOver_smul_add_smul hnt hnt (-1) 0)
      using 1
    simp only [E, logCanonicalDivisor_add_smul]
    module
  -- the flipped side
  have hHK : IsFlip ℂ sX sZ sX'
      (logCanonicalDivisor K (QDivisor.toRDivisor (H - Divisor.toQDivisor K))) f fp g := by
    convert hF using 1
    rw [logCanonicalDivisor, map_sub, QDivisor.toRDivisor_toQDivisor]
    abel
  haveI : IsDominant f := hF.isSmall_source.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hF.isSmall.isBirationalMorphism.isDominant
  obtain ⟨hK₁, -, -⟩ := smallLogDiscrepancySet_subset_of_isFlip hX hK
    (by rw [add_sub_cancel]; exact hHQ) hHK
  set K₁ : Divisor X' := Mori.RationalMap.transformDivisor g K
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'v hK₁ hK'
  have h0 : Divisor.LinearlyEquivalent (K₁ - K') 0 := ⟨φ, by rw [sub_zero, hφ]⟩
  have hP := isNumericallyTrivialOver_of_linearlyEquivalent_zero (k := ℂ) (sX := sX') (f := fp)
    (Divisor.IsCartier.of_linearlyEquivalent h0 Divisor.isCartier_zero) h0
  have hamp' : IsRelativelyAmple fp (Mori.RationalMap.transformDivisor g E) := by
    convert isRelativelyAmple_add_of_isNumericallyTrivialOver hX'v hZ hF.isSmall.comp_eq
      (isRelativelyAmple_smul hF.isRelativelyAmple_transform hε')
      (isNumericallyTrivialOver_smul_add_smul hcrep hP 1 1) using 1
    have hKR : Mori.RationalMap.transformDivisor g (Divisor.toRDivisor K) =
        Divisor.toRDivisor K₁ :=
      transformDivisor_mapCoeffsAddMonoidHom g (Int.castAddHom ℝ) K
    have hBR : Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor B) =
        QDivisor.toRDivisor B' :=
      hB ▸ transformDivisor_mapCoeffsAddMonoidHom g _ B
    have hs : Mori.RationalMap.transformDivisor g ((ε : ℝ) • QDivisor.toRDivisor H) =
        (ε : ℝ) • Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor H) :=
      (Mori.RationalMap.transformDivisorₗ ℝ g).map_smul _ _
    simp only [E, logCanonicalDivisor_add_smul]
    rw [logCanonicalDivisor, logCanonicalDivisor, map_add, map_add, hKR, hBR, hs, map_sub]
    module
  exact
    { toIsGeneralizedFlip :=
        { hF.toIsGeneralizedFlip with
          isCartierCombination := by
            simpa using isCartierCombination_smul_add_smul
              (isCartierCombination_of_isRelativelyAmple hanti')
              (isCartierCombination_of_isRelativelyAmple hanti') (-1) 0
          isRelativelyAntiAmple := hanti'
          isCartierCombination_transform := isCartierCombination_of_isRelativelyAmple hamp'
          isRelativelyAmple_transform := hamp' }
      isSmall_source := hF.isSmall_source }

/-- `i + 1 < n + 1` in `ℕ∞` means `i < n`. -/
private theorem lt_of_succ_lt_add_one {i : ℕ} {n : ℕ∞} (h : ((i + 1 : ℕ) : ℕ∞) < n + 1) :
    (i : ℕ∞) < n :=
  (ENat.add_lt_add_iff_right ENat.one_ne_top).1 (by exact_mod_cast h)

open MMP.Fourfold in
private theorem solution : ∀ (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) [∀ i, LocallyOfFiniteType (sY i)]
    (K : ∀ i, Divisor (Y i)) (B H : ∀ i, QDivisor (Y i))
    (hproj₀ : MMP.Mori.IsProjectiveVariety ℂ (sY 0)) (hdim₀ : topologicalKrullDim (Y 0) = 3)
    (hQ₀ : IsQFactorial (sY 0)) (hB₀ : (B 0).IsEffective) (hklt₀ : Mori.IsKltPair (sY 0) 3 (K 0) (B 0))
    (hH₀ : (H 0).IsEffective) (hHQ₀ : (H 0).IsQCartier)
    (n : ℕ∞) (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ Z i) (fp : ∀ i, Y (i + 1) ⟶ Z i) (g : ∀ i, (Y i).RationalMap (Y (i + 1)))
    (hproj : ∀ i : ℕ, (i : ℕ∞) ≤ n → MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (hQ : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (sY i))
    (hK : ∀ i : ℕ, (i : ℕ∞) ≤ n → (K i).IsCanonicalDivisor (sY i) 3)
    (hflop : ∀ i : ℕ, (i : ℕ∞) < n →
      IsHFlop ℂ (sY i) (sZ i) (sY (i + 1)) 3 (K i) (QDivisor.toRDivisor (B i)) (H i) (f i) (fp i)
        (g i))
    (hρ : ∀ i : ℕ, (i : ℕ∞) < n → Flips.relativePicardNumber (sY i) (f i) = 1)
    (hprojZ : ∀ i : ℕ, (i : ℕ∞) < n → MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hcrep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsNumericallyTrivialOver ℂ (sY (i + 1)) (fp i)
        (logCanonicalDivisor (K (i + 1)) (QDivisor.toRDivisor (B (i + 1)))))
    (hB : ∀ i : ℕ, (i : ℕ∞) < n → B (i + 1) = Mori.RationalMap.transformDivisor (g i) (B i))
    (hH : ∀ i : ℕ, (i : ℕ∞) < n → H (i + 1) = Mori.RationalMap.transformDivisor (g i) (H i)),
    n < ⊤ := by
  intro Y _ _ _ _ sY _ K B H hproj₀ hdim₀ hQ₀ hB₀ hklt₀ hH₀ hHQ₀ n Z sZ f fp g hproj hQ hK hflop
    hρ hprojZ hcrep hB hH
  -- a fixed rational `ε > 0` with `(X, B + εH)` klt
  obtain ⟨ε₀, hε₀, hall⟩ := hklt₀.exists_forall_isKltPair_add_smul hH₀ hHQ₀
  set ε : ℚ := ε₀ / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hkltD := hall ε hε.le (by rw [hεdef]; linarith)
  set D : ∀ i, QDivisor (Y i) := fun i => B i + ε • H i with hDdef
  have hvar : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsNormalVariety ℂ (sY i) := fun i hi =>
    ⟨(hproj i hi).toIsVariety, inferInstance⟩
  -- every flop is a flip for `K + B + εH`
  have hstep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsFlip ℂ (sY i) (sZ i) (sY (i + 1)) (logCanonicalDivisor (K i) (QDivisor.toRDivisor (D i)))
        (f i) (fp i) (g i) := fun i hi =>
    isFlip_of_isHFlop (hK i hi.le) (hK (i + 1) (by exact_mod_cast Order.add_one_le_of_lt hi))
      (hflop i hi) (hcrep i hi) (hB i hi) hε
  let S : SequenceOfFlips (sY 0) 3 (K 0) (D 0) :=
    { isNormalVariety := hvar 0 (by simp)
      isCanonicalDivisor := ⟨inferInstance, inferInstance, hK 0 (by simp)⟩
      isQCartier := ⟨inferInstance, inferInstance, hkltD.1.2.2⟩
      length := n + 1
      one_le_length := le_add_self
      model := fun i => ⟨Y i, sY i, K i, D i⟩
      model_zero := rfl
      isNormalVariety_model := fun i hi => hvar i (Order.le_of_lt_add_one hi)
      isLocallyNoetherian_model := fun i => inferInstance
      isNormal_model := fun i => inferInstance
      compactSpace_model := fun i => inferInstance
      isCanonicalDivisor_model := fun i hi => hK i (Order.le_of_lt_add_one hi)
      base := Z
      baseStr := sZ
      contraction := f
      flip := fp
      flipMap := g
      isNegativeExtremalContraction := fun i hi => by
        have h := hstep i (lt_of_succ_lt_add_one hi)
        exact ⟨h.isNormalVariety_source, h.isNormalVariety_target, h.isCartierCombination,
          h.isContraction, h.isRelativelyAntiAmple, hρ i (lt_of_succ_lt_add_one hi)⟩
      isSmall := fun i hi => (hstep i (lt_of_succ_lt_add_one hi)).isSmall_source
      isFlip := fun i hi => hstep i (lt_of_succ_lt_add_one hi)
      transform_eq := fun i hi => by
        have hi' := lt_of_succ_lt_add_one hi
        change B (i + 1) + ε • H (i + 1) =
          Mori.RationalMap.transformDivisorₗ ℚ (g i) (B i + ε • H i)
        rw [map_add, map_smul, hB i hi', hH i hi']
        rfl }
  -- the initial pair `(X, B + εH)` is an effective klt pair in every convention
  have hDeff : (D 0).IsEffective := fun P => by
    simp only [hDdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact add_nonneg (hB₀ P) (mul_nonneg hε.le (hH₀ P))
  have hBd : IsBoundary (QDivisor.toRDivisor (D 0)) := fun P => by
    rw [QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hDeff P,
      by exact_mod_cast (roundDown_nonpos_iff.mp hkltD.2.2 P).le⟩
  have hFK : IsKawamataLogTerminal (sY 0) 3 (K 0) (QDivisor.toRDivisor (D 0)) :=
    (isKawamataLogTerminal_iff_isKltPair (sY 0) 3 (K 0) (D 0) (hvar 0 (by simp))
      (hK 0 (by simp)) hBd hkltD.1.2.2).2 hkltD
  have hFour : MMP.Fourfold.IsKltPair (sY 0) (D 0) :=
    (isKltPair_iff_mori_isKltPair (sY 0) (hK 0 (by simp))
      ⟨inferInstance, inferInstance, hkltD.1.isPair, hDeff⟩).2 hkltD
  have hterm : S.Terminates :=
    forall_projectiveKltTerminationLevel_and_terminates.2 (Y 0) (sY 0) (K 0) (D 0) hproj₀ hdim₀
      hQ₀ hDeff hFour hFK S (fun i hi => hproj i (Order.le_of_lt_add_one hi))
      (fun i hi => hprojZ i (lt_of_succ_lt_add_one hi))
  exact lt_of_le_of_lt le_self_add hterm

end Proof_lem_fourfold_projective_effective_divisor_flops_terminate

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Termination of `H`-flops on a projective klt threefold.** Let `X_0` be a normal projective
`ℚ`-factorial complex threefold with canonical divisor `K_0`, `B_0` an effective `ℚ`-divisor with
`(X_0, B_0)` klt, and `H_0 ≥ 0` a `ℚ`-Cartier `ℚ`-divisor. Every sequence of `n` steps
`X_i ⟶ Z_i ⟵ X_{i+1}`, each an `H_i`-flop with respect to `K_i + B_i` of a contraction of relative
Picard number one onto a projective variety, crepant for `K + B`, with `B_{i+1}`, `H_{i+1}` the
birational transforms of `B_i`, `H_i` and all models projective and `ℚ`-factorial, is finite:
`n < ∞`. -/
@[mmp "lem_fourfold_projective_effective_divisor_flops_terminate"]
public theorem hFlopSequence_length_lt_top
    (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) [∀ i, LocallyOfFiniteType (sY i)]
    (K : ∀ i, Divisor (Y i)) (B H : ∀ i, QDivisor (Y i))
    (hproj₀ : MMP.Mori.IsProjectiveVariety ℂ (sY 0)) (hdim₀ : topologicalKrullDim (Y 0) = 3)
    (hQ₀ : IsQFactorial (sY 0)) (hB₀ : (B 0).IsEffective) (hklt₀ : Mori.IsKltPair (sY 0) 3 (K 0) (B 0))
    (hH₀ : (H 0).IsEffective) (hHQ₀ : (H 0).IsQCartier)
    (n : ℕ∞) (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ Z i) (fp : ∀ i, Y (i + 1) ⟶ Z i) (g : ∀ i, (Y i).RationalMap (Y (i + 1)))
    (hproj : ∀ i : ℕ, (i : ℕ∞) ≤ n → MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (hQ : ∀ i : ℕ, (i : ℕ∞) ≤ n → IsQFactorial (sY i))
    (hK : ∀ i : ℕ, (i : ℕ∞) ≤ n → (K i).IsCanonicalDivisor (sY i) 3)
    (hflop : ∀ i : ℕ, (i : ℕ∞) < n →
      IsHFlop ℂ (sY i) (sZ i) (sY (i + 1)) 3 (K i) (QDivisor.toRDivisor (B i)) (H i) (f i) (fp i)
        (g i))
    (hρ : ∀ i : ℕ, (i : ℕ∞) < n → Flips.relativePicardNumber (sY i) (f i) = 1)
    (hprojZ : ∀ i : ℕ, (i : ℕ∞) < n → MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hcrep : ∀ i : ℕ, (i : ℕ∞) < n →
      IsNumericallyTrivialOver ℂ (sY (i + 1)) (fp i)
        (logCanonicalDivisor (K (i + 1)) (QDivisor.toRDivisor (B (i + 1)))))
    (hB : ∀ i : ℕ, (i : ℕ∞) < n → B (i + 1) = Mori.RationalMap.transformDivisor (g i) (B i))
    (hH : ∀ i : ℕ, (i : ℕ∞) < n → H (i + 1) = Mori.RationalMap.transformDivisor (g i) (H i)) :
    n < ⊤ :=
      by revert Y sY K B H hproj₀ hdim₀ hQ₀ hB₀ hklt₀ hH₀ hHQ₀ n Z sZ f fp g hproj hQ hK hflop hρ hprojZ hcrep hB hH; first | exact Proof_lem_fourfold_projective_effective_divisor_flops_terminate.solution | exact Proof_lem_fourfold_projective_effective_divisor_flops_terminate.solution _ | exact Proof_lem_fourfold_projective_effective_divisor_flops_terminate.solution _ _ | exact Proof_lem_fourfold_projective_effective_divisor_flops_terminate.solution _ _ _ | exact Proof_lem_fourfold_projective_effective_divisor_flops_terminate.solution _ _ _ _

end MMP.Fourfold
