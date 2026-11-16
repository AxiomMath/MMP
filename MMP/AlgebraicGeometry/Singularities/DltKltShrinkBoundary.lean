module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Divisor.LocalSectionDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.BoundaryLowering

/-!
# Klt perturbations of dlt pairs: shrinking the boundary

Two consequences of the dlt-to-klt perturbation over an algebraically closed field of
characteristic zero. For a dlt pair `(X, Δ)` with `X` `ℚ`-factorial and quasi-projective,
`(X, (1 - δ)Δ)` is klt for all small rational `δ > 0` (Kollár–Mori, proof of Theorem 3.35). For a
projective `ℚ`-factorial dlt pair `(U, Δ)` and a `(K_U + Δ)`-negative extremal ray `R`, lowering
the reduced part `⌊Δ⌋` by a small rational multiple gives a klt pair on which `R` is still
negative.

## Main results

* `MMP.Mori.IsDltPair.exists_forall_isKltPair_one_sub_smul`: `(X, (1 - δ)Δ)` is klt for every
  rational `0 < δ < δ₀`.
* `MMP.Fourfold.IsProjectiveQFactorialDltPair.exists_isKltPair_sub_smul_roundDown`: some rational
  `ε > 0` makes `(U, Δ - ε⌊Δ⌋)` klt and `R` a `(K_U + Δ - ε⌊Δ⌋)`-negative extremal ray.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result. The first result perturbs `Δ` by an effective `D ∼_ℚ Δ + cH`, `H`
ample (`MMP.Mori.IsDltPair.exists_forall_isKltPair_sub_smul_add_smul`), and removes `δD`. The
second uses that a dlt pair with all coefficients `< 1` is klt
(`MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one`) and the linearity of
`MMP.Fourfold.QDivisor.curveForm` in the divisor, reduced to that of
`MMP.Mori.QDivisor.intersectionNumber` on proper curves. `⌊Δ⌋` is
`MMP.Mori.DivisorWithCoeffs.roundDown Δ`, regarded as a `ℚ`-divisor through
`MMP.Mori.Divisor.toQDivisor`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.35, via Proposition 2.43
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_km3c_dlt_qfactorial_perturb_klt

/-- A quasi-projective integral normal scheme over a field carries an ample Cartier divisor. -/
private theorem exists_isCartier_isAmple {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hqp : IsQuasiProjective sX) :
    ∃ H : Divisor X, ∃ hH : H.IsCartier, H.IsAmple hH := by
  obtain ⟨-, M, hMinv, hMamp⟩ :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective sX).mp hqp
  have hM : Stacks.Ample.IsAmple X M :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX M hMamp
  obtain ⟨IX, hIX, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple M hM isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor IX hIX
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple M n hn hM)⟩

end Proof_lem_km3c_dlt_qfactorial_perturb_klt

namespace MMP.Mori

open Proof_lem_km3c_dlt_qfactorial_perturb_klt

/-- **Shrinking a `ℚ`-factorial dlt boundary** (Kollár–Mori, proof of Theorem 3.35). Let
`(X, Δ)` be a dlt pair, with canonical divisor `K` of dimension `n`, over an algebraically
closed field of characteristic zero, with `X` `ℚ`-factorial and quasi-projective. Then there is
a rational `δ₀ > 0` such that `(X, (1 - δ)Δ)` is klt for every rational `0 < δ < δ₀`. -/
@[mmp "lem_km3c_dlt_qfactorial_perturb_klt"]
public theorem IsDltPair.exists_forall_isKltPair_one_sub_smul {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsDltPair sX n K Δ) (hQ : MMP.Fourfold.IsQFactorial sX)
    (hqp : IsQuasiProjective sX) :
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ → IsKltPair sX n K ((1 - δ) • Δ) := by
  haveI : CompactSpace X := haveI := hqp.1.2; QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨H, hH, hHa⟩ := exists_isCartier_isAmple hqp
  obtain ⟨-, -, -, -, D, hD, -, ε₀, hε₀, hklt⟩ :=
    MMP.Mori.IsDltPair.exists_forall_isKltPair_sub_smul_add_smul h hqp hH hHa
      (fun P => (h.2.1 P).1)
      (by rw [sub_self]; exact DivisorWithCoeffs.isEffective_zero) rfl
  refine ⟨ε₀, hε₀, fun δ hδ hδε => ?_⟩
  refine MMP.Threefold.Mori.IsKltPair.of_add (Δ' := δ • D)
    ⟨h.1.1, h.1.2.1, MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _⟩
    (by rw [DivisorWithCoeffs.isEffective_iff_nonneg] at hD ⊢; exact smul_nonneg hδ.le hD)
    (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _) ?_
  simpa [sub_smul] using hklt δ hδ hδε

end MMP.Mori

namespace Proof_lem_oai4_c3_dlt_klt_perturbation

open MMP.Fourfold

/-- For `a < 0` and any `b`, some rational `ε ∈ (0, 1]` keeps `a - ε b` negative. -/
private theorem exists_rat_sub_mul_neg {a : ℝ} (ha : a < 0) (b : ℝ) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ a - ε * b < 0 := by
  obtain ⟨ε, hε0, hεlt⟩ :=
    exists_rat_btwn (lt_min one_pos (div_pos (neg_pos.mpr ha) (by positivity : (0 : ℝ) < |b| + 1)))
  have h2 : (ε : ℝ) * (|b| + 1) < -a :=
    (lt_div_iff₀ (by positivity)).mp (hεlt.trans_le (min_le_right _ _))
  refine ⟨ε, by exact_mod_cast hε0, by exact_mod_cast (hεlt.trans_le (min_le_left _ _)).le, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le b) hε0.le]

section CurveForm

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor on the class of a proper curve is its
intersection number with that curve. -/
private theorem curveForm_numericalClass_cycle (D : QDivisor X) (h : D.IsQCartier)
    (C : ProperCurve sX) :
    QDivisor.curveForm sX D h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  have hC := Divisor.mem_cartierSubgroup.mp (D.cartierIndexSMul h).2
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D h _ hC
      (QDivisor.toQDivisor_cartierIndexSMul D h),
    QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, Finsupp.sum_single_index (by simp), LinearMap.smul_apply,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  simp only [smul_eq_mul, mul_one]
  rw [ProperCurve.degree_divisorialSheaf C _ hC]
  push_cast
  ring

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
/-- Two linear forms on `N₁(X)_ℝ` agreeing on the classes of proper curves are equal. -/
private theorem linearMap_ext_numericalClass_cycle {φ ψ : NumericalCurveClasses sX →ₗ[ℝ] ℝ}
    (h : ∀ C : ProperCurve sX,
      φ (OneCycle.numericalClass sX (C.cycle ℝ)) = ψ (OneCycle.numericalClass sX (C.cycle ℝ))) :
    φ = ψ :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun C => LinearMap.ext_ring (h C))

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, curveForm_numericalClass_cycle, curveForm_numericalClass_cycle,
    curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast; rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
private theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    QDivisor.curveForm sX (q • D) hqD = (q : ℝ) • QDivisor.curveForm sX D hD := by
  refine linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, curveForm_numericalClass_cycle, curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q D hD hqD]
  push_cast; rfl

/-- The curve form depends only on the divisor, not on the proof that it is `ℚ`-Cartier. -/
private theorem curveForm_congr {D D' : QDivisor X} (e : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) : QDivisor.curveForm sX D hD = QDivisor.curveForm sX D' hD' := by
  subst e; rfl

/-- On a `ℚ`-factorial variety, `(D - qF) · z = D · z - q (F · z)`. -/
private theorem curveForm_sub_smul (hX : IsQFactorial sX) (D F : QDivisor X) (q : ℚ)
    (hD : D.IsQCartier) (h : (D - q • F).IsQCartier) (z : NumericalCurveClasses sX) :
    QDivisor.curveForm sX (D - q • F) h z =
      QDivisor.curveForm sX D hD z -
        q * QDivisor.curveForm sX F (isQCartier_of_isQFactorial sX hX F) z := by
  have hQ := isQCartier_of_isQFactorial sX hX
  rw [curveForm_congr sX (by rw [neg_smul, sub_eq_add_neg] : D - q • F = D + (-q) • F) h (hQ _),
    curveForm_add sX _ _ hD (hQ _), curveForm_smul sX _ _ (hQ F)]
  simp [sub_eq_add_neg]

/-- **Perturbing a negative ray.** On a `ℚ`-factorial variety, a `D`-negative extremal ray stays
`(D - εF)`-negative for some rational `ε ∈ (0, 1]`. -/
private theorem exists_isNegativeExtremalRayOf_sub_smul (hX : IsQFactorial sX) {D : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} (hR : IsNegativeExtremalRayOf sX D R) (F : QDivisor X) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ IsNegativeExtremalRayOf sX (D - ε • F) R := by
  obtain ⟨hD, hray, hneg⟩ := hR
  obtain ⟨v, hv0, hRv⟩ := hray.2
  obtain ⟨ε, hε, hε1, key⟩ := exists_rat_sub_mul_neg
    (hneg v (hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩) hv0)
    (QDivisor.curveForm sX F (isQCartier_of_isQFactorial sX hX F) v)
  refine ⟨ε, hε, hε1, isQCartier_of_isQFactorial sX hX _, hray, fun u hu hu0 => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hRv ▸ hu
  have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
  rw [curveForm_sub_smul sX hX D F ε hD, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    ← mul_left_comm, ← mul_sub]
  exact mul_neg_of_pos_of_neg hc0 key

end CurveForm

/-- Lowering a coefficient `x ∈ [0, 1]` by `ε ⌊x⌋`, `0 < ε ≤ 1`, keeps it in `[0, x]` and makes
it `< 1`. -/
private theorem sub_mul_floor_nonneg_and_le_and_lt_one {x ε : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ x - ε * ⌊x⌋ ∧ x - ε * ⌊x⌋ ≤ x ∧ x - ε * ⌊x⌋ < 1 := by
  rcases h1.lt_or_eq with h1 | rfl
  · simp [Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, h0, h1]
  · simp only [Int.floor_one, Int.cast_one, mul_one]
    exact ⟨by linarith, by linarith, by linarith⟩

/-- For `0 < ε ≤ 1`, lowering the boundary of a projective `ℚ`-factorial dlt pair by `ε ⌊Δ⌋`
gives a klt pair. -/
private theorem isKltPair_sub_smul_roundDown {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {K : Divisor U} {Δ : QDivisor U}
    (h : IsProjectiveQFactorialDltPair sU K Δ) {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsKltPair sU (Δ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) := by
  have hcoeff : ∀ P, (Δ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) P =
      Δ P - ε * ⌊Δ P⌋ := fun P => by simp [← DivisorWithCoeffs.coeff_apply]
  have hdlt := h.isDltPair
  have hmem P := sub_mul_floor_nonneg_and_le_and_lt_one (hdlt.1.2.1 P) (hdlt.2.1 P) hε hε1
  refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one
    (MMP.Intersection.IsDltPair.of_le sU hdlt (fun P => ?_) (fun P => ?_)
      (isQCartier_of_isQFactorial sU h.isQFactorial _)) (fun P => ?_)
  · rw [Finsupp.coe_zero, Pi.zero_apply, hcoeff]; exact (hmem P).1
  · rw [hcoeff]; exact (hmem P).2.1
  · rw [DivisorWithCoeffs.coeff_apply, hcoeff]; exact (hmem P).2.2

end Proof_lem_oai4_c3_dlt_klt_perturbation

namespace MMP.Fourfold

open Proof_lem_oai4_c3_dlt_klt_perturbation

/-- **Klt perturbation of a dlt pair.** For a projective `ℚ`-factorial dlt pair `(U, Δ)` with
canonical divisor `K` and a `(K + Δ)`-negative extremal ray `R` of `NE̅(U)`, there is a rational
`ε > 0` such that `(U, Δ - ε⌊Δ⌋)` is klt and `R` is `(K + Δ - ε⌊Δ⌋)`-negative. -/
@[mmp "lem_oai4_c3_dlt_klt_perturbation"]
public theorem IsProjectiveQFactorialDltPair.exists_isKltPair_sub_smul_roundDown
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {U : Scheme.{u}}
    {sU : U ⟶ Spec (.of k)} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {K : Divisor U} {Δ : QDivisor U} {R : Set (NumericalCurveClasses sU)}
    (h : IsProjectiveQFactorialDltPair sU K Δ)
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R) :
    ∃ ε : ℚ, 0 < ε ∧
      IsKltPair sU (Δ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ)) ∧
      IsNegativeExtremalRayOf sU
        (Divisor.toQDivisor K +
          (Δ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ))) R := by
  haveI : QuasiCompact sU := quasiCompact_of_compactSpace sU
  obtain ⟨ε, hε, hε1, hRε⟩ := exists_isNegativeExtremalRayOf_sub_smul sU h.isQFactorial hR
    (Divisor.toQDivisor (DivisorWithCoeffs.roundDown Δ))
  exact ⟨ε, hε, isKltPair_sub_smul_roundDown h hε hε1,
    add_sub_assoc (Divisor.toQDivisor K) Δ _ ▸ hRε⟩

end MMP.Fourfold

end
