module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.MinimalModel.KltStepQFactorial
import MMP.AlgebraicGeometry.MMP.Contraction.NumericallyTrivialDescent
import MMP.AlgebraicGeometry.MMP.Flip.PicardNumber
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.Analysis.Complex.CauchyOsgoodLaurent
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
import MMP.Analysis.Complex.WeierstrassDivision
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.KltFlipExistence
import MMP.AlgebraicGeometry.MMP.Flip.NegativeAdjointTransfer
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialDiscrepancyIncrease
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Elementary steps of real klt threefolds over a projective base

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold, and let `(X, B)` be a klt pair with effective real boundary `B` and canonical
divisor `K`. If `K + B` is not `g`-nef, there is a `(K + B)`-negative extremal ray `R` of the
closed relative cone `NE̅(X/S)` together with its contraction `f : X ⟶ Z`, `h : Z ⟶ S` over `S`,
with `Z` projective, `-(K + B)` `f`-ample and `ρ(X/Z) = 1`. If `f` is divisorial, `Z` is
`ℚ`-factorial and `(Z, f_* B)` is klt; if `f` is small, it has a real flip `f⁺ : X⁺ ⟶ Z` with
`X⁺` a projective `ℚ`-factorial threefold, and `(X⁺, B⁺)` is klt for the strict transform `B⁺`.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef`.

## Implementation notes

Real divisors are `MMP.Mori.RDivisor`s; the adjoint is `MMP.Flips.logCanonicalDivisor K B`, its
relative nefness is `MMP.Flips.IsRelativelyNef` and its intersection numbers with curves are
`MMP.Flips.IsRIntersectionNumber`, computed with any presentation by Cartier divisors. The ray
is `(K + B)`-negative when `(K + B) · C < 0` for every curve `C` contracted by `g` whose class
lies in `R`. The divisorial case is "`f` is birational and `Ex(f)` is a prime divisor", the small
case is `MMP.Flips.IsSmall`, and the flip is a step of an extremal real flip sequence,
`MMP.Fourfold.IsRealFlipStep`, whose boundary is `flipTransform f f⁺ B`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.25, 3.36,
  3.37
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips MMP.Fourfold

namespace Proof_lem_fourfold_real_klt_elementary_step

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Real intersection forms of Cartier presentations -/

section Forms

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [QuasiCompact sX]

/-- The degree form `z ↦ (L · z)` on `N₁(X)` of a Cartier divisor `L`. -/
private noncomputable def degForm (M : Divisor X) (hM : M.IsCartier) :
    NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  haveI := hM.isInvertibleModule_divisorialSheaf
  NumericalCurveClasses.degree sX M.divisorialSheaf

/-- The linear form `z ↦ ∑ r_j (L_j · z)` on `N₁(X)` of a presentation `∑ r_j L_j` by Cartier
divisors. -/
private noncomputable def presForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  ∑ j, r j • degForm (L j) (hL j)

private theorem presForm_numericalClass {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sX) :
    presForm r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ) := by
  simp only [presForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  unfold degForm
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
    ProperCurve.degree_divisorialSheaf C _ (hL j)]

/-- The value `∑ r_j (L_j · C)` is an intersection number of `∑ r_j L_j` with `C`. -/
private theorem isRIntersectionNumber_presForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (presForm r L hL (OneCycle.numericalClass sX (C.cycle ℝ))) := by
  rw [presForm_numericalClass]
  exact MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL

/-- Every value of `D · C` is the value at `[C]` of the form of any presentation of `D`. -/
private theorem eq_presForm_of_isRIntersectionNumber {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {C : ProperCurve sX} {m' : ℕ}
    {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX D r' L' C x) :
    x = presForm r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  subst hD
  exact (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r' L' r L _ _ hx
    (isRIntersectionNumber_presForm r L hL C)

/-- The form of a presentation depends only on the divisor presented. -/
private theorem presForm_eq {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X)
    (hL' : ∀ j, (L' j).IsCartier)
    (h : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    presForm (sX := sX) r L hL = presForm r' L' hL' :=
  MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C =>
    (eq_presForm_of_isRIntersectionNumber r' L' hL' h
      (isRIntersectionNumber_presForm r L hL C))

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor is the form of any presentation of it. -/
private theorem curveForm_eq_presForm {Q : QDivisor X} (hQ : Q.IsQCartier) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : QDivisor.toRDivisor Q = ∑ j, r j • Divisor.toRDivisor (L j)) :
    QDivisor.curveForm sX Q hQ = presForm r L hL := by
  obtain ⟨N, hN, E, hE, hEQ⟩ : ∃ N : ℕ, 0 < N ∧ ∃ E : Divisor X, E.IsCartier ∧
      Divisor.toQDivisor E = (N : ℤ) • Q := by
    obtain ⟨N, hN, hc⟩ := hQ.exists_pos
    obtain ⟨E, hE, hc⟩ := hc
    exact ⟨N, hN, E, hc, hE⟩
  have hQE : QDivisor.toRDivisor Q = ∑ j : Fin 1, ![(N : ℝ)⁻¹] j • Divisor.toRDivisor (![E] j) := by
    rw [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero,
      ← QDivisor.toRDivisor_toQDivisor, hEQ, map_zsmul, natCast_zsmul,
      ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity)]
  have hE1 : ∀ j, (![E] j).IsCartier := fun j => by fin_cases j; exact hE
  rw [← presForm_eq _ _ hE1 r L hL (hQE.symm.trans h)]
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, presForm_numericalClass,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul ℂ sX C.ι C.dim_le
      (fun E E' hE hE' => Divisor.degreeOn_add ℂ sX C.ι C.dim_le E E' hE hE') Q hQ hN E hE hEQ]
  simp [div_eq_inv_mul]

/-- **The form of a real combination of `ℚ`-Cartier divisors.** If `∑ c_j Q_j = ∑ r_i L_i`
with the `Q_j` `ℚ`-Cartier, then the form of the presentation is `∑ c_j (Q_j · -)`. -/
private theorem presForm_eq_sum_smul_curveForm {ι : Type} [Fintype ι] (Q : ι → QDivisor X)
    (hq : ∀ j, (Q j).IsQCartier) (c : ι → ℝ) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier)
    (hD : ∑ j, c j • QDivisor.toRDivisor (Q j) = ∑ j, r j • Divisor.toRDivisor (L j)) :
    presForm (sX := sX) r L hL = ∑ j, c j • QDivisor.curveForm sX (Q j) (hq j) := by
  classical
  have hex : ∀ j, ∃ N : ℕ, 0 < N ∧ ∃ E : Divisor X, E.IsCartier ∧
      Divisor.toQDivisor E = (N : ℤ) • Q j := fun j => by
    obtain ⟨N, hN, E, hE, hc⟩ := (hq j).exists_pos
    exact ⟨N, hN, E, hc, hE⟩
  choose N hN M hMc hM using hex
  have hRM : ∀ j, Divisor.toRDivisor (M j) = (N j : ℝ) • QDivisor.toRDivisor (Q j) := fun j => by
    rw [← QDivisor.toRDivisor_toQDivisor, hM j, map_zsmul, natCast_zsmul,
      ← Nat.cast_smul_eq_nsmul ℝ]
  have hcf : ∀ j, QDivisor.curveForm sX (Q j) (hq j) =
      (N j : ℝ)⁻¹ • degForm (M j) (hMc j) := fun j => by
    have h1 : ∀ i, (![M j] i).IsCartier := fun i => by fin_cases i; exact hMc j
    rw [curveForm_eq_presForm (hq j) ![(N j : ℝ)⁻¹] ![M j] h1 (by
      rw [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, hRM j,
        inv_smul_smul₀ (by exact_mod_cast (hN j).ne')])]
    simp only [presForm, Fin.sum_univ_one, Matrix.cons_val_zero]
  let e := Fintype.equivFin ι
  let r' : Fin (Fintype.card ι) → ℝ := fun k => c (e.symm k) * (N (e.symm k) : ℝ)⁻¹
  let L' : Fin (Fintype.card ι) → Divisor X := fun k => M (e.symm k)
  have hL' : ∀ k, (L' k).IsCartier := fun k => hMc _
  have hpres : ∑ j, r j • Divisor.toRDivisor (L j) =
      ∑ k, r' k • Divisor.toRDivisor (L' k) := by
    rw [← hD]
    change _ = ∑ k, (fun j => (c j * (N j : ℝ)⁻¹) • Divisor.toRDivisor (M j)) (e.symm k)
    rw [Equiv.sum_comp e.symm (fun j => (c j * (N j : ℝ)⁻¹) • Divisor.toRDivisor (M j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hRM j, smul_smul, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (hN j).ne'), mul_one]
  rw [presForm_eq r L hL r' L' hL' hpres]
  simp_rw [hcf]
  change ∑ k, (fun j => (c j * (N j : ℝ)⁻¹) • degForm (sX := sX) (M j) (hMc j)) (e.symm k) = _
  rw [Equiv.sum_comp e.symm (fun j => (c j * (N j : ℝ)⁻¹) • degForm (sX := sX) (M j) (hMc j))]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

/-- **The form of a convex combination of `ℚ`-Cartier adjoints.** If
`K + ∑ w_j B_j = ∑ r_i L_i` with `∑ w_j = 1`, then the form of the presentation is
`∑ w_j (K + B_j · -)`. -/
private theorem presForm_eq_sum_curveForm {ι : Type} [Fintype ι] (K : Divisor X)
    (v : ι → QDivisor X) (w : ι → ℝ) (hq : ∀ j, (Divisor.toQDivisor K + v j).IsQCartier)
    (hw1 : ∑ j, w j = 1) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier)
    (hD : Divisor.toRDivisor K + ∑ j, w j • QDivisor.toRDivisor (v j) =
      ∑ j, r j • Divisor.toRDivisor (L j)) :
    presForm (sX := sX) r L hL =
      ∑ j, w j • QDivisor.curveForm sX (Divisor.toQDivisor K + v j) (hq j) := by
  refine presForm_eq_sum_smul_curveForm _ hq w r L hL ?_
  rw [← hD]
  simp_rw [map_add, QDivisor.toRDivisor_toQDivisor, smul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul]

/-- The intersection number `(D · C)` of a `ℚ`-divisor with a proper curve on a `ℚ`-factorial
variety, as a `ℚ`-linear form. -/
private noncomputable def qdeg (hXQ : IsQFactorial sX) (C : ProperCurve sX) :
    QDivisor X →ₗ[ℚ] ℚ where
  toFun D := D.intersectionNumber ℂ sX C.ι C.dim_le (isQCartier_of_isQFactorial sX hXQ D)
  map_add' D D' := QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le D D' _ _ _
  map_smul' q D := MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le D _ q _

private theorem qdeg_apply (hXQ : IsQFactorial sX) (C : ProperCurve sX) (D : QDivisor X)
    (hD : D.IsQCartier) : qdeg hXQ C D = D.intersectionNumber ℂ sX C.ι C.dim_le hD := rfl

private theorem curveForm_numericalClass_eq_qdeg (hXQ : IsQFactorial sX) (C : ProperCurve sX)
    (D : QDivisor X) (hD : D.IsQCartier) :
    QDivisor.curveForm sX D hD (OneCycle.numericalClass sX (C.cycle ℝ)) = (qdeg hXQ C D : ℝ) := by
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, qdeg_apply hXQ C D hD]

private theorem qdeg_toQDivisor (hXQ : IsQFactorial sX) (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    qdeg hXQ C (Divisor.toQDivisor L) = L.degreeOn ℂ sX C.ι C.dim_le hL := by
  rw [qdeg_apply hXQ C _ (QDivisor.isQCartier_toQDivisor hL),
    QDivisor.intersectionNumber_toQDivisor ℂ sX C.ι C.dim_le L hL]

/-- A `ℚ`-divisor with a relatively ample multiple is positive on every contracted curve. -/
private theorem qdeg_pos_of_hasRelativelyAmpleMultiple (hXQ : IsQFactorial sX) {W : Scheme.{0}}
    {q : X ⟶ W} {Q : QDivisor X} (h : Q.HasRelativelyAmpleMultiple q) (C : ProperCurve sX)
    (hC : C.IsContractedBy q) : 0 < qdeg hXQ C Q := by
  obtain ⟨m, hm, L, hL, hLQ, hamp⟩ := h
  haveI := hL.isInvertibleModule_divisorialSheaf
  have h1 := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy q _
    hamp C hC
  rw [qdeg_apply hXQ C Q (isQCartier_of_isQFactorial sX hXQ Q),
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul ℂ sX C.ι C.dim_le
      (fun E E' hE hE' => Divisor.degreeOn_add ℂ sX C.ι C.dim_le E E' hE hE') Q _ hm L hL hLQ]
  exact div_pos (by exact_mod_cast h1) (by exact_mod_cast hm)

end Forms

/-! ### Real divisors on a `ℚ`-factorial variety -/

section QFactorial

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is a real combination of Cartier divisors. -/
private theorem exists_presentation_of_isQFactorial (hXQ : IsQFactorial sX) (G : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      G = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hXQ.2 (Finsupp.single P 1)
  set s := G.support
  let P : Fin s.card → MMP.Mori.PrimeDivisor X := fun j => (s.equivFin.symm j : _)
  refine ⟨s.card, fun j => G (P j) / mq (P j),
    fun j => (mq (P j) : ℤ) • Finsupp.single (P j) 1, fun j => hmqC _, ?_⟩
  have key : ∀ Q : MMP.Mori.PrimeDivisor X, (G Q / mq Q) •
      Divisor.toRDivisor ((mq Q : ℤ) • Finsupp.single Q (1 : ℤ)) = Finsupp.single Q (G Q) := by
    intro Q
    have h0 : (mq Q : ℝ) ≠ 0 := by exact_mod_cast (hmq Q).ne'
    refine DivisorWithCoeffs.ext' fun T => ?_
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor]
    change (G Q / mq Q) • ((((mq Q : ℤ) • Finsupp.single Q (1 : ℤ)) T : ℤ) : ℝ) =
      Finsupp.single Q (G Q) T
    rw [Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · rw [smul_eq_mul, smul_eq_mul, mul_one, Int.cast_natCast, div_mul_cancel₀ _ h0]
    · rw [smul_eq_mul, smul_zero, Int.cast_zero, mul_zero]
  calc G = ∑ Q ∈ s, Finsupp.single Q (G Q) := (Finsupp.sum_single G).symm
    _ = ∑ Q : s, Finsupp.single (Q : MMP.Mori.PrimeDivisor X) (G Q) :=
        (Finset.sum_coe_sort s _).symm
    _ = ∑ j, (G (P j) / mq (P j)) •
          Divisor.toRDivisor ((mq (P j) : ℤ) • Finsupp.single (P j) (1 : ℤ)) := by
        rw [← Equiv.sum_comp s.equivFin.symm]
        exact Finset.sum_congr rfl fun j _ => (key _).symm

end QFactorial

/-! ### A negative curve and a negative relative extremal ray -/

section Ray

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- A divisor that is not `g`-nef is negative on some curve contracted by `g`, for the form of any
presentation. -/
private theorem exists_neg_of_not_isRelativelyNef {g : X ⟶ S} {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (hnef : ¬ IsRelativelyNef ℂ sX g D) :
    ∃ (C : ProperCurve sX) (hC : C.IsContractedBy g),
      presForm r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) < 0 := by
  by_contra! h
  exact hnef ⟨m, r, L, hL, hD, fun C hC x hx => by
    rw [eq_presForm_of_isRIntersectionNumber r L hL hD hx]; exact h C hC⟩

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
/-- A linear form on `N₁(X/S)` negative on the class of a contracted curve is negative on every
nonzero element of some extremal ray of `NE̅(X/S)`. -/
private theorem exists_isExtremalRay_neg [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
    [AlgebraicGeometry.IsProjectiveVariety ℂ sS] (g : X ⟶ S) (hg : g ≫ sS = sX)
    (φ : RelativeNumericalCurveClasses sX g →ₗ[ℝ] ℝ) {C : ProperCurve sX}
    (hC : C.IsContractedBy g) (hφ : φ (C.relativeClass g hC) < 0) :
    ∃ R : Set (RelativeNumericalCurveClasses sX g),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX g :
        Set (RelativeNumericalCurveClasses sX g)) R ∧ ∀ u ∈ R, u ≠ 0 → φ u < 0 := by
  have hz : C.relativeClass g hC ∈ relativeClosedConeOfCurves sX g := by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)
  obtain ⟨s, R, w, hRw, hsum⟩ :=
    exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sS g hg hz
  rw [hsum, map_sum] at hφ
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
    (f := fun i => φ (w i)) (g := fun _ => (0 : ℝ)) (by simpa using hφ)
  refine ⟨R i, (hRw i).1, ?_⟩
  obtain ⟨-, v, -, hRv⟩ := (hRw i).1
  have hwi := (hRw i).2
  rw [hRv] at hwi
  obtain ⟨c, hc, hcv⟩ := hwi
  have hφv : φ v < 0 := by
    rw [← hcv, map_smul, smul_eq_mul] at hi
    exact neg_of_mul_neg_right hi hc
  intro u hu hu0
  rw [hRv] at hu
  obtain ⟨c', hc', rfl⟩ := hu
  have hc'0 : c' ≠ 0 := by rintro rfl; exact hu0 (zero_smul _ _)
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc' (Ne.symm hc'0)) hφv

end Ray

/-! ### Rational klt vertices -/

section Vertex

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
private theorem sum_single_apply_of_injective {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    {p : ι → MMP.Mori.PrimeDivisor X} (hp : Function.Injective p) (v : ι → R) (i : ι) :
    (∑ i', Finsupp.single (p i') (v i') : MMP.Mori.PrimeDivisor X →₀ R) (p i) = v i := by
  classical
  rw [Finset.sum_apply', Finset.sum_eq_single i]
  · exact Finsupp.single_eq_same
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (hp.ne hb)]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
private theorem sum_single_apply_of_notMem {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    {p : ι → MMP.Mori.PrimeDivisor X} (v : ι → R) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∉ Set.range p) :
    (∑ i', Finsupp.single (p i') (v i') : MMP.Mori.PrimeDivisor X →₀ R) P = 0 := by
  classical
  rw [Finset.sum_apply']
  exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg fun h => hP ⟨i, h⟩]

/-- **A real klt boundary is a convex combination of rational klt boundaries.** -/
private theorem exists_convex_isKltPair (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXQ : IsQFactorial sX) (B : RDivisor X) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → QDivisor X) (w : ι → ℝ),
      (∀ j, IsKltPair sX (v j)) ∧ (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        B = ∑ j, w j • QDivisor.toRDivisor (v j) := by
  classical
  set s := B.support
  let p : Fin s.card → MMP.Mori.PrimeDivisor X := fun j => (s.equivFin.symm j : _)
  have hp : Function.Injective p := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  have hΔp : ∀ P, B.coeff P ≠ 0 → P ∈ Set.range p := fun P hP => by
    have hPs : P ∈ s := Finsupp.mem_support_iff.mpr hP
    exact ⟨s.equivFin ⟨P, hPs⟩, congrArg Subtype.val (s.equivFin.symm_apply_apply _)⟩
  obtain ⟨V0, -, hint, -, hklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sX hX hXQ
    B hB0 hB 0 le_rfl (by rw [map_zero]; exact hB0) p hp hΔp (fun P hP => absurd rfl hP)
  have hmem := intrinsicInterior_subset hint
  set φ : (Fin s.card → ℚ) → (Fin s.card → ℝ) := fun v i => (v i : ℝ)
  have hφi : Function.Injective φ := fun a b h =>
    funext fun i => Rat.cast_injective (congrFun h i)
  rw [← Finset.coe_image, Finset.mem_convexHull] at hmem
  obtain ⟨w, hw0, hw1, hwc⟩ := hmem
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1, Finset.sum_image fun a _ b _ h => hφi h] at hwc
  rw [Finset.sum_image fun a _ b _ h => hφi h] at hw1
  refine ⟨V0, inferInstance, fun j => ∑ i, Finsupp.single (p i) (j.1 i), fun j => w (φ j.1),
    fun j => hklt _ j.2, fun j => hw0 _ (Finset.mem_image_of_mem _ j.2), ?_, ?_⟩
  · exact (Finset.sum_coe_sort V0 (fun v => w (φ v))).trans hw1
  · refine DivisorWithCoeffs.ext' fun P => ?_
    have hcoeff : (∑ j : V0, w (φ j.1) •
        QDivisor.toRDivisor (∑ i, Finsupp.single (p i) (j.1 i))).coeff P =
        ∑ j : V0, w (φ j.1) *
          (((∑ i, Finsupp.single (p i) (j.1 i) : MMP.Mori.PrimeDivisor X →₀ ℚ) P : ℚ) : ℝ) := by
      change (∑ j : V0, w (φ j.1) •
        QDivisor.toRDivisor (∑ i, Finsupp.single (p i) (j.1 i))) P = _
      rw [Finset.sum_apply']
      rfl
    rw [hcoeff]
    by_cases h : P ∈ Set.range p
    · obtain ⟨i, rfl⟩ := h
      have hsum : ∀ j : V0,
          ((∑ i', Finsupp.single (p i') (j.1 i') : MMP.Mori.PrimeDivisor X →₀ ℚ) (p i)) =
            j.1 i := fun j => sum_single_apply_of_injective hp j.1 i
      simp_rw [hsum]
      have h1 : ∑ x ∈ V0, w (φ x) * ((x i : ℚ) : ℝ) = B.coeff (p i) := by
        rw [← congrFun hwc i, Finset.sum_apply]
        exact Finset.sum_congr rfl fun x _ => rfl
      rw [Finset.sum_coe_sort V0 (fun v => w (φ v) * ((v i : ℚ) : ℝ)), h1]
    · have hsum : ∀ j : V0,
          ((∑ i', Finsupp.single (p i') (j.1 i') : MMP.Mori.PrimeDivisor X →₀ ℚ) P) = 0 :=
        fun j => sum_single_apply_of_notMem j.1 h
      simp_rw [hsum, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
      exact not_not.mp fun hne => h (hΔp P hne)

end Vertex

/-! ### The contraction of the ray -/

section Contraction

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The class of a proper curve on a projective variety is nonzero. -/
private theorem numericalClass_ne_zero (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (C : ProperCurve sX) : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  obtain ⟨H, hH⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sX)
  intro h0
  have hpos := MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hX.toIsVariety H hH C
  have h1 : NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf H)
      (OneCycle.numericalClass sX (C.cycle ℝ)) = 0 := by rw [h0, map_zero]
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at h1
  exact hpos.ne' (by exact_mod_cast h1)

/-- A curve whose class comes from `N₁(X/S)` is contracted by `g`. -/
private theorem isContractedBy_of_mem_range {S : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {g : X ⟶ S} (hg : g ≫ sS = sX) {C : ProperCurve sX}
    (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ LinearMap.range (relativeToAbsolute sX g)) :
    C.IsContractedBy g := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sS := hS.toIsVariety.toLocallyOfFiniteType
  obtain ⟨A, hA⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sS)
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero g hg _
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple S _).mpr hA) C ?_
  obtain ⟨z, hz⟩ := hC
  have h1 := NumericalCurveClasses.degree_pushforward g hg
    (MMP.CartierDivisor.sheaf A) (relativeToAbsolute sX g z)
  rw [LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward g hg ⟨z, rfl⟩), map_zero,
    hz, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at h1
  exact_mod_cast h1.symm

/-- A divisor negative on a ray is anti-nef for the contraction of the ray. -/
private theorem isRelativelyNef_neg_of_isContractionOfRay (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} (hfR : IsContractionOfRay sX sZ R f)
    {D : RDivisor X} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j))
    (hneg : ∀ u ∈ R, u ≠ 0 → presForm r L hL u < 0) :
    IsRelativelyNef ℂ sX f (-D) := by
  have hnD : -D = ∑ j, (-r) j • Divisor.toRDivisor (L j) := by
    rw [hD, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, neg_smul]
  have hneg' : presForm (sX := sX) (-r) L hL = -presForm r L hL := by
    simp only [presForm, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  refine ⟨m, -r, L, hL, hnD, fun C hC x hx => ?_⟩
  rw [eq_presForm_of_isRIntersectionNumber (-r) L hL hnD hx, hneg', LinearMap.neg_apply]
  exact (neg_pos.mpr (hneg _ ((hfR.isContractedBy_iff C).1 hC)
    (numericalClass_ne_zero hX C))).le

/-- The contraction of a `D`-negative extremal ray spanned by a curve is a `D`-negative extremal
contraction. -/
private theorem isNegativeExtremalContraction_of_isContractionOfRay
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {K : Divisor X} {B₀ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B₀) R)
    {f : X ⟶ Z} (hfR : IsContractionOfRay sX sZ R f)
    (T : ProperCurve sX)
    (hRT : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w})
    {D : RDivisor X} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j))
    (hneg : ∀ u ∈ R, u ≠ 0 → presForm r L hL u < 0) :
    IsNegativeExtremalContraction ℂ sX sZ D f := by
  have hXv := hfR.isNormalVariety_source
  have hZv := hfR.isNormalVariety_target
  have hT0 := numericalClass_ne_zero hX T
  have hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R := hRT ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hTc : T.IsContractedBy f := (hfR.isContractedBy_iff T).2 hTR
  have hρ := MMP.Fourfold.relativePicardNumber_eq_one_of_isContractionOfRay hR ⟨T, hRT⟩ hfR
  have hfproper : IsProper f := isProper_of_isProjectiveMorphism f hfR.isProjectiveMorphism
  have hcont : MMP.Flips.IsContraction ℂ sZ sX f :=
    ⟨hZv.1, hXv.1, hfR.comp_eq, hfproper, hfR.isIso_app⟩
  have hnD : -D = ∑ j, (-r) j • Divisor.toRDivisor (L j) := by
    rw [hD, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, neg_smul]
  have hneg' : presForm (sX := sX) (-r) L hL = -presForm r L hL := by
    simp only [presForm, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  refine ⟨hXv, hZv, ⟨m, r, L, hL, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hD⟩,
    hcont, ?_, hρ⟩
  refine isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one sX sZ hXv hZv f
    (IsProjectiveMorphism.isProjective hfR.isProjectiveMorphism) hfR.comp_eq hρ (-D)
    ⟨m, -r, L, hL, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hnD⟩
    (isRelativelyNef_neg_of_isContractionOfRay hX hfR r L hL hD hneg) fun htriv => ?_
  have h₁ : IsRIntersectionNumber ℂ sX (-D) (-r) L T
      (presForm (-r) L hL (OneCycle.numericalClass sX (T.cycle ℝ))) := by
    rw [hnD]
    exact isRIntersectionNumber_presForm (-r) L hL T
  have h₀ : IsRIntersectionNumber ℂ sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) T 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have h2 := htriv.2.2 T hTc m (-r) L _ 0 _ _ _ h₁ h₀
  rw [hneg', LinearMap.neg_apply, neg_eq_zero] at h2
  exact (hneg _ hTR hT0).ne h2

end Contraction

/-! ### Comparison of log discrepancies over a common base -/

section Comparison

/-- An injective morphism contracts no proper curve. -/
private theorem not_isContractedBy_of_injective {Y W : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (q : Y ⟶ W) (hq : Function.Injective q) (C : ProperCurve sY) : ¬ C.IsContractedBy q := by
  intro hC
  have hcl : closure ({C.point} : Set Y) = {C.point} :=
    Set.Subset.antisymm (fun x hx => hq (hC x hx))
      (Set.singleton_subset_iff.mpr (subset_closure rfl))
  have hrange := range_curveSubschemeAtι C.point
  haveI : Subsingleton C.scheme := ⟨fun a b => (curveSubschemeAtι C.point).isEmbedding.injective
    (by
      have ha : curveSubschemeAtι C.point a ∈ closure ({C.point} : Set Y) :=
        hrange ▸ Set.mem_range_self a
      have hb : curveSubschemeAtι C.point b ∈ closure ({C.point} : Set Y) :=
        hrange ▸ Set.mem_range_self b
      rw [hcl] at ha hb
      exact ha.trans hb.symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- The push-forward along a birational morphism onto a normal variety has, along a prime divisor
`Q` which is the image of a prime divisor `P`, the coefficient of the divisor along `P`. -/
private theorem transformDivisor_apply_of_genericPoint_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z} [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Z} (h : f P.genericPoint = Q.genericPoint) :
    RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P := by
  haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsDominant f := hf.isDominant
  rw [RationalMap.transformDivisor]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr h)
    (fun P' hP' => ?_) D
  have := Q.isDiscreteValuationRing_localRing
  have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P' Q).mp hP'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Fourfold.eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective h1 h)

/-- Along a prime divisor which is not exceptional over `Z`, a divisor and the strict transform of
its push-forward to `Z` have the same coefficient. -/
private theorem apply_eq_birationalInverseTransform_transformDivisor {X Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z} [IsProper f]
    (hX : IsNormalVariety ℂ (f ≫ sZ)) (hf : IsBirationalMorphism f) (D : RDivisor X)
    {P : MMP.Mori.PrimeDivisor X} (hP : ¬ IsExceptionalPrimeDivisor sZ f P) :
    D P = birationalInverseTransform f hf
      (RationalMap.transformDivisor (X := X) f.toRationalMap D) P := by
  haveI : IsNormal X := hX.2
  haveI : LocallyOfFiniteType (f ≫ sZ) := hX.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sZ)
  let DP : MMP.Flips.ProperDivisorOver ℂ sZ :=
    MMP.Flips.ProperDivisorOver.mk ⟨X, f, hX, hf, P⟩ inferInstance
  obtain ⟨Q, -, hQ, -, -⟩ := DP.exists_primeDivisor_of_not_isExceptional hZ
    (fun h => hP ⟨hX, hf, inferInstance, h⟩)
  change f P.genericPoint = Q.genericPoint at hQ
  rw [MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hZ f hX.1 hf _ hQ,
    transformDivisor_apply_of_genericPoint_eq hZ hf D hQ]

/-- **Log discrepancies do not decrease over a common base** (FA 2.28). Let `f : X ⟶ Z` and
`g : Y ⟶ Z` be proper birational morphisms of normal varieties, with canonical divisors
`K_X = div(f^*ω)`, `K_Y = div(g^*ω)` for one rational form `ω` on `Z`, and `B_X`, `B_Y` real
divisors agreeing with the strict transforms of one divisor `D` on `Z` away from the exceptional
prime divisors. If `K_X + B_X`, `K_Y + B_Y` are `ℝ`-Cartier, `-(K_X + B_X)` is `f`-nef and
`K_Y + B_Y` is `g`-nef, then every divisor over `Y` with a proper model is realized by a divisor
over `X` with a proper model and no larger log discrepancy. -/
private theorem exists_isLogDiscrepancy_le_of_isRelativelyNef {X Y Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ]
    [LocallyOfFiniteType sZ] (hZ : IsNormalVariety ℂ sZ) (hX : IsNormalVariety ℂ sX)
    (hY : IsNormalVariety ℂ sY)
    {f : X ⟶ Z} {g : Y ⟶ Z} [IsProper f] [IsProper g] (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g)
    {n : ℕ} {ω : RationalPluriForms sZ n 1} {KX : Divisor X} {KY : Divisor Y}
    (hKX : haveI : IsDominant f := hf.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ f ω) = KX)
    (hKY : haveI : IsDominant g := hg.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ g ω) = KY)
    (hKXc : KX.IsCanonicalDivisor sX n) (hKYc : KY.IsCanonicalDivisor sY n)
    {D : RDivisor Z} {BX : RDivisor X} {BY : RDivisor Y}
    (hBX : ∀ P, ¬ IsExceptionalPrimeDivisor sZ f P → BX P = birationalInverseTransform f hf D P)
    (hBY : ∀ P, ¬ IsExceptionalPrimeDivisor sZ g P → BY P = birationalInverseTransform g hg D P)
    (hcX : IsCartierCombination (logCanonicalDivisor KX BX))
    (hcY : IsCartierCombination (logCanonicalDivisor KY BY))
    (hAX : IsRelativelyNef ℂ sX f (-logCanonicalDivisor KX BX))
    (hAY : IsRelativelyNef ℂ sY g (logCanonicalDivisor KY BY))
    {n' : ℕ} (E' : DivisorOver ℂ sY) (hE' : IsProper E'.f) {a' : ℝ}
    (ha' : MMP.Intersection.IsLogDiscrepancy sY n' BY E' a') :
    ∃ (E : DivisorOver ℂ sX) (_ : IsProper E.f), ∀ (n'' : ℕ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n'' BX E a → a ≤ a' := by
  subst hfs hgs
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant g := hg.isDominant
  haveI := hE'
  set EX : RDivisor X := BX - birationalInverseTransform f hf D with hEX
  set EY : RDivisor Y := BY - birationalInverseTransform g hg D with hEY
  have hDX : birationalInverseTransform f hf D + EX = BX := add_sub_cancel _ _
  have hDY : birationalInverseTransform g hg D + EY = BY := add_sub_cancel _ _
  have hEX0 : ∀ P, ¬ IsExceptionalPrimeDivisor sZ f P → EX.coeff P = 0 := fun P hP => by
    change (BX - _) P = 0
    rw [Finsupp.sub_apply, hBX P hP, sub_self]
  have hEY0 : ∀ P, ¬ IsExceptionalPrimeDivisor sZ g P → EY.coeff P = 0 := fun P hP => by
    change (BY - _) P = 0
    rw [Finsupp.sub_apply, hBY P hP, sub_self]
  have ha'FA := MMP.Fourfold.isDiscrepancy_of_isLogDiscrepancy hY hKYc hcY
    (E := ⟨E', hE'⟩) ha'
  let PZ : MMP.Flips.ProperDivisorOver ℂ sZ :=
    ⟨MMP.Mori.compDivisorOver g hY hg E', inferInstanceAs (IsProper (E'.f ≫ g))⟩
  have hPZ : PZ.valuation = E'.valuation.comap (functionFieldMap g) :=
    MMP.Mori.valuation_compDivisorOver g hY hg E'
  have hv : MMP.Flips.HasNonemptyCenter ℂ sZ (E'.valuation.comap (functionFieldMap g)) := by
    rw [← hPZ]
    haveI := PZ.isIntegral
    haveI := PZ.isNormal
    haveI := PZ.isLocallyNoetherian
    haveI := PZ.isDominant
    exact ⟨⟨PZ.Y, PZ.f ≫ sZ, PZ.isNormalVariety, PZ.E,
      functionFieldAlgEquiv sZ PZ.f PZ.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
      PZ, rfl⟩
  obtain ⟨D₁, hD₁, -⟩ :=
    MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZ.1 f hX.1 hf PZ
  refine ⟨D₁.toDivisorOver, D₁.isProper, fun n'' a ha => ?_⟩
  have haFA := MMP.Fourfold.isDiscrepancy_of_isLogDiscrepancy hX hKXc hcX (E := D₁) ha
  have hle := (MMP.Flips.isDiscrepancy_le_of_isRelativelyNef hZ hX hY hf hg hKX hKY hEX0 hEY0
    (by rw [hDX]; exact hAX) (by rw [hDY]; exact hAY) hv (hD₁.trans hPZ) rfl).2.2 (a - 1) (a' - 1)
    (by rw [hDX]; exact haFA) (by rw [hDY]; exact ha'FA)
  linarith

end Comparison

/-! ### The divisorial case -/

section Divisorial

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z]
  [IsNormal Z]

/-- **Discrepancies do not decrease under a divisorial contraction**: the push-forward of a real
klt boundary along a `(K + B)`-negative birational contraction to a `ℚ`-factorial variety is real
klt. The log discrepancies are compared over the target, with the identity as second model. -/
private theorem isRealKltPair_transformDivisor (hXQ : IsQFactorial sX) (hZQ : IsQFactorial sZ)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) {B : RDivisor X} (hB0 : 0 ≤ B)
    (hB : IsRealKltPair sX B) {f : X ⟶ Z}
    (hNE : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f)
    (hnef : IsRelativelyNef ℂ sX f (-logCanonicalDivisor K B)) (hfb : IsBirationalMorphism f) :
    IsRealKltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B) := by
  classical
  obtain ⟨n, hKn⟩ := hK
  have hXv := hNE.isNormalVariety_source
  have hZv := hNE.isNormalVariety_target
  have hcont := hNE.isContraction
  haveI : IsProper f := hcont.isProper
  haveI : QuasiCompact sZ := hZv.1.toQuasiCompact
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsDominant f := hfb.isDominant
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZv.1
  have hfs : f ≫ sZ = sX := hcont.comp_eq
  subst hfs
  have hdimXZ := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (f ≫ sZ) hfb
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZ hZv
    (hdimXZ.trans hKn.topologicalKrullDim_eq)
  have hKZ := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZv hXv hfb hK₀ hKn
  obtain ⟨ω, -, hωZ, hωX⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hZv hXv hfb hKZ hKn rfl
  set KZ := RationalMap.transformDivisor (X := X) f.toRationalMap K with hKZdef
  set BZ := RationalMap.transformDivisor (X := X) f.toRationalMap B with hBZ
  obtain ⟨mZ, rZ, LZ, hLZ, hKBZ⟩ := exists_presentation_of_isQFactorial hZQ
    (logCanonicalDivisor KZ BZ)
  have hcartZ : IsCartierCombination (logCanonicalDivisor KZ BZ) :=
    ⟨mZ, rZ, LZ, hLZ, by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hKBZ⟩
  refine ⟨hZv, fun Q => ?_, ⟨n, KZ, hKZ, mZ, rZ, LZ, hLZ, fun Γ => ?_⟩, fun n' E a' ha' => ?_⟩
  · haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZv
    change (RationalMap.transformDivisor (X := X) f.toRationalMap B) Q < 1
    rw [RationalMap.transformDivisor]
    by_cases hQ : ∃ P, RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P = some Q
    · obtain ⟨P, hP⟩ := hQ
      have huniq : ∀ P', RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P' = some Q →
          P' = P := fun P' hP' => by
        have := Q.isDiscreteValuationRing_localRing
        have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P' Q).mp hP'
        have h2 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mp hP
        exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (MMP.Fourfold.eq_of_map_eq_of_valuationRing hfb.functionFieldMap_bijective h1 h2)
      rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP huniq]
      exact hB.2.1 P
    · push Not at hQ
      rw [MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne hQ]
      exact one_pos
  · have hc := congrArg (fun D : RDivisor Z => D.coeff Γ) hKBZ
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at hc
    exact hc
  · have hEp : IsProper E.f := ha'.2.1
    have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ)
      hKZ.topologicalKrullDim_eq
    have hKZ' : divisorOfForm (pullbackRationalPluriForms sZ (𝟙 Z) ω) = KZ := by
      rw [pullbackRationalPluriForms_id hd]; exact hωZ
    have hg : IsBirationalMorphism (𝟙 Z) := isBirationalMorphism_of_isIso (𝟙 Z)
    have hnefZ : IsRelativelyNef ℂ sZ (𝟙 Z) (logCanonicalDivisor KZ BZ) :=
      ⟨mZ, rZ, LZ, hLZ, hKBZ, fun C hC =>
        (not_isContractedBy_of_injective (𝟙 Z) (fun _ _ h => h) C hC).elim⟩
    obtain ⟨D₁, hD₁p, hle⟩ := exists_isLogDiscrepancy_le_of_isRelativelyNef hZv hXv hZv rfl
      (Category.id_comp sZ) hfb hg hωX hKZ' hKn hKZ
      (fun P hP => apply_eq_birationalInverseTransform_transformDivisor hZv hXv hfb B hP)
      (fun Q _ => (MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hZv (𝟙 Z)
        (by rw [Category.id_comp]; exact hZv.1) hg BZ rfl).symm)
      hNE.isCartierCombination hcartZ hnef hnefZ E hEp ha'
    obtain ⟨ωX, hωX0, hωXK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hKn
    replace hωXK : divisorOfForm ωX = K := DivisorWithCoeffs.ext' hωXK
    obtain ⟨b, hb⟩ := exists_isLogDiscrepancy hXv hωX0 (hωXK ▸ hKn)
      (by rw [hωXK]; exact hNE.isCartierCombination) D₁ hD₁p
    exact lt_of_lt_of_le (hB.2.2.2 n D₁ b hb) (hle n b hb)

end Divisorial

/-! ### The small case -/

section SmallHelpers

/-- A small birational contraction onto a normal variety has exceptional set, in the sense of
the biregular locus, of codimension at least two. -/
private theorem two_le_closedsCodimension_exceptionalSet_of_isSmall {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] {f : X ⟶ Z} (hsm : IsSmall ℂ sZ sX f) :
    2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f) := by
  haveI : IsIntegral X := hsm.isVariety_source.toIsIntegral
  haveI : IsProper f := hsm.isProper
  have hFA := (MMP.Flips.le_closedsCodimension_iff_le_coheight
    (C := MMP.Flips.exceptionalCloseds f)).mp
    ((MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet
      hsm.toIsBirationalContraction).mp hsm)
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  by_contra hlt
  have hle : Order.coheight x ≤ 1 := by
    by_contra h1
    exact hlt (le_trans (by norm_num) (Order.add_one_le_of_lt (not_le.mp h1)))
  have hxFA : x ∉ MMP.Flips.exceptionalSet f := fun h => hlt (hFA x h)
  have hco : Order.coheight (f x) ≤ 1 := by
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hxFA]; exact hle
  exact hx (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f
    hsm.isBirationalMorphism hco)

/-- A morphism contracting a proper curve is not an isomorphism. -/
private theorem not_isIso_of_isContractedBy {Y W : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (q : Y ⟶ W) {C : ProperCurve sY} (hC : C.IsContractedBy q) : ¬ IsIso q := fun _ =>
  not_isContractedBy_of_injective q q.isOpenEmbedding.injective C hC

/-- A morphism with a flipping curve is not an isomorphism. -/
private theorem not_isIso_of_isFlippingCurve {Y W : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {q : Y ⟶ W} {C : Set Y} (hC : IsFlippingCurve ℂ sY sW q C) :
    ¬ IsIso q := by
  intro hiso
  obtain ⟨-, -, -, -, z, -, hmax, hdim⟩ := hC
  have hsub : C.Subsingleton := fun a ha b hb =>
    q.isOpenEmbedding.injective ((hmax.prop.2 ha).trans (hmax.prop.2 hb).symm)
  have : Subsingleton C := hsub.coe_sort
  have key : ∀ S : TopologicalSpace.IrreducibleCloseds C, (S : Set C) = Set.univ := fun S =>
    Set.eq_univ_of_forall fun x => by
      obtain ⟨y, hy⟩ := S.isIrreducible.nonempty
      rwa [Subsingleton.elim x y]
  have : Subsingleton (TopologicalSpace.IrreducibleCloseds C) :=
    ⟨fun S T => TopologicalSpace.IrreducibleCloseds.ext ((key S).trans (key T).symm)⟩
  have h0 : topologicalKrullDim C ≤ 0 := by
    rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
    intro a b _
    exact le_of_eq (Subsingleton.elim b a)
  exact absurd (lt_of_lt_of_le hdim h0) (lt_irrefl _)

/-- A proper birational morphism onto a normal variety which is not an isomorphism contracts a
proper curve. -/
private theorem exists_properCurve_isContractedBy_of_not_isIso {Y W : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hW : IsNormalVariety ℂ sW) (q : Y ⟶ W) (hq : q ≫ sW = sY) [IsProper q]
    (hqs : Function.Surjective q) (hqb : IsBirationalMorphism q) (hni : ¬ IsIso q) :
    ∃ C : ProperCurve sY, C.IsContractedBy q := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY.isProjective
  haveI : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  by_contra hno
  have hlqf : LocallyQuasiFinite q := by
    by_contra h
    exact hno (MMP.Fourfold.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  obtain ⟨hoi, -⟩ := isOpenImmersion_and_isIso_of_locallyQuasiFinite_of_isBirationalMorphism sY sW
    hY.toIsVariety hW q hq hqb
  exact hni ((isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨hoi, ⟨hqs⟩⟩)

/-- The strict transform back and forth along two small birational contractions is the
identity. -/
private theorem flipTransform_flipTransform {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] {f : X ⟶ Z}
    {fp : X' ⟶ Z} (hf : IsSmallMorphism sX sZ f) (hfp : IsSmallMorphism sX' sZ fp)
    (hfs : Function.Surjective f) {R : Type*} [AddCommMonoid R] (M : DivisorWithCoeffs R X') :
    flipTransform f fp (flipTransform fp f M) = M := by
  haveI := hf.isProper
  haveI := hfp.isProper
  refine DivisorWithCoeffs.ext' fun P => ?_
  change (flipTransform f fp (flipTransform fp f M)) P = M P
  obtain ⟨x, hx⟩ := hfs (fp P.genericPoint)
  obtain ⟨Pm, rfl, hPm⟩ :=
    exists_eq_genericPoint_flipTransform_apply hf.isBirationalMorphism hfp P x hx
  rw [hPm]
  obtain ⟨P', hP', hP'v⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfp.isBirationalMorphism hf Pm P.genericPoint hx.symm
  rw [hP'v, AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP'.symm]

/-- Every prime divisor `P` of the target `X⁺` of a small morphism `f⁺ : X⁺ ⟶ Z` lies over a
prime divisor `Q` of `Z`, which is the image of a prime divisor `Pₘ` of `X`, and the strict
transform from `X` to `X⁺` takes the coefficient along `Pₘ` to the coefficient along `P`. -/
private theorem exists_flipTransform_apply_eq {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral Z] {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} (hZ : IsNormalVariety ℂ sZ) [IsProper fm] (hfm : IsBirationalMorphism fm)
    (hfp : IsSmallMorphism sXp sZ fp) (P : MMP.Mori.PrimeDivisor Xp) :
    ∃ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Z),
      fm Pm.genericPoint = Q.genericPoint ∧ fp P.genericPoint = Q.genericPoint ∧
      ∀ {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm),
        flipTransform fm fp D P = D Pm := by
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfm hfp P
  have h1 := MMP.Fourfold.map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have h2 := MMP.Fourfold.map_genericPoint_eq_of_image_eq P Q hPQ
  obtain ⟨Pm', hPm', hD⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfm hfp P Pm.genericPoint (h1.trans h2.symm)
  obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPm'
  exact ⟨Pm, Q, h1, h2, hD⟩

/-- Pushing prime divisors forward commutes with changing the coefficients. -/
private theorem mapPrimeDivisors_mapCoeffs {X Y : Scheme.{0}} {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (g : R →+ S) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- Strict transforms commute with changing the coefficients. -/
private theorem flipTransform_mapCoeffs {X X' Z : Scheme.{0}} {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (f : X ⟶ Z) (fp : X' ⟶ Z) (g : R →+ S) (D : DivisorWithCoeffs R X) :
    flipTransform f fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffs]

/-- Strict transforms are `ℝ`-linear on real divisors. -/
private theorem flipTransform_smul {X X' Z : Scheme.{0}} (f : X ⟶ Z) (fp : X' ⟶ Z) (c : ℝ)
    (D : RDivisor X) : flipTransform f fp (c • D) = c • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

/-- An invertible module on an integral normal Noetherian scheme is `𝒪(D)` for a Cartier divisor
`D`, the divisor of a local frame. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

end SmallHelpers

/-! ### The small case -/

section Small

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z]
  [IsNormal Z]

/-- **The real flip of a small contraction.** The flip of a rational klt adjoint negative on the
ray is a real flip of the real adjoint, and the flipped pair is real klt. -/
private theorem exists_isRealFlipStep (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3) {n : ℕ} {K : Divisor X}
    (hKn : K.IsCanonicalDivisor sX n) {B : RDivisor X} (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B)
    {B₀ : QDivisor X} (hB₀ : IsKltPair sX B₀) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B₀) R) {f : X ⟶ Z}
    (hfR : IsContractionOfRay sX sZ R f) (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hamp : (-(Divisor.toQDivisor K + B₀)).HasRelativelyAmpleMultiple f)
    (T : ProperCurve sX)
    (hRT : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w})
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (hDneg : ∀ u ∈ R, u ≠ 0 → presForm (sX := sX) r L hL u < 0)
    (hNE : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f)
    (hsm : IsSmall ℂ sZ sX f) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
      (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
      (K' : Divisor X') (fp : X' ⟶ Z),
      IsRealFlipStep sX sZ sX' K B K' (flipTransform f fp B) f fp ∧
        MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
        topologicalKrullDim X' = 3 ∧ IsRealKltPair sX' (flipTransform f fp B) := by
  classical
  have hXv : IsNormalVariety ℂ sX := hfR.isNormalVariety_source
  have hZv : IsNormalVariety ℂ sZ := hfR.isNormalVariety_target
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZp
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZv.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfR.isProjectiveMorphism
  have hfb : IsBirationalMorphism f := hsm.isBirationalMorphism
  have hfcod := two_le_closedsCodimension_exceptionalSet_of_isSmall hsm
  have hfsm : IsSmallMorphism sX sZ f := ⟨hXv, hZv, hfR.comp_eq, inferInstance, hfb, hfcod⟩
  have hfs : Function.Surjective f := hfR.surjective
  obtain ⟨hD0q, hRext, hRneg0⟩ := id hR
  have hflipping : IsFlippingContraction sX sZ K B₀ f :=
    ⟨hXv, hZv, hfR.comp_eq, ⟨n, hKn⟩, hD0q, inferInstance, hfb, hfcod, hamp⟩
  obtain ⟨X', _, _, _, sX', fp, hflip⟩ :=
    exists_isFlip_of_isKltPair sX K B₀ hX hdim hXQ ⟨n, hKn⟩ hB₀ sZ R f hR hfR hflipping
  have hX'v : IsNormalVariety ℂ sX' := hflip.isNormalVariety
  haveI : IsIntegral X' := hX'v.1.toIsIntegral
  haveI : IsProper fp := hflip.isProper
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'v.1
  have hfpb : IsBirationalMorphism fp := hflip.isBirationalMorphism
  have hfpsm : IsSmallMorphism sX' sZ fp :=
    ⟨hX'v, hZv, hflip.comp_eq, inferInstance, hfpb, hflip.two_le_codimension⟩
  set D0 : QDivisor X := Divisor.toQDivisor K + B₀ with hD0def
  have hflipD0 : flipTransform f fp D0 =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B₀ := by
    rw [hD0def, map_add]
    congr 1
    exact flipTransform_mapCoeffs f fp _ K
  -- `f⁺` is projective, and so is `X⁺`
  obtain ⟨mA, hmA, LA, hLA, hLAeq, hLAamp⟩ := hflip.hasRelativelyAmpleMultiple
  have hfpP : IsProjective fp :=
    MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple ℂ sX' sZ fp hflip.comp_eq LA hLA
      hLAamp
  obtain ⟨H, hH⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sZ)
  have hfpproj : IsProjectiveMorphism fp :=
    AlgebraicGeometry.isProjectiveMorphism_of_isProjective fp _ hH hfpP
  have hX'p : MMP.Mori.IsProjectiveVariety ℂ sX' :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sX').mpr
      ⟨hX'v.1, hflip.comp_eq ▸ hfpproj.comp hZp.isProjective⟩
  have hdimX' : topologicalKrullDim X' = 3 :=
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX' hfpb).symm.trans
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb)).trans hdim
  -- the step diagram and its flip in the sense of *Flips and abundance*
  have hKp := MMP.Mori.IsFlip.isCanonicalDivisor_flipTransform hKn hflip
  have happp : ∀ U : Z.Opens, IsIso (fp.app U) :=
    (MMP.Flips.isIso_app_and_exists_isBiregular_of_isBirationalMorphism hZv fp
      (hflip.comp_eq ▸ hX'v.1) hfpb).1
  have hstep : IsThreefoldStepDiagram sX sZ sX' K B₀ f fp :=
    { isProjectiveVariety_minus := hX
      isNormalVariety_minus := hXv
      dim_minus := hdim
      isProjectiveVariety_plus := hX'p
      isNormalVariety_plus := hX'v
      dim_plus := hdimX'
      isProjectiveVariety_target := hZp
      isNormalVariety_target := hZv
      comp_eq_minus := hfR.comp_eq
      comp_eq_plus := hflip.comp_eq
      isProjectiveMorphism_minus := hfR.isProjectiveMorphism
      isProjectiveMorphism_plus := hfpproj
      isBirationalMorphism_minus := hfb
      isIso_app_minus := hfR.isIso_app
      isIso_app_plus := happp
      isSmallMorphism_plus := hfpsm
      isCanonicalDivisor := ⟨n, hKn⟩
      isCanonicalDivisor_plus := ⟨n, hKp⟩
      nonneg := hB₀.1.nonneg
      isQCartier_minus := hD0q
      isQCartier_plus := hflip.isQCartier
      hasRelativelyAmpleMultiple_minus := hamp
      hasRelativelyAmpleMultiple_plus := hflip.hasRelativelyAmpleMultiple }
  obtain ⟨φ, hφ, -⟩ := hstep.exists_isFlip hfsm hR ⟨T, hRT⟩ hfR
  have hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R := hRT ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hTc : T.IsContractedBy f := (hfR.isContractedBy_iff T).2 hTR
  have hfni : ¬ IsIso f := not_isIso_of_isContractedBy f hTc
  have hE : logCanonicalDivisor K (QDivisor.toRDivisor B₀) = QDivisor.toRDivisor D0 := by
    rw [hD0def, map_add, QDivisor.toRDivisor_toQDivisor]; rfl
  rw [hE] at hφ
  obtain ⟨Cf, hCf⟩ := MMP.Flips.IsFlip.exists_isFlippedCurveOf_of_not_isIso hD0q hφ hfni
  have hfpni : ¬ IsIso fp := not_isIso_of_isFlippingCurve hCf.2
  have hfpsurj : Function.Surjective fp :=
    hφ.isSmall.toIsBirationalContraction.surjective_and_isBirational.1.surj
  obtain ⟨Cp, hCp⟩ := exists_properCurve_isContractedBy_of_not_isIso hX'p hZv fp hflip.comp_eq
    hfpsurj hfpb hfpni
  -- the flip of `K + B₀` is a flip of every `ℚ`-divisor negative on the ray
  have hFO : IsFlipOf sX sZ sX' D0 f fp :=
    ⟨hD0q, hfR.toIsContraction, hfsm, hamp, hfpsm, hfpproj,
      by rw [hflipD0]; exact hflip.isQCartier,
      by rw [hflipD0]; exact hflip.hasRelativelyAmpleMultiple⟩
  have htransfer : ∀ Q : QDivisor X, IsNegativeExtremalRayOf sX Q R →
      IsFlipOf sX sZ sX' Q f fp := fun Q hQ =>
    IsFlipOf.of_isNegativeExtremalRayOf hX hXQ hB₀ ⟨n, hKn⟩ hR hfR hQ hR hFO
  have hX'Q : IsQFactorial sX' :=
    (IsKltPair.isQFactorial_of_isContractionOfRay hB₀ hX hXQ ⟨n, hKn⟩ hR hfR hfb).2 X' sX' fp
      hFO
  have hd0 : qdeg hXQ T D0 < 0 := by
    have h := hRneg0 _ hTR (numericalClass_ne_zero hX T)
    rw [curveForm_numericalClass_eq_qdeg hXQ T D0 hD0q] at h
    exact_mod_cast h
  have hneg_of : ∀ Q : QDivisor X, qdeg hXQ T Q < 0 → IsNegativeExtremalRayOf sX Q R :=
    fun Q hQ => ⟨isQCartier_of_isQFactorial sX hXQ Q, hRext, fun u hu hu0 => by
      rw [hRT] at hu
      obtain ⟨c, hc, rfl⟩ := hu
      have hc0 : c ≠ 0 := by rintro rfl; exact hu0 (zero_smul _ _)
      rw [map_smul, smul_eq_mul, curveForm_numericalClass_eq_qdeg hXQ T]
      exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) (by exact_mod_cast hQ)⟩
  set A' : QDivisor X' := flipTransform f fp D0 with hA'def
  have ha_pos : ∀ C : ProperCurve sX', C.IsContractedBy fp → 0 < qdeg hX'Q C A' := fun C hC =>
    qdeg_pos_of_hasRelativelyAmpleMultiple hX'Q hFO.hasRelativelyAmpleMultiple_flip C hC
  -- the key identity: on curves contracted by `f⁺`, every `ℚ`-divisor is proportional to `A'`
  have hlow : ∀ (M : QDivisor X') (C : ProperCurve sX'), C.IsContractedBy fp → ∀ s : ℚ,
      s < qdeg hXQ T (flipTransform fp f M) / qdeg hXQ T D0 →
        s * qdeg hX'Q C A' < qdeg hX'Q C M := by
    intro M C hC s hs
    have hQ : qdeg hXQ T (flipTransform fp f M - s • D0) < 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      have := (lt_div_iff_of_neg hd0).mp hs
      linarith
    have hFQ := htransfer _ (hneg_of _ hQ)
    have hQ' : flipTransform f fp (flipTransform fp f M - s • D0) = M - s • A' := by
      rw [map_sub, map_rat_smul, flipTransform_flipTransform hfsm hfpsm hfs M]
    have hpos := qdeg_pos_of_hasRelativelyAmpleMultiple hX'Q hFQ.hasRelativelyAmpleMultiple_flip
      C hC
    rw [hQ', map_sub, map_smul, smul_eq_mul] at hpos
    linarith
  have hkey : ∀ (M : QDivisor X') (C : ProperCurve sX'), C.IsContractedBy fp →
      qdeg hX'Q C M = qdeg hXQ T (flipTransform fp f M) / qdeg hXQ T D0 * qdeg hX'Q C A' := by
    intro M C hC
    have ha := ha_pos C hC
    set t := qdeg hXQ T (flipTransform fp f M) / qdeg hXQ T D0 with ht
    have h1 := hlow M C hC
    have h2 := hlow (-M) C hC
    have htneg : qdeg hXQ T (flipTransform fp f (-M)) / qdeg hXQ T D0 = -t := by
      rw [map_neg, map_neg, ht, neg_div]
    rw [htneg] at h2
    rcases lt_trichotomy (qdeg hX'Q C M) (t * qdeg hX'Q C A') with hlt | heq | hgt
    · have := h1 (qdeg hX'Q C M / qdeg hX'Q C A') (by rwa [div_lt_iff₀ ha])
      rw [div_mul_cancel₀ _ ha.ne'] at this
      exact absurd this (lt_irrefl _)
    · exact heq
    · have := h2 (-(qdeg hX'Q C M / qdeg hX'Q C A')) (by
        rw [neg_lt_neg_iff, lt_div_iff₀ ha]; exact hgt)
      rw [map_neg, neg_mul, div_mul_cancel₀ _ ha.ne'] at this
      exact absurd this (lt_irrefl _)
  -- `ρ(X⁺/Z) = 1`
  have hρ' : MMP.Flips.relativePicardNumber sX' fp = 1 := by
    let φC : ProperCurve sX' → (KCartierDivisor ℝ X' →ₗ[ℝ] ℝ) := fun C =>
      (OneCycle.intersectionPairing (sX := sX')).flip (C.cycle ℝ)
    have hφC : ∀ C B, φC C B = (C.cycle ℝ).intersectionNumber B := fun _ _ => rfl
    have hdegM : ∀ E : X'.CartierDivisor, ∃ M : Divisor X', ∃ _ : M.IsCartier,
        ∀ C' : ProperCurve sX', φC C' (KCartierDivisor.ofCartier ℝ E) =
          (qdeg hX'Q C' (Divisor.toQDivisor M) : ℝ) := by
      intro E
      obtain ⟨M, hMc, ⟨eM⟩⟩ :=
        exists_isCartier_divisorialSheaf_iso (MMP.CartierDivisor.sheaf E)
      refine ⟨M, hMc, fun C' => ?_⟩
      haveI := hMc.isInvertibleModule_divisorialSheaf
      rw [hφC, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
        OneCycle.degree_cycle, qdeg_toQDivisor hX'Q C' M hMc, ProperCurve.degree,
        ← degreeOn_eq_of_iso ℂ sX' C'.ι C'.dim_le eM]
      push_cast
      rfl
    have hlin : ∀ C : ProperCurve sX', C.IsContractedBy fp →
        (qdeg hX'Q Cp A' : ℝ) • φC C = (qdeg hX'Q C A' : ℝ) • φC Cp := by
      intro C hC
      refine Finsupp.lhom_ext fun E c => ?_
      obtain ⟨M, -, hM⟩ := hdegM E
      have e : (Finsupp.single E c : KCartierDivisor ℝ X') =
          c • KCartierDivisor.ofCartier ℝ E := by
        simp [KCartierDivisor.ofCartier]
      rw [LinearMap.smul_apply, LinearMap.smul_apply, e, map_smul, map_smul, hM C, hM Cp,
        hkey (Divisor.toQDivisor M) C hC, hkey (Divisor.toQDivisor M) Cp hCp]
      simp only [smul_eq_mul]
      push_cast
      ring
    have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX' fp = LinearMap.ker (φC Cp) := by
      ext B
      rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker]
      refine ⟨fun hB => hB Cp hCp, fun hB C hC => ?_⟩
      have h1 := LinearMap.congr_fun (hlin C hC) B
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hB, smul_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast (ha_pos Cp hCp).ne')
    have hsurj : Function.Surjective (φC Cp) := by
      obtain ⟨N, hN, LA', hLA'eq, hLA'c⟩ := (isQCartier_of_isQFactorial sX' hX'Q A').exists_pos
      haveI := hLA'c.isInvertibleModule_divisorialSheaf
      obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf LA'.divisorialSheaf
      have hE0 : φC Cp (KCartierDivisor.ofCartier ℝ E) ≠ 0 := by
        rw [hφC, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
          OneCycle.degree_cycle, ProperCurve.degree, ← degreeOn_eq_of_iso ℂ sX' Cp.ι Cp.dim_le e]
        have h1 := qdeg_toQDivisor hX'Q Cp LA' hLA'c
        rw [hLA'eq, map_zsmul, zsmul_eq_mul] at h1
        have h2 : (LA'.degreeOn ℂ sX' Cp.ι Cp.dim_le hLA'c : ℚ) ≠ 0 := by
          rw [← h1]; exact mul_ne_zero (by exact_mod_cast hN.ne') (ha_pos Cp hCp).ne'
        exact_mod_cast h2
      intro y
      exact ⟨(y / φC Cp (KCartierDivisor.ofCartier ℝ E)) • KCartierDivisor.ofCartier ℝ E, by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hE0]⟩
    have hrank := ((Submodule.quotEquivOfEq _ _ hker).trans
      ((φC Cp).quotKerEquivOfSurjective hsurj)).lift_rank_eq
    rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
    rw [MMP.Flips.relativePicardNumber, hrank, map_one]
  -- the real adjoint of the flip is `f⁺`-ample
  set K' : Divisor X' := flipTransform f fp K with hK'def
  set B' : RDivisor X' := flipTransform f fp B with hB'def
  have hDp : logCanonicalDivisor K' B' =
      ∑ i, r i • QDivisor.toRDivisor (flipTransform f fp (Divisor.toQDivisor (L i))) := by
    have h1 : logCanonicalDivisor K' B' = flipTransform f fp (logCanonicalDivisor K B) := by
      rw [logCanonicalDivisor, logCanonicalDivisor, map_add, hK'def, hB'def]
      congr 1
      exact (flipTransform_mapCoeffs f fp _ K).symm
    rw [h1, hD, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [flipTransform_smul, ← QDivisor.toRDivisor_toQDivisor]
    congr 1
    exact flipTransform_mapCoeffs f fp _ _
  obtain ⟨m', r', L', hL', hDp'⟩ := exists_presentation_of_isQFactorial hX'Q
    (logCanonicalDivisor K' B')
  have hform' := presForm_eq_sum_smul_curveForm (sX := sX')
    (fun i => flipTransform f fp (Divisor.toQDivisor (L i)))
    (fun i => isQCartier_of_isQFactorial sX' hX'Q _) r r' L' hL' (hDp.symm.trans hDp')
  have hDT : presForm r L hL (OneCycle.numericalClass sX (T.cycle ℝ)) < 0 :=
    hDneg _ hTR (numericalClass_ne_zero hX T)
  rw [presForm_numericalClass] at hDT
  have hpos : ∀ C : ProperCurve sX', C.IsContractedBy fp →
      0 < presForm r' L' hL' (OneCycle.numericalClass sX' (C.cycle ℝ)) := by
    intro C hC
    have ha := ha_pos C hC
    rw [hform', LinearMap.sum_apply]
    have hterm : ∀ i, (r i • QDivisor.curveForm sX' (flipTransform f fp (Divisor.toQDivisor (L i)))
        (isQCartier_of_isQFactorial sX' hX'Q _)) (OneCycle.numericalClass sX' (C.cycle ℝ)) =
        ((qdeg hX'Q C A' : ℝ) / (qdeg hXQ T D0 : ℝ)) *
          (r i * ((L i).degreeOn ℂ sX T.ι T.dim_le (hL i) : ℝ)) := by
      intro i
      rw [LinearMap.smul_apply, smul_eq_mul, curveForm_numericalClass_eq_qdeg hX'Q, hkey _ C hC,
        flipTransform_flipTransform hfpsm hfsm hfpsurj, qdeg_toQDivisor hXQ T (L i) (hL i)]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
    exact mul_pos_of_neg_of_neg (div_neg_of_pos_of_neg (by exact_mod_cast ha)
      (by exact_mod_cast hd0)) hDT
  have hcartD' : IsCartierCombination (logCanonicalDivisor K' B') :=
    ⟨m', r', L', hL', by simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hDp'⟩
  have hnefD' : IsRelativelyNef ℂ sX' fp (logCanonicalDivisor K' B') :=
    ⟨m', r', L', hL', hDp', fun C hC x hx => by
      rw [eq_presForm_of_isRIntersectionNumber r' L' hL' hDp' hx]
      exact (hpos C hC).le⟩
  have hampD' : MMP.Flips.IsRelativelyAmple fp (logCanonicalDivisor K' B') := by
    refine isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one sX' sZ hX'v hZv fp
      hfpP hflip.comp_eq hρ' _ hcartD' hnefD' ?_
    · intro htriv
      have h₁ : IsRIntersectionNumber ℂ sX' (logCanonicalDivisor K' B') r' L' Cp
          (presForm r' L' hL' (OneCycle.numericalClass sX' (Cp.cycle ℝ))) := by
        rw [hDp']; exact isRIntersectionNumber_presForm r' L' hL' Cp
      have h₀ : IsRIntersectionNumber ℂ sX' (0 : RDivisor X') (Fin.elim0 : Fin 0 → ℝ)
          (Fin.elim0 : Fin 0 → Divisor X') Cp 0 :=
        ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
      exact (hpos Cp hCp).ne' (htriv.2.2 Cp hCp _ _ _ _ 0 _ _ _ h₁ h₀)
  -- the real flip step
  have hstepR : IsRealFlipStep sX sZ sX' K B K' B' f fp :=
    { isQuasiProjectiveVariety_target := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ
      isNegativeExtremalContraction := hNE
      isSmall := hsm
      isBirationalMorphism := hfb
      isProjectiveMorphism := hfR.isProjectiveMorphism
      not_isIso := hfni
      isCanonicalDivisor_flip := ⟨n, hKp⟩
      isSmall_flip := hfpsm.isSmall happp
      isBirationalMorphism_flip := hfpb
      isProjectiveMorphism_flip := hfpproj
      not_isIso_flip := hfpni
      relativePicardNumber_flip := hρ'
      isRelativelyAmple_flip := hampD'
      eq_flipTransform := rfl }
  refine ⟨X', inferInstance, inferInstance, inferInstance, inferInstance, sX', K', fp, hstepR, hX'p,
    hX'Q, hdimX', ?_⟩
  refine ⟨hX'v, fun P => ?_, ⟨n, K', hKp, m', r', L', hL', fun Γ => ?_⟩, fun n' E' a' ha' => ?_⟩
  · obtain ⟨x, hx⟩ := hfs (fp P.genericPoint)
    obtain ⟨Pm, -, hPm⟩ := exists_eq_genericPoint_flipTransform_apply hfb hfpsm P x hx
    change flipTransform f fp B P < 1
    rw [hPm B]
    exact hB.2.1 Pm
  · have hc := congrArg (fun D : RDivisor X' => D.coeff Γ) hDp'
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at hc
    exact hc
  · haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
    haveI : QuasiCompact sZ := hZv.1.toQuasiCompact
    haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
    haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
    haveI : IsDominant f := hfb.isDominant
    haveI : IsDominant fp := hfpb.isDominant
    have hfs : f ≫ sZ = sX := hfR.comp_eq
    have hXvZ : IsNormalVariety ℂ (f ≫ sZ) := by rw [hfs]; exact hXv
    have hX'vZ : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hflip.comp_eq]; exact hX'v
    have hKnZ : K.IsCanonicalDivisor (f ≫ sZ) n := by rw [hfs]; exact hKn
    haveI : LocallyOfFiniteType (f ≫ sZ) := hXvZ.1.toLocallyOfFiniteType
    haveI : AlgebraicGeometry.IsVariety ℂ (f ≫ sZ) := hXvZ.1
    -- compatible canonical divisors `K = div(f^*ω)`, `K⁺ = div(f⁺^*ω)`
    have hdimXZ := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (f ≫ sZ) hfb
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZ hZv
      (hdimXZ.trans hKnZ.topologicalKrullDim_eq)
    have hKZ := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZv hXvZ hfb hK₀ hKnZ
    obtain ⟨ω, -, -, hωX⟩ :=
      MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hZv hXvZ hfb hKZ hKnZ rfl
    have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ)
      hKZ.topologicalKrullDim_eq
    have hKω : divisorOfForm (pullbackRationalPluriForms sZ fp ω) = K' := by
      refine Finsupp.ext fun P' => ?_
      obtain ⟨Pm, Q, hPm, hP', hfl⟩ := exists_flipTransform_apply_eq hZv hfb hfpsm P'
      have := Q.isDiscreteValuationRing_localRing
      haveI : ValuationRing (Z.presheaf.stalk (fp P'.genericPoint)) := by
        rw [hP']; infer_instance
      haveI : ValuationRing (Z.presheaf.stalk (f Pm.genericPoint)) := by
        rw [hPm]; infer_instance
      haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hfpb.functionFieldMap_bijective
        P'.genericPoint
      haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hfb.functionFieldMap_bijective
        Pm.genericPoint
      change P'.ordForm (pullbackRationalPluriForms sZ fp ω) = flipTransform f fp K P'
      rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
          hfpb.functionFieldMap_bijective hd P' Q hP' ω,
        ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f
          hfb.functionFieldMap_bijective hd Pm Q hPm ω, hfl K, ← hωX]
      rfl
    have hBY : ∀ P', ¬ IsExceptionalPrimeDivisor sZ fp P' → B' P' =
        birationalInverseTransform fp hfpb (RationalMap.transformDivisor (X := X)
          f.toRationalMap B) P' := fun P' _ => by
      obtain ⟨Pm, Q, hPm, hP', hfl⟩ := exists_flipTransform_apply_eq hZv hfb hfpsm P'
      change flipTransform f fp B P' = _
      rw [hfl B, MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hZv fp hX'vZ.1 hfpb
        _ hP', transformDivisor_apply_of_genericPoint_eq hZv hfb B hPm]
    obtain ⟨E, hEp, hle⟩ := exists_isLogDiscrepancy_le_of_isRelativelyNef hZv hXv hX'v
      hfR.comp_eq hflip.comp_eq hfb hfpb hωX hKω hKn hKp
      (fun P hP => apply_eq_birationalInverseTransform_transformDivisor hZv hXvZ hfb B hP) hBY
      hNE.isCartierCombination hcartD'
      (isRelativelyNef_neg_of_isContractionOfRay hX hfR r L hL hD hDneg) hnefD' E' ha'.2.1 ha'
    obtain ⟨ωX, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hKn
    replace hωK : divisorOfForm ωX = K := DivisorWithCoeffs.ext' hωK
    obtain ⟨a, ha⟩ := exists_isLogDiscrepancy hXv hω0 (hωK ▸ hKn)
      (by rw [hωK]; exact hNE.isCartierCombination) E hEp
    exact lt_of_lt_of_le (hB.2.2.2 n E a ha) (hle n a ha)

end Small

private theorem solution
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B)
    (hnef : ¬ IsRelativelyNef ℂ sX g (logCanonicalDivisor K B)) :
    ∃ (R : Set (RelativeNumericalCurveClasses sX g)) (Z : Scheme.{0})
      (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L C x → x < 0) ∧
        IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        ((IsBirationalMorphism f ∧
            ∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) →
          IsQFactorial sZ ∧
            IsRealKltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B)) ∧
        (IsSmall ℂ sZ sX f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (K' : Divisor X') (fp : X' ⟶ Z),
            IsRealFlipStep sX sZ sX' K B K' (flipTransform f fp B) f fp ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 3 ∧ IsRealKltPair sX' (flipTransform f fp B)) := by
  classical
  have hXv : IsNormalVariety ℂ sX := hB.1
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨m, r, L, hL, hD⟩ := exists_presentation_of_isQFactorial hXQ (logCanonicalDivisor K B)
  obtain ⟨C₀, hC₀, hC₀neg⟩ := exists_neg_of_not_isRelativelyNef r L hL hD hnef
  obtain ⟨R, hR, hRneg⟩ := exists_isExtremalRay_neg (sS := sS) g hg
    (presForm r L hL ∘ₗ relativeToAbsolute sX g) hC₀ hC₀neg
  obtain ⟨J, _, v, w, hvklt, hw0, hw1, hBw⟩ := exists_convex_isKltPair hX hXQ B hB0 hB
  have hq : ∀ j, (Divisor.toQDivisor K + v j).IsQCartier := fun j =>
    isQCartier_of_isQFactorial sX hXQ _
  have hform := presForm_eq_sum_curveForm (sX := sX) K v w hq hw1 r L hL
    (by rw [← hBw]; exact hD)
  obtain ⟨u₀, hu₀, hRu₀⟩ := hR.2
  have hu₀R : u₀ ∈ R := hRu₀ ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hneg₀ : presForm r L hL (relativeToAbsolute sX g u₀) < 0 := hRneg u₀ hu₀R hu₀
  obtain ⟨j₀, hj₀⟩ : ∃ j, QDivisor.curveForm sX (Divisor.toQDivisor K + v j) (hq j)
      (relativeToAbsolute sX g u₀) < 0 := by
    rw [hform, LinearMap.sum_apply] at hneg₀
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun j => (w j • QDivisor.curveForm sX (Divisor.toQDivisor K + v j) (hq j))
        (relativeToAbsolute sX g u₀)) (g := fun _ => (0 : ℝ)) (by simpa using hneg₀)
    rw [LinearMap.smul_apply, smul_eq_mul] at hj
    exact ⟨j, neg_of_mul_neg_right hj (hw0 j)⟩
  have hmemR : ∀ u ∈ R, ∃ c : ℝ, 0 ≤ c ∧ c • u₀ = u := fun u hu => by rwa [hRu₀] at hu
  have hRabs : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + v j₀)
      (relativeToAbsolute sX g '' R) := by
    refine ⟨hq j₀, isExtremalRay_image_relativeToAbsolute sX sS g hg hR, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hu0
    obtain ⟨c, hc, rfl⟩ := hmemR u hu
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hu0 (by rw [zero_smul, map_zero])
    rw [map_smul, map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hj₀
  have hDabs : ∀ u ∈ relativeToAbsolute sX g '' R, u ≠ 0 → presForm r L hL u < 0 := by
    rintro _ ⟨u, hu, rfl⟩ hu0
    exact hRneg u hu fun h0 => hu0 (by rw [h0, map_zero])
  obtain ⟨⟨T, -, hRT⟩, Z, sZ, f, hfR, hZp, -, hamp⟩ :=
    exists_isContractionOfRay_of_isKltPair sX hX (hvklt j₀) hKn hRabs
  have hZv : IsNormalVariety ℂ sZ := hfR.isNormalVariety_target
  haveI : IsIntegral Z := hZv.1.toIsIntegral
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hinj : Function.Injective (relativeToAbsolute sX g) :=
    (existsUnique_isNaturalRelativeMap_and_injective sX g).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX g)
  have hcontr : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈
      relativeToAbsolute sX g '' R → C.IsContractedBy g := by
    rintro C ⟨u, -, hu⟩
    exact isContractedBy_of_mem_range hX hS hg ⟨u, hu⟩
  have hgproj : IsProjectiveMorphism g :=
    IsProjectiveMorphism.of_comp g sS (by rw [hg]; exact hX.isProjective)
  obtain ⟨h, hfh, -⟩ :=
    existsUnique_comp_eq_of_isContractionOfRay hX hgproj hg hRabs.2.1 hcontr hfR
  have hhs : h ≫ sS = sZ := by
    have hall : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈
        relativeToAbsolute sX g '' R → C.IsContractedBy sX := fun C _ x _ =>
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    obtain ⟨h', -, huniq⟩ := existsUnique_comp_eq_of_isContractionOfRay
      (sZ := 𝟙 (Spec (.of ℂ))) hX hX.isProjective (Category.comp_id _) hRabs.2.1 hall hfR
    rw [huniq (h ≫ sS) (by show f ≫ h ≫ sS = sX; rw [← Category.assoc, hfh, hg]),
      huniq sZ hfR.comp_eq]
  have hRC : IsRelativeContractionOfFace g R f h :=
    { isExtremalFace := hR.1
      isProjectiveMorphism :=
        IsProjectiveMorphism.of_comp h sS (by rw [hhs]; exact hZp.isProjective)
      comp_eq := hfh
      isIso_app := hfR.isIso_app
      isContractedBy_iff := fun C hC => by
        rw [hfR.isContractedBy_iff C]
        exact ⟨fun ⟨u, hu, hu'⟩ => (hinj hu' : u = C.relativeClass g hC) ▸ hu,
          fun hC' => ⟨_, hC', rfl⟩⟩ }
  have hNE : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f :=
    isNegativeExtremalContraction_of_isContractionOfRay hX hRabs hfR T hRT r L hL hD hDabs
  refine ⟨R, Z, inferInstance, inferInstance, inferInstance, sZ, f, h, hR, ?_, hRC, hZp, hNE, ?_,
    ?_⟩
  · intro C hC hCR m' r' L' x hx
    rw [eq_presForm_of_isRIntersectionNumber r L hL hD hx]
    exact hRneg _ hCR fun h0 => numericalClass_ne_zero hX C
      (show relativeToAbsolute sX g (C.relativeClass g hC) = 0 by rw [h0, map_zero])
  · rintro ⟨hfb, hE⟩
    have hZQ : IsQFactorial sZ :=
      (IsKltPair.isQFactorial_of_isContractionOfRay (hvklt j₀) hX hXQ ⟨n, hKn⟩ hRabs hfR hfb).1 hE
    exact ⟨hZQ, isRealKltPair_transformDivisor hXQ hZQ ⟨n, hKn⟩ hB0 hB hNE
      (isRelativelyNef_neg_of_isContractionOfRay hX hfR r L hL hD hDabs) hfb⟩
  · intro hsm
    exact exists_isRealFlipStep hX hXQ hdim hKn hB0 hB (hvklt j₀) hRabs hfR hZp hamp T hRT r L
      hL hD hDabs hNE hsm

end Proof_lem_fourfold_real_klt_elementary_step

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Elementary steps of real klt threefolds.** Let `g : X ⟶ S` be a morphism of projective
complex varieties, `X` a normal `ℚ`-factorial threefold with canonical divisor `K`, and `(X, B)` a
klt pair with effective real boundary. If `K + B` is not `g`-nef, there are a `(K + B)`-negative
extremal ray `R` of `NE̅(X/S)` and its contraction `f : X ⟶ Z`, `h : Z ⟶ S` over `S`, with `Z`
projective, `-(K + B)` `f`-ample and `ρ(X/Z) = 1`, such that

* if `f` is divisorial, `Z` is `ℚ`-factorial and `(Z, f_* B)` is klt;
* if `f` is small, there is a step of an extremal real flip sequence `X ⟶ Z ⟵ X⁺` with `X⁺` a
  projective `ℚ`-factorial threefold, and `(X⁺, (f⁺)⁻¹_* f_* B)` is klt. -/
@[mmp "lem_fourfold_real_klt_elementary_step"]
public theorem IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B)
    (hnef : ¬ IsRelativelyNef ℂ sX g (logCanonicalDivisor K B)) :
    ∃ (R : Set (RelativeNumericalCurveClasses sX g)) (Z : Scheme.{0})
      (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L C x → x < 0) ∧
        IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        ((IsBirationalMorphism f ∧
            ∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) →
          IsQFactorial sZ ∧
            IsRealKltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B)) ∧
        (IsSmall ℂ sZ sX f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (K' : Divisor X') (fp : X' ⟶ Z),
            IsRealFlipStep sX sZ sX' K B K' (flipTransform f fp B) f fp ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 3 ∧ IsRealKltPair sX' (flipTransform f fp B)) :=
  Proof_lem_fourfold_real_klt_elementary_step.solution hX hS hg hXQ hdim hK hB0 hB hnef

end MMP.Fourfold
