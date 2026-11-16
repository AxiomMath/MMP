module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength

/-!
# The cone theorem with an ample perturbation: finitely many extremal rays

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective, of dimension `n`. For every ample `ℚ`-divisor `H`
and every real `ε > 0` there are finitely many rational curves `C_1, …, C_k ⊆ X` with
`0 < -((K_X + Δ) · C_j) ≤ 2n`, each spanning an extremal ray `ℝ_{≥0}[C_j]` of `NE̅(X)`, such that
`NE̅(X) = NE̅(X)_{(K_X + Δ + εH) ≥ 0} + ∑_j ℝ_{≥0}[C_j]`.

## Main results

* `MMP.Mori.exists_finset_isRationalCurve_closedConeOfCurves_eq`: the statement above.

## Implementation notes

The curves form a `Finset` `S` of `MMP.Mori.ProperCurve`s; the rational curve attached to
`C ∈ S` is the reduced closure of its generic point and its class is
`OneCycle.numericalClass sX (C.cycle ℝ)`. The sum `∑_j ℝ_{≥0}[C_j]` of rays is the convex cone
`PointedCone.hull ℝ` of these classes, and the sum with `NE̅(X)_{(K_X + Δ + εH) ≥ 0}` is the
pointwise sum of sets. Since `ε` is real, `K_X + Δ + εH` is an `ℝ`-divisor; its form on `N₁(X)`
is `(K_X + Δ) · z + ε (H · z)`, with both forms `MMP.Fourfold.QDivisor.curveForm`. The
`ℚ`-Cartier witness for `H` is the one its ampleness provides (`curveForm` does not depend on
the witness).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7(2)
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct Pointwise MMP.Mori
  MMP.Positivity

namespace MMP.FourfoldProofs.Km3bConeFiniteProof

/-- The curve form of a nef `ℚ`-Cartier `ℚ`-divisor is nonnegative on `NE̅(X)`. -/
private theorem curveForm_nonneg_of_isNef {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {D : QDivisor X} (hD : D.IsNef k sX) (h : D.IsQCartier) :
    ∀ z ∈ closedConeOfCurves sX, 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h z := by
  have hcont : Continuous (MMP.Fourfold.QDivisor.curveForm sX D h) := by
    unfold MMP.Fourfold.QDivisor.curveForm Finsupp.sum
    rw [LinearMap.coe_sum, Finset.sum_fn]
    refine continuous_finset_sum _ fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    exact (NumericalCurveClasses.continuous_degree sX _).const_smul _
  intro z hz
  replace hz : z ∈ closure (coneOfCurves sX : Set (NumericalCurveClasses sX)) := hz
  refine closure_minimal (s := (coneOfCurves sX : Set (NumericalCurveClasses sX)))
    (t := ((PointedCone.positive ℝ ℝ).comap (MMP.Fourfold.QDivisor.curveForm sX D h) :
      Set (NumericalCurveClasses sX))) (Submodule.span_le.2 ?_)
    (isClosed_Ici.preimage hcont) hz
  rintro _ ⟨C, rfl⟩
  obtain ⟨hq, hC⟩ := hD
  change 0 ≤ MMP.Fourfold.QDivisor.curveForm sX D h _
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  exact_mod_cast hC C.scheme C.ι C.dim_eq

/-- **Kleiman positivity for ample `ℚ`-divisors.** The curve form of an ample `ℚ`-divisor `H`
on a projective variety is positive on `NE̅(X) ∖ {0}`. -/
private theorem curveForm_pos_of_isAmple {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX] {H : QDivisor X}
    (hH : H.IsAmple) (h : H.IsQCartier) :
    ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < MMP.Fourfold.QDivisor.curveForm sX H h z := by
  intro z hz hz0
  obtain ⟨m, hm, L, hLH, hL, hamp⟩ := hH
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  have hE : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf E) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hamp
  obtain ⟨Zc, hZc⟩ := OneCycle.numericalClass_surjective sX z
  have hpos := closedConeOfCurves_diff_zero_subset_posHalfspace sX E hE ⟨hz, hz0⟩ Zc hZc
  -- the degree form of `𝒪_X(L)` is `m` times the curve form of `H`
  have hdeg : NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) =
      (m : ℝ) • MMP.Fourfold.QDivisor.curveForm sX H h := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
    have hd : C.degree k (MMP.CartierDivisor.sheaf E) =
        C.degree k L.divisorialSheaf := (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm
    rw [hd, ProperCurve.degree_divisorialSheaf C L hL,
      QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k sX C.ι C.dim_le
        (Divisor.degreeOn_add k sX C.ι C.dim_le) H h hm L hL
        (by rw [hLH, natCast_zsmul, Nat.cast_smul_eq_nsmul])]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    rw [smul_eq_mul, mul_div_cancel₀ _ this]
  rw [← NumericalCurveClasses.intersectionNumber_numericalClass, hZc,
    NumericalCurveClasses.intersectionNumber_ofCartier, hdeg, LinearMap.smul_apply,
    smul_eq_mul] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- The pointed cone generated by classes of curves lies in `NE̅(X)`. -/
private theorem hull_le_closedConeOfCurves {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (S : Set (ProperCurve sX)) :
    PointedCone.hull ℝ ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' S)
      ≤ closedConeOfCurves sX :=
  Submodule.span_le.2 (by
    rintro _ ⟨C, -, rfl⟩
    exact coneOfCurves_le_closedConeOfCurves sX (Submodule.subset_span ⟨C, rfl⟩))

/-- A set `C` lies in `(C ∩ {κ + ε γ ≥ 0}) + P` when `κ`, `γ` are nonnegative on `C` and
`ε ≥ 0`. -/
private theorem subset_inter_add_of_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] {C : Set V}
    (P : PointedCone ℝ V) {κ γ : V →ₗ[ℝ] ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hκ : ∀ x ∈ C, 0 ≤ κ x)
    (hγ : ∀ x ∈ C, 0 ≤ γ x) : C ⊆ (C ∩ {z | 0 ≤ κ z + ε * γ z}) + (P : Set V) :=
  fun x hx => ⟨x, ⟨hx, add_nonneg (hκ x hx) (mul_nonneg hε (hγ x hx))⟩, 0, P.zero_mem, add_zero x⟩

/-- For a non-nef klt `K + Δ`, the cone datum on the numerical curve lattice, transported to
`N₁(X)` along the base-change isomorphism `ψ`. -/
private theorem exists_coneDatum_linearEquiv {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    (hnef : ¬ QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)) :
    ∃ (_ : Module.Free ℤ (numericalCurveLattice sX))
      (_ : Module.Finite ℤ (numericalCurveLattice sX))
      (D : ConeDatum (numericalCurveLattice sX))
      (ψ : ℝ ⊗[ℤ] numericalCurveLattice sX ≃ₗ[ℝ] NumericalCurveClasses sX),
      (∀ w, w ∈ D.cone ↔ ψ w ∈ closedConeOfCurves sX) ∧
      ∀ w, realOfRatForm _ D.form w =
        MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 (ψ w) := by
  obtain ⟨m, hm, hCart⟩ := hklt.1.2.2.exists_pos
  obtain ⟨_, _, hbij, -, D, hDcone, hDform, -⟩ :=
    exists_coneDatum_numericalCurveLattice_of_isKltPair hklt hΔ hnef (a := (m : ℤ))
      (by exact_mod_cast hm) hCart
  refine ⟨‹_›, ‹_›, D, LinearEquiv.ofBijective _ hbij, fun w => ?_, fun w => ?_⟩
  · rw [← SetLike.mem_coe, hDcone]
    rfl
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r z =>
    simp [realOfRatForm_tmul, LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul,
      hDform]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The image under `ψ` of a negative rational ray of a cone datum matching `NE̅(X)` and the
form of `B` is a `B`-negative extremal ray of `NE̅(X)`. -/
private theorem isNegativeExtremalRayOf_image_of_mem_negativeRationalRays {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [QuasiCompact sX] [Module.Free ℤ (numericalCurveLattice sX)]
    [Module.Finite ℤ (numericalCurveLattice sX)] {B : QDivisor X} (hB : B.IsQCartier)
    (D : ConeDatum (numericalCurveLattice sX))
    (ψ : ℝ ⊗[ℤ] numericalCurveLattice sX ≃ₗ[ℝ] NumericalCurveClasses sX)
    (hDc : ∀ w, w ∈ D.cone ↔ ψ w ∈ closedConeOfCurves sX)
    (hψK : ∀ w, realOfRatForm _ D.form w = MMP.Fourfold.QDivisor.curveForm sX B hB (ψ w)) :
    ∀ R ∈ D.negativeRationalRays, MMP.Fourfold.IsNegativeExtremalRayOf sX B (ψ '' R) := by
  rintro R ⟨ξ, hξ, hRξ, L, hL, hRL⟩
  have hface : ψ '' R = faceOfNefForm (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (realOfRatForm _ L ∘ₗ ψ.symm.toLinearMap) := by
    ext x
    rw [hRL]
    constructor
    · rintro ⟨w, ⟨hw, hL0⟩, rfl⟩
      exact ⟨(hDc w).1 hw, by simpa using hL0⟩
    · rintro ⟨hx, h0⟩
      exact ⟨ψ.symm x, ⟨(hDc _).2 (by simpa using hx), by simpa using h0⟩, by simp⟩
  refine ⟨hB, ⟨?_, ψ ξ, ?_, ?_⟩, ?_⟩
  · rw [hface]
    exact isExtremalFace_faceOfNefForm (isCone_coe _) (fun u hu v hv => add_mem hu hv)
      fun z hz => by simpa using hL (ψ.symm z) ((hDc _).2 (by simpa using hz))
  · intro h
    have := hψK ξ
    rw [h, map_zero] at this
    linarith
  · rw [hRξ]
    ext x
    constructor
    · rintro ⟨w, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • ξ, ⟨c, hc, rfl⟩, by rw [map_smul]⟩
  · rintro u ⟨w, hw, rfl⟩ hu0
    rw [hRξ] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    have hc0 : 0 < c := lt_of_le_of_ne hc fun h => hu0 (by rw [← h, zero_smul, map_zero])
    rw [← hψK, map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc0 hξ

end MMP.FourfoldProofs.Km3bConeFiniteProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct Pointwise MMP.Positivity
  MMP.FourfoldProofs.Km3bConeFiniteProof

namespace MMP.Mori

/-- An ample `ℚ`-divisor is `ℚ`-Cartier. -/
theorem QDivisor.IsAmple.isQCartier {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    [IsNormal X] {H : QDivisor X} (hH : H.IsAmple) : H.IsQCartier := by
  obtain ⟨m, hm, D, hDH, hDc, -⟩ := hH
  exact ⟨m, by exact_mod_cast hm.ne', D, by rw [hDH, natCast_zsmul, Nat.cast_smul_eq_nsmul], hDc⟩

/-- **Cone theorem, finite form** (Kollár–Mori 3.7(2)). Let `X` be a projective variety over an
algebraically closed field `k` of characteristic zero, and `(X, Δ)` a klt pair of dimension `n`
with canonical divisor `K` and `Δ` effective. Let `H` be an ample `ℚ`-divisor and `ε > 0`. Then
there is a finite set `S` of curves on `X`, each a rational curve `C` with
`0 < -((K + Δ) · C) ≤ 2n` spanning an extremal ray `ℝ_{≥0}[C]` of `NE̅(X)`, such that
`NE̅(X) = NE̅(X)_{(K + Δ + εH) ≥ 0} + ∑_{C ∈ S} ℝ_{≥0}[C]`. -/
@[mmp "thm_km3b_cone_finite"]
public theorem exists_finset_isRationalCurve_closedConeOfCurves_eq {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {ε : ℝ} (hε : 0 < ε) {H : QDivisor X}
    (hH : H.IsAmple) :
    ∃ S : Finset (ProperCurve sX),
      (∀ C ∈ S,
        IsRationalCurve sX
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
          0 < -MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
            (OneCycle.numericalClass sX (C.cycle ℝ)) ∧
          -MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
            (OneCycle.numericalClass sX (C.cycle ℝ)) ≤ 2 * n ∧
          IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
            {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w}) ∧
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) =
        ((closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩
            {z | 0 ≤ MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 z +
              ε * MMP.Fourfold.QDivisor.curveForm sX H hH.isQCartier z}) +
          (PointedCone.hull ℝ
              ((fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' ↑S) :
            Set (NumericalCurveClasses sX)) := by
  classical
  set κ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2
  set γ := MMP.Fourfold.QDivisor.curveForm sX H hH.isQCartier
  have hγ : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < γ z := curveForm_pos_of_isAmple hH _
  set cl : ProperCurve sX → NumericalCurveClasses sX :=
    fun C => OneCycle.numericalClass sX (C.cycle ℝ)
  have hsup : ∀ S : Set (ProperCurve sX),
      ((closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩ {z | 0 ≤ κ z + ε * γ z}) +
        (PointedCone.hull ℝ (cl '' S) : Set (NumericalCurveClasses sX)) ⊆
        closedConeOfCurves sX := by
    rintro S _ ⟨c, hc, h, hh, rfl⟩
    exact (closedConeOfCurves sX).add_mem hc.1 (hull_le_closedConeOfCurves S hh)
  by_cases hnef : QDivisor.IsNef k sX (Divisor.toQDivisor K + Δ)
  · refine ⟨∅, by simp, Set.Subset.antisymm (subset_inter_add_of_nonneg _ hε.le
      (curveForm_nonneg_of_isNef hnef hklt.1.2.2) fun x hx => ?_) (by simpa using hsup ∅)⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (hγ x hx hx0).le
  obtain ⟨_, _, D, ψ, hDc, hψK⟩ := exists_coneDatum_linearEquiv hklt hΔ hnef
  replace hψK : ∀ w, realOfRatForm _ D.form w = κ (ψ w) := hψK
  have hneg := isNegativeExtremalRayOf_image_of_mem_negativeRationalRays hklt.1.2.2 D ψ hDc hψK
  have hG : ∀ z ∈ D.cone, z ≠ 0 → 0 < (γ ∘ₗ ψ.toLinearMap) z := fun z hz hz0 =>
    hγ _ ((hDc z).1 hz) (by simpa using hz0)
  obtain ⟨F, hF, hcone⟩ := MMP.Positivity.ConeDatum.cone_eq_nonneg_add_sum_rays D hG hε
  have hFR : ∀ R ∈ F, R ∈ D.negativeRationalRays := fun R hR => ((Set.ext_iff.1 hF R).1 hR).1
  have hT : ∀ R : F, ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        ψ '' R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • cl T = w} ∧ 0 < -κ (cl T) ∧ -κ (cl T) ≤ 2 * n :=
    fun R => MMP.Fourfold.exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed
      sX hklt (DivisorWithCoeffs.isEffective_iff_nonneg.1 hΔ) (hneg R (hFR R R.2))
  choose T hTrat hTray hTpos hTle using hT
  refine ⟨F.attach.image T, ?_, Set.Subset.antisymm (fun x hx => ?_) (by simpa using hsup _)⟩
  · intro C hC
    obtain ⟨R, -, rfl⟩ := Finset.mem_image.1 hC
    refine ⟨hTrat R, hTpos R, hTle R, ?_⟩
    rw [← hTray R]
    exact (hneg R (hFR R R.2)).2.1
  obtain ⟨c, hc, hc0, r, hr, hxr⟩ :=
    (Set.ext_iff.1 hcone _).1 ((hDc (ψ.symm x)).2 (by simpa using hx))
  refine ⟨ψ c, ⟨(hDc c).1 hc, by simpa [← hψK] using hc0⟩, ψ (∑ R ∈ F, r R), ?_, ?_⟩
  · rw [map_sum]
    refine Submodule.sum_mem _ fun R hRF => ?_
    have hmem : ψ (r R) ∈ ψ '' R := ⟨_, hr R hRF, rfl⟩
    rw [hTray ⟨R, hRF⟩] at hmem
    obtain ⟨t, ht, hteq⟩ := hmem
    rw [← hteq]
    exact (PointedCone.hull ℝ _).smul_mem ht
      (PointedCone.subset_hull ⟨T ⟨R, hRF⟩, by simp, rfl⟩)
  · change ψ c + ψ (∑ R ∈ F, r R) = x
    rw [← map_add, ← hxr]
    simp

end MMP.Mori

end
