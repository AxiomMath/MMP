module
public import MMP.AlgebraicGeometry.Singularities.RealKltRationalDecomposition
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltRayLength

/-!
# A rational curve on a klt-negative ray bounding finitely many adjoints

Let `X` be a normal `ℚ`-factorial projective complex threefold with canonical divisor `K_X`, and
let `B⁽¹⁾, …, B⁽ˡ⁾` be finitely many effective real boundaries with every `(X, B⁽ʲ⁾)` klt. If `R`
is an extremal ray of the closed cone of curves `NE̅(X)` on which at least one adjoint
`K_X + B⁽ʲ⁾` is negative, then `R` contains the class of a rational curve `C` with
`(K_X + B⁽ʲ⁾) · C ≥ -6` for every `j` simultaneously.

The proof decomposes each real boundary as a convex combination of rational klt boundaries, takes
a rational curve in `R` of least degree with respect to a fixed ample divisor, and compares it,
for each negative rational adjoint, with the curve of length at most `6 = 2 dim X` that the cone
theorem provides in `R`.

## Main results

* `MMP.Fourfold.exists_isRationalCurve_numericalClass_mem_and_neg_six_le`.

## Implementation notes

The boundaries are indexed by an arbitrary finite type. An `ℝ`-Cartier divisor `K_X + B` is a
real combination `∑ rᵢ Lᵢ` of Cartier Weil divisors `Lᵢ` (`MMP.Fourfold.RDivisor.IsRCartier`),
and its pairing with a class `z ∈ N₁(X)_ℝ` is `∑ rᵢ (z · 𝒪_X(Lᵢ))`, computed with
`MMP.Mori.NumericalCurveClasses.degree`; this is the real form of
`MMP.Fourfold.QDivisor.curveForm`. The pairing does not depend on the presentation, so the
negativity hypothesis asks for one presentation and the bound is asserted for all of them. The
canonical divisor `K` is fixed; the dimension of `X` is the `3` of
`MMP.Mori.Divisor.IsCanonicalDivisor`. A curve is an `MMP.Mori.ProperCurve`, rational when its
reduced closed subscheme is (`MMP.Mori.IsRationalCurve`), with class
`MMP.Mori.OneCycle.numericalClass` of its cycle.

The source minimizes the degree of a fixed ample Cartier divisor `H` among the rational curves of
`R`. Any integral Cartier divisor of constant nonzero sign on `R \ {0}` serves equally well, and
the Cartier multiple `E = m (K + B₀)` of a negative rational adjoint is one at hand, so `H` is not
needed. The value `∑ rᵢ (u · Lᵢ)` of a real Cartier presentation `∑ rᵢ Lᵢ` at `u ∈ N₁(X)` depends
only on the divisor `∑ rᵢ Lᵢ`: on curve classes this is the uniqueness of presentations in
`Ca(X) ⊗ ℝ` (`MMP.Flips.sum_tmul_eq_of_sum_smul_eq`), and curve classes span `N₁(X)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori
open scoped TensorProduct

section Presentation

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- `L ↦ deg_C 𝒪_X(L)` as an additive map on Cartier divisors. -/
private noncomputable def degreeHom (C : ProperCurve sX) :
    Divisor.cartierSubgroup (X := X) →+ ℤ where
  toFun L := (L : Divisor X).degreeOn ℂ sX C.ι C.dim_le L.2
  map_zero' := Divisor.degreeOn_zero' ℂ sX C.ι C.dim_le
  map_add' L₁ L₂ := Divisor.degreeOn_add ℂ sX C.ι C.dim_le L₁.1 L₂.1 L₁.2 L₂.2

/-- The extension `Ca(X) ⊗ ℝ → ℝ`, `L ⊗ r ↦ r · deg_C 𝒪_X(L)`. -/
private noncomputable def degreeTensor (C : ProperCurve sX) :
    Divisor.cartierSubgroup (X := X) ⊗[ℤ] ℝ →+ ℝ :=
  TensorProduct.liftAddHom (AddMonoidHom.mul.comp ((Int.castAddHom ℝ).comp (degreeHom C)))
    fun n L r => by simp [mul_assoc, mul_left_comm]

/-- The value `∑ rᵢ (C · Lᵢ)` of a real Cartier presentation `∑ rᵢ Lᵢ` on a proper curve depends
only on the divisor `∑ rᵢ Lᵢ`. -/
private theorem sum_mul_degreeOn_eq {m p : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    (hL : ∀ i, (L i).IsCartier) {s : Fin p → ℝ} {M : Fin p → Divisor X}
    (hM : ∀ i, (M i).IsCartier)
    (h : ∑ i, r i • Divisor.toRDivisor (L i) = ∑ i, s i • Divisor.toRDivisor (M i))
    (C : ProperCurve sX) :
    ∑ i, r i * ((L i).degreeOn ℂ sX C.ι C.dim_le (hL i) : ℝ) =
      ∑ i, s i * ((M i).degreeOn ℂ sX C.ι C.dim_le (hM i) : ℝ) := by
  have key := congrArg (degreeTensor C) (MMP.Flips.sum_tmul_eq_of_sum_smul_eq
    (fun i => ⟨L i, hL i⟩) r (fun i => ⟨M i, hM i⟩) s h)
  simp only [map_sum, degreeTensor, TensorProduct.liftAddHom_tmul, AddMonoidHom.comp_apply,
    AddMonoidHom.mul_apply, Int.coe_castAddHom] at key
  simpa [degreeHom, mul_comm] using key

variable [CompactSpace X]

/-- The linear form `u ↦ ∑ rᵢ (u · Lᵢ)` on `N₁(X)` of a real Cartier presentation `∑ rᵢ Lᵢ`. -/
private noncomputable def presentationForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ i, (L i).IsCartier) : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  ∑ i, r i • (haveI := (hL i).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sX (L i).divisorialSheaf)

private theorem presentationForm_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ i, (L i).IsCartier) (u : NumericalCurveClasses sX) :
    presentationForm r L hL u = ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX (L i).divisorialSheaf u) := by
  simp [presentationForm]

private theorem presentationForm_numericalClass_cycle {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ i, (L i).IsCartier) (C : ProperCurve sX) :
    presentationForm r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ∑ i, r i * ((L i).degreeOn ℂ sX C.ι C.dim_le (hL i) : ℝ) := by
  rw [presentationForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := (hL i).isInvertibleModule_divisorialSheaf
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  rfl

/-- The form of a real Cartier presentation depends only on the divisor it presents. -/
private theorem presentationForm_eq {m p : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    (hL : ∀ i, (L i).IsCartier) {s : Fin p → ℝ} {M : Fin p → Divisor X}
    (hM : ∀ i, (M i).IsCartier)
    (h : ∑ i, r i • Divisor.toRDivisor (L i) = ∑ i, s i • Divisor.toRDivisor (M i)) :
    presentationForm (sX := sX) r L hL = presentationForm s M hM :=
  MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => by
    rw [presentationForm_numericalClass_cycle, presentationForm_numericalClass_cycle]
    exact sum_mul_degreeOn_eq hL hM h C

/-- If `E = m D` for a Cartier divisor `E`, the curve form of the `ℚ`-Cartier `D` is
`u ↦ (u · E) / m`. -/
private theorem curveForm_eq_presentationForm {D : QDivisor X} (hD : D.IsQCartier) {m : ℕ}
    (hm : 0 < m) {E : Divisor X} (hE : E.IsCartier)
    (h : Divisor.toQDivisor E = (m : ℚ) • D) :
    QDivisor.curveForm sX D hD = presentationForm (fun _ : Fin 1 => (1 / m : ℝ)) (fun _ => E)
      (fun _ => hE) :=
  MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle, presentationForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul ℂ sX C.ι C.dim_le
        (Divisor.degreeOn_add ℂ sX C.ι C.dim_le) D hD hm E hE
        (by rw [h, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast)]
    simp [div_eq_inv_mul]

end Presentation

/-- If `E = m (K + B)` with `m > 0`, then `K + B = (1 / m) E` as real divisors. -/
private theorem toRDivisor_add_eq_smul {X : Scheme.{0}} {K : Divisor X} {B : QDivisor X} {m : ℕ}
    (hm : 0 < m) {E : Divisor X} (h : Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B)) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B = (1 / m : ℝ) • Divisor.toRDivisor E := by
  ext P
  have hP : (E.coeff P : ℚ) = m * (K.coeff P + B.coeff P) := by
    rw [mul_add]; simpa using congrArg (·.coeff P) h
  have hR : (E.coeff P : ℝ) = m * (K.coeff P + (B.coeff P : ℝ)) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hP
    push_cast at this
    exact this
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change (K.coeff P : ℝ) + (B.coeff P : ℝ) = 1 / m * (E.coeff P : ℝ)
  rw [hR]
  field_simp

/-- On a ray `R = ℝ_{≥0} v`, a linear form negative at `v` is negative on `R \ {0}`. -/
private theorem neg_of_mem_ray {V : Type*} [AddCommGroup V] [Module ℝ V] {R : Set V} {v : V}
    (hRv : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}) (φ : V →ₗ[ℝ] ℝ) (hφ : φ v < 0) :
    ∀ u ∈ R, u ≠ 0 → φ u < 0 := by
  intro u hu hu0
  rw [hRv] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  have hc0 : 0 < c := lt_of_le_of_ne hc fun h => hu0 (by rw [← h, zero_smul])
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hc0 hφ

/-- On a ray `R = ℝ_{≥0} v`, a linear form negative somewhere on `R` is negative at `v`. -/
private theorem neg_of_neg_of_mem_ray {V : Type*} [AddCommGroup V] [Module ℝ V] {R : Set V}
    {v : V} (hRv : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}) (φ : V →ₗ[ℝ] ℝ) {u : V} (hu : u ∈ R)
    (hφ : φ u < 0) : φ v < 0 := by
  rw [hRv] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  rw [map_smul, smul_eq_mul] at hφ
  by_contra h
  exact (mul_nonneg hc (not_lt.mp h)).not_gt hφ

/-- If `ψ t < 0`, `ψ t ≤ ψ (c • t)` and `φ t ≤ 0`, then `φ t ≤ φ (c • t)`. -/
private theorem apply_le_apply_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ψ φ : V →ₗ[ℝ] ℝ} {t : V} {c : ℝ} (hψt : ψ t < 0) (hψ : ψ t ≤ ψ (c • t)) (hφ : φ t ≤ 0) :
    φ t ≤ φ (c • t) := by
  simp only [map_smul, smul_eq_mul] at hψ ⊢
  nlinarith

/-- **A common rational curve on a klt-negative ray.** Let `X` be a normal `ℚ`-factorial
projective complex threefold with canonical divisor `K`, and let `B j` (`j` in a finite type) be
effective real boundaries with every `(X, B j)` klt. Let `R` be an extremal ray of `NE̅(X)` on
which `K + B j₀` is negative for some `j₀`. Then there is a rational curve `C` with
`0 ≠ [C] ∈ R` and `(K + B j) · C ≥ -6` for every `j`, the intersection number being computed
from any presentation `K + B j = ∑ rᵢ Lᵢ` by Cartier divisors `Lᵢ`. -/
@[mmp "lem_fourfold_common_ray_curve_bound"]
public theorem exists_isRationalCurve_numericalClass_mem_and_neg_six_le
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3)
    {ι : Type*} [Finite ι] {B : ι → RDivisor X} (hB0 : ∀ j P, 0 ≤ (B j).coeff P)
    (hB : ∀ j, IsRealKltPair sX (B j))
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∃ (j₀ : ι) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X)
      (hL : ∀ i, (L i).IsCartier),
      Divisor.toRDivisor K + B j₀ = ∑ i, r i • Divisor.toRDivisor (L i) ∧
      ∀ u ∈ R, u ≠ 0 →
        ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sX (L i).divisorialSheaf u) < 0) :
    ∃ C : ProperCurve sX,
      IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ R ∧ OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0 ∧
      ∀ (j : ι) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ i, (L i).IsCartier),
        Divisor.toRDivisor K + B j = ∑ i, r i • Divisor.toRDivisor (L i) →
        -6 ≤ ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sX (L i).divisorialSheaf
            (OneCycle.numericalClass sX (C.cycle ℝ))) := by
  classical
  obtain ⟨v, hv0, hRv⟩ := hR.2
  -- decompose every real boundary into rational klt boundaries
  have hdec := fun j => exists_convexCombination_isKltPair_of_isRealKltPair sX
    (inferInstance : MMP.Mori.IsProjectiveVariety ℂ sX) hXq K hK (B j) (fun P => hB0 j P) (hB j)
  choose s Bs rr m E hE hklt _hhull hrr hrr1 hm hsum hEq _hnull using hdec
  -- the curve forms `φ j i = K + Bs j i = (1 / m j) E j i`
  set φ : ∀ j, Fin (s j) → NumericalCurveClasses sX →ₗ[ℝ] ℝ := fun j i =>
    presentationForm (fun _ : Fin 1 => (1 / m j : ℝ)) (fun _ => E j i) (fun _ => hE j i)
    with hφ
  have hcf : ∀ j i (h : (Divisor.toQDivisor K + Bs j i).IsQCartier),
      QDivisor.curveForm sX _ h = φ j i := fun j i h =>
    curveForm_eq_presentationForm h (hm j) (hE j i) (hEq j i)
  -- every presentation of `K + B j` computes `∑ rr j i · φ j i`
  have hpres : ∀ j {m' : ℕ} (r : Fin m' → ℝ) (L : Fin m' → Divisor X)
      (hL : ∀ i, (L i).IsCartier),
      Divisor.toRDivisor K + B j = ∑ i, r i • Divisor.toRDivisor (L i) →
      ∀ u, ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
        NumericalCurveClasses.degree sX (L i).divisorialSheaf u) = ∑ i, rr j i * φ j i u := by
    intro j m' r L hL hrL u
    rw [← presentationForm_apply r L hL, presentationForm_eq hL (hE j)
      (s := fun i => rr j i * (1 / m j)) (by
        rw [← hrL, hsum j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [toRDivisor_add_eq_smul (hm j) (hEq j i), smul_smul]), presentationForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφ, presentationForm_apply, Fin.sum_univ_one, mul_assoc]
  -- the length bound for a rational boundary negative on `R`
  have hlen : ∀ j i, φ j i v < 0 → ∃ T : ProperCurve sX,
      IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w} ∧
      -6 ≤ φ j i (OneCycle.numericalClass sX (T.cycle ℝ)) ∧
      φ j i (OneCycle.numericalClass sX (T.cycle ℝ)) < 0 := by
    intro j i hv
    have hk : MMP.Mori.IsKltPair sX 3 K (Bs j i) :=
      (isKltPair_iff_mori_isKltPair sX hK (hklt j i).1).mp (hklt j i)
    obtain ⟨T, hT, hRT, hpos, hle⟩ :=
      exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf sX hk
        (fun P => (hklt j i).1.nonneg P)
        ⟨hk.1.2.2, hR, fun u hu hu0 => by rw [hcf]; exact neg_of_mem_ray hRv _ hv u hu hu0⟩
    rw [hcf] at hpos hle
    refine ⟨T, hT, hRT, ?_, by linarith⟩
    push_cast at hle
    linarith
  -- some rational boundary of the decomposition of `B j₀` is negative on `R`
  obtain ⟨j₀, m₀, r₀, L₀, hL₀, hKL₀, hneg₀⟩ := hneg
  have hv : ∑ i, rr j₀ i * φ j₀ i v < 0 := by
    rw [← hpres j₀ r₀ L₀ hL₀ hKL₀ v]
    exact hneg₀ v (by rw [hRv]; exact ⟨1, zero_le_one, one_smul ℝ v⟩) hv0
  obtain ⟨i₀, hi₀⟩ : ∃ i, φ j₀ i v < 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact (Finset.sum_nonneg fun i _ => mul_nonneg (hrr j₀ i).le (h i)).not_gt hv
  -- the integral degree `d C = (C · E j₀ i₀)`, negative on the curves of `R`
  set d : ProperCurve sX → ℤ := fun C => (E j₀ i₀).degreeOn ℂ sX C.ι C.dim_le (hE j₀ i₀)
  have hφ₀ : ∀ C : ProperCurve sX,
      φ j₀ i₀ (OneCycle.numericalClass sX (C.cycle ℝ)) = 1 / m j₀ * (d C : ℝ) := fun C => by
    rw [hφ, presentationForm_numericalClass_cycle, Fin.sum_univ_one]
  let Good : ProperCurve sX → Prop := fun C =>
    IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ R ∧ OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0
  have hdneg : ∀ C, Good C → d C < 0 := fun C hC => by
    have h := neg_of_mem_ray hRv _ hi₀ _ hC.2.1 hC.2.2
    rw [hφ₀] at h
    exact_mod_cast neg_of_mul_neg_right h (by positivity)
  -- the curve produced by the length bound is good
  have hgood : ∀ j i (T : ProperCurve sX),
      IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) →
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w} →
      φ j i (OneCycle.numericalClass sX (T.cycle ℝ)) < 0 → Good T := fun j i T hT hRT hTneg =>
    ⟨hT, by rw [hRT]; exact ⟨1, zero_le_one, one_smul ℝ _⟩, fun h0 => by simp [h0] at hTneg⟩
  -- a good curve of least `-d`
  obtain ⟨T₀, hT₀, hRT₀, -, hT₀neg⟩ := hlen j₀ i₀ hi₀
  obtain ⟨-, ⟨C, hCg, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun z => ∃ C, Good C ∧ d C = z)
      ⟨0, fun _ ⟨C, hC, h⟩ => h ▸ (hdneg C hC).le⟩ ⟨_, T₀, hgood j₀ i₀ T₀ hT₀ hRT₀ hT₀neg, rfl⟩
  refine ⟨C, hCg.1, hCg.2.1, hCg.2.2, fun j m' r L hL hrL => ?_⟩
  rw [hpres j r L hL hrL]
  -- every rational adjoint is at least `-6` on `C`
  have hbd : ∀ i, -6 ≤ φ j i (OneCycle.numericalClass sX (C.cycle ℝ)) := by
    intro i
    by_cases h0 : 0 ≤ φ j i (OneCycle.numericalClass sX (C.cycle ℝ))
    · linarith
    obtain ⟨T, hT, hRT, hT6, hTneg⟩ :=
      hlen j i (neg_of_neg_of_mem_ray hRv _ hCg.2.1 (not_le.mp h0))
    have hTg := hgood j i T hT hRT hTneg
    obtain ⟨c, -, hcT⟩ := hRT ▸ hCg.2.1
    rw [← hcT]
    refine hT6.trans (apply_le_apply_smul (neg_of_mem_ray hRv _ hi₀ _ hTg.2.1 hTg.2.2) ?_
      hTneg.le)
    rw [hcT, hφ₀, hφ₀]
    gcongr
    exact_mod_cast hmax _ ⟨T, hTg, rfl⟩
  calc (-6 : ℝ) = ∑ i, rr j i * (-6) := by rw [← Finset.sum_mul, hrr1 j]; ring
    _ ≤ ∑ i, rr j i * φ j i (OneCycle.numericalClass sX (C.cycle ℝ)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbd i) (hrr j i).le

end MMP.Fourfold

end
