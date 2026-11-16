module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportSandwichFiniteRays
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor

section

/-!
# The attained boundary-removal threshold

Let `h : Y ⟶ Z` be a projective birational morphism of normal projective varieties, `Y`
`ℚ`-factorial, and `D, G ≥ 0` with `(Y, D + G)` dlt, `K_Y + D + G` nef over `Z` and `K_Y + D` not.
Write `φ = (K_Y + D) · -` and `γ = G · -` on `N₁(Y/Z)`, so that `K_Y + D + (1 - c) G` is nef over
`Z` exactly when `φ + (1 - c) γ ≥ 0` on every contracted curve. The nef parameters `c ∈ [0, 1]`
have supremum `e`, attained, with `e < 1`.

Fix a rational `c₀ ∈ (e, 1)`. The finiteness of the `(K_Y + B_{c₀})`-negative extremal rays,
`B_{c₀} = D + (1 - c₀) G`, gives a finite set `𝓡` of rays, each spanned by a rational curve. If
no ray `R ∈ 𝓡` with `γ > 0` on `R` had `(φ + (1 - e) γ) · R = 0`, then for every rational `c > e`
close enough to `e` all these rays would be `(φ + (1 - c) γ)`-positive. But `K_Y + B_c` is not
nef, so some extremal ray `R'` is `(φ + (1 - c) γ)`-negative; nefness at `e` forces `γ > 0` on
`R'`, so `R'` is `(φ + (1 - c₀) γ)`-negative and lies in `𝓡`, a contradiction. The ray found is
spanned by a curve, on which `φ` and `γ` take rational values; hence
`e = 1 + (φ · R) / (γ · R)` is rational.

## Main results

* `MMP.FourfoldProofs.FourfoldProjectiveBoundaryRemovalThresholdRayProof.exists_rat_eq_sSup_and_ray`.

## Implementation notes

The source passes to the limit along a sequence `c_k ↓ e` and uses that one ray of `𝓡` recurs.
Here the finiteness of `𝓡` is used directly: a finite intersection of open conditions on `c` is a
neighbourhood of `e`, which replaces the sequence.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold Filter Topology

namespace MMP.FourfoldProofs.FourfoldProjectiveBoundaryRemovalThresholdRayProof

section CurveForm

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- The curve form depends only on the divisor, not on the `ℚ`-Cartier witness. -/
private theorem curveForm_congr {D D' : QDivisor X} (hDD' : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) : QDivisor.curveForm sX D hD = QDivisor.curveForm sX D' hD' := by
  subst hDD'; rfl

/-- The curve form is `ℚ`-affine in the divisor: `(M₁ + q M₂) · - = M₁ · - + q (M₂ · -)`. -/
private theorem curveForm_add_smul (M₁ M₂ : QDivisor X) (q : ℚ) (h₁ : M₁.IsQCartier)
    (h₂ : M₂.IsQCartier) (hq : (q • M₂).IsQCartier) (h : (M₁ + q • M₂).IsQCartier) :
    QDivisor.curveForm sX (M₁ + q • M₂) h =
      QDivisor.curveForm sX M₁ h₁ + (q : ℝ) • QDivisor.curveForm sX M₂ h₂ := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le M₁ (q • M₂) h₁ hq h,
    QDivisor.intersectionNumber_smul k sX C.ι C.dim_le q M₂ h₂ hq]
  push_cast; rfl

end CurveForm

/-! ### Intersection numbers with proper curves are degrees -/

section Normalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  obtain ⟨d, hd⟩ := MMP.Flips.exists_isCartierIntersectionNumber C L hL
  rwa [← hd.eq_degreeOn]

end Normalization

/-! ### Relative nefness through curve forms -/

section Nef

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- For a `ℚ`-Cartier `ℚ`-divisor `M` with Cartier index `n`, the curve form on a proper curve is
`deg_C 𝒪_X(nM) / n`. -/
private theorem curveForm_eq_degreeOn_div (M : QDivisor X) (h : M.IsQCartier) (C : ProperCurve sX) :
    QDivisor.curveForm sX M h (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ((M.cartierIndexSMul h : Divisor X).degreeOn k sX C.ι C.dim_le (M.cartierIndexSMul h).2 : ℝ) /
        M.cartierIndex h := by
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le M h _
      (M.cartierIndexSMul h).2 (QDivisor.toQDivisor_cartierIndexSMul M h)]
  push_cast; rfl

/-- `M = (1 / n) (n M)` as `ℝ`-divisors, for the Cartier index `n` of `M`. -/
private theorem toRDivisor_eq_inv_smul (M : QDivisor X) (h : M.IsQCartier) :
    QDivisor.toRDivisor M =
      ((M.cartierIndex h : ℝ)⁻¹) • Divisor.toRDivisor (M.cartierIndexSMul h : Divisor X) := by
  have hn : (M.cartierIndex h : ℝ) ≠ 0 := by exact_mod_cast (QDivisor.cartierIndex_pos h).ne'
  ext P
  have := congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul M h)
  simp only [Divisor.coeff_toQDivisor] at this
  have hP : (((M.cartierIndexSMul h : Divisor X).coeff P : ℚ) : ℝ) =
      (M.cartierIndex h : ℝ) * (M.coeff P : ℝ) := by
    rw [this]; simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul]
  simp only [DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [← Rat.cast_intCast, hP]
  field_simp

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    MMP.Flips.IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn C (L j) (hL j), rfl⟩

/-- **Nefness on curves.** For `ℚ`-Cartier `ℚ`-divisors `M₁, M₂` and `s ∈ ℝ`, the `ℝ`-divisor
`M₁ + s M₂` is nef over `Y` if and only if `(M₁ · C) + s (M₂ · C) ≥ 0` for every curve `C`
contracted to a point of `Y`. -/
private theorem isRelativelyNef_add_smul_iff (f : X ⟶ Y) (M₁ M₂ : QDivisor X)
    (h₁ : M₁.IsQCartier) (h₂ : M₂.IsQCartier) (s : ℝ) :
    MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor M₁ + s • QDivisor.toRDivisor M₂) ↔
      ∀ C : ProperCurve sX, C.IsContractedBy f →
        0 ≤ QDivisor.curveForm sX M₁ h₁ (OneCycle.numericalClass sX (C.cycle ℝ)) +
          s * QDivisor.curveForm sX M₂ h₂ (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  set L₁ : Divisor X := (M₁.cartierIndexSMul h₁ : Divisor X)
  set L₂ : Divisor X := (M₂.cartierIndexSMul h₂ : Divisor X)
  have hL₁ : L₁.IsCartier := (M₁.cartierIndexSMul h₁).2
  have hL₂ : L₂.IsCartier := (M₂.cartierIndexSMul h₂).2
  set r : Fin 2 → ℝ := ![(M₁.cartierIndex h₁ : ℝ)⁻¹, s * (M₂.cartierIndex h₂ : ℝ)⁻¹]
  set L : Fin 2 → Divisor X := ![L₁, L₂]
  have hL : ∀ j, (L j).IsCartier := Fin.forall_fin_two.2 ⟨hL₁, hL₂⟩
  have heq : QDivisor.toRDivisor M₁ + s • QDivisor.toRDivisor M₂ =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    rw [Fin.sum_univ_two, toRDivisor_eq_inv_smul M₁ h₁, toRDivisor_eq_inv_smul M₂ h₂, smul_smul]
    rfl
  have hval : ∀ C : ProperCurve sX,
      ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) =
        QDivisor.curveForm sX M₁ h₁ (OneCycle.numericalClass sX (C.cycle ℝ)) +
          s * QDivisor.curveForm sX M₂ h₂ (OneCycle.numericalClass sX (C.cycle ℝ)) := by
    intro C
    rw [Fin.sum_univ_two, curveForm_eq_degreeOn_div M₁ h₁, curveForm_eq_degreeOn_div M₂ h₂]
    change (M₁.cartierIndex h₁ : ℝ)⁻¹ * (L₁.degreeOn k sX C.ι C.dim_le hL₁ : ℝ) +
      s * (M₂.cartierIndex h₂ : ℝ)⁻¹ * (L₂.degreeOn k sX C.ι C.dim_le hL₂ : ℝ) = _
    ring
  have hx : ∀ C : ProperCurve sX, MMP.Flips.IsRIntersectionNumber k sX
      (QDivisor.toRDivisor M₁ + s • QDivisor.toRDivisor M₂) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := fun C => by
    rw [heq]; exact isRIntersectionNumber_sum_degreeOn C r L hL
  constructor
  · rintro ⟨m, r', L', hL', hD', hnn⟩ C hC
    have hx' := isRIntersectionNumber_sum_degreeOn C r' L' hL'
    rw [← hD'] at hx'
    rw [← hval C, (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L r' L' _ _
      (hx C) hx']
    exact hnn C hC _ hx'
  · intro H
    refine ⟨2, r, L, hL, heq, fun C hC x hx' => ?_⟩
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L r L _ _ hx' (hx C), hval C]
    exact H C hC

end Nef

/-! ### Linear forms on the relative cone -/

section Relative

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}

/-- The degree form of an invertible sheaf on `N₁(X)`, pulled back to `N₁(X/Z)`, is its degree
form on `N₁(X/Z)`. -/
private theorem degree_relativeToAbsolute (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.degree sX f L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

/-- The curve form of a `ℚ`-Cartier divisor is continuous on `N₁(X/Z)`. -/
private theorem continuous_curveForm_relativeToAbsolute [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (D : QDivisor X) (h : D.IsQCartier) :
    Continuous fun z : RelativeNumericalCurveClasses sX f =>
      QDivisor.curveForm sX D h (relativeToAbsolute sX f z) := by
  simp only [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  apply continuous_finset_sum
  intro E _
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  simp only [degree_relativeToAbsolute]
  exact continuous_const.mul (RelativeNumericalCurveClasses.continuous_degree sX f _)

/-- A continuous linear form on `N₁(X/Z)` which is nonnegative on the classes of the contracted
curves is nonnegative on the closed relative cone `NE̅(X/Z)`. -/
private theorem nonneg_of_mem_relativeClosedConeOfCurves
    (ψ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ) (hψ : Continuous ψ)
    (h : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), 0 ≤ ψ (C.relativeClass f hC))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ ψ z := by
  have hcl : z ∈ closure (relativeConeOfCurves sX f : Set _) := by
    rwa [← coe_relativeClosedConeOfCurves]
  refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const hψ) hcl
  change z ∈ PointedCone.hull ℝ _ at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact h C hC
  | zero => simp
  | add x y _ _ hx hy =>
    change 0 ≤ ψ (x + y)
    rw [map_add]; exact add_nonneg hx hy
  | smul a x _ hx =>
    change 0 ≤ ψ (a • x)
    rw [LinearMap.map_smul_of_tower]
    change 0 ≤ (a : ℝ) * ψ x
    exact mul_nonneg a.2 hx

/-- **A negative ray.** For morphisms of projective varieties, if a linear form on `N₁(X/Z)` is
negative on the class of some contracted curve, it is negative on every nonzero element of some
extremal ray of `NE̅(X/Z)`. -/
private theorem exists_isExtremalRay_neg [IsAlgClosed k] [CharZero k] (sZ : Z ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k sX] [MMP.Mori.IsProjectiveVariety k sZ] (hfs : f ≫ sZ = sX)
    (ψ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) (hneg : ψ (C.relativeClass f hC) < 0) :
    ∃ R : Set (RelativeNumericalCurveClasses sX f),
      IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R ∧
        ∀ u ∈ R, u ≠ 0 → ψ u < 0 := by
  have hz : C.relativeClass f hC ∈ relativeClosedConeOfCurves sX f := by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hC)
  obtain ⟨s, R, w, hRw, hsum⟩ :=
    exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sZ f hfs hz
  rw [hsum, map_sum] at hneg
  have hneg' : ∑ i, ψ (w i) < ∑ _i : Fin s, (0 : ℝ) := by simpa using hneg
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hneg'
  refine ⟨R i, (hRw i).1, ?_⟩
  obtain ⟨-, v, -, hRv⟩ := (hRw i).1
  obtain ⟨c, hc, hcv⟩ : w i ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := hRv ▸ (hRw i).2
  have hψv : ψ v < 0 := by
    by_contra! hv
    rw [← hcv, map_smul, smul_eq_mul] at hi
    exact absurd hi (not_lt.mpr (mul_nonneg hc hv))
  intro u hu hu0
  rw [hRv] at hu
  obtain ⟨c', hc', rfl⟩ := hu
  have hc'0 : c' ≠ 0 := by rintro rfl; simp at hu0
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (hc'.lt_of_ne' hc'0) hψv

end Relative

/-! ### The threshold and its ray -/

section Threshold

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
  {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sZ]
  [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The threshold of an affine family.** If `x + (1 - c) y ≥ 0` holds for `c = 0` but not for
`c = 1`, the supremum `e` of the parameters `c ∈ [0, 1]` where it holds is attained, `e < 1`,
and it fails for every `c ∈ (e, 1]`. -/
private theorem sSup_threshold {ι : Type*} (x y : ι → ℝ) {S : Set ℝ}
    (hSP : ∀ c, c ∈ S ↔ c ∈ Set.Icc 0 1 ∧ ∀ i, 0 ≤ x i + (1 - c) * y i)
    (h0 : ∀ i, 0 ≤ x i + y i) (h1 : ¬ ∀ i, 0 ≤ x i) :
    0 ≤ sSup S ∧ (∀ i, 0 ≤ x i + (1 - sSup S) * y i) ∧
      (∀ c, sSup S < c → c ≤ 1 → ∃ i, x i + (1 - c) * y i < 0) ∧ sSup S < 1 := by
  have h0S : (0 : ℝ) ∈ S := (hSP 0).2 ⟨⟨le_rfl, zero_le_one⟩, fun i => by simpa using h0 i⟩
  have hSbdd : BddAbove S := ⟨1, fun c hc => ((hSP c).1 hc).1.2⟩
  have he0 : 0 ≤ sSup S := le_csSup hSbdd h0S
  have he1 : sSup S ≤ 1 := csSup_le ⟨0, h0S⟩ fun c hc => ((hSP c).1 hc).1.2
  have hPe : ∀ i, 0 ≤ x i + (1 - sSup S) * y i := by
    intro i
    have hx0 := h0 i
    by_cases hy : y i ≤ 0
    · nlinarith
    · push Not at hy
      have hle : sSup S ≤ (x i + y i) / y i := csSup_le ⟨0, h0S⟩ fun c hc => by
        have := ((hSP c).1 hc).2 i
        rw [le_div_iff₀ hy]
        nlinarith
      rw [le_div_iff₀ hy] at hle
      nlinarith
  refine ⟨he0, hPe, fun c hec hc1 => ?_,
    he1.lt_of_ne fun h1e => h1 fun i => by simpa [h1e] using hPe i⟩
  by_contra! hP
  exact absurd (le_csSup hSbdd ((hSP c).2 ⟨⟨by linarith, hc1⟩, hP⟩)) (not_le.2 hec)

/-- **A recurring ray.** Let `φ, γ` be linear forms on `N₁(Y/Z)` with `φ + (1 - e) γ ≥ 0` on
`NE̅(Y/Z)`, such that for every `c ∈ (e, 1]` some contracted curve is `(φ + (1 - c) γ)`-negative.
If, for some `c₀ ∈ (e, 1)`, the finite set `𝓡` contains every `(φ + (1 - c₀) γ)`-negative
extremal ray, then some `R ∈ 𝓡` is `γ`-positive and `(φ + (1 - e) γ)`-trivial. -/
private theorem exists_mem_ray_trivial {h : Y ⟶ Z} (hh : h ≫ sZ = sY)
    (φ γ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ) {e c₀ : ℝ} (hec₀ : e < c₀)
    (hc₀1 : c₀ < 1) (hψe : ∀ z ∈ relativeClosedConeOfCurves sY h, 0 ≤ φ z + (1 - e) * γ z)
    (hnotP : ∀ c, e < c → c ≤ 1 → ∃ i : Σ' C : ProperCurve sY, C.IsContractedBy h,
      φ (i.1.relativeClass h i.2) + (1 - c) * γ (i.1.relativeClass h i.2) < 0)
    {𝓡 : Set (Set (RelativeNumericalCurveClasses sY h))} (hfin : 𝓡.Finite)
    (hmem : ∀ R, IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R →
      (∀ u ∈ R, u ≠ 0 → φ u + (1 - c₀) * γ u < 0) → R ∈ 𝓡) :
    ∃ R ∈ 𝓡, ∀ u ∈ R, u ≠ 0 → 0 < γ u ∧ φ u + (1 - e) * γ u ≤ 0 := by
  by_contra hcon
  push Not at hcon
  choose! w hwR hw0 hwpos using hcon
  have hev : ∀ᶠ c in 𝓝 e, ∀ R ∈ 𝓡, 0 < γ (w R) → 0 < φ (w R) + (1 - c) * γ (w R) := by
    refine (eventually_all_finite hfin).2 fun R hR => ?_
    by_cases hγR : 0 < γ (w R)
    · have hpos := hwpos R hR hγR
      have ht : Tendsto (fun c : ℝ => φ (w R) + (1 - c) * γ (w R)) (𝓝 e)
          (𝓝 (φ (w R) + (1 - e) * γ (w R))) :=
        ((continuous_const.add ((continuous_const.sub continuous_id).mul
          continuous_const)).tendsto e)
      exact (ht.eventually (lt_mem_nhds hpos)).mono fun c hc _ => hc
    · exact Eventually.of_forall fun c hc => absurd hc hγR
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨c, hec, hcc⟩ := exists_between (lt_min (lt_add_of_pos_right e hε) hec₀)
  have hcε : c < e + ε := hcc.trans_le (min_le_left _ _)
  have hcc₀ : c < c₀ := hcc.trans_le (min_le_right _ _)
  obtain ⟨⟨C, hC⟩, hCneg⟩ := hnotP c hec (hcc₀.trans hc₀1).le
  obtain ⟨R', hR', hR'neg⟩ := exists_isExtremalRay_neg sZ hh (φ + (1 - c) • γ) hC
    (by simpa using hCneg)
  have hR'neg' : ∀ u ∈ R', u ≠ 0 → φ u + (1 - c) * γ u < 0 := fun u hu hu0 => by
    simpa using hR'neg u hu hu0
  have hγR' : ∀ u ∈ R', u ≠ 0 → 0 < γ u := fun u hu hu0 => by
    nlinarith [hR'neg' u hu hu0, hψe u (hR'.1.1 hu)]
  have hR'𝓡 : R' ∈ 𝓡 := hmem R' hR' fun u hu hu0 => by
    nlinarith [hR'neg' u hu hu0, hγR' u hu hu0]
  have hdist : dist c e < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have := hεP hdist R' hR'𝓡 (hγR' _ (hwR R' hR'𝓡) (hw0 R' hR'𝓡))
  exact absurd (hR'neg' _ (hwR R' hR'𝓡) (hw0 R' hR'𝓡)) (not_lt.2 this.le)

/-- **Rationality on a curve ray.** Let `R` be an extremal ray of `NE̅(Y/Z)` spanned by the class
of a contracted curve, `e < 1`, and `φ = A · -`, `γ = G · -` with `φ + (1 - e) γ ≥ 0` on
`NE̅(Y/Z)`. If `γ > 0` and `φ + (1 - e) γ ≤ 0` on `R`, then `e` is rational, `R` is `A`-negative,
and on `R` the divisor `A + (1 - e) G` is trivial and `G` is positive. -/
private theorem exists_rat_isNegativeRelativeExtremalRayOf_of_ray
    (hq : ∀ M : QDivisor Y, M.IsQCartier) {h : Y ⟶ Z} (A G : QDivisor Y)
    {R : Set (RelativeNumericalCurveClasses sY h)}
    (hRext : IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R)
    (C : ProperCurve sY) (hC : C.IsContractedBy h)
    (hRC : R = {v | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = v}) {e : ℝ} (he1 : e < 1)
    (hψe : ∀ z ∈ relativeClosedConeOfCurves sY h,
      0 ≤ (QDivisor.curveForm sY A (hq A) ∘ₗ relativeToAbsolute sY h) z +
        (1 - e) * (QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h) z)
    (hRgood : ∀ u ∈ R, u ≠ 0 → 0 < (QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h) u ∧
      (QDivisor.curveForm sY A (hq A) ∘ₗ relativeToAbsolute sY h) u +
        (1 - e) * (QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h) u ≤ 0) :
    ∃ e' : ℚ, (e' : ℝ) = e ∧ IsNegativeRelativeExtremalRayOf sY h A R ∧
      ∀ u ∈ R, u ≠ 0 → QDivisor.relativeCurveForm sY h (A + (1 - e') • G) (hq _) u = 0 ∧
        0 < QDivisor.relativeCurveForm sY h G (hq G) u := by
  set φ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY A (hq A) ∘ₗ relativeToAbsolute sY h with hφ
  set γ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h with hγ
  set ξ := C.relativeClass h hC with hξ
  have hgen' : ∀ u ∈ R, ∃ t : ℝ, 0 ≤ t ∧ t • ξ = u := fun u hu => by
    rw [hRC] at hu
    exact hu
  have hξR : ξ ∈ R := by
    rw [hRC]
    exact ⟨1, zero_le_one, one_smul _ _⟩
  have hξ0 : ξ ≠ 0 := by
    intro hξ0
    obtain ⟨-, v, hv0, hRv⟩ := hRext
    have hvR : v ∈ R := by
      rw [hRv]
      exact ⟨1, zero_le_one, one_smul _ _⟩
    obtain ⟨t, -, ht⟩ := hgen' v hvR
    rw [hξ0, smul_zero] at ht
    exact hv0 ht.symm
  have hpos : ∀ u ∈ R, u ≠ 0 → ∃ t : ℝ, 0 < t ∧ t • ξ = u := fun u hu hu0 => by
    obtain ⟨t, ht, rfl⟩ := hgen' u hu
    exact ⟨t, lt_of_le_of_ne ht fun h0 => hu0 (by rw [← h0, zero_smul]), rfl⟩
  obtain ⟨hγξ, hψξ⟩ := hRgood ξ hξR hξ0
  have hψξ0 : φ ξ + (1 - e) * γ ξ = 0 := le_antisymm hψξ (hψe ξ (hRext.1.1 hξR))
  obtain ⟨q₁, hφξ⟩ : ∃ q : ℚ, φ ξ = q :=
    ⟨_, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY A (hq A) C⟩
  obtain ⟨q₂, hγξ'⟩ : ∃ q : ℚ, γ ξ = q :=
    ⟨_, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY G (hq G) C⟩
  have hq₂pos : (0 : ℝ) < q₂ := hγξ' ▸ hγξ
  set e' : ℚ := 1 + q₁ / q₂ with he'
  have he'e : (e' : ℝ) = e := by
    rw [he']
    push_cast
    rw [hφξ, hγξ'] at hψξ0
    field_simp
    linarith
  refine ⟨e', he'e, ⟨hq A, hRext, fun u hu hu0 => ?_⟩, fun u hu hu0 => ?_⟩
  · obtain ⟨t, ht0, rfl⟩ := hpos u hu hu0
    rw [QDivisor.relativeCurveForm_eq_comp]
    change φ (t • ξ) < 0
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg ht0 (by nlinarith)
  · obtain ⟨t, ht0, rfl⟩ := hpos u hu hu0
    rw [QDivisor.relativeCurveForm_eq_comp, QDivisor.relativeCurveForm_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply,
      curveForm_add_smul sY A G (1 - e') (hq A) (hq G) (hq _) (hq _)]
    change (QDivisor.curveForm sY A (hq A) + _) (relativeToAbsolute sY h (t • ξ)) = 0 ∧
      0 < γ (t • ξ)
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    change φ (t • ξ) + _ • γ (t • ξ) = 0 ∧ 0 < γ (t • ξ)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    push_cast
    rw [he'e]
    exact ⟨by linear_combination t * hψξ0, mul_pos ht0 hγξ⟩

/-- **The attained threshold, from finiteness of the negative rays.** Suppose that for every
rational `0 < c₀ < 1` the `(K + D + (1 - c₀) G)`-negative extremal rays of `NE̅(Y/Z)` form a finite
set `𝓡`, each ray spanned by the class of a contracted curve. If `K + D + G` is nef over `Z` and
`K + D` is not, then the threshold `e` is rational, `e < 1`, and it is attained on a
`(K + D)`-negative extremal ray on which `G` is positive. -/
private theorem exists_rat_eq_sSup_and_ray (hY : IsQFactorial sY) {h : Y ⟶ Z} (hh : h ≫ sZ = sY)
    {K : Divisor Y} {D G : QDivisor Y}
    (hnef : MMP.Flips.IsRelativelyNef k sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D + G)))
    (hnotnef : ¬ MMP.Flips.IsRelativelyNef k sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D)))
    (hrays : ∀ c₀ : ℚ, 0 < c₀ → c₀ < 1 →
      ∃ hKB : (Divisor.toQDivisor K + (D + (1 - c₀) • G)).IsQCartier,
        ∃ 𝓡 : Set (Set (RelativeNumericalCurveClasses sY h)), 𝓡.Finite ∧
          (∀ R, R ∈ 𝓡 ↔
            IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R ∧
              ∀ u ∈ R, u ≠ 0 →
                QDivisor.curveForm sY (Divisor.toQDivisor K + (D + (1 - c₀) • G)) hKB
                  (relativeToAbsolute sY h u) < 0) ∧
          (∀ R ∈ 𝓡, ∃ (C : ProperCurve sY) (hC : C.IsContractedBy h),
            R = {v | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = v})) :
    ∃ e : ℚ, (e : ℝ) = sSup {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef k sY h
        (QDivisor.toRDivisor (Divisor.toQDivisor K + D) + (1 - c) • QDivisor.toRDivisor G)} ∧
      e < 1 ∧ ∃ R : Set (RelativeNumericalCurveClasses sY h),
        IsNegativeRelativeExtremalRayOf sY h (Divisor.toQDivisor K + D) R ∧
        ∃ (he : (Divisor.toQDivisor K + D + (1 - e) • G).IsQCartier) (hGq : G.IsQCartier),
          ∀ u ∈ R, u ≠ 0 →
            QDivisor.relativeCurveForm sY h (Divisor.toQDivisor K + D + (1 - e) • G) he u = 0 ∧
              0 < QDivisor.relativeCurveForm sY h G hGq u := by
  classical
  have hq : ∀ M : QDivisor Y, M.IsQCartier := isQCartier_of_isQFactorial sY hY
  set A : QDivisor Y := Divisor.toQDivisor K + D with hA
  set φ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY A (hq A) ∘ₗ relativeToAbsolute sY h with hφ
  set γ : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY G (hq G) ∘ₗ relativeToAbsolute sY h with hγ
  have hφc : Continuous φ := continuous_curveForm_relativeToAbsolute A (hq A)
  have hγc : Continuous γ := continuous_curveForm_relativeToAbsolute G (hq G)
  have hnefiff : ∀ s : ℝ, MMP.Flips.IsRelativelyNef k sY h
      (QDivisor.toRDivisor A + s • QDivisor.toRDivisor G) ↔
        ∀ i : Σ' C : ProperCurve sY, C.IsContractedBy h,
          0 ≤ φ (i.1.relativeClass h i.2) + s * γ (i.1.relativeClass h i.2) := fun s =>
    (isRelativelyNef_add_smul_iff h A G (hq A) (hq G) s).trans
      ⟨fun H i => H i.1 i.2, fun H C hC => H ⟨C, hC⟩⟩
  set S : Set ℝ := {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef k sY h
    (QDivisor.toRDivisor A + (1 - c) • QDivisor.toRDivisor G)} with hS
  obtain ⟨he0, hPe, hnotP, he_lt⟩ :=
    sSup_threshold (ι := Σ' C : ProperCurve sY, C.IsContractedBy h) (S := S)
      (fun i => φ (i.1.relativeClass h i.2)) (fun i => γ (i.1.relativeClass h i.2))
      (fun c => and_congr_right' (hnefiff _))
      (fun i => by simpa using (hnefiff 1).1 (by simpa [map_add] using hnef) i)
      fun hP1 => hnotnef (by simpa using (hnefiff 0).2 fun i => by simpa using hP1 i)
  set e : ℝ := sSup S with he
  have hψe : ∀ z ∈ relativeClosedConeOfCurves sY h, 0 ≤ φ z + (1 - e) * γ z := by
    intro z hz
    have := nonneg_of_mem_relativeClosedConeOfCurves (φ + (1 - e) • γ)
      (by rw [LinearMap.coe_add, LinearMap.coe_smul]; exact hφc.add (hγc.const_smul _))
      (fun C hC => by simpa using hPe ⟨C, hC⟩) hz
    simpa using this
  obtain ⟨c₀, hec₀, hc₀1⟩ := exists_rat_btwn he_lt
  have hc₀pos : (0 : ℚ) < c₀ := by exact_mod_cast he0.trans_lt hec₀
  obtain ⟨hKB, 𝓡, hfin, hmem, hgen⟩ := hrays c₀ hc₀pos (by exact_mod_cast hc₀1)
  have hform : ∀ u, QDivisor.curveForm sY (Divisor.toQDivisor K + (D + (1 - c₀) • G)) hKB
      (relativeToAbsolute sY h u) = φ u + (1 - (c₀ : ℝ)) * γ u := by
    intro u
    rw [curveForm_congr sY (show Divisor.toQDivisor K + (D + (1 - c₀) • G) = A + (1 - c₀) • G by
      rw [hA, add_assoc]) hKB (hq _),
      curveForm_add_smul sY A G (1 - c₀) (hq A) (hq G) (hq _) (hq _)]
    simp [φ, γ]
  obtain ⟨R, hR𝓡, hRgood⟩ := exists_mem_ray_trivial hh φ γ hec₀ hc₀1 hψe hnotP hfin
    fun R hR hneg => (hmem R).2 ⟨hR, fun u hu hu0 => by rw [hform]; exact hneg u hu hu0⟩
  obtain ⟨C, hC, hRC⟩ := hgen R hR𝓡
  obtain ⟨e', he'e, hRneg, hR⟩ := exists_rat_isNegativeRelativeExtremalRayOf_of_ray hq A G
    ((hmem R).1 hR𝓡).1 C hC hRC he_lt hψe hRgood
  exact ⟨e', he'e, by exact_mod_cast (he'e ▸ he_lt : (e' : ℝ) < 1), R, hRneg, hq _, hq G, hR⟩

end Threshold

end MMP.FourfoldProofs.FourfoldProjectiveBoundaryRemovalThresholdRayProof

end

section

/-!
# The attained boundary-removal threshold

Let `h : Y ⟶ Z` be a projective birational morphism of normal projective varieties over an
algebraically closed field of characteristic zero, with `Y` `ℚ`-factorial, and let `D, G ≥ 0`
be `ℚ`-divisors on `Y` such that `(Y, D + G)` is dlt, `K_Y + D + G` is nef over `Z` and `K_Y + D`
is not. Suppose a single effective Cartier divisor `H` on `Z` satisfies, for every rational
`0 < c < 1`, the support sandwich `Supp ⌊B_c⌋ ⊆ Supp h^* H ⊆ Supp B_c` for
`B_c = D + (1 - c) G`. Then the threshold
`e = sup {c ∈ [0, 1] | K_Y + D + (1 - c) G is nef over Z}`
is a rational number `< 1`, and it is attained on an extremal ray `R` of `NE̅(Y/Z)`:
`(K_Y + D + (1 - e) G) · R = 0` and `G · R > 0`, so that `(K_Y + D) · R < 0`.

The proof applies the finiteness of `(K_Y + B_c)`-negative relative extremal rays under the
support sandwich at one fixed `c₀ ∈ (e, 1)`: the negative rays for `B_c`, `e < c < c₀`, all lie
among these finitely many rays, so one of them recurs as `c ↓ e`.

## Main results

* `MMP.Fourfold.exists_isNegativeRelativeExtremalRayOf_of_supp_roundDown_le_supp_pullback`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero. Nefness over `Z` along the real segment `c ∈ [0, 1]` is
`MMP.Flips.IsRelativelyNef` of the `ℝ`-divisor `K_Y + D + (1 - c) G`. The degrees on `R` are
the linear forms `MMP.Fourfold.QDivisor.relativeCurveForm` on `N₁(Y/Z)`, evaluated on the
nonzero classes of `R`; `(K_Y + D) · R < 0` is
`MMP.Fourfold.IsNegativeRelativeExtremalRayOf`. The pull-back `h^* H` is
`MMP.Mori.Divisor.pullback`, whose side condition (no generic point of `Y` maps into `Supp H`) is
a hypothesis.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **The attained boundary-removal threshold.** Let `h : Y ⟶ Z` be a projective birational
morphism of normal projective varieties over an algebraically closed field of characteristic
zero, `Y` `ℚ`-factorial with canonical divisor `K`, and `D, G` effective `ℚ`-divisors with
`(Y, D + G)` dlt, `K + D + G` nef over `Z` and `K + D` not nef over `Z`. Suppose an effective
Cartier divisor `H` on `Z` satisfies `Supp ⌊D + (1 - c) G⌋ ⊆ Supp h^* H ⊆ Supp (D + (1 - c) G)`
for every rational `0 < c < 1`. Then `e = sup {c ∈ [0, 1] | K + D + (1 - c) G is nef over Z}` is
a rational number `e < 1`, and there is a `(K + D)`-negative extremal ray `R` of `NE̅(Y/Z)` on
which `K + D + (1 - e) G` has degree `0` and `G` has positive degree. -/
@[mmp "lem_fourfold_projective_boundary_removal_threshold_ray"]
public theorem exists_isNegativeRelativeExtremalRayOf_of_supp_roundDown_le_supp_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sZ]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsQFactorial sY) (hZ : IsNormalVariety k sZ)
    {h : Y ⟶ Z} (hh : h ≫ sZ = sY) (hhp : IsProjectiveMorphism h)
    (hhb : IsBirationalMorphism h)
    {K : Divisor Y} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n)
    {D G : QDivisor Y} (hD : D.IsEffective) (hG : G.IsEffective)
    (hDG : MMP.Intersection.IsDltPair sY (D + G))
    (hnef : MMP.Flips.IsRelativelyNef k sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D + G)))
    (hnotnef : ¬ MMP.Flips.IsRelativelyNef k sY h
      (QDivisor.toRDivisor (Divisor.toQDivisor K + D)))
    {H : Divisor Z} (hH : H.IsCartier) (hHe : H.IsEffective)
    (hHf : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H.supp)
    (hsand : ∀ c : ℚ, 0 < c → c < 1 →
      (D + (1 - c) • G).roundDown.supp ≤ (H.pullback hH hHf).supp ∧
        (H.pullback hH hHf).supp ≤ (D + (1 - c) • G).supp) :
    ∃ e : ℚ, (e : ℝ) = sSup {c : ℝ | c ∈ Set.Icc 0 1 ∧ MMP.Flips.IsRelativelyNef k sY h
        (QDivisor.toRDivisor (Divisor.toQDivisor K + D) + (1 - c) • QDivisor.toRDivisor G)} ∧
      e < 1 ∧ ∃ R : Set (RelativeNumericalCurveClasses sY h),
        IsNegativeRelativeExtremalRayOf sY h (Divisor.toQDivisor K + D) R ∧
        ∃ (he : (Divisor.toQDivisor K + D + (1 - e) • G).IsQCartier) (hGq : G.IsQCartier),
          ∀ u ∈ R, u ≠ 0 →
            QDivisor.relativeCurveForm sY h (Divisor.toQDivisor K + D + (1 - e) • G) he u = 0 ∧
              0 < QDivisor.relativeCurveForm sY h G hGq u := by
  refine MMP.FourfoldProofs.FourfoldProjectiveBoundaryRemovalThresholdRayProof.exists_rat_eq_sSup_and_ray
    hY hh hnef hnotnef fun c₀ hc₀ hc₀1 => ?_
  have hs : IsProjectiveSetting k sY sZ h := ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, hh⟩
  have hB : MMP.Intersection.IsDltPair sY (D + (1 - c₀) • G) := by
    refine MMP.Intersection.IsDltPair.of_le sY hDG (fun P => ?_) (fun P => ?_)
      (isQCartier_of_isQFactorial sY hY _)
    · have h1 : 0 ≤ D P := hD P
      have h2 : 0 ≤ G P := hG P
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Finsupp.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ (1 - c₀) * G P := mul_nonneg (by linarith) h2
      linarith
    · have h2 : 0 ≤ G P := hG P
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  obtain ⟨hKB, 𝓡, hfin, hmem, hgen, -⟩ :=
    exists_finite_isExtremalRay_of_support_roundDown_subset_pullback sY sZ h hs hhp hhb hZ hY hK
      hB hH hHe hHf (hsand c₀ hc₀ hc₀1).1 (hsand c₀ hc₀ hc₀1).2
  refine ⟨hKB, 𝓡, hfin, hmem, fun R hR => ?_⟩
  obtain ⟨C, hC, -, hRC⟩ := hgen R hR
  exact ⟨C, hC, hRC⟩

end MMP.Fourfold

end
