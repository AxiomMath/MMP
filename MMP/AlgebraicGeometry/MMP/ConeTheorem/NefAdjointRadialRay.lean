module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.CommonRayCurveBound
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute

/-!
# A uniform radial neighbourhood of a nef threefold adjoint

Let `f : Y ⟶ Z` be a morphism of projective complex varieties, with `Y` a normal
`ℚ`-factorial threefold, and let `(Y, B)` be a real klt pair whose adjoint `D = K_Y + B` is nef
over `Z`. Suppose a constant `a > 0` bounds from below the positive degrees `D · ℓ` on the
curves `ℓ` contracted by `f`, and put `ε = a / (2 (a + 6))`. Then for every effective real klt
boundary `C` and every `0 < t < ε`, every extremal ray `R` of the relative closed cone of curves
`NE̅(Y/Z)` which is negative for `D_t = (1 - t) D + t (K_Y + C)` is `D`-trivial.

The proof: a `D_t`-negative ray is `(K_Y + C)`-negative since `D` is nef, so it is spanned by
a rational curve `ℓ` with `(K_Y + C) · ℓ ≥ -6`; if `D · ℓ > 0` then `D · ℓ ≥ a` and
`D_t · ℓ ≥ a - t (a + 6) > a / 2 > 0`, a contradiction.

## Main results

* `MMP.Fourfold.extremalRay_degree_eq_zero_of_lt`

## Implementation notes

Degrees of `ℝ`-Cartier divisors on `N₁(Y/Z)` (`MMP.Mori.RelativeNumericalCurveClasses`) are
computed from a presentation `D = ∑ⱼ rⱼ Lⱼ` by Cartier divisors `Lⱼ`, as the linear form
`u ↦ ∑ⱼ rⱼ deg_u 𝒪_Y(Lⱼ)`. Negativity of the ray asks for one presentation of `D_t` that is
negative on `R ∖ {0}`; the conclusion holds for every presentation of `D`. Degrees on curves
are `MMP.Flips.IsRIntersectionNumber`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.ChainBigThreefoldRadialRay

open MMP.Mori MMP.Flips MMP.Fourfold

section Normalization

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_isCurveNormalization {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : MMP.Flips.IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve ℂ p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType ℂ p
  haveI hvar : AlgebraicGeometry.IsVariety ℂ (normalizationOverField ℂ p ≫ p) :=
    isVariety_normalizationOverField ℂ p
  haveI : IsIntegral (normalizationSchemeOverField ℂ p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField ℂ p) := isFinite_normalizationOverField ℂ p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField ℂ p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField ℂ p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField ℂ p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty
          hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField ℂ p).le.trans C.dim_le⟩

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    MMP.Flips.IsCartierIntersectionNumber ℂ sX C L hL (L.degreeOn ℂ sX C.ι C.dim_le hL) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_isCurveNormalization C
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

end Normalization

section Forms

variable {Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  (sY : Y ⟶ Spec (.of ℂ)) (f : Y ⟶ Z)

/-- The degree form `z ↦ (z · 𝒪_Y(L))` on `N₁(Y/Z)` of a Cartier divisor `L`. -/
private def relDeg (L : Divisor Y) (hL : L.IsCartier) :
    RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  haveI := hL.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sY f L.divisorialSheaf

private theorem relDeg_congr {L L' : Divisor Y} (h : L = L') (hL : L.IsCartier)
    (hL' : L'.IsCartier) : relDeg sY f L hL = relDeg sY f L' hL' := by
  subst h; rfl

/-- The degree form `z ↦ ∑ⱼ rⱼ (z · 𝒪_Y(Lⱼ))` on `N₁(Y/Z)` of a Cartier presentation. -/
private def relForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier) :
    RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  ∑ j, r j • relDeg sY f (L j) (hL j)

private theorem relForm_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : RelativeNumericalCurveClasses sY f) :
    relForm sY f r L hL z = ∑ j, r j *
      (haveI := (hL j).isInvertibleModule_divisorialSheaf
       RelativeNumericalCurveClasses.degree sY f (L j).divisorialSheaf z) := by
  simp [relForm, LinearMap.sum_apply, relDeg]

variable {sY f} in
/-- On the class of a contracted curve `ℓ`, the degree form of a presentation is
`∑ⱼ rⱼ deg_ℓ 𝒪_Y(Lⱼ)`. -/
private theorem relForm_relativeClass [QuasiCompact sY] {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier) {ℓ : ProperCurve sY}
    (hℓ : ℓ.IsContractedBy f) :
    relForm sY f r L hL (ℓ.relativeClass f hℓ) =
      ∑ j, r j * ((L j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hL j) : ℝ) := by
  rw [relForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  change OneCycle.degree ℝ sY (L j).divisorialSheaf (ℓ.cycle ℝ) = _
  rw [OneCycle.degree_cycle]
  rfl

private theorem continuous_relForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : Continuous (relForm sY f r L hL) := by
  rw [show ⇑(relForm sY f r L hL) = fun z => ∑ j, r j * relDeg sY f (L j) (hL j) z from
    funext fun z => by simp [relForm, LinearMap.sum_apply]]
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  exact RelativeNumericalCurveClasses.continuous_degree sY f _

/-- The form of the presentation `Fin.append (a • r₁) (b • r₂)`, `Fin.append L₁ L₂`. -/
private theorem relForm_append {m₁ m₂ : ℕ} (a b : ℝ) (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor Y)
    (hL₁ : ∀ j, (L₁ j).IsCartier) (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor Y)
    (hL₂ : ∀ j, (L₂ j).IsCartier) (hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier)
    (z : RelativeNumericalCurveClasses sY f) :
    relForm sY f (Fin.append (a • r₁) (b • r₂)) (Fin.append L₁ L₂) hL z =
      a * relForm sY f r₁ L₁ hL₁ z + b * relForm sY f r₂ L₂ hL₂ z := by
  have h₁ : ∀ j, relDeg sY f (Fin.append L₁ L₂ (Fin.castAdd m₂ j)) (hL _) =
      relDeg sY f (L₁ j) (hL₁ j) := fun j => relDeg_congr sY f (Fin.append_left L₁ L₂ j) _ _
  have h₂ : ∀ j, relDeg sY f (Fin.append L₁ L₂ (Fin.natAdd m₁ j)) (hL _) =
      relDeg sY f (L₂ j) (hL₂ j) := fun j => relDeg_congr sY f (Fin.append_right L₁ L₂ j) _ _
  simp only [relForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Fin.sum_univ_add,
    h₁, h₂, Fin.append_left, Fin.append_right, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- The degree form `z ↦ ∑ⱼ rⱼ (z · 𝒪_Y(Lⱼ))` on `N₁(Y)` of a Cartier presentation. -/
private def absForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier) :
    NumericalCurveClasses sY →ₗ[ℝ] ℝ :=
  ∑ j, r j • (haveI := (hL j).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sY (L j).divisorialSheaf)

private theorem absForm_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : NumericalCurveClasses sY) :
    absForm sY r L hL z = ∑ j, r j *
      (haveI := (hL j).isInvertibleModule_divisorialSheaf
       NumericalCurveClasses.degree sY (L j).divisorialSheaf z) := by
  simp [absForm, LinearMap.sum_apply]

private theorem absForm_relativeToAbsolute {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : RelativeNumericalCurveClasses sY f) :
    absForm sY r L hL (relativeToAbsolute sY f z) = relForm sY f r L hL z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
  rw [absForm_apply, relForm_apply]
  rfl

variable {sY f} in
/-- On a contracted curve `ℓ`, the value of the degree form of a presentation of `D` at `[ℓ]` is
an intersection number `D · ℓ`. -/
private theorem isRIntersectionNumber_relForm [QuasiCompact sY] {D : RDivisor Y} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {ℓ : ProperCurve sY}
    (hℓ : ℓ.IsContractedBy f) :
    IsRIntersectionNumber ℂ sY D r L ℓ (relForm sY f r L hL (ℓ.relativeClass f hℓ)) :=
  ⟨hL, fun j => (L j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hL j), hD,
    fun j =>
      isCartierIntersectionNumber_degreeOn sY ℓ (L j) (hL j),
    relForm_relativeClass r L hL hℓ⟩

variable {sY f} in
/-- The degree form of any presentation of an `f`-nef divisor is nonnegative on `NE̅(Y/Z)`. -/
private theorem relForm_nonneg_of_isRelativelyNef [QuasiCompact sY] {D : RDivisor Y}
    (hnef : IsRelativelyNef ℂ sY f D) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, 0 ≤ relForm sY f r L hL z := by
  obtain ⟨m₀, r₀, L₀, hL₀, hD₀, hnn⟩ := hnef
  have hcurve : ∀ (ℓ : ProperCurve sY) (hℓ : ℓ.IsContractedBy f),
      0 ≤ relForm sY f r L hL (ℓ.relativeClass f hℓ) := by
    intro ℓ hℓ
    have hx := isRIntersectionNumber_relForm r L hL hD hℓ
    have hx₀ := isRIntersectionNumber_relForm r₀ L₀ hL₀ hD₀ hℓ
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sY ℓ).1 _ _ _ _ _ _ _ hx hx₀]
    exact hnn ℓ hℓ _ hx₀
  have hcone : ∀ z ∈ relativeConeOfCurves sY f, 0 ≤ relForm sY f r L hL z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcurve C hC
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  intro z hz
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal (t := {z | 0 ≤ relForm sY f r L hL z}) hcone
    (isClosed_le continuous_const (continuous_relForm sY f r L hL)) hz

variable {sY f} in
/-- Over a projective base, a curve whose class comes from `N₁(Y/Z)` is contracted. -/
private theorem isContractedBy_of_relativeToAbsolute_eq {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hfc : f ≫ sZ = sY) (ℓ : ProperCurve sY)
    (u : RelativeNumericalCurveClasses sY f)
    (hu : relativeToAbsolute sY f u = OneCycle.numericalClass sY (ℓ.cycle ℝ)) :
    ℓ.IsContractedBy f := by
  obtain ⟨H, hHinv, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj H) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback f.toLRSHom.toShHom _
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfc H hHa ℓ ?_
  obtain ⟨⟨Z₁, hZ₁⟩, rfl⟩ := relativeNumericalClass_surjective sY f u
  have h0 : OneCycle.degree ℝ sY ((Scheme.Modules.pullback f).obj H) Z₁ = 0 := by
    rw [OneCycle.degree_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    dsimp only
    rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hfc C (hZ₁ hC) H]
    simp
  have h1 : ((ℓ.degree ℂ ((Scheme.Modules.pullback f).obj H) : ℤ) : ℝ) = 0 := by
    rw [← OneCycle.degree_cycle ℝ]
    change NumericalCurveClasses.degree sY _ (OneCycle.numericalClass sY (ℓ.cycle ℝ)) = 0
    rw [← hu]
    exact h0
  exact_mod_cast h1

end Forms

/-- A linear form vanishing at a nonzero point of an extremal ray vanishes on the ray. -/
private theorem map_eq_zero_of_isExtremalRay {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N R : Set V} (hR : IsExtremalRay ℝ N R) (g : V →ₗ[ℝ] ℝ) {u₁ : V} (hu₁R : u₁ ∈ R)
    (hu₁0 : u₁ ≠ 0) (hg : g u₁ = 0) : ∀ u ∈ R, g u = 0 := by
  obtain ⟨-, v, -, hRv⟩ := hR
  intro u hu
  rw [hRv] at hu hu₁R
  obtain ⟨c, -, rfl⟩ := hu
  obtain ⟨c₁, -, rfl⟩ := hu₁R
  have hc₁ : c₁ ≠ 0 := fun h => hu₁0 (by rw [h, zero_smul])
  rw [map_smul, smul_eq_mul] at hg
  rw [map_smul, smul_eq_mul, (mul_eq_zero.1 hg).resolve_left hc₁, mul_zero]

/-- For `0 < t < a / (2 (a + 6))`, `t⁻¹ ψ - ((1 - t) / t) φ < 0` when `ψ < 0 ≤ φ`. -/
private theorem inv_mul_add_div_mul_neg {a t ψ φ : ℝ} (ha : 0 < a) (ht₀ : 0 < t)
    (ht : t < a / (2 * (a + 6))) (hψ : ψ < 0) (hφ : 0 ≤ φ) :
    t⁻¹ * ψ + (-(1 - t) / t) * φ < 0 := by
  have ht1 : t < 1 / 2 := by
    refine ht.trans ?_
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h3 : 0 < t⁻¹ := inv_pos.2 ht₀
  have h4 : -(1 - t) / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ht₀.le
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h4 hφ]

/-- If `(1 - t) (K + B) + t (K + C) = ∑ rᵢ Lᵢ` and `K + B = ∑ r'ⱼ L'ⱼ`, then `K + C` is presented
by `Fin.append (t⁻¹ • r) ((-(1 - t) / t) • r')`, `Fin.append L L'`. -/
private theorem toRDivisor_add_eq_sum_append {Y : Scheme.{0}} (K : Divisor Y) (B C : RDivisor Y)
    {t : ℝ} (ht₀ : 0 < t) {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (r' : Fin m' → ℝ) (L' : Fin m' → Divisor Y)
    (heq : (1 - t) • logCanonicalDivisor K B + t • logCanonicalDivisor K C =
      ∑ j, r j • Divisor.toRDivisor (L j))
    (hD : logCanonicalDivisor K B = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    Divisor.toRDivisor K + C = ∑ j, Fin.append (t⁻¹ • r) ((-(1 - t) / t) • r') j •
      Divisor.toRDivisor (Fin.append L L' j) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply,
    smul_eq_mul, mul_smul, ← Finset.smul_sum, ← heq, ← hD]
  unfold logCanonicalDivisor
  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht₀.ne', one_smul, add_right_comm,
    ← add_smul]
  have : t⁻¹ * (1 - t) + -(1 - t) / t = 0 := by field_simp; ring
  rw [this, zero_smul, zero_add]

/-- The numerical heart of the radial ray lemma: `ψ < 0`, `a ≤ φ` and
`-6 ≤ t⁻¹ ψ - ((1 - t) / t) φ` are incompatible for `0 < t < a / (2 (a + 6))`. -/
private theorem false_of_lt_div_two_mul_add_six {a t ψ φ : ℝ} (ha : 0 < a) (ht₀ : 0 < t)
    (ht : t < a / (2 * (a + 6))) (hψ : ψ < 0) (hax : a ≤ φ)
    (hχ : -6 ≤ t⁻¹ * ψ + (-(1 - t) / t) * φ) : False := by
  have ht1 : t < 1 / 2 := by
    refine ht.trans ?_
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have key : ψ = t * (t⁻¹ * ψ + (-(1 - t) / t) * φ) + (1 - t) * φ := by
    field_simp; ring
  have hta : t * (2 * (a + 6)) < a := (lt_div_iff₀ (by positivity)).1 ht
  nlinarith

/-- **The radial ray lemma over a projective base.** For a morphism `f : Y ⟶ Z` of projective
complex varieties, every extremal ray of `NE̅(Y/Z)` which is negative for
`D_t = (1 - t) D + t (K + C)`, `0 < t < a / (2 (a + 6))`, is `D`-trivial. -/
private theorem extremalRay_degree_eq_zero_of_lt_of_isProjectiveVariety
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) [QuasiCompact sY] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z) (hfc : f ≫ sZ = sY)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (K : Divisor Y) (hK : K.IsCanonicalDivisor sY 3)
    (B : RDivisor Y)
    (hnef : IsRelativelyNef ℂ sY f (logCanonicalDivisor K B))
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ ℓ : ProperCurve sY, ℓ.IsContractedBy f →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber ℂ sY (logCanonicalDivisor K B) r L ℓ x → 0 < x → a ≤ x)
    (C : RDivisor Y) (hC : ∀ P, 0 ≤ C.coeff P) (hCklt : IsRealKltPair sY C)
    (t : ℝ) (ht₀ : 0 < t) (ht : t < a / (2 * (a + 6)))
    (R : Set (RelativeNumericalCurveClasses sY f))
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sY f :
      Set (RelativeNumericalCurveClasses sY f)) R)
    (hneg : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier),
      (1 - t) • logCanonicalDivisor K B + t • logCanonicalDivisor K C =
          ∑ j, r j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 → ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree sY f (L j).divisorialSheaf u) < 0)
    {m' : ℕ} (r' : Fin m' → ℝ) (L' : Fin m' → Divisor Y) (hL' : ∀ j, (L' j).IsCartier)
    (hD : logCanonicalDivisor K B = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    ∀ u ∈ R, relForm sY f r' L' hL' u = 0 := by
  obtain ⟨m, r, L, hL, heq, hlt⟩ := hneg
  have hφR : ∀ z ∈ R, 0 ≤ relForm sY f r' L' hL' z := fun z hz =>
    relForm_nonneg_of_isRelativelyNef hnef r' L' hL' hD z (hR.1.1 hz)
  have hψR : ∀ z ∈ R, z ≠ 0 → relForm sY f r L hL z < 0 := fun z hz hz0 => by
    rw [relForm_apply]; exact hlt z hz hz0
  set rE : Fin (m + m') → ℝ := Fin.append (t⁻¹ • r) ((-(1 - t) / t) • r')
  set LE : Fin (m + m') → Divisor Y := Fin.append L L'
  have hLE : ∀ j, (LE j).IsCartier := Fin.addCases (fun j => by simpa [LE] using hL j)
    (fun j => by simpa [LE] using hL' j)
  have hE : Divisor.toRDivisor K + C = ∑ j, rE j • Divisor.toRDivisor (LE j) :=
    toRDivisor_add_eq_sum_append K B C ht₀ r L r' L' heq hD
  have hχ : ∀ z, relForm sY f rE LE hLE z =
      t⁻¹ * relForm sY f r L hL z + (-(1 - t) / t) * relForm sY f r' L' hL' z :=
    fun z => relForm_append sY f _ _ r L hL r' L' hL' hLE z
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  have hR' := isExtremalRay_image_relativeToAbsolute sY sZ f hfc hR
  have hneg' : ∃ (j₀ : Unit) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y)
      (hL : ∀ i, (L i).IsCartier),
      Divisor.toRDivisor K + (fun _ => C) j₀ = ∑ i, r i • Divisor.toRDivisor (L i) ∧
      ∀ u ∈ relativeToAbsolute sY f '' R, u ≠ 0 →
        ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sY (L i).divisorialSheaf u) < 0 := by
    refine ⟨(), _, rE, LE, hLE, hE, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ hz0
    have hz0' : z ≠ 0 := fun h => hz0 (by rw [h, map_zero])
    rw [← absForm_apply sY rE LE hLE, absForm_relativeToAbsolute, hχ]
    exact inv_mul_add_div_mul_neg ha ht₀ ht (hψR z hz hz0') (hφR z hz)
  obtain ⟨ℓ, -, ⟨u₁, hu₁R, hu₁⟩, hℓ0, hbound⟩ :=
    exists_isRationalCurve_numericalClass_mem_and_neg_six_le (sX := sY) hYq hK
      (B := fun _ : Unit => C) (fun _ => hC) (fun _ => hCklt) hR' hneg'
  have hℓc := isContractedBy_of_relativeToAbsolute_eq hZ hfc ℓ u₁ hu₁
  have hinj := (existsUnique_isNaturalRelativeMap_and_injective sY f).2 _
    (isNaturalRelativeMap_relativeToAbsolute sY f)
  have hu₁eq : ℓ.relativeClass f hℓc = u₁ := hinj (by rw [hu₁]; rfl)
  have hu₁0 : u₁ ≠ 0 := fun h => hℓ0 (by rw [← hu₁, h, map_zero])
  have hχℓ : -6 ≤ relForm sY f rE LE hLE u₁ := by
    have := hbound () _ rE LE hLE hE
    rwa [← absForm_apply sY rE LE hLE, ← hu₁, absForm_relativeToAbsolute] at this
  have hφu₁ : relForm sY f r' L' hL' u₁ = 0 := by
    by_contra hne
    have hpos : 0 < relForm sY f r' L' hL' u₁ := lt_of_le_of_ne (hφR u₁ hu₁R) (Ne.symm hne)
    have hx := isRIntersectionNumber_relForm r' L' hL' hD hℓc
    rw [hu₁eq] at hx
    rw [hχ] at hχℓ
    exact false_of_lt_div_two_mul_add_six ha ht₀ ht (hψR u₁ hu₁R hu₁0)
      (hgap ℓ hℓc m' r' L' _ hx hpos) hχℓ
  exact map_eq_zero_of_isExtremalRay hR _ hu₁R hu₁0 hφu₁

end MMP.ChainBigThreefoldRadialRay

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A uniform radial neighbourhood of a nef threefold adjoint.** Let `f : Y ⟶ Z` be a
morphism of projective complex varieties, `Y` a normal `ℚ`-factorial threefold with canonical
divisor `K`, and `B` a real boundary with `(Y, B)` klt and `D = K + B` nef over `Z`. Let `a > 0`
be such that `a ≤ D · ℓ` whenever `D · ℓ > 0` for a curve `ℓ` contracted by `f`. Then for every
effective real klt boundary `C`, every `0 < t < a / (2 (a + 6))` and every extremal ray `R` of
`NE̅(Y/Z)` on which `D_t = (1 - t) D + t (K + C)` is negative, `D` has degree zero on `R`. -/
@[mmp "lem_fourfold_big_threefold_radial_ray"]
public theorem extremalRay_degree_eq_zero_of_lt
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) [QuasiCompact sY] (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z)
    (hf : f ≫ sZ = sY) (hYq : IsQFactorial sY)
    (K : Divisor Y) (hK : K.IsCanonicalDivisor sY 3)
    (B : RDivisor Y) (_hB : IsRealKltPair sY B)
    (hnef : IsRelativelyNef ℂ sY f (logCanonicalDivisor K B))
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ ℓ : ProperCurve sY, ℓ.IsContractedBy f →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber ℂ sY (logCanonicalDivisor K B) r L ℓ x → 0 < x → a ≤ x)
    (C : RDivisor Y) (hC : ∀ P, 0 ≤ C.coeff P) (hCklt : IsRealKltPair sY C)
    (t : ℝ) (ht₀ : 0 < t) (ht : t < a / (2 * (a + 6)))
    (R : Set (RelativeNumericalCurveClasses sY f))
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sY f :
      Set (RelativeNumericalCurveClasses sY f)) R)
    (hneg : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier),
      (1 - t) • logCanonicalDivisor K B + t • logCanonicalDivisor K C =
          ∑ j, r j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 → ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree sY f (L j).divisorialSheaf u) < 0) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier),
      logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j) →
        ∀ u ∈ R, ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree sY f (L j).divisorialSheaf u) = 0 := by
  intro m r L hL hD u hu
  rw [← MMP.ChainBigThreefoldRadialRay.relForm_apply]
  exact
    MMP.ChainBigThreefoldRadialRay.extremalRay_degree_eq_zero_of_lt_of_isProjectiveVariety sY
    hZ f hf hY hYq K hK B hnef a ha hgap C hC hCklt t ht₀ ht R hR hneg r L hL hD u hu

end MMP.Fourfold
