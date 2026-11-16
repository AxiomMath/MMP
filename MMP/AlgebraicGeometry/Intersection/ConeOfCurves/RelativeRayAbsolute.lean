module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
import MMP.AlgebraicGeometry.Morphisms.ClosedPointsDense
import MMP.AlgebraicGeometry.Positivity.NakaiMoishezonKleiman
import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.Analysis.Convex.Cone.CompactSlices
import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.AmpleStrictlyPositive
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Relative extremal rays over a projective base are absolute extremal rays

Let `f : X ⟶ S` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, and let `ι : N₁(X/S) → N₁(X)` be the natural map sending the class of a
relative 1-cycle to its class in `N₁(X)`. The image under `ι` of every extremal ray of the
relative closed cone of curves `NE̅(X/S)` is an extremal ray of the closed cone of curves
`NE̅(X)`. The point is that `ι(NE̅(X/S))` is the intersection of `NE̅(X)` with the kernel of the
pushforward `f_*`, and `NE̅(S)` contains no line because `S` is projective.

## Main results

* `MMP.Mori.isExtremalRay_image_relativeToAbsolute`: `ι` sends extremal rays of `NE̅(X/S)` to
  extremal rays of `NE̅(X)`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §3.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Degrees of Cartier divisors -/

section Pairing

variable {k : Type} [Field k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}

/-- `deg_C 𝒪_Y(E + E') = deg_C 𝒪_Y(E) + deg_C 𝒪_Y(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sY) (E E' : Y.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) + C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sY C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

end Pairing

/-! ### Domination by a positive form -/

private theorem apply_eq_norm_mul_apply_symm_smul {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃ₗ[ℝ] W) (χ : V →ₗ[ℝ] ℝ) (z : V) :
    χ z = ‖e z‖ * χ (e.symm (‖e z‖⁻¹ • e z)) := by
  rcases eq_or_ne (e z) 0 with h0 | h0
  · simp [show z = 0 by simpa using h0]
  rw [map_smul, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]

private theorem smul_mem_preimage_inter_sphere {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (e : V ≃ₗ[ℝ] W) {K : Set V}
    (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) {z : V} (hz : z ∈ K) (hz0 : z ≠ 0) :
    ‖e z‖⁻¹ • e z ∈ e.symm ⁻¹' K ∩ Metric.sphere 0 1 := by
  have hez : e z ≠ 0 := by simpa using hz0
  refine ⟨?_, by simp [norm_smul, norm_ne_zero_iff.2 hez]⟩
  rw [Set.mem_preimage, map_smul, LinearEquiv.symm_apply_apply]
  exact hcone z hz _ (inv_pos.2 (norm_pos_iff.2 hez))

/-- **A positive form dominates every form on a closed cone.** In a finite-dimensional real vector
space whose topology makes the linear maps from `ℝⁿ` continuous, if `φ` is positive on the
nonzero vectors of a closed cone `K`, then every linear form `ψ` satisfies `ψ ≤ m φ` on `K` for
some natural number `m`. -/
private theorem exists_nat_le_mul_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : Set V}
    (hK : IsClosed K) (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (φ ψ : V →ₗ[ℝ] ℝ)
    (hφ : ∀ z ∈ K, z ≠ 0 → 0 < φ z) :
    ∃ m : ℕ, ∀ z ∈ K, ψ z ≤ m * φ z := by
  let e := (Module.finBasis ℝ V).equivFun
  set K' : Set (Fin (Module.finrank ℝ V) → ℝ) := e.symm ⁻¹' K
  have hK' : IsClosed K' := hK.preimage (hcont e.symm.toLinearMap)
  let φ' := φ.comp e.symm.toLinearMap
  let ψ' := ψ.comp e.symm.toLinearMap
  by_cases hS : (K' ∩ Metric.sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).Nonempty
  swap
  · refine ⟨1, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact absurd ⟨_, smul_mem_preimage_inter_sphere e hcone hz hz0⟩ hS
  have hφc : Continuous φ' := LinearMap.continuous_of_finiteDimensional φ'
  obtain ⟨w0, hw0, hmin⟩ :=
    ((isCompact_sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).inter_left hK').exists_isMinOn hS
      hφc.continuousOn
  have hw00 : e.symm w0 ≠ 0 := by
    intro h
    simp [show w0 = 0 by simpa using h] at hw0
  have hc : 0 < φ' w0 := hφ _ hw0.1 hw00
  set C := ‖LinearMap.toContinuousLinearMap ψ'‖
  obtain ⟨m, hm⟩ := exists_nat_gt (C / φ' w0)
  refine ⟨m + 1, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  have hu := smul_mem_preimage_inter_sphere e hcone hz hz0
  set u := ‖e z‖⁻¹ • e z
  have hnu : ‖u‖ = 1 := by simpa using hu.2
  have h1 : φ' w0 ≤ φ' u := hmin hu
  have h2 : ψ' u ≤ C := by
    have := (LinearMap.toContinuousLinearMap ψ').le_opNorm u
    rw [hnu, mul_one] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have h3 : C ≤ m * φ' w0 := ((div_lt_iff₀ hc).1 hm).le
  have h4 : ψ' u ≤ (m + 1 : ℕ) * φ' u := by
    push_cast
    nlinarith
  rw [apply_eq_norm_mul_apply_symm_smul e ψ z, apply_eq_norm_mul_apply_symm_smul e φ z]
  calc ‖e z‖ * ψ (e.symm u) = ‖e z‖ * ψ' u := rfl
    _ ≤ ‖e z‖ * ((m + 1 : ℕ) * φ' u) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = ((m + 1 : ℕ) : ℝ) * (‖e z‖ * φ (e.symm u)) := by
      change ‖e z‖ * ((m + 1 : ℕ) * φ (e.symm u)) = _
      ring

section Natural

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

private theorem degree_relativeToAbsolute (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.degree sX L (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.degree sX f L z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

private theorem intersectionNumber_relativeToAbsolute (D : KCartierDivisor ℝ X)
    (z : RelativeNumericalCurveClasses sX f) :
    NumericalCurveClasses.intersectionNumber D (relativeToAbsolute sX f z) =
      RelativeNumericalCurveClasses.intersectionNumber D z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rfl

/-- Isomorphic invertible sheaves have the same degree form on `N₁(X)`. -/
private theorem degree_eq_of_iso {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    NumericalCurveClasses.degree sX L = NumericalCurveClasses.degree sX L' := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  change OneCycle.degree ℝ sX L Z = OneCycle.degree ℝ sX L' Z
  rw [OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

private theorem continuous_relativeToAbsolute : Continuous (relativeToAbsolute sX f) :=
  continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun h => continuous_induced_rng.2 <| by
    have he : ⇑(NumericalCurveClasses.degree sX L) ∘ ⇑(relativeToAbsolute sX f) =
        RelativeNumericalCurveClasses.degree sX f L :=
      funext (degree_relativeToAbsolute L)
    rw [he]
    exact RelativeNumericalCurveClasses.continuous_degree sX f L

private theorem relativeToAbsolute_mem_coneOfCurves {z : RelativeNumericalCurveClasses sX f}
    (hz : z ∈ relativeConeOfCurves sX f) : relativeToAbsolute sX f z ∈ coneOfCurves sX := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact numericalClass_cycle_mem_coneOfCurves sX C
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : ℝ) • x from rfl, map_smul]
    exact (coneOfCurves sX).smul_mem a.2 hx

private theorem relativeToAbsolute_mem_closedConeOfCurves {z : RelativeNumericalCurveClasses sX f}
    (hz : z ∈ relativeClosedConeOfCurves sX f) :
    relativeToAbsolute sX f z ∈ closedConeOfCurves sX :=
  closure_mono (Set.image_subset_iff.2 fun _ hw => relativeToAbsolute_mem_coneOfCurves hw)
    (image_closure_subset_closure_image continuous_relativeToAbsolute ⟨z, hz, rfl⟩)

private theorem relativeToAbsolute_injective : Function.Injective (relativeToAbsolute sX f) :=
  (existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
    (isNaturalRelativeMap_relativeToAbsolute sX f)

end Natural

/-! ### Projective morphisms -/

/-- A morphism of projective `k`-varieties is projective. -/
private theorem isProjective_of_comp_eq {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjective f := by
  have : IsSeparated sY := hY.toIsVariety.toIsSeparated
  let γ : X ⟶ Limits.pullback sX sY := Limits.pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (Limits.pullback.fst sX sY) inferInstance
      (by simp only [γ, Limits.pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ Limits.pullback.snd sX sY = f := Limits.pullback.lift_snd _ _ _
  rw [← hγ]
  exact ((MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)).isProjective

/-! ### The pairing on `N₁(X)` -/

section Absolute

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The pairing `E ↦ (z · E)` with a fixed class `z ∈ N₁(X)`, additive on Cartier divisors. -/
private noncomputable def absPairing (z : NumericalCurveClasses sX) : X.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    simp only [NumericalCurveClasses.intersectionNumber_numericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem absPairing_apply (z : NumericalCurveClasses sX) (E : X.CartierDivisor) :
    absPairing z E = NumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z := rfl

/-- Cartier divisors separate `N₁(X)` on an integral `X`. -/
private theorem exists_absPairing_ne_zero [IsIntegral X] {z : NumericalCurveClasses sX}
    (hz0 : z ≠ 0) : ∃ E : X.CartierDivisor, absPairing z E ≠ 0 := by
  by_contra! h
  apply hz0
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  simp only [absPairing_apply, NumericalCurveClasses.intersectionNumber_numericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

variable (sX) in
/-- Linear maps from a coordinate space into `N₁(X)` are continuous for its numerical topology. -/
private theorem continuous_linearMap_abs {ι : Type} [Finite ι]
    (g : (ι → ℝ) →ₗ[ℝ] NumericalCurveClasses sX) : Continuous g :=
  continuous_iInf_rng.2 fun M => continuous_iInf_rng.2 fun _ => continuous_induced_rng.2 <|
    LinearMap.continuous_of_finiteDimensional ((NumericalCurveClasses.degree sX M).comp g)

/-- An ample Cartier divisor on a projective variety is positive on `NE̅(X) ∖ {0}`. -/
private theorem absPairing_pos_of_isAmple (hX : MMP.Mori.IsProjectiveVariety k sX)
    {A : X.CartierDivisor} (hA : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A))
    {z : NumericalCurveClasses sX} (hz : z ∈ closedConeOfCurves sX) (hz0 : z ≠ 0) :
    0 < absPairing z A := by
  obtain ⟨Z, hZ⟩ := OneCycle.numericalClass_surjective sX z
  have := closedConeOfCurves_diff_zero_subset_posHalfspace sX A hA ⟨hz, hz0⟩ Z hZ
  rwa [absPairing_apply, ← hZ, NumericalCurveClasses.intersectionNumber_numericalClass]

/-- On a projective variety some Cartier divisor is positive on `NE̅(X) ∖ {0}`. -/
private theorem exists_absPairing_pos (hX : MMP.Mori.IsProjectiveVariety k sX) :
    ∃ A : X.CartierDivisor, ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < absPairing z A := by
  obtain ⟨A, hA⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sX)
  exact ⟨A, fun z hz hz0 => absPairing_pos_of_isAmple hX hA hz hz0⟩

/-- **Domination on `NE̅(X)`.** If `A` is positive on `NE̅(X) ∖ {0}`, then every Cartier divisor
`E` satisfies `|(E · z)| ≤ m (A · z)` on `NE̅(X)` for some natural number `m`. -/
private theorem exists_abs_absPairing_le [FiniteDimensional ℝ (NumericalCurveClasses sX)]
    {A : X.CartierDivisor} (hA : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 → 0 < absPairing z A)
    (E : X.CartierDivisor) :
    ∃ m : ℕ, ∀ z ∈ closedConeOfCurves sX, |absPairing z E| ≤ m * absPairing z A := by
  have hcl : IsClosed (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) := by
    rw [coe_closedConeOfCurves]; exact isClosed_closure
  have hcone : ∀ z ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)), ∀ t : ℝ, 0 < t →
      t • z ∈ closedConeOfCurves sX := fun z hz t ht => (closedConeOfCurves sX).smul_mem ht.le hz
  let ψ : X.CartierDivisor → Module.Dual ℝ (NumericalCurveClasses sX) := fun E =>
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E)
  obtain ⟨m₁, h₁⟩ := exists_nat_le_mul_of_pos (continuous_linearMap_abs sX) hcl hcone
    (ψ A) (ψ E) hA
  obtain ⟨m₂, h₂⟩ := exists_nat_le_mul_of_pos (continuous_linearMap_abs sX) hcl hcone
    (ψ A) (-ψ E) hA
  refine ⟨m₁ + m₂, fun z hz => ?_⟩
  have h0 : 0 ≤ absPairing z A := by
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [absPairing_apply, map_zero]
    · exact (hA z hz hz0).le
  have h₁' : absPairing z E ≤ m₁ * absPairing z A := h₁ z hz
  have h₂' : -absPairing z E ≤ m₂ * absPairing z A := h₂ z hz
  rw [abs_le]
  push_cast
  constructor <;> nlinarith

/-- **Cartier divisors span the dual of `N₁(X)`.** On an integral `X` with `N₁(X)`
finite-dimensional, every linear form on `N₁(X)` is a finite real combination of the evaluations
`z ↦ (E · z)` at Cartier divisors `E`. -/
private theorem exists_finsupp_eq_sum_absPairing [IsIntegral X]
    [FiniteDimensional ℝ (NumericalCurveClasses sX)]
    (φ : Module.Dual ℝ (NumericalCurveClasses sX)) :
    ∃ c : X.CartierDivisor →₀ ℝ, ∀ z, φ z = ∑ E ∈ c.support, c E * absPairing z E := by
  classical
  let ψ : X.CartierDivisor → Module.Dual ℝ (NumericalCurveClasses sX) := fun E =>
    NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E)
  have h0 : (Submodule.span ℝ (Set.range ψ)).dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun z hz => by_contra fun hz0 => ?_
    obtain ⟨E, hE⟩ := exists_absPairing_ne_zero hz0
    exact hE ((Submodule.mem_dualCoannihilator _).1 hz _ (Submodule.subset_span ⟨E, rfl⟩))
  have hspan : Submodule.span ℝ (Set.range ψ) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℝ (Set.range ψ)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (hspan ▸ Submodule.mem_top : φ ∈ Submodule.span ℝ (Set.range ψ))
  refine ⟨c, fun z => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  simp [ψ, absPairing_apply]

/-- **Rounding error.** Replacing the real coefficients `t c_E` by their floors changes the
pairing of `∑ t c_E E` with `z` by at most `∑ |(E · z)|`. -/
private theorem abs_absPairing_sum_floor_sub_le (s : Finset X.CartierDivisor)
    (c : X.CartierDivisor → ℝ) (t : ℝ) (z : NumericalCurveClasses sX) :
    |absPairing z (∑ E ∈ s, ⌊t * c E⌋ • E) - t * ∑ E ∈ s, c E * absPairing z E| ≤
      ∑ E ∈ s, |absPairing z E| := by
  rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E _ => ?_)
  rw [map_zsmul, zsmul_eq_mul, ← mul_assoc, ← sub_mul, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨?_, ?_⟩)
  · linarith [Int.lt_floor_add_one (t * c E)]
  · linarith [Int.floor_le (t * c E)]

/-- **A divisor separating `u` from a hyperplane section of `NE̅(X)`.** If `φ u = -1`, some Cartier
divisor `D` is negative on `u` and positive on the nonzero classes of `NE̅(X) ∩ ker φ`. -/
private theorem exists_absPairing_neg_and_pos (hX : MMP.Mori.IsProjectiveVariety k sX)
    [FiniteDimensional ℝ (NumericalCurveClasses sX)]
    (φ : Module.Dual ℝ (NumericalCurveClasses sX)) {u : NumericalCurveClasses sX}
    (hφu : φ u = -1) :
    ∃ D : X.CartierDivisor, absPairing u D < 0 ∧
      ∀ w ∈ closedConeOfCurves sX, w ≠ 0 → φ w = 0 → 0 < absPairing w D := by
  haveI : IsIntegral X := hX.toIsVariety.toIsIntegral
  obtain ⟨c, hφc⟩ := exists_finsupp_eq_sum_absPairing φ
  obtain ⟨A, hA⟩ := exists_absPairing_pos hX
  choose m hm using exists_abs_absPairing_le (sX := sX) hA
  set M : ℕ := ∑ E ∈ c.support, m E + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ E ∈ c.support, |absPairing u E| + M * absPairing u A)
  set D : X.CartierDivisor := ∑ E ∈ c.support, ⌊(N : ℝ) * c E⌋ • E + M • A
  have herr := fun z : NumericalCurveClasses sX =>
    abs_le.1 (abs_absPairing_sum_floor_sub_le c.support c N z)
  have hD : ∀ z : NumericalCurveClasses sX, absPairing z D =
      absPairing z (∑ E ∈ c.support, ⌊(N : ℝ) * c E⌋ • E) + M * absPairing z A := fun z => by
    rw [map_add, map_nsmul, nsmul_eq_mul]
  refine ⟨D, ?_, fun w hwK hw0 hφw => ?_⟩
  · have h1 := (herr u).2
    rw [← hφc, hφu] at h1
    rw [hD]
    linarith
  have h1 := (herr w).1
  rw [← hφc, hφw, mul_zero, sub_zero] at h1
  have h2 : ∑ E ∈ c.support, |absPairing w E| ≤
      (∑ E ∈ c.support, (m E : ℝ)) * absPairing w A := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun E _ => hm E w hwK
  rw [hD]
  push_cast [M]
  nlinarith [hA w hwK hw0]

end Absolute

/-- **An `f`-ample divisor is positive on `NE̅(X) ∩ ker f_* ∖ {0}`.** If `H` is `f`-ample and
`u ∈ NE̅(X)` is nonzero with `f_* u = 0`, then `(H · u) > 0`. -/
private theorem absPairing_pos_of_isRelativelyAmple {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) {H : X.CartierDivisor}
    (hH : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf H))
    {u : NumericalCurveClasses sX} (hu : u ∈ closedConeOfCurves sX) (hu0 : u ≠ 0)
    (hfu : NumericalCurveClasses.pushforward f hf u = 0) : 0 < absPairing u H := by
  haveI : IsIntegral X := hX.toIsVariety.toIsIntegral
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  obtain ⟨M, hM⟩ := IsProjectiveVariety.exists_isAmple_cartierDivisorSheaf (sX := sY)
  obtain ⟨B, ⟨eB⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))
  obtain ⟨ν, hν⟩ := (MMP.Foundations.isAmple_add_zsmul_pullback k hX hY hf hM hH
    ⟨eB.symm⟩).exists
  have hpos : 0 < absPairing u (H + ν • B) := absPairing_pos_of_isAmple hX hν hu hu0
  have hB : absPairing u B = 0 := by
    rw [absPairing_apply, NumericalCurveClasses.intersectionNumber_ofCartier,
      degree_eq_of_iso eB.symm, ← NumericalCurveClasses.degree_pushforward f hf, hfu, map_zero]
  rwa [map_add, map_zsmul, hB, smul_zero, add_zero] at hpos

/-! ### The closed cone meets the kernel of `f_*` inside `ι(N₁(X/Y))` -/

/-- **`NE̅(X) ∩ ker f_* ⊆ ι(N₁(X/Y))`.** For a morphism `f : X ⟶ Y` of projective varieties over
an algebraically closed field of characteristic zero, a class `u ∈ NE̅(X)` with `f_* u = 0` lies in
the image of the natural map `ι : N₁(X/Y) → N₁(X)`. -/
private theorem mem_range_relativeToAbsolute_of_pushforward_eq_zero {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hY : MMP.Mori.IsProjectiveVariety k sY) {f : X ⟶ Y} (hf : f ≫ sY = sX)
    {u : NumericalCurveClasses sX} (hu : u ∈ closedConeOfCurves sX)
    (hfu : NumericalCurveClasses.pushforward f hf u = 0) :
    u ∈ LinearMap.range (relativeToAbsolute sX f) := by
  by_contra hW
  haveI : IsIntegral X := hX.toIsVariety.toIsIntegral
  haveI : MMP.Mori.IsVariety k sX := hX.toIsVariety
  haveI : MMP.Mori.IsVariety k sY := hY.toIsVariety
  haveI := MMP.Mori.finiteDimensional_numericalCurveClasses sX
  have hinj := relativeToAbsolute_injective (sX := sX) (f := f)
  have hu0 : u ≠ 0 := fun h => hW (h ▸ zero_mem _)
  obtain ⟨φ₀, hφ₀u, hφ₀W⟩ := Submodule.exists_le_ker_of_notMem hW
  set φ : Module.Dual ℝ (NumericalCurveClasses sX) := (-(φ₀ u)⁻¹) • φ₀
  have hφW : ∀ z, φ (relativeToAbsolute sX f z) = 0 := fun z => by
    simp [φ, LinearMap.mem_ker.1 (hφ₀W ⟨z, rfl⟩)]
  obtain ⟨D, hDu, hD⟩ := exists_absPairing_neg_and_pos hX φ (u := u) (by simp [φ, hφ₀u])
  have hDpos : ∀ z ∈ relativeClosedConeOfCurves sX f, z ≠ 0 →
      0 < RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z :=
    fun z hz hz0 => by
      rw [← intersectionNumber_relativeToAbsolute, ← absPairing_apply]
      exact hD _ (relativeToAbsolute_mem_closedConeOfCurves hz)
        (fun h => hz0 (hinj (h.trans (map_zero _).symm))) (hφW z)
  have hDamp : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf D) :=
    (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
      (isProjective_of_comp_eq hX hY hf) hf D).2 hDpos
  exact hDu.not_gt (absPairing_pos_of_isRelativelyAmple hX hY hf hDamp hu hu0 hfu)

/-- A class of `NE̅(X) ∩ ker f_*` is the image of a class of `NE̅(X/S)`. -/
private theorem mem_image_relativeClosedConeOfCurves_of_pushforward_eq_zero
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] {f : X ⟶ S} (hf : f ≫ sS = sX) {u : NumericalCurveClasses sX}
    (hu : u ∈ closedConeOfCurves sX) (hfu : NumericalCurveClasses.pushforward f hf u = 0) :
    u ∈ relativeToAbsolute sX f '' (relativeClosedConeOfCurves sX f : Set _) := by
  obtain ⟨a, rfl⟩ := mem_range_relativeToAbsolute_of_pushforward_eq_zero ‹_› ‹_› hf hu hfu
  rw [MMP.Mori.image_relativeClosedConeOfCurves_eq_inter_range sX sS f hf]
  exact ⟨hu, a, rfl⟩

/-- If `f_* u + f_* w = 0` for `u, w ∈ NE̅(X)`, then `f_* u = 0`, as `NE̅(S)` is pointed. -/
private theorem pushforward_eq_zero_of_add_eq_zero
    {k : Type} [Field k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sS] {f : X ⟶ S} (hf : f ≫ sS = sX) {u w : NumericalCurveClasses sX}
    (hu : u ∈ closedConeOfCurves sX) (hw : w ∈ closedConeOfCurves sX)
    (hsum : NumericalCurveClasses.pushforward f hf u +
      NumericalCurveClasses.pushforward f hf w = 0) :
    NumericalCurveClasses.pushforward f hf u = 0 := by
  have hπK : ∀ u ∈ closedConeOfCurves sX,
      NumericalCurveClasses.pushforward f hf u ∈ closedConeOfCurves sS := fun u hu =>
    image_closedConeOfCurves_subset f hf
      (NumericalCurveClasses.isNumericalPushforward_pushforward f hf) ⟨u, hu, rfl⟩
  rw [← Submodule.mem_bot ℝ, ← lineal_closedConeOfCurves_eq_bot sS]
  refine PointedCone.mem_lineal.2 ⟨hπK u hu, ?_⟩
  rw [neg_eq_iff_add_eq_zero.2 hsum]
  exact hπK w hw

/-! ### The main theorem -/

/-- For a morphism `f : X ⟶ S` of projective varieties over an algebraically closed field of
characteristic zero, the natural map `relativeToAbsolute sX f : N₁(X/S) → N₁(X)` carries every
extremal ray of the relative closed cone of curves `relativeClosedConeOfCurves sX f` onto an
extremal ray of the closed cone of curves `closedConeOfCurves sX`. -/
@[mmp "lem_mmp_projective_relative_ray_absolute"]
public theorem isExtremalRay_image_relativeToAbsolute
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sS] (f : X ⟶ S) (hf : f ≫ sS = sX)
    {R : Set (RelativeNumericalCurveClasses sX f)}
    (hR : IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set _) R) :
    IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (relativeToAbsolute sX f '' R) := by
  have hinj := relativeToAbsolute_injective (sX := sX) (f := f)
  obtain ⟨⟨hRK, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := hR
  set π := NumericalCurveClasses.pushforward f hf
  refine ⟨⟨?_, ⟨⟨0, hR0, map_zero _⟩, ?_⟩, ?_, ?_⟩, relativeToAbsolute sX f v,
    fun h => hv0 (hinj (h.trans (map_zero _).symm)), ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact relativeToAbsolute_mem_closedConeOfCurves (hRK hr)
  · rintro _ ⟨r, hr, rfl⟩ c hc
    exact ⟨c • r, hRs r hr c hc, map_smul _ _ _⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    exact ⟨r + r', hRadd r hr r' hr', map_add _ _ _⟩
  · rintro u hu w hw ⟨r, hr, hrw⟩
    have hsum : π u + π w = 0 := by
      rw [← map_add, ← hrw]
      exact LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward f hf ⟨r, rfl⟩)
    have hπu : π u = 0 := pushforward_eq_zero_of_add_eq_zero sS hf hu hw hsum
    have hπw : π w = 0 := by rwa [hπu, zero_add] at hsum
    obtain ⟨a, ha, rfl⟩ := mem_image_relativeClosedConeOfCurves_of_pushforward_eq_zero sS hf hu hπu
    obtain ⟨b, hb, rfl⟩ := mem_image_relativeClosedConeOfCurves_of_pushforward_eq_zero sS hf hw hπw
    have hab : a + b = r := hinj (by rw [map_add, hrw])
    obtain ⟨haR, hbR⟩ := hRext a ha b hb (hab ▸ hr)
    exact ⟨⟨a, haR, rfl⟩, ⟨b, hbR, rfl⟩⟩
  · rw [hRv]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul _ _ _⟩

end MMP.Mori
