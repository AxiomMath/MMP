module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
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
# The relative closed cone of curves inside the absolute one

Let `f : X ⟶ Y` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, and let `ι : N₁(X/Y) → N₁(X)` be the natural map sending the class of a
relative 1-cycle to its class in `N₁(X)`. The image under `ι` of the relative closed cone of curves
`NE(X/Y)‾` is the intersection of the closed cone of curves `NE(X)‾` with the image of `ι`.

The inclusion `⊆` holds because `ι` is continuous and sends the class of a contracted curve to
its class in `N₁(X)`. Conversely let `ξ = ι v ∈ NE(X)‾` with `v ∉ NE(X/Y)‾`. Since `NE(X/Y)‾`
embeds in the pointed cone `NE(X)‾`, it contains no line, so there is `ℓ ∈ N₁(X/Y)^*` positive on
`NE(X/Y)‾ ∖ {0}` with `ℓ(v) < 0`. Cartier divisors span `N₁(X/Y)^*`; rounding the coefficients of
a large multiple of `ℓ` gives a Cartier divisor `H` with the same two properties. By the relative
Kleiman criterion `H` is `f`-ample, so `H + ν f^*M` is ample for an ample `M` on `Y` and `ν ≫ 0`,
hence `((H + ν f^*M) · ξ) > 0`. But `(f^*M · ξ) = (M · f_*ξ) = 0`, so `(H · v) > 0`, a
contradiction.

## Main results

* `MMP.Mori.image_relativeClosedConeOfCurves_eq_inter_range`:
  `ι(NE(X/Y)‾) = NE(X)‾ ∩ ι(N₁(X/Y))`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, 1.44,
  Proposition 3.27(4).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-! ### The pairing with Cartier divisors -/

section Pairing

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) + C.degree k (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (CartierDivisor.sheaf E)).obj (CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

variable (f) in
/-- The pairing `E ↦ (z · E)` with a fixed class `z ∈ N₁(X/Y)`, additive on Cartier divisors. -/
private noncomputable def pairing (z : RelativeNumericalCurveClasses sX f) :
    X.CartierDivisor →+ ℝ :=
  AddMonoidHom.mk' (fun E => RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z) fun E E' => by
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
    simp only [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_apply]
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun C _ => ?_
    rw [degree_cartierSheaf_add]
    push_cast
    ring

private theorem pairing_apply (z : RelativeNumericalCurveClasses sX f) (E : X.CartierDivisor) :
    pairing f z E = RelativeNumericalCurveClasses.intersectionNumber
      (KCartierDivisor.ofCartier ℝ E) z := rfl

/-- Cartier divisors separate `N₁(X/Y)` on an integral `X`. -/
private theorem exists_pairing_ne_zero [IsIntegral X] {z : RelativeNumericalCurveClasses sX f}
    (hz0 : z ≠ 0) : ∃ E : X.CartierDivisor, pairing f z E ≠ 0 := by
  by_contra! h
  apply hz0
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  simp only [pairing_apply, RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

variable (sX f) in
/-- Linear maps from a coordinate space into `N₁(X/Y)` are continuous for its weak topology. -/
private theorem continuous_linearMap {ι : Type} [Finite ι]
    (g : (ι → ℝ) →ₗ[ℝ] RelativeNumericalCurveClasses sX f) : Continuous g :=
  continuous_iInf_rng.2 fun M => continuous_iInf_rng.2 fun _ => continuous_induced_rng.2 <|
    LinearMap.continuous_of_finiteDimensional ((RelativeNumericalCurveClasses.degree sX f M).comp g)

end Pairing

/-! ### Convex geometry in `N₁(X/Y)` -/

/-- A linear form is determined by its values on the normalized vectors `‖e z‖⁻¹ • e z`. -/
private theorem apply_eq_norm_mul_apply_symm_smul {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : V ≃ₗ[ℝ] E) (χ : V →ₗ[ℝ] ℝ) (z : V) :
    χ z = ‖e z‖ * χ (e.symm (‖e z‖⁻¹ • e z)) := by
  rcases eq_or_ne (e z) 0 with h0 | h0
  · obtain rfl : z = 0 := by simpa using h0
    simp
  rw [map_smul, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]

/-- **A positive form dominates every form on a closed cone.** In a finite-dimensional real vector
space whose topology makes the linear maps from `ℝⁿ` continuous, if `φ` is positive on the
nonzero vectors of a closed cone `K`, then every linear form `ψ` satisfies `ψ ≤ m φ` on `K` for
some positive integer `m`. -/
private theorem exists_nat_le_mul_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : Set V}
    (hK : IsClosed K) (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (φ ψ : V →ₗ[ℝ] ℝ)
    (hφ : ∀ z ∈ K, z ≠ 0 → 0 < φ z) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ K, ψ z ≤ m * φ z := by
  let e := (Module.finBasis ℝ V).equivFun
  set K' : Set (Fin (Module.finrank ℝ V) → ℝ) := e.symm ⁻¹' K
  let φ' := φ.comp e.symm.toLinearMap
  let ψ' := ψ.comp e.symm.toLinearMap
  have hunit : ∀ z ∈ K, z ≠ 0 → ‖e z‖⁻¹ • e z ∈ K' ∩ Metric.sphere 0 1 := by
    intro z hz hz0
    have hez : e z ≠ 0 := by simpa using hz0
    refine ⟨?_, by simp [norm_smul, norm_ne_zero_iff.2 hez]⟩
    rw [Set.mem_preimage, map_smul, LinearEquiv.symm_apply_apply]
    exact hcone z hz _ (inv_pos.2 (norm_pos_iff.2 hez))
  by_cases hS : (K' ∩ Metric.sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).Nonempty
  swap
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact absurd ⟨_, hunit z hz hz0⟩ hS
  obtain ⟨w0, hw0, hmin⟩ :=
    ((isCompact_sphere (0 : Fin (Module.finrank ℝ V) → ℝ) 1).inter_left
      (hK.preimage (hcont e.symm.toLinearMap))).exists_isMinOn hS
      (LinearMap.continuous_of_finiteDimensional φ').continuousOn
  have hw00 : e.symm w0 ≠ 0 := by
    intro h
    obtain rfl : w0 = 0 := by simpa using h
    simp at hw0
  have hc : 0 < φ' w0 := hφ _ hw0.1 hw00
  set C := ‖LinearMap.toContinuousLinearMap ψ'‖
  obtain ⟨m, hm⟩ := exists_nat_gt (C / φ' w0)
  refine ⟨m + 1, by omega, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  have hu := hunit z hz hz0
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
  have := mul_le_mul_of_nonneg_left h4 (norm_nonneg (e z))
  simp only [ψ', φ', LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  linarith

/-- Under the hypotheses of `exists_nat_le_mul_of_pos`, every linear form `ψ` satisfies
`|ψ| ≤ m φ` on `K` for some natural number `m`. -/
private theorem exists_nat_abs_le_mul_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : Set V}
    (hK : IsClosed K) (hcone : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (φ ψ : V →ₗ[ℝ] ℝ)
    (hφ : ∀ z ∈ K, z ≠ 0 → 0 < φ z) :
    ∃ m : ℕ, ∀ z ∈ K, |ψ z| ≤ m * φ z := by
  have hφ0 : ∀ z ∈ K, 0 ≤ φ z := fun z hz => by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · exact (hφ z hz hz0).le
  obtain ⟨m₁, -, h₁⟩ := exists_nat_le_mul_of_pos hcont hK hcone φ ψ hφ
  obtain ⟨m₂, -, h₂⟩ := exists_nat_le_mul_of_pos hcont hK hcone φ (-ψ) hφ
  refine ⟨max m₁ m₂, fun z hz => abs_le.2 ⟨?_, ?_⟩⟩
  · have := h₂ z hz
    have hm : (m₂ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_right _ _
    simp only [LinearMap.neg_apply] at this
    nlinarith [hφ0 z hz]
  · have := h₁ z hz
    have hm : (m₁ : ℝ) ≤ (max m₁ m₂ : ℕ) := by exact_mod_cast le_max_left _ _
    nlinarith [hφ0 z hz]

/-- A point outside a closed salient convex cone `K` of a finite-dimensional real vector space is
separated from `K` by a linear form positive on `K ∖ {0}`. The topology on `V` is only assumed to
make every linear map from a coordinate space continuous. -/
private theorem exists_dual_pos_and_neg_of_notMem {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V]
    (hcont : ∀ g : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V, Continuous g) {K : PointedCone ℝ V}
    (hK : IsClosed (K : Set V)) (hKs : ∀ z ∈ K, -z ∈ K → z = 0) {v : V} (hv : v ∉ K) :
    ∃ ℓ : Module.Dual ℝ V, (∀ z ∈ K, z ≠ 0 → 0 < ℓ z) ∧ ℓ v < 0 := by
  let e := (Module.finBasis ℝ V).equivFun
  set K' : Set (Fin (Module.finrank ℝ V) → ℝ) := e.symm ⁻¹' K
  have hK'cl : IsClosed K' := hK.preimage (hcont e.symm.toLinearMap)
  have hK'c : Convex ℝ K' := (K.convex).linear_preimage e.symm.toLinearMap
  have hK'cone : MMP.Mori.IsCone ℝ K' :=
    MMP.Positivity.isCone_preimage (MMP.Mori.isCone_coe K) e.symm.toLinearMap
  have hmem : ∀ z, e z ∈ K' ↔ z ∈ K := fun z => by simp [K']
  have hv' : e v ∉ K' := by rwa [hmem]
  obtain ⟨φ, u, hφv, hφK⟩ := geometric_hahn_banach_point_closed hK'c hK'cl hv'
  have hu : u < 0 := by simpa using hφK 0 hK'cone.1
  have hφK' : ∀ b ∈ K', 0 ≤ φ b := by
    intro b hb
    by_contra! hneg
    have hc : 0 < u / φ b := div_pos_of_neg_of_neg hu hneg
    have := hφK _ (hK'cone.2 b hb _ hc)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hneg.ne] at this
    exact lt_irrefl _ this
  obtain ⟨G, hG⟩ := MMP.Positivity.exists_dual_pos_of_salient_of_normed hK'cone hK'c hK'cl
    fun z hz hnz => by
      have h := hKs _ hz (by simpa [K'] using hnz)
      simpa using congrArg e h
  set δ := -φ (e v) / (2 * (|G (e v)| + 1))
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  refine ⟨(φ.toLinearMap + δ • G.toLinearMap) ∘ₗ e.toLinearMap, fun z hz hz0 => ?_, ?_⟩ <;>
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, smul_eq_mul]
  · have hez : e z ∈ K' := (hmem z).2 hz
    have hez0 : e z ≠ 0 := by simpa using hz0
    nlinarith [hφK' _ hez, hG _ hez hez0]
  · have h1 : δ * G (e v) ≤ δ * |G (e v)| := mul_le_mul_of_nonneg_left (le_abs_self _) hδ.le
    have h2 : δ * |G (e v)| ≤ -φ (e v) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [abs_nonneg (G (e v))]
    linarith

/-! ### The natural map `ι : N₁(X/Y) → N₁(X)` -/

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
private theorem numericalCurveClasses_degree_eq_of_iso {L L' : X.Modules}
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
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [show a • x = (a : ℝ) • x from rfl, map_smul]
    exact (coneOfCurves sX).smul_mem a.2 hx

private theorem relativeToAbsolute_mem_closedConeOfCurves {z : RelativeNumericalCurveClasses sX f}
    (hz : z ∈ relativeClosedConeOfCurves sX f) :
    relativeToAbsolute sX f z ∈ closedConeOfCurves sX :=
  closure_mono (Set.image_subset_iff.2 fun _ hw => relativeToAbsolute_mem_coneOfCurves hw)
    (image_closure_subset_closure_image continuous_relativeToAbsolute ⟨z, hz, rfl⟩)

end Natural

/-! ### Approximation by Cartier divisors -/

/-- On an integral `X`, the forms `z ↦ (z · E)` for Cartier divisors `E` span the dual of
`N₁(X/Y)`. -/
private theorem span_range_intersectionNumber_ofCartier {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y} [IsIntegral X]
    [FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f)] :
    Submodule.span ℝ (Set.range fun E : X.CartierDivisor =>
      (RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) :
        Module.Dual ℝ (RelativeNumericalCurveClasses sX f))) = ⊤ := by
  set W := Submodule.span ℝ (Set.range fun E : X.CartierDivisor =>
    (RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) :
      Module.Dual ℝ (RelativeNumericalCurveClasses sX f)))
  have h0 : W.dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hz0
    obtain ⟨E, hE⟩ := exists_pairing_ne_zero hz0
    exact hE ((Submodule.mem_dualCoannihilator _).1 hz _ (Submodule.subset_span ⟨E, rfl⟩))
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), h0, Submodule.dualAnnihilator_bot]

/-- A real linear form on `N₁(X/Y)` positive on `NE̅(X/Y) ∖ {0}` and negative at `v` can be
replaced by a Cartier divisor with the same two properties. -/
private theorem exists_cartierDivisor_pos_neg {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y} [IsIntegral X]
    [FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f)]
    {ℓ : Module.Dual ℝ (RelativeNumericalCurveClasses sX f)}
    (hℓ : ∀ z ∈ relativeClosedConeOfCurves sX f, z ≠ 0 → 0 < ℓ z)
    {v : RelativeNumericalCurveClasses sX f} (hv : ℓ v < 0) :
    ∃ H : X.CartierDivisor, (∀ z ∈ relativeClosedConeOfCurves sX f, z ≠ 0 →
      0 < pairing f z H) ∧ pairing f v H < 0 := by
  classical
  set K := relativeClosedConeOfCurves sX f
  let φ : X.CartierDivisor → Module.Dual ℝ (RelativeNumericalCurveClasses sX f) := fun E =>
    RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E)
  have hφ : ∀ z E, φ E z = pairing f z E := fun _ _ => rfl
  have hspan : Submodule.span ℝ (Set.range φ) = ⊤ := span_range_intersectionNumber_ofCartier
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (hspan ▸ Submodule.mem_top : ℓ ∈ Submodule.span ℝ (Set.range φ))
  have hℓz : ∀ z, ℓ z = ∑ E ∈ c.support, c E * φ E z := by
    intro z
    rw [← hc, Finsupp.sum, LinearMap.sum_apply]
    simp
  have hb : ∀ E, ∃ m : ℕ, ∀ z ∈ K, |φ E z| ≤ m * ℓ z := fun E =>
    exists_nat_abs_le_mul_of_pos (continuous_linearMap sX f) isClosed_closure
      (fun z hz t ht => (relativeClosedConeOfCurves sX f).smul_mem ht.le hz) ℓ (φ E) hℓ
  choose m hm using hb
  set R : ℝ := ∑ E ∈ c.support, (m E : ℝ)
  set Sv : ℝ := ∑ E ∈ c.support, |φ E v|
  obtain ⟨N, hN⟩ := exists_nat_gt (max R (Sv / -ℓ v))
  have hNR : R < N := (le_max_left _ _).trans_lt hN
  have hNv : Sv < N * -ℓ v := (div_lt_iff₀ (by linarith)).1 ((le_max_right _ _).trans_lt hN)
  refine ⟨∑ E ∈ c.support, ⌊(N : ℝ) * c E⌋ • E, ?_⟩
  have herr : ∀ z, |pairing f z (∑ E ∈ c.support, ⌊(N : ℝ) * c E⌋ • E) - N * ℓ z| ≤
      ∑ E ∈ c.support, |φ E z| := by
    intro z
    have heq : pairing f z (∑ E ∈ c.support, ⌊(N : ℝ) * c E⌋ • E) - N * ℓ z =
        ∑ E ∈ c.support, ((⌊(N : ℝ) * c E⌋ : ℝ) - N * c E) * φ E z := by
      rw [map_sum, hℓz, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hφ]
      ring
    rw [heq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E _ => ?_)
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨?_, ?_⟩)
    · linarith [Int.lt_floor_add_one ((N : ℝ) * c E)]
    · linarith [Int.floor_le ((N : ℝ) * c E)]
  refine ⟨fun z hz hz0 => ?_, ?_⟩
  · have h2 : ∑ E ∈ c.support, |φ E z| ≤ R * ℓ z := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun E _ => hm E z hz
    nlinarith [hℓ z hz hz0, (abs_le.1 (herr z)).1]
  · linarith [(abs_le.1 (herr v)).2]

/-! ### The main theorem -/

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

/-- **An `f`-ample divisor is positive on `NE̅(X) ∩ ι(N₁(X/Y)) ∖ {0}`.** If `H` is `f`-ample and
`ι v ∈ NE̅(X)` is nonzero, then `(H · v) > 0`. -/
private theorem pairing_pos_of_isRelativelyAmple {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) {H : X.CartierDivisor}
    (hH : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf H))
    {v : RelativeNumericalCurveClasses sX f}
    (hv : relativeToAbsolute sX f v ∈ closedConeOfCurves sX)
    (hv0 : relativeToAbsolute sX f v ≠ 0) : 0 < pairing f v H := by
  haveI : IsIntegral X := hX.toIsVariety.toIsIntegral
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  obtain ⟨⟨LY, _, hLYrel, hLYA⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple hY.isProjective.isProjective
  obtain ⟨M, ⟨eM⟩⟩ := hLYA inferInstance
  have hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf M) :=
    (isAmple_congr _ _ eM).mpr
      (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY LY hLYrel)
  obtain ⟨B, ⟨eB⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))
  obtain ⟨ν, hν⟩ := (MMP.Foundations.isAmple_add_zsmul_pullback k hX hY hf hM hH
    ⟨eB.symm⟩).exists
  have hpos : 0 < pairing f v (H + ν • B) := by
    obtain ⟨Z, hZ⟩ := OneCycle.numericalClass_surjective sX (relativeToAbsolute sX f v)
    have := closedConeOfCurves_diff_zero_subset_posHalfspace sX (H + ν • B)
      ((isAmple_congr _ _ (Iso.refl (MMP.CartierDivisor.sheaf (H + ν • B))).symm).mpr hν)
      ⟨hv, hv0⟩ Z hZ
    rwa [pairing_apply, ← intersectionNumber_relativeToAbsolute, ← hZ,
      NumericalCurveClasses.intersectionNumber_numericalClass]
  have hB : pairing f v B = 0 := by
    rw [pairing_apply, ← intersectionNumber_relativeToAbsolute,
      NumericalCurveClasses.intersectionNumber_ofCartier,
      numericalCurveClasses_degree_eq_of_iso eB.symm,
      ← NumericalCurveClasses.degree_pushforward f hf,
      LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward f hf ⟨v, rfl⟩), map_zero]
  rwa [map_add, map_zsmul, hB, smul_zero, add_zero] at hpos

/-- For a morphism `f : X ⟶ Y` of projective varieties over an algebraically closed field of
characteristic zero, the natural map `ι = relativeToAbsolute sX f : N₁(X/Y) → N₁(X)` carries the
relative closed cone of curves onto the intersection of the closed cone of curves of `X` with the
image of `ι`. -/
@[mmp "lem_km3b_relative_cone_equals_intersection"]
public theorem image_relativeClosedConeOfCurves_eq_inter_range
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsProjectiveVariety k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    relativeToAbsolute sX f '' (relativeClosedConeOfCurves sX f : Set _) =
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩
        Set.range (relativeToAbsolute sX f) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨relativeToAbsolute_mem_closedConeOfCurves hz, z, rfl⟩
  rintro _ ⟨hξ, v, rfl⟩
  by_contra hv'
  have hv : v ∉ relativeClosedConeOfCurves sX f := fun h => hv' ⟨v, h, rfl⟩
  have hX : MMP.Mori.IsProjectiveVariety k sX := ‹_›
  have hY : MMP.Mori.IsProjectiveVariety k sY := ‹_›
  haveI : IsIntegral X := hX.toIsVariety.toIsIntegral
  haveI : MMP.Mori.IsVariety k sX := hX.toIsVariety
  haveI : MMP.Mori.IsVariety k sY := hY.toIsVariety
  haveI := MMP.Mori.finiteDimensional_numericalCurveClasses sX
  have hinj : Function.Injective (relativeToAbsolute sX f) :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX f).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX f)
  haveI : FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f) :=
    FiniteDimensional.of_injective _ hinj
  obtain ⟨ℓ, hℓK, hℓv⟩ := exists_dual_pos_and_neg_of_notMem (continuous_linearMap sX f)
    (K := relativeClosedConeOfCurves sX f) isClosed_closure (fun z hz hnz => hinj <| by
      rw [map_zero, ← Submodule.mem_bot ℝ, ← lineal_closedConeOfCurves_eq_bot]
      refine PointedCone.mem_lineal.2 ⟨relativeToAbsolute_mem_closedConeOfCurves hz, ?_⟩
      simpa using relativeToAbsolute_mem_closedConeOfCurves hnz) hv
  obtain ⟨H, hHK, hHv⟩ := exists_cartierDivisor_pos_neg hℓK hℓv
  have hHamp : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf H) :=
    (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
      (isProjective_of_comp_eq hX hY hf) hf H).mpr hHK
  exact hHv.not_gt (pairing_pos_of_isRelativelyAmple hX hY hf hHamp hξ fun h =>
    hv (hinj (h.trans (map_zero _).symm) ▸ zero_mem _))

end MMP.Mori

end
