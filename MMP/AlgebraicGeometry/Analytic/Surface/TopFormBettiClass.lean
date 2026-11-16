module
public import MMP.AlgebraicGeometry.Analytic.ProjectiveSingularSheafComparison
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.Analysis.Complex.StratifiedFlows
import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra

/-!
# The Betti class of a holomorphic two-form on a surface

Let `Z` be a smooth projective complex surface. A regular two-form `ω ∈ H⁰(Z, Ω²_{Z/ℂ})` is a
holomorphic top form on the compact complex surface `Z^an`, hence closed, and the holomorphic
de Rham resolution of the constant sheaf `ℂ_{Z^an}` gives it a class in `H²(Z^an, ℂ)`. This class
map is `ℂ`-linear, compatible with pull-back along morphisms of surfaces over `ℂ`, and injective:
if the class of `ω` vanished, `ω = dα` for a smooth one-form `α`, and Stokes' theorem would give
`∫_{Z^an} ω ∧ ω̄ = ∫ d(α ∧ ω̄) = 0`, whereas `ω ∧ ω̄` is a nonnegative multiple of the volume form,
positive where `ω ≠ 0`.

## Main definitions

* `MMP.Fourfold.topFormBettiClass`: the de Rham class map
  `H⁰(Z, Ω²_{Z/ℂ}) → H²(Z^an, ℂ_{Z^an})`.

## Main results

* `MMP.Fourfold.topFormBettiClass_injective_and_pullback`: for a smooth projective complex
  surface the de Rham class map is injective and `ℂ`-linear, and it commutes with pull-back
  along morphisms of surfaces over `ℂ`.
* `MMP.Fourfold.exists_injective_topFormBettiClass`: the same in singular cohomology
  `H²(Z^an; ℂ)`, through a comparison with constant-sheaf cohomology natural for pull-back.

## Implementation notes

* `H⁰(Z, Ω²_{Z/ℂ})` is the module of global sections of the sheaf
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms sZ 2` of relative differential
  two-forms; it is a module over `Γ(Z, 𝒪_Z)`, and `ℂ` acts through `sZ`. The pull-back of a form
  along `g : Z ⟶ Z'` over `ℂ` is the unit `Ω² ⟶ g_* g^* Ω²` on global sections followed by the
  canonical map `g^* Ω²_{Z'/ℂ} ⟶ Ω²_{Z/ℂ}`
  (`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`).
* `H²(Z^an, ℂ)` is singular cohomology `MMP.relativeSingularCohomology` of the
  complex realization `MMP.Analytic.ComplexPoints.analyticSpace sZ` with coefficients in `ℂ`,
  pulled back along `MMP.Analytic.ComplexPoints.analyticMap`; it agrees with the cohomology of
  the constant sheaf `ℂ_{Z^an}` `ℂ`-linearly and naturally in `Z`
  (`MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology_ring`).
* A smooth projective complex surface is a scheme `Z` with `sZ : Z ⟶ Spec ℂ` projective and
  smooth of relative dimension `2`; connectedness is not required.
* The class is built on the sheaf side. With `𝒜ᵏ` the sheaf of smooth complex `k`-forms on the
  real manifold `Z^an` and `𝒵ᵏ ⊆ 𝒜ᵏ` the closed ones, the Poincaré lemma (proved here by the
  radial homotopy operator) makes `0 → ℂ → 𝒜⁰ → 𝒵¹ → 0` and `0 → 𝒵¹ → 𝒜¹ → 𝒵² → 0` exact, and
  the class of `ω` is the image of the closed form `ω^an ∈ Γ(Z^an, 𝒵²)` under the two connecting
  maps. Since `𝒜⁰` is fine (partitions of unity), `H¹(Z^an, 𝒜⁰) = 0`, so a vanishing class makes
  `ω^an = dα` globally; Stokes' theorem is then checked chart by chart against a partition of
  unity, in Wirtinger coordinates.
* The file has four parts: smooth forms on manifolds and their sheaves (the Poincaré lemma,
  exactness, fineness, pull-back); the analytic form `ω^an` of an algebraic two-form, read in
  étale coordinates; Stokes' theorem and the vanishing of exact holomorphic two-forms; and the
  class, its linearity and its naturality.

## References

* [P. Griffiths, J. Harris, *Principles of algebraic geometry*], Ch. 0 §7.
-/

open CategoryTheory AlgebraicGeometry Opposite MMP.Analytic.ComplexPoints MMP
open Abelian

namespace MMP.Fourfold

/-! ### Smooth differential forms and the Poincaré lemma -/

section Poincare

open Set Filter ContinuousAlternatingMap CategoryTheory Opposite MeasureTheory
open scoped ContDiff Manifold Topology

universe u

section Radial

private theorem removeNth_succ_cons {α : Type*} {n : ℕ} (x : α) (v : Fin (n+1) → α)
    (i : Fin (n+1)) :
    Fin.removeNth i.succ (Fin.cons x v : Fin (n+2) → α) = Fin.cons x (Fin.removeNth i v) := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

private theorem curryLeft_alternatizeUncurryFin_add {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} (L : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] F)
    (x : E) :
    (alternatizeUncurryFin L).curryLeft x +
      alternatizeUncurryFin
        (((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp L).flip x) =
      L x := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, curryLeft_apply_apply,
    alternatizeUncurryFin_apply, alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have h : ∀ i : Fin (k + 1), Fin.removeNth i.succ (Matrix.vecCons x v) =
      Matrix.vecCons x (Fin.removeNth i v) := fun i ↦ removeNth_succ_cons x v i
  simp only [h, Fin.removeNth_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero,
    pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul]
  simp [Matrix.tail_cons, curryLeft_apply_apply]

private theorem hasFDerivAt_intervalIntegral_of_contDiff {H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : H → ℝ → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) (a b : ℝ) (x₀ : H) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t)
      (∫ t in a..b, (fderiv ℝ (Function.uncurry F) (x₀, t)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) x₀ := by
  set F' : H → ℝ → H →L[ℝ] E := fun x t ↦
    (fderiv ℝ (Function.uncurry F) (x, t)).comp (ContinuousLinearMap.inl ℝ H ℝ) with hF'
  have hcF : Continuous (Function.uncurry F) := hF.continuous
  have hcF' : Continuous (Function.uncurry F') := by
    have := hF.continuous_fderiv one_ne_zero
    exact (ContinuousLinearMap.compL ℝ H (H × ℝ) E |>.flip (ContinuousLinearMap.inl ℝ H ℝ)
      |>.continuous).comp this
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hcF'.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (s := Metric.closedBall x₀ 1) (bound := fun _ ↦ C) (F' := F')
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun x ↦
      (hcF.comp (Continuous.prodMk_right x)).aestronglyMeasurable
  · exact (hcF.comp (Continuous.prodMk_right x₀)).intervalIntegrable _ _
  · exact (hcF'.comp (Continuous.prodMk_right x₀)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx ↦ hC (x, t) ⟨hx, ?_⟩
    exact uIoc_subset_uIcc ht
  · refine Filter.Eventually.of_forall fun t _ x _ ↦ ?_
    have hd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x, t)) (x, t) :=
      (hF.differentiable one_ne_zero (x, t)).hasFDerivAt
    exact hd.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

/-- The same, with the partial derivative given explicitly. -/
private theorem hasFDerivAt_intervalIntegral_of_contDiff' {H E : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : H → ℝ → E} (hF : ContDiff ℝ 1 (Function.uncurry F)) {F' : H → ℝ → H →L[ℝ] E}
    (hF' : ∀ x t, HasFDerivAt (fun y ↦ F y t) (F' x t) x) (a b : ℝ) (x₀ : H) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  have h := hasFDerivAt_intervalIntegral_of_contDiff hF a b x₀
  have he : ∀ t, (fderiv ℝ (Function.uncurry F) (x₀, t)).comp
      (ContinuousLinearMap.inl ℝ H ℝ) = F' x₀ t := fun t ↦ by
    have hd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x₀, t)) (x₀, t) :=
      (hF.differentiable one_ne_zero (x₀, t)).hasFDerivAt
    have h2 := hd.comp x₀ (hasFDerivAt_prodMk_left (𝕜 := ℝ) x₀ t)
    exact h2.unique (hF' x₀ t :)
  simp_rw [he] at h
  exact h

private theorem contDiff_intervalIntegral {H : Type u} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] (n : ℕ) : ∀ {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : H → ℝ → E}, ContDiff ℝ n (Function.uncurry F) → ∀ a b : ℝ,
    ContDiff ℝ n (fun x ↦ ∫ t in a..b, F x t) := by
  induction n with
  | zero =>
    intro E _ _ F hF a b
    simp only [Nat.cast_zero, contDiff_zero] at hF ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF a b
  | succ n ih =>
    intro E _ _ F hF a b
    have hF1 : ContDiff ℝ 1 (Function.uncurry F) :=
      hF.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hfd : fderiv ℝ (fun x ↦ ∫ t in a..b, F x t) = fun x ↦ ∫ t in a..b,
        (fderiv ℝ (Function.uncurry F) (x, t)).comp (ContinuousLinearMap.inl ℝ H ℝ) := by
      funext x; exact (hasFDerivAt_intervalIntegral_of_contDiff hF1 a b x).fderiv
    have hF2 : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (Function.uncurry F) := by exact_mod_cast hF
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hasFDerivAt_intervalIntegral_of_contDiff hF1 a b x).differentiableAt,
      by simp, ?_⟩
    rw [hfd]
    apply ih (F := fun x t ↦ (fderiv ℝ (Function.uncurry F) (x, t)).comp
      (ContinuousLinearMap.inl ℝ H ℝ))
    have h1 : ContDiff ℝ n (fderiv ℝ (Function.uncurry F)) :=
      (contDiff_succ_iff_fderiv.1 hF2).2.2
    exact ((ContinuousLinearMap.compL ℝ H (H × ℝ) E).flip
      (ContinuousLinearMap.inl ℝ H ℝ)).contDiff.comp h1

private theorem contDiff_infty_intervalIntegral {H E : Type u} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : H → ℝ → E} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in a..b, F x t) :=
  contDiff_infty.2 fun n ↦ contDiff_intervalIntegral n (hF.of_le (by exact_mod_cast le_top)) a b

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The radial homotopy operator `(H β)(x) = ∫₀¹ tᵏ ι_x β(t x) dt` on `(k+1)`-forms. -/
private noncomputable def radialHomotopy (k : ℕ) (β : E → E [⋀^Fin (k + 1)]→L[ℝ] F) (x : E) :
    E [⋀^Fin k]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, t ^ k • (β (t • x)).curryLeft x

/-- The partial derivative of the integrand. -/
private theorem hasFDerivAt_radialIntegrand {k : ℕ} {β : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hβ : Differentiable ℝ β) (x : E) (t : ℝ) :
    HasFDerivAt (fun y ↦ t ^ k • (β (t • y)).curryLeft y)
      (t ^ k • ((β (t • x)).curryLeft + t •
        ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
          (fderiv ℝ β (t • x))).flip x)) x := by

  have hc : HasFDerivAt (fun y ↦
      (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap (β (t • y)))
      ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
        ((fderiv ℝ β (t • x)).comp (t • ContinuousLinearMap.id ℝ E))) x := by
    refine (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.hasFDerivAt.comp
        x ?_
    exact (hβ (t • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have h := (hc.clm_apply (hasFDerivAt_id x)).const_smul (t ^ k)
  have h' : HasFDerivAt (fun y ↦ t ^ k • (β (t • y)).curryLeft y) _ x := h
  refine h'.congr_fderiv ?_
  congr 1
  ext w v
  simp [curryLeft_apply_apply, add_comm]

private theorem extDeriv_radialHomotopy_add {k : ℕ} {β : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hβ : ContDiff ℝ 1 β) (x : E) :
    extDeriv (radialHomotopy k β) x + radialHomotopy (k + 1) (extDeriv β) x = β x := by
  set cL := (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap with hcL
  set D : ℝ → E →L[ℝ] E [⋀^Fin k]→L[ℝ] F := fun t ↦
    t ^ k • ((β (t • x)).curryLeft + t • (cL.comp (fderiv ℝ β (t • x))).flip x) with hDdef
  have hβd : Differentiable ℝ β := hβ.differentiable one_ne_zero
  have hβc : Continuous β := hβ.continuous
  have hβ' : Continuous (fderiv ℝ β) := hβ.continuous_fderiv one_ne_zero
  have hg : ContDiff ℝ 1 (Function.uncurry fun y (t : ℝ) ↦ t ^ k • (β (t • y)).curryLeft y) := by
    have h1 : ContDiff ℝ 1 (fun p : E × ℝ ↦ β (p.2 • p.1)) :=
      hβ.comp (contDiff_snd.smul contDiff_fst)
    have h2 : ContDiff ℝ 1 (fun p : E × ℝ ↦ cL (β (p.2 • p.1))) := cL.contDiff.comp h1
    exact (contDiff_snd.pow k).smul (h2.clm_apply contDiff_fst)
  have hD : HasFDerivAt (radialHomotopy k β) (∫ t in (0 : ℝ)..1, D t) x :=
    hasFDerivAt_intervalIntegral_of_contDiff' hg
      (fun y t ↦ hasFDerivAt_radialIntegrand hβd y t) 0 1 x
  have hDc : Continuous D := by
    refine (continuous_pow k).smul ?_
    refine ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).continuous.comp
      (hβc.comp (continuous_id.smul continuous_const))).add (continuous_id.smul ?_)
    have h3 : Continuous fun t : ℝ ↦ cL.comp (fderiv ℝ β (t • x)) :=
      ((ContinuousLinearMap.compL ℝ E _ _) cL).continuous.comp
        (hβ'.comp (continuous_id.smul continuous_const))
    exact (ContinuousLinearMap.apply ℝ _ x).continuous.comp
      ((ContinuousLinearMap.flipₗᵢ ℝ E E (E [⋀^Fin k]→L[ℝ] F)).continuous.comp h3)
  have h1 : extDeriv (radialHomotopy k β) x =
      ∫ t in (0 : ℝ)..1, alternatizeUncurryFin (D t) := by
    rw [extDeriv, hD.fderiv, ← alternatizeUncurryFinCLM_apply]
    rw [← (alternatizeUncurryFinCLM ℝ E F).intervalIntegral_comp_comm
      (hDc.intervalIntegrable 0 1)]
    simp [alternatizeUncurryFinCLM_apply]
  have h2 : radialHomotopy (k + 1) (extDeriv β) x = ∫ t in (0 : ℝ)..1,
      t ^ (k + 1) • (alternatizeUncurryFin (fderiv ℝ β (t • x))).curryLeft x := rfl
  have hpt : ∀ t : ℝ, alternatizeUncurryFin (D t) +
      t ^ (k + 1) • (alternatizeUncurryFin (fderiv ℝ β (t • x))).curryLeft x =
      ((k + 1 : ℝ) * t ^ k) • β (t • x) + t ^ (k + 1) • fderiv ℝ β (t • x) x := by
    intro t
    rw [← curryLeft_alternatizeUncurryFin_add (fderiv ℝ β (t • x)) x]
    simp only [hDdef, alternatizeUncurryFin_smul, alternatizeUncurryFin_add,
      alternatizeUncurryFin_curryLeft]
    rw [← hcL, ← Nat.cast_smul_eq_nsmul ℝ]
    push_cast
    module
  have hint1 : IntervalIntegrable (fun t ↦ alternatizeUncurryFin (D t)) volume 0 1 :=
    ((alternatizeUncurryFinCLM ℝ E F).continuous.comp hDc).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun t : ℝ ↦
      t ^ (k + 1) • (alternatizeUncurryFin (fderiv ℝ β (t • x))).curryLeft x) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    refine (continuous_pow (k + 1)).smul ?_
    exact (ContinuousLinearMap.apply ℝ _ x).continuous.comp
      ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k + 1)).continuous.comp
        ((alternatizeUncurryFinCLM ℝ E F).continuous.comp
          (hβ'.comp (continuous_id.smul continuous_const))))
  rw [h1, h2, ← intervalIntegral.integral_add hint1 hint2]
  simp_rw [hpt]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ s ^ (k + 1) • β (s • x))
      (((k + 1 : ℝ) * t ^ k) • β (t • x) + t ^ (k + 1) • fderiv ℝ β (t • x) x) t := by
    intro t _
    have hp : HasDerivAt (fun s : ℝ ↦ s ^ (k + 1)) ((k + 1 : ℕ) * t ^ k) t := by
      simpa using hasDerivAt_pow (k + 1) t
    have hb := (hβd (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h3 := hp.smul hb
    refine h3.congr_deriv ?_
    simp only [id, one_smul, Function.comp_apply]
    push_cast
    exact add_comm _ _
  have hcont : Continuous fun t : ℝ ↦
      ((k + 1 : ℝ) * t ^ k) • β (t • x) + t ^ (k + 1) • fderiv ℝ β (t • x) x := by
    refine ((continuous_const.mul (continuous_pow k)).smul
      (hβc.comp (continuous_id.smul continuous_const))).add
      ((continuous_pow (k + 1)).smul ?_)
    exact (ContinuousLinearMap.apply ℝ _ x).continuous.comp
      (hβ'.comp (continuous_id.smul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  simp

private theorem contDiff_radialHomotopy {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {k : ℕ} {β : E → E [⋀^Fin (k + 1)]→L[ℝ] F} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (radialHomotopy k β) := by
  have hg : ContDiff ℝ ∞ (Function.uncurry fun y (t : ℝ) ↦ t ^ k • (β (t • y)).curryLeft y) := by
    have h1 : ContDiff ℝ ∞ (fun p : E × ℝ ↦ β (p.2 • p.1)) :=
      hβ.comp (contDiff_snd.smul contDiff_fst)
    have h2 : ContDiff ℝ ∞ (fun p : E × ℝ ↦
        (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap
          (β (p.2 • p.1))) :=
      (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.contDiff.comp h1
    exact (contDiff_snd.pow k).smul (h2.clm_apply contDiff_fst)
  exact contDiff_infty_intervalIntegral hg 0 1

/-- **Poincaré lemma** on a set star-convex about `0`. -/
private theorem extDeriv_radialHomotopy_of_starConvex {k : ℕ} {β : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hβ : ContDiff ℝ 1 β) {s : Set E} (hs : StarConvex ℝ 0 s)
    (hd : ∀ y ∈ s, extDeriv β y = 0) {x : E} (hx : x ∈ s) :
    extDeriv (radialHomotopy k β) x = β x := by
  have h := extDeriv_radialHomotopy_add hβ x
  have h0 : radialHomotopy (k + 1) (extDeriv β) x = 0 := by
    unfold radialHomotopy
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0)]
    · simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hts : t • x ∈ s := by
        simpa using hs hx (sub_nonneg.2 ht.2) ht.1 (by ring)
      simp [hd _ hts]
  rwa [h0, add_zero] at h

end Radial

section AltSmooth

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiffOn_continuousAlternatingMap_of_apply {n : WithTop ℕ∞} {s : Set X} :
    ∀ {k : ℕ} {f : X → E [⋀^Fin k]→L[ℝ] F}, (∀ v, ContDiffOn ℝ n (fun x ↦ f x v) s) →
      ContDiffOn ℝ n f s
  | 0, f, h => by
    have : f = fun x ↦ constOfIsEmpty ℝ E (Fin 0) (f x ![]) := by
      funext x; ext v; simp [Subsingleton.elim v ![]]
    rw [this]
    exact (constOfIsEmptyLIE ℝ E F (Fin 0)).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (h ![])
  | k + 1, f, h => by
    have hc : ContDiffOn ℝ n (fun x ↦ (f x).curryLeft) s := by
      rw [contDiffOn_clm_apply]
      intro w
      refine contDiffOn_continuousAlternatingMap_of_apply fun u ↦ ?_
      simpa [curryLeft_apply_apply] using h (Matrix.vecCons w u)
    have : f = fun x ↦ ((k + 1 : ℝ)⁻¹) • alternatizeUncurryFinCLM ℝ E F (f x).curryLeft := by
      funext x
      rw [alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_curryLeft,
          ← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul]
      have : ((k + 1 : ℝ)⁻¹) * ((k + 1 : ℕ) : ℝ) = 1 := by
        push_cast; field_simp
      rw [this, one_smul]
    rw [this]
    exact ((alternatizeUncurryFinCLM ℝ E F).contDiff.comp_contDiffOn hc).const_smul _

private theorem contDiffOn_continuousAlternatingMap_apply {n : WithTop ℕ∞} {s : Set X} :
    ∀ {k : ℕ} {A : X → E [⋀^Fin k]→L[ℝ] F} {y : X → Fin k → E}, ContDiffOn ℝ n A s →
      (∀ i, ContDiffOn ℝ n (fun x ↦ y x i) s) → ContDiffOn ℝ n (fun x ↦ A x (y x)) s
  | 0, A, y, hA, _ => by
    have : (fun x ↦ A x (y x)) = fun x ↦ (constOfIsEmptyLIE ℝ E F (Fin 0)).symm (A x) := by
      funext x
      rw [eq_comm, LinearIsometryEquiv.symm_apply_eq]
      ext v
      simp [constOfIsEmptyLIE, Subsingleton.elim v (y x)]
      rfl
    rw [this]
    exact (constOfIsEmptyLIE ℝ E F (Fin 0)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hA
  | k + 1, A, y, hA, hy => by
    have h1 : ContDiffOn ℝ n (fun x ↦ (A x).curryLeft (y x 0)) s :=
      ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.contDiff
        |>.comp_contDiffOn hA).clm_apply (hy 0)
    have h2 := contDiffOn_continuousAlternatingMap_apply (y := fun x ↦ Fin.tail (y x)) h1
      (fun i ↦ hy i.succ)
    refine h2.congr fun x _ ↦ ?_
    simp only [curryLeft_apply_apply]
    congr 1
    exact (Fin.cons_self_tail (y x)).symm

private theorem contDiffOn_compCLM {n : WithTop ℕ∞}
    {s : Set X} {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A : X → E [⋀^Fin k]→L[ℝ] F} {L : X → G →L[ℝ] E} [FiniteDimensional ℝ G]
    (hA : ContDiffOn ℝ n A s) (hL : ContDiffOn ℝ n L s) :
    ContDiffOn ℝ n (fun x ↦ (A x).compContinuousLinearMap (L x)) s := by
  refine contDiffOn_continuousAlternatingMap_of_apply fun v ↦ ?_
  simp only [compContinuousLinearMap_apply]
  exact contDiffOn_continuousAlternatingMap_apply hA fun i ↦ hL.clm_apply contDiffOn_const

end AltSmooth

namespace Forms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The transition map `e' ∘ e⁻¹` between two charts. -/
private abbrev tr (e e' : OpenPartialHomeomorph M V) : OpenPartialHomeomorph V V := e.symm.trans e'

omit [IsManifold 𝓘(ℝ, V) ∞ M] in
private lemma tr_apply (e e' : OpenPartialHomeomorph M V) (v : V) : tr e e' v = e' (e.symm v) := rfl

private lemma contDiffOn_tr {e e' : OpenPartialHomeomorph M V} (he : e ∈ atlas V M)
    (he' : e' ∈ atlas V M) : ContDiffOn ℝ ∞ (tr e e') (tr e e').source := by
  have h := (contDiffGroupoid ∞ 𝓘(ℝ, V)).compatible he he'
  have h' := (mem_groupoid_of_pregroupoid.mp h).1
  simpa [contDiffPregroupoid] using h'

private lemma isOpen_tr_source (e e' : OpenPartialHomeomorph M V) : IsOpen (tr e e').source :=
  (tr e e').open_source

private lemma differentiableAt_tr {e e' : OpenPartialHomeomorph M V} (he : e ∈ atlas V M)
    (he' : e' ∈ atlas V M) {v : V} (hv : v ∈ (tr e e').source) :
    DifferentiableAt ℝ (tr e e') v :=
  ((contDiffOn_tr he he').contDiffAt ((isOpen_tr_source e e').mem_nhds hv)).differentiableAt
    (by simp)

/-- The local expression in the chart `e` of a form `β`, whose value at `x` is read in the
coordinates of `chartAt V x`. -/
private noncomputable def loc {k : ℕ} (e : OpenPartialHomeomorph M V) (β : M → V [⋀^Fin k]→L[ℝ] F)
    (v : V) : V [⋀^Fin k]→L[ℝ] F :=
  (β (e.symm v)).compContinuousLinearMap (fderiv ℝ (tr e (chartAt V (e.symm v))) v)

private lemma mem_tr_source_chartAt {e : OpenPartialHomeomorph M V} {v : V} (hv : v ∈ e.target) :
    v ∈ (tr e (chartAt V (e.symm v))).source := by
  simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff,
    mem_preimage]
  exact ⟨hv, mem_chart_source V _⟩

/-- **Change of chart** for local expressions. -/
private lemma loc_eventuallyEq {k : ℕ} {e e' : OpenPartialHomeomorph M V} (he : e ∈ atlas V M)
    (he' : e' ∈ atlas V M) (β : M → V [⋀^Fin k]→L[ℝ] F) {v : V} (hv : v ∈ (tr e e').source) :
    loc e β =ᶠ[𝓝 v] fun w ↦
      (loc e' β (tr e e' w)).compContinuousLinearMap (fderiv ℝ (tr e e') w) := by
  filter_upwards [(isOpen_tr_source e e').mem_nhds hv] with w hw
  have hw' : w ∈ e.target ∧ e.symm w ∈ e'.source := by
    simpa [tr] using hw
  set y := e.symm w with hy
  set c := chartAt V y
  have hyy : e'.symm (tr e e' w) = y := by
    rw [tr_apply]; exact e'.left_inv hw'.2
  have hcomp : tr e c =ᶠ[𝓝 w] (tr e' c) ∘ (tr e e') := by
    filter_upwards [(isOpen_tr_source e e').mem_nhds hw] with u hu
    have hu' : e.symm u ∈ e'.source := by simp [tr] at hu; exact hu.2
    simp [tr, e'.left_inv hu']
  have hTw : tr e e' w ∈ (tr e' c).source := by
    simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨e'.map_source hw'.2, ?_⟩
    rw [show e'.symm ((e.symm ≫ₕ e') w) = y from e'.left_inv hw'.2]
    exact mem_chart_source V y
  have hd1 : DifferentiableAt ℝ (tr e' c) (tr e e' w) :=
    differentiableAt_tr he' (chart_mem_atlas V y) hTw
  have hd2 : DifferentiableAt ℝ (tr e e') w := differentiableAt_tr he he' hw
  have hf : fderiv ℝ (tr e c) w = (fderiv ℝ (tr e' c) (tr e e' w)).comp (fderiv ℝ (tr e e') w) := by
    rw [hcomp.fderiv_eq]
    exact fderiv_comp w hd1 hd2
  simp only [loc]
  rw [hyy, ← hy, hf]
  ext u
  rfl

/-- `β` is smooth on `U`: its local expression in every atlas chart is smooth. -/
private def IsSmoothOn {k : ℕ} (U : Set M) (β : M → V [⋀^Fin k]→L[ℝ] F) : Prop :=
  ∀ e ∈ atlas V M, ContDiffOn ℝ ∞ (loc e β) (e.target ∩ e.symm ⁻¹' U)

/-- The exterior derivative of a form, computed in the preferred chart. -/
private noncomputable def d {k : ℕ} (β : M → V [⋀^Fin k]→L[ℝ] F) (x : M) :
    V [⋀^Fin (k + 1)]→L[ℝ] F :=
  extDeriv (loc (chartAt V x) β) (chartAt V x x)

private lemma two_le_infty : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact ENat.LEInfty.out

private lemma contDiffAt_tr {e e' : OpenPartialHomeomorph M V} (he : e ∈ atlas V M)
    (he' : e' ∈ atlas V M) {v : V} (hv : v ∈ (tr e e').source) :
    ContDiffAt ℝ ∞ (tr e e') v :=
  (contDiffOn_tr he he').contDiffAt ((isOpen_tr_source e e').mem_nhds hv)

private lemma mem_target_inter {U : Set M} {y : M} (hy : y ∈ U) :
    chartAt V y y ∈ (chartAt V y).target ∩ (chartAt V y).symm ⁻¹' U :=
  ⟨(chartAt V y).map_source (mem_chart_source V y), by
    simpa [(chartAt V y).left_inv (mem_chart_source V y)] using hy⟩

private lemma loc_d {k : ℕ} {U : Set M} (hU : IsOpen U) {β : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) {e : OpenPartialHomeomorph M V} (he : e ∈ atlas V M) {v : V}
    (hv : v ∈ e.target) (hvU : e.symm v ∈ U) :
    loc e (d β) v = extDeriv (loc e β) v := by
  set y := e.symm v with hy
  set c := chartAt V y with hc
  have hsrc := mem_tr_source_chartAt (e := e) hv
  rw [(loc_eventuallyEq he (chart_mem_atlas V y) β hsrc).extDeriv_eq]
  have hω : DifferentiableAt ℝ (loc c β) (tr e c v) := by
    have hm := mem_target_inter (V := V) hvU
    have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
    exact ((hβ c (chart_mem_atlas V y)).contDiffAt (hopen.mem_nhds hm)).differentiableAt
      (by simp)
  rw [extDeriv_pullback hω (contDiffAt_tr he (chart_mem_atlas V y) hsrc) two_le_infty]
  rfl

private lemma isOpen_target_inter (e : OpenPartialHomeomorph M V) {U : Set M} (hU : IsOpen U) :
    IsOpen (e.target ∩ e.symm ⁻¹' U) :=
  e.isOpen_inter_preimage_symm hU

private lemma isSmoothOn_d {k : ℕ} {U : Set M} (hU : IsOpen U) {β : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) : IsSmoothOn U (d β) := by
  intro e he
  have hS := isOpen_target_inter e hU
  have h1 : ContDiffOn ℝ ∞ (fun v ↦ extDeriv (loc e β) v) (e.target ∩ e.symm ⁻¹' U) := by
    have h2 : ContDiffOn ℝ ∞ (fun v ↦ fderiv ℝ (loc e β) v) (e.target ∩ e.symm ⁻¹' U) :=
      (hβ e he).fderiv_of_isOpen hS (by simp)
    exact (alternatizeUncurryFinCLM ℝ V F).contDiff.comp_contDiffOn h2
  exact h1.congr fun v hv ↦ loc_d hU hβ he hv.1 hv.2

private lemma d_d {k : ℕ} {U : Set M} (hU : IsOpen U) {β : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) {x : M} (hx : x ∈ U) : d (d β) x = 0 := by
  set c := chartAt V x
  have hS := isOpen_target_inter c hU
  have hm : c x ∈ c.target ∩ c.symm ⁻¹' U := mem_target_inter hx
  have heq : loc c (d β) =ᶠ[𝓝 (c x)] extDeriv (loc c β) := by
    filter_upwards [hS.mem_nhds hm] with v hv
    exact loc_d hU hβ (chart_mem_atlas V x) hv.1 hv.2
  change extDeriv (loc c (d β)) (c x) = 0
  rw [heq.extDeriv_eq]
  exact extDeriv_extDeriv_apply ((hβ c (chart_mem_atlas V x)).contDiffAt (hS.mem_nhds hm))
    two_le_infty

private lemma fderiv_tr_self {e : OpenPartialHomeomorph M V} {v : V} (hv : v ∈ e.target) :
    fderiv ℝ (tr e e) v = ContinuousLinearMap.id ℝ V := by
  have h : (tr e e : V → V) =ᶠ[𝓝 v] id := by
    filter_upwards [e.open_target.mem_nhds hv] with w hw
    simp [tr, e.right_inv hw]
  rw [h.fderiv_eq, fderiv_id]

private lemma loc_chartAt_self {k : ℕ} (β : M → V [⋀^Fin k]→L[ℝ] F) (x : M) :
    loc (chartAt V x) β (chartAt V x x) = β x := by
  have hx := (chartAt V x).left_inv (mem_chart_source V x)
  simp only [loc, hx]
  rw [fderiv_tr_self ((chartAt V x).map_source (mem_chart_source V x))]
  ext v; rfl

/-- Local expressions only see the form near the point. -/
private lemma loc_congr {k : ℕ} {e : OpenPartialHomeomorph M V} {β β' : M → V [⋀^Fin k]→L[ℝ] F}
    {v : V} (h : β (e.symm v) = β' (e.symm v)) : loc e β v = loc e β' v := by
  simp [loc, h]

private lemma d_congr {k : ℕ} {β β' : M → V [⋀^Fin k]→L[ℝ] F} {x : M} (h : β =ᶠ[𝓝 x] β') :
    d β x = d β' x := by
  set c := chartAt V x
  have h' : loc c β =ᶠ[𝓝 (c x)] loc c β' := by
    have hc : ContinuousAt c.symm (c x) :=
      c.continuousAt_symm (c.map_source (mem_chart_source V x))
    have h2 : β ∘ c.symm =ᶠ[𝓝 (c x)] β' ∘ c.symm := by
      have := hc.tendsto
      rw [c.left_inv (mem_chart_source V x)] at this
      exact this.eventually h
    filter_upwards [h2] with v hv
    exact loc_congr hv
  exact h'.extDeriv_eq

private lemma IsSmoothOn.mono {k : ℕ} {U U' : Set M} {β : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) (h : U' ⊆ U) : IsSmoothOn U' β := fun e he ↦
  (hβ e he).mono (inter_subset_inter_right _ (preimage_mono h))

private lemma IsSmoothOn.congr {k : ℕ} {U : Set M} {β β' : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) (h : EqOn β β' U) : IsSmoothOn U β' := fun e he ↦
  (hβ e he).congr fun v hv ↦ (loc_congr (h hv.2)).symm

private lemma isSmoothOn_of_locally {k : ℕ} {U : Set M} {β : M → V [⋀^Fin k]→L[ℝ] F}
    (h : ∀ x ∈ U, ∃ U' : Set M, IsOpen U' ∧ x ∈ U' ∧ IsSmoothOn U' β) : IsSmoothOn U β := by
  intro e he
  refine contDiffOn_of_locally_contDiffOn fun v hv ↦ ?_
  obtain ⟨U', hU', hxU', hβ'⟩ := h _ hv.2
  refine ⟨e.target ∩ e.symm ⁻¹' U', isOpen_target_inter e hU', ⟨hv.1, hxU'⟩, ?_⟩
  exact (hβ' e he).mono (by intro w hw; exact ⟨hw.1.1, hw.2.2⟩)

private lemma isSmoothOn_add {k : ℕ} {U : Set M} {β β' : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) (hβ' : IsSmoothOn U β') : IsSmoothOn U (β + β') := by
  intro e he
  refine ((hβ e he).add (hβ' e he)).congr fun v _ ↦ ?_
  ext u; simp [loc]

private lemma isSmoothOn_smul {k : ℕ} {U : Set M} {β : M → V [⋀^Fin k]→L[ℝ] F} (c : ℝ)
    (hβ : IsSmoothOn U β) : IsSmoothOn U (c • β) := by
  intro e he
  refine ((hβ e he).const_smul c).congr fun v _ ↦ ?_
  ext u; simp [loc]

private lemma isSmoothOn_zero {k : ℕ} (U : Set M) : IsSmoothOn U (0 : M → V [⋀^Fin k]→L[ℝ] F) := by
  intro e _
  refine (contDiffOn_const (c := (0 : V [⋀^Fin k]→L[ℝ] F))).congr fun v _ ↦ ?_
  ext u; simp [loc]

/-- The form on `M` with local expression `g` in the chart `c`. -/
private noncomputable def ofLoc {k : ℕ} (c : OpenPartialHomeomorph M V) (g : V → V [⋀^Fin k]→L[ℝ] F)
    (y : M) : V [⋀^Fin k]→L[ℝ] F :=
  (g (c y)).compContinuousLinearMap (fderiv ℝ (tr (chartAt V y) c) (chartAt V y y))

private lemma fderiv_tr_comp_tr {e e' : OpenPartialHomeomorph M V} (he : e ∈ atlas V M)
    (he' : e' ∈ atlas V M) {v : V} (hv : v ∈ (tr e e').source) :
    (fderiv ℝ (tr e' e) (tr e e' v)).comp (fderiv ℝ (tr e e') v) = ContinuousLinearMap.id ℝ V := by
  have hv' : v ∈ e.target ∧ e.symm v ∈ e'.source := by simpa [tr] using hv
  have hTv : tr e e' v ∈ (tr e' e).source := by
    simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    refine ⟨e'.map_source hv'.2, ?_⟩
    rw [show e'.symm ((e.symm ≫ₕ e') v) = e.symm v from e'.left_inv hv'.2]
    exact e.map_target hv'.1
  have hid : (tr e' e) ∘ (tr e e') =ᶠ[𝓝 v] id := by
    filter_upwards [(isOpen_tr_source e e').mem_nhds hv] with w hw
    have hw' : w ∈ e.target ∧ e.symm w ∈ e'.source := by simpa [tr] using hw
    simp [tr, e'.left_inv hw'.2, e.right_inv hw'.1]
  rw [← fderiv_comp v (differentiableAt_tr he' he hTv) (differentiableAt_tr he he' hv),
    hid.fderiv_eq, fderiv_id]

private lemma loc_ofLoc {k : ℕ} {c : OpenPartialHomeomorph M V} (hc : c ∈ atlas V M)
    (g : V → V [⋀^Fin k]→L[ℝ] F) {v : V} (hv : v ∈ c.target) :
    loc c (ofLoc c g) v = g v := by
  set y := c.symm v
  have hsrc := mem_tr_source_chartAt (e := c) hv
  have h := fderiv_tr_comp_tr hc (chart_mem_atlas V y) hsrc
  simp only [loc, ofLoc]
  rw [show c y = v from c.right_inv hv]
  rw [show chartAt V y y = tr c (chartAt V y) v from rfl]
  ext u
  simp only [compContinuousLinearMap_apply]
  congr 1
  funext i
  have := congrArg (fun L : V →L[ℝ] V ↦ L (u i)) h
  simpa using this

/-- A form built from a smooth local expression is smooth on the corresponding open. -/
private lemma isSmoothOn_ofLoc {k : ℕ} {c : OpenPartialHomeomorph M V} (hc : c ∈ atlas V M)
    {g : V → V [⋀^Fin k]→L[ℝ] F} {O : Set V} (hO : IsOpen O) (hOc : O ⊆ c.target)
    (hg : ContDiffOn ℝ ∞ g O) : IsSmoothOn (c.source ∩ c ⁻¹' O) (ofLoc c g) := by
  intro e he
  refine contDiffOn_of_locally_contDiffOn fun v hv ↦ ?_
  have hvsrc : v ∈ (tr e c).source := by
    simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨hv.1, hv.2.1⟩
  set S := (tr e c).source ∩ (tr e c) ⁻¹' O
  have hS : IsOpen S := (contDiffOn_tr he hc).continuousOn.isOpen_inter_preimage
    (isOpen_tr_source e c) hO
  refine ⟨S, hS, ⟨hvsrc, hv.2.2⟩, ?_⟩
  have h1 : ContDiffOn ℝ ∞ (fun w ↦ (g (tr e c w)).compContinuousLinearMap
      (fderiv ℝ (tr e c) w)) S := by
    have hgT : ContDiffOn ℝ ∞ (fun w ↦ g (tr e c w)) S :=
      hg.comp ((contDiffOn_tr he hc).mono inter_subset_left) (fun w hw ↦ hw.2)
    have hdT : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ (tr e c) w) S :=
      ((contDiffOn_tr he hc).fderiv_of_isOpen (isOpen_tr_source e c) (by simp)).mono
        inter_subset_left
    exact contDiffOn_compCLM hgT hdT
  refine (h1.mono inter_subset_right).congr fun w hw ↦ ?_
  have hm : w ∈ (tr e c).source := hw.2.1
  have hm' : e.symm w ∈ c.source := by simp [tr] at hm; exact hm.2
  have := (loc_eventuallyEq he hc (ofLoc c g) hm).eq_of_nhds
  rw [this, show (tr e c) w = c (e.symm w) from rfl, loc_ofLoc hc g (c.map_source hm')]

/-- A form is determined at `y` by its local expression in any atlas chart at `y`. -/
private lemma eq_of_loc_eq {k : ℕ} {c : OpenPartialHomeomorph M V} (hc : c ∈ atlas V M)
    {β β' : M → V [⋀^Fin k]→L[ℝ] F} {y : M} (hy : y ∈ c.source)
    (h : loc c β (c y) = loc c β' (c y)) : β y = β' y := by
  set cy := chartAt V y
  have hsrc : cy y ∈ (tr cy c).source := by
    simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨cy.map_source (mem_chart_source V y), by
      rw [cy.left_inv (mem_chart_source V y)]; exact hy⟩
  have hid := fderiv_tr_comp_tr (chart_mem_atlas V y) hc hsrc
  have hT : tr cy c (cy y) = c y := by simp [tr, cy.left_inv (mem_chart_source V y)]
  have hcy : c.symm (c y) = y := c.left_inv hy
  have key : ∀ γ : M → V [⋀^Fin k]→L[ℝ] F,
      (loc c γ (c y)).compContinuousLinearMap (fderiv ℝ (tr cy c) (cy y)) = γ y := by
    intro γ
    rw [← hT] at *
    ext u
    simp only [loc, compContinuousLinearMap_apply]
    rw [show c.symm (tr cy c (cy y)) = y by rw [hT, hcy]]
    congr 1
    funext i
    have := congrArg (fun L : V →L[ℝ] V ↦ L (u i)) hid
    simpa [hT] using this
  rw [← key β, ← key β', h]

private lemma extDeriv_comp_add_right {k : ℕ} (f : V → V [⋀^Fin k]→L[ℝ] F) (a u : V)
    (hf : DifferentiableAt ℝ f (u + a)) :
    extDeriv (fun w ↦ f (w + a)) u = extDeriv f (u + a) := by
  have h : extDeriv (fun w ↦ (f (w + a)).compContinuousLinearMap
      (fderiv ℝ (fun w : V ↦ w + a) w)) u =
      (extDeriv f (u + a)).compContinuousLinearMap (fderiv ℝ (fun w : V ↦ w + a) u) :=
    extDeriv_pullback hf (contDiff_id.add contDiff_const).contDiffAt two_le_infty
  have hd : ∀ w : V, fderiv ℝ (fun w : V ↦ w + a) w = ContinuousLinearMap.id ℝ V := fun w ↦ by
    simp
  simp only [hd] at h
  have e1 : ∀ {n : ℕ} (A : V [⋀^Fin n]→L[ℝ] F),
      A.compContinuousLinearMap (ContinuousLinearMap.id ℝ V) = A :=
    fun A ↦ by ext v; rfl
  simpa only [e1] using h

section LocalPoincare

variable {V F : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A function smooth on an open set and multiplied by a bump supported in it is smooth. -/
private lemma contDiff_bump_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {S : Set V}
    (hS : IsOpen S) {g : V → G} (hg : ContDiffOn ℝ ∞ g S) {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχS : tsupport χ ⊆ S) : ContDiff ℝ ∞ (fun v ↦ χ v • g v) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ S
  · exact (hχ.contDiffAt.smul (hg.contDiffAt (hS.mem_nhds hv)))
  · have hv' : v ∉ tsupport χ := fun h ↦ hv (hχS h)
    have h0 : (fun v ↦ χ v • g v) =ᶠ[𝓝 v] fun _ ↦ (0 : G) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hv'] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- **The Poincaré lemma on a manifold.** A closed smooth `(k+1)`-form is exact near every
point. -/
private theorem exists_local_primitive {k : ℕ} {U : Set M} (hU : IsOpen U)
    {β : M → V [⋀^Fin (k + 1)]→L[ℝ] F} (hβ : IsSmoothOn U β) (hdβ : ∀ x ∈ U, d β x = 0)
    {x : M} (hx : x ∈ U) :
    ∃ U' : Set M, ∃ η : M → V [⋀^Fin k]→L[ℝ] F, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧
      IsSmoothOn U' η ∧ ∀ y ∈ U', d η y = β y := by
  set c := chartAt V x with hcdef
  have hc : c ∈ atlas V M := chart_mem_atlas V x
  set S := c.target ∩ c.symm ⁻¹' U with hSdef
  have hS : IsOpen S := isOpen_target_inter c hU
  have hxS : c x ∈ S := mem_target_inter hx
  set b := loc c β
  have hb : ContDiffOn ℝ ∞ b S := hβ c hc
  have hdb : ∀ v ∈ S, extDeriv b v = 0 := by
    intro v hv
    rw [← loc_d hU hβ hc hv.1 hv.2]
    simp only [loc, hdβ _ hv.2]
    ext u
    simp
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS _ hxS
  let χ : ContDiffBump (c x) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχS : tsupport χ ⊆ S := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hrS
  set b₁ : V → V [⋀^Fin (k + 1)]→L[ℝ] F := fun v ↦ χ v • b v
  have hb₁ : ContDiff ℝ ∞ b₁ := contDiff_bump_smul hS hb χ.contDiff hχS
  have hb₁b : ∀ v ∈ Metric.ball (c x) (r / 4), b₁ =ᶠ[𝓝 v] b := by
    intro v hv
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
    simp [b₁, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)]
  set b₂ : V → V [⋀^Fin (k + 1)]→L[ℝ] F := fun u ↦ b₁ (u + c x)
  have hb₂ : ContDiff ℝ ∞ b₂ := hb₁.comp (contDiff_id.add contDiff_const)
  have hdb₂ : ∀ u ∈ Metric.ball (0 : V) (r / 4), extDeriv b₂ u = 0 := by
    intro u hu
    have hu' : u + c x ∈ Metric.ball (c x) (r / 4) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    rw [extDeriv_comp_add_right b₁ (c x) u (hb₁.differentiable (by simp) _),
      (hb₁b _ hu').extDeriv_eq]
    exact hdb _ (hrS (Metric.ball_subset_ball (by linarith) hu'))
  set η₀ := radialHomotopy k b₂
  have hη₀ : ContDiff ℝ ∞ η₀ := contDiff_radialHomotopy hb₂
  have hdη₀ : ∀ u ∈ Metric.ball (0 : V) (r / 4), extDeriv η₀ u = b₂ u := fun u hu ↦
    extDeriv_radialHomotopy_of_starConvex (hb₂.of_le (by exact_mod_cast le_top))
      ((convex_ball (0 : V) (r / 4)).starConvex (Metric.mem_ball_self (by positivity)))
      hdb₂ hu
  set η₁ : V → V [⋀^Fin k]→L[ℝ] F := fun v ↦ η₀ (v + -c x)
  have hη₁ : ContDiff ℝ ∞ η₁ := hη₀.comp (contDiff_id.add contDiff_const)
  have hdη₁ : ∀ v ∈ Metric.ball (c x) (r / 4), extDeriv η₁ v = b v := by
    intro v hv
    have hv' : v + -c x ∈ Metric.ball (0 : V) (r / 4) := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hv
    rw [extDeriv_comp_add_right η₀ (-c x) v (hη₀.differentiable (by simp) _), hdη₀ _ hv']
    simp only [b₂, neg_add_cancel_right]
    exact (hb₁b v hv).eq_of_nhds
  set O := Metric.ball (c x) (r / 4)
  have hOS : O ⊆ S := (Metric.ball_subset_ball (by linarith)).trans hrS
  have hOc : O ⊆ c.target := hOS.trans inter_subset_left
  refine ⟨c.source ∩ c ⁻¹' O, ofLoc c η₁, c.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨mem_chart_source V x, Metric.mem_ball_self (by positivity)⟩, ?_,
    isSmoothOn_ofLoc hc Metric.isOpen_ball hOc hη₁.contDiffOn, ?_⟩
  · intro y hy
    have := (hOS hy.2).2
    simpa [c.left_inv hy.1] using this
  · intro y hy
    have hU' : IsOpen (c.source ∩ c ⁻¹' O) := c.isOpen_inter_preimage Metric.isOpen_ball
    have hsm := isSmoothOn_ofLoc hc Metric.isOpen_ball hOc hη₁.contDiffOn
    refine eq_of_loc_eq hc hy.1 ?_
    have hcy : c y ∈ c.target := c.map_source hy.1
    rw [loc_d hU' hsm hc hcy (by rw [c.left_inv hy.1]; exact hy)]
    have heq : loc c (ofLoc c η₁) =ᶠ[𝓝 (c y)] η₁ := by
      filter_upwards [c.open_target.mem_nhds hcy] with v hv
      exact loc_ofLoc hc η₁ hv
    rw [heq.extDeriv_eq, hdη₁ _ hy.2]

end LocalPoincare

section Additive

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma loc_add {k : ℕ} (e : OpenPartialHomeomorph M V) (β β' : M → V [⋀^Fin k]→L[ℝ] F) :
    loc e (β + β') = loc e β + loc e β' := by
  funext v
  ext u
  simp [loc]

private lemma loc_smul {k : ℕ} (e : OpenPartialHomeomorph M V) (a : ℝ)
    (β : M → V [⋀^Fin k]→L[ℝ] F) :
    loc e (a • β) = a • loc e β := by
  funext v
  ext u
  simp [loc]

private lemma loc_zero {k : ℕ} (e : OpenPartialHomeomorph M V) :
    loc e (0 : M → V [⋀^Fin k]→L[ℝ] F) = 0 := by
  funext v
  ext u
  simp [loc]

private lemma differentiableAt_loc {k : ℕ} {U : Set M} (hU : IsOpen U) {β : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) {e : OpenPartialHomeomorph M V} (he : e ∈ atlas V M) {v : V}
    (hv : v ∈ e.target) (hvU : e.symm v ∈ U) : DifferentiableAt ℝ (loc e β) v :=
  ((hβ e he).contDiffAt ((isOpen_target_inter e hU).mem_nhds ⟨hv, hvU⟩)).differentiableAt
    (by simp)

private lemma d_add {k : ℕ} {U : Set M} (hU : IsOpen U) {β β' : M → V [⋀^Fin k]→L[ℝ] F}
    (hβ : IsSmoothOn U β) (hβ' : IsSmoothOn U β') {x : M} (hx : x ∈ U) :
    d (β + β') x = d β x + d β' x := by
  have hm := mem_target_inter (V := V) hx
  simp only [d, loc_add]
  exact extDeriv_add (differentiableAt_loc hU hβ (chart_mem_atlas V x) hm.1 hm.2)
    (differentiableAt_loc hU hβ' (chart_mem_atlas V x) hm.1 hm.2)

private lemma d_smul {k : ℕ} (a : ℝ) (β : M → V [⋀^Fin k]→L[ℝ] F) (x : M) :
    d (a • β) x = a • d β x := by
  simp only [d, loc_smul]
  exact extDeriv_smul a _

private lemma d_zero {k : ℕ} (x : M) : d (0 : M → V [⋀^Fin k]→L[ℝ] F) x = 0 := by
  have := d_smul (0 : ℝ) (0 : M → V [⋀^Fin k]→L[ℝ] F) x
  simpa using this

end Additive

/-! ### The sheaves of smooth and of closed forms -/

section Sheaves

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (M : Type) [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {V M F} in
open Classical in
/-- Extension by zero of a section over `W`. -/
private noncomputable def extend {k : ℕ} {W : Set M} (s : ∀ x : W, V [⋀^Fin k]→L[ℝ] F) :
    M → V [⋀^Fin k]→L[ℝ] F :=
  fun y ↦ if h : y ∈ W then s ⟨y, h⟩ else 0

variable {V M F} in
private lemma extend_apply {k : ℕ} {W : Set M} (s : ∀ x : W, V [⋀^Fin k]→L[ℝ] F) (x : W) :
    extend s x = s x := by
  simp [extend, x.2]

/-- The local predicate of smooth forms (`C = False`) or of closed smooth forms (`C = True`). -/
private def formPredicate (k : ℕ) (C : Prop) :
    TopCat.LocalPredicate (fun _ : TopCat.of M ↦ V [⋀^Fin k]→L[ℝ] F) where
  pred {W} s := IsSmoothOn (W : Set M) (extend s) ∧
    (C → ∀ y ∈ (W : Set M), d (extend s) y = 0)
  res := by
    intro W W' i s ⟨hs, hc⟩
    have heq : EqOn (extend s) (extend fun x : W ↦ s ⟨x.1, i.le x.2⟩) (W : Set M) := by
      intro y hy
      rw [extend_apply (fun x : W ↦ s ⟨x.1, i.le x.2⟩) ⟨y, hy⟩, extend_apply s ⟨y, i.le hy⟩]
    refine ⟨(hs.mono i.le).congr heq, fun hC y hy ↦ ?_⟩
    have h2 : extend s =ᶠ[𝓝 y] extend fun x : W ↦ s ⟨x.1, i.le x.2⟩ := by
      filter_upwards [W.isOpen.mem_nhds hy] with z hz using heq hz
    show d (extend fun x : W ↦ s ⟨x.1, i.le x.2⟩) y = 0
    rw [← d_congr h2]
    exact hc hC y (i.le hy)
  locality := by
    intro W s hs
    have heq : ∀ (V' : TopologicalSpace.Opens (TopCat.of M)) (i : V' ⟶ W),
        EqOn (extend fun x : V' ↦ s ⟨x.1, i.le x.2⟩) (extend s) (V' : Set M) := by
      intro V' i y hy
      rw [extend_apply (fun x : V' ↦ s ⟨x.1, i.le x.2⟩) ⟨y, hy⟩, extend_apply s ⟨y, i.le hy⟩]
    refine ⟨isSmoothOn_of_locally fun x hx ↦ ?_, fun hC y hy ↦ ?_⟩
    · obtain ⟨V', hxV, i, hV⟩ := hs ⟨x, hx⟩
      exact ⟨V', V'.isOpen, hxV, hV.1.congr (heq V' i)⟩
    · obtain ⟨V', hyV, i, hV⟩ := hs ⟨y, hy⟩
      have h2 : extend (fun x : V' ↦ s ⟨x.1, i.le x.2⟩) =ᶠ[𝓝 y] extend s := by
        filter_upwards [V'.isOpen.mem_nhds hyV] with z hz using heq V' i hz
      rw [← d_congr h2]
      exact hV.2 hC y hyV

variable {V M F} in
private lemma extend_zero {k : ℕ} {W : Set M} :
    extend (0 : ∀ x : W, V [⋀^Fin k]→L[ℝ] F) = 0 := by
  funext y; simp [extend]

variable {V M F} in
private lemma extend_add {k : ℕ} {W : Set M} (s t : ∀ x : W, V [⋀^Fin k]→L[ℝ] F) :
    extend (s + t) = extend s + extend t := by
  funext y
  by_cases h : y ∈ W <;> simp [extend, h]

variable {V M F} in
private lemma extend_neg {k : ℕ} {W : Set M} (s : ∀ x : W, V [⋀^Fin k]→L[ℝ] F) :
    extend (-s) = (-1 : ℝ) • extend s := by
  funext y
  by_cases h : y ∈ W <;> simp [extend, h]

/-- The group of sections over `W` of the sheaf of smooth (or closed smooth) `k`-forms. -/
private def formSections (k : ℕ) (C : Prop) (W : TopologicalSpace.Opens (TopCat.of M)) :
    AddSubgroup (∀ x : W, V [⋀^Fin k]→L[ℝ] F) where
  carrier := {s | (formPredicate V M F k C).pred s}
  zero_mem' := by
    refine ⟨?_, fun _ y _ ↦ ?_⟩
    · rw [extend_zero]; exact isSmoothOn_zero _
    · rw [extend_zero]; exact d_zero y
  add_mem' := by
    intro s t hs ht
    refine ⟨?_, fun hC y hy ↦ ?_⟩
    · rw [extend_add]; exact isSmoothOn_add hs.1 ht.1
    · rw [extend_add, d_add W.isOpen hs.1 ht.1 hy, hs.2 hC y hy, ht.2 hC y hy, add_zero]
  neg_mem' := by
    intro s hs
    refine ⟨?_, fun hC y hy ↦ ?_⟩
    · rw [extend_neg]; exact isSmoothOn_smul _ hs.1
    · rw [extend_neg, d_smul, hs.2 hC y hy, smul_zero]

variable {V M F} in
/-- Restriction of forms to a smaller open. -/
private def formRestrict {k : ℕ} {C : Prop} {W W' : TopologicalSpace.Opens (TopCat.of M)}
    (h : W' ≤ W) :
    formSections V M F k C W →+ formSections V M F k C W' where
  toFun s := ⟨fun x ↦ s.1 ⟨x.1, h x.2⟩, (formPredicate V M F k C).res (homOfLE h) s.1 s.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of smooth (or closed smooth) `k`-forms. -/
private def formPresheaf (k : ℕ) (C : Prop) : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) where
  obj W := AddCommGrpCat.of (formSections V M F k C W.unop)
  map i := AddCommGrpCat.ofHom (formRestrict i.unop.le)
  map_id _ := by ext : 2; rfl
  map_comp _ _ := by ext : 2; rfl

/-- Forgetting the group structure gives the sheaf of sections of the local predicate. -/
private def formPresheafCompForget (k : ℕ) (C : Prop) :
    formPresheaf V M F k C ⋙ forget AddCommGrpCat ≅
      TopCat.subpresheafToTypes (formPredicate V M F k C).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun W ↦ Iso.refl
      ((TopCat.subpresheafToTypes (formPredicate V M F k C).toPrelocalPredicate).obj W))
    (fun _ ↦ rfl)

/-- The sheaf of smooth (`C = False`) or closed smooth (`C = True`) `k`-forms. -/
private def formSheaf (k : ℕ) (C : Prop) : Sheaf (Opens.grothendieckTopology
    (TopCat.of M)) AddCommGrpCat.{0} where
  obj := formPresheaf V M F k C
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
    exact TopCat.Presheaf.isSheaf_of_iso (formPresheafCompForget V M F k C).symm
      (TopCat.subpresheafToTypes.isSheaf _)

variable {V M F} in
private lemma isSmoothOn_extend_d {k : ℕ} {C : Prop} {W : TopologicalSpace.Opens (TopCat.of M)}
    (s : formSections V M F k C W) :
    (formPredicate V M F (k + 1) True).pred (fun x : W ↦ d (extend s.1) x) := by
  have heq : EqOn (d (extend s.1)) (extend fun x : W ↦ d (extend s.1) x) (W : Set M) := by
    intro y hy; rw [extend_apply (fun x : W ↦ d (extend s.1) x) ⟨y, hy⟩]
  refine ⟨(isSmoothOn_d W.isOpen s.2.1).congr heq, fun _ y hy ↦ ?_⟩
  have h2 : d (extend s.1) =ᶠ[𝓝 y] extend fun x : W ↦ d (extend s.1) x := by
    filter_upwards [W.isOpen.mem_nhds hy] with z hz using heq hz
  rw [← d_congr h2]
  exact d_d W.isOpen s.2.1 hy

variable {V M F} in
/-- The exterior derivative on sections over `W`. -/
private noncomputable def dSections {k : ℕ} {C : Prop} (W : TopologicalSpace.Opens (TopCat.of M)) :
    formSections V M F k C W →+ formSections V M F (k + 1) True W where
  toFun s := ⟨fun x ↦ d (extend s.1) x, isSmoothOn_extend_d s⟩
  map_zero' := Subtype.ext <| funext fun x ↦ by
    show d (extend (0 : ∀ x : W, V [⋀^Fin k]→L[ℝ] F)) x = 0
    rw [extend_zero]; exact d_zero _
  map_add' s t := Subtype.ext <| funext fun x ↦ by
    show d (extend (s.1 + t.1)) x = d (extend s.1) x + d (extend t.1) x
    rw [extend_add]; exact d_add W.isOpen s.2.1 t.2.1 x.2

/-- The exterior derivative as a morphism of sheaves `𝒜ᵏ ⟶ 𝒵ᵏ⁺¹`. -/
private noncomputable def dHom (k : ℕ) (C : Prop) : formSheaf V M F k C ⟶ formSheaf V M F
    (k + 1) True :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (dSections W.unop)
     naturality := by
      intro W W' i
      ext s
      refine Subtype.ext (funext fun x ↦ ?_)
      change d (extend fun y : W'.unop ↦ s.1 ⟨y.1, i.unop.le y.2⟩) x = d (extend s.1) x
      refine d_congr ?_
      filter_upwards [W'.unop.isOpen.mem_nhds x.2] with z hz
      rw [extend_apply (fun y : W'.unop ↦ s.1 ⟨y.1, i.unop.le y.2⟩) ⟨z, hz⟩,
        extend_apply s.1 ⟨z, i.unop.le hz⟩] }⟩

/-- The inclusion of closed forms into all forms. -/
private def closedIncl (k : ℕ) : formSheaf V M F k True ⟶ formSheaf V M F k False :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom
      { toFun := fun s ↦ ⟨s.1, s.2.1, fun h ↦ h.elim⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
     naturality := fun _ _ _ ↦ rfl }⟩

end Sheaves

section Exactness

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (M : Type) [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private lemma closedIncl_dHom (k : ℕ) : closedIncl V M F k ≫ dHom V M F k False = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
  ext s
  refine Subtype.ext (funext fun x ↦ ?_)
  exact s.2.2 trivial x x.2

/-- The short complex `𝒵ᵏ ⟶ 𝒜ᵏ ⟶ 𝒵ᵏ⁺¹`. -/
private noncomputable def closedComplex (k : ℕ) :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk (closedIncl V M F k) (dHom V M F k False) (closedIncl_dHom V M F k)

private lemma mono_closedIncl (k : ℕ) : Mono (closedIncl V M F k) :=
  Sheaf.mono_of_injective _ fun W s t h ↦ by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'

private lemma epi_dHom (k : ℕ) : Epi (dHom V M F k False) := by
  refine (Sheaf.isLocallySurjective_iff_epi' (J := Opens.grothendieckTopology (TopCat.of M))
    AddCommGrpCat.{0} (dHom V M F k False)).1 ?_
  change TopCat.Presheaf.IsLocallySurjective (dHom V M F k False).hom
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨U', η, hU', hxU', hU'U, hη, hdη⟩ :=
    exists_local_primitive U.isOpen t.2.1 (fun y hy ↦ t.2.2 trivial y hy) hx
  let W : TopologicalSpace.Opens (TopCat.of M) := ⟨U', hU'⟩
  have hext : EqOn η (extend fun y : W ↦ η y) U' := by
    intro y hy; rw [extend_apply (fun y : W ↦ η y) ⟨y, hy⟩]
  refine ⟨W, hU'U, ⟨⟨fun y : W ↦ η y, (hη.congr hext), fun h ↦ h.elim⟩, ?_⟩, hxU'⟩
  refine Subtype.ext (funext fun y ↦ ?_)
  change d (extend fun y : W ↦ η y) y = t.1 ⟨y.1, hU'U y.2⟩
  have h2 : η =ᶠ[𝓝 y.1] extend fun y : W ↦ η y := by
    filter_upwards [hU'.mem_nhds y.2] with z hz using hext hz
  rw [← d_congr h2, hdη y.1 y.2, ← extend_apply t.1 ⟨y.1, hU'U y.2⟩]

/-- A morphism into `𝒜ᵏ` killed by `d` factors through the closed forms. -/
private noncomputable def liftClosed {k : ℕ} {T : Sheaf (Opens.grothendieckTopology
    (TopCat.of M)) AddCommGrpCat.{0}}
    (φ : T ⟶ formSheaf V M F k False) (hφ : φ ≫ dHom V M F k False = 0) :
    T ⟶ formSheaf V M F k True :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom
      { toFun := fun t ↦ ⟨(φ.hom.app W t).1, (φ.hom.app W t).2.1, fun _ y hy ↦ by
          have h := congrArg (fun f : T ⟶ formSheaf V M F (k + 1) True ↦
              (f.hom.app W t).1 ⟨y, hy⟩) hφ
          exact h.trans rfl⟩
        map_zero' := Subtype.ext (by
          show (φ.hom.app W 0).1 = 0
          rw [_root_.map_zero]; rfl)
        map_add' := fun a b ↦ Subtype.ext (by
          show (φ.hom.app W (a + b)).1 = (φ.hom.app W a).1 + (φ.hom.app W b).1
          rw [_root_.map_add]; rfl) }
     naturality := fun W W' i ↦ by
      ext t
      refine Subtype.ext ?_
      have h := congrArg Subtype.val (ConcreteCategory.congr_hom (φ.hom.naturality i) t)
      exact h }⟩

private lemma closedComplex_exact (k : ℕ) : (closedComplex V M F k).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ ?_
  refine Limits.KernelFork.IsLimit.ofι _ _ (fun φ hφ ↦ liftClosed V M F φ hφ) ?_ ?_
  · intro T φ hφ
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
    ext t
    rfl
  · intro T φ hφ m hm
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
    ext t
    refine Subtype.ext ?_
    have h := congrArg (fun f : T ⟶ formSheaf V M F k False ↦ (f.hom.app W t).1) hm
    exact h

private lemma closedComplex_shortExact (k : ℕ) : (closedComplex V M F (k + 1)).ShortExact :=
  { exact := closedComplex_exact V M F (k + 1)
    mono_f := mono_closedIncl V M F (k + 1)
    epi_g := epi_dHom V M F (k + 1) }

end Exactness

section ZeroForms

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma zeroForm_ext {A B : V [⋀^Fin 0]→L[ℝ] F} (h : A ![] = B ![]) : A = B := by
  ext v; rwa [Subsingleton.elim v ![]]

private lemma loc_zeroForm (e : OpenPartialHomeomorph M V) (β : M → V [⋀^Fin 0]→L[ℝ] F) (v : V) :
    loc e β v = β (e.symm v) :=
  zeroForm_ext (by simp [loc, Subsingleton.elim (fun i : Fin 0 ↦ _) ![]])

/-- A smooth function with vanishing differential is locally constant. -/
private lemma exists_eq_of_d_eq_zero {W : Set M} (hW : IsOpen W) {β : M → V [⋀^Fin 0]→L[ℝ] F}
    (hβ : IsSmoothOn W β) (hd : ∀ y ∈ W, d β y = 0) {x : M} (hx : x ∈ W) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧ ∀ y ∈ U, β y = β x := by
  set c := chartAt V x
  have hc : c ∈ atlas V M := chart_mem_atlas V x
  set S := c.target ∩ c.symm ⁻¹' W
  have hS : IsOpen S := isOpen_target_inter c hW
  have hxS : c x ∈ S := mem_target_inter hx
  set g : V → F := fun v ↦ loc c β v ![]
  have hloc : ∀ v, loc c β v = constOfIsEmpty ℝ V (Fin 0) (g v) := fun v ↦
    zeroForm_ext (by simp [g])
  have hgd : ContDiffOn ℝ ∞ g S := by
    have := (hβ c hc)
    exact contDiffOn_continuousAlternatingMap_apply this (fun i ↦ i.elim0)
  have hg0 : ∀ v ∈ S, fderiv ℝ g v = 0 := by
    intro v hv
    have h1 : extDeriv (loc c β) v = 0 := by
      rw [← loc_d hW hβ hc hv.1 hv.2]
      simp only [loc, hd _ hv.2]
      ext u
      simp
    have h2 : loc c β = fun v ↦ constOfIsEmpty ℝ V (Fin 0) (g v) := funext hloc
    rw [h2, extDeriv_constOfIsEmpty] at h1
    ext w
    have := congrArg (fun A : V [⋀^Fin 1]→L[ℝ] F ↦ A ![w]) h1
    simpa using this
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS _ hxS
  have hconst : ∀ v ∈ Metric.ball (c x) r, g v = g (c x) := by
    intro v hv
    refine (convex_ball (c x) r).is_const_of_fderivWithin_eq_zero
      ((hgd.mono hrS).differentiableOn (by simp)) (fun w hw ↦ ?_) hv
      (Metric.mem_ball_self hr)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
    exact hg0 w (hrS hw)
  refine ⟨c.source ∩ c ⁻¹' Metric.ball (c x) r, c.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨mem_chart_source V x, Metric.mem_ball_self hr⟩, ?_, ?_⟩
  · intro y hy
    have := (hrS hy.2).2
    simpa [c.left_inv hy.1] using this
  · intro y hy
    have e1 : β y = loc c β (c y) := by rw [loc_zeroForm, c.left_inv hy.1]
    have e2 : β x = loc c β (c x) := by rw [loc_zeroForm, c.left_inv (mem_chart_source V x)]
    rw [e1, e2, hloc, hloc, hconst _ hy.2]

end ZeroForms

section Constants

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (M : Type) [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable {V M F} in
private lemma isSmoothOn_const (a : F) (W : Set M) :
    IsSmoothOn W (fun _ : M ↦ constOfIsEmpty ℝ V (Fin 0) a) := by
  intro e _
  exact contDiffOn_const.congr fun v _ ↦ by rw [loc_zeroForm]

variable {V M F} in
private lemma d_const (a : F) (x : M) : d (fun _ : M ↦ constOfIsEmpty ℝ V (Fin 0) a) x = 0 := by
  have h : loc (chartAt V x) (fun _ : M ↦ constOfIsEmpty ℝ V (Fin 0) a) =
      fun _ ↦ constOfIsEmpty ℝ V (Fin 0) a := funext fun v ↦ by rw [loc_zeroForm]
  simp only [d, h]
  rw [extDeriv_constOfIsEmpty (f := fun _ : V ↦ a)]
  rw [show fderiv ℝ (fun _ : V ↦ a) (chartAt V x x) = 0 from fderiv_const_apply a]
  ext v; simp

variable {V M F} in
private lemma extend_const_eqOn {W : Set M} (a : F) :
    EqOn (extend fun _ : W ↦ constOfIsEmpty ℝ V (Fin 0) a)
      (fun _ ↦ constOfIsEmpty ℝ V (Fin 0) a) W :=
  fun y hy ↦ by rw [extend_apply (fun _ : W ↦ constOfIsEmpty ℝ V (Fin 0) a) ⟨y, hy⟩]

/-- Constant functions, on the constant presheaf. -/
private noncomputable def constToForm :
    (Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of F) ⟶
      (formSheaf V M F 0 False).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨fun _ ↦ constOfIsEmpty ℝ V (Fin 0) a,
        (isSmoothOn_const a _).congr (extend_const_eqOn a).symm, fun h ↦ h.elim⟩
      map_zero' := Subtype.ext (funext fun _ ↦ by ext v; simp)
      map_add' := fun a b ↦ Subtype.ext (funext fun _ ↦ by ext; simp) }
  naturality _ _ _ := rfl

/-- The inclusion `F_M ⟶ 𝒜⁰` of the constant sheaf into smooth functions. -/
private noncomputable def constIncl :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of F) ⟶ formSheaf V M F 0 False :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of M)) (constToForm V M F)
    (formSheaf V M F 0 False).property⟩

private lemma toSheafify_constIncl :
    toSheafify (Opens.grothendieckTopology (TopCat.of M)) _ ≫ (constIncl V M F).hom =
      constToForm V M F :=
  toSheafify_sheafifyLift _ _ _

private lemma constToForm_dHom : constToForm V M F ≫ (dHom V M F 0 False).hom = 0 := by
  refine NatTrans.ext (funext fun W ↦ ?_)
  ext a
  refine Subtype.ext (funext fun x ↦ ?_)
  have key : ∀ b : F, d (extend fun _ : W.unop ↦ constOfIsEmpty ℝ V (Fin 0) b) x = 0 := by
    intro b
    have h2 : (extend fun _ : W.unop ↦ constOfIsEmpty ℝ V (Fin 0) b) =ᶠ[𝓝 x.1]
        fun _ ↦ constOfIsEmpty ℝ V (Fin 0) b := by
      filter_upwards [W.unop.isOpen.mem_nhds x.2] with z hz using extend_const_eqOn b hz
    rw [d_congr h2, d_const]
  exact key a

private lemma constIncl_dHom : constIncl V M F ≫ dHom V M F 0 False = 0 := by
  refine Sheaf.hom_ext ?_
  refine sheafify_hom_ext _ _ _ (formSheaf V M F 1 True).property ?_
  have h := congrArg (· ≫ (dHom V M F 0 False).hom) (toSheafify_constIncl V M F)
  simp only [Category.assoc] at h
  exact h.trans ((constToForm_dHom V M F).trans (Limits.comp_zero).symm)

/-- The short complex `F_M ⟶ 𝒜⁰ ⟶ 𝒵¹`. -/
private noncomputable def constComplex : ShortComplex (Sheaf (Opens.grothendieckTopology
    (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk (constIncl V M F) (dHom V M F 0 False) (constIncl_dHom V M F)

private lemma stalk_constIncl (x : TopCat.of M) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of F))) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (constIncl V M F).hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (constToForm V M F) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map_comp _ _).symm.trans
    (congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (toSheafify_constIncl V M F))

private lemma const_exact_germ (x : TopCat.of M) (U : TopologicalSpace.Opens (TopCat.of M))
    (hxU : x ∈ U)
    (s : ToType ((formPresheaf V M F 0 False).obj (op U)))
    (he : (formPresheaf V M F 1 True).germ U x hxU ((dHom V M F 0 False).hom.app (op U) s) = 0) :
    ∃ (W : TopologicalSpace.Opens (TopCat.of M)) (hxW : x ∈ W) (a : F),
      (formPresheaf V M F 0 False).germ W x hxW ((constToForm V M F).app (op W) a) =
        (formPresheaf V M F 0 False).germ U x hxU s := by
  have he2 : (formPresheaf V M F 1 True).germ U x hxU ((dHom V M F 0 False).hom.app (op U) s) =
      (formPresheaf V M F 1 True).germ U x hxU 0 := he.trans (_root_.map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ he2
  have hdW : ∀ y ∈ (W : Set M), d (extend s.1) y = 0 := by
    intro y hy
    have h1 := congrArg (fun t : ToType ((formPresheaf V M F 1 True).obj (op W)) ↦ t.1 ⟨y, hy⟩) hW
    simp only [_root_.map_zero] at h1
    exact h1
  obtain ⟨U', hU', hxU', hU'W, hconst⟩ := exists_eq_of_d_eq_zero W.isOpen
    (s.2.1.mono iU.le) hdW hxW
  let W' : TopologicalSpace.Opens (TopCat.of M) := ⟨U', hU'⟩
  refine ⟨W', hxU', extend s.1 x ![], ?_⟩
  have hres : (constToForm V M F).app (op W') (extend s.1 x ![]) =
      (formPresheaf V M F 0 False).map (homOfLE (hU'W.trans iU.le) : W' ⟶ U).op s := by
    refine Subtype.ext (funext fun y ↦ ?_)
    change constOfIsEmpty ℝ V (Fin 0) (extend s.1 x ![]) = s.1 ⟨y.1, _⟩
    rw [← extend_apply s.1 ⟨y.1, (hU'W.trans iU.le) y.2⟩]
    refine zeroForm_ext ?_
    rw [hconst y.1 y.2]
    rfl
  rw [hres, TopCat.Presheaf.germ_res_apply]

private lemma constComplex_exact : (constComplex V M F).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{0}) (X := TopCat.of M)
    (constComplex V M F)).2 fun x ↦ ?_
  rw [ShortComplex.ab_exact_iff]
  intro e he
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ e
  have he' : (formPresheaf V M F 1 True).germ U x hxU ((dHom V M F 0 False).hom.app (op U) s) =
      0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU (dHom V M F 0 False).hom s).symm.trans he
  obtain ⟨W, hxW, a, ha⟩ := const_exact_germ V M F x U hxU s he'
  let P : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) :=
    (Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of F)
  refine ⟨(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
    (toSheafify (Opens.grothendieckTopology (TopCat.of M)) P) (P.germ W x hxW a), ?_⟩
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  exact (ConcreteCategory.congr_hom (stalk_constIncl V M F x) (P.germ W x hxW a)).trans
    ((TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW (constToForm V M F) a).trans ha)

private lemma mono_constIncl : Mono (constIncl V M F) := by
  let P : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) :=
    (Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of F)
  have hm : ∀ x : TopCat.of M, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (constIncl V M F).hom) := by
    intro x
    rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro w hw
    haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{0} P
    have hsurj := ((ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology (TopCat.of M)) P))).1 inferInstance).2
    obtain ⟨w', rfl⟩ := hsurj w
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq P w'
    have h1 := ConcreteCategory.congr_hom (stalk_constIncl V M F x) (P.germ U x hxU a)
    have h2 : (formPresheaf V M F 0 False).germ U x hxU ((constToForm V M F).app (op U) a) =
        (formPresheaf V M F 0 False).germ U x hxU 0 :=
      ((TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU (constToForm V M F) a).symm.trans
        (h1.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans hw))).trans
          (_root_.map_zero _).symm
    obtain ⟨W, hxW, iU, _, hW⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ h2
    have h3 := congrArg (fun t : ToType ((formPresheaf V M F 0 False).obj (op W)) ↦
      t.1 ⟨x, hxW⟩ ![]) hW
    have ha : (show F from a) = 0 := h3
    have : (P.germ U x hxU a) = 0 := by
      rw [show a = 0 from ha]; exact _root_.map_zero _
    rw [this]; exact _root_.map_zero _
  exact TopCat.Presheaf.mono_of_stalk_mono (C := AddCommGrpCat.{0}) (X := TopCat.of M)
    (constIncl V M F)

private lemma constComplex_shortExact : (constComplex V M F).ShortExact :=
  { exact := constComplex_exact V M F
    mono_f := mono_constIncl V M F
    epi_g := epi_dHom V M F 0 }

end Constants

section Fine

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private lemma contDiffOn_comp_symm_of_contMDiff {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ) ∞ ρ)
    {e : OpenPartialHomeomorph M V} (he : e ∈ atlas V M) :
    ContDiffOn ℝ ∞ (ρ ∘ e.symm) e.target := by
  have := (hρ.contMDiffOn (s := e.source))
  rw [contMDiffOn_iff_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℝ (0:ℝ))) le_rfl (fun _ _ ↦ trivial)] at this
  simpa [e.image_source_eq_target, chartAt_self_eq] using this.2

open Classical in
/-- A smooth real function times a smooth function on an open set `W`, where the function is
supported in a closed set inside `W`, extended by zero. -/
private lemma isSmoothOn_smul_extend {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ) ∞ ρ) {U W : Set M}
    (hU : IsOpen U) (hW : IsOpen W) (hρW : tsupport ρ ⊆ W) {f : M → V [⋀^Fin 0]→L[ℝ] F}
    (hf : IsSmoothOn (U ∩ W) f) :
    IsSmoothOn U (fun y ↦ if y ∈ W then ρ y • f y else 0) := by
  refine isSmoothOn_of_locally fun x hx ↦ ?_
  by_cases hxW : x ∈ W
  · refine ⟨U ∩ W, hU.inter hW, ⟨hx, hxW⟩, ?_⟩
    intro e he
    have h1 : ContDiffOn ℝ ∞ (fun v ↦ ρ (e.symm v) • loc e f v) (e.target ∩ e.symm ⁻¹' (U ∩ W)) :=
      ((contDiffOn_comp_symm_of_contMDiff hρ he).mono inter_subset_left).smul (hf e he)
    refine h1.congr fun v hv ↦ ?_
    rw [loc_zeroForm, loc_zeroForm, if_pos hv.2.2]
  · have hx' : x ∉ tsupport ρ := fun h ↦ hxW (hρW h)
    refine ⟨U \ tsupport ρ, hU.sdiff (isClosed_tsupport ρ), ⟨hx, hx'⟩, ?_⟩
    refine (isSmoothOn_zero (U \ tsupport ρ)).congr fun y hy ↦ ?_
    simp only [Pi.zero_apply]
    split_ifs
    · rw [image_eq_zero_of_notMem_tsupport hy.2, zero_smul]
    · rfl

private lemma isSmoothOn_finset_sum {k : ℕ} {U : Set M} {κ : Type*} (S : Finset κ)
    (f : κ → M → V [⋀^Fin k]→L[ℝ] F) (h : ∀ i ∈ S, IsSmoothOn U (f i)) :
    IsSmoothOn U (fun y ↦ ∑ i ∈ S, f i y) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (isSmoothOn_zero U).congr fun y _ ↦ by simp
  | insert i S hi ih =>
    have := isSmoothOn_add (h i (Finset.mem_insert_self i S))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    exact this.congr fun y _ ↦ by simp [Finset.sum_insert hi]

private lemma res_res {T : Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}}
    {W W' W'' : TopologicalSpace.Opens (TopCat.of M)} (h₁ : W'' ≤ W') (h₂ : W' ≤ W)
    (x : ToType (T.obj.obj (op W))) :
    T.obj.map (homOfLE h₁).op (T.obj.map (homOfLE h₂).op x) =
      T.obj.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← T.obj.map_comp]
  rfl

private lemma app_res {T T' : Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}}
    (φ : T ⟶ T') {W W' : TopologicalSpace.Opens (TopCat.of M)} (h : W' ≤ W)
    (x : ToType (T.obj.obj (op W))) :
    φ.hom.app (op W') (T.obj.map (homOfLE h).op x) =
      T'.obj.map (homOfLE h).op (φ.hom.app (op W) x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE h).op) x

private lemma injective_app_of_mono {T T' : Sheaf (Opens.grothendieckTopology
    (TopCat.of M)) AddCommGrpCat.{0}}
    (φ : T ⟶ T') [Mono φ] (W) : Function.Injective (φ.hom.app W) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

open Classical in
/-- **Smooth functions form a fine sheaf**: in a short exact sequence
`0 → 𝒜⁰ → I → Q → 0` of abelian sheaves on a compact Hausdorff manifold, every global section of
`Q` lifts to `I`. -/
private theorem exists_lift_of_shortExact [CompactSpace M] [T2Space M]
    {I Q : Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}}
    {ι : formSheaf V M F 0 False ⟶ I} {π : I ⟶ Q} {w : ι ≫ π = 0}
    (hS : (ShortComplex.mk ι π w).ShortExact) (q : ToType (Q.obj.obj (op ⊤))) :
    ∃ s : ToType (I.obj.obj (op ⊤)), π.hom.app (op ⊤) s = q := by
  -- local lifts
  have hls : TopCat.Presheaf.IsLocallySurjective π.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (J := Opens.grothendieckTopology (TopCat.of M))
      AddCommGrpCat.{0} π).2 hS.epi_g
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hls
  have hloc : ∀ x : M, ∃ (U : TopologicalSpace.Opens (TopCat.of M)) (_ : U ≤ ⊤),
      (∃ s, π.hom.app (op U) s = Q.obj.map (homOfLE le_top).op q) ∧ x ∈ U :=
    fun x ↦ hls ⊤ q x trivial
  choose U _ hs hxU using hloc
  choose s hs using hs
  -- a finite subcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set M))
    (fun x ↦ (U x).isOpen) (fun y _ ↦ mem_iUnion.2 ⟨y, hxU y⟩)
  -- a subordinate partition of unity
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) isClosed_univ
    (fun i : t ↦ (U i.1 : Set M)) (fun i ↦ (U i.1).isOpen) (by
      intro y _
      obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hy⟩)
  -- the differences of the local lifts come from `𝒜⁰`
  have hdiff : ∀ i j : t, ∃ a : ToType ((formSheaf V M F 0 False).obj.obj (op (U i.1 ⊓ U j.1))),
      ι.hom.app _ a = I.obj.map (homOfLE inf_le_left).op (s i.1) -
        I.obj.map (homOfLE inf_le_right).op (s j.1) := by
    intro i j
    refine TopCat.Sheaf.sections_exact_of_left_exact (S := ShortComplex.mk ι π w) hS.exact
      hS.mono_f _ ?_
    change π.hom.app _ (_ - _) = 0
    have hnat : ∀ {W W' : TopologicalSpace.Opens (TopCat.of M)} (h : W' ≤ W)
        (x : ToType (I.obj.obj (op W))), π.hom.app (op W') (I.obj.map (homOfLE h).op x) =
          Q.obj.map (homOfLE h).op (π.hom.app (op W) x) :=
      fun h x ↦ ConcreteCategory.congr_hom (π.hom.naturality (homOfLE h).op) x
    rw [map_sub, hnat, hnat, hs, hs, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Q.obj.map_comp, ← Q.obj.map_comp]
    exact sub_self _
  choose a ha using hdiff
  haveI := hS.mono_f
  have hιinj : ∀ W, Function.Injective (ι.hom.app W) := injective_app_of_mono ι
  -- the cocycle condition, pointwise
  have hcoc : ∀ (i j k : t) (y : M) (hi : y ∈ U i.1) (hj : y ∈ U j.1) (hk : y ∈ U k.1),
      (a i k).1 ⟨y, hi, hk⟩ - (a j k).1 ⟨y, hj, hk⟩ = (a i j).1 ⟨y, hi, hj⟩ := by
    intro i j k y hi hj hk
    let W := U i.1 ⊓ U j.1 ⊓ U k.1
    have e : (formSheaf V M F 0 False).obj.map
          (homOfLE (show W ≤ U i.1 ⊓ U k.1 from le_inf (inf_le_left.trans inf_le_left)
            inf_le_right)).op (a i k) -
        (formSheaf V M F 0 False).obj.map
          (homOfLE (show W ≤ U j.1 ⊓ U k.1 from le_inf (inf_le_left.trans inf_le_right)
            inf_le_right)).op (a j k) =
        (formSheaf V M F 0 False).obj.map (homOfLE (show W ≤ U i.1 ⊓ U j.1 from inf_le_left)).op
          (a i j) := by
      apply hιinj
      rw [map_sub, app_res, app_res, app_res, ha, ha, ha]
      simp only [map_sub]
      rw [res_res, res_res, res_res, res_res, res_res, res_res]
      abel
    have := congrArg (fun z : ToType ((formSheaf V M F 0 False).obj.obj (op W)) ↦
      z.1 ⟨y, ⟨hi, hj⟩, hk⟩) e
    exact this
  -- the correction terms `t_i = ∑ⱼ ρⱼ a_ij`
  let T : t → M → V [⋀^Fin 0]→L[ℝ] F := fun i y ↦
    ∑ j : t, if y ∈ (U j.1 : Set M) then ρ j y • extend (a i j).1 y else 0
  have hT : ∀ i, IsSmoothOn (U i.1 : Set M) (T i) := fun i ↦
    isSmoothOn_finset_sum _ _ fun j _ ↦ isSmoothOn_smul_extend (ρ j).contMDiff (U i.1).isOpen
      (U j.1).isOpen (hρ j) (a i j).2.1
  let ts : ∀ i : t, ToType ((formSheaf V M F 0 False).obj.obj (op (U i.1))) := fun i ↦
    (⟨fun y ↦ T i y.1, (hT i).congr fun y hy ↦
      (extend_apply (fun y : U i.1 ↦ T i y.1) ⟨y, hy⟩).symm, fun h ↦ h.elim⟩ :
        formSections V M F 0 False (U i.1))
  have hkey : ∀ i j : t, (formSheaf V M F 0 False).obj.map (homOfLE inf_le_left).op (ts i) -
      (formSheaf V M F 0 False).obj.map (homOfLE inf_le_right).op (ts j) = a i j := by
    intro i j
    refine Subtype.ext (funext fun y ↦ ?_)
    change T i y.1 - T j y.1 = (a i j).1 y
    simp only [T, ← Finset.sum_sub_distrib]
    have hy := y.2
    have hterm : ∀ k : t, ((if y.1 ∈ (U k.1 : Set M) then ρ k y.1 • extend (a i k).1 y.1 else 0) -
        (if y.1 ∈ (U k.1 : Set M) then ρ k y.1 • extend (a j k).1 y.1 else 0)) =
          ρ k y.1 • (a i j).1 y := by
      intro k
      by_cases hk : y.1 ∈ (U k.1 : Set M)
      · rw [if_pos hk, if_pos hk, ← smul_sub,
          show extend (a i k).1 y.1 = (a i k).1 ⟨y.1, hy.1, hk⟩ from
            extend_apply (a i k).1 ⟨y.1, hy.1, hk⟩,
          show extend (a j k).1 y.1 = (a j k).1 ⟨y.1, hy.2, hk⟩ from
            extend_apply (a j k).1 ⟨y.1, hy.2, hk⟩,
          hcoc i j k y.1 hy.1 hy.2 hk]
      · rw [if_neg hk, if_neg hk, sub_zero,
          image_eq_zero_of_notMem_tsupport (fun h ↦ hk (hρ k h)), zero_smul]
    rw [Finset.sum_congr rfl (fun k _ ↦ hterm k), ← Finset.sum_smul,
      ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ _), one_smul]
  -- the corrected local lifts are compatible
  let s' : ∀ i : t, ToType (I.obj.obj (op (U i.1))) := fun i ↦ s i.1 - ι.hom.app _ (ts i)
  have hcompat : TopCat.Presheaf.IsCompatible I.obj (fun i : t ↦ U i.1) s' := by
    intro i j
    change I.obj.map (homOfLE inf_le_left).op (s' i) = I.obj.map (homOfLE inf_le_right).op (s' j)
    simp only [s', map_sub]
    rw [← app_res, ← app_res, sub_eq_sub_iff_sub_eq_sub, ← map_sub, hkey, ha]
  have hcover : (⊤ : TopologicalSpace.Opens (TopCat.of M)) ≤ iSup fun i : t ↦ U i.1 := by
    intro y _
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy⟩
  obtain ⟨sg, hsg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (show TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) from I) (fun i : t ↦ U i.1) ⊤
    (fun i ↦ homOfLE le_top) hcover s' hcompat
  refine ⟨sg, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (show TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) from Q)
    (fun i : t ↦ U i.1) ⊤ (fun i ↦ homOfLE le_top) hcover _ _ fun i ↦ ?_
  change Q.obj.map (homOfLE le_top).op (π.hom.app _ sg) = Q.obj.map (homOfLE le_top).op q
  rw [← app_res, hsg i]
  simp only [s', map_sub, hs]
  have h0 : π.hom.app (op (U i.1)) (ι.hom.app (op (U i.1)) (ts i)) = 0 := by
    have := congrArg (fun f ↦ (f.hom.app (op (U i.1))) (ts i)) w
    exact this
  rw [h0, sub_zero]

/-- **Smooth functions are acyclic**: `H¹(M, 𝒜⁰) = 0` on a compact Hausdorff manifold. -/
private theorem formSheaf_zero_H_one [CompactSpace M] [T2Space M]
    (e : Sheaf.H (formSheaf V M F 0 False) 1) : e = 0 := by
  let A := formSheaf V M F 0 False
  let ι := Injective.ι A
  let S := ShortComplex.mk ι (Limits.cokernel.π ι) (Limits.cokernel.condition ι)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel S (Limits.cokernelIsCokernel ι)
      mono_f := Injective.ι_mono A
      epi_g := inferInstance }
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS e
      (Abelian.Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨sI, hsI⟩ := exists_lift_of_shortExact hS (Sheaf.H.equiv₀ _ Limits.isTerminalTop x₃)
  let y := (Sheaf.H.equiv₀ (Injective.under A) Limits.isTerminalTop).symm sI
  have hy : y.comp (Abelian.Ext.mk₀ (Limits.cokernel.π ι)) (add_zero 0) = x₃ := by
    apply (Sheaf.H.equiv₀ _ Limits.isTerminalTop).injective
    have h := Sheaf.H.equiv₀_naturality Limits.isTerminalTop (Limits.cokernel.π ι) y
    rw [show Sheaf.H.map (Limits.cokernel.π ι) 0 y = y.comp (Abelian.Ext.mk₀ _)
        (add_zero 0) from rfl] at h
    rw [← h]
    simp only [y, AddEquiv.apply_symm_apply]
    exact hsI
  rw [← hx₃, ← hy, Abelian.Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by norm_num)]
  rw [show (Abelian.Ext.mk₀ (Limits.cokernel.π ι)).comp hS.extClass (zero_add 1) = 0 from
      hS.comp_extClass,
    Abelian.Ext.comp_zero]

end Fine

section ComplexScalars

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (M : Type) [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]

variable {V M} in
private lemma loc_csmul {k : ℕ} (e : OpenPartialHomeomorph M V) (c : ℂ)
    (β : M → V [⋀^Fin k]→L[ℝ] ℂ) :
    loc e (c • β) = c • loc e β := by
  funext v
  ext u
  simp [loc]

variable {V M} in
private lemma isSmoothOn_csmul {k : ℕ} {U : Set M} (c : ℂ) {β : M → V [⋀^Fin k]→L[ℝ] ℂ}
    (hβ : IsSmoothOn U β) : IsSmoothOn U (c • β) := by
  intro e he
  rw [loc_csmul]
  exact (hβ e he).const_smul c

variable {V M} in
private lemma d_csmul {k : ℕ} {U : Set M} (hU : IsOpen U) (c : ℂ) {β : M → V [⋀^Fin k]→L[ℝ] ℂ}
    (hβ : IsSmoothOn U β) {x : M} (hx : x ∈ U) : d (c • β) x = c • d β x := by
  have hm := mem_target_inter (V := V) hx
  simp only [d, loc_csmul]
  rw [show (c • loc (chartAt V x) β) = fun v ↦ c • loc (chartAt V x) β v from rfl]
  simp only [extDeriv]
  rw [fderiv_fun_const_smul (differentiableAt_loc hU hβ (chart_mem_atlas V x) hm.1 hm.2) c]
  exact alternatizeUncurryFin_smul c _

variable {V M} in
private lemma extend_csmul {k : ℕ} {W : Set M} (c : ℂ) (s : ∀ x : W, V [⋀^Fin k]→L[ℝ] ℂ) :
    extend (c • s) = c • extend s := by
  funext y
  by_cases h : y ∈ W <;> simp [extend, h]

variable {V M} in
/-- Multiplication by `c ∈ ℂ` on sections. -/
private noncomputable def smulSections (c : ℂ) {k : ℕ} {C : Prop} (W : TopologicalSpace.Opens
    (TopCat.of M)) :
    formSections V M ℂ k C W →+ formSections V M ℂ k C W where
  toFun s := ⟨c • s.1, by
    refine ⟨?_, fun hC y hy ↦ ?_⟩
    · rw [extend_csmul]
      exact isSmoothOn_csmul c s.2.1
    · rw [extend_csmul, d_csmul W.isOpen c s.2.1 hy, s.2.2 hC y hy, smul_zero]⟩
  map_zero' := Subtype.ext (smul_zero c)
  map_add' a b := Subtype.ext (smul_add c a.1 b.1)

/-- Multiplication by `c ∈ ℂ` on the sheaf of complex forms. -/
private noncomputable def smulHom (c : ℂ) (k : ℕ) (C : Prop) :
    formSheaf V M ℂ k C ⟶ formSheaf V M ℂ k C :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (smulSections c W.unop)
     naturality := fun _ _ _ ↦ rfl }⟩

private lemma closedIncl_smulHom (c : ℂ) (k : ℕ) :
    closedIncl V M ℂ k ≫ smulHom V M c k False = smulHom V M c k True ≫ closedIncl V M ℂ k :=
  rfl

private lemma dHom_smulHom (c : ℂ) (k : ℕ) (C : Prop) :
    dHom V M ℂ k C ≫ smulHom V M c (k + 1) True = smulHom V M c k C ≫ dHom V M ℂ k C := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
  ext s
  refine Subtype.ext (funext fun x ↦ ?_)
  change c • d (extend s.1) x = d (extend (c • s.1)) x
  rw [extend_csmul, d_csmul W.unop.isOpen c s.2.1 x.2]

private lemma constIncl_smulHom (c : ℂ) :
    constIncl V M ℂ ≫ smulHom V M c 0 False =
      (constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).map
        (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)) ≫ constIncl V M ℂ := by
  refine Sheaf.hom_ext ?_
  refine sheafify_hom_ext _ _ _ (formSheaf V M ℂ 0 False).property ?_
  have h1 := congrArg (· ≫ (smulHom V M c 0 False).hom) (toSheafify_constIncl V M ℂ)
  simp only [Category.assoc] at h1
  refine h1.trans ?_
  have h2 := toSheafify_naturality (Opens.grothendieckTopology (TopCat.of M))
    ((Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).map
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)))
  have h3 : toSheafify (Opens.grothendieckTopology (TopCat.of M)) _ ≫
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).map
        (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)) ≫ constIncl V M ℂ).hom =
      (Functor.const (TopologicalSpace.Opens (TopCat.of M))ᵒᵖ).map
        (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)) ≫ constToForm V M ℂ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (constIncl V M ℂ).hom) h2.symm).trans
        ((Category.assoc _ _ _).trans (whisker_eq _ (toSheafify_constIncl V M ℂ))))
  refine Eq.trans ?_ h3.symm
  refine NatTrans.ext (funext fun W ↦ ?_)
  ext a
  refine Subtype.ext (funext fun y ↦ ?_)
  ext v
  rfl

end ComplexScalars

/-! ### Pulling back forms along a smooth map -/

section Pullback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ, V) ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map `φ : M → N` read in the charts `e` of `M` and `e'` of `N`. -/
private def rd (φ : M → N) (e : OpenPartialHomeomorph M V) (e' : OpenPartialHomeomorph N V) :
    V → V :=
  fun v ↦ e' (φ (e.symm v))

/-- The open set on which `rd φ e e'` is defined. -/
private def rdSrc (φ : M → N) (e : OpenPartialHomeomorph M V) (e' : OpenPartialHomeomorph N V) :
    Set V :=
  e.target ∩ e.symm ⁻¹' (φ ⁻¹' e'.source)

/-- `φ` is continuous and smooth in every pair of atlas charts. -/
private def IsSmoothMap (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] {M N : Type*}
    [TopologicalSpace M] [ChartedSpace V M] [TopologicalSpace N] [ChartedSpace V N]
    (φ : M → N) : Prop :=
  Continuous φ ∧ ∀ e ∈ atlas V M, ∀ e' ∈ atlas V N, ContDiffOn ℝ ∞ (rd φ e e') (rdSrc φ e e')

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma isOpen_rdSrc {φ : M → N} (hφ : Continuous φ) (e : OpenPartialHomeomorph M V)
    (e' : OpenPartialHomeomorph N V) : IsOpen (rdSrc φ e e') :=
  e.isOpen_inter_preimage_symm (e'.open_source.preimage hφ)

/-- The pullback `φ^* β` of a form `β` on `N`. -/
private noncomputable def pb {k : ℕ} (φ : M → N) (β : N → V [⋀^Fin k]→L[ℝ] F) (x : M) :
    V [⋀^Fin k]→L[ℝ] F :=
  (β (φ x)).compContinuousLinearMap
    (fderiv ℝ (rd φ (chartAt V x) (chartAt V (φ x))) (chartAt V x x))

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma compCLM_compCLM {k : ℕ} (A : V [⋀^Fin k]→L[ℝ] F) (L₁ L₂ : V →L[ℝ] V) :
    (A.compContinuousLinearMap L₁).compContinuousLinearMap L₂ =
      A.compContinuousLinearMap (L₁.comp L₂) := by
  ext u; rfl

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma mem_rdSrc_chartAt {φ : M → N} (x : M) :
    chartAt V x x ∈ rdSrc φ (chartAt V x) (chartAt V (φ x)) :=
  ⟨(chartAt V x).map_source (mem_chart_source V x), by
    simp [(chartAt V x).left_inv (mem_chart_source V x), mem_chart_source]⟩

private lemma differentiableAt_rd {φ : M → N} (hφ : IsSmoothMap V φ) {e : OpenPartialHomeomorph M V}
    (he : e ∈ atlas V M) {e' : OpenPartialHomeomorph N V} (he' : e' ∈ atlas V N) {v : V}
    (hv : v ∈ rdSrc φ e e') : DifferentiableAt ℝ (rd φ e e') v :=
  ((hφ.2 e he e' he').contDiffAt ((isOpen_rdSrc hφ.1 e e').mem_nhds hv)).differentiableAt
    (by simp)

/-- **The local expression of a pullback** in charts `e` and `e'`. -/
private lemma loc_pb {k : ℕ} {φ : M → N} (hφ : IsSmoothMap V φ) (β : N → V [⋀^Fin k]→L[ℝ] F)
    {e : OpenPartialHomeomorph M V} (he : e ∈ atlas V M) {e' : OpenPartialHomeomorph N V}
    (he' : e' ∈ atlas V N) {v : V} (hv : v ∈ rdSrc φ e e') :
    loc e (pb φ β) v =
      (loc e' β (rd φ e e' v)).compContinuousLinearMap (fderiv ℝ (rd φ e e') v) := by
  set y := e.symm v with hy
  set c := chartAt V y
  set c' := chartAt V (φ y)
  have hv1 : v ∈ e.target := hv.1
  have hv2 : φ y ∈ e'.source := hv.2
  have hyc : y ∈ c.source := mem_chart_source V y
  have hφc : φ y ∈ c'.source := mem_chart_source V (φ y)
  have hT : e'.symm (rd φ e e' v) = φ y := e'.left_inv hv2
  -- the two factorizations of `rd φ e c'`
  have hsrc1 : v ∈ (tr e c).source := mem_tr_source_chartAt hv1
  have hcy : c y ∈ rdSrc φ c c' := ⟨c.map_source hyc, by simp [c.left_inv hyc, hφc]⟩
  have hsrc2 : rd φ e e' v ∈ (tr e' c').source := by
    simp only [tr, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨e'.map_source hv2, by rw [hT]; exact hφc⟩
  have h1 : rd φ c c' ∘ tr e c =ᶠ[𝓝 v] rd φ e c' := by
    filter_upwards [(isOpen_tr_source e c).mem_nhds hsrc1] with w hw
    have hw' : e.symm w ∈ c.source := by
      simp [tr] at hw
      exact hw.2
    simp [rd, tr, c.left_inv hw']
  have h2 : tr e' c' ∘ rd φ e e' =ᶠ[𝓝 v] rd φ e c' := by
    filter_upwards [(isOpen_rdSrc hφ.1 e e').mem_nhds hv] with w hw
    have hw' : φ (e.symm w) ∈ e'.source := hw.2
    simp [rd, tr, e'.left_inv hw']
  have hD1 : (fderiv ℝ (rd φ c c') (c y)).comp (fderiv ℝ (tr e c) v) = fderiv ℝ (rd φ e c') v := by
    rw [← h1.fderiv_eq]
    exact (fderiv_comp v (differentiableAt_rd hφ (chart_mem_atlas V y) (chart_mem_atlas V
        (φ y)) hcy)
      (differentiableAt_tr he (chart_mem_atlas V y) hsrc1)).symm
  have hD2 : (fderiv ℝ (tr e' c') (rd φ e e' v)).comp (fderiv ℝ (rd φ e e') v) =
      fderiv ℝ (rd φ e c') v := by
    rw [← h2.fderiv_eq]
    exact (fderiv_comp v (differentiableAt_tr he' (chart_mem_atlas V (φ y)) hsrc2)
      (differentiableAt_rd hφ he he' hv)).symm
  simp only [loc, pb]
  rw [compCLM_compCLM, compCLM_compCLM, hT]
  congr 1
  rw [hD2]
  exact hD1

private lemma rd_mem_target_inter {φ : M → N} {e : OpenPartialHomeomorph M V}
    {e' : OpenPartialHomeomorph N V} {U : Set N} {v : V}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' (φ ⁻¹' (e'.source ∩ U))) :
    rd φ e e' v ∈ e'.target ∩ e'.symm ⁻¹' U :=
  ⟨e'.map_source hv.2.1, by simp only [rd, mem_preimage, e'.left_inv hv.2.1]; exact hv.2.2⟩

/-- A pullback of a smooth form is smooth. -/
private lemma isSmoothOn_pb {k : ℕ} {φ : M → N} (hφ : IsSmoothMap V φ) {U : Set N}
    (hU : IsOpen U) {β : N → V [⋀^Fin k]→L[ℝ] F} (hβ : IsSmoothOn U β) :
    IsSmoothOn (φ ⁻¹' U) (pb φ β) := by
  intro e he
  refine contDiffOn_of_locally_contDiffOn fun v hv ↦ ?_
  set e' := chartAt V (φ (e.symm v))
  have he' : e' ∈ atlas V N := chart_mem_atlas V _
  set S := e.target ∩ e.symm ⁻¹' (φ ⁻¹' (e'.source ∩ U))
  have hS : IsOpen S := e.isOpen_inter_preimage_symm
    ((e'.open_source.inter hU).preimage hφ.1)
  refine ⟨S, hS, ⟨hv.1, mem_chart_source V _, hv.2⟩, ?_⟩
  have hSsrc : S ⊆ rdSrc φ e e' := fun w hw ↦ ⟨hw.1, hw.2.1⟩
  have hrd : ContDiffOn ℝ ∞ (rd φ e e') S := (hφ.2 e he e' he').mono hSsrc
  have h1 : ContDiffOn ℝ ∞ (fun w ↦ (loc e' β (rd φ e e' w)).compContinuousLinearMap
      (fderiv ℝ (rd φ e e') w)) S := by
    have hgT : ContDiffOn ℝ ∞ (fun w ↦ loc e' β (rd φ e e' w)) S :=
      (hβ e' he').comp hrd fun w hw ↦ rd_mem_target_inter hw
    have hdT : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ (rd φ e e') w) S :=
      ((hφ.2 e he e' he').fderiv_of_isOpen (isOpen_rdSrc hφ.1 e e') (by simp)).mono hSsrc
    exact contDiffOn_compCLM hgT hdT
  refine (h1.mono inter_subset_right).congr fun w hw ↦ ?_
  exact loc_pb hφ β he he' (hSsrc hw.2)

/-- **The exterior derivative commutes with pullback.** -/
private lemma d_pb {k : ℕ} {φ : M → N} (hφ : IsSmoothMap V φ) {U : Set N} (hU : IsOpen U)
    {β : N → V [⋀^Fin k]→L[ℝ] F} (hβ : IsSmoothOn U β) {x : M} (hx : φ x ∈ U) :
    d (pb φ β) x = pb φ (d β) x := by
  set c := chartAt V x
  set c' := chartAt V (φ x)
  have hc : c ∈ atlas V M := chart_mem_atlas V x
  have hc' : c' ∈ atlas V N := chart_mem_atlas V (φ x)
  have hx0 : c x ∈ rdSrc φ c c' := mem_rdSrc_chartAt x
  have heq : loc c (pb φ β) =ᶠ[𝓝 (c x)] fun w ↦
      (loc c' β (rd φ c c' w)).compContinuousLinearMap (fderiv ℝ (rd φ c c') w) := by
    filter_upwards [(isOpen_rdSrc hφ.1 c c').mem_nhds hx0] with w hw
    exact loc_pb hφ β hc hc' hw
  have hTx : rd φ c c' (c x) = c' (φ x) := by
    simp [rd, c.left_inv (mem_chart_source V x)]
  have hm : c' (φ x) ∈ c'.target := c'.map_source (mem_chart_source V (φ x))
  have hmU : c'.symm (c' (φ x)) ∈ U := by rw [c'.left_inv (mem_chart_source V (φ x))]; exact hx
  have hω : DifferentiableAt ℝ (loc c' β) (rd φ c c' (c x)) := by
    rw [hTx]; exact differentiableAt_loc hU hβ hc' hm hmU
  have hT : ContDiffAt ℝ ∞ (rd φ c c') (c x) :=
    (hφ.2 c hc c' hc').contDiffAt ((isOpen_rdSrc hφ.1 c c').mem_nhds hx0)
  change extDeriv (loc c (pb φ β)) (c x) = _
  rw [heq.extDeriv_eq, extDeriv_pullback hω hT two_le_infty, hTx,
    ← loc_d hU hβ hc' hm hmU, ← hTx, ← loc_pb hφ (d β) hc hc' hx0, loc_chartAt_self]

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma pb_congr {k : ℕ} {φ : M → N} {β β' : N → V [⋀^Fin k]→L[ℝ] F} {x : M}
    (h : β (φ x) = β' (φ x)) : pb φ β x = pb φ β' x := by
  simp [pb, h]

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma pb_add {k : ℕ} (φ : M → N) (β β' : N → V [⋀^Fin k]→L[ℝ] F) (x : M) :
    pb φ (β + β') x = pb φ β x + pb φ β' x := by
  ext u; simp [pb]

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, V) ∞ M] [IsManifold 𝓘(ℝ, V) ∞ N] in
private lemma pb_zero {k : ℕ} (φ : M → N) (x : M) :
    pb φ (0 : N → V [⋀^Fin k]→L[ℝ] F) x = 0 := by
  ext u; simp [pb]

end Pullback

/-! ### Pulling back the sheaves of forms -/

section PullbackSheaves

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {N : Type} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ, V) ∞ N]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : IsSmoothMap V ⇑f)

include hf in
private lemma pred_pb {k : ℕ} {C : Prop} {U : TopologicalSpace.Opens (TopCat.of N)}
    (s : formSections V N F k C U) :
    (formPredicate V M F k C).pred (U := (TopologicalSpace.Opens.map f).obj U)
      (fun x ↦ pb (⇑f) (extend s.1) x.1) := by
  have heq : EqOn (pb (⇑f) (extend s.1))
      (extend fun x : ((TopologicalSpace.Opens.map f).obj U) ↦ pb (⇑f) (extend s.1) x.1)
      ((TopologicalSpace.Opens.map f).obj U : Set M) := by
    intro y hy
    rw [extend_apply (fun x : ((TopologicalSpace.Opens.map f).obj U) ↦
      pb (⇑f) (extend s.1) x.1) ⟨y, hy⟩]
  refine ⟨(isSmoothOn_pb hf U.isOpen s.2.1).congr heq, fun hC y hy ↦ ?_⟩
  have h2 : pb (⇑f) (extend s.1) =ᶠ[𝓝 y]
      extend fun x : ((TopologicalSpace.Opens.map f).obj U) ↦ pb (⇑f) (extend s.1) x.1 := by
    filter_upwards [((TopologicalSpace.Opens.map f).obj U).isOpen.mem_nhds hy] with z hz
      using heq hz
  rw [← d_congr h2, d_pb hf U.isOpen s.2.1 hy, pb_congr (β' := 0) (s.2.2 hC _ hy), pb_zero]

/-- Pulling back forms over `U ⊆ N` to `f⁻¹ U`. -/
private noncomputable def pbSections {k : ℕ} {C : Prop} (U : TopologicalSpace.Opens (TopCat.of N)) :
    formSections V N F k C U →+ formSections V M F k C ((TopologicalSpace.Opens.map f).obj U) where
  toFun s := ⟨fun x ↦ pb (⇑f) (extend s.1) x.1, pred_pb f hf s⟩
  map_zero' := Subtype.ext <| funext fun x ↦ by
    show pb (⇑f) (extend (0 : ∀ x : U, V [⋀^Fin k]→L[ℝ] F)) x.1 = 0
    rw [extend_zero]; exact pb_zero _ _
  map_add' s t := Subtype.ext <| funext fun x ↦ by
    show pb (⇑f) (extend (s.1 + t.1)) x.1 = pb (⇑f) (extend s.1) x.1 + pb (⇑f) (extend t.1) x.1
    rw [extend_add]; exact pb_add _ _ _ _

/-- Pulling back forms, as a morphism `𝒜ᵏ_N ⟶ f_* 𝒜ᵏ_M`. -/
private noncomputable def pbHom (k : ℕ) (C : Prop) :
    formSheaf V N F k C ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj (formSheaf V M F k C) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom (pbSections f hf U.unop)
     naturality := by
      intro U U' i
      ext s
      refine Subtype.ext (funext fun x ↦ ?_)
      change pb (⇑f) (extend fun y : U'.unop ↦ s.1 ⟨y.1, i.unop.le y.2⟩) x.1 =
        pb (⇑f) (extend s.1) x.1
      exact pb_congr (by
        rw [extend_apply (fun y : U'.unop ↦ s.1 ⟨y.1, i.unop.le y.2⟩) ⟨_, x.2⟩,
          extend_apply s.1 ⟨_, i.unop.le x.2⟩]) }⟩

private lemma pbHom_app_apply {k : ℕ} {C : Prop} (U : TopologicalSpace.Opens (TopCat.of N))
    (s : ToType ((formSheaf V N F k C).obj.obj (op U)))
    (x : (TopologicalSpace.Opens.map f).obj U) :
    ((pbHom f hf k C).hom.app (op U) s).1 x = pb (⇑f) (extend s.1) x.1 := rfl

/-- The pullback `f⁻¹ 𝒜ᵏ_N ⟶ 𝒜ᵏ_M`, adjoint to `pbHom`. -/
private noncomputable def pbPull (k : ℕ) (C : Prop) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (formSheaf V N F k C) ⟶ formSheaf V M F k C :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm
    (pbHom f hf k C)

private lemma closedIncl_pbHom (k : ℕ) :
    closedIncl V N F k ≫ pbHom f hf k False =
      pbHom f hf k True ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (closedIncl V M F k) :=
  rfl

private lemma dHom_pbHom (k : ℕ) (C : Prop) :
    dHom V N F k C ≫ pbHom f hf (k + 1) True =
      pbHom f hf k C ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (dHom V M F k C) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  ext s
  refine Subtype.ext (funext fun x ↦ ?_)
  change pb (⇑f) (extend fun y : U.unop ↦ d (extend s.1) y) x.1 =
    d (extend fun y : ((TopologicalSpace.Opens.map f).obj U.unop) ↦ pb (⇑f) (extend s.1) y.1) x.1
  have h1 : pb (⇑f) (extend fun y : U.unop ↦ d (extend s.1) y) x.1 =
      pb (⇑f) (d (extend s.1)) x.1 :=
    pb_congr (extend_apply (fun y : U.unop ↦ d (extend s.1) y) ⟨_, x.2⟩)
  have h2 : (extend fun y : ((TopologicalSpace.Opens.map f).obj U.unop) ↦
      pb (⇑f) (extend s.1) y.1) =ᶠ[𝓝 x.1] pb (⇑f) (extend s.1) := by
    filter_upwards [((TopologicalSpace.Opens.map f).obj U.unop).isOpen.mem_nhds x.2] with z hz
    exact extend_apply (fun y : ((TopologicalSpace.Opens.map f).obj U.unop) ↦
      pb (⇑f) (extend s.1) y.1) ⟨z, hz⟩
  rw [h1, d_congr h2, d_pb hf U.unop.isOpen s.2.1 x.2]

end PullbackSheaves

end Forms

end Poincare

/-- The constant sheaf `ℂ` on the analytic space of `Z`. -/
private noncomputable abbrev constC {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) :
    Sheaf (Opens.grothendieckTopology (analyticSpace sZ)) AddCommGrpCat.{0} :=
  (constantSheaf (Opens.grothendieckTopology (analyticSpace sZ)) AddCommGrpCat.{0}).obj
    (.of ℂ)

/-- Multiplication by `c` on the constant sheaf `ℂ`. -/
private noncomputable abbrev mulC {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (c : ℂ) :
    constC sZ ⟶ constC sZ :=
  (constantSheaf _ AddCommGrpCat.{0}).map
    (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))

section ConstPull

open Limits Forms TopologicalSpace
open scoped Manifold ContDiff Topology

/-- Transposing a commutative square through an adjunction. -/
private lemma map_comp_homEquiv_symm {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A B : C} {A' B' : D} (u : A ⟶ B) (v : A' ⟶ B')
    (φA : A ⟶ R.obj A') (φB : B ⟶ R.obj B') (h : u ≫ φB = φA ≫ R.map v) :
    L.map u ≫ (adj.homEquiv _ _).symm φB = (adj.homEquiv _ _).symm φA ≫ v := by
  rw [← Adjunction.homEquiv_naturality_left_symm, h, Adjunction.homEquiv_naturality_right_symm]

private lemma unit_comp_map_comp_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B : C} {Y : D} (u : A ⟶ B) (φ : B ⟶ R.obj Y) :
    adj.unit.app A ≫ R.map (L.map u ≫ (adj.homEquiv _ _).symm φ) = u ≫ φ := by
  rw [show adj.unit.app A ≫ R.map (L.map u ≫ (adj.homEquiv B Y).symm φ) =
      adj.homEquiv _ _ (L.map u ≫ (adj.homEquiv B Y).symm φ) by simp [Adjunction.homEquiv_unit],
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The adjoint of `M_Z ⟶ f⁻¹ M_W ⟶ f⁻¹ G ⟶ H` under the constant-sheaf adjunction, for
`u : M_W ⟶ G` and the adjoint of `v : G ⟶ f_* H`, is `u` on global sections followed by `v`. -/
private lemma homEquiv_constPullbackComparison_comp {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) {G : TopCat.Sheaf AddCommGrpCat.{0} W}
    {H : TopCat.Sheaf AddCommGrpCat.{0} Z}
    (u : (constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M ⟶ G)
    (v : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj H) :
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homEquiv
        M H (MMP.Analytic.constPullbackComparison f M ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map u ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm v) =
      (constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).homEquiv
        M G u ≫ v.hom.app (op ⊤) := by
  have k := congrArg (fun φ ↦ φ.hom.app (op (⊤ : Opens W)))
    (unit_comp_map_comp_homEquiv_symm
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f) u v)
  refine ((constantSheafAdj _ _ isTerminalTop).homEquiv_naturality_right _ _).trans ?_
  refine (eq_whisker (MMP.Analytic.homEquiv_constPullbackComparison f M) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ (constantSheafAdj _ _ isTerminalTop).unit.app M ≫ t) k).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ v.hom.app (op ⊤))
    ((constantSheafAdj _ _ isTerminalTop).homEquiv_unit M G u).symm)

/-- `homEquiv_constPullbackComparison_comp`, with the composite associated to the left. -/
private lemma homEquiv_constPullbackComparison_comp' {Z W : TopCat.{0}} (f : Z ⟶ W)
    (M : AddCommGrpCat.{0}) {G : TopCat.Sheaf AddCommGrpCat.{0} W}
    {H : TopCat.Sheaf AddCommGrpCat.{0} Z}
    (u : (constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj M ⟶ G)
    (v : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj H) :
    (constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0} isTerminalTop).homEquiv
        M H ((MMP.Analytic.constPullbackComparison f M ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map u) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm v) =
      (constantSheafAdj (Opens.grothendieckTopology W) AddCommGrpCat.{0} isTerminalTop).homEquiv
        M G u ≫ v.hom.app (op ⊤) :=
  (congrArg ((constantSheafAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}
    isTerminalTop).homEquiv M H) (Category.assoc _ _ _)).trans
      (homEquiv_constPullbackComparison_comp f M u v)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type} [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
  {N : Type} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℝ, V) ∞ N]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : IsSmoothMap V ⇑f)

private lemma constIncl_app_top_unit (a : F) :
    (constIncl V M F).hom.app (op ⊤)
        ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}
          Limits.isTerminalTop).unit.app (.of F) a) =
      (constToForm V M F).app (op ⊤) a :=
  ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.app (op (⊤ : Opens (TopCat.of M))))
    (toSheafify_constIncl V M F)) a

private lemma pbHom_constToForm (a : F) :
    (pbHom f hf 0 False).hom.app (op ⊤) ((constToForm V N F).app (op ⊤) a) =
      (constToForm V M F).app (op ⊤) a := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change pb (⇑f) (extend fun _ : (⊤ : Opens (TopCat.of N)) ↦
      ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) a) x.1 =
    ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) a
  refine (pb_congr (β' := fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) a)
    (extend_const_eqOn a (show _ ∈ ((⊤ : Opens (TopCat.of N)) : Set N) from trivial))).trans ?_
  exact zeroForm_ext (by simp [pb])

/-- Constant functions pull back to constant functions. -/
private lemma constPull_comp_constIncl :
    MMP.Analytic.constPullbackComparison f (.of F) ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (constIncl V N F) ≫
      pbPull f hf 0 False = constIncl V M F := by
  apply ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}
    Limits.isTerminalTop).homEquiv _ _).injective
  refine (homEquiv_constPullbackComparison_comp f (.of F) (constIncl V N F)
    (pbHom f hf 0 False)).trans ?_
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a
  change (pbHom f hf 0 False).hom.app (op ⊤) ((constIncl V N F).hom.app (op ⊤)
      ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of N)) AddCommGrpCat.{0}
          Limits.isTerminalTop).unit.app (.of F) a)) =
    (constIncl V M F).hom.app (op ⊤)
      ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}
          Limits.isTerminalTop).unit.app (.of F) a)
  rw [constIncl_app_top_unit, constIncl_app_top_unit, pbHom_constToForm]

private lemma constIncl_square :
    MMP.Analytic.pullbackConstComparison f (.of F) ≫ constIncl V M F =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map (constIncl V N F) ≫ pbPull f hf 0 False := by
  refine (congrArg (MMP.Analytic.pullbackConstComparison f (.of F) ≫ ·)
    (constPull_comp_constIncl f hf)).symm.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (eq_whisker
    (MMP.Analytic.pullbackConstComparison_comp_constPullbackComparison f (.of F)) _).trans
      (Category.id_comp _)

/-- The short complex `F → 𝒜⁰ → 𝒵¹`, in the category of sheaves on the space `M`. -/
private noncomputable abbrev constComplexTop (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : Type) [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold 𝓘(ℝ, V) ∞ M] (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  constComplex V M F

/-- The short complex `𝒵ᵏ → 𝒜ᵏ → 𝒵ᵏ⁺¹`, in the category of sheaves on the space `M`. -/
private noncomputable abbrev closedComplexTop (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (M : Type) [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold 𝓘(ℝ, V) ∞ M] (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (k : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  closedComplex V M F k

end ConstPull

/-- The pull-back of a two-form along a morphism of surfaces over `ℂ`. -/
private noncomputable abbrev formPull {Z Z' : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (sZ' : Z' ⟶ Spec (.of ℂ)) (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)) :
    (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤) :=
  (Scheme.Hom.relativeDifferentialFormsMap g sZ' sZ (𝟙 _) (by simp [hg]) 2).app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app ⊤ ω)

/-! ### Pulling back algebraic forms, on affine opens -/

section AlgebraicPullback

open KaehlerDifferential Stacks.AlgebraicGeometry.AffineOpenDeRham

universe u

variable {k : Type u} [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sX' : X' ⟶ Spec (.of k)) (g : X' ⟶ X) (hg : g ≫ sX = sX')

/-- An affine open, as an open with its affineness. -/
private theorem isAffineOpen_coe {Y : Scheme.{u}} (U : Y.affineOpens) : IsAffineOpen
    (U : Y.Opens) :=
  U.2

/-- Every open lies over the top open. -/
private theorem le_preimage_top {Y Y' : Scheme.{u}} (f : Y ⟶ Y') (U : Y.Opens) : U ≤ f ⁻¹ᵁ ⊤ := by
  simp

include hg in
/-- `k → Γ(X, W) → Γ(X', W')` is a scalar tower along `g^♯`. -/
private theorem isScalarTower_appLE {W : X.Opens} {W' : X'.Opens} (h : W' ≤ g ⁻¹ᵁ W) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    IsScalarTower k Γ(X, W) Γ(X', W') := by
  subst hg
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra (g ≫ sX) W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  exact (congrArg (fun t ↦ ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom)
    (Scheme.Hom.appLE_comp_appLE g sX ⊤ W W' (by simp) h)).symm

set_option maxRecDepth 20000 in
include hg in
/-- The pull-back of `d c₁ ∧ ⋯ ∧ d c_q`, restricted to `W'`, is `d (g^♯ c₁) ∧ ⋯ ∧ d (g^♯ c_q)`. -/
private theorem formsSectionsIso_hom_map_deRhamFormsPushforwardSections_ιMulti_d (q : ℕ)
    (W : X.affineOpens) (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (c : Fin q → Γ(X, W)) :
    (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _) (le_preimage_top sX' _) q).hom
        ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op
          (deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q
            ((formsSectionsIso sX (isAffineOpen_coe W) (isAffineOpen_top _)
                (le_preimage_top sX _) q).inv
              (exteriorPower.ιMulti Γ(X, W) q fun i ↦
                CommRingCat.KaehlerDifferential.d (c i))))) =
      exteriorPower.ιMulti Γ(X', W') q fun i ↦
        CommRingCat.KaehlerDifferential.d ((g.appLE W W' h).hom (c i)) := by
  have e1 := formsSectionsIso_inv_ιMulti_d sX (isAffineOpen_coe W) (isAffineOpen_top _)
    (le_preimage_top sX _) q c
  have e2 := Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft g sX sX' (𝟙 _)
    (by rw [hg, Category.comp_id]) (op (W : X.Opens)) q c
  have e3 := Stacks.GradedAlgebra.homogeneousProdLeft_naturality
    (Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra (homOfLE h).op q
    (fun i ↦ SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
      ((g.app W).hom (c i)))
  have e4 := formsSectionsIso_inv_ιMulti_d sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q fun i ↦ (g.appLE W W' h).hom (c i)
  have e5 : ∀ i, ((Scheme.Hom.deRhamAlgebras sX').exteriorPower 1).val.map (homOfLE h).op
      (SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
        ((g.app W).hom (c i))) =
      SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (W' : X'.Opens))
        ((g.appLE W W' h).hom (c i)) := fun i ↦
    SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras sX') (homOfLE h).op _
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op (deRhamFormsPushforwardSections g sX sX' (𝟙 _)
        (by rw [hg, Category.comp_id]) q t))) e1).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op t)) e2).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom t) e3).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom
      ((Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op (W' : X'.Opens)) q t)) (funext e5)).trans ?_
  refine (congrArg (formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom e4.symm).trans ?_
  exact Iso.inv_hom_id_apply _ _

include hg in
/-- The pull-back of forms over `W`, restricted to `W'`, read through the affine comparisons and
the change of base `kaehlerSpecEquiv`. -/
private noncomputable def pullAffine (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))) :
    letI := MMP.Mori.sectionAlgebra sX' W'
    ⋀[Γ(X', W')]^q (Ω[Γ(X', W')⁄k]) :=
  letI := MMP.Mori.sectionAlgebra sX' W'
  exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX' W').toLinearMap
    ((formsSectionsIso sX' (isAffineOpen_coe W') (isAffineOpen_top _)
        (le_preimage_top sX' _) q).hom
      ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op
        (deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q
          ((formsSectionsIso sX (isAffineOpen_coe W) (isAffineOpen_top _)
              (le_preimage_top sX _) q).inv y))))

/-- `pullAffine` agrees with the map of Kähler forms at `0`. -/
private theorem pullAffine_zero (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
      pullAffine sX sX' g hg q W W' h 0 =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap 0) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  unfold pullAffine
  rw [map_zero, show deRhamFormsPushforwardSections g sX sX' (𝟙 _)
      (by rw [hg, Category.comp_id]) q 0 = 0 from
    map_zero (((Scheme.Hom.deRhamFormsPushforwardHom g sX sX' (𝟙 _)
      (by rw [hg, Category.comp_id])).app (q : ℤ)).val.app (op (W : X.Opens))).hom]
  simp only [map_zero]

/-- `pullAffine` is additive. -/
private theorem pullAffine_add (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (y z : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))) :
    pullAffine sX sX' g hg q W W' h (y + z) =
      pullAffine sX sX' g hg q W W' h y + pullAffine sX sX' g hg q W W' h z := by
  unfold pullAffine
  simp only [map_add, deRhamFormsPushforwardSections_add]

/-- `pullAffine` agrees with the map of Kähler forms on sums of elements where it agrees. -/
private theorem pullAffine_add_eq (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ y z : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) →
      pullAffine sX sX' g hg q W W' h z = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap z) →
      pullAffine sX sX' g hg q W W' h (y + z) = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (y + z)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ y z hy hz
  have hG : mapExteriorPower k Γ(X, W) Γ(X', W') q
      (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (y + z)) =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) +
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap z) := by
    rw [map_add (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap) y z,
      map_add (mapExteriorPower k Γ(X, W) Γ(X', W') q)]
  rw [pullAffine_add, hG]
  exact congrArg₂ _ hy hz

/-- `pullAffine` agrees with the map of Kähler forms on multiples of elements where it agrees. -/
private theorem pullAffine_smul_eq (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ (b : Γ(X, W))
      (y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) →
      pullAffine sX sX' g hg q W W' h (b • y) = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (b • y)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ b y hy
  unfold pullAffine at hy ⊢
  simp only [map_smul, deRhamFormsPushforwardSections_smul, Scheme.Modules.map_smul]
  rw [hy]
  exact (algebraMap_smul Γ(X', W') b _).symm

/-- `pullAffine` agrees with the map of Kähler forms on wedges of differentials. -/
private theorem pullAffine_ιMulti_d (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')], ∀ c : Fin q → Γ(X, W),
      pullAffine sX sX' g hg q W W' h (exteriorPower.ιMulti Γ(X, W) q fun i ↦
          CommRingCat.KaehlerDifferential.d (c i)) =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap
            (exteriorPower.ιMulti Γ(X, W) q fun i ↦ CommRingCat.KaehlerDifferential.d (c i))) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ c
  unfold pullAffine
  rw [formsSectionsIso_hom_map_deRhamFormsPushforwardSections_ιMulti_d sX sX' g hg q W W' h c]
  simp only [exteriorPower.map_apply_ιMulti, Function.comp_def, LinearEquiv.coe_coe,
    MMP.DeRham.kaehlerBaseEquiv_d, mapExteriorPower_ιMulti, map_D]
  rfl

/-- The pull-back of forms, restricted to `W'`, read through the affine comparisons. -/
private theorem pullAffine_eq (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
        (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  exact eq_of_smul_ιMulti_d (sX.appLE ⊤ W (le_preimage_top sX _)) q _ _
    (pullAffine_zero sX sX' g hg q W W' h) (pullAffine_add_eq sX sX' g hg q W W' h)
    (pullAffine_smul_eq sX sX' g hg q W W' h) (pullAffine_ιMulti_d sX sX' g hg q W W' h)

set_option maxRecDepth 20000 in
include hg in
/-- **The pull-back of a form on an affine open, restricted to an affine open, is the map of
Kähler forms along `g^♯`.** -/
private theorem formsAlgEquiv_map_deRhamFormsPushforwardSections (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (η : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    MMP.DeRham.formsAlgEquiv sX' q W' ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE h).op (deRhamFormsPushforwardSections g sX sX' (𝟙 _)
          (by rw [hg, Category.comp_id]) q η)) =
      mapExteriorPower k Γ(X, W) Γ(X', W') q (MMP.DeRham.formsAlgEquiv sX q W η) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  obtain ⟨y, rfl⟩ : ∃ y, (formsSectionsIso sX (isAffineOpen_coe W) (isAffineOpen_top _)
      (le_preimage_top sX _) q).inv y = η :=
    ⟨(formsSectionsIso sX (isAffineOpen_coe W) (isAffineOpen_top _)
      (le_preimage_top sX _) q).hom η, by simp⟩
  rw [MMP.DeRham.formsAlgEquiv_apply, MMP.DeRham.formsAlgEquiv_apply, Iso.inv_hom_id_apply]
  have e := pullAffine_eq sX sX' g hg q W W' h y
  unfold pullAffine at e
  refine Eq.trans ?_ e
  congr!

include hg in
/-- **The pull-back of a global form, on affine opens, is the map of Kähler forms along `g^♯`.** -/
private theorem formsAlgEquiv_res_pullback (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), ⊤)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    MMP.DeRham.formsAlgEquiv sX' q W' ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (le_top : (W' : X'.Opens) ≤ ⊤)).op
        ((Scheme.Hom.relativeDifferentialFormsMap g sX sX' (𝟙 _) (by rw [hg, Category.comp_id])
          (q : ℤ)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app ⊤ ω))) =
      mapExteriorPower k Γ(X, W) Γ(X', W') q (MMP.DeRham.formsAlgEquiv sX q W
        ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  rw [← formsAlgEquiv_map_deRhamFormsPushforwardSections sX sX' g hg q W W' h]
  congr 1
  have hΦ : ∀ η : Γ(sX.relativeDifferentialForms (q : ℤ), W),
      deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q η =
        Scheme.Hom.relativeDifferentialFormsPullback g sX sX' (𝟙 _)
          (by rw [hg, Category.comp_id]) (q : ℤ) W η := by
    intro η
    rw [deRhamFormsPushforwardSections_apply, ← Scheme.Hom.homEquiv_relativeDifferentialFormsMap]
    rfl
  have e := Scheme.Hom.relativeDifferentialFormsPullback_map g sX sX' (𝟙 _)
    (by rw [hg, Category.comp_id]) (q : ℤ) (le_top : (W : X.Opens) ≤ ⊤) ω
  rw [hΦ, e, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end AlgebraicPullback

/-! ### The class of a two-form -/

section ExtClass

open Forms MMP.Analytic
open scoped Manifold

/-- If the composite of `w` with the extension classes of `0 → A → B → Z → 0` and
`0 → Z → B' → Z' → 0` vanishes and `Ext¹(X, B) = 0`, then `w` lifts through `B' → Z'`. -/
private theorem exists_comp_eq_of_comp_extClass_comp_extClass_eq_zero {C : Type*} [Category C]
    [Abelian C] [HasExt C] (X : C) {A B Z B' Z' : C} {f₁ : A ⟶ B} {g₁ : B ⟶ Z}
    {w₁ : f₁ ≫ g₁ = 0} {f₂ : Z ⟶ B'} {g₂ : B' ⟶ Z'} {w₂ : f₂ ≫ g₂ = 0}
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact) (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact)
    (hB : ∀ e : Ext X B 1, e = 0) (w : Ext X Z' 0)
    (hw : (w.comp h₂.extClass (zero_add 1)).comp h₁.extClass (by norm_num : 1 + 1 = 2) = 0) :
    ∃ v : Ext X B' 0, v.comp (Ext.mk₀ g₂) (add_zero 0) = w := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ X h₁ (w.comp h₂.extClass (zero_add 1))
    (by norm_num : 1 + 1 = 2) hw
  have hu : w.comp h₂.extClass (zero_add 1) = 0 := by
    rw [← hx₂, hB x₂, Ext.zero_comp]
  exact Ext.covariant_sequence_exact₃ X h₂ w (zero_add 1) hu

/-- Naturality of a two-step connecting composite: endomorphisms of two short exact sequences
`0 → A → B → Z → 0` and `0 → Z → B' → Z' → 0`, agreeing on `Z`, commute with
`w ↦ (w ∘ δ₂) ∘ δ₁`. -/
private theorem comp_extClass_comp_extClass_naturality {C : Type*} [Category C]
    [Abelian C] [HasExt C] {X A B Z B' Z' : C} {f₁ : A ⟶ B} {g₁ : B ⟶ Z}
    {w₁ : f₁ ≫ g₁ = 0} {f₂ : Z ⟶ B'} {g₂ : B' ⟶ Z'} {w₂ : f₂ ≫ g₂ = 0}
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact) (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact)
    (a : A ⟶ A) (b : B ⟶ B) (z : Z ⟶ Z) (b' : B' ⟶ B') (z' : Z' ⟶ Z')
    (ha : f₁ ≫ b = a ≫ f₁) (hb : g₁ ≫ z = b ≫ g₁) (hz : f₂ ≫ b' = z ≫ f₂)
    (hb' : g₂ ≫ z' = b' ≫ g₂) (w : Ext X Z' 0) :
    ((w.comp (Ext.mk₀ z') (add_zero 0)).comp h₂.extClass (zero_add 1)).comp h₁.extClass
        (by norm_num : 1 + 1 = 2) =
      ((w.comp h₂.extClass (zero_add 1)).comp h₁.extClass (by norm_num : 1 + 1 = 2)).comp
        (Ext.mk₀ a) (add_zero 2) := by
  have n₁ := h₁.extClass_naturality h₁
    { τ₁ := a, τ₂ := b, τ₃ := z, comm₁₂ := ha.symm, comm₂₃ := hb.symm }
  have n₂ := h₂.extClass_naturality h₂
    { τ₁ := z, τ₂ := b', τ₃ := z', comm₁₂ := hz.symm, comm₂₃ := hb'.symm }
  simp only at n₁ n₂
  rw [Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by norm_num), ← n₂,
    ← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by norm_num),
    Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by norm_num), ← n₁,
    ← Ext.comp_assoc _ _ _ (show (1:ℕ) + 1 = 2 from rfl) (add_zero 1)
      (show (1:ℕ) + 1 + 0 = 2 from rfl)]

/-- Naturality of a two-step connecting composite for morphisms `φ₁`, `φ₂` from a pair of short
exact sequences `0 → A₀ → B₀ → Z₀ → 0`, `0 → Z₀ → B₀' → Z₀' → 0` to a pair
`0 → A → B → Z → 0`, `0 → Z → B' → Z' → 0` agreeing on `Z₀ ⟶ Z`. -/
private theorem comp_extClass_comp_extClass_naturality_of_hom {C : Type*} [Category C]
    [Abelian C] [HasExt C] {X A B Z B' Z' A₀ B₀ Z₀ B₀' Z₀' : C}
    {f₁ : A ⟶ B} {g₁ : B ⟶ Z} {w₁ : f₁ ≫ g₁ = 0} {f₂ : Z ⟶ B'} {g₂ : B' ⟶ Z'}
    {w₂ : f₂ ≫ g₂ = 0}
    {f₀₁ : A₀ ⟶ B₀} {g₀₁ : B₀ ⟶ Z₀} {w₀₁ : f₀₁ ≫ g₀₁ = 0} {f₀₂ : Z₀ ⟶ B₀'}
    {g₀₂ : B₀' ⟶ Z₀'} {w₀₂ : f₀₂ ≫ g₀₂ = 0}
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact) (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact)
    (h₀₁ : (ShortComplex.mk f₀₁ g₀₁ w₀₁).ShortExact)
    (h₀₂ : (ShortComplex.mk f₀₂ g₀₂ w₀₂).ShortExact)
    (φ₁ : ShortComplex.mk f₀₁ g₀₁ w₀₁ ⟶ ShortComplex.mk f₁ g₁ w₁)
    (φ₂ : ShortComplex.mk f₀₂ g₀₂ w₀₂ ⟶ ShortComplex.mk f₂ g₂ w₂) (hφ : φ₁.τ₃ = φ₂.τ₁)
    (w : Ext X Z₀' 0) :
    ((w.comp (Ext.mk₀ φ₂.τ₃) (add_zero 0)).comp h₂.extClass (zero_add 1)).comp h₁.extClass
        (by norm_num : 1 + 1 = 2) =
      ((w.comp h₀₂.extClass (zero_add 1)).comp h₀₁.extClass (by norm_num : 1 + 1 = 2)).comp
        (Ext.mk₀ φ₁.τ₁) (add_zero 2) := by
  have n₁ := h₀₁.extClass_naturality h₁ φ₁
  have n₂ := h₀₂.extClass_naturality h₂ φ₂
  rw [← hφ] at n₂
  rw [Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by norm_num), ← n₂,
    ← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by norm_num),
    Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by norm_num), ← n₁,
    ← Ext.comp_assoc _ _ _ (show (1:ℕ) + 1 = 2 from rfl) (add_zero 1)
      (show (1:ℕ) + 1 + 0 = 2 from rfl)]

/-- An exact functor carries a two-step connecting composite to the two-step connecting
composite of the image sequences. -/
private theorem mapExactFunctor_comp_extClass_comp_extClass {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [HasExt C] [HasExt D] (P : C ⥤ D) [P.Additive]
    [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P] {X A B Z B' Z' : C}
    {f₁ : A ⟶ B} {g₁ : B ⟶ Z} {w₁ : f₁ ≫ g₁ = 0} {f₂ : Z ⟶ B'} {g₂ : B' ⟶ Z'}
    {w₂ : f₂ ≫ g₂ = 0}
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact) (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact)
    (w : Ext X Z' 0) :
    ((w.comp h₂.extClass (zero_add 1)).comp h₁.extClass
        (by norm_num : 1 + 1 = 2)).mapExactFunctor P =
      ((w.mapExactFunctor P).comp (h₂.map_of_exact P).extClass (zero_add 1)).comp
        (h₁.map_of_exact P).extClass (by norm_num : 1 + 1 = 2) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_extClass]

/-- Composing a two-step composite starting in degree `0` with a retraction pair. -/
private theorem comp_comp_extClass_eq_of_comp_eq_id {C : Type*} [Category C] [Abelian C]
    [HasExt C] {X Y Y₂ Y₁ Y₀ T : C} (a : X ⟶ Y) (m : Y ⟶ Y₂) (δ₂ : Ext Y₂ Y₁ 1)
    (δ₁ : Ext Y₁ Y₀ 1) (β : Y₀ ⟶ T) (α' : T ⟶ Y₀) (hβ : β ≫ α' = 𝟙 Y₀) :
    (Ext.mk₀ a).comp (((Ext.mk₀ m).comp δ₂ (zero_add 1)).comp δ₁ (by norm_num : 1 + 1 = 2))
        (zero_add 2) =
      ((((Ext.mk₀ (a ≫ m)).comp δ₂ (zero_add 1)).comp δ₁ (by norm_num : 1 + 1 = 2)).comp
        (Ext.mk₀ β) (add_zero 2)).comp (Ext.mk₀ α') (add_zero 2) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hβ, Ext.comp_mk₀_id,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ (zero_add 1) (by norm_num : 1 + 1 = 2) (by norm_num)).symm

/-- `H.equiv₀` of a morphism from the constant sheaf `ℤ`: its adjoint at `1`. -/
private lemma equiv₀_mk₀ {X : TopCat.{0}} {G : Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}}
    (φ : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (.of (ULift ℤ)) ⟶ G) :
    Sheaf.H.equiv₀ G Limits.isTerminalTop (Ext.mk₀ φ) =
      (constantSheafAdj _ _ Limits.isTerminalTop).homEquiv _ _ φ (ULift.up 1) := by
  rw [show Ext.mk₀ φ = Ext.addEquiv₀.symm φ from rfl]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

/-- The global section of `ℤ_Z ⟶ f⁻¹ ℤ_W ⟶ f⁻¹ G ⟶ H` is the image under `v : G ⟶ f_* H` of
the global section of `u : ℤ_W ⟶ G`. -/
private lemma equiv₀_mk₀_constPullbackComparison_comp {Z W : TopCat.{0}} (f : Z ⟶ W)
    {G : Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}}
    {H : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}}
    (u : (constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{0}).obj
      (.of (ULift ℤ)) ⟶ G)
    (v : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj H) :
    Sheaf.H.equiv₀ H Limits.isTerminalTop
        (Ext.mk₀ ((MMP.Analytic.constPullbackComparison f (.of (ULift ℤ)) ≫
          (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map u) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).homEquiv _ _).symm v)) =
      v.hom.app (op ⊤) (Sheaf.H.equiv₀ G Limits.isTerminalTop (Ext.mk₀ u)) := by
  rw [equiv₀_mk₀, equiv₀_mk₀]
  have := ConcreteCategory.congr_hom
    (homEquiv_constPullbackComparison_comp' f (.of (ULift ℤ)) u v) (ULift.up 1)
  exact this.trans (ConcreteCategory.comp_apply _ _ _)

variable {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sZ]

/-- The real smooth structure of the complex surface `Z^an`. -/
private noncomputable abbrev realManifold :
    IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞) (ComplexPoints sZ) :=
  StratifiedFlows.isManifold_real_of_complex

attribute [local instance] realManifold

/-- The sheaf of smooth (`C = False`) or closed (`C = True`) complex `k`-forms on `Z^an`. -/
private noncomputable abbrev forms (k : ℕ) (C : Prop) :=
  formSheaf (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ k C

/-! ### The analytic two-form of an algebraic two-form -/

open ContinuousAlternatingMap in
/-- The wedge product of two `ℂ`-valued real one-forms. -/
private noncomputable def wedge (ℓ₁ ℓ₂ : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℂ) :
    EuclideanSpace ℂ (Fin 2) [⋀^Fin 2]→L[ℝ] ℂ :=
  alternatizeUncurryFin (ℓ₁.smulRight
    (ContinuousAlternatingMap.ofSubsingleton ℝ (EuclideanSpace ℂ (Fin 2)) ℂ (0 : Fin 1) ℓ₂))

open ContinuousAlternatingMap in
private lemma wedge_apply (ℓ₁ ℓ₂ : EuclideanSpace ℂ (Fin 2) →L[ℝ] ℂ)
    (v : Fin 2 → EuclideanSpace ℂ (Fin 2)) :
    wedge ℓ₁ ℓ₂ v = ℓ₁ (v 0) * ℓ₂ (v 1) - ℓ₁ (v 1) * ℓ₂ (v 0) := by
  simp [wedge, alternatizeUncurryFin_apply, Fin.sum_univ_two, Fin.removeNth]
  ring

/-- The holomorphic volume form `dz₁ ∧ dz₂` of `ℂ²`, as a real two-form. -/
private noncomputable def detC : EuclideanSpace ℂ (Fin 2) [⋀^Fin 2]→L[ℝ] ℂ :=
  wedge ((EuclideanSpace.proj (𝕜 := ℂ) 0).restrictScalars ℝ)
    ((EuclideanSpace.proj (𝕜 := ℂ) 1).restrictScalars ℝ)

private lemma detC_apply (v : Fin 2 → EuclideanSpace ℂ (Fin 2)) :
    detC v = v 0 0 * v 1 1 - v 1 0 * v 0 1 := by
  simp [detC, wedge_apply]

open Classical in
/-- the realization of a regular function -/
private noncomputable def fan {sZ : Z ⟶ Spec (.of ℂ)} (U : Z.Opens) (f : Γ(Z, U)) :
    ComplexPoints sZ → ℂ :=
  fun y ↦ if h : y ∈ chart U then evalHom U ⟨y, h⟩ f else 0

private lemma fan_of_mem {sZ : Z ⟶ Spec (.of ℂ)} {U : Z.Opens} (f : Γ(Z, U))
    {y : ComplexPoints sZ} (h : y ∈ chart U) :
    fan U f y = evalHom U ⟨y, h⟩ f := by simp [fan, h]

/-- regular functions are holomorphic in atlas charts -/
private theorem analyticOnNhd_fan
    {e : OpenPartialHomeomorph (ComplexPoints sZ) (EuclideanSpace ℂ (Fin 2))}
    (he : e ∈ atlas (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ)) (U : Z.Opens) (f : Γ(Z, U)) :
    AnalyticOnNhd ℂ (fan U f ∘ e.symm) (e.target ∩ e.symm ⁻¹' chart U) := by
  obtain ⟨c, rfl⟩ := he
  obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd U f
  set L := (EuclideanSpace.equiv (Fin 2) ℂ).symm
  have hS : IsOpen ((c.toChart L).target ∩ (c.toChart L).symm ⁻¹' chart U) :=
    (c.toChart L).isOpen_inter_preimage_symm (isOpen_chart sZ U)
  have hsymm : ∀ v, (c.toChart L).symm v = c.toOpenPartialHomeomorph.symm (L.symm v) := by
    intro v; simp [EtaleCoordinateChart.toChart]
  have htg : ∀ v ∈ (c.toChart L).target, L.symm v ∈ c.toOpenPartialHomeomorph.target := by
    intro v hv; simpa [EtaleCoordinateChart.toChart] using hv
  have key : ∀ v ∈ (c.toChart L).target ∩ (c.toChart L).symm ⁻¹' chart U,
      (fan U f ∘ (c.toChart L).symm) v = (G ∘ L.symm) v := by
    intro v hv
    have hv1 := htg v hv.1
    have hv2 : (c.toChart L).symm v ∈ chart U := hv.2
    simp only [Function.comp_apply]
    have hW : (c.toChart L).symm v ∈ c.W := by
      rw [hsymm]; exact c.toOpenPartialHomeomorph_symm_mem hv1
    rw [fan_of_mem f hv2, evalHom_apply, hGe _ hW hv2, hsymm,
      c.toOpenPartialHomeomorph_apply_symm hv1]
  have hGL : AnalyticOnNhd ℂ (G ∘ L.symm)
      ((c.toChart L).target ∩ (c.toChart L).symm ⁻¹' chart U) := by
    intro v hv
    refine (hG _ ⟨htg v hv.1, ?_⟩).comp (L.symm.analyticAt v)
    have := hv.2
    simp only [Set.mem_preimage, hsymm] at this
    exact this
  exact hGL.congr hS (fun v hv ↦ (key v hv).symm)

local notation "𝔼" => EuclideanSpace ℂ (Fin 2)

private lemma isOpen_target_inter_chart (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼)
    (U : Z.Opens) : IsOpen (e.target ∩ e.symm ⁻¹' chart U) :=
  e.isOpen_inter_preimage_symm (isOpen_chart sZ U)

/-- `d f^an` at `v`, read in the chart `e`. -/
private noncomputable def dfan (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼) (U : Z.Opens)
    (v : 𝔼) (f : Γ(Z, U)) : 𝔼 →L[ℂ] ℂ :=
  fderiv ℂ (fan U f ∘ e.symm) v

private lemma fan_eventuallyEq {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {U : Z.Opens}
    {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) {F G : ComplexPoints sZ → ℂ}
    (h : ∀ y' ∈ chart U, F y' = G y') : F ∘ e.symm =ᶠ[nhds v] G ∘ e.symm := by
  filter_upwards [(isOpen_target_inter_chart sZ e U).mem_nhds hv] with w hw
  exact h _ hw.2

private lemma differentiableAt_fan {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {U : Z.Opens} {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (f : Γ(Z, U)) :
    DifferentiableAt ℂ (fan U f ∘ e.symm) v :=
  (analyticOnNhd_fan sZ he U f v hv).differentiableAt

private lemma dfan_add {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {U : Z.Opens} {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (f g : Γ(Z, U)) :
    dfan sZ e U v (f + g) = dfan sZ e U v f + dfan sZ e U v g := by
  have h := fan_eventuallyEq sZ hv (F := fan U (f + g)) (G := fan U f + fan U g) (fun y' hy' ↦ by
    simp [fan_of_mem _ hy'])
  unfold dfan
  rw [h.fderiv_eq]
  exact fderiv_add (differentiableAt_fan sZ he hv f) (differentiableAt_fan sZ he hv g)

private lemma dfan_mul {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {U : Z.Opens} {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (f g : Γ(Z, U)) :
    dfan sZ e U v (f * g) = evalHom U ⟨_, hv.2⟩ f • dfan sZ e U v g +
      evalHom U ⟨_, hv.2⟩ g • dfan sZ e U v f := by
  have h := fan_eventuallyEq sZ hv (F := fan U (f * g)) (G := fan U f * fan U g) (fun y' hy' ↦ by
    simp [fan_of_mem _ hy'])
  unfold dfan
  rw [h.fderiv_eq]
  have := fderiv_mul (differentiableAt_fan sZ he hv f) (differentiableAt_fan sZ he hv g)
  simp only [Function.comp_apply] at this
  rw [fan_of_mem _ hv.2, fan_of_mem _ hv.2] at this
  exact this

private lemma dfan_baseRingHom {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {U : Z.Opens}
    {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (a : ℂ) :
    dfan sZ e U v (baseRingHom sZ U a) = 0 := by
  have h := fan_eventuallyEq sZ hv (F := fan U (baseRingHom sZ U a)) (G := fun _ ↦ a)
    (fun y' hy' ↦ by rw [fan_of_mem _ hy', evalHom_baseRingHom])
  unfold dfan
  rw [h.fderiv_eq]
  exact fderiv_const_apply a

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma algebraMap_eq_baseRingHom (U : Z.Opens) (a : ℂ) :
    letI := MMP.Mori.sectionAlgebra sZ U
    algebraMap ℂ Γ(Z, U) a = baseRingHom sZ U a := rfl

/-- The `2 × 2` determinant of two `ℂ`-linear forms on `ℂ²`. -/
private noncomputable def det2 (ℓ₁ ℓ₂ : 𝔼 →L[ℂ] ℂ) : ℂ :=
  ℓ₁ (EuclideanSpace.single 0 1) * ℓ₂ (EuclideanSpace.single 1 1) -
    ℓ₁ (EuclideanSpace.single 1 1) * ℓ₂ (EuclideanSpace.single 0 1)

/-- `Γ(Z, U)` acts on a complex vector space through evaluation at `y`. -/
private noncomputable abbrev ptModule {sZ : Z ⟶ Spec (.of ℂ)} (U : Z.Opens) (y : chart (sX := sZ) U)
    (N : Type*) [AddCommGroup N] [Module ℂ N] : Module Γ(Z, U) N :=
  Module.compHom N (evalHom U y)

private lemma ptModule_smul {sZ : Z ⟶ Spec (.of ℂ)} (U : Z.Opens) (y : chart (sX := sZ) U)
    {N : Type*} [AddCommGroup N] [Module ℂ N] (a : Γ(Z, U)) (n : N) :
    letI := ptModule U y N
    a • n = evalHom U y a • n := rfl

private lemma isScalarTower_ptModule {sZ : Z ⟶ Spec (.of ℂ)} (U : Z.Opens) (y : chart (sX := sZ) U)
    (N : Type*) [AddCommGroup N] [Module ℂ N] :
    letI := MMP.Mori.sectionAlgebra sZ U
    letI := ptModule U y N
    IsScalarTower ℂ Γ(Z, U) N := by
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U y N
  refine ⟨fun c a n ↦ ?_⟩
  rw [ptModule_smul, ptModule_smul, Algebra.smul_def, map_mul, mul_smul,
    algebraMap_eq_baseRingHom, evalHom_baseRingHom]

/-- `f ↦ d f^an` at `v` in the chart `e`, as a derivation. -/
private noncomputable def dfanDer {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) :
    letI := MMP.Mori.sectionAlgebra sZ U
    letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
    Derivation ℂ Γ(Z, U) (𝔼 →L[ℂ] ℂ) :=
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  Derivation.mk'
    { toFun := dfan sZ e U v
      map_add' := dfan_add sZ he hv
      map_smul' := fun c f ↦ by
        rw [Algebra.smul_def, dfan_mul sZ he hv, algebraMap_eq_baseRingHom,
          dfan_baseRingHom sZ hv, smul_zero, add_zero, evalHom_baseRingHom]
        rfl }
    (fun f g ↦ by
      change dfan sZ e U v (f * g) = _
      rw [dfan_mul sZ he hv]
      rfl)

/-- `d f^an` at `v` in the chart `e`, on Kähler differentials. -/
private noncomputable def dfanLin {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) :
    letI := MMP.Mori.sectionAlgebra sZ U
    letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
    Ω[Γ(Z, U)⁄ℂ] →ₗ[Γ(Z, U)] (𝔼 →L[ℂ] ℂ) :=
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  haveI := isScalarTower_ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  (dfanDer sZ he U hv).liftKaehlerDifferential

private lemma dfanLin_D {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (f : Γ(Z, U)) :
    letI := MMP.Mori.sectionAlgebra sZ U
    dfanLin sZ he U hv (KaehlerDifferential.D ℂ Γ(Z, U) f) = dfan sZ e U v f := by
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  haveI := isScalarTower_ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  exact (dfanDer sZ he U hv).liftKaehlerDifferential_comp_D f

private lemma det2_add_left (ℓ₁ ℓ₁' ℓ₂ : 𝔼 →L[ℂ] ℂ) :
    det2 (ℓ₁ + ℓ₁') ℓ₂ = det2 ℓ₁ ℓ₂ + det2 ℓ₁' ℓ₂ := by simp [det2]; ring
private lemma det2_add_right (ℓ₁ ℓ₂ ℓ₂' : 𝔼 →L[ℂ] ℂ) :
    det2 ℓ₁ (ℓ₂ + ℓ₂') = det2 ℓ₁ ℓ₂ + det2 ℓ₁ ℓ₂' := by simp [det2]; ring
private lemma det2_smul_left (c : ℂ) (ℓ₁ ℓ₂ : 𝔼 →L[ℂ] ℂ) :
    det2 (c • ℓ₁) ℓ₂ = c * det2 ℓ₁ ℓ₂ := by simp [det2]; ring
private lemma det2_smul_right (c : ℂ) (ℓ₁ ℓ₂ : 𝔼 →L[ℂ] ℂ) :
    det2 ℓ₁ (c • ℓ₂) = c * det2 ℓ₁ ℓ₂ := by simp [det2]; ring
private lemma det2_self (ℓ : 𝔼 →L[ℂ] ℂ) : det2 ℓ ℓ = 0 := by simp [det2]; ring

/-- The determinant of `(φ v₀, φ v₁)` as an alternating map, for a linear `φ`. -/
private noncomputable def det2Alt {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module A ℂ] (hA : ∀ (a : A) (z : ℂ), a • z = (a • (1 : ℂ)) * z)
    [Module A (𝔼 →L[ℂ] ℂ)]
    (hA' : ∀ (a : A) (ℓ : 𝔼 →L[ℂ] ℂ), a • ℓ = (a • (1 : ℂ)) • ℓ)
    (φ : M →ₗ[A] (𝔼 →L[ℂ] ℂ)) : M [⋀^Fin 2]→ₗ[A] ℂ where
  toFun v := det2 (φ (v 0)) (φ (v 1))
  map_update_add' := by
    intro _ m i x y
    fin_cases i
    · simp [det2_add_left]
    · simp [det2_add_right]
  map_update_smul' := by
    intro _ m i a x
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Function.update_self, ne_eq, zero_ne_one,
        not_false_eq_true, Function.update_of_ne, map_smul]
      rw [hA' a, det2_smul_left, hA a (det2 _ _)]
      simp [Function.update_apply]
    · simp only [Fin.mk_one, Fin.isValue, Function.update_self, ne_eq, one_ne_zero,
        not_false_eq_true, Function.update_of_ne, map_smul]
      rw [hA' a, det2_smul_right, hA a (det2 _ _)]
      simp [Function.update_apply]
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at hv ⊢; rw [hv, det2_self]
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta] at hv ⊢; rw [hv, det2_self]
    · exact absurd rfl hij

/-- The coefficient at `v`, in the chart `e`, of the analytic two-form of an algebraic two-form
on `U`. -/
private noncomputable def coeffLin {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) :
    letI := MMP.Mori.sectionAlgebra sZ U
    letI := ptModule U ⟨_, hv.2⟩ ℂ
    ⋀[Γ(Z, U)]^2 (Ω[Γ(Z, U)⁄ℂ]) →ₗ[Γ(Z, U)] ℂ :=
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ ℂ
  letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  exteriorPower.alternatingMapLinearEquiv
    (det2Alt (fun a z ↦ by simp [ptModule_smul]) (fun a ℓ ↦ by simp [ptModule_smul])
      (dfanLin sZ he U hv))

private lemma coeffLin_ιMulti {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (w : Fin 2 → Γ(Z, U)) :
    letI := MMP.Mori.sectionAlgebra sZ U
    coeffLin sZ he U hv (exteriorPower.ιMulti _ 2 fun i ↦ KaehlerDifferential.D ℂ Γ(Z, U) (w i)) =
      det2 (dfan sZ e U v (w 0)) (dfan sZ e U v (w 1)) := by
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ ℂ
  letI := ptModule U ⟨_, hv.2⟩ (𝔼 →L[ℂ] ℂ)
  unfold coeffLin
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change det2 (dfanLin sZ he U hv _) (dfanLin sZ he U hv _) = _
  simp [dfanLin_D]

private lemma coeffLin_smul {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (a : Γ(Z, U)) x :
    letI := MMP.Mori.sectionAlgebra sZ U
    coeffLin sZ he U hv (a • x) = evalHom U ⟨_, hv.2⟩ a * coeffLin sZ he U hv x := by
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := ptModule U ⟨_, hv.2⟩ ℂ
  rw [map_smul]
  rfl

open scoped ContDiff in
/-- Transition maps of the étale atlas are holomorphic. -/
private lemma differentiableAt_trans {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼}
    (hv : v ∈ (e.symm.trans e').source) : DifferentiableAt ℂ (e.symm.trans e') v := by
  have h := (contDiffGroupoid ∞ 𝓘(ℂ, 𝔼)).compatible he he'
  have h' := (mem_groupoid_of_pregroupoid.mp h).1
  have hc : ContDiffOn ℂ ∞ (e.symm.trans e') (e.symm.trans e').source := by
    simpa [contDiffPregroupoid] using h'
  exact (hc.contDiffAt ((e.symm.trans e').open_source.mem_nhds hv)).differentiableAt (by simp)

private lemma mem_source_trans {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {v : 𝔼}
    (hv : v ∈ e.target) (hv' : e.symm v ∈ e'.source) : v ∈ (e.symm.trans e').source := by
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨hv, hv'⟩

private lemma mem_target_inter_trans {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {U : Z.Opens} {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (hv' : e.symm v ∈ e'.source) :
    e' (e.symm v) ∈ e'.target ∩ e'.symm ⁻¹' chart U :=
  ⟨e'.map_source hv', by simpa [e'.left_inv hv'] using hv.2⟩

/-- **Chain rule for `d f^an`** under a change of chart. -/
private lemma dfan_eq_comp {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {U : Z.Opens}
    {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (hv' : e.symm v ∈ e'.source) (f : Γ(Z, U)) :
    dfan sZ e U v f = (dfan sZ e' U (e' (e.symm v)) f).comp (fderiv ℂ (e.symm.trans e') v) := by
  have hsrc := mem_source_trans sZ hv.1 hv'
  have heq : fan U f ∘ e.symm =ᶠ[nhds v] (fan U f ∘ e'.symm) ∘ (e.symm.trans e') := by
    filter_upwards [(e.symm.trans e').open_source.mem_nhds hsrc] with w hw
    have hw' : e.symm w ∈ e'.source := by
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage] at hw
      exact hw.2
    simp [e'.left_inv hw']
  unfold dfan
  rw [heq.fderiv_eq]
  exact fderiv_comp v (differentiableAt_fan sZ he' (mem_target_inter_trans sZ hv hv') f)
    (differentiableAt_trans sZ he he' hsrc)

private lemma clin (ℓ : 𝔼 →L[ℂ] ℂ) (u : 𝔼) :
    ℓ u = u 0 * ℓ (EuclideanSpace.single 0 1) + u 1 * ℓ (EuclideanSpace.single 1 1) := by
  conv_lhs => rw [show u = u 0 • EuclideanSpace.single 0 1 + u 1 • EuclideanSpace.single 1 1 by
    ext i; fin_cases i <;> simp]
  simp

/-- The complex Jacobian determinant of a `ℂ`-linear endomorphism of `ℂ²`. -/
private noncomputable def jac (J : 𝔼 →L[ℂ] 𝔼) : ℂ :=
  det2 ((EuclideanSpace.proj 0).comp J) ((EuclideanSpace.proj 1).comp J)

private lemma det2_comp (ℓ₁ ℓ₂ : 𝔼 →L[ℂ] ℂ) (J : 𝔼 →L[ℂ] 𝔼) :
    det2 (ℓ₁.comp J) (ℓ₂.comp J) = det2 ℓ₁ ℓ₂ * jac J := by
  simp only [jac, det2, ContinuousLinearMap.comp_apply]
  rw [clin ℓ₁ (J _), clin ℓ₁ (J _), clin ℓ₂ (J _), clin ℓ₂ (J _)]
  simp only [EuclideanSpace.proj, ContinuousLinearMap.coe_comp', Function.comp_apply,
    PiLp.proj_apply]
  ring

/-- Induction on the generators `a • d w₀ ∧ d w₁` of `⋀² Ω`. -/
private lemma exteriorPower_two_induction {A : Type} [CommRing A] [Algebra ℂ A]
    {P : ⋀[A]^2 (Ω[A⁄ℂ]) → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hneg : ∀ x, P x → P (-x))
    (hgen : ∀ (a : A) (w : Fin 2 → A),
      P (a • exteriorPower.ιMulti A 2 fun i ↦ KaehlerDifferential.D ℂ A (w i))) (x) : P x := by
  have hspan := Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ) (KaehlerDifferential.D ℂ A)
    (KaehlerDifferential.span_range_derivation ℂ A) 2
  have hx : x ∈ Submodule.span ℤ _ := hspan ▸ Submodule.mem_top
  refine Submodule.span_induction (fun y hy ↦ ?_) h0 (fun y z _ _ ↦ hadd y z) (fun n y _ hy ↦ ?_) hx
  · obtain ⟨c, rfl⟩ := hy
    exact hgen (c 0) (fun i ↦ c i.succ)
  · induction n using Int.induction_on with
    | zero => simpa using h0
    | succ k ih => simpa [add_smul] using hadd _ _ ih hy
    | pred k ih =>
      have := hadd _ _ ih (hneg _ hy)
      convert this using 1
      rw [sub_smul, one_smul, sub_eq_add_neg]

/-- **Change of chart for the coefficient.** -/
private lemma coeffLin_eq_mul_jac {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {U : Z.Opens}
    {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (hv' : e.symm v ∈ e'.source) x :
    coeffLin sZ he U hv x = coeffLin sZ he' U (mem_target_inter_trans sZ hv hv') x *
      jac (fderiv ℂ (e.symm.trans e') v) := by
  letI := MMP.Mori.sectionAlgebra sZ U
  induction x using exteriorPower_two_induction with
  | h0 => simp
  | hadd x y hx hy => simp [hx, hy, add_mul]
  | hneg x hx => simp [hx]
  | hgen a w =>
    rw [coeffLin_smul, coeffLin_smul, coeffLin_ιMulti, coeffLin_ιMulti,
      dfan_eq_comp sZ he he' hv hv', dfan_eq_comp sZ he he' hv hv', det2_comp]
    have : (⟨e'.symm (e' (e.symm v)), (mem_target_inter_trans sZ hv hv').2⟩ : chart (sX := sZ) U) =
        ⟨e.symm v, hv.2⟩ := Subtype.ext (e'.left_inv hv')
    rw [this]
    ring

private lemma mem_target_inter_mono {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {U W : Z.Opens} (h : W ≤ U) {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart W) :
    v ∈ e.target ∩ e.symm ⁻¹' chart U :=
  ⟨hv.1, chart_mono h hv.2⟩

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma fan_res {U W : Z.Opens} (h : W ≤ U) (f : Γ(Z, U)) {y : ComplexPoints sZ}
    (hy : y ∈ chart W) : fan W (Z.presheaf.map (homOfLE h).op f) y = fan U f y := by
  rw [fan_of_mem _ hy, fan_of_mem _ (chart_mono h hy), ← evalHom_res h ⟨y, hy⟩ f]

private lemma dfan_res {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {U W : Z.Opens}
    (h : W ≤ U) {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart W) (f : Γ(Z, U)) :
    dfan sZ e W v (Z.presheaf.map (homOfLE h).op f) = dfan sZ e U v f := by
  have heq := fan_eventuallyEq sZ hv (F := fan W (Z.presheaf.map (homOfLE h).op f))
    (G := fan U f) (fun y hy ↦ fan_res sZ h f hy)
  unfold dfan
  rw [heq.fderiv_eq]

/-- **Restriction compatibility of the coefficient.** -/
private lemma coeffLin_res {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {U W : Z.Opens} (h : W ≤ U) {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart W) x :
    letI := MMP.Mori.sectionAlgebra sZ U
    letI := MMP.Mori.sectionAlgebra sZ W
    letI : Algebra Γ(Z, U) Γ(Z, W) := (Z.presheaf.map (homOfLE h).op).hom.toAlgebra
    haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res sZ h
    coeffLin sZ he W hv (KaehlerDifferential.mapExteriorPower ℂ Γ(Z, U) Γ(Z, W) 2 x) =
      coeffLin sZ he U (mem_target_inter_mono sZ h hv) x := by
  letI := MMP.Mori.sectionAlgebra sZ U
  letI := MMP.Mori.sectionAlgebra sZ W
  letI : Algebra Γ(Z, U) Γ(Z, W) := (Z.presheaf.map (homOfLE h).op).hom.toAlgebra
  haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res sZ h
  induction x using exteriorPower_two_induction with
  | h0 => simp
  | hadd x y hx hy => simp [hx, hy]
  | hneg x hx => simp [hx]
  | hgen a w =>
    rw [map_smul, ← algebraMap_smul Γ(Z, W) a,
      coeffLin_smul, coeffLin_smul, KaehlerDifferential.mapExteriorPower_ιMulti]
    simp only [KaehlerDifferential.map_D]
    rw [coeffLin_ιMulti, coeffLin_ιMulti]
    change evalHom W ⟨_, hv.2⟩ (Z.presheaf.map (homOfLE h).op a) *
        det2 (dfan sZ e W v (Z.presheaf.map (homOfLE h).op (w 0)))
          (dfan sZ e W v (Z.presheaf.map (homOfLE h).op (w 1))) = _
    rw [dfan_res sZ h hv, dfan_res sZ h hv, ← evalHom_res h ⟨_, hv.2⟩ a]

open Classical in
/-- The coefficient `v ↦ coeffLin … x` as a total function on `𝔼`. -/
private noncomputable def coeffFun {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens)
    (x : letI := MMP.Mori.sectionAlgebra sZ U; ⋀[Γ(Z, U)]^2 (Ω[Γ(Z, U)⁄ℂ])) (v : 𝔼) : ℂ :=
  if hv : v ∈ e.target ∩ e.symm ⁻¹' chart U then coeffLin sZ he U hv x else 0

private lemma coeffFun_of_mem {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) x {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) : coeffFun sZ he U x v = coeffLin sZ he U hv x := by
  simp [coeffFun, hv]

private lemma analyticOnNhd_apply_fderiv {f : 𝔼 → ℂ} {s : Set 𝔼} (hf : AnalyticOnNhd ℂ f s)
    (u : 𝔼) : AnalyticOnNhd ℂ (fun v ↦ fderiv ℂ f v u) s := fun v hv ↦
  (ContinuousLinearMap.apply ℂ ℂ u).analyticAt _ |>.comp (hf.fderiv v hv)

/-- **The coefficient is holomorphic.** -/
private lemma analyticOnNhd_coeffFun {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) x :
    AnalyticOnNhd ℂ (coeffFun sZ he U x) (e.target ∩ e.symm ⁻¹' chart U) := by
  letI := MMP.Mori.sectionAlgebra sZ U
  have hS := isOpen_target_inter_chart sZ e U
  induction x using exteriorPower_two_induction with
  | h0 =>
    exact (analyticOnNhd_const (v := (0 : ℂ))).congr hS fun v hv ↦ by
      rw [coeffFun_of_mem sZ he U _ hv, map_zero]
  | hadd x y hx hy =>
    exact (hx.add hy).congr hS fun v hv ↦ by
      simp only [Pi.add_apply, coeffFun_of_mem sZ he U _ hv, map_add]
  | hneg x hx =>
    exact hx.neg.congr hS fun v hv ↦ by
      simp only [Pi.neg_apply, coeffFun_of_mem sZ he U _ hv, map_neg]
  | hgen a w =>
    have ha := analyticOnNhd_fan sZ he U a
    have hw := fun i ↦ analyticOnNhd_fan sZ he U (w i)
    have hd := fun i j ↦ analyticOnNhd_apply_fderiv (hw i) (EuclideanSpace.single j 1)
    refine (ha.mul (((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0)))).congr hS
      fun v hv ↦ ?_
    rw [coeffFun_of_mem sZ he U _ hv, coeffLin_smul, coeffLin_ιMulti]
    simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, det2, dfan]
    rw [fan_of_mem _ hv.2]

open ContinuousAlternatingMap in
/-- `dz₁ ∧ dz₂` pulled back by a `ℂ`-linear map is multiplied by its determinant. -/
private lemma detC_comp (J : 𝔼 →L[ℂ] 𝔼) :
    detC.compContinuousLinearMap (J.restrictScalars ℝ) = jac J • detC := by
  ext v
  simp only [compContinuousLinearMap_apply, detC_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, jac, det2, ContinuousLinearMap.coe_restrictScalars', Function.comp_apply]
  rw [show J (v 0) = (v 0) 0 • J (EuclideanSpace.single 0 1) + (v 0) 1 • J
      (EuclideanSpace.single 1 1) by
      rw [← map_smul, ← map_smul, ← map_add]; congr 1; ext i; fin_cases i <;> simp,
    show J (v 1) = (v 1) 0 • J (EuclideanSpace.single 0 1) + (v 1) 1 • J
        (EuclideanSpace.single 1 1) by
      rw [← map_smul, ← map_smul, ← map_add]; congr 1; ext i; fin_cases i <;> simp]
  simp [EuclideanSpace.proj]
  ring

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma exists_isAffineOpen_le {y : ComplexPoints sZ} {U : Z.Opens} (hy : y ∈ chart U) :
    ∃ W : Z.affineOpens, (W : Z.Opens) ≤ U ∧ y ∈ chart (W : Z.Opens) := by
  obtain ⟨W, hW, hyW, hWU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Z)) (mem_chart_iff.1 hy)
  exact ⟨⟨W, hW⟩, hWU, mem_chart_iff.2 hyW⟩

/-- The algebraic form `ω|_W ∈ ⋀² Ω_{Γ(Z, W)/ℂ}` on an affine open `W`. -/
private noncomputable def formsAt (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (W : Z.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sZ W
    ⋀[Γ(Z, W)]^2 (Ω[Γ(Z, W)⁄ℂ]) :=
  MMP.DeRham.formsAlgEquiv sZ 2 W
    ((Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op ω)

private lemma formsAt_res (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    {W W' : Z.affineOpens} (h : (W' : Z.Opens) ≤ W) :
    letI := MMP.Mori.sectionAlgebra sZ W
    letI := MMP.Mori.sectionAlgebra sZ W'
    letI : Algebra Γ(Z, W) Γ(Z, W') := (Z.presheaf.map (homOfLE h).op).hom.toAlgebra
    haveI := MMP.Flips.ResolutionInputs.isScalarTower_section_res sZ h
    formsAt sZ ω W' = KaehlerDifferential.mapExteriorPower ℂ Γ(Z, W) Γ(Z, W') 2
      (formsAt sZ ω W) := by
  rw [formsAt, formsAt, ← MMP.DeRham.formsAlgEquiv_restrict]
  congr 1
  show _ = ((Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op ≫
    (Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)).presheaf.map (homOfLE h).op)
      (show (Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)).presheaf.obj (op ⊤) from ω)
  rw [← Functor.map_comp]
  rfl

/-- The coefficient of `ω^an` does not depend on the affine open used to compute it. -/
private lemma coeffLin_formsAt_eq (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    {W W' : Z.affineOpens} {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens))
    (hv' : v ∈ e.target ∩ e.symm ⁻¹' chart (W' : Z.Opens)) :
    coeffLin sZ he W hv (formsAt sZ ω W) = coeffLin sZ he W' hv' (formsAt sZ ω W') := by
  obtain ⟨W'', hW'', hv''⟩ := exists_isAffineOpen_le sZ
    (show e.symm v ∈ chart ((W : Z.Opens) ⊓ W') from mem_chart_iff.2 ⟨mem_chart_iff.1 hv.2,
      mem_chart_iff.1 hv'.2⟩)
  have h1 : (W'' : Z.Opens) ≤ W := hW''.trans inf_le_left
  have h2 : (W'' : Z.Opens) ≤ W' := hW''.trans inf_le_right
  have hv3 : v ∈ e.target ∩ e.symm ⁻¹' chart (W'' : Z.Opens) := ⟨hv.1, hv''⟩
  have e1 := coeffLin_res sZ he h1 hv3 (formsAt sZ ω W)
  have e2 := coeffLin_res sZ he h2 hv3 (formsAt sZ ω W')
  rw [← formsAt_res sZ ω h1] at e1
  rw [← formsAt_res sZ ω h2] at e2
  exact e1.symm.trans e2

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma mem_chart_top (y : ComplexPoints sZ) : y ∈ chart (⊤ : Z.Opens) :=
  mem_chart_iff.2 trivial

/-- An affine open of `Z` containing `y`. -/
private noncomputable def affAt (y : ComplexPoints sZ) : Z.affineOpens :=
  (exists_isAffineOpen_le sZ (mem_chart_top sZ y)).choose

private lemma mem_chart_affAt (y : ComplexPoints sZ) : y ∈ chart (affAt sZ y : Z.Opens) :=
  (exists_isAffineOpen_le sZ (mem_chart_top sZ y)).choose_spec.2

private lemma mem_chartAt_target_inter {y : ComplexPoints sZ} {U : Z.Opens} (hy : y ∈ chart U) :
    chartAt 𝔼 y y ∈ (chartAt 𝔼 y).target ∩ (chartAt 𝔼 y).symm ⁻¹' chart U :=
  ⟨(chartAt _ y).map_source (mem_chart_source _ y), by
    simpa [(chartAt 𝔼 y).left_inv (mem_chart_source _ y)] using hy⟩

/-- The coefficient of `ω^an` at `y`, in the preferred chart at `y`. -/
private noncomputable def holoCoeff (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (y : ComplexPoints sZ) : ℂ :=
  coeffLin sZ (chart_mem_atlas 𝔼 y) (affAt sZ y)
    (mem_chartAt_target_inter sZ (mem_chart_affAt sZ y))
    (formsAt sZ ω (affAt sZ y))

/-- The analytic two-form `ω^an = a dz₁ ∧ dz₂` of an algebraic two-form `ω`, its value at `y` read
in the preferred chart at `y`. -/
private noncomputable def holoVal (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (y : ComplexPoints sZ) : 𝔼 [⋀^Fin 2]→L[ℝ] ℂ :=
  holoCoeff sZ ω y • detC

open ContinuousAlternatingMap in
private lemma smul_compContinuousLinearMap' (c : ℂ) (A : 𝔼 [⋀^Fin 2]→L[ℝ] ℂ) (L : 𝔼 →L[ℝ] 𝔼) :
    (c • A).compContinuousLinearMap L = c • A.compContinuousLinearMap L := by
  ext v; rfl

/-- **The local expression of `ω^an`** in any atlas chart, on the `ℂ`-points of any affine open,
is its holomorphic coefficient times `dz₁ ∧ dz₂`. -/
private lemma loc_holoVal (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    {W : Z.affineOpens} {v : 𝔼} (hv : v ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens)) :
    Forms.loc e (holoVal sZ ω) v = coeffLin sZ he W hv (formsAt sZ ω W) • detC := by
  have hys : e.symm v ∈ (chartAt 𝔼 (e.symm v)).source := mem_chart_source _ _
  have hsrc := mem_source_trans sZ hv.1 hys
  have hdiff := differentiableAt_trans sZ he (chart_mem_atlas 𝔼 (e.symm v)) hsrc
  have h1 := coeffLin_eq_mul_jac sZ he (chart_mem_atlas 𝔼 (e.symm v)) hv hys (formsAt sZ ω W)
  have h2 := coeffLin_formsAt_eq sZ ω (chart_mem_atlas 𝔼 (e.symm v))
    (mem_target_inter_trans sZ hv hys) (mem_chartAt_target_inter sZ (mem_chart_affAt sZ (e.symm v)))
  unfold Forms.loc holoVal holoCoeff
  rw [smul_compContinuousLinearMap', hdiff.fderiv_restrictScalars ℝ, detC_comp, smul_smul, h1, h2]

section Stokes

open MeasureTheory Complex ComplexConjugate ContinuousAlternatingMap
open scoped Topology

/-- The `j`-th coordinate vector of `ℂ²`. -/
private noncomputable abbrev ej (j : Fin 2) : 𝔼 := EuclideanSpace.single j 1

/-- The Wirtinger derivative `∂/∂z_j` of a real-linear map, at the `j`-th coordinate. -/
private noncomputable def wl (j : Fin 2) : (𝔼 →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (ej j) - I • ContinuousLinearMap.apply ℝ ℂ (I • ej j))

private lemma wl_apply (j : Fin 2) (L : 𝔼 →L[ℝ] ℂ) :
    wl j L = (L (ej j) - I * L (I • ej j)) / 2 := by
  simp [wl]; ring

/-- The `(1,0)`-coefficient `α(∂/∂z_j)` of a real one-form. -/
private noncomputable def part (j : Fin 2) : (𝔼 [⋀^Fin 1]→L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (ContinuousAlternatingMap.apply ℝ 𝔼 ℂ ![ej j] -
    I • ContinuousAlternatingMap.apply ℝ 𝔼 ℂ ![I • ej j])

private lemma part_apply (j : Fin 2) (L : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) :
    part j L = (L ![ej j] - I * L ![I • ej j]) / 2 := by
  simp [part]; ring

/-- The Wirtinger derivative of a function. -/
private noncomputable def wirt (f : 𝔼 → ℂ) (v : 𝔼) (j : Fin 2) : ℂ := wl j (fderiv ℝ f v)

private lemma extDeriv_coeff {A : 𝔼 → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} {v : 𝔼} (hA : DifferentiableAt ℝ A v)
    {c : ℂ}
    (h : extDeriv A v = c • detC) :
    c = wirt (fun w ↦ part 1 (A w)) v 0 - wirt (fun w ↦ part 0 (A w)) v 1 := by
  have hd : ∀ j, fderiv ℝ (fun w ↦ part j (A w)) v = (part j).comp (fderiv ℝ A v) := fun j ↦
    ((part j).hasFDerivAt.comp v hA.hasFDerivAt).fderiv
  simp only [wirt, hd]
  have key : ∀ u w : 𝔼, fderiv ℝ A v u ![w] - fderiv ℝ A v w ![u] = c * detC ![u, w] := by
    intro u w
    have := congrArg (fun B : 𝔼 [⋀^Fin 2]→L[ℝ] ℂ ↦ B ![u, w]) h
    simp only [extDeriv, alternatizeUncurryFin_apply, Fin.sum_univ_two] at this
    have hr : Fin.removeNth 1 ![u, w] = ![u] := by ext i; fin_cases i; rfl
    have hr0 : Fin.removeNth 0 ![u, w] = ![w] := by ext i; fin_cases i; rfl
    simpa [hr, hr0, sub_eq_add_neg] using this
  have k1 := key (ej 0) (ej 1)
  have k2 := key (I • ej 0) (ej 1)
  have k3 := key (ej 0) (I • ej 1)
  have k4 := key (I • ej 0) (I • ej 1)
  simp only [detC_apply] at k1 k2 k3 k4
  simp only [wl_apply, ContinuousLinearMap.comp_apply, part_apply]
  simp at k1 k2 k3 k4 ⊢
  linear_combination (norm := (ring_nf; simp only [I_sq]; ring_nf))
    (-1/4 : ℂ) * k1 + (I/4) * k2 + (I/4) * k3 + (1/4) * k4

/-- The `(1,0)`-part `u ↦ (L u - i L (i u)) / 2` of a real-linear form on `ℂ²`. -/
private noncomputable def hol10 (L : 𝔼 →L[ℝ] ℂ) : 𝔼 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ (L u - I * L (I • u)) / 2
      map_add' := fun u w ↦ by simp only [smul_add, map_add]; ring
      map_smul' := fun c u ↦ by
        have hc : c • u = c.re • u + c.im • (I • u) := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]
        have hc' : c • (I • u) = c.re • (I • u) - c.im • u := by
          conv_lhs => rw [← Complex.re_add_im c]
          rw [add_smul, mul_smul, ← mul_smul I I u, I_mul_I, neg_one_smul, smul_neg,
            ← sub_eq_add_neg, Complex.coe_smul, Complex.coe_smul]
        rw [smul_comm I c u, hc', hc]
        simp only [map_add, map_sub, map_smul, Complex.real_smul, RingHom.id_apply, smul_eq_mul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring_nf; simp only [I_sq]; ring }

private lemma hol10_apply (L : 𝔼 →L[ℝ] ℂ) (u : 𝔼) : hol10 L u = (L u - I * L (I • u)) / 2 := rfl

private lemma wl_eq_hol10 (j : Fin 2) (L : 𝔼 →L[ℝ] ℂ) : wl j L = hol10 L (ej j) := by
  rw [wl_apply, hol10_apply]

private lemma hol10_comp (L : 𝔼 →L[ℝ] ℂ) (J : 𝔼 →L[ℂ] 𝔼) :
    hol10 (L.comp (J.restrictScalars ℝ)) = (hol10 L).comp J := by
  ext u
  simp [hol10_apply, map_smul]

private lemma wl_smul (j : Fin 2) (c : ℂ) (L : 𝔼 →L[ℝ] ℂ) : wl j (c • L) = c * wl j L := by
  simp only [wl_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_comm c I]; ring

private lemma wirt_mul {f g : 𝔼 → ℂ} {v : 𝔼} (hf : DifferentiableAt ℝ f v)
    (hg : DifferentiableAt ℝ g v)
    (j : Fin 2) : wirt (fun w ↦ f w * g w) v j = f v * wirt g v j + g v * wirt f v j := by
  simp only [wirt, fderiv_fun_mul hf hg, map_add, wl_smul]

private lemma wirt_conj {a : 𝔼 → ℂ} {v : 𝔼} (ha : DifferentiableAt ℂ a v) (j : Fin 2) :
    wirt (fun w ↦ conj (a w)) v j = 0 := by
  have h : HasFDerivAt (fun w ↦ conj (a w))
      ((conjCLE.toContinuousLinearMap).comp ((fderiv ℂ a v).restrictScalars ℝ)) v :=
    conjCLE.toContinuousLinearMap.hasFDerivAt.comp v (ha.hasFDerivAt.restrictScalars ℝ)
  rw [wirt, h.fderiv, wl_apply]
  simp [map_smul]
  ring_nf; simp [I_sq]

private lemma linearMap_det_eq_jac (J : 𝔼 →L[ℂ] 𝔼) : LinearMap.det (J : 𝔼 →ₗ[ℂ] 𝔼) = jac J := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, jac, det2]

private lemma det_restrictScalars_eq_normSq (J : 𝔼 →L[ℂ] 𝔼) :
    (J.restrictScalars ℝ).det = Complex.normSq (jac J) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, linearMap_det_eq_jac, Algebra.norm_complex_apply]

private lemma continuous_mul_of_tsupport_subset {S : Set 𝔼} (hS : IsOpen S) {φ g : 𝔼 → ℂ}
    (hφ : Continuous φ) (hφS : tsupport φ ⊆ S) (hg : ContinuousOn g S) :
    Continuous fun v ↦ φ v * g v := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v ∈ S
  · exact hφ.continuousAt.mul (hg.continuousAt (hS.mem_nhds hv))
  · have hv' : v ∉ tsupport φ := fun h ↦ hv (hφS h)
    have h0 : (fun v ↦ φ v * g v) =ᶠ[𝓝 v] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hv'] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    exact continuousAt_const.congr h0.symm

private lemma integrable_mul_of_tsupport_subset {S : Set 𝔼} (hS : IsOpen S) {φ g : 𝔼 → ℂ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφS : tsupport φ ⊆ S)
    (hg : ContinuousOn g S) : Integrable (fun v ↦ φ v * g v) :=
  (continuous_mul_of_tsupport_subset hS hφ hφS hg).integrable_of_hasCompactSupport
    (hφc.mul_right)

/-- **Integration by parts for a Wirtinger derivative**, against a compactly supported smooth
function supported in the open set where the other factor is `C¹`. -/
private lemma integral_mul_wirt {S : Set 𝔼} (hS : IsOpen S) {ρ : 𝔼 → ℂ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (hρS : tsupport ρ ⊆ S) {g : 𝔼 → ℂ} (hg : ContDiffOn ℝ 1 g S)
    (j : Fin 2) : ∫ v, ρ v * wirt g v j = - ∫ v, wirt ρ v j * g v := by
  have hρd : ∀ u : 𝔼, Continuous fun v ↦ fderiv ℝ ρ v u := fun u ↦
    (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp (hρ.continuous_fderiv one_ne_zero)
  have hρdS : ∀ u : 𝔼, tsupport (fun v ↦ fderiv ℝ ρ v u) ⊆ S := fun u ↦
    (tsupport_comp_subset (map_zero (ContinuousLinearMap.apply ℝ ℂ u)) _).trans
      ((tsupport_fderiv_subset ℝ).trans hρS)
  have hρdc : ∀ u : 𝔼, HasCompactSupport fun v ↦ fderiv ℝ ρ v u := fun u ↦
    hρc.fderiv_apply (𝕜 := ℝ) u
  have hgd : ∀ u : 𝔼, ContinuousOn (fun v ↦ fderiv ℝ g v u) S := fun u ↦
    (ContinuousLinearMap.apply ℝ ℂ u).continuous.comp_continuousOn
      ((hg.continuousOn_fderiv_of_isOpen hS le_rfl))
  have ibp : ∀ u : 𝔼, ∫ v, ρ v * fderiv ℝ g v u = - ∫ v, fderiv ℝ ρ v u * g v := fun u ↦
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_mul_of_tsupport_subset hS (hρd u) (hρdc u) (hρdS u) hg.continuousOn)
      (integrable_mul_of_tsupport_subset hS hρ.continuous hρc hρS (hgd u))
      (integrable_mul_of_tsupport_subset hS hρ.continuous hρc hρS hg.continuousOn)
      (fun x _ ↦ hρ.differentiable one_ne_zero x)
      (fun x hx ↦ (hg.differentiableOn one_ne_zero x (hρS hx)).differentiableAt
        (hS.mem_nhds (hρS hx)))
  have i1 : ∀ u : 𝔼, Integrable fun v ↦ ρ v * fderiv ℝ g v u := fun u ↦
    integrable_mul_of_tsupport_subset hS hρ.continuous hρc hρS (hgd u)
  have i2 : ∀ u : 𝔼, Integrable fun v ↦ fderiv ℝ ρ v u * g v := fun u ↦
    integrable_mul_of_tsupport_subset hS (hρd u) (hρdc u) (hρdS u) hg.continuousOn
  simp only [wirt, wl_apply]
  have e1 : (fun v ↦ ρ v * ((fderiv ℝ g v (ej j) - I * fderiv ℝ g v (I • ej j)) / 2)) =
      fun v ↦ (2⁻¹ : ℂ) * (ρ v * fderiv ℝ g v (ej j) - I * (ρ v * fderiv ℝ g v (I • ej j))) := by
    funext v; ring
  have e2 : (fun v ↦ (fderiv ℝ ρ v (ej j) - I * fderiv ℝ ρ v (I • ej j)) / 2 * g v) =
      fun v ↦ (2⁻¹ : ℂ) * (fderiv ℝ ρ v (ej j) * g v - I * (fderiv ℝ ρ v (I • ej j) * g v)) := by
    funext v; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_sub (i1 _) ((i1 _).const_mul _),
    integral_sub (i2 _) ((i2 _).const_mul _), integral_const_mul, integral_const_mul, ibp, ibp]
  ring

/-- A one-form as a real-linear map. -/
private noncomputable def one1 (L : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) : 𝔼 →L[ℝ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ 𝔼 ℂ (0 : Fin 1)).symm L

private lemma one1_apply (L : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) (u : 𝔼) : one1 L u = L ![u] := by
  conv_rhs => rw [← Equiv.apply_symm_apply (ContinuousAlternatingMap.ofSubsingleton ℝ 𝔼 ℂ
    (0 : Fin 1)) L]
  rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  rfl

private lemma one1_compContinuousLinearMap (L : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) (J : 𝔼 →L[ℝ] 𝔼) :
    one1 (L.compContinuousLinearMap J) = (one1 L).comp J := by
  ext u
  simp only [one1_apply, ContinuousLinearMap.comp_apply, compContinuousLinearMap_apply]
  congr 1
  ext i; fin_cases i; rfl

private lemma part_eq_hol10 (j : Fin 2) (L : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) :
    part j L = hol10 (one1 L) (ej j) := by
  rw [part_apply, hol10_apply, one1_apply, one1_apply]

/-- **Stokes in a chart.** -/
private lemma integral_mul_normSq_eq {S : Set 𝔼} (hS : IsOpen S) {ρ : 𝔼 → ℂ} (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (hρS : tsupport ρ ⊆ S) {a : 𝔼 → ℂ}
    (ha : AnalyticOnNhd ℂ a S) {A : 𝔼 → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} (hA : ContDiffOn ℝ 2 A S)
    (hdA : ∀ v ∈ S, extDeriv A v = a v • detC) :
    ∫ v, ρ v * (conj (a v) * a v) =
      - ∫ v, conj (a v) * det2 (hol10 (fderiv ℝ ρ v)) (hol10 (one1 (A v))) := by
  have haS : ContDiffOn ℝ 2 (fun w ↦ conj (a w)) S :=
    conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn
      ((ha.contDiffOn hS.uniqueDiffOn).restrict_scalars ℝ)
  set G : Fin 2 → 𝔼 → ℂ := fun j w ↦ conj (a w) * part j (A w) with hG
  have hGS : ∀ j, ContDiffOn ℝ 2 (G j) S := fun j ↦
    haS.mul ((part j).contDiff.comp_contDiffOn hA)
  have hGd : ∀ j, ∀ v ∈ S, DifferentiableAt ℝ (G j) v := fun j v hv ↦
    ((hGS j).differentiableOn (by norm_num) v hv).differentiableAt (hS.mem_nhds hv)
  have hpt : ∀ v ∈ S, conj (a v) * a v = wirt (G 1) v 0 - wirt (G 0) v 1 := by
    intro v hv
    have hAv : DifferentiableAt ℝ A v :=
      (hA.differentiableOn (by norm_num) v hv).differentiableAt (hS.mem_nhds hv)
    have hav : DifferentiableAt ℂ a v := (ha v hv).differentiableAt
    have hP : ∀ j, DifferentiableAt ℝ (fun w ↦ part j (A w)) v := fun j ↦
      (part j).differentiableAt.comp v hAv
    have hc : DifferentiableAt ℝ (fun w ↦ conj (a w)) v :=
      (haS.differentiableOn (by norm_num) v hv).differentiableAt (hS.mem_nhds hv)
    rw [congrArg (conj (a v) * ·) (extDeriv_coeff hAv (hdA v hv)), hG]
    simp only
    rw [wirt_mul hc (hP 1), wirt_mul hc (hP 0), wirt_conj hav, wirt_conj hav]
    ring
  have h1 : (fun v ↦ ρ v * (conj (a v) * a v)) =
      fun v ↦ ρ v * wirt (G 1) v 0 - ρ v * wirt (G 0) v 1 := by
    funext v
    by_cases hv : v ∈ S
    · rw [hpt v hv]; ring
    · have : ρ v = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hv (hρS h)
      simp [this]
  have hwc : ∀ j k, ContinuousOn (fun v ↦ wirt (G j) v k) S := fun j k ↦
    (wl k).continuous.comp_continuousOn
      ((hGS j).continuousOn_fderiv_of_isOpen hS (by norm_num))
  rw [h1, integral_sub
    (integrable_mul_of_tsupport_subset hS hρ.continuous hρc hρS (hwc 1 0))
    (integrable_mul_of_tsupport_subset hS hρ.continuous hρc hρS (hwc 0 1)),
    integral_mul_wirt hS hρ hρc hρS ((hGS 1).of_le (by norm_num)),
    integral_mul_wirt hS hρ hρc hρS ((hGS 0).of_le (by norm_num))]
  have hρw : ∀ k, Continuous fun v ↦ wirt ρ v k := fun k ↦
    (wl k).continuous.comp (hρ.continuous_fderiv one_ne_zero)
  have hρwS : ∀ k, tsupport (fun v ↦ wirt ρ v k) ⊆ S := fun k ↦
    (tsupport_comp_subset (map_zero (wl k)) _).trans ((tsupport_fderiv_subset ℝ).trans hρS)
  have hρwc : ∀ k, HasCompactSupport fun v ↦ wirt ρ v k := fun k ↦
    (hρc.fderiv (𝕜 := ℝ)).comp_left (map_zero (wl k))
  rw [← neg_sub', ← integral_sub
    (integrable_mul_of_tsupport_subset hS (hρw 0) (hρwc 0) (hρwS 0) (hGS 1).continuousOn)
    (integrable_mul_of_tsupport_subset hS (hρw 1) (hρwc 1) (hρwS 1) (hGS 0).continuousOn)]
  congr 2
  funext v
  simp only [hG, wirt, det2, wl_eq_hol10, part_eq_hol10]
  ring

/-- **Change of variables for densities** along a holomorphic local diffeomorphism. -/
private lemma integral_eq_of_density {T : OpenPartialHomeomorph 𝔼 𝔼}
    (hT : ∀ v ∈ T.source, DifferentiableAt ℂ T v) {F G : 𝔼 → ℂ}
    (hFG : ∀ v ∈ T.source, F v = G (T v) * Complex.normSq (jac (fderiv ℂ T v)))
    (hF : ∀ v ∉ T.source, F v = 0) (hG : ∀ w ∉ T.target, G w = 0) :
    ∫ v, F v = ∫ w, G w := by
  have hd : ∀ v ∈ T.source, HasFDerivWithinAt T ((fderiv ℂ T v).restrictScalars ℝ) T.source v :=
    fun v hv ↦ ((hT v hv).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume T.open_source.measurableSet hd
    T.injOn G
  rw [T.image_source_eq_target] at h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hG, h]
  refine setIntegral_congr_fun T.open_source.measurableSet fun v hv ↦ ?_
  simp only [det_restrictScalars_eq_normSq, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.real_smul, hFG v hv]
  ring

end Stokes

/-- The complex realization of a projective complex scheme is compact. -/
private theorem compactSpace_complexPoints_of_isProjective (hP : IsProjectiveMorphism sZ) :
    CompactSpace (ComplexPoints sZ) := by
  letI : Z.Over (Spec (.of ℂ)) := ⟨sZ⟩
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  have : sZ.IsOver (Spec (.of ℂ)) := ⟨Category.comp_id sZ⟩
  have : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (𝟙 _) from inferInstance
  have hp := MMP.UnderlyingSpace.isProperMap_map (K := ℂ) sZ
  have : Subsingleton (MMP.UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ MMP.UnderlyingSpace.ext
      (((Category.comp_id _).symm.trans p.toHom_comp_over).trans
        ((Category.comp_id _).symm.trans q.toHom_comp_over).symm)⟩
  have hc : CompactSpace (MMP.UnderlyingSpace ℂ Z) :=
    ⟨by simpa using hp.isCompact_preimage (Set.subsingleton_univ.isCompact)⟩
  exact (homeomorphUnderlyingSpace (X := Z)).symm.compactSpace

/-- The complex realization of a projective complex scheme is Hausdorff. -/
private theorem t2Space_complexPoints_of_isProjective (hP : IsProjectiveMorphism sZ) :
    T2Space (ComplexPoints sZ) := by
  have : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  infer_instance

/-- **Smooth functions are acyclic**: `H¹(Z^an, 𝒜⁰) = 0`, by partitions of unity. -/
private theorem forms_zero_H_one (hP : IsProjectiveMorphism sZ) :
    ∀ e : Sheaf.H (forms sZ 0 False) 1, e = 0 := by
  haveI := compactSpace_complexPoints_of_isProjective sZ hP
  haveI := t2Space_complexPoints_of_isProjective sZ hP
  exact formSheaf_zero_H_one

private lemma formsAt_add (ω ω' : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (W : Z.affineOpens) : formsAt sZ (ω + ω') W = formsAt sZ ω W + formsAt sZ ω' W := by
  unfold formsAt
  rw [← map_add]
  exact congrArg _ (map_add _ ω ω')

private lemma formsAt_zero (W : Z.affineOpens) : formsAt sZ 0 W = 0 := by
  unfold formsAt
  rw [← map_zero (MMP.DeRham.formsAlgEquiv sZ 2 W)]
  exact congrArg _ (map_zero _)

private lemma formsAt_smul (c : ℂ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (W : Z.affineOpens) :
    formsAt sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
        sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) W =
      baseRingHom sZ W c • formsAt sZ ω W := by
  unfold formsAt
  rw [← map_smul]
  congr 1
  exact (Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)).val.map_smul _ _ _

private lemma holoVal_add (ω ω' : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    holoVal sZ (ω + ω') = holoVal sZ ω + holoVal sZ ω' := by
  funext y
  simp only [holoVal, holoCoeff, Pi.add_apply, formsAt_add, map_add, add_smul]

private lemma holoVal_zero : holoVal sZ 0 = 0 := by
  funext y
  simp only [holoVal, holoCoeff, Pi.zero_apply, formsAt_zero, map_zero, zero_smul]

private lemma holoVal_smul (c : ℂ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    holoVal sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
        sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) = c • holoVal sZ ω := by
  funext y
  simp only [holoVal, holoCoeff, Pi.smul_apply]
  rw [formsAt_smul, coeffLin_smul, evalHom_baseRingHom, smul_smul]

/-- The local expression of `ω^an` in an atlas chart is smooth. -/
private lemma contDiffOn_loc_holoVal (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj
    (op ⊤))
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) :
    ContDiffOn ℝ ⊤ (Forms.loc e (holoVal sZ ω)) e.target := by
  refine contDiffOn_of_locally_contDiffOn fun v hv ↦ ?_
  set W := affAt sZ (e.symm v)
  have hvW : v ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens) := ⟨hv, mem_chart_affAt sZ _⟩
  refine ⟨e.target ∩ e.symm ⁻¹' chart (W : Z.Opens), isOpen_target_inter_chart sZ e _, hvW, ?_⟩
  have h1 : ContDiffOn ℝ ⊤ (fun w ↦ coeffFun sZ he W (formsAt sZ ω W) w • detC)
      (e.target ∩ e.symm ⁻¹' chart (W : Z.Opens)) :=
    (((analyticOnNhd_coeffFun sZ he W _).contDiffOn
      (isOpen_target_inter_chart sZ e _).uniqueDiffOn (n := ⊤)).restrict_scalars ℝ).smul
      contDiffOn_const
  refine (h1.mono Set.inter_subset_right).congr fun w hw ↦ ?_
  rw [loc_holoVal sZ ω he hw.2, coeffFun_of_mem sZ he W _ hw.2]

open ContinuousAlternatingMap in
/-- `ℓ ∧ dz₁ ∧ dz₂ = 0` for a `ℂ`-linear form `ℓ` on `ℂ²`. -/
private lemma alternatizeUncurryFin_smulRight_detC (ℓ : 𝔼 →L[ℂ] ℂ) :
    alternatizeUncurryFin ((ℓ.restrictScalars ℝ).smulRight detC) = 0 := by
  ext v
  rw [alternatizeUncurryFin_apply, Fin.sum_univ_three]
  simp only [ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousAlternatingMap.smul_apply, detC_apply]
  simp only [Fin.removeNth, Fin.succAbove, Fin.isValue, smul_eq_mul]
  rw [clin ℓ (v 0), clin ℓ (v 1), clin ℓ (v 2)]
  simp [Fin.lt_def]
  ring

/-- `ω^an` is closed. -/
private lemma d_holoVal (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (x : ComplexPoints sZ) : Forms.d (holoVal sZ ω) x = 0 := by
  set c := chartAt 𝔼 x
  have he : c ∈ atlas 𝔼 (ComplexPoints sZ) := chart_mem_atlas 𝔼 x
  set W := affAt sZ x
  have hx : c x ∈ c.target ∩ c.symm ⁻¹' chart (W : Z.Opens) :=
    mem_chartAt_target_inter sZ (mem_chart_affAt sZ x)
  set a := coeffFun sZ he W (formsAt sZ ω W)
  have heq : Forms.loc c (holoVal sZ ω) =ᶠ[nhds (c x)] fun w ↦ a w • detC := by
    filter_upwards [(isOpen_target_inter_chart sZ c _).mem_nhds hx] with w hw
    rw [loc_holoVal sZ ω he hw]
    exact congrArg (· • detC) (coeffFun_of_mem sZ he W _ hw).symm
  have ha : DifferentiableAt ℂ a (c x) :=
    (analyticOnNhd_coeffFun sZ he W _ _ hx).differentiableAt
  change extDeriv (Forms.loc c (holoVal sZ ω)) (c x) = 0
  rw [heq.extDeriv_eq, extDeriv, fderiv_smul_const (ha.restrictScalars ℝ),
    ha.fderiv_restrictScalars ℝ]
  exact alternatizeUncurryFin_smulRight_detC _

/-- `ω^an` is a smooth form on `Z^an`. -/
private lemma isSmoothOn_holoVal (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    Forms.IsSmoothOn Set.univ (holoVal sZ ω) := fun e he ↦
  ((contDiffOn_loc_holoVal sZ ω he).of_le le_top).mono Set.inter_subset_left

private lemma extend_top_eq {k : ℕ} (β : ComplexPoints sZ → 𝔼 [⋀^Fin k]→L[ℝ] ℂ) :
    Forms.extend (fun y : (⊤ : TopologicalSpace.Opens (TopCat.of (ComplexPoints sZ))) ↦ β y.1) =
      β := by
  funext y
  exact Forms.extend_apply (W := ((⊤ : TopologicalSpace.Opens (TopCat.of (ComplexPoints sZ))) :
    Set (ComplexPoints sZ))) (fun y ↦ β y.1) ⟨y, trivial⟩

/-- The closed smooth two-form `ω^an` on `Z^an` of a regular two-form `ω`, written
`a dz₁ ∧ dz₂` in étale coordinates. -/
private noncomputable def holoForm :
    (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤) →+
      ToType ((forms sZ 2 True).obj.obj (op ⊤)) where
  toFun ω := (⟨fun y ↦ holoVal sZ ω y.1, by
      refine ⟨?_, fun _ y _ ↦ ?_⟩
      · rw [extend_top_eq]
        exact isSmoothOn_holoVal sZ ω
      · rw [extend_top_eq]
        exact d_holoVal sZ ω y⟩ :
    Forms.formSections (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 2 True ⊤)
  map_zero' := Subtype.ext (funext fun y ↦ by simp [holoVal_zero]; rfl)
  map_add' ω ω' := Subtype.ext (funext fun y ↦ by simp [holoVal_add]; rfl)

/-- The analytic form of `c • ω` is `c • ω^an`. -/
private theorem holoForm_smul (c : ℂ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    holoForm sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
        sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) =
      (smulHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) c 2 True).hom.app (op ⊤)
        (holoForm sZ ω) :=
  Subtype.ext (funext fun y ↦ congrFun (holoVal_smul sZ c ω) y.1)

section StokesGlobal

open MeasureTheory Complex ComplexConjugate
open scoped Topology Manifold

private lemma detC_ej : detC ![ej 0, ej 1] = 1 := by simp [detC_apply, ej]

private lemma smul_detC_ej (c : ℂ) : (c • detC) ![ej 0, ej 1] = c := by
  rw [ContinuousAlternatingMap.smul_apply, detC_ej, smul_eq_mul, mul_one]

/-- The coefficient against `dz₁ ∧ dz₂` of the local expression of a two-form in the chart `e`. -/
private noncomputable def coefAt (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼)
    (β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ) (v : 𝔼) : ℂ :=
  Forms.loc e β v ![ej 0, ej 1]

private lemma loc_holoVal_eq_coefAt
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    {v : 𝔼} (hv : v ∈ e.target) :
    Forms.loc e (holoVal sZ ω) v = coefAt sZ e (holoVal sZ ω) v • detC := by
  have hvW : v ∈ e.target ∩ e.symm ⁻¹' chart (affAt sZ (e.symm v) : Z.Opens) :=
    ⟨hv, mem_chart_affAt sZ _⟩
  rw [coefAt, loc_holoVal sZ ω he hvW, smul_detC_ej]

private lemma analyticOnNhd_coefAt_holoVal
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) :
    AnalyticOnNhd ℂ (coefAt sZ e (holoVal sZ ω)) e.target := by
  intro v hv
  set W := affAt sZ (e.symm v)
  have hvW : v ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens) := ⟨hv, mem_chart_affAt sZ _⟩
  refine (analyticOnNhd_coeffFun sZ he W (formsAt sZ ω W) v hvW).congr ?_
  filter_upwards [(isOpen_target_inter_chart sZ e _).mem_nhds hvW] with w hw
  rw [coefAt, loc_holoVal sZ ω he hw, smul_detC_ej, coeffFun_of_mem sZ he W _ hw]

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma mem_of_mem_trans_source {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {v : 𝔼}
    (hv : v ∈ (e.symm.trans e').source) : v ∈ e.target ∧ e.symm v ∈ e'.source := by
  simpa using hv

/-- **Change of chart for the coefficient of a `(2,0)`-form.** -/
private lemma coefAt_eq_mul_jac {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    (hβ : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), ∀ v ∈ e.target,
      Forms.loc e β v = coefAt sZ e β v • detC)
    {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼} (hv : v ∈ (e.symm.trans e').source) :
    coefAt sZ e β v =
      coefAt sZ e' β ((e.symm.trans e') v) * jac (fderiv ℂ (e.symm.trans e') v) := by
  have h := (Forms.loc_eventuallyEq he he' β hv).eq_of_nhds
  simp only [Forms.tr] at h
  have hv' := mem_of_mem_trans_source sZ hv
  have hT : (e.symm.trans e') v ∈ e'.target := e'.map_source hv'.2
  have hd := differentiableAt_trans sZ he he' hv
  rw [coefAt, h, hβ e' he' _ hT, smul_compContinuousLinearMap', hd.fderiv_restrictScalars ℝ,
    detC_comp, smul_smul, smul_detC_ej]

/-- The one-form `α` under a change of chart, through its `(1,0)`-part. -/
private lemma hol10_one1_loc_eq {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ}
    {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼} (hv : v ∈ (e.symm.trans e').source) :
    hol10 (one1 (Forms.loc e α v)) =
      (hol10 (one1 (Forms.loc e' α ((e.symm.trans e') v)))).comp
        (fderiv ℂ (e.symm.trans e') v) := by
  have h := (Forms.loc_eventuallyEq he he' α hv).eq_of_nhds
  simp only [Forms.tr] at h
  have hd := differentiableAt_trans sZ he he' hv
  rw [h, one1_compContinuousLinearMap, hd.fderiv_restrictScalars ℝ, hol10_comp]

private lemma contDiffOn_comp_symm {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v ↦ (ρ (e.symm v) : ℂ)) e.target :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (Forms.contDiffOn_comp_symm_of_contMDiff hρ he)

private lemma differentiableAt_comp_symm {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼} (hv : v ∈ e.target) :
    DifferentiableAt ℝ (fun v ↦ (ρ (e.symm v) : ℂ)) v :=
  ((contDiffOn_comp_symm sZ hρ he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt
    (by simp)

/-- The derivative of a function read in two charts. -/
private lemma fderiv_comp_symm_eq {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼}
    (hv : v ∈ (e.symm.trans e').source) :
    fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v =
      (fderiv ℝ (fun w ↦ (ρ (e'.symm w) : ℂ)) ((e.symm.trans e') v)).comp
        ((fderiv ℂ (e.symm.trans e') v).restrictScalars ℝ) := by
  have hd := differentiableAt_trans sZ he he' hv
  have heq : (fun w ↦ (ρ (e.symm w) : ℂ)) =ᶠ[𝓝 v]
      (fun w ↦ (ρ (e'.symm w) : ℂ)) ∘ (e.symm.trans e') := by
    filter_upwards [(e.symm.trans e').open_source.mem_nhds hv] with w hw
    have hw' := mem_of_mem_trans_source sZ hw
    simp [e'.left_inv hw'.2]
  have hT : (e.symm.trans e') v ∈ e'.target := e'.map_source (mem_of_mem_trans_source sZ hv).2
  rw [heq.fderiv_eq, fderiv_comp v (differentiableAt_comp_symm sZ hρ he' hT)
    (hd.restrictScalars ℝ), hd.fderiv_restrictScalars ℝ]

open Classical in
/-- `ρ ∘ e⁻¹` on the target of `e`, extended by zero. -/
private noncomputable def cutR (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼)
    (ρ : ComplexPoints sZ → ℝ) (v : 𝔼) : ℝ :=
  if v ∈ e.target then ρ (e.symm v) else 0

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma cutR_of_mem {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} {v : 𝔼} (hv : v ∈ e.target) : cutR sZ e ρ v = ρ (e.symm v) :=
  if_pos hv

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma cutR_of_notMem {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} {v : 𝔼} (hv : v ∉ e.target) : cutR sZ e ρ v = 0 :=
  if_neg hv

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma cutR_eq_zero_of_notMem_image {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} {v : 𝔼} (hv : v ∉ e '' tsupport ρ) : cutR sZ e ρ v = 0 := by
  by_cases h : v ∈ e.target
  · rw [cutR_of_mem sZ h]
    by_contra h0
    exact hv ⟨e.symm v, subset_tsupport _ h0, e.right_inv h⟩
  · exact cutR_of_notMem sZ h

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma isCompact_image_tsupport [CompactSpace (ComplexPoints sZ)]
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {ρ : ComplexPoints sZ → ℝ}
    (hρe : tsupport ρ ⊆ e.source) : IsCompact (e '' tsupport ρ) :=
  (isClosed_tsupport ρ).isCompact.image_of_continuousOn (e.continuousOn.mono hρe)

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma image_tsupport_subset {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} (hρe : tsupport ρ ⊆ e.source) : e '' tsupport ρ ⊆ e.target := by
  rintro _ ⟨y, hy, rfl⟩
  exact e.map_source (hρe hy)

private lemma contDiff_cut [CompactSpace (ComplexPoints sZ)] {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (hρe : tsupport ρ ⊆ e.source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v ↦ (cutR sZ e ρ v : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ e.target
  · have h : (fun v ↦ (cutR sZ e ρ v : ℂ)) =ᶠ[𝓝 v] fun v ↦ (ρ (e.symm v) : ℂ) := by
      filter_upwards [e.open_target.mem_nhds hv] with w hw
      rw [cutR_of_mem sZ hw]
    exact ((contDiffOn_comp_symm sZ hρ he).contDiffAt
      (e.open_target.mem_nhds hv)).congr_of_eventuallyEq h
  · have hK := isCompact_image_tsupport sZ hρe
    have hvK : v ∉ e '' tsupport ρ := fun h ↦ hv (image_tsupport_subset sZ hρe h)
    have h : (fun v ↦ (cutR sZ e ρ v : ℂ)) =ᶠ[𝓝 v] fun _ ↦ 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hvK] with w hw
      rw [cutR_eq_zero_of_notMem_image sZ hw, Complex.ofReal_zero]
    exact contDiffAt_const.congr_of_eventuallyEq h

private lemma hasCompactSupport_cut [CompactSpace (ComplexPoints sZ)]
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {ρ : ComplexPoints sZ → ℝ}
    (hρe : tsupport ρ ⊆ e.source) : HasCompactSupport (fun v ↦ (cutR sZ e ρ v : ℂ)) :=
  HasCompactSupport.intro (isCompact_image_tsupport sZ hρe) fun v hv ↦ by
    rw [cutR_eq_zero_of_notMem_image sZ hv, Complex.ofReal_zero]

private lemma tsupport_cut_subset [CompactSpace (ComplexPoints sZ)]
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {ρ : ComplexPoints sZ → ℝ}
    (hρe : tsupport ρ ⊆ e.source) : tsupport (fun v ↦ (cutR sZ e ρ v : ℂ)) ⊆ e.target := by
  refine (closure_minimal (fun v hv ↦ ?_) (isCompact_image_tsupport sZ hρe).isClosed).trans
    (image_tsupport_subset sZ hρe)
  by_contra h
  exact hv (show (cutR sZ e ρ v : ℂ) = 0 by
    rw [cutR_eq_zero_of_notMem_image sZ h, Complex.ofReal_zero])

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma continuous_of_continuousOn_of_eq_zero {F : Type*} [NormedAddCommGroup F]
    {S K : Set 𝔼} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S) {f : 𝔼 → F}
    (hf : ContinuousOn f S) (h0 : ∀ v ∉ K, f v = 0) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v ∈ S
  · exact hf.continuousAt (hS.mem_nhds hv)
  · have hvK : v ∉ K := fun h ↦ hv (hKS h)
    have h : f =ᶠ[𝓝 v] fun _ ↦ 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hvK] with w hw using h0 w hw
    exact continuousAt_const.congr h.symm

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma integrable_of_continuousOn_of_eq_zero {F : Type*} [NormedAddCommGroup F]
    {S K : Set 𝔼} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S) {f : 𝔼 → F}
    (hf : ContinuousOn f S) (h0 : ∀ v ∉ K, f v = 0) : Integrable f :=
  (continuous_of_continuousOn_of_eq_zero hS hK hKS hf h0).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK h0)

open Classical in
/-- The density `ā · (∂ρ ∧ α^{1,0})` in the chart `e`, read against Lebesgue measure. -/
private noncomputable def dens (β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ)
    (α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼)
    (ρ : ComplexPoints sZ → ℝ) (v : 𝔼) : ℂ :=
  if v ∈ e.target then conj (coefAt sZ e β v) *
    det2 (hol10 (fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v)) (hol10 (one1 (Forms.loc e α v)))
  else 0

private lemma det2_hol10_eq (L : 𝔼 →L[ℝ] ℂ) (A : 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) :
    det2 (hol10 L) (hol10 (one1 A)) = wl 0 L * part 1 A - wl 1 L * part 0 A := by
  simp only [det2, wl_eq_hol10, part_eq_hol10, ej]

private lemma hol10_zero : hol10 0 = 0 := by
  ext u; simp [hol10_apply]

/-- **Change of chart for the density**: it transforms by the real Jacobian. -/
private lemma dens_eq_mul_normSq {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    (hβ : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), ∀ v ∈ e.target,
      Forms.loc e β v = coefAt sZ e β v • detC)
    (α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ)) {v : 𝔼}
    (hv : v ∈ (e.symm.trans e').source) :
    dens sZ β α e ρ v = dens sZ β α e' ρ ((e.symm.trans e') v) *
      Complex.normSq (jac (fderiv ℂ (e.symm.trans e') v)) := by
  have hv' := mem_of_mem_trans_source sZ hv
  have hT : (e.symm.trans e') v ∈ e'.target := e'.map_source hv'.2
  rw [dens, if_pos hv'.1, dens, if_pos hT, coefAt_eq_mul_jac sZ hβ he he' hv,
    hol10_one1_loc_eq sZ he he' hv, fderiv_comp_symm_eq sZ hρ he he' hv, hol10_comp, det2_comp,
    map_mul, Complex.normSq_eq_conj_mul_self]
  ring

private lemma fderiv_comp_symm_eq_zero {ρ : ComplexPoints sZ → ℝ}
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} {v : 𝔼} (hv : v ∈ e.target)
    (hρv : e.symm v ∉ tsupport ρ) : fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v = 0 := by
  have hc : ContinuousAt e.symm v := e.continuousAt_symm hv
  have h : (fun w ↦ (ρ (e.symm w) : ℂ)) =ᶠ[𝓝 v] fun _ ↦ 0 := by
    filter_upwards [hc.preimage_mem_nhds ((isClosed_tsupport ρ).isOpen_compl.mem_nhds hρv)]
      with w hw
    rw [image_eq_zero_of_notMem_tsupport hw, Complex.ofReal_zero]
  rw [h.fderiv_eq, fderiv_const_apply]

private lemma dens_eq_zero {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} {v : 𝔼} (hρv : v ∈ e.target → e.symm v ∉ tsupport ρ) :
    dens sZ β α e ρ v = 0 := by
  by_cases hv : v ∈ e.target
  · rw [dens, if_pos hv, fderiv_comp_symm_eq_zero sZ hv (hρv hv), hol10_zero]
    simp [det2]
  · exact if_neg hv

private lemma dens_eq_zero_of_notMem_image {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    {ρ : ComplexPoints sZ → ℝ} {v : 𝔼} (hv : v ∉ e '' tsupport ρ) : dens sZ β α e ρ v = 0 :=
  dens_eq_zero sZ fun hvt hρ ↦ hv ⟨e.symm v, hρ, e.right_inv hvt⟩

private lemma continuousOn_dens {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} (hα : Forms.IsSmoothOn Set.univ α)
    {ρ : ComplexPoints sZ → ℝ} (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    (hβa : AnalyticOnNhd ℂ (coefAt sZ e β) e.target) :
    ContinuousOn (dens sZ β α e ρ) e.target := by
  have hA : ContinuousOn (Forms.loc e α) e.target := by
    have := (hα e he).continuousOn
    simpa using this
  have hD : ContinuousOn (fun v ↦ fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v) e.target :=
    (contDiffOn_comp_symm sZ hρ he).continuousOn_fderiv_of_isOpen e.open_target (by simp)
  have hc : ContinuousOn (fun v ↦ conj (coefAt sZ e β v)) e.target :=
    Complex.continuous_conj.comp_continuousOn hβa.continuousOn
  refine ContinuousOn.congr (f := fun v ↦ conj (coefAt sZ e β v) *
      (wl 0 (fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v) * part 1 (Forms.loc e α v) -
        wl 1 (fderiv ℝ (fun w ↦ (ρ (e.symm w) : ℂ)) v) * part 0 (Forms.loc e α v))) ?_ ?_
  · exact hc.mul ((((wl 0).continuous.comp_continuousOn hD).mul
      ((part 1).continuous.comp_continuousOn hA)).sub
      (((wl 1).continuous.comp_continuousOn hD).mul ((part 0).continuous.comp_continuousOn hA)))
  · intro v hv
    rw [dens, if_pos hv, det2_hol10_eq]

/-- **Stokes, chart by chart.** -/
private lemma integral_cut_normSq [CompactSpace (ComplexPoints sZ)]
    {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    (hβ : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), ∀ v ∈ e.target,
      Forms.loc e β v = coefAt sZ e β v • detC)
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} (hα : Forms.IsSmoothOn Set.univ α)
    (hdα : ∀ x, Forms.d α x = β x) {ρ : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (hβa : AnalyticOnNhd ℂ (coefAt sZ e β) e.target)
    (hρe : tsupport ρ ⊆ e.source) :
    ∫ v, (cutR sZ e ρ v : ℂ) * (conj (coefAt sZ e β v) * coefAt sZ e β v) =
      - ∫ v, dens sZ β α e ρ v := by
  have hA : ContDiffOn ℝ 2 (Forms.loc e α) e.target := by
    have := hα e he
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact this.of_le ENat.LEInfty.out
  have hdβ : Forms.d α = β := funext hdα
  have hdA : ∀ v ∈ e.target, extDeriv (Forms.loc e α) v = coefAt sZ e β v • detC := by
    intro v hv
    rw [← Forms.loc_d isOpen_univ hα he hv (Set.mem_univ _), hdβ, hβ e he v hv]
  rw [integral_mul_normSq_eq e.open_target ((contDiff_cut sZ hρ he hρe).of_le
    (by simp)) (hasCompactSupport_cut sZ hρe) (tsupport_cut_subset sZ hρe) hβa
    hA hdA]
  congr 2
  funext v
  by_cases hv : v ∈ e.target
  · have h : (fun v ↦ (cutR sZ e ρ v : ℂ)) =ᶠ[𝓝 v] fun v ↦ (ρ (e.symm v) : ℂ) := by
      filter_upwards [e.open_target.mem_nhds hv] with w hw
      rw [cutR_of_mem sZ hw]
    rw [h.fderiv_eq, dens, if_pos hv]
  · have hK := isCompact_image_tsupport sZ hρe
    have hvK : v ∉ e '' tsupport ρ := fun h ↦ hv (image_tsupport_subset sZ hρe h)
    have h : (fun v ↦ (cutR sZ e ρ v : ℂ)) =ᶠ[𝓝 v] fun _ ↦ 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hvK] with w hw
      rw [cutR_eq_zero_of_notMem_image sZ hw, Complex.ofReal_zero]
    rw [h.fderiv_eq, fderiv_const_apply, hol10_zero, dens, if_neg hv]
    simp [det2]

private lemma integrable_cut_mul_dens [CompactSpace (ComplexPoints sZ)]
    {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} (hα : Forms.IsSmoothOn Set.univ α)
    {ρ ρ' : ComplexPoints sZ → ℝ} (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ' : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ')
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (hβa : AnalyticOnNhd ℂ (coefAt sZ e β) e.target)
    (hρe : tsupport ρ ⊆ e.source ∨ tsupport ρ' ⊆ e.source) :
    Integrable fun v ↦ (cutR sZ e ρ' v : ℂ) * dens sZ β α e ρ v := by
  have hcont : ContinuousOn (fun v ↦ (cutR sZ e ρ' v : ℂ) * dens sZ β α e ρ v) e.target :=
    (((contDiffOn_comp_symm sZ hρ' he).continuousOn).congr fun v hv ↦ by
      rw [cutR_of_mem sZ hv]).mul (continuousOn_dens sZ hα hρ he hβa)
  rcases hρe with h | h
  · exact integrable_of_continuousOn_of_eq_zero e.open_target (isCompact_image_tsupport sZ h)
      (image_tsupport_subset sZ h) hcont fun v hv ↦ by
        rw [dens_eq_zero_of_notMem_image sZ hv, mul_zero]
  · exact integrable_of_continuousOn_of_eq_zero e.open_target (isCompact_image_tsupport sZ h)
      (image_tsupport_subset sZ h) hcont fun v hv ↦ by
        rw [cutR_eq_zero_of_notMem_image sZ hv, Complex.ofReal_zero, zero_mul]

/-- The density integrated against a cut-off is independent of the chart. -/
private lemma integral_cut_mul_dens_eq [CompactSpace (ComplexPoints sZ)]
    {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    (hβ : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), ∀ v ∈ e.target,
      Forms.loc e β v = coefAt sZ e β v • detC)
    (α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ) {ρ ρ' : ComplexPoints sZ → ℝ}
    (hρ : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {e e' : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ))
    (hρe : tsupport ρ ⊆ e.source) (hρ'e' : tsupport ρ' ⊆ e'.source) :
    ∫ v, (cutR sZ e ρ' v : ℂ) * dens sZ β α e ρ v =
      ∫ w, (cutR sZ e' ρ' w : ℂ) * dens sZ β α e' ρ w := by
  refine integral_eq_of_density (T := e.symm.trans e')
    (fun v hv ↦ differentiableAt_trans sZ he he' hv) (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    (fun w hw ↦ ?_)
  · have hv' := mem_of_mem_trans_source sZ hv
    have hT : (e.symm.trans e') v ∈ e'.target := e'.map_source hv'.2
    rw [dens_eq_mul_normSq sZ hβ α hρ he he' hv, cutR_of_mem sZ hv'.1, cutR_of_mem sZ hT]
    have : e'.symm ((e.symm.trans e') v) = e.symm v := e'.left_inv hv'.2
    rw [this]
    ring
  · by_cases hvt : v ∈ e.target
    · have hs : e.symm v ∉ e'.source := fun h ↦ hv (mem_source_trans sZ hvt h)
      rw [cutR_of_mem sZ hvt, image_eq_zero_of_notMem_tsupport fun h ↦ hs (hρ'e' h),
        Complex.ofReal_zero, zero_mul]
    · rw [dens, if_neg hvt, mul_zero]
  · by_cases hwt : w ∈ e'.target
    · have hs : e'.symm w ∉ e.source := fun h ↦ hw (by
        simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
          Set.mem_inter_iff, Set.mem_preimage]
        exact ⟨hwt, h⟩)
      rw [dens_eq_zero sZ fun _ h ↦ hs (hρe h), mul_zero]
    · rw [cutR_of_notMem sZ hwt, Complex.ofReal_zero, zero_mul]

/-- **A closed holomorphic two-form on a compact surface that is exact vanishes.** If `β` is
`a dz₁ ∧ dz₂` with `a` holomorphic in every chart, and `β = dα` for a smooth one-form `α`, then
`β = 0`: by Stokes, `∫ β ∧ β̄ = 0`, while `β ∧ β̄` is a positive multiple of `|a|²` times the
Lebesgue measure in every chart. -/
private theorem eq_zero_of_eq_d_of_holomorphic [CompactSpace (ComplexPoints sZ)]
    [T2Space (ComplexPoints sZ)] {β : ComplexPoints sZ → 𝔼 [⋀^Fin 2]→L[ℝ] ℂ}
    (hβ : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), ∀ v ∈ e.target,
      Forms.loc e β v = coefAt sZ e β v • detC)
    (hβa : ∀ e ∈ atlas 𝔼 (ComplexPoints sZ), AnalyticOnNhd ℂ (coefAt sZ e β) e.target)
    {α : ComplexPoints sZ → 𝔼 [⋀^Fin 1]→L[ℝ] ℂ} (hα : Forms.IsSmoothOn Set.univ α)
    (hdα : ∀ x, Forms.d α x = β x) (x : ComplexPoints sZ) : β x = 0 := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : ComplexPoints sZ ↦ (chartAt 𝔼 y).source) (fun y ↦ (chartAt 𝔼 y).open_source)
    (fun y _ ↦ Set.mem_iUnion.2 ⟨y, mem_chart_source 𝔼 y⟩)
  set e : t → OpenPartialHomeomorph (ComplexPoints sZ) 𝔼 := fun i ↦ chartAt 𝔼 i.1 with he_def
  have he : ∀ i, e i ∈ atlas 𝔼 (ComplexPoints sZ) := fun i ↦ chart_mem_atlas 𝔼 i.1
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, 𝔼) isClosed_univ
    (fun i : t ↦ (e i).source) (fun i ↦ (e i).open_source) (by
      intro y _
      obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
      exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, hy⟩)
  have hsum : ∀ y, ∑ i, ρ i y = 1 := fun y ↦ by
    rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one (Set.mem_univ y)
  have hsm : ∀ i, ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i ↦ (ρ i).contMDiff
  set r : t → 𝔼 → ℝ := fun i v ↦ cutR sZ (e i) (ρ i) v * Complex.normSq (coefAt sZ (e i) β v)
    with hr
  -- (1) Stokes in each chart
  have h1 : ∀ i, ((∫ v, r i v : ℝ) : ℂ) = - ∫ v, dens sZ β α (e i) (ρ i) v := by
    intro i
    rw [← integral_cut_normSq sZ hβ hα hdα (hsm i) (he i) (hβa _ (he i)) (hρ i),
        ← integral_complex_ofReal]
    congr 1
    funext v
    simp only [hr, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  -- (2) insert the partition of unity
  have h2 : ∀ i, ∫ v, dens sZ β α (e i) (ρ i) v =
      ∑ j, ∫ v, (cutR sZ (e i) (ρ j) v : ℂ) * dens sZ β α (e i) (ρ i) v := by
    intro i
    rw [← integral_finset_sum _ fun j _ ↦ integrable_cut_mul_dens sZ hα (hsm i) (hsm j) (he i)
      (hβa _ (he i)) (Or.inl (hρ i))]
    congr 1
    funext v
    rw [← Finset.sum_mul]
    by_cases hv : v ∈ (e i).target
    · simp only [cutR_of_mem sZ hv]
      rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]
    · rw [dens, if_neg hv, mul_zero]
  -- (3) change charts
  have h3 : ∀ i j, ∫ v, (cutR sZ (e i) (ρ j) v : ℂ) * dens sZ β α (e i) (ρ i) v =
      ∫ v, (cutR sZ (e j) (ρ j) v : ℂ) * dens sZ β α (e j) (ρ i) v := fun i j ↦
    integral_cut_mul_dens_eq sZ hβ α (hsm i) (he i) (he j) (hρ i) (hρ j)
  -- (4) the derivatives of the partition of unity sum to zero
  have h4 : ∀ j, ∑ i, ∫ v, (cutR sZ (e j) (ρ j) v : ℂ) * dens sZ β α (e j) (ρ i) v = 0 := by
    intro j
    rw [← integral_finset_sum _ fun i _ ↦ integrable_cut_mul_dens sZ hα (hsm i) (hsm j) (he j)
      (hβa _ (he j)) (Or.inr (hρ j))]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)).trans
      (integral_zero 𝔼 ℂ)
    show ∑ i, (cutR sZ (e j) (ρ j) v : ℂ) * dens sZ β α (e j) (ρ i) v = 0
    rw [← Finset.mul_sum]
    by_cases hv : v ∈ (e j).target
    · have hd : ∑ i, fderiv ℝ (fun w ↦ (ρ i ((e j).symm w) : ℂ)) v = 0 := by
        rw [← fderiv_sum fun i _ ↦ differentiableAt_comp_symm sZ (hsm i) (he j) hv]
        have h : (∑ i, fun w ↦ (ρ i ((e j).symm w) : ℂ)) =ᶠ[𝓝 v] fun _ ↦ 1 := by
          filter_upwards [(e j).open_target.mem_nhds hv] with w hw
          simp only [Finset.sum_apply]
          rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
        rw [h.fderiv_eq, fderiv_const_apply]
      have : ∑ i, dens sZ β α (e j) (ρ i) v = 0 := by
        simp only [dens, if_pos hv, det2_hol10_eq]
        rw [show (∑ i, conj (coefAt sZ (e j) β v) *
            (wl 0 (fderiv ℝ (fun w ↦ (ρ i ((e j).symm w) : ℂ)) v) * part 1 (Forms.loc (e j) α v) -
              wl 1 (fderiv ℝ (fun w ↦ (ρ i ((e j).symm w) : ℂ)) v) * part 0 (Forms.loc (e j) α v)))
            = conj (coefAt sZ (e j) β v) *
              (wl 0 (∑ i, fderiv ℝ (fun w ↦ (ρ i ((e j).symm w) : ℂ)) v) *
                  part 1 (Forms.loc (e j) α v) -
                wl 1 (∑ i, fderiv ℝ (fun w ↦ (ρ i ((e j).symm w) : ℂ)) v) *
                  part 0 (Forms.loc (e j) α v)) by
          rw [map_sum, map_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
            Finset.mul_sum], hd]
        simp
      rw [this, mul_zero]
    · rw [cutR_of_notMem sZ hv, Complex.ofReal_zero, zero_mul]
  -- the total integral vanishes
  have htot : ∑ i, ((∫ v, r i v : ℝ) : ℂ) = 0 := by
    calc ∑ i, ((∫ v, r i v : ℝ) : ℂ) = - ∑ i, ∑ j,
          ∫ v, (cutR sZ (e j) (ρ j) v : ℂ) * dens sZ β α (e j) (ρ i) v := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [h1, h2]
          exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ h3 i j)
      _ = - ∑ j, ∑ i, ∫ v, (cutR sZ (e j) (ρ j) v : ℂ) * dens sZ β α (e j) (ρ i) v := by
          rw [Finset.sum_comm]
      _ = 0 := by rw [Finset.sum_eq_zero fun j _ ↦ h4 j, neg_zero]
  have hreal : ∑ i, ∫ v, r i v = 0 := by exact_mod_cast htot
  have hr0 : ∀ i v, 0 ≤ r i v := fun i v ↦ by
    simp only [hr]
    refine mul_nonneg ?_ (Complex.normSq_nonneg _)
    by_cases hv : v ∈ (e i).target
    · rw [cutR_of_mem sZ hv]; exact ρ.nonneg i _
    · rw [cutR_of_notMem sZ hv]
  have hzero : ∀ i, ∫ v, r i v = 0 := fun i ↦
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ integral_nonneg (hr0 i))).1 hreal i
      (Finset.mem_univ i)
  have hrc : ∀ i, Continuous (r i) := fun i ↦ by
    refine continuous_of_continuousOn_of_eq_zero (e i).open_target
      (isCompact_image_tsupport sZ (hρ i)) (image_tsupport_subset sZ (hρ i)) ?_ fun v hv ↦ by
        simp only [hr]; rw [cutR_eq_zero_of_notMem_image sZ hv, zero_mul]
    refine ContinuousOn.mul ?_ (Complex.continuous_normSq.comp_continuousOn
      (hβa _ (he i)).continuousOn)
    exact ((Forms.contDiffOn_comp_symm_of_contMDiff (hsm i) (he i)).continuousOn).congr
      fun v hv ↦ cutR_of_mem sZ hv
  have hrs : ∀ i, HasCompactSupport (r i) := fun i ↦
    HasCompactSupport.intro (isCompact_image_tsupport sZ (hρ i)) fun v hv ↦ by
      simp only [hr]; rw [cutR_eq_zero_of_notMem_image sZ hv, zero_mul]
  obtain ⟨i, hi⟩ : ∃ i, ρ i x ≠ 0 := by
    by_contra! h
    have := hsum x
    simp [h] at this
  have hx : x ∈ (e i).source := hρ i (subset_tsupport _ hi)
  have hrx : r i (e i x) = 0 := by
    by_contra hne
    have := (hrc i).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (hrs i)
      (fun v ↦ hr0 i v) hne
    linarith [hzero i]
  have hxt : e i x ∈ (e i).target := (e i).map_source hx
  simp only [hr, cutR_of_mem sZ hxt, (e i).left_inv hx, mul_eq_zero, hi, false_or,
    Complex.normSq_eq_zero] at hrx
  refine Forms.eq_of_loc_eq (β' := 0) (he i) hx ?_
  rw [hβ _ (he i) _ hxt, hrx, zero_smul, Forms.loc_zero]
  rfl

end StokesGlobal

/-! ### A regular two-form with vanishing analytic coefficient is zero -/

section Vanishing

open MMP.Analytic.ComplexPoints

omit [SmoothOfRelativeDimension 2 sZ] in
/-- The point of `Z` under a `ℂ`-point is closed. -/
private theorem isClosed_singleton_toScheme (x : ComplexPoints sZ) :
    IsClosed ({x.toScheme} : Set Z) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sZ x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

omit [SmoothOfRelativeDimension 2 sZ] in
/-- At a closed point of a scheme locally of finite type over `ℂ` the residue field is `ℂ`. -/
private theorem isIso_fromSpecResidueField_comp [LocallyOfFiniteType sZ] (p : Z)
    (hp : IsClosed ({p} : Set Z)) : IsIso (Z.fromSpecResidueField p ≫ sZ) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hp
  have hfin : IsFinite (Z.fromSpecResidueField p ≫ sZ) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← Spec.map_preimage (Z.fromSpecResidueField p ≫ sZ)] at hfin ⊢
  rw [IsFinite.SpecMap_iff] at hfin
  have : IsIso (Spec.preimage (Z.fromSpecResidueField p ≫ sZ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (IsAlgClosed.ringHom_bijective_of_isIntegral _ hfin.to_isIntegral)
  infer_instance

omit [SmoothOfRelativeDimension 2 sZ] in
/-- Every closed point of a scheme locally of finite type over `ℂ` is a `ℂ`-point. -/
private theorem exists_toScheme_eq [LocallyOfFiniteType sZ] (p : Z)
    (hp : IsClosed ({p} : Set Z)) : ∃ y : ComplexPoints sZ, y.toScheme = p := by
  have := isIso_fromSpecResidueField_comp sZ p hp
  refine ⟨⟨inv (Z.fromSpecResidueField p ≫ sZ) ≫ Z.fromSpecResidueField p, by simp⟩, ?_⟩
  simp only [ComplexPoints.toScheme, ComplexPoints.hom, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

/-- **A regular function vanishing at every `ℂ`-point is zero**, on a smooth complex scheme. -/
private theorem eq_zero_of_forall_evalHom_eq_zero {V : Z.Opens} (r : Γ(Z, V))
    (h : ∀ y : chart (sX := sZ) V, evalHom V y r = 0) : r = 0 := by
  have : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  have : IsReduced Z := isReduced_of_smooth sZ
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  refine eq_zero_of_basicOpen_eq_bot r ?_
  by_contra hne
  obtain ⟨p, hpD, hp⟩ := nonempty_inter_closedPoints
    (Set.nonempty_iff_ne_empty.2 fun h' ↦ hne (TopologicalSpace.Opens.ext h'))
    (Z.basicOpen r).isOpen.isLocallyClosed
  obtain ⟨y, rfl⟩ := exists_toScheme_eq sZ p hp
  have hyD : y ∈ chart (Z.basicOpen r) := mem_chart_iff.2 hpD
  have hres : IsUnit (Z.presheaf.map (homOfLE (Z.basicOpen_le r)).op r) :=
    RingedSpace.isUnit_res_basicOpen Z.toRingedSpace r
  have hu := hres.map (evalHom (Z.basicOpen r) ⟨y, hyD⟩)
  rw [← evalHom_res (Z.basicOpen_le r) ⟨y, hyD⟩ r, h] at hu
  exact not_isUnit_zero hu

/-- The generator `d g₀ ∧ d g₁` of `Ω²` over an affine open is `ιMulti (d g)` on algebraic
forms. -/
private lemma formsAlgEquiv_gen (W : Z.affineOpens) (g : Fin 2 → Γ(Z, W)) :
    letI := MMP.Mori.sectionAlgebra sZ W
    MMP.DeRham.formsAlgEquiv sZ 2 W (Stacks.DeRham.FormsGenerators.gen sZ (W : Z.Opens) g) =
      exteriorPower.ιMulti _ 2 (fun i ↦ KaehlerDifferential.D ℂ Γ(Z, W) (g i)) := by
  letI := MMP.Mori.sectionAlgebra sZ W
  rw [MMP.DeRham.formsAlgEquiv_apply, Stacks.DeRham.FormsGenerators.gen,
    ← Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_inv_ιMulti_d sZ W.2
      (isAffineOpen_top _) (by simp) 2 g, Iso.inv_hom_id_apply, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  simp [MMP.DeRham.kaehlerSpecEquiv]

/-- In the chart of étale coordinates `z`, the differential of `z_j` is the `j`-th coordinate. -/
private lemma dfan_coord (c : EtaleCoordinateChart sZ 2) {W : Z.Opens} (hWU : W ≤ c.U) {v : 𝔼}
    (hv : v ∈ (c.toChart (EuclideanSpace.equiv (Fin 2) ℂ).symm).target ∩
      (c.toChart (EuclideanSpace.equiv (Fin 2) ℂ).symm).symm ⁻¹' chart W) (j : Fin 2) :
    dfan sZ (c.toChart (EuclideanSpace.equiv (Fin 2) ℂ).symm) W v
        (Z.presheaf.map (homOfLE hWU).op (c.z j)) = EuclideanSpace.proj j := by
  set e := c.toChart (EuclideanSpace.equiv (Fin 2) ℂ).symm
  have heq : fan W (Z.presheaf.map (homOfLE hWU).op (c.z j)) ∘ e.symm =ᶠ[nhds v]
      ⇑(EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 2) j) := by
    filter_upwards [(isOpen_target_inter_chart sZ e W).mem_nhds hv] with w hw
    have hws : e.symm w ∈ c.W := by
      have := e.map_target hw.1
      rwa [EtaleCoordinateChart.source_toChart] at this
    simp only [Function.comp_apply]
    rw [fan_of_mem _ hw.2, ← evalHom_res hWU ⟨_, hw.2⟩, evalHom_apply,
      ← c.toOpenPartialHomeomorph_apply hws j]
    have h1 : e (e.symm w) = w := e.right_inv hw.1
    rw [EtaleCoordinateChart.toChart_apply] at h1
    have h2 : c.toOpenPartialHomeomorph (e.symm w) = (EuclideanSpace.equiv (Fin 2) ℂ) w := by
      conv_rhs => rw [← h1]
      rfl
    rw [h2]
    rfl
  unfold dfan
  rw [heq.fderiv_eq]
  exact (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 2) j).fderiv

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma presheaf_map_map {L : Z.Modules} {U V W : Z.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (x : Γ(L, U)) :
    L.presheaf.map (homOfLE h₁).op (L.presheaf.map (homOfLE h₂).op x) =
      L.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option maxRecDepth 20000 in
/-- **A regular two-form whose analytic coefficient vanishes everywhere is zero.** -/
private theorem eq_zero_of_coeffLin_eq_zero
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (h : ∀ (e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼) (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
      (W : Z.affineOpens) (v : 𝔼) (hv : v ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens)),
      coeffLin sZ he W hv (formsAt sZ ω W) = 0) : ω = 0 := by
  set L := Scheme.Hom.relativeDifferentialForms sZ ((2 : ℕ) : ℤ)
  haveI : Stacks.Ample.IsInvertibleModule Z L :=
    Stacks.Discriminant.isInvertible_relativeDifferentialForms sZ 2
  have hloc : ∀ x : Z, ∃ U₀ : Z.Opens, x ∈ U₀ ∧
      L.presheaf.map (homOfLE (le_top : U₀ ≤ ⊤)).op ω = 0 := by
    intro x
    obtain ⟨U₀, -, a, hxU₀, ha⟩ := MMP.Intersection.exists_isTrivializingGenerator L (V := ⊤)
        (x := x) trivial
    obtain ⟨r, hr⟩ := (ha U₀ le_rfl).2 (L.presheaf.map (homOfLE le_top).op ω)
    refine ⟨U₀, hxU₀, ?_⟩
    rw [← hr]
    beta_reduce
    suffices hr0 : r = 0 by rw [hr0, zero_smul]
    refine eq_zero_of_forall_evalHom_eq_zero sZ r fun y ↦ ?_
    obtain ⟨c, hyc⟩ := EtaleCoordinateChart.exists_mem_W (n := 2) y.1
    obtain ⟨W, hWle, hyW⟩ := exists_isAffineOpen_le sZ
      (show y.1 ∈ chart (U₀ ⊓ c.U) from
        mem_chart_iff.2 ⟨mem_chart_iff.1 y.2, mem_chart_iff.1 (c.subset hyc)⟩)
    have hW0 : (W : Z.Opens) ≤ U₀ := hWle.trans inf_le_left
    have hWU : (W : Z.Opens) ≤ c.U := hWle.trans inf_le_right
    set e := c.toChart (EuclideanSpace.equiv (Fin 2) ℂ).symm
    have he : e ∈ atlas 𝔼 (ComplexPoints sZ) := ⟨c, rfl⟩
    have hys : y.1 ∈ e.source := by rwa [EtaleCoordinateChart.source_toChart]
    have hv : e y.1 ∈ e.target ∩ e.symm ⁻¹' chart (W : Z.Opens) :=
      ⟨e.map_source hys, by rw [Set.mem_preimage, e.left_inv hys]; exact hyW⟩
    have hsec : L.presheaf.map (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op ω =
        Z.presheaf.map (homOfLE hW0).op r •
          L.presheaf.map (homOfLE hW0).op (L.presheaf.map (homOfLE le_rfl).op a) := by
      refine (presheaf_map_map hW0 le_top _).symm.trans ?_
      refine (congrArg (L.presheaf.map (homOfLE hW0).op) hr.symm).trans ?_
      exact L.val.map_smul (homOfLE hW0).op r _
    have hfω : formsAt sZ ω W = Z.presheaf.map (homOfLE hW0).op r •
        MMP.DeRham.formsAlgEquiv sZ 2 W
          (L.presheaf.map (homOfLE hW0).op (L.presheaf.map (homOfLE le_rfl).op a)) := by
      unfold formsAt
      rw [← map_smul]
      congr 1
    obtain ⟨s, hs⟩ := (ha W hW0).2 (Stacks.DeRham.FormsGenerators.gen sZ (W : Z.Opens)
      fun j ↦ Z.presheaf.map (homOfLE hWU).op (c.z j))
    have hs' : Stacks.DeRham.FormsGenerators.gen sZ (W : Z.Opens)
        (fun j ↦ Z.presheaf.map (homOfLE hWU).op (c.z j)) =
          s • L.presheaf.map (homOfLE hW0).op a := hs.symm
    have h2 : coeffLin sZ he W hv (MMP.DeRham.formsAlgEquiv sZ 2 W
        (Stacks.DeRham.FormsGenerators.gen sZ (W : Z.Opens)
          fun j ↦ Z.presheaf.map (homOfLE hWU).op (c.z j))) = 1 := by
      rw [formsAlgEquiv_gen, coeffLin_ιMulti, dfan_coord sZ c hWU hv, dfan_coord sZ c hWU hv]
      simp [det2]
    rw [hs', (MMP.DeRham.formsAlgEquiv sZ 2 W).map_smul, coeffLin_smul] at h2
    have h1 := h e he W _ hv
    rw [hfω, coeffLin_smul, presheaf_map_map] at h1
    have hne : coeffLin sZ he W hv (MMP.DeRham.formsAlgEquiv sZ 2 W
        (L.presheaf.map (homOfLE hW0).op a)) ≠ 0 := fun h0 ↦ by
      rw [h0, mul_zero] at h2
      exact zero_ne_one h2
    have h3 := (mul_eq_zero.1 h1).resolve_right hne
    rw [← evalHom_res hW0] at h3
    have key : ∀ y' : chart (sX := sZ) U₀, y'.1 = y.1 → evalHom U₀ y' r = evalHom U₀ y r :=
      fun y' hy' ↦ by rw [Subtype.ext hy']
    rwa [key _ (e.left_inv hys)] at h3
  choose U₀ hxU₀ hU₀ using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf Z.ringCatSheaf).obj L)
    U₀ ⊤ (fun x ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU₀ y⟩) _ _ fun x ↦ ?_
  change L.presheaf.map (homOfLE le_top).op ω = L.presheaf.map (homOfLE le_top).op 0
  rw [map_zero]
  exact hU₀ x

/-- If `ω^an` vanishes, then `ω = 0`. -/
private theorem eq_zero_of_holoVal_eq_zero
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (h : ∀ x, holoVal sZ ω x = 0) : ω = 0 := by
  refine eq_zero_of_coeffLin_eq_zero sZ ω fun e he W v hv ↦ ?_
  have h1 := loc_holoVal sZ ω he hv
  have h0 : Forms.loc e (holoVal sZ ω) v = 0 := by
    rw [Forms.loc, h]
    ext u
    rfl
  rw [h0] at h1
  have := congrArg (fun A : 𝔼 [⋀^Fin 2]→L[ℝ] ℂ ↦ A ![ej 0, ej 1]) h1
  simp only [smul_detC_ej] at this
  exact this.symm

end Vanishing

/-- **A nonzero holomorphic two-form is not exact**: if `ω^an = dα` for a global smooth
one-form `α` on the compact surface `Z^an`, then `ω = 0` (Stokes: `∫ ω ∧ ω̄ = 0`). -/
private theorem eq_zero_of_holoForm_eq_d (hP : IsProjectiveMorphism sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (α : ToType ((forms sZ 1 False).obj.obj (op ⊤)))
    (hα : (dHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 1 False).hom.app (op ⊤) α =
      holoForm sZ ω) : ω = 0 := by
  haveI := compactSpace_complexPoints_of_isProjective sZ hP
  haveI := t2Space_complexPoints_of_isProjective sZ hP
  have hsm : Forms.IsSmoothOn Set.univ (Forms.extend α.1) := by simpa using α.2.1
  refine eq_zero_of_holoVal_eq_zero sZ ω fun x ↦ ?_
  refine eq_zero_of_eq_d_of_holomorphic sZ (fun e he v hv ↦ loc_holoVal_eq_coefAt sZ ω he hv)
    (fun e he ↦ analyticOnNhd_coefAt_holoVal sZ ω he) hsm (fun y ↦ ?_) x
  exact congrArg (fun t : ToType ((forms sZ 2 True).obj.obj (op ⊤)) ↦ t.1 ⟨y, trivial⟩) hα

/-- The class `δ₁ δ₂ ω^an ∈ H²(Z^an, ℂ)`. -/
private noncomputable def extClassOf :
    (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤) →+ Sheaf.H (constC sZ) 2 :=
  ((constComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ).extClass.postcomp
      _ (by norm_num : 1 + 1 = 2)).comp
    (((closedComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 0).extClass.postcomp
      _ (zero_add 1)).comp
      ((Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).symm.toAddMonoidHom.comp
        (holoForm sZ)))

private theorem extClassOf_injective (hP : IsProjectiveMorphism sZ) :
    Function.Injective (extClassOf sZ) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨v, hv⟩ := exists_comp_eq_of_comp_extClass_comp_extClass_eq_zero _
    (constComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ)
    (closedComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 0)
    (forms_zero_H_one sZ hP) _ hω
  refine eq_zero_of_holoForm_eq_d sZ hP ω (Sheaf.H.equiv₀ _ Limits.isTerminalTop v) ?_
  have h := Sheaf.H.equiv₀_naturality Limits.isTerminalTop
    (dHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 1 False) v
  refine h.trans ?_
  rw [show Sheaf.H.map (dHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 1 False) 0 v =
    v.comp (Ext.mk₀ _) (add_zero 0) from rfl, hv]
  exact (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).apply_symm_apply _

/-- The class is `ℂ`-linear: multiplying `ω` by `c` multiplies its class by `c` on the
coefficients. -/
private theorem extClassOf_smul (c : ℂ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    extClassOf sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
        sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) =
      (extClassOf sZ ω).comp (Ext.mk₀ (mulC sZ c)) (add_zero 2) := by
  set w := (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).symm (holoForm sZ ω) with hw
  have hw' : (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).symm
      (holoForm sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
        sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω)) =
      w.comp (Ext.mk₀ (smulHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) c 2 True))
        (add_zero 0) := by
    apply (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).injective
    rw [AddEquiv.apply_symm_apply, holoForm_smul]
    have h := Sheaf.H.equiv₀_naturality Limits.isTerminalTop
      (smulHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) c 2 True) w
    rw [show Sheaf.H.map (smulHom (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) c 2 True) 0 w =
      w.comp (Ext.mk₀ _) (add_zero 0) from rfl] at h
    rw [← h, hw, AddEquiv.apply_symm_apply]
  change (((Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).symm
      (holoForm sZ _)).comp
        (closedComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 0).extClass
        (zero_add 1)).comp
      (constComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ).extClass
        (by norm_num : 1 + 1 = 2) = _
  rw [hw']
  exact comp_extClass_comp_extClass_naturality
    (constComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ)
    (closedComplex_shortExact (EuclideanSpace ℂ (Fin 2)) (ComplexPoints sZ) ℂ 0)
    (mulC sZ c) (smulHom _ _ c 0 False) (smulHom _ _ c 1 True) (smulHom _ _ c 1 False)
    (smulHom _ _ c 2 True) (constIncl_smulHom _ _ c) (dHom_smulHom _ _ c 0 False)
    (closedIncl_smulHom _ _ c 1) (dHom_smulHom _ _ c 1 False) w

/-! ### Pulling back the analytic two-form -/

omit [SmoothOfRelativeDimension 2 sZ] in
/-- **Realized morphisms are holomorphic in atlas charts.** -/
private theorem contDiffOn_rd_realize {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ] [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z')
    (hg : g ≫ sZ' = sZ) {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) {e' : OpenPartialHomeomorph (ComplexPoints sZ') 𝔼}
    (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ')) :
    ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (rd (realize g hg) e e') (rdSrc (realize g hg) e e') := by
  have hc : ContMDiff 𝓘(ℂ, 𝔼) 𝓘(ℂ, 𝔼) ((⊤ : ℕ∞) : WithTop ℕ∞) (realize g hg) :=
    ComplexPoints.contMDiff_realize _ g hg
  have h2s : Set.MapsTo (realize g hg) (e.source ∩ realize g hg ⁻¹' e'.source) e'.source :=
    fun _ hx ↦ hx.2
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' (IsManifold.subset_maximalAtlas he)
    (IsManifold.subset_maximalAtlas he') Set.inter_subset_left h2s).1 hc.contMDiffOn
  have himg : e.extend 𝓘(ℂ, 𝔼) '' (e.source ∩ realize g hg ⁻¹' e'.source) =
      rdSrc (realize g hg) e e' := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.map_source hx.1, by
        simpa [rdSrc, OpenPartialHomeomorph.extend, e.left_inv hx.1] using hx.2⟩
    · intro hv
      exact ⟨e.symm v, ⟨e.map_target hv.1, hv.2⟩, by
        simp [OpenPartialHomeomorph.extend, e.right_inv hv.1]⟩
  rw [himg] at h
  exact h.congr fun v _ ↦ by simp [rd, OpenPartialHomeomorph.extend]

omit [SmoothOfRelativeDimension 2 sZ] in
/-- The realization of a morphism of smooth complex surfaces is smooth. -/
private theorem isSmoothMap_analyticMap {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ] [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z')
    (hg : g ≫ sZ' = sZ) : IsSmoothMap 𝔼 ⇑(analyticMap g hg) :=
  ⟨continuous_realize g hg, fun _ he _ he' ↦
    (contDiffOn_rd_realize sZ sZ' g hg he he').restrict_scalars ℝ⟩

omit [SmoothOfRelativeDimension 2 sZ] in
/-- Evaluating the pull-back of a function along `g` at `y` is evaluating it at `g y`. -/
private lemma evalHom_appLE {Z' : Scheme.{0}} {sZ' : Z' ⟶ Spec (.of ℂ)} (g : Z ⟶ Z')
    (hg : g ≫ sZ' = sZ) {W : Z.Opens} {W' : Z'.Opens} (h : W ≤ g ⁻¹ᵁ W')
    (y : chart (sX := sZ) W) (f : Γ(Z', W')) :
    evalHom W y ((g.appLE W' W h).hom f) =
      evalHom W' ⟨realize g hg y.1, (mem_chart_preimage_iff g hg W' y.1).1
          (chart_mono h y.2)⟩ f := by
  simp only [evalHom, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply (g.appLE W' W h), Scheme.Hom.appLE_comp_appLE]
  rfl

omit [SmoothOfRelativeDimension 2 sZ] in
private lemma fan_appLE {Z' : Scheme.{0}} {sZ' : Z' ⟶ Spec (.of ℂ)} (g : Z ⟶ Z')
    (hg : g ≫ sZ' = sZ) {W : Z.Opens} {W' : Z'.Opens} (h : W ≤ g ⁻¹ᵁ W') (f : Γ(Z', W'))
    {y : ComplexPoints sZ} (hy : y ∈ chart W) :
    fan W ((g.appLE W' W h).hom f) y = fan W' f (realize g hg y) := by
  rw [fan_of_mem _ hy, fan_of_mem _ ((mem_chart_preimage_iff g hg W' y).1 (chart_mono h hy)),
    evalHom_appLE sZ g hg h ⟨y, hy⟩ f]

/-- **Chain rule for `d f^an`** along a realized morphism. -/
private lemma dfan_appLE {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    {e' : OpenPartialHomeomorph (ComplexPoints sZ') 𝔼} (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ'))
    {W : Z.Opens} {W' : Z'.Opens} (h : W ≤ g ⁻¹ᵁ W') {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart W) (hv' : realize g hg (e.symm v) ∈ e'.source)
    (hrd : rd (realize g hg) e e' v ∈ e'.target ∩ e'.symm ⁻¹' chart W') (f : Γ(Z', W')) :
    dfan sZ e W v ((g.appLE W' W h).hom f) =
      (dfan sZ' e' W' (rd (realize g hg) e e' v) f).comp (fderiv ℂ (rd (realize g hg) e e') v) := by
  have hsrc : v ∈ rdSrc (realize g hg) e e' := ⟨hv.1, hv'⟩
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' (chart W ∩ realize g hg ⁻¹' e'.source)) :=
    e.isOpen_inter_preimage_symm ((isOpen_chart sZ W).inter
      (e'.open_source.preimage (continuous_realize g hg)))
  have heq : fan W ((g.appLE W' W h).hom f) ∘ e.symm =ᶠ[nhds v]
      (fan W' f ∘ e'.symm) ∘ rd (realize g hg) e e' := by
    filter_upwards [hO.mem_nhds ⟨hv.1, hv.2, hv'⟩] with w hw
    simp only [Function.comp_apply, rd]
    rw [e'.left_inv hw.2.2, fan_appLE sZ g hg h f hw.2.1]
  have hd : DifferentiableAt ℂ (rd (realize g hg) e e') v :=
    ((contDiffOn_rd_realize sZ sZ' g hg he he').contDiffAt
      ((isOpen_rdSrc (continuous_realize g hg) e e').mem_nhds hsrc)).differentiableAt (by simp)
  unfold dfan
  rw [heq.fderiv_eq]
  exact fderiv_comp v (differentiableAt_fan sZ' he' hrd f) hd

/-- The coefficient does not depend on how its point is written. -/
private lemma coeffLin_congr {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼}
    (he : e ∈ atlas 𝔼 (ComplexPoints sZ)) (U : Z.Opens) {v v' : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart U) (hv' : v' ∈ e.target ∩ e.symm ⁻¹' chart U)
    (hvv : v = v') x : coeffLin sZ he U hv x = coeffLin sZ he U hv' x := by
  subst hvv
  rfl

/-- **The coefficient of a pulled-back form** is the coefficient of the form times the complex
Jacobian determinant of the realized morphism. -/
private lemma coeffLin_appLE {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    {e : OpenPartialHomeomorph (ComplexPoints sZ) 𝔼} (he : e ∈ atlas 𝔼 (ComplexPoints sZ))
    {e' : OpenPartialHomeomorph (ComplexPoints sZ') 𝔼} (he' : e' ∈ atlas 𝔼 (ComplexPoints sZ'))
    {W : Z.Opens} {W' : Z'.Opens} (h : W ≤ g ⁻¹ᵁ W') {v : 𝔼}
    (hv : v ∈ e.target ∩ e.symm ⁻¹' chart W) (hv' : realize g hg (e.symm v) ∈ e'.source)
    (hrd : rd (realize g hg) e e' v ∈ e'.target ∩ e'.symm ⁻¹' chart W') x :
    letI := MMP.Mori.sectionAlgebra sZ' W'
    letI := MMP.Mori.sectionAlgebra sZ W
    letI : Algebra Γ(Z', W') Γ(Z, W) := (g.appLE W' W h).hom.toAlgebra
    haveI := isScalarTower_appLE sZ' sZ g hg h
    coeffLin sZ he W hv (KaehlerDifferential.mapExteriorPower ℂ Γ(Z', W') Γ(Z, W) 2 x) =
      coeffLin sZ' he' W' hrd x * jac (fderiv ℂ (rd (realize g hg) e e') v) := by
  letI := MMP.Mori.sectionAlgebra sZ' W'
  letI := MMP.Mori.sectionAlgebra sZ W
  letI : Algebra Γ(Z', W') Γ(Z, W) := (g.appLE W' W h).hom.toAlgebra
  haveI := isScalarTower_appLE sZ' sZ g hg h
  induction x using exteriorPower_two_induction with
  | h0 => simp
  | hadd x y hx hy => simp [hx, hy, add_mul]
  | hneg x hx => simp [hx]
  | hgen a w =>
    rw [map_smul, ← algebraMap_smul Γ(Z, W) a, coeffLin_smul, coeffLin_smul,
      KaehlerDifferential.mapExteriorPower_ιMulti]
    simp only [KaehlerDifferential.map_D]
    rw [coeffLin_ιMulti, coeffLin_ιMulti]
    change evalHom W ⟨_, hv.2⟩ ((g.appLE W' W h).hom a) *
        det2 (dfan sZ e W v ((g.appLE W' W h).hom (w 0)))
          (dfan sZ e W v ((g.appLE W' W h).hom (w 1))) = _
    rw [dfan_appLE sZ sZ' g hg he he' h hv hv' hrd, dfan_appLE sZ sZ' g hg he he' h hv hv' hrd,
      det2_comp, evalHom_appLE sZ g hg h ⟨_, hv.2⟩ a]
    have : (⟨e'.symm (rd (realize g hg) e e' v), hrd.2⟩ : chart (sX := sZ') W') =
        ⟨realize g hg (e.symm v), (mem_chart_preimage_iff g hg W' _).1 (chart_mono h hv.2)⟩ :=
      Subtype.ext (e'.left_inv hv')
    rw [this]
    ring

set_option maxRecDepth 20000 in
/-- **The analytic form of a pulled-back algebraic form is the pulled-back analytic form**, at
every point. -/
private theorem pb_holoVal {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)) (y : ComplexPoints sZ) :
    pb (realize g hg) (holoVal sZ' ω) y = holoVal sZ (formPull sZ sZ' g hg ω) y := by
  obtain ⟨W, hWle, hyW⟩ := exists_isAffineOpen_le sZ
    ((mem_chart_preimage_iff g hg (affAt sZ' (realize g hg y) : Z'.Opens) y).2
      (mem_chart_affAt sZ' (realize g hg y)))
  have hyc : y ∈ (chartAt 𝔼 y).source := mem_chart_source _ y
  have hv : chartAt 𝔼 y y ∈ (chartAt 𝔼 y).target ∩ (chartAt 𝔼 y).symm ⁻¹' chart (W : Z.Opens) :=
    mem_chartAt_target_inter sZ hyW
  have hv' : realize g hg ((chartAt 𝔼 y).symm (chartAt 𝔼 y y)) ∈
      (chartAt 𝔼 (realize g hg y)).source := by
    rw [(chartAt 𝔼 y).left_inv hyc]; exact mem_chart_source _ _
  have hrdv : rd (realize g hg) (chartAt 𝔼 y) (chartAt 𝔼 (realize g hg y)) (chartAt 𝔼 y y) =
      chartAt 𝔼 (realize g hg y) (realize g hg y) := by
    simp only [rd, (chartAt 𝔼 y).left_inv hyc]
  have hrd : rd (realize g hg) (chartAt 𝔼 y) (chartAt 𝔼 (realize g hg y)) (chartAt 𝔼 y y) ∈
      (chartAt 𝔼 (realize g hg y)).target ∩ (chartAt 𝔼 (realize g hg y)).symm ⁻¹'
        chart (affAt sZ' (realize g hg y) : Z'.Opens) := by
    rw [hrdv]; exact mem_chartAt_target_inter sZ' (mem_chart_affAt sZ' _)
  have hd : DifferentiableAt ℂ (rd (realize g hg) (chartAt 𝔼 y) (chartAt 𝔼 (realize g hg y)))
      (chartAt 𝔼 y y) :=
    ((contDiffOn_rd_realize sZ sZ' g hg (chart_mem_atlas 𝔼 y)
      (chart_mem_atlas 𝔼 (realize g hg y))).contDiffAt
      ((isOpen_rdSrc (continuous_realize g hg) _ _).mem_nhds
        (mem_rdSrc_chartAt y))).differentiableAt
        (by simp)
  have hA : letI := MMP.Mori.sectionAlgebra sZ' (affAt sZ' (realize g hg y) : Z'.Opens)
      letI := MMP.Mori.sectionAlgebra sZ (W : Z.Opens)
      letI : Algebra Γ(Z', (affAt sZ' (realize g hg y) : Z'.Opens)) Γ(Z, (W : Z.Opens)) :=
        (g.appLE _ _ hWle).hom.toAlgebra
      haveI := isScalarTower_appLE sZ' sZ g hg hWle
      formsAt sZ (formPull sZ sZ' g hg ω) W =
        KaehlerDifferential.mapExteriorPower ℂ Γ(Z', (affAt sZ' (realize g hg y) : Z'.Opens))
          Γ(Z, (W : Z.Opens)) 2 (formsAt sZ' ω (affAt sZ' (realize g hg y))) :=
    by
      haveI := isScalarTower_appLE sZ' sZ g hg hWle
      exact formsAlgEquiv_res_pullback sZ' sZ g hg 2 (affAt sZ' (realize g hg y)) W hWle ω
  have hcoeff : holoCoeff sZ (formPull sZ sZ' g hg ω) y = holoCoeff sZ' ω (realize g hg y) *
      jac (fderiv ℂ (rd (realize g hg) (chartAt 𝔼 y) (chartAt 𝔼 (realize g hg y)))
        (chartAt 𝔼 y y)) := by
    unfold holoCoeff
    rw [coeffLin_formsAt_eq sZ (formPull sZ sZ' g hg ω) (chart_mem_atlas 𝔼 y)
      (mem_chartAt_target_inter sZ (mem_chart_affAt sZ y)) hv, hA,
      coeffLin_appLE sZ sZ' g hg (chart_mem_atlas 𝔼 y) (chart_mem_atlas 𝔼 (realize g hg y)) hWle
        hv hv' hrd,
      coeffLin_congr sZ' (chart_mem_atlas 𝔼 (realize g hg y)) _ hrd
        (mem_chartAt_target_inter sZ' (mem_chart_affAt sZ' _)) hrdv]
  unfold pb holoVal
  rw [hd.fderiv_restrictScalars ℝ, smul_compContinuousLinearMap', detC_comp, smul_smul, hcoeff]

/-- **The analytic form of a pulled-back algebraic form is the pulled-back analytic form.** -/
private theorem pbHom_holoForm {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)) :
    (pbHom (analyticMap g hg) (isSmoothMap_analyticMap sZ sZ' g hg) 2 True).hom.app (op ⊤)
        (holoForm sZ' ω) = holoForm sZ (formPull sZ sZ' g hg ω) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  refine (pbHom_app_apply (analyticMap g hg) (isSmoothMap_analyticMap sZ sZ' g hg) ⊤
    (holoForm sZ' ω) x).trans ?_
  change pb (realize g hg) (Forms.extend fun y : (⊤ : TopologicalSpace.Opens
      (TopCat.of (ComplexPoints sZ'))) ↦ holoVal sZ' ω y.1) x.1 = holoVal sZ
          (formPull sZ sZ' g hg ω) x.1
  rw [extend_top_eq sZ' (holoVal sZ' ω)]
  exact pb_holoVal sZ sZ' g hg ω x.1

/-- The class is natural for pull-back along morphisms of surfaces over `ℂ`. -/
private theorem extClassOf_natural {Z' : Scheme.{0}} (sZ' : Z' ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ'] (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)) :
    (Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg) (.of (ULift ℤ)))).comp
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ 2
          (extClassOf sZ' ω)) (zero_add 2) =
      (extClassOf sZ (formPull sZ sZ' g hg ω)).comp
        (Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg) (.of ℂ)))
            (add_zero 2) := by
  have hf := isSmoothMap_analyticMap sZ sZ' g hg
  let w' := (Sheaf.H.equiv₀ (forms sZ' 2 True) Limits.isTerminalTop).symm (holoForm sZ' ω)
  obtain ⟨u, hu⟩ := (Ext.mk₀_bijective _ _).2 w'
  let w := Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg) (.of (ULift ℤ)) ≫
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).map u)
  have hS₁ : (constComplexTop 𝔼 (ComplexPoints sZ) ℂ).ShortExact :=
    constComplex_shortExact 𝔼 (ComplexPoints sZ) ℂ
  have hS₂ : (closedComplexTop 𝔼 (ComplexPoints sZ) ℂ 1).ShortExact :=
    closedComplex_shortExact 𝔼 (ComplexPoints sZ) ℂ 0
  have hS₁' : (constComplexTop 𝔼 (ComplexPoints sZ') ℂ).ShortExact :=
    constComplex_shortExact 𝔼 (ComplexPoints sZ') ℂ
  have hS₂' : (closedComplexTop 𝔼 (ComplexPoints sZ') ℂ 1).ShortExact :=
    closedComplex_shortExact 𝔼 (ComplexPoints sZ') ℂ 0
  have h0 : w.comp (Ext.mk₀ (pbPull (analyticMap g hg) hf 2 True)) (add_zero 0) =
      (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).symm
        (holoForm sZ (formPull sZ sZ' g hg ω)) := by
    apply (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop).injective
    refine Eq.trans ?_ (AddEquiv.apply_symm_apply _ _).symm
    refine Eq.trans ?_ (pbHom_holoForm sZ sZ' g hg ω)
    refine (congrArg (Sheaf.H.equiv₀ (forms sZ 2 True) Limits.isTerminalTop)
      (Ext.mk₀_comp_mk₀ _ _)).trans ?_
    refine (equiv₀_mk₀_constPullbackComparison_comp (analyticMap g hg) u
      (pbHom (analyticMap g hg) hf 2 True)).trans ?_
    refine congrArg ((pbHom (analyticMap g hg) hf 2 True).hom.app (op ⊤)) ?_
    rw [hu]
    exact AddEquiv.apply_symm_apply _ _
  have key := comp_extClass_comp_extClass_naturality_of_hom hS₁ hS₂
    (hS₁'.map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)))
    (hS₂'.map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)))
    { τ₁ := MMP.Analytic.pullbackConstComparison (analyticMap g hg) (.of ℂ)
      τ₂ := pbPull (analyticMap g hg) hf 0 False
      τ₃ := pbPull (analyticMap g hg) hf 1 True
      comm₁₂ := constIncl_square (analyticMap g hg) hf
      comm₂₃ := (map_comp_homEquiv_symm _ _ _ _ _ (dHom_pbHom (analyticMap g hg) hf 0 False)).symm }
    { τ₁ := pbPull (analyticMap g hg) hf 1 True
      τ₂ := pbPull (analyticMap g hg) hf 1 False
      τ₃ := pbPull (analyticMap g hg) hf 2 True
      comm₁₂ := (map_comp_homEquiv_symm _ _ _ _ _ (closedIncl_pbHom (analyticMap g hg) hf 1)).symm
      comm₂₃ := (map_comp_homEquiv_symm _ _ _ _ _ (dHom_pbHom (analyticMap g hg) hf 1 False)).symm }
    rfl w
  have hmap := mapExactFunctor_comp_extClass_comp_extClass
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)) hS₁' hS₂' w'
  have hP : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ 0 w' =
      Ext.mk₀ ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).map u) := by
    rw [← hu]
    exact Ext.mapExactFunctor_mk₀ _ _
  have hL := hmap.trans (congrArg (fun t ↦ (t.comp
      (hS₂'.map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg))).extClass
        (zero_add 1)).comp
      (hS₁'.map_of_exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg))).extClass
        (by norm_num : 1 + 1 = 2)) hP)
  have e : extClassOf sZ (formPull sZ sZ' g hg ω) =
      ((w.comp (Ext.mk₀ (pbPull (analyticMap g hg) hf 2 True)) (add_zero 0)).comp
        hS₂.extClass (zero_add 1)).comp hS₁.extClass (by norm_num : 1 + 1 = 2) := by
    rw [h0]; rfl
  refine (congrArg (fun t ↦ (Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg)
    (.of (ULift ℤ)))).comp t (zero_add 2)) hL).trans ?_
  refine (comp_comp_extClass_eq_of_comp_eq_id _ _ _ _ _ _
    (MMP.Analytic.pullbackConstComparison_comp_constPullbackComparison (analyticMap g hg)
      (.of ℂ))).trans ?_
  refine (congrArg (fun t ↦ t.comp (Ext.mk₀ (MMP.Analytic.constPullbackComparison
    (analyticMap g hg) (.of ℂ))) (add_zero 2)) key.symm).trans ?_
  exact congrArg (fun t ↦ t.comp (Ext.mk₀ (MMP.Analytic.constPullbackComparison
    (analyticMap g hg) (.of ℂ))) (add_zero 2)) e.symm

end ExtClass

/-! ### The de Rham class map -/

/-- **The de Rham class of a regular two-form on a surface.** For `sZ : Z ⟶ Spec ℂ` smooth of
relative dimension `2`, the map `H⁰(Z, Ω²_{Z/ℂ}) → H²(Z^an, ℂ_{Z^an})` sending `ω` to the class of
the closed smooth two-form `ω^an` under the de Rham resolution of the constant sheaf: with `𝒜ᵏ`
the sheaf of smooth complex `k`-forms on `Z^an` and `𝒵ᵏ ⊆ 𝒜ᵏ` the closed ones, it is the image of
`ω^an ∈ Γ(Z^an, 𝒵²)` under the connecting maps of `0 → 𝒵¹ → 𝒜¹ → 𝒵² → 0` and
`0 → ℂ → 𝒜⁰ → 𝒵¹ → 0`. -/
public noncomputable def topFormBettiClass {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ] :
    (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤) →+
      Sheaf.H ((constantSheaf (Opens.grothendieckTopology (analyticSpace sZ))
        AddCommGrpCat.{0}).obj (.of ℂ)) 2 :=
  extClassOf sZ

/-- **The de Rham class of a holomorphic two-form on a surface.** For a smooth projective complex
surface `Z`, the de Rham class map `topFormBettiClass : H⁰(Z, Ω²_{Z/ℂ}) → H²(Z^an, ℂ_{Z^an})` is
injective and `ℂ`-linear, and it commutes with pull-back: for a morphism `g : Z ⟶ Z'` over `ℂ` of
smooth projective complex surfaces with realized map `f = g^an`, the classes `f⁻¹ (cl ω)` and
`cl (g^* ω)` agree in `Ext²(ℤ_{Z^an}, f⁻¹ ℂ_{Z'^an})` after comparison through the canonical
maps `MMP.Analytic.constPullbackComparison` of constant sheaves. Here `g^* ω` is the image of
`ω` under the unit of `g^* ⊣ g_*` and the canonical map `g^* Ω²_{Z'/ℂ} ⟶ Ω²_{Z/ℂ}`. -/
@[mmp "lem_fourfold_surface_top_form_betti_injective"]
public theorem topFormBettiClass_injective_and_pullback :
    (∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sZ],
        IsProjectiveMorphism sZ → Function.Injective (topFormBettiClass sZ)) ∧
      (∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sZ],
        IsProjectiveMorphism sZ → ∀ (c : ℂ)
          (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)),
          topFormBettiClass sZ ((show Z.ringCatSheaf.obj.obj (op ⊤) from
              sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) =
            (topFormBettiClass sZ ω).comp (Ext.mk₀ ((constantSheaf _ AddCommGrpCat.{0}).map
              (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)))) (add_zero 2)) ∧
      (∀ {Z Z' : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (sZ' : Z' ⟶ Spec (.of ℂ))
          [SmoothOfRelativeDimension 2 sZ] [SmoothOfRelativeDimension 2 sZ'],
          IsProjectiveMorphism sZ → IsProjectiveMorphism sZ' →
          ∀ (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
            (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)),
          (Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg) (.of (ULift ℤ)))).comp
              ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).mapExtAddHom _ _ 2
                (topFormBettiClass sZ' ω)) (zero_add 2) =
            (topFormBettiClass sZ
                ((Scheme.Hom.relativeDifferentialFormsMap g sZ' sZ (𝟙 _) (by simp [hg]) 2).app ⊤
                  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app ⊤ ω))).comp
              (Ext.mk₀ (MMP.Analytic.constPullbackComparison (analyticMap g hg) (.of ℂ)))
              (add_zero 2)) :=
  ⟨fun sZ _ hP ↦ extClassOf_injective sZ hP, fun sZ _ _ c ω ↦ extClassOf_smul sZ c ω,
    fun sZ sZ' _ _ _ _ g hg ω ↦ extClassOf_natural sZ sZ' g hg ω⟩

/-- **The de Rham class of a holomorphic two-form, in singular cohomology.** Composing
`topFormBettiClass` with a comparison `H²(Z^an, ℂ_{Z^an}) ≃+ H²_sing(Z^an; ℂ)` from
`MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology_ring` gives a family of
`ℂ`-linear maps `cl_Z : H⁰(Z, Ω²_{Z/ℂ}) → H²_sing(Z^an; ℂ)`, one for every smooth projective
complex surface, each injective, with `cl_Z (g^* ω) = (g^an)^* (cl_{Z'} ω)` for every morphism
`g : Z ⟶ Z'` over `ℂ`. -/
public theorem exists_injective_topFormBettiClass :
    ∃ cl : ∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)), IsProjectiveMorphism sZ →
        SmoothOfRelativeDimension 2 sZ →
        ((Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤) →+
          relativeSingularCohomology ℂ (.of ℂ ℂ) (analyticSpace sZ) ∅ 2),
      (∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ)
          (hS : SmoothOfRelativeDimension 2 sZ), Function.Injective (cl sZ hP hS)) ∧
      (∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ)
          (hS : SmoothOfRelativeDimension 2 sZ) (c : ℂ)
          (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)),
          cl sZ hP hS ((show Z.ringCatSheaf.obj.obj (op ⊤) from
              sZ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) • ω) = c • cl sZ hP hS ω) ∧
      (∀ {Z Z' : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (sZ' : Z' ⟶ Spec (.of ℂ))
          (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ)
          (hP' : IsProjectiveMorphism sZ') (hS' : SmoothOfRelativeDimension 2 sZ')
          (g : Z ⟶ Z') (hg : g ≫ sZ' = sZ)
          (ω : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)),
          cl sZ hP hS
              ((Scheme.Hom.relativeDifferentialFormsMap g sZ' sZ (𝟙 _) (by simp [hg]) 2).app ⊤
                (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app ⊤ ω)) =
            (relativeSingularCohomology.map ℂ (.of ℂ ℂ) (analyticMap g hg)
              (Set.empty_subset _) 2).hom (cl sZ' hP' hS' ω)) := by
  obtain ⟨ψ, hψlin, hψnat⟩ :=
    MMP.Analytic.exists_addEquiv_sheafH_constantSheaf_singularCohomology_ring ℂ 2
  obtain ⟨hinj, hlin, hnat⟩ := topFormBettiClass_injective_and_pullback
  refine ⟨fun sZ hP _ ↦ (ψ sZ hP).toAddMonoidHom.comp (topFormBettiClass sZ), ?_, ?_, ?_⟩
  · intro Z sZ hP _
    exact (ψ sZ hP).injective.comp (hinj sZ hP)
  · intro Z sZ hP _ c ω
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [hlin sZ hP, hψlin]
  · intro Z Z' sZ sZ' hP _ hP' _ g hg ω
    exact hψnat sZ sZ' hP hP' g hg _ _ (hnat sZ sZ' hP hP' g hg ω)

end MMP.Fourfold
