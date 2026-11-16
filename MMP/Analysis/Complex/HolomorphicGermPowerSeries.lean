module
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.UniformSpace.Uniformizable
public import MMP.Attr

/-!
# Holomorphic germs are convergent coordinate power series

A function `f : (σ → ℂ) → ℂ` on a finite-dimensional coordinate space is holomorphic near a
point `p` exactly when it is the sum, near `p`, of a power series in the coordinates
`zᵢ - pᵢ`, that is, when there is `a : MvPowerSeries σ ℂ` with
`f z = ∑ α, aₐ ∏ᵢ (zᵢ - pᵢ) ^ αᵢ` for all `z` near `p`. The series is determined by the germ of
`f`. Substitution of power series realises composition: if `f` is the sum of `a` near `q` and
the coordinates of `G` minus `q` are the sums of series `bⱼ` without constant term near `p`,
then `f ∘ G` is the sum of the substituted series `a(b)` near `p`.

These are the facts identifying the ring of holomorphic germs at `p` with the ring `ℂ{z}` of
convergent power series; compatibility with the ring operations follows from substitution into
`X₀ + X₁` and `X₀ * X₁`.

## Main results

* `MMP.Analytic.eventually_differentiableAt_iff_exists_hasSum_mvPowerSeries`: holomorphy near
  a point is representability by a coordinate power series, which is unique, and substitution
  of series computes composition.

## Implementation notes

The monomial `zᵅ` in the coordinates centred at `p` is `α.prod fun i k ↦ (z i - p i) ^ k`, and
"`a` converges to `f` near `p`" is `∀ᶠ z in 𝓝 p, HasSum (fun α ↦ coeff α a * zᵅ) (f z)`.
Holomorphy near `p` is `∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z`, the defining condition of the
germs in `MMP.Analytic.holGerms`. Substitution is `MvPowerSeries.subst`; the series substituted
have zero constant coefficient, which is the condition `G p = q` read on the series.

## References

* [Grauert, Remmert, *Coherent analytic sheaves*], Chapter 1, §1–§2.
-/

@[expose] public section

open Filter Topology

namespace MMP.Analytic

section CauchyFormula

open Metric Complex

/-- Product of geometric series, summed over exponent vectors. -/
private theorem hasSum_prod_geometric {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    HasSum (fun g : ι → ℕ ↦ ∏ i, u i ^ g i) (∏ i, (1 - u i)⁻¹) := by
  revert u
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ u : ι → ℂ, (∀ i, ‖u i‖ < 1) →
    HasSum (fun g : ι → ℕ ↦ ∏ i, u i ^ g i) (∏ i, (1 - u i)⁻¹)) ?_ ?_ ?_ ι
  · intro α β _ e h u hu
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have := h (u ∘ e) (fun a ↦ hu _)
    rw [← (e.arrowCongr (Equiv.refl ℕ)).hasSum_iff]
    convert this using 1
    · funext g
      simp only [Function.comp_apply, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp]
      exact Fintype.prod_equiv e.symm _ _ (fun b ↦ by simp)
    · exact (Fintype.prod_equiv e _ _ (fun _ ↦ rfl)).symm
  · intro u _
    simpa using hasSum_fintype (fun g : PEmpty → ℕ ↦ (1 : ℂ))
  · intro α _ ih u hu
    have h1 := ih (u ∘ some) (fun _ ↦ hu _)
    have h0 : HasSum (fun k : ℕ ↦ u none ^ k) (1 - u none)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hu none)
    have hn0 : Summable fun k : ℕ ↦ ‖u none ^ k‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hu none)
    have hn1 : Summable fun g : α → ℕ ↦ ‖∏ i, (u ∘ some) i ^ g i‖ := by
      have := (ih (fun i ↦ (‖u (some i)‖ : ℂ)) (by simpa using fun i ↦ hu (some i))).summable
      refine this.norm.congr fun g ↦ ?_
      simp [norm_prod]
    have hm := h0.mul h1 (summable_mul_of_summable_norm (f := fun k : ℕ ↦ u none ^ k)
      (g := fun g : α → ℕ ↦ ∏ i, (u ∘ some) i ^ g i) hn0 hn1)
    rw [← (Equiv.piOptionEquivProd (β := fun _ ↦ ℕ)).symm.hasSum_iff, Fintype.prod_option]
    have he : ∀ x : ℕ × (α → ℕ), ((fun g : Option α → ℕ ↦ ∏ i, u i ^ g i) ∘
        (Equiv.piOptionEquivProd (β := fun _ ↦ ℕ)).symm) x =
        u none ^ x.1 * ∏ i, (u ∘ some) i ^ x.2 i := fun x ↦ by
      rw [Function.comp_apply, Fintype.prod_option]
      rfl
    rw [funext he]
    exact hm

variable {σ : Type*} [DecidableEq σ]

/-- The iterated circle integral `∮_{i₁} ⋯ ∮_{iₖ} φ` over the coordinates `l = [i₁, …, iₖ]`,
each on the circle of radius `R` about `p i`, the remaining coordinates taken from the point. -/
private noncomputable def itInt (p : σ → ℂ) (R : ℝ) : List σ → ((σ → ℂ) → ℂ) → (σ → ℂ) → ℂ
  | [], φ => φ
  | i :: l, φ => fun y ↦ ∮ w in C(p i, R), itInt p R l φ (Function.update y i w)

variable (p : σ → ℂ) (R : ℝ)

private lemma itInt_nil (φ : (σ → ℂ) → ℂ) : itInt p R [] φ = φ := rfl

private lemma itInt_cons (i : σ) (l : List σ) (φ : (σ → ℂ) → ℂ) (y : σ → ℂ) :
    itInt p R (i :: l) φ y = ∮ w in C(p i, R), itInt p R l φ (Function.update y i w) := rfl

private lemma itInt_congr_point (l : List σ) (φ : (σ → ℂ) → ℂ) {y y' : σ → ℂ}
    (h : ∀ j ∉ l, y j = y' j) : itInt p R l φ y = itInt p R l φ y' := by
  induction l generalizing y y' with
  | nil => exact congrArg φ (funext fun j ↦ h j List.not_mem_nil)
  | cons i l ih =>
    simp only [itInt_cons]
    congr 1; funext w
    refine ih fun j hj ↦ ?_
    by_cases hji : j = i
    · subst hji; simp
    · simp only [Function.update_of_ne hji]
      exact h j (by simp [hji, hj])

private lemma itInt_const_mul (l : List σ) (c : ℂ) (φ : (σ → ℂ) → ℂ) (y : σ → ℂ) :
    itInt p R l (fun w ↦ c * φ w) y = c * itInt p R l φ y := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih =>
    simp only [itInt_cons, ih]
    simpa using
      circleIntegral.integral_smul c (fun w ↦ itInt p R l φ (Function.update y i w)) (p i) R

private lemma itInt_mul_left (l : List σ) {i : σ} (hi : i ∉ l) (g : ℂ → ℂ) (φ : (σ → ℂ) → ℂ)
    (y : σ → ℂ) : itInt p R l (fun w ↦ g (w i) * φ w) y = g (y i) * itInt p R l φ y := by
  induction l generalizing y with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h ↦ hi (h ▸ List.mem_cons_self)
    simp only [itInt_cons, ih (fun h ↦ hi (List.mem_cons_of_mem _ h)),
      Function.update_of_ne hij]
    simpa using circleIntegral.integral_smul (g (y i))
      (fun w ↦ itInt p R l φ (Function.update y j w)) (p j) R

/-- The torus with centre `p` and radius `R` in each coordinate. -/
private abbrev torus : Set (σ → ℂ) := Set.univ.pi fun j ↦ sphere (p j) R

private lemma update_mem_torus {y : σ → ℂ} (hy : y ∈ torus p R) {i : σ} {w : ℂ}
    (hw : w ∈ sphere (p i) R) : Function.update y i w ∈ torus p R := by
  intro j _
  by_cases hji : j = i
  · subst hji; simpa using hw
  · simpa [Function.update_of_ne hji] using hy j trivial

private lemma continuousOn_itInt (hR : 0 ≤ R) (l : List σ) {φ : (σ → ℂ) → ℂ}
    (hφ : ContinuousOn φ (torus p R)) : ContinuousOn (itInt p R l φ) (torus p R) := by
  induction l with
  | nil => exact hφ
  | cons i l ih =>
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous fun x : torus p R × ℝ ↦
        deriv (circleMap (p i) R) x.2 •
          itInt p R l φ (Function.update x.1.1 i (circleMap (p i) R x.2)) := by
      refine Continuous.smul (f := fun x : torus p R × ℝ ↦ deriv (circleMap (p i) R) x.2) ?_ ?_
      · simp only [deriv_circleMap]; fun_prop
      · refine ih.comp_continuous ?_ fun x ↦
          update_mem_torus p R x.1.2 (circleMap_mem_sphere _ hR _)
        exact (continuous_subtype_val.comp continuous_fst).update i
          ((continuous_circleMap _ _).comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (y : torus p R) (t : ℝ) ↦ deriv (circleMap (p i) R) t •
        itInt p R l φ (Function.update y.1 i (circleMap (p i) R t))) hc 0 (2 * Real.pi)

private lemma norm_itInt_le (hR : 0 ≤ R) (l : List σ) {φ : (σ → ℂ) → ℂ} {B : ℝ}
    (hφ : ∀ w ∈ torus p R, ‖φ w‖ ≤ B) :
    ∀ y ∈ torus p R, ‖itInt p R l φ y‖ ≤ (2 * Real.pi * R) ^ l.length * B := by
  induction l with
  | nil => simpa [itInt_nil] using hφ
  | cons i l ih =>
    intro y hy
    rw [itInt_cons, List.length_cons, pow_succ, mul_comm _ (2 * Real.pi * R), mul_assoc]
    exact circleIntegral.norm_integral_le_of_norm_le_const hR fun w hw ↦
      ih _ (update_mem_torus p R hy hw)

private lemma hasSum_itInt (hR : 0 ≤ R) (l : List σ) {ι : Type*} [Countable ι] {φ : ι → (σ → ℂ) → ℂ}
    {Φ : (σ → ℂ) → ℂ} {B : ι → ℝ} (hφc : ∀ a, ContinuousOn (φ a) (torus p R))
    (hφB : ∀ a, ∀ w ∈ torus p R, ‖φ a w‖ ≤ B a) (hB : Summable B)
    (hΦ : ∀ w ∈ torus p R, HasSum (fun a ↦ φ a w) (Φ w)) :
    ∀ y ∈ torus p R, HasSum (fun a ↦ itInt p R l (φ a) y) (itInt p R l Φ y) := by
  induction l with
  | nil => simpa [itInt_nil] using hΦ
  | cons i l ih =>
    intro y hy
    show HasSum (fun a ↦ ∫ t in (0)..(2 * Real.pi), deriv (circleMap (p i) R) t •
      itInt p R l (φ a) (Function.update y i (circleMap (p i) R t)))
      (∫ t in (0)..(2 * Real.pi), deriv (circleMap (p i) R) t •
      itInt p R l Φ (Function.update y i (circleMap (p i) R t)))
    have hmem : ∀ t, Function.update y i (circleMap (p i) R t) ∈ torus p R := fun t ↦
      update_mem_torus p R hy (circleMap_mem_sphere _ hR _)
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun a _ ↦ R * ((2 * Real.pi * R) ^ l.length * B a)) (fun a ↦ ?_) (fun a ↦ ?_) ?_ ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine Continuous.smul (f := fun t : ℝ ↦ deriv (circleMap (p i) R) t)
        (by simp only [deriv_circleMap]; fun_prop) ?_
      exact (continuousOn_itInt p R hR l (hφc a)).comp_continuous
        ((continuous_const.update i (continuous_circleMap _ _))) hmem
    · refine Filter.Eventually.of_forall fun t _ ↦ ?_
      rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
        abs_of_nonneg hR]
      gcongr
      exact norm_itInt_le p R hR l (hφB a) _ (hmem t)
    · exact Filter.Eventually.of_forall fun t _ ↦ (hB.mul_left _).mul_left _
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ ↦ (ih _ (hmem t)).const_smul _

/-- Iterated Cauchy integral formula on a polydisc. -/
private lemma itInt_cauchy [Fintype σ] (hR : 0 < R) {f : (σ → ℂ) → ℂ}
    (hf : ∀ w : σ → ℂ, (∀ j, ‖w j - p j‖ ≤ R) → DifferentiableAt ℂ f w) (l : List σ)
    (hl : l.Nodup) : ∀ z : σ → ℂ, (∀ j, ‖z j - p j‖ ≤ R) → (∀ j ∈ l, ‖z j - p j‖ < R) →
      itInt p R l (fun w ↦ (∏ j ∈ l.toFinset, (w j - z j)⁻¹) * f w) z =
        (2 * Real.pi * I) ^ l.length * f z := by
  induction l with
  | nil => intro z _ _; simp [itInt_nil]
  | cons i l ih =>
    intro z hz hzl
    obtain ⟨hi, hl⟩ := List.nodup_cons.1 hl
    have hi' : i ∉ l.toFinset := by simpa using hi
    have hfun : (fun w : σ → ℂ ↦ (∏ j ∈ (i :: l).toFinset, (w j - z j)⁻¹) * f w) =
        fun w ↦ (fun t ↦ (t - z i)⁻¹) (w i) * ((∏ j ∈ l.toFinset, (w j - z j)⁻¹) * f w) := by
      funext w
      rw [List.toFinset_cons, Finset.prod_insert hi', mul_assoc]
    rw [hfun, itInt_cons]
    have hpt : ∀ w ∈ sphere (p i) R,
        itInt p R l (fun w' ↦ (fun t ↦ (t - z i)⁻¹) (w' i) *
          ((∏ j ∈ l.toFinset, (w' j - z j)⁻¹) * f w')) (Function.update z i w) =
        (w - z i)⁻¹ • ((2 * Real.pi * I) ^ l.length * f (Function.update z i w)) := by
      intro w hw
      refine (itInt_mul_left p R l hi (fun t ↦ (t - z i)⁻¹) _ _).trans ?_
      rw [Function.update_self, smul_eq_mul]
      congr 1
      have hk : (fun w' : σ → ℂ ↦ (∏ j ∈ l.toFinset, (w' j - z j)⁻¹) * f w') =
          fun w' ↦ (∏ j ∈ l.toFinset, (w' j - Function.update z i w j)⁻¹) * f w' := by
        funext w'
        congr 1
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        have hji : j ≠ i := fun h ↦ hi' (h ▸ hj)
        rw [Function.update_of_ne hji]
      rw [hk]
      refine ih hl _ (fun j ↦ ?_) (fun j hj ↦ ?_)
      · by_cases hji : j = i
        · subst hji; simp only [Function.update_self]; exact (mem_sphere_iff_norm.1 hw).le
        · rw [Function.update_of_ne hji]; exact hz j
      · have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
        rw [Function.update_of_ne hji]; exact hzl j (List.mem_cons_of_mem _ hj)
    rw [circleIntegral.integral_congr hR.le hpt]
    have hd : DifferentiableOn ℂ (fun w ↦ (2 * Real.pi * I) ^ l.length * f (Function.update z i w))
        (closedBall (p i) R) := by
      intro w hw
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (hf _ fun j ↦ ?_).comp w (hasFDerivAt_update z w).differentiableAt
      by_cases hji : j = i
      · subst hji; simpa [dist_eq_norm] using hw
      · rw [Function.update_of_ne hji]; exact hz j
    have hzi : z i ∈ ball (p i) R := mem_ball_iff_norm.2 (hzl i List.mem_cons_self)
    rw [(hd.diffContOnCl_ball subset_rfl).circleIntegral_sub_inv_smul hzi, Function.update_eq_self,
      smul_eq_mul, List.length_cons, pow_succ]
    ring

/-- Geometric expansion of the product Cauchy kernel. -/
private lemma hasSum_cauchyKernel [Fintype σ] {z w : σ → ℂ} (h : ∀ j, ‖z j - p j‖ < ‖w j - p j‖) :
    HasSum (fun α : σ →₀ ℕ ↦ (∏ i, (z i - p i) ^ α i) * ∏ j, (w j - p j)⁻¹ ^ (α j + 1))
      (∏ j, (w j - z j)⁻¹) := by
  have hw : ∀ j, w j - p j ≠ 0 := fun j ↦ norm_ne_zero_iff.1 ((norm_nonneg _).trans_lt (h j)).ne'
  have hv : ∀ j, ‖(z j - p j) * (w j - p j)⁻¹‖ < 1 := fun j ↦ by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one (norm_pos_iff.2 (hw j))]
    exact h j
  have h2 := (hasSum_prod_geometric _ hv).mul_right (∏ j, (w j - p j)⁻¹)
  have h3 := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.2 h2
  have e1 : ((fun g : σ → ℕ ↦ (∏ i, ((z i - p i) * (w i - p i)⁻¹) ^ g i) *
      ∏ j, (w j - p j)⁻¹) ∘ Finsupp.equivFunOnFinite) =
      fun α : σ →₀ ℕ ↦ (∏ i, (z i - p i) ^ α i) * ∏ j, (w j - p j)⁻¹ ^ (α j + 1) := by
    funext α
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply, mul_pow, pow_succ,
      Finset.prod_mul_distrib]
    ring
  have e2 : (∏ i, (1 - (z i - p i) * (w i - p i)⁻¹)⁻¹) * ∏ j, (w j - p j)⁻¹ =
      ∏ j, (w j - z j)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hz : w j - z j ≠ 0 := by
      intro h0
      have := h j
      rw [show z j - p j = w j - p j by linear_combination -h0] at this
      exact lt_irrefl _ this
    rw [← mul_inv]
    congr 1
    have := hw j
    field_simp
    ring
  rw [e1, e2] at h3
  exact h3

/-- A function holomorphic near `p` is the sum near `p` of a coordinate power series. -/
private theorem exists_hasSum_of_eventually_differentiableAt [Fintype σ] (p : σ → ℂ)
    (f : (σ → ℂ) → ℂ) (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) :
    ∃ a : MvPowerSeries σ ℂ, ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α a * α.prod fun i k ↦ (z i - p i) ^ k)
        (f z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hf
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := by positivity
  have hdiff : ∀ w : σ → ℂ, (∀ j, ‖w j - p j‖ ≤ R) → DifferentiableAt ℂ f w := fun w hw ↦
    hball w (by
      rw [mem_ball, dist_eq_norm]
      exact ((pi_norm_le_iff_of_nonneg hR.le).2 fun j ↦ by simpa using hw j).trans_lt
        (by linarith))
  set L : List σ := (Finset.univ : Finset σ).toList with hLdef
  have hL : L.Nodup := Finset.nodup_toList _
  have hLs : L.toFinset = Finset.univ := Finset.toList_toFinset _
  have hLm : ∀ j, j ∈ L := fun j ↦ Finset.mem_toList.2 (Finset.mem_univ j)
  set c : ℂ := (2 * Real.pi * I) ^ L.length with hcdef
  have hc : c ≠ 0 := pow_ne_zero _ two_pi_I_ne_zero
  set y0 : σ → ℂ := fun j ↦ p j + R with hy0def
  have hy0 : y0 ∈ torus p R := fun j _ ↦ by
    simp [hy0def, abs_of_pos hR]
  set g : (σ →₀ ℕ) → (σ → ℂ) → ℂ := fun α w ↦ (∏ j, (w j - p j)⁻¹ ^ (α j + 1)) * f w
    with hgdef
  refine ⟨fun α ↦ c⁻¹ * itInt p R L (g α) y0, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p hR] with z hz
  have hzj : ∀ j, ‖z j - p j‖ < R := fun j ↦
    (norm_le_pi_norm (z - p) j).trans_lt (by rw [← dist_eq_norm]; exact hz)
  have htorus : ∀ w ∈ torus p R, ∀ j, ‖w j - p j‖ = R := fun w hw j ↦
    mem_sphere_iff_norm.1 (hw j trivial)
  have hfc : ContinuousOn f (torus p R) := fun w hw ↦
    (hdiff w fun j ↦ (htorus w hw j).le).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ :=
    (isCompact_univ_pi fun j ↦ isCompact_sphere (p j) R).exists_bound_of_continuousOn hfc
  set mono : (σ →₀ ℕ) → ℂ := fun α ↦ ∏ i, (z i - p i) ^ (α i) with hmonodef
  have hmono : ∀ α : σ →₀ ℕ, (α.prod fun i k ↦ (z i - p i) ^ k) = mono α := fun α ↦
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)
  have hcont : ∀ α, ContinuousOn (fun w ↦ mono α * g α w) (torus p R) := fun α ↦
    continuousOn_const.mul ((continuousOn_finset_prod _ fun j _ ↦
      ((((continuous_apply j).sub continuous_const).continuousOn).inv₀ fun w hw h0 ↦ by
        have := htorus w hw j
        simp only [Pi.sub_apply] at h0
        rw [h0, norm_zero] at this
        exact hR.ne' this.symm).pow _).mul hfc)
  set B : (σ →₀ ℕ) → ℝ := fun α ↦
    (∏ i, (‖z i - p i‖ * R⁻¹) ^ (α i)) * (R⁻¹ ^ Fintype.card σ * M) with hBdef
  have hbound : ∀ α, ∀ w ∈ torus p R, ‖mono α * g α w‖ ≤ B α := by
    intro α w hw
    have key : (∏ i, ‖z i - p i‖ ^ α i) * (∏ j, R⁻¹ ^ (α j + 1)) =
        (∏ i, (‖z i - p i‖ * R⁻¹) ^ (α i)) * R⁻¹ ^ Fintype.card σ := by
      simp only [mul_pow, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring
    have hn : ‖mono α * g α w‖ =
        (∏ i, ‖z i - p i‖ ^ α i) * (∏ j, R⁻¹ ^ (α j + 1)) * ‖f w‖ := by
      simp only [hmonodef, hgdef, norm_mul, norm_prod, norm_pow, norm_inv, htorus w hw]
      ring
    rw [hn, key, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM w hw) (by positivity))
      (by positivity)
  have hsumm : Summable B := by
    have hu : ∀ i, ‖((‖z i - p i‖ * R⁻¹ : ℝ) : ℂ)‖ < 1 := fun i ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv,
        div_lt_one hR]
      exact hzj i
    have h1 := (hasSum_prod_geometric _ hu).summable.norm
    have h2 : Summable fun g : σ → ℕ ↦ ∏ i, (‖z i - p i‖ * R⁻¹) ^ (g i) :=
      h1.congr fun g ↦ by
        rw [norm_prod]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact ((Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).summable_iff.2 h2).mul_right _
  have hlim : ∀ w ∈ torus p R, HasSum (fun α ↦ mono α * g α w)
      ((∏ j ∈ L.toFinset, (w j - z j)⁻¹) * f w) := by
    intro w hw
    have := (hasSum_cauchyKernel p fun j ↦ (hzj j).trans_eq (htorus w hw j).symm).mul_right (f w)
    rw [hLs]
    have e : (fun α : σ →₀ ℕ ↦ (∏ i, (z i - p i) ^ α i) * (∏ j, (w j - p j)⁻¹ ^ (α j + 1)) *
        f w) = fun α ↦ mono α * g α w := funext fun α ↦ mul_assoc _ _ _
    rw [e] at this
    exact this
  have hS := hasSum_itInt p R hR.le L hcont hbound hsumm hlim y0 hy0
  rw [itInt_congr_point p R L _ (y' := z) (fun j hj ↦ absurd (hLm j) hj),
    itInt_cauchy p R hR hdiff L hL z (fun j ↦ (hzj j).le) (fun j _ ↦ hzj j)] at hS
  have h := hS.mul_left c⁻¹
  rw [inv_mul_cancel_left₀ hc] at h
  have e : (fun α : σ →₀ ℕ ↦ c⁻¹ * itInt p R L (fun w ↦ mono α * g α w) y0) =
      fun α ↦ MvPowerSeries.coeff α (fun α ↦ c⁻¹ * itInt p R L (g α) y0 : MvPowerSeries σ ℂ) *
        α.prod fun i k ↦ (z i - p i) ^ k := by
    funext α
    rw [hmono, itInt_const_mul]
    change _ = c⁻¹ * itInt p R L (g α) y0 * mono α
    ring
  rwa [e] at h

end CauchyFormula

/-- Monomials are homogeneous: scaling the point by `t` scales the monomial `zᵅ` by `t ^ |α|`. -/
private lemma prod_mul_pow {σ : Type*} (t : ℂ) (v : σ → ℂ) (α : σ →₀ ℕ) :
    (α.prod fun i k ↦ (t * v i) ^ k) = t ^ α.degree * α.prod fun i k ↦ v i ^ k := by
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree]
  rfl

/-- `‖vᵅ‖ ≤ t ^ |α|` when every coordinate of `v` has norm at most `t`. -/
private lemma norm_mono_le {σ : Type*} (v : σ → ℂ) {t : ℝ} (hv : ∀ i, ‖v i‖ ≤ t) (α : σ →₀ ℕ) :
    ‖α.prod fun i k ↦ v i ^ k‖ ≤ t ^ α.degree := by
  rw [Finsupp.prod, norm_prod, show α.degree = ∑ i ∈ α.support, α i from rfl,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hv i) _

/-- A coordinate series converging near `p` on the ball of radius `ε` converges absolutely,
with room to spare, on every polydisc of radius `r < ε`. -/
private lemma summable_norm_mul_pow {σ : Type*} [Fintype σ] (p : σ → ℂ) (f : (σ → ℂ) → ℂ)
    (c : MvPowerSeries σ ℂ) {ε r : ℝ}
    (hball : ∀ z ∈ Metric.ball p ε,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α c * α.prod fun i k ↦ (z i - p i) ^ k) (f z))
    (hr : 0 < r) (hrε : r < ε) :
    Summable fun α : σ →₀ ℕ ↦ ‖MvPowerSeries.coeff α c‖ * r ^ α.degree := by
  have hmem : p + (fun _ ↦ (r : ℂ)) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hr.le).2 fun i ↦ ?_) hrε
    simp [abs_of_pos hr]
  refine (hball _ hmem).summable.norm.congr fun α ↦ ?_
  have he : ‖α.prod fun i k ↦ (r : ℂ) ^ k‖ = r ^ α.degree := by
    rw [Finsupp.prod, norm_prod, show α.degree = ∑ i ∈ α.support, α i from rfl,
      ← Finset.prod_pow_eq_pow_sum]
    simp [abs_of_pos hr]
  simp only [Pi.add_apply, add_sub_cancel_left, norm_mul, he]

/-- The sum of a coordinate power series near `p` is holomorphic near `p`. -/
private theorem eventually_differentiableAt_of_hasSum {σ : Type*} [Fintype σ]
    (p : σ → ℂ) (f : (σ → ℂ) → ℂ) (a : MvPowerSeries σ ℂ)
    (ha : ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α a * α.prod fun i k ↦ (z i - p i) ^ k)
        (f z)) :
    ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 ha
  set r : ℝ := ε / 2 with hrdef
  set ρ : ℝ := ε / 4 with hρdef
  have hr : 0 < r := by positivity
  have hρ : 0 < ρ := by positivity
  set c : (σ →₀ ℕ) → ℂ := fun α ↦ MvPowerSeries.coeff α a with hcdef
  have hsum : Summable fun α : σ →₀ ℕ ↦ ‖c α‖ * r ^ α.degree :=
    summable_norm_mul_pow p f a hball hr (by linarith)
  -- derivatives of the monomials
  set g : (σ →₀ ℕ) → σ → (σ → ℂ) → ℂ := fun α i z ↦ (z i - p i) ^ (α i) with hgdef
  set g' : (σ →₀ ℕ) → σ → (σ → ℂ) → (σ → ℂ) →L[ℂ] ℂ :=
    fun α i z ↦ ((α i : ℂ) * (z i - p i) ^ (α i - 1)) • ContinuousLinearMap.proj i with hg'def
  have hg : ∀ α i z, HasFDerivAt (g α i) (g' α i z) z := by
    intro α i z
    simpa [hgdef, hg'def] using (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ)
      i).hasFDerivAt (x := z)).sub_const (p i)).pow (α i)
  set F' : (σ →₀ ℕ) → (σ → ℂ) → (σ → ℂ) →L[ℂ] ℂ := fun α z ↦
    c α • ∑ i ∈ α.support, (∏ j ∈ α.support.erase i, g α j z) • g' α i z with hF'def
  have hF : ∀ α z, HasFDerivAt (fun y ↦ c α * α.prod fun i k ↦ (y i - p i) ^ k) (F' α z) z :=
    fun α z ↦ (HasFDerivAt.finset_prod fun i _ ↦ hg α i z).const_mul (c α)
  have hbound : ∀ α, ∀ z ∈ Metric.ball p ρ,
      ‖F' α z‖ ≤ ‖c α‖ * (α.degree * ρ ^ α.degree / ρ) := by
    intro α z hz
    have hzi : ∀ i, ‖z i - p i‖ ≤ ρ := fun i ↦
      (norm_le_pi_norm (z - p) i).trans (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hz).le)
    simp only [hF'def, norm_smul]
    gcongr
    calc ‖∑ i ∈ α.support, (∏ j ∈ α.support.erase i, g α j z) • g' α i z‖
        ≤ ∑ i ∈ α.support, ‖(∏ j ∈ α.support.erase i, g α j z) • g' α i z‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ α.support, (α i : ℝ) * ρ ^ α.degree / ρ := by
          gcongr with i hi
          rw [norm_smul, norm_prod]
          have h1 : ∏ j ∈ α.support.erase i, ‖g α j z‖ ≤ ∏ j ∈ α.support.erase i, ρ ^ (α j) :=
            Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ by
              simp only [hgdef, norm_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (hzi j) _
          have h2 : ‖g' α i z‖ ≤ α i * ρ ^ (α i - 1) := by
            simp only [hg'def]
            refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
            calc ‖(α i : ℂ) * (z i - p i) ^ (α i - 1)‖ * ‖ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : σ ↦ ℂ) i‖
                ≤ ‖(α i : ℂ) * (z i - p i) ^ (α i - 1)‖ * 1 := by
                  gcongr
                  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
                    simpa using norm_le_pi_norm x i
              _ ≤ α i * ρ ^ (α i - 1) := by
                  rw [mul_one, norm_mul, norm_pow, Complex.norm_natCast]
                  gcongr
                  exact hzi i
          calc (∏ j ∈ α.support.erase i, ‖g α j z‖) * ‖g' α i z‖
              ≤ (∏ j ∈ α.support.erase i, ρ ^ (α j)) * (α i * ρ ^ (α i - 1)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = α i * ρ ^ α.degree / ρ := by
                rw [eq_div_iff hρ.ne']
                calc (∏ j ∈ α.support.erase i, ρ ^ (α j)) * (α i * ρ ^ (α i - 1)) * ρ
                    = α i * ((∏ j ∈ α.support.erase i, ρ ^ (α j)) * (ρ ^ (α i - 1) * ρ)) := by
                      ring
                  _ = α i * ρ ^ α.degree := by
                      rw [← pow_succ, Nat.sub_add_cancel
                          (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)),
                        Finset.prod_erase_mul _ _ hi, Finset.prod_pow_eq_pow_sum]
                      rfl
      _ = α.degree * ρ ^ α.degree / ρ := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
          congr 2
          show _ = ((∑ i ∈ α.support, α i : ℕ) : ℝ)
          push_cast
          rfl
  have hu : Summable fun α : σ →₀ ℕ ↦ ‖c α‖ * (α.degree * ρ ^ α.degree / ρ) := by
    refine Summable.of_nonneg_of_le (fun α ↦ by positivity) (fun α ↦ ?_) (hsum.div_const ρ)
    have hd : (α.degree : ℝ) * ρ ^ α.degree ≤ r ^ α.degree := by
      have hρr : ρ = r / 2 := by rw [hρdef, hrdef]; ring
      rw [hρr, div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      calc (α.degree : ℝ) * r ^ α.degree ≤ 2 ^ α.degree * r ^ α.degree := by
            gcongr; exact_mod_cast Nat.lt_two_pow_self.le
        _ = r ^ α.degree * 2 ^ α.degree := mul_comm _ _
    calc ‖c α‖ * (α.degree * ρ ^ α.degree / ρ) = ‖c α‖ * (α.degree * ρ ^ α.degree) / ρ := by
          ring
      _ ≤ ‖c α‖ * r ^ α.degree / ρ := by gcongr
  have hp0 : Summable fun α : σ →₀ ℕ ↦ c α * α.prod fun i k ↦ (p i - p i) ^ k :=
    (hball p (Metric.mem_ball_self hε)).summable
  have hρε : ρ ≤ ε := by rw [hρdef]; linarith
  filter_upwards [Metric.ball_mem_nhds p hρ] with z hz
  have hD := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball p ρ).isPreconnected (fun α y _ ↦ hF α y) hbound (Metric.mem_ball_self hρ) hp0 hz
  refine (hD.congr_of_eventuallyEq ?_).differentiableAt
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρε hz)] with y hy
  exact (hball y hy).tsum_eq.symm

/-- A coordinate power series whose sum vanishes near `p` is zero: restrict to the complex
lines through `p`, regroup by total degree, and compare with the one-variable identity
theorem; the homogeneous parts then vanish as polynomial functions. -/
private theorem eq_zero_of_hasSum_zero {σ : Type*} [Fintype σ] (p : σ → ℂ)
    (c : MvPowerSeries σ ℂ)
    (hc : ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α c * α.prod fun i k ↦ (z i - p i) ^ k) 0) :
    c = 0 := by
  classical
  set S : ℕ → Finset (σ →₀ ℕ) := fun n ↦ Finset.univ.finsuppAntidiag n with hSdef
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := by
    intro n α
    simp [hSdef, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  set Q : ℕ → MvPolynomial σ ℂ :=
    fun n ↦ ∑ α ∈ S n, MvPolynomial.monomial α (MvPowerSeries.coeff α c) with hQdef
  have hQ : ∀ n v, MvPolynomial.eval v (Q n) = 0 := by
    intro n v
    have hcont : Tendsto (fun t : ℂ ↦ p + t • v) (𝓝 0) (𝓝 p) := by
      have : Continuous (fun t : ℂ ↦ p + t • v) := by fun_prop
      simpa using this.tendsto 0
    have ht : ∀ᶠ t : ℂ in 𝓝 0, HasSum (fun m ↦ t ^ m • MvPolynomial.eval v (Q m)) 0 := by
      filter_upwards [hcont.eventually hc] with t ht
      have h1 : HasSum (fun α : σ →₀ ℕ ↦
          t ^ α.degree * (MvPowerSeries.coeff α c * α.prod fun i k ↦ v i ^ k)) 0 := by
        convert ht using 2 with α
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, prod_mul_pow]
        ring
      have h2 := h1.tsum_fiberwise Finsupp.degree
      refine (funext fun m ↦ ?_ : (fun m ↦ t ^ m • MvPolynomial.eval v (Q m)) = _) ▸ h2
      have hset : (Finsupp.degree ⁻¹' {m} : Set (σ →₀ ℕ)) = ↑(S m) := by
        ext α; simp [hS]
      rw [hset]
      refine Eq.trans ?_ (Finset.tsum_subtype (S m) fun α : σ →₀ ℕ ↦
        t ^ α.degree * (MvPowerSeries.coeff α c * α.prod fun i k ↦ v i ^ k)).symm
      simp only [hQdef, map_sum, MvPolynomial.eval_monomial, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα ↦ ?_
      rw [(hS m α).1 hα]
    have hp : HasFPowerSeriesAt (0 : ℂ → ℂ)
        (FormalMultilinearSeries.ofScalars ℂ fun m ↦ MvPolynomial.eval v (Q m)) 0 :=
      hasFPowerSeriesAt_iff.2 (by simpa [FormalMultilinearSeries.coeff_ofScalars] using ht)
    have h0 := congrArg (fun q ↦ q.coeff n) hp.eq_zero
    rw [FormalMultilinearSeries.coeff_ofScalars] at h0
    simpa [FormalMultilinearSeries.coeff] using h0
  ext α
  have hQ0 : Q α.degree = 0 := MvPolynomial.funext fun v ↦ by simpa using hQ _ v
  have := congrArg (fun q : MvPolynomial σ ℂ ↦ q.coeff α) hQ0
  simpa [hQdef, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hS] using this

/-- Identity theorem for coordinate power series: two series with the same sum near `p` are
equal. -/
private theorem eq_of_hasSum_of_hasSum {σ : Type*} [Fintype σ]
    (p : σ → ℂ) (f : (σ → ℂ) → ℂ) (a b : MvPowerSeries σ ℂ)
    (ha : ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α a * α.prod fun i k ↦ (z i - p i) ^ k)
        (f z))
    (hb : ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α b * α.prod fun i k ↦ (z i - p i) ^ k)
        (f z)) :
    a = b := by
  refine sub_eq_zero.1 (eq_zero_of_hasSum_zero p (a - b) ?_)
  filter_upwards [ha, hb] with z hza hzb
  simpa [sub_mul] using hza.sub hzb

/-- The `α`-th term `cₐ vᵅ` of the coordinate series of `c` evaluated at `v`. -/
private noncomputable def term {σ : Type*} (v : σ → ℂ) (c : MvPowerSeries σ ℂ) (α : σ →₀ ℕ) : ℂ :=
  MvPowerSeries.coeff α c * α.prod fun i k ↦ v i ^ k

private lemma term_mul {σ : Type*} [DecidableEq σ] (v : σ → ℂ) (c d : MvPowerSeries σ ℂ)
    (α : σ →₀ ℕ) :
    term v (c * d) α =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, term v c x.1 * term v d x.2 := by
  classical
  simp only [term, MvPowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← (Finset.HasAntidiagonal.mem_antidiagonal.1 hx),
    Finsupp.prod_add_index' (h := fun i k ↦ v i ^ k) (fun _ ↦ pow_zero _)
      fun _ _ _ ↦ pow_add _ _ _]
  ring

private lemma summable_term_mul {σ : Type*} [DecidableEq σ] (v : σ → ℂ) {c d : MvPowerSeries σ ℂ}
    (hc : Summable fun α ↦ ‖term v c α‖) (hd : Summable fun α ↦ ‖term v d α‖) :
    Summable (fun α ↦ ‖term v (c * d) α‖) ∧
      ∑' α, ‖term v (c * d) α‖ ≤ (∑' α, ‖term v c α‖) * ∑' α, ‖term v d α‖ ∧
      HasSum (term v (c * d)) ((∑' α, term v c α) * ∑' α, term v d α) := by
  have hn : Summable fun x : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ ‖term v c x.1‖ * ‖term v d x.2‖ :=
    hc.mul_of_nonneg hd (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hs :
      Summable fun α ↦
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, ‖term v c x.1‖ * ‖term v d x.2‖ :=
    summable_sum_mul_antidiagonal_of_summable_mul (f := fun α ↦ ‖term v c α‖)
      (g := fun α ↦ ‖term v d α‖) hn
  have hle : ∀ α, ‖term v (c * d) α‖ ≤
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, ‖term v c x.1‖ * ‖term v d x.2‖ := fun α ↦ by
    rw [term_mul]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _)
  have hcd : Summable fun α ↦ ‖term v (c * d) α‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hs
  refine ⟨hcd, ?_, ?_⟩
  · rw [hc.tsum_mul_tsum_eq_tsum_sum_antidiagonal hd hn]
    exact hcd.tsum_le_tsum hle hs
  · rw [hc.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hd.of_norm
      (summable_mul_of_summable_norm hc hd)]
    have : term v (c * d) =
        fun α ↦ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, term v c x.1 * term v d x.2 :=
      funext (term_mul v c d)
    have h' : Summable (term v (c * d)) := hcd.of_norm
    rw [this] at h' ⊢
    exact h'.hasSum

private lemma term_one {σ : Type*} [DecidableEq σ] (v : σ → ℂ) : term v 1 = Pi.single 0 1 := by
  classical
  ext α
  by_cases h : α = 0
  · subst h; simp [term]
  · simp [term, MvPowerSeries.coeff_one, h]

private lemma summable_term_prod {σ ι : Type*} (v : σ → ℂ) (s : Finset ι)
    (f : ι → MvPowerSeries σ ℂ)
    (hf : ∀ i ∈ s, Summable fun α ↦ ‖term v (f i) α‖) :
    Summable (fun α ↦ ‖term v (∏ i ∈ s, f i) α‖) ∧
      ∑' α, ‖term v (∏ i ∈ s, f i) α‖ ≤ ∏ i ∈ s, ∑' α, ‖term v (f i) α‖ ∧
      HasSum (term v (∏ i ∈ s, f i)) (∏ i ∈ s, ∑' α, term v (f i) α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, term_one]
    refine ⟨(hasSum_pi_single 0 1).summable.norm, ?_,
      by simpa using hasSum_pi_single (0 : σ →₀ ℕ) (1 : ℂ)⟩
    exact (tsum_eq_single 0 fun b hb ↦ by simp [hb]).trans_le (by simp)
  | insert i s hi ih =>
    obtain ⟨h1, h2, h3⟩ := ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨k1, k2, k3⟩ := summable_term_mul v hfi h1
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    refine ⟨k1, k2.trans (by gcongr), ?_⟩
    rw [← h3.tsum_eq]; exact k3

private lemma summable_term_finsuppProd {σ τ : Type*} (v : σ → ℂ) (b : τ → MvPowerSeries σ ℂ)
    (hb : ∀ j, Summable fun α ↦ ‖term v (b j) α‖) (β : τ →₀ ℕ) :
    Summable (fun α ↦ ‖term v (β.prod fun j e ↦ b j ^ e) α‖) ∧
      ∑' α, ‖term v (β.prod fun j e ↦ b j ^ e) α‖ ≤
        (β.prod fun j e ↦ (∑' α, ‖term v (b j) α‖) ^ e) ∧
      HasSum (term v (β.prod fun j e ↦ b j ^ e))
        (β.prod fun j e ↦ (∑' α, term v (b j) α) ^ e) := by
  have hpow : ∀ j n, Summable (fun α ↦ ‖term v (b j ^ n) α‖) ∧
      ∑' α, ‖term v (b j ^ n) α‖ ≤ (∑' α, ‖term v (b j) α‖) ^ n ∧
      HasSum (term v (b j ^ n)) ((∑' α, term v (b j) α) ^ n) := fun j n ↦ by
    simpa [Finset.prod_const] using
      summable_term_prod v (Finset.range n) (fun _ ↦ b j) fun _ _ ↦ hb j
  obtain ⟨h1, h2, h3⟩ := summable_term_prod v β.support (fun j ↦ b j ^ β j) fun j _ ↦ (hpow j _).1
  refine ⟨h1, h2.trans (Finset.prod_le_prod₀ (fun _ _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
    fun j _ ↦ (hpow j _).2.1), ?_⟩
  simpa [Finsupp.prod, (hpow _ _).2.2.tsum_eq] using h3

private lemma norm_term_le_of_constantCoeff_eq_zero {σ : Type*} [Fintype σ] (v : σ → ℂ)
    (c : MvPowerSeries σ ℂ) (hc : MvPowerSeries.constantCoeff c = 0) {t : ℝ} (ht : 0 < t)
    (hv : ‖v‖ ≤ t) (α : σ →₀ ℕ) :
    ‖term v c α‖ ≤ ‖v‖ / t * (‖MvPowerSeries.coeff α c‖ * t ^ α.degree) := by
  by_cases hα : α = 0
  · subst hα
    simp [term, hc]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (fun h ↦ hα ((Finsupp.degree_eq_zero_iff α).1 h))
  have hm := norm_mono_le v (t := ‖v‖) (fun i ↦ norm_le_pi_norm v i) α
  rw [term, norm_mul, hn, pow_succ'] at *
  calc ‖MvPowerSeries.coeff α c‖ * ‖α.prod fun i k ↦ v i ^ k‖
      ≤ ‖MvPowerSeries.coeff α c‖ * (‖v‖ * ‖v‖ ^ n) := by gcongr
    _ ≤ ‖MvPowerSeries.coeff α c‖ * (‖v‖ * t ^ n) := by gcongr
    _ = ‖v‖ / t * (‖MvPowerSeries.coeff α c‖ * (t * t ^ n)) := by field_simp

/-- Substitution of convergent series without constant term computes composition: on a small
polydisc the double family `aᵦ · (bᵝ)ₐ zᵅ` is absolutely summable, and summing it in the two
orders gives `f (G z)` and the substituted series. -/
private theorem hasSum_subst {σ : Type*} [Fintype σ] (p : σ → ℂ)
    {τ : Type*} [Fintype τ] (q : τ → ℂ) (f : (τ → ℂ) → ℂ) (a : MvPowerSeries τ ℂ)
    (G : (σ → ℂ) → τ → ℂ) (b : τ → MvPowerSeries σ ℂ)
    (ha : ∀ᶠ w in 𝓝 q,
      HasSum (fun β : τ →₀ ℕ ↦ MvPowerSeries.coeff β a * β.prod fun j k ↦ (w j - q j) ^ k)
        (f w))
    (hb : ∀ j, ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α (b j) * α.prod fun i k ↦ (z i - p i) ^ k)
        (G z j - q j))
    (hb0 : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ᶠ z in 𝓝 p,
      HasSum (fun α : σ →₀ ℕ ↦
          MvPowerSeries.coeff α (MvPowerSeries.subst b a) * α.prod fun i k ↦ (z i - p i) ^ k)
        (f (G z)) := by
  classical
  obtain ⟨εa, hεa, hA⟩ := Metric.eventually_nhds_iff_ball.1 ha
  obtain ⟨εb, hεb, hB⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_all.2 hb)
  set r : ℝ := εa / 2 with hrdef
  set t : ℝ := εb / 2 with htdef
  have hr : 0 < r := by positivity
  have ht : 0 < t := by positivity
  have hAs := summable_norm_mul_pow q f a hA hr (by linarith)
  have hBs : ∀ j, Summable fun α : σ →₀ ℕ ↦ ‖MvPowerSeries.coeff α (b j)‖ * t ^ α.degree :=
    fun j ↦ summable_norm_mul_pow p (fun z ↦ G z j - q j) (b j) (fun z hz ↦ hB z hz j) ht
      (by linarith)
  set K : ℝ := ∑ j, ∑' α : σ →₀ ℕ, ‖MvPowerSeries.coeff α (b j)‖ * t ^ α.degree with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun j _ ↦ tsum_nonneg fun _ ↦ by positivity
  set δ : ℝ := min t (r * t / (K + 1)) with hδdef
  have hδ : 0 < δ := lt_min ht (by positivity)
  filter_upwards [Metric.ball_mem_nhds p hδ] with z hz
  set v : σ → ℂ := z - p with hvdef
  have hv : ‖v‖ < δ := by rw [hvdef, ← dist_eq_norm]; exact hz
  have hvt : ‖v‖ ≤ t := hv.le.trans (min_le_left _ _)
  have hzb : z ∈ Metric.ball p εb := Metric.mem_ball.2 (by
    rw [dist_eq_norm, ← hvdef]; linarith)
  have hgood : ∀ j, Summable fun α ↦ ‖term v (b j) α‖ := fun j ↦
    (hBs j).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun α ↦ by
      rw [term, norm_mul]
      gcongr
      exact norm_mono_le v (fun i ↦ (norm_le_pi_norm v i).trans hvt) α
  have hN : ∀ j, ∑' α, ‖term v (b j) α‖ ≤ r := fun j ↦ by
    have hKj : ∑' α : σ →₀ ℕ, ‖MvPowerSeries.coeff α (b j)‖ * t ^ α.degree ≤ K :=
      Finset.single_le_sum (f := fun j ↦ ∑' α : σ →₀ ℕ, ‖MvPowerSeries.coeff α (b j)‖ *
        t ^ α.degree) (fun j _ ↦ tsum_nonneg fun _ ↦ by positivity) (Finset.mem_univ j)
    calc ∑' α, ‖term v (b j) α‖
        ≤ ∑' α : σ →₀ ℕ, ‖v‖ / t * (‖MvPowerSeries.coeff α (b j)‖ * t ^ α.degree) :=
          (hgood j).tsum_le_tsum (norm_term_le_of_constantCoeff_eq_zero v (b j) (hb0 j) ht hvt)
            ((hBs j).mul_left _)
      _ ≤ δ / t * K := by
          rw [tsum_mul_left]
          gcongr
      _ ≤ r * t / (K + 1) / t * K := by gcongr; exact min_le_right _ _
      _ = r * (K / (K + 1)) := by field_simp
      _ ≤ r * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = r := mul_one r
  have hS : ∀ j, ∑' α, term v (b j) α = G z j - q j := fun j ↦ (hB z hzb j).tsum_eq
  set P : (τ →₀ ℕ) → MvPowerSeries σ ℂ := fun β ↦ β.prod fun j e ↦ b j ^ e with hPdef
  have hP := fun β ↦ summable_term_finsuppProd v b hgood β
  set F : (τ →₀ ℕ) × (σ →₀ ℕ) → ℂ := fun x ↦ MvPowerSeries.coeff x.1 a * term v (P x.1) x.2
    with hFdef
  have hFn : Summable fun x ↦ ‖F x‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    refine ⟨fun β ↦ by
      simp only [F, norm_mul]; exact (hP β).1.mul_left ‖MvPowerSeries.coeff β a‖, ?_⟩
    refine hAs.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _) fun β ↦ ?_
    simp only [F, norm_mul, tsum_mul_left]
    gcongr
    calc _ ≤ _ := (hP β).2.1
      _ ≤ β.prod fun j e ↦ r ^ e := Finset.prod_le_prod₀
          (fun _ _ ↦ pow_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _) _)
          fun j _ ↦ pow_le_pow_left₀ (tsum_nonneg fun _ ↦ norm_nonneg _) (hN j) _
      _ = r ^ β.degree := by
          rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]; rfl
  have hF := hFn.of_norm.hasSum
  have hfib1 : ∀ β, HasSum (fun α ↦ F (β, α))
      (MvPowerSeries.coeff β a * β.prod fun j k ↦ (G z j - q j) ^ k) := fun β ↦ by
    simpa only [hS] using ((hP β).2.2).mul_left (MvPowerSeries.coeff β a)
  have hw : G z ∈ Metric.ball q εa := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hr.le).2 fun j ↦ ?_) (by linarith)
    rw [Pi.sub_apply, ← hS j]
    exact (norm_tsum_le_tsum_norm (hgood j)).trans (hN j)
  have hval : ∑' x, F x = f (G z) := (hF.prod_fiberwise hfib1).unique (hA _ hw)
  rw [hval] at hF
  have hF' : HasSum (fun x : (σ →₀ ℕ) × (τ →₀ ℕ) ↦ F x.swap) (f (G z)) :=
    (Equiv.prodComm _ _).hasSum_iff.2 hF
  refine hF'.prod_fiberwise fun α ↦ ?_
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  rw [MvPowerSeries.coeff_subst hsub]
  have hfin := MvPowerSeries.coeff_subst_finite hsub a α
  rw [finsum_eq_sum _ hfin, Finset.sum_mul]
  have he : ∀ β, MvPowerSeries.coeff β a • MvPowerSeries.coeff α (P β) *
      (α.prod fun i k ↦ (z i - p i) ^ k) = F (β, α) := fun β ↦ by
    simp only [F, term, smul_eq_mul, mul_assoc, hvdef, Pi.sub_apply]
  have hfz : ∀ β ∉ hfin.toFinset, F (β, α) = 0 := fun β hβ ↦ by
    have h0 : MvPowerSeries.coeff β a • MvPowerSeries.coeff α (P β) = 0 := by
      by_contra hne
      exact hβ ((Set.Finite.mem_toFinset _).2 hne)
    rw [← he, h0, zero_mul]
  convert hasSum_sum_of_ne_finset_zero hfz using 1
  all_goals first | rfl | infer_instance | exact Finset.sum_congr rfl fun β _ ↦ he β

/-- A function on `σ → ℂ` is holomorphic near `p` if and only if it is the sum near `p` of a power
series in the coordinates `z i - p i`; this series is unique; and substitution of series without
constant term computes the composition of the represented functions. -/
@[mmp "lem_mmp_holomorphic_germs_convergent_coordinates"]
public theorem eventually_differentiableAt_iff_exists_hasSum_mvPowerSeries
    {σ : Type*} [Fintype σ] (p : σ → ℂ) :
    (∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) ↔
      ∃ a : MvPowerSeries σ ℂ, ∀ᶠ z in 𝓝 p,
        HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α a * α.prod fun i k ↦ (z i - p i) ^ k)
          (f z)) ∧
    (∀ (f : (σ → ℂ) → ℂ) (a b : MvPowerSeries σ ℂ),
      (∀ᶠ z in 𝓝 p,
        HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α a * α.prod fun i k ↦ (z i - p i) ^ k)
          (f z)) →
      (∀ᶠ z in 𝓝 p,
        HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α b * α.prod fun i k ↦ (z i - p i) ^ k)
          (f z)) →
      a = b) ∧
    (∀ {τ : Type*} [Fintype τ] (q : τ → ℂ) (f : (τ → ℂ) → ℂ) (a : MvPowerSeries τ ℂ)
      (G : (σ → ℂ) → τ → ℂ) (b : τ → MvPowerSeries σ ℂ),
      (∀ᶠ w in 𝓝 q,
        HasSum (fun β : τ →₀ ℕ ↦ MvPowerSeries.coeff β a * β.prod fun j k ↦ (w j - q j) ^ k)
          (f w)) →
      (∀ j, ∀ᶠ z in 𝓝 p,
        HasSum (fun α : σ →₀ ℕ ↦ MvPowerSeries.coeff α (b j) * α.prod fun i k ↦ (z i - p i) ^ k)
          (G z j - q j)) →
      (∀ j, MvPowerSeries.constantCoeff (b j) = 0) →
      ∀ᶠ z in 𝓝 p,
        HasSum (fun α : σ →₀ ℕ ↦
            MvPowerSeries.coeff α (MvPowerSeries.subst b a) * α.prod fun i k ↦ (z i - p i) ^ k)
          (f (G z))) :=
  ⟨fun f ↦ ⟨by classical exact exists_hasSum_of_eventually_differentiableAt p f,
      fun ⟨a, ha⟩ ↦ eventually_differentiableAt_of_hasSum p f a ha⟩,
    eq_of_hasSum_of_hasSum p,
    fun q f a G b ha hb hb0 ↦ hasSum_subst p q f a G b ha hb hb0⟩

end MMP.Analytic

end
