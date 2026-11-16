module

public import MMP.AlgebraicGeometry.Semialgebraic.GoodDirection
public import MMP.AlgebraicGeometry.Semialgebraic.CylindricalDecomposition
public import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Bounded roots after a good direction

Let `F ∈ ℝ[X_σ][T]` have a nonzero constant leading coefficient `c`. Then for every `a ∈ ℝ^σ`
the roots `t` of `F(a, T)` satisfy `|t| < 1 + Σ_{i < deg F} |F_i(a)| / |c|` (Cauchy's bound),
a continuous function of `a`. Hence the zero set of `F` over a compact set `K ⊆ ℝ^σ` is
compact: the projection `(a, t) ↦ a` is proper on the zero set. By
`MMP.exists_shearPolynomial_leadingCoeff`, every nonzero real polynomial has this
form after the linear change of coordinates `(a, t) ↦ (a + t v, t)`
(`MMP.eval_specAt_shearPolynomial`).

## Main definitions

* `MMP.polyRootBound`: the Cauchy bound `1 + Σ_{i < deg F} |F_i(a)| / |c|`.

## Main results

* `MMP.eval_specAt_shearPolynomial`: `F = shear_v f` evaluates as
  `F(a, t) = f(a + t v, t)`.
* `MMP.abs_lt_polyRootBound`: the roots of `F(a, T)` are bounded by the Cauchy
  bound.
* `MMP.isCompact_setOf_eval_specAt_eq_zero`: the zero set of `F` over a compact
  set is compact.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], proof of
  Theorem 9.2.1.
-/

@[expose] public section

open Polynomial Set

namespace MMP

open TarskiSeidenberg

variable {σ : Type*}

/-- The shear `F = shear_v f` evaluates as `F(a, t) = f(a + t v, t)`. -/
theorem eval_specAt_shearPolynomial (v : σ → ℝ) (f : MvPolynomial (Option σ) ℝ) (a : σ → ℝ)
    (t : ℝ) :
    (specAt a (shearPolynomial v f)).eval t = MvPolynomial.eval (optionCons (a + t • v) t) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [shearPolynomial]
  | add p q hp hq => simp only [map_add, eval_add, hp, hq]
  | mul_X p o hp =>
    rw [map_mul, map_mul, eval_mul, hp, map_mul]
    congr 1
    rcases o with _ | i
    · simp [shearPolynomial, shearPolynomialAux, optionCons]
    · simp [shearPolynomial, shearPolynomialAux, optionCons]
      ring

/-- The Cauchy bound `1 + Σ_{i < deg F} |F_i(a)| / |c|` for the roots of `F(a, T)`, where `c`
is the leading coefficient of `F`. -/
noncomputable def polyRootBound (F : (MvPolynomial σ ℝ)[X]) (c : ℝ) (a : σ → ℝ) : ℝ :=
  1 + ∑ i ∈ Finset.range F.natDegree, |MvPolynomial.eval a (F.coeff i)| / |c|

/-- The Cauchy bound `polyRootBound F c` is a continuous function of `a`. -/
@[fun_prop]
theorem continuous_polyRootBound (F : (MvPolynomial σ ℝ)[X]) (c : ℝ) :
    Continuous (polyRootBound F c) := by
  unfold polyRootBound
  exact continuous_const.add (continuous_finset_sum _ fun i _ ↦
    ((MvPolynomial.continuous_eval _).abs).div_const _)

/-- Specialising a polynomial with constant leading coefficient `c ≠ 0` keeps its degree and
its leading coefficient. -/
theorem natDegree_specAt_of_leadingCoeff {F : (MvPolynomial σ ℝ)[X]} {c : ℝ} (hc : c ≠ 0)
    (hF : F.leadingCoeff = MvPolynomial.C c) (a : σ → ℝ) :
    (specAt a F).natDegree = F.natDegree ∧ (specAt a F).leadingCoeff = c := by
  have hne : MvPolynomial.eval a F.leadingCoeff ≠ 0 := by simpa [hF] using hc
  have hdeg : (specAt a F).natDegree = F.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hne
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg]
  simpa [hF] using congrArg (MvPolynomial.eval a) hF

/-- **Cauchy's bound.** If `F` has constant leading coefficient `c ≠ 0`, every root `t` of
`F(a, T)` satisfies `|t| < polyRootBound F c a`. -/
theorem abs_lt_polyRootBound {F : (MvPolynomial σ ℝ)[X]} {c : ℝ} (hc : c ≠ 0)
    (hF : F.leadingCoeff = MvPolynomial.C c) {a : σ → ℝ} {t : ℝ}
    (ht : (specAt a F).eval t = 0) : |t| < polyRootBound F c a := by
  obtain ⟨hdeg, hlc⟩ := natDegree_specAt_of_leadingCoeff hc hF a
  have hp : specAt a F ≠ 0 := fun h ↦ hc (by rw [← hlc, h, leadingCoeff_zero])
  have h := IsRoot.norm_lt_cauchyBound hp ht
  rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs] at h
  refine h.trans_le ?_
  rw [cauchyBound, hdeg, hlc, polyRootBound, NNReal.coe_add, NNReal.coe_one, add_comm,
    NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
  have hsup : (((Finset.range F.natDegree).sup fun i ↦ ‖(specAt a F).coeff i‖₊ : NNReal) : ℝ) ≤
      ∑ i ∈ Finset.range F.natDegree, |MvPolynomial.eval a (F.coeff i)| := by
    have h0 : 0 ≤ ∑ i ∈ Finset.range F.natDegree, |MvPolynomial.eval a (F.coeff i)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    refine (NNReal.coe_le_coe.2 (Finset.sup_le (f := fun i ↦ ‖(specAt a F).coeff i‖₊)
      (a := Real.toNNReal _) fun i hi ↦ ?_)).trans (Real.coe_toNNReal _ h0).le
    rw [Real.le_toNNReal_iff_coe_le h0, coe_nnnorm, Real.norm_eq_abs]
    have : (specAt a F).coeff i = MvPolynomial.eval a (F.coeff i) := by simp
    rw [this]
    exact Finset.single_le_sum (f := fun i ↦ |MvPolynomial.eval a (F.coeff i)|)
      (fun _ _ ↦ abs_nonneg _) hi
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  gcongr

/-- **Properness after a good direction.** If `F` has constant leading coefficient `c ≠ 0`,
its zero set over a compact `K ⊆ ℝ^σ` is compact. -/
theorem isCompact_setOf_eval_specAt_eq_zero [Fintype σ] {F : (MvPolynomial σ ℝ)[X]} {c : ℝ}
    (hc : c ≠ 0) (hF : F.leadingCoeff = MvPolynomial.C c) {K : Set (σ → ℝ)} (hK : IsCompact K) :
    IsCompact {x : Option σ → ℝ | x ∘ some ∈ K ∧ (specAt (x ∘ some) F).eval (x none) = 0} := by
  obtain ⟨B, hB⟩ := (hK.image (continuous_polyRootBound F c)).isBounded.subset_closedBall 0
  have hcpt : IsCompact ((fun p : (σ → ℝ) × ℝ ↦ optionCons p.1 p.2) ''
      (K ×ˢ Metric.closedBall 0 B)) :=
    (hK.prod (isCompact_closedBall 0 B)).image continuous_optionCons
  refine hcpt.of_isClosed_subset ?_ ?_
  · have hcont : Continuous fun x : Option σ → ℝ ↦ (specAt (x ∘ some) F).eval (x none) := by
      have := fun x : Option σ → ℝ ↦
        eval_eq_eval_specAt_optionEquivLeft ((MvPolynomial.optionEquivLeft ℝ σ).symm F) x
      simp only [AlgEquiv.apply_symm_apply] at this
      simp_rw [← this]
      exact MvPolynomial.continuous_eval _
    exact (hK.isClosed.preimage (by fun_prop)).inter (isClosed_eq hcont continuous_const)
  · rintro x ⟨hxK, hx⟩
    refine ⟨(x ∘ some, x none), ⟨hxK, ?_⟩, optionCons_eta x⟩
    have h1 := abs_lt_polyRootBound hc hF hx
    have h2 := hB (mem_image_of_mem _ hxK)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact h1.le.trans ((le_abs_self _).trans h2)

end MMP
