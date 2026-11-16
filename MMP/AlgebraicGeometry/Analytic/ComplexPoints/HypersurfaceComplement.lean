module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The complement of a complex hypersurface is connected and dense

Let `p` be a nonzero polynomial in the variables `ι` over `ℂ`. The set of points of `ℂ^ι` at
which `p` does not vanish is path-connected and dense in the classical topology. Indeed, given
`x` with `p(x) ≠ 0` and any `y`, the restriction `t ↦ p(x + t(y - x))` of `p` to the complex line
through `x` and `y` is a nonzero polynomial in `t`, so it vanishes at finitely many `t`; the
complement of a finite set in `ℂ` is path-connected and dense.

This is the first step of the classical proof that `V_reg - Z` is connected and dense for an
irreducible complex variety `V` and a proper Zariski closed `Z ⊊ V`: a Noether normalization
`V → ℂⁿ` is a finite covering away from a hypersurface of `ℂⁿ`, whose complement is connected.

## Main results

* `MMP.SmoothLocusConnected.isPathConnected_setOf_eval_ne_zero`: the
  nonvanishing locus of a nonzero complex polynomial is path-connected.
* `MMP.SmoothLocusConnected.dense_setOf_eval_ne_zero`: it is dense.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 2*], Chapter VII, §2.
-/

public section

open Polynomial

namespace MMP.SmoothLocusConnected

variable {ι : Type*}

private lemma eval_line (p : MvPolynomial ι ℂ) (x y : ι → ℂ) (t : ℂ) :
    (MvPolynomial.aeval (fun i ↦ C (x i) + X * C (y i - x i)) p).eval t =
      MvPolynomial.eval (x + t • (y - x)) p := by
  have : (x + t • (y - x)) = fun i ↦ (C (x i) + X * C (y i - x i)).eval t := by
    ext i; simp
  rw [this]
  induction p using MvPolynomial.induction_on <;> simp_all

private lemma one_lt_rank : 1 < Module.rank ℝ ℂ := by
  rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num

private lemma continuous_line (x y : ι → ℂ) : Continuous fun t : ℂ ↦ x + t • (y - x) := by
  fun_prop

/-- On the complex line through `x` and `y`, the parameters at which `p` vanishes form a finite
set when `p(x) ≠ 0`. -/
private lemma finite_line_zeros {p : MvPolynomial ι ℂ} {x : ι → ℂ}
    (hx : MvPolynomial.eval x p ≠ 0) (y : ι → ℂ) :
    {t : ℂ | MvPolynomial.eval (x + t • (y - x)) p = 0}.Finite := by
  set q := MvPolynomial.aeval (fun i ↦ C (x i) + X * C (y i - x i)) p with hqdef
  have hq : q ≠ 0 := by
    intro h
    apply hx
    have := eval_line p x y 0
    simp only [zero_smul, add_zero] at this
    rw [← this, ← hqdef, h, eval_zero]
  refine (q.roots.toFinset.finite_toSet).subset fun t ht ↦ ?_
  simp only [Set.mem_setOf_eq] at ht
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hq, IsRoot, hqdef, eval_line]
  exact ht

/-- The nonvanishing locus of a nonzero complex polynomial is path-connected in the classical
topology. -/
theorem isPathConnected_setOf_eval_ne_zero {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    IsPathConnected {x : ι → ℂ | MvPolynomial.eval x p ≠ 0} := by
  refine isPathConnected_iff.mpr ⟨?_, fun x hx y hy ↦ ?_⟩
  · by_contra h
    exact hp (MvPolynomial.funext fun x ↦ by
      simpa using fun hx ↦ h ⟨x, hx⟩)
  · set S := {t : ℂ | MvPolynomial.eval (x + t • (y - x)) p = 0}
    have hS := (finite_line_zeros hx y).countable.isPathConnected_compl_of_one_lt_rank
      one_lt_rank
    have h0 : (0 : ℂ) ∈ Sᶜ := by simpa [S] using hx
    have h1 : (1 : ℂ) ∈ Sᶜ := by simpa [S] using hy
    have := (hS.joinedIn 0 h0 1 h1).map (continuous_line x y).continuousOn
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at this
    refine this.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ht

/-- The nonvanishing locus of a nonzero complex polynomial is dense in the classical
topology. -/
theorem dense_setOf_eval_ne_zero {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    Dense {x : ι → ℂ | MvPolynomial.eval x p ≠ 0} := by
  obtain ⟨x, hx⟩ := (isPathConnected_setOf_eval_ne_zero hp).nonempty
  refine fun y ↦ ?_
  set S := {t : ℂ | MvPolynomial.eval (x + t • (y - x)) p = 0}
  have hS : Dense Sᶜ := (finite_line_zeros hx y).countable.dense_compl ℂ
  have h := image_closure_subset_closure_image (f := fun t : ℂ ↦ x + t • (y - x))
    (s := Sᶜ) (continuous_line x y)
  rw [hS.closure_eq, Set.image_univ] at h
  refine closure_mono ?_ (h ⟨1, by simp⟩)
  rintro _ ⟨t, ht, rfl⟩
  exact ht

end MMP.SmoothLocusConnected
