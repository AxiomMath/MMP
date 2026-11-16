module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Good directions: a linear change of coordinates making a polynomial monic

Let `K` be an infinite field and `f ≠ 0` a polynomial in the variables `X_i` (`i ∈ σ`) and `T`,
of total degree `d`. After the shear `X_i ↦ X_i + v_i T`, `T ↦ T`, the polynomial `f`, read as a
polynomial in `T` with coefficients in `K[X_σ]`, has degree at most `d`, and its coefficient of
`T^d` is the constant `f_d(v, 1)`, where `f_d` is the homogeneous component of degree `d` of `f`.
Since `f_d ≠ 0` and `K` is infinite, `f_d(v, 1) ≠ 0` for some `v`: in the sheared coordinates,
`f` is a nonzero constant times a monic polynomial in `T`. This is the step of the cylindrical
decomposition, of the triangulation of semialgebraic sets and of Hardt's triviality theorem
where the projection `(x, t) ↦ x` is made finite on the zero set of `f`.

## Main definitions

* `MMP.shearPolynomial v`: the substitution `X_i ↦ X_i + v_i T`, `T ↦ T`, from
  `K[X_{Option σ}]` (with `T = X_none`) to `K[X_σ][T]`.

## Main results

* `MMP.natDegree_shearPolynomial_le`: the `T`-degree is at most the total degree.
* `MMP.coeff_shearPolynomial`: the coefficient of `T^n`, `n ≥ totalDegree f`, is
  the constant `f_n(v, 1)`.
* `MMP.exists_shearPolynomial_leadingCoeff`: for `f ≠ 0` some shear makes `f`
  of `T`-degree `totalDegree f` with a nonzero constant leading coefficient.
* `MMP.exists_shearPolynomial_leadingCoeff_forall`: one shear does this for
  finitely many nonzero polynomials at once.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], the preparation of a
  polynomial by a linear change of coordinates in the proof of Theorem 9.2.1.
-/

@[expose] public section

open Polynomial

namespace MMP

section ProdPow

variable {S ι : Type*} [CommSemiring S] [DecidableEq ι]

/-- A product of powers of polynomials of degree at most one has degree at most the sum of the
exponents, and its coefficient there is the product of powers of the linear coefficients. -/
theorem natDegree_prod_pow_le_and_coeff (s : Finset ι) (g : ι → S[X]) (k : ι → ℕ)
    (hg : ∀ i ∈ s, (g i).natDegree ≤ 1) :
    (∏ i ∈ s, g i ^ k i).natDegree ≤ ∑ i ∈ s, k i ∧
      (∏ i ∈ s, g i ^ k i).coeff (∑ i ∈ s, k i) = ∏ i ∈ s, (g i).coeff 1 ^ k i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha IH =>
    obtain ⟨IH₁, IH₂⟩ := IH fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
    have hpow : (g a ^ k a).natDegree ≤ k a :=
      natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (k a) (hg a (by simp)))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (add_le_add hpow IH₁), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpow IH₁, IH₂]
    congr 1
    simpa using coeff_pow_of_natDegree_le (m := k a) (hg a (by simp))

end ProdPow

variable {K σ : Type*} [Field K]

/-- The linear forms of the shear: `T` for `none`, `X_i + v_i T` for `some i`. -/
noncomputable def shearPolynomialAux (v : σ → K) (o : Option σ) : (MvPolynomial σ K)[X] :=
  o.elim Polynomial.X fun i ↦ C (MvPolynomial.X i) + C (MvPolynomial.C (v i)) * Polynomial.X

/-- The shear `X_i ↦ X_i + v_i T`, `T ↦ T`, from `K[X_{Option σ}]` (`T = X_none`) to
`K[X_σ][T]`. -/
noncomputable def shearPolynomial (v : σ → K) :
    MvPolynomial (Option σ) K →ₐ[K] (MvPolynomial σ K)[X] :=
  MvPolynomial.aeval (shearPolynomialAux v)

/-- The point `(v, 1)`: the leading coefficients of the linear forms of the shear. -/
def shearDirection (v : σ → K) (o : Option σ) : K := o.elim 1 v

/-- Each linear form of the shear has `T`-degree at most one. -/
theorem natDegree_shearPolynomialAux_le (v : σ → K) (o : Option σ) :
    (shearPolynomialAux v o).natDegree ≤ 1 := by
  rcases o with _ | i
  · simp [shearPolynomialAux]
  · simp only [shearPolynomialAux, Option.elim_some]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)

/-- The coefficient of `T` in the linear form of the shear indexed by `o` is the constant
`shearDirection v o`. -/
theorem coeff_one_shearPolynomialAux (v : σ → K) (o : Option σ) :
    (shearPolynomialAux v o).coeff 1 = MvPolynomial.C (shearDirection v o) := by
  rcases o with _ | i
  · simp [shearPolynomialAux, shearDirection]
  · simp [shearPolynomialAux, shearDirection, coeff_C]

/-- The shear of a monomial `c X^m` has `T`-degree at most `|m|`, with coefficient
`c (v, 1)^m` there. -/
theorem shearPolynomial_monomial (v : σ → K) (m : Option σ →₀ ℕ) (c : K) :
    (shearPolynomial v (MvPolynomial.monomial m c)).natDegree ≤ m.degree ∧
      (shearPolynomial v (MvPolynomial.monomial m c)).coeff m.degree =
        MvPolynomial.C (c * m.prod fun o k ↦ shearDirection v o ^ k) := by
  classical
  obtain ⟨h₁, h₂⟩ := natDegree_prod_pow_le_and_coeff m.support (shearPolynomialAux v) m
    fun o _ ↦ natDegree_shearPolynomialAux_le v o
  have hdeg : m.degree = ∑ o ∈ m.support, m o := rfl
  have hshear : shearPolynomial v (MvPolynomial.monomial m c) =
      C (MvPolynomial.C c) * ∏ o ∈ m.support, shearPolynomialAux v o ^ m o := by
    rw [shearPolynomial, MvPolynomial.aeval_monomial]
    rfl
  rw [hshear, hdeg]
  refine ⟨(natDegree_C_mul_le _ _).trans h₁, ?_⟩
  rw [coeff_C_mul, h₂]
  simp only [coeff_one_shearPolynomialAux, Finsupp.prod, map_mul, map_prod, map_pow]

/-- The shear of `f` has `T`-degree at most the total degree of `f`. -/
theorem natDegree_shearPolynomial_le (v : σ → K) (f : MvPolynomial (Option σ) K) :
    (shearPolynomial v f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  exact (shearPolynomial_monomial v m _).1.trans (MvPolynomial.le_totalDegree hm)

/-- **The leading coefficient of a shear.** For `n ≥ totalDegree f`, the coefficient of `T^n`
in the shear of `f` is the constant `f_n(v, 1)`, the value at `(v, 1)` of the homogeneous
component of degree `n` of `f`. -/
theorem coeff_shearPolynomial (v : σ → K) (f : MvPolynomial (Option σ) K) {n : ℕ}
    (hn : f.totalDegree ≤ n) :
    (shearPolynomial v f).coeff n =
      MvPolynomial.C (MvPolynomial.eval (shearDirection v)
        (MvPolynomial.homogeneousComponent n f)) := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [finset_sum_coeff, MvPolynomial.homogeneousComponent_apply, map_sum, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨h₁, h₂⟩ := shearPolynomial_monomial v m (f.coeff m)
  have hle : m.degree ≤ n := (MvPolynomial.le_totalDegree hm).trans hn
  split_ifs with h
  · rw [← h, h₂, MvPolynomial.eval_monomial]
  · exact coeff_eq_zero_of_natDegree_lt (h₁.trans_lt (lt_of_le_of_ne hle h))

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero {τ : Type*} {f : MvPolynomial τ K}
    (hf : f ≠ 0) : MvPolynomial.homogeneousComponent f.totalDegree f ≠ 0 := by
  classical
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_eq_empty.not.2 hf |> Finset.nonempty_iff_ne_empty.2)
    fun s ↦ s.sum fun _ e ↦ e
  intro h
  have := congrArg (fun p => p.coeff m) h
  rw [MvPolynomial.coeff_homogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply,
    if_pos (by rw [MvPolynomial.totalDegree, hmd]; rfl)] at this
  exact (MvPolynomial.mem_support_iff.1 hm) this

/-- Homogeneous polynomials scale: `h(t y) = t^n h(y)`. -/
theorem eval_smul_of_isHomogeneous {τ : Type*} [Fintype τ] {h : MvPolynomial τ K} {n : ℕ}
    (hh : h.IsHomogeneous n) (t : K) (y : τ → K) :
    MvPolynomial.eval (t • y) h = t ^ n * MvPolynomial.eval y h := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have := hh (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- **Good directions.** Over an infinite field, every nonzero `f ∈ K[X_σ, T]` has a shear
`X_i ↦ X_i + v_i T` after which, as a polynomial in `T` over `K[X_σ]`, it has degree
`totalDegree f` and a nonzero constant leading coefficient. -/
theorem exists_shearPolynomial_leadingCoeff [Infinite K] [Fintype σ]
    {f : MvPolynomial (Option σ) K} (hf : f ≠ 0) :
    ∃ v : σ → K, ∃ c : K, c ≠ 0 ∧ (shearPolynomial v f).natDegree = f.totalDegree ∧
      (shearPolynomial v f).leadingCoeff = MvPolynomial.C c := by
  set h := MvPolynomial.homogeneousComponent f.totalDegree f
  have hh : h.IsHomogeneous f.totalDegree := MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have hne : h * MvPolynomial.X none ≠ 0 :=
    mul_ne_zero (homogeneousComponent_totalDegree_ne_zero hf) (MvPolynomial.X_ne_zero _)
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (h * MvPolynomial.X none) ≠ 0 := by
    by_contra! H
    exact hne (MvPolynomial.funext fun x ↦ by simp [H x])
  rw [map_mul, MvPolynomial.eval_X] at hx
  obtain ⟨hx₁, hx₂⟩ := mul_ne_zero_iff.1 hx
  set v : σ → K := fun i ↦ (x none)⁻¹ * x (some i)
  have hxv : x = x none • shearDirection v := by
    funext o
    rcases o with _ | i
    · simp [shearDirection]
    · simp [shearDirection, v, hx₂]
  have hc : MvPolynomial.eval (shearDirection v) h ≠ 0 := by
    intro h0
    rw [hxv, eval_smul_of_isHomogeneous hh, h0, mul_zero] at hx₁
    exact hx₁ rfl
  have hcoeff := coeff_shearPolynomial v f le_rfl
  have hdeg : (shearPolynomial v f).natDegree = f.totalDegree := by
    refine le_antisymm (natDegree_shearPolynomial_le v f) (le_natDegree_of_ne_zero ?_)
    rw [hcoeff]
    exact (map_ne_zero_iff _ (MvPolynomial.C_injective σ K)).2 hc
  refine ⟨v, _, hc, hdeg, ?_⟩
  rw [leadingCoeff, hdeg, hcoeff]

/-- A factor of a nonzero constant polynomial is a nonzero constant. -/
theorem exists_eq_C_of_mul_eq_C {τ : Type*} {a b : MvPolynomial τ K} {c : K} (hc : c ≠ 0)
    (h : a * b = MvPolynomial.C c) : ∃ c' : K, c' ≠ 0 ∧ a = MvPolynomial.C c' := by
  have hab : a * b ≠ 0 := by rw [h]; exact (map_ne_zero_iff _ (MvPolynomial.C_injective τ K)).2 hc
  have ha : a ≠ 0 := left_ne_zero_of_mul hab
  have hb : b ≠ 0 := right_ne_zero_of_mul hab
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain ha hb
  rw [h, MvPolynomial.totalDegree_C] at hdeg
  have ha0 : a = MvPolynomial.C (a.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (by omega)
  refine ⟨_, fun h0 ↦ ha ?_, ha0⟩
  rw [ha0, h0, map_zero]

/-- **Good directions for a finite family.** Over an infinite field, finitely many nonzero
`f_j ∈ K[X_σ, T]` have a common shear `X_i ↦ X_i + v_i T` after which each has a nonzero
constant leading coefficient as a polynomial in `T`: apply
`MMP.exists_shearPolynomial_leadingCoeff` to their product. -/
theorem exists_shearPolynomial_leadingCoeff_forall [Infinite K] [Fintype σ] {ι : Type*}
    (s : Finset ι) {f : ι → MvPolynomial (Option σ) K} (hf : ∀ j ∈ s, f j ≠ 0) :
    ∃ v : σ → K, ∀ j ∈ s, ∃ c : K, c ≠ 0 ∧
      (shearPolynomial v (f j)).leadingCoeff = MvPolynomial.C c := by
  classical
  obtain ⟨v, c, hc, -, hlc⟩ :=
    exists_shearPolynomial_leadingCoeff (Finset.prod_ne_zero_iff.2 hf)
  refine ⟨v, fun j hj ↦ ?_⟩
  rw [map_prod, leadingCoeff_prod, ← Finset.mul_prod_erase s _ hj] at hlc
  exact exists_eq_C_of_mul_eq_C hc hlc

end MMP
