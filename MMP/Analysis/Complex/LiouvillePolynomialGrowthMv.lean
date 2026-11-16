module

public import MMP.Analysis.Complex.LiouvillePolynomialGrowth
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HypersurfaceComplement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Holomorphic functions of polynomial growth off a hypersurface are polynomials

Let `g` be a nonzero polynomial in `n` complex variables and `h` a holomorphic function on the
complement `{g ≠ 0}` of the hypersurface `g = 0` in `ℂⁿ`, with `‖h z‖ ≤ C (1 + ‖z‖)^N` there.
Then `h` is the restriction of a polynomial. This combines the Riemann extension theorem across
the hypersurface with Liouville's theorem for functions of polynomial growth.

We argue by induction on `n`, slicing along the first coordinate. Write `g` as a polynomial in
`z₀` with coefficients in `ℂ[z₁, …, zₙ₋₁]` and leading coefficient `ℓ`. For `x` with `ℓ(x) ≠ 0`,
the slice `t ↦ h(t, x)` is holomorphic off the finitely many roots of `g(·, x)` and has
polynomial growth, so it is a polynomial of degree at most `N`
(`MMP.LiouvilleGrowth.exists_polynomial_of_differentiableOn_compl_finite`). Its coefficients are,
by Lagrange interpolation at `N + 1` nodes chosen among `0, 1, …, N + deg g` away from the roots,
finite linear combinations of values of `h`; so they are holomorphic of polynomial growth on
`{ℓ ≠ 0}`, hence polynomials by induction. The two sides then agree on the dense set `{g ℓ ≠ 0}`
of `{g ≠ 0}`.

## Main results

* `MMP.exists_mvPolynomial_eq_of_differentiableOn_of_norm_le`: a holomorphic
  function on `{g ≠ 0} ⊆ ℂⁿ` bounded there by `C (1 + ‖z‖)^N` is a polynomial.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial Filter Topology Set

namespace MMP

namespace PolynomialGrowth

variable {n : ℕ}

/-- The sup norm of `Fin.cons t x` is at most `‖t‖ + ‖x‖`. -/
lemma norm_cons_le (t : ℂ) (x : Fin n → ℂ) :
    ‖(Fin.cons t x : Fin (n + 1) → ℂ)‖ ≤ ‖t‖ + ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp only [Fin.cons_succ]
    linarith [norm_le_pi_norm x j, norm_nonneg t]

/-- `(1 + ‖Fin.cons t x‖)^N ≤ (1 + ‖x‖)^N (1 + ‖t‖)^N`. -/
lemma one_add_norm_cons_pow_le (t : ℂ) (x : Fin n → ℂ) (N : ℕ) :
    (1 + ‖(Fin.cons t x : Fin (n + 1) → ℂ)‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖t‖) ^ N := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ N
  nlinarith [norm_cons_le t x, norm_nonneg t, norm_nonneg x]

/-- The map `t ↦ Fin.cons t x` from `ℂ` to `ℂⁿ⁺¹` is holomorphic. -/
lemma differentiable_cons_left (x : Fin n → ℂ) :
    Differentiable ℂ fun t : ℂ ↦ (Fin.cons t x : Fin (n + 1) → ℂ) := by
  fun_prop

/-- The map `x ↦ Fin.cons t x` from `ℂⁿ` to `ℂⁿ⁺¹` is holomorphic. -/
lemma differentiable_cons_right (t : ℂ) :
    Differentiable ℂ fun x : Fin n → ℂ ↦ (Fin.cons t x : Fin (n + 1) → ℂ) := by
  fun_prop

/-- A bound `‖a‖ ≤ C (1 + r)^N` with `0 ≤ r` forces `0 ≤ C`. -/
lemma nonneg_of_norm_le_mul_one_add_pow {E : Type*} [SeminormedAddCommGroup E] {a : E}
    {C r : ℝ} {N : ℕ} (hr : 0 ≤ r) (h : ‖a‖ ≤ C * (1 + r) ^ N) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (by positivity)

/-- Evaluating `g` at `Fin.cons t x` equals evaluating at `t` the one-variable polynomial obtained
from `g`, viewed as a polynomial in the first variable, by evaluating its coefficients at `x`. -/
lemma eval_cons (g : MvPolynomial (Fin (n + 1)) ℂ) (t : ℂ) (x : Fin n → ℂ) :
    MvPolynomial.eval (Fin.cons t x) g =
      ((MvPolynomial.finSuccEquiv ℂ n g).map (MvPolynomial.eval x)).eval t :=
  MvPolynomial.eval_eq_eval_mv_eval' x t g

/-- The slice of `g` through `x` along the first coordinate is a nonzero polynomial when the
leading coefficient `ℓ` of `g` in the first variable does not vanish at `x`. -/
lemma map_ne_zero {g : MvPolynomial (Fin (n + 1)) ℂ} {x : Fin n → ℂ}
    (hx : MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0) :
    (MvPolynomial.finSuccEquiv ℂ n g).map (MvPolynomial.eval x) ≠ 0 := by
  rwa [← leadingCoeff_ne_zero, leadingCoeff_map_of_leadingCoeff_ne_zero _ hx]

variable {g : MvPolynomial (Fin (n + 1)) ℂ} {h : (Fin (n + 1) → ℂ) → ℂ} {C : ℝ} {N : ℕ}

/-- The slices of `h` along the first coordinate are polynomials of degree at most `N`. -/
lemma exists_slice (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0})
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) {x : Fin n → ℂ}
    (hx : MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧
      ∀ t, MvPolynomial.eval (Fin.cons t x) g ≠ 0 → h (Fin.cons t x) = p.eval t := by
  set q := (MvPolynomial.finSuccEquiv ℂ n g).map (MvPolynomial.eval x)
  set S := {t | q.eval t = 0}
  have hSf : S.Finite := Polynomial.finite_setOf_isRoot (map_ne_zero hx)
  have hS : ∀ t, t ∉ S ↔ MvPolynomial.eval (Fin.cons t x) g ≠ 0 := fun t ↦ by
    rw [eval_cons]
    rfl
  have hC : 0 ≤ C := by
    obtain ⟨t, ht⟩ := hSf.infinite_compl.nonempty
    exact nonneg_of_norm_le_mul_one_add_pow (norm_nonneg _) (hb _ ((hS t).mp ht))
  obtain ⟨p, hp, hpe⟩ := LiouvilleGrowth.exists_polynomial_of_differentiableOn_compl_finite
    (f := fun t ↦ h (Fin.cons t x)) (C := C * (1 + ‖x‖) ^ N) (N := N) hSf
    (hh.comp (differentiable_cons_left x).differentiableOn fun t ht ↦ (hS t).mp ht)
    (fun t ht ↦ by
      refine (hb _ ((hS t).mp ht)).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (one_add_norm_cons_pow_le t x N) hC)
  exact ⟨p, hp, fun t ht ↦ hpe t ((hS t).mpr ht)⟩

/-- The coefficients of a polynomial of degree at most `N` are fixed linear combinations of its
values at `N + 1` distinct natural numbers (Lagrange interpolation). -/
lemma coeff_eq_sum_lagrange {p : ℂ[X]} {N : ℕ} (hp : p.natDegree ≤ N) {s : Finset ℕ}
    (hs : s.card = N + 1) (k : ℕ) :
    p.coeff k =
      ∑ c ∈ s, p.eval (c : ℂ) * (Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k := by
  have hinj : Set.InjOn (fun c : ℕ ↦ (c : ℂ)) s := Nat.cast_injective.injOn
  have hdeg : p.degree < s.card := by
    rw [hs]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  simp only [coeff_C_mul]

/-- Off the zeros of the leading coefficient, `N + 1` interpolation nodes avoiding the roots of the
slice of `g` can be chosen among `0, 1, …, N + deg g`. -/
lemma exists_nodes {g : MvPolynomial (Fin (n + 1)) ℂ} {x : Fin n → ℂ}
    (hx : MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0) (N : ℕ) :
    ∃ s ⊆ Finset.range (N + (MvPolynomial.finSuccEquiv ℂ n g).natDegree + 1),
      s.card = N + 1 ∧ ∀ c ∈ s, MvPolynomial.eval (Fin.cons (c : ℂ) x) g ≠ 0 := by
  classical
  set G := MvPolynomial.finSuccEquiv ℂ n g
  set q := G.map (MvPolynomial.eval x)
  set R := Finset.range (N + G.natDegree + 1)
  set A := R.filter fun c : ℕ ↦ MvPolynomial.eval (Fin.cons (c : ℂ) x) g ≠ 0
  set B := R.filter fun c : ℕ ↦ ¬ MvPolynomial.eval (Fin.cons (c : ℂ) x) g ≠ 0
  have hB : B.card ≤ G.natDegree := by
    have h1 : B.card ≤ q.roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun c : ℕ ↦ (c : ℂ)) ?_ Nat.cast_injective.injOn
      intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      rw [not_not, eval_cons] at hc'
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (mem_roots (map_ne_zero hx)).mpr hc'
    exact h1.trans ((Multiset.toFinset_card_le _).trans ((card_roots' q).trans natDegree_map_le))
  have hAB : A.card + B.card = R.card := Finset.card_filter_add_card_filter_not _
  have hR : R.card = N + G.natDegree + 1 := Finset.card_range _
  obtain ⟨s, hsA, hs⟩ := Finset.exists_subset_card_eq (s := A) (n := N + 1) (by omega)
  exact ⟨s, hsA.trans (Finset.filter_subset _ _), hs,
    fun c hc ↦ (Finset.mem_filter.mp (hsA hc)).2⟩

open Classical in
/-- The slice of `h` through `x` along the first coordinate, as a polynomial of degree at most
`N`, when there is one (and `0` otherwise). -/
noncomputable def slicePoly (g : MvPolynomial (Fin (n + 1)) ℂ) (h : (Fin (n + 1) → ℂ) → ℂ)
    (N : ℕ) (x : Fin n → ℂ) : ℂ[X] :=
  if hx : ∃ p : ℂ[X], p.natDegree ≤ N ∧
      ∀ t, MvPolynomial.eval (Fin.cons t x) g ≠ 0 → h (Fin.cons t x) = p.eval t
  then hx.choose else 0

/-- Where the leading coefficient of `g` in the first variable does not vanish at `x`,
`slicePoly g h N x` has degree at most `N` and agrees with `t ↦ h (Fin.cons t x)` wherever
`g (Fin.cons t x) ≠ 0`. -/
lemma slicePoly_spec (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0})
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) {x : Fin n → ℂ}
    (hx : MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0) :
    (slicePoly g h N x).natDegree ≤ N ∧ ∀ t, MvPolynomial.eval (Fin.cons t x) g ≠ 0 →
      h (Fin.cons t x) = (slicePoly g h N x).eval t := by
  have he := exists_slice hh hb hx
  rw [slicePoly, dif_pos he]
  exact he.choose_spec

/-- The coefficients of the slice polynomial are given, near `x`, by Lagrange interpolation at
any admissible nodes. -/
lemma slicePoly_coeff_eq (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0})
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) {x : Fin n → ℂ}
    (hx : MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0)
    {s : Finset ℕ} (hs : s.card = N + 1)
    (hsg : ∀ c ∈ s, MvPolynomial.eval (Fin.cons (c : ℂ) x) g ≠ 0) (k : ℕ) :
    (slicePoly g h N x).coeff k =
      ∑ c ∈ s, h (Fin.cons (c : ℂ) x) * (Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k := by
  obtain ⟨hdeg, heq⟩ := slicePoly_spec hh hb hx
  rw [coeff_eq_sum_lagrange hdeg hs]
  exact Finset.sum_congr rfl fun c hc ↦ by rw [heq _ (hsg c hc)]

/-- The complement of the zero set of a complex polynomial is open. -/
lemma isOpen_setOf_eval_ne_zero {ι : Type*} (p : MvPolynomial ι ℂ) :
    IsOpen {z : ι → ℂ | MvPolynomial.eval z p ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const

/-- The coefficients of the slice polynomials are holomorphic off the zeros of the leading
coefficient. -/
lemma differentiableOn_slicePoly_coeff
    (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0})
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) (k : ℕ) :
    DifferentiableOn ℂ (fun x ↦ (slicePoly g h N x).coeff k)
      {x | MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0} := by
  intro x₀ hx₀
  obtain ⟨s, -, hs, hsg⟩ := exists_nodes hx₀ N
  set W := {x : Fin n → ℂ |
      MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0} ∩
      ⋂ c ∈ s, {x | MvPolynomial.eval (Fin.cons (c : ℂ) x) g ≠ 0}
  have hW : W ∈ 𝓝 x₀ := by
    refine IsOpen.mem_nhds ((isOpen_setOf_eval_ne_zero _).inter
      (isOpen_biInter_finset fun c _ ↦ ?_)) ⟨hx₀, Set.mem_iInter₂.mpr hsg⟩
    exact isOpen_ne_fun ((MvPolynomial.continuous_eval g).comp
      (differentiable_cons_right (c : ℂ)).continuous) continuous_const
  have hF : DifferentiableAt ℂ (fun x ↦ ∑ c ∈ s, h (Fin.cons (c : ℂ) x) *
      (Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k) x₀ := by
    refine DifferentiableAt.fun_sum fun c hc ↦ DifferentiableAt.mul_const ?_ _
    exact (hh.differentiableAt ((isOpen_setOf_eval_ne_zero g).mem_nhds (hsg c hc))).comp x₀
      (differentiable_cons_right _ _)
  refine (hF.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hW] with x hx
  exact slicePoly_coeff_eq hh hb hx.1 hs (Set.mem_iInter₂.mp hx.2) k

/-- The coefficients of the slice polynomials have polynomial growth. -/
lemma norm_slicePoly_coeff_le
    (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0})
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) (k : ℕ) :
    ∃ C' : ℝ, ∀ x, MvPolynomial.eval x (MvPolynomial.finSuccEquiv ℂ n g).leadingCoeff ≠ 0 →
      ‖(slicePoly g h N x).coeff k‖ ≤ C' * (1 + ‖x‖) ^ N := by
  classical
  set M := N + (MvPolynomial.finSuccEquiv ℂ n g).natDegree + 1
  set β : Finset ℕ → ℕ → ℝ := fun s c ↦
    (1 + (c : ℝ)) ^ N * ‖(Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k‖
  set B := ∑ s ∈ (Finset.range M).powerset, ∑ c ∈ s, β s c
  refine ⟨C * B, fun x hx ↦ ?_⟩
  obtain ⟨s, hsM, hs, hsg⟩ := exists_nodes hx N
  have hC : 0 ≤ C := by
    obtain ⟨c, hc⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    exact nonneg_of_norm_le_mul_one_add_pow (norm_nonneg _) (hb _ (hsg c hc))
  rw [slicePoly_coeff_eq hh hb hx hs hsg]
  calc ‖∑ c ∈ s, h (Fin.cons (c : ℂ) x) * (Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k‖
      ≤ ∑ c ∈ s, C * (1 + ‖x‖) ^ N * β s c := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc ↦ ?_)
        rw [norm_mul]
        have h1 := (hb _ (hsg c hc)).trans (mul_le_mul_of_nonneg_left
          (one_add_norm_cons_pow_le (c : ℂ) x N) hC)
        rw [Complex.norm_natCast] at h1
        calc ‖h (Fin.cons (c : ℂ) x)‖ * ‖(Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k‖
            ≤ C * ((1 + ‖x‖) ^ N * (1 + (c : ℝ)) ^ N) *
                ‖(Lagrange.basis s (fun c : ℕ ↦ (c : ℂ)) c).coeff k‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = C * (1 + ‖x‖) ^ N * β s c := by
            simp only [β]
            ring
    _ = C * (1 + ‖x‖) ^ N * ∑ c ∈ s, β s c := by rw [Finset.mul_sum]
    _ ≤ C * (1 + ‖x‖) ^ N * B := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.single_le_sum (f := fun s ↦ ∑ c ∈ s, β s c)
          (fun s _ ↦ Finset.sum_nonneg fun c _ ↦ by positivity) (Finset.mem_powerset.mpr hsM)
    _ = C * B * (1 + ‖x‖) ^ N := by ring

end PolynomialGrowth

open PolynomialGrowth in
/-- **Holomorphic functions of polynomial growth off a hypersurface are polynomials.** Let `g` be
a nonzero polynomial in `n` complex variables and `h` holomorphic on `{g ≠ 0} ⊆ ℂⁿ` with
`‖h z‖ ≤ C (1 + ‖z‖)^N` there. Then `h` agrees on `{g ≠ 0}` with a polynomial. (Riemann extension
across the hypersurface `g = 0` followed by Liouville's theorem with polynomial growth.) -/
theorem exists_mvPolynomial_eq_of_differentiableOn_of_norm_le {n : ℕ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ≠ 0) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h {z | MvPolynomial.eval z g ≠ 0}) {C : ℝ} {N : ℕ}
    (hb : ∀ z, MvPolynomial.eval z g ≠ 0 → ‖h z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z g ≠ 0 →
      h z = MvPolynomial.eval z P := by
  induction n generalizing C with
  | zero =>
    refine ⟨MvPolynomial.C (h 0), fun z _ ↦ ?_⟩
    rw [MvPolynomial.eval_C, Subsingleton.elim z 0]
  | succ n ih =>
    set G := MvPolynomial.finSuccEquiv ℂ n g
    have hG : G ≠ 0 := fun h0 ↦ hg ((MvPolynomial.finSuccEquiv ℂ n).injective
      (h0.trans (map_zero _).symm))
    have hℓ : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hG
    choose C' hC' using fun k ↦ norm_slicePoly_coeff_le hh hb k
    choose P hP using fun k ↦ ih hℓ (differentiableOn_slicePoly_coeff hh hb k) (hC' k)
    set Q := (MvPolynomial.finSuccEquiv ℂ n).symm
      (∑ k ∈ Finset.range (N + 1), Polynomial.monomial k (P k))
    have hkey : ∀ (t : ℂ) (x : Fin n → ℂ), MvPolynomial.eval x G.leadingCoeff ≠ 0 →
        MvPolynomial.eval (Fin.cons t x) g ≠ 0 →
        h (Fin.cons t x) = MvPolynomial.eval (Fin.cons t x) Q := by
      intro t x hx htx
      obtain ⟨hdeg, heq⟩ := slicePoly_spec hh hb hx
      rw [heq t htx, MvPolynomial.eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply,
        eval_eq_sum_range' (n := N + 1) (by omega), Polynomial.map_sum, eval_finset_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Polynomial.map_monomial, eval_monomial, hP k x hx]
    set ℓ' := MvPolynomial.rename Fin.succ G.leadingCoeff
    have hℓ' : ℓ' ≠ 0 := fun h0 ↦ hℓ (MvPolynomial.rename_injective _ (Fin.succ_injective _)
      (h0.trans (map_zero _).symm))
    refine ⟨Q, fun z hz ↦ ?_⟩
    refine Set.EqOn.of_subset_closure (s := {z | MvPolynomial.eval z g ≠ 0} ∩
        {z | MvPolynomial.eval z ℓ' ≠ 0}) (t := {z | MvPolynomial.eval z g ≠ 0})
      (fun z hz ↦ ?_) hh.continuousOn (MvPolynomial.continuous_eval Q).continuousOn
      Set.inter_subset_left ((MMP.SmoothLocusConnected.dense_setOf_eval_ne_zero
        hℓ').open_subset_closure_inter (isOpen_setOf_eval_ne_zero g)) hz
    have hz2 : MvPolynomial.eval (Fin.tail z) G.leadingCoeff ≠ 0 := by
      have := hz.2
      simp only [Set.mem_setOf_eq, ℓ', MvPolynomial.eval_rename] at this
      exact this
    have := hkey (z 0) (Fin.tail z) hz2 (by rw [Fin.cons_self_tail]; exact hz.1)
    rwa [Fin.cons_self_tail] at this

end MMP
