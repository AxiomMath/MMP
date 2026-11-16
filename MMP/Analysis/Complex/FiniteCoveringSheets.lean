module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The sheets of a polynomial with simple roots over `ℂⁿ`

Let `f` be a polynomial in one variable `t` whose coefficients are polynomials in
`x = (x₁, …, xₙ) ∈ ℂⁿ`, and write `f_x` for its specialization at `x`. If `t₀` is a simple root
of `f_{x₀}`, the implicit function theorem gives a holomorphic function `φ` near `x₀` with
`φ(x₀) = t₀` and `f_x(φ(x)) = 0`. When `f` is monic and `f_{x₀}` is separable, the `d = deg f`
roots of `f_{x₀}` give `d` such sheets, and near `x₀` the roots of `f_x` are exactly their values:
`{f = 0}` is a `d`-sheeted covering near `x₀`.

## Main results

* `MMP.SmoothLocusConnected.exists_implicit_root`: a holomorphic implicit root.
* `MMP.SmoothLocusConnected.exists_sheets`: near a point where `f_x` is separable,
  the roots of `f_x` are the values of `deg f` holomorphic functions.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial Filter Topology Set

namespace MMP.SmoothLocusConnected

/-- Polynomial functions on `ℂ^ι` are smooth. -/
lemma contDiff_mvPolynomial_eval {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ)
    {m : WithTop ℕ∞} : ContDiff ℂ m fun z : ι → ℂ ↦ MvPolynomial.eval z P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℂ (fun _ : ι ↦ ℂ) i)

/-- **A holomorphic implicit root.** If `F(u) = 0` and `∂F/∂t (u) ≠ 0` for a `C¹` function
`F : E × ℂ → ℂ`, there is a function `φ`, holomorphic near `u.1`, with `φ(u.1) = u.2` and
`F(x, φ(x)) = 0` near `u.1`. -/
theorem exists_implicit_root {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : E × ℂ → ℂ} {u : E × ℂ} (hF : ContDiff ℂ 1 F) (hu : F u = 0) {c : ℂ}
    (hc : HasDerivAt (fun t ↦ F (u.1, t)) c u.2) (hc0 : c ≠ 0) :
    ∃ φ : E → ℂ, φ u.1 = u.2 ∧ ∀ᶠ x in 𝓝 u.1, F (x, φ x) = 0 ∧ DifferentiableAt ℂ φ x := by
  have cdf : ContDiffAt ℂ 1 F u := hF.contDiffAt
  have hd : HasDerivAt (fun t ↦ F (u.1, t)) (fderiv ℂ F u (0, 1)) u.2 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ (u.1, t)) ((0 : E), (1 : ℂ)) u.2 :=
      (hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)
    have h2 : HasFDerivAt F (fderiv ℂ F u) (u.1, u.2) :=
      (hF.differentiable one_ne_zero u).hasFDerivAt
    exact h2.comp_hasDerivAt u.2 h1
  have hcd : c = fderiv ℂ F u (0, 1) := hc.unique hd
  have if₂ : (fderiv ℂ F u ∘L .inr ℂ E ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc0),
      ContinuousLinearMap.ext_ring ?_⟩
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, hcd]
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self _ _, ?_⟩
  filter_upwards [cdf.eventually_apply_implicitFunction one_ne_zero if₂,
    (cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)] with x hx hx'
  exact ⟨hx.trans hu, hx'.differentiableAt one_ne_zero⟩

variable {n : ℕ}

/-- The specialization `(x, t) ↦ f_x(t)` of a polynomial with polynomial coefficients is
smooth. -/
lemma contDiff_eval_map (f : (MvPolynomial (Fin n) ℂ)[X]) {m : WithTop ℕ∞} :
    ContDiff ℂ m fun u : (Fin n → ℂ) × ℂ ↦ (f.map (MvPolynomial.eval u.1)).eval u.2 := by
  have : (fun u : (Fin n → ℂ) × ℂ ↦ (f.map (MvPolynomial.eval u.1)).eval u.2) =
      fun u ↦ MvPolynomial.eval (Fin.consEquivL ℂ (fun _ ↦ ℂ) (u.2, u.1))
        ((MvPolynomial.finSuccEquiv ℂ n).symm f) := by
    ext u
    have h : (Fin.consEquivL ℂ (fun _ ↦ ℂ) (u.2, u.1) : Fin (n + 1) → ℂ) = Fin.cons u.2 u.1 := by
      ext i; simp
    rw [h, MvPolynomial.eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply]
  rw [this]
  exact (contDiff_mvPolynomial_eval _).comp
    ((Fin.consEquivL ℂ (fun _ ↦ ℂ)).contDiff.comp (contDiff_snd.prodMk contDiff_fst))

/-- A separable complex polynomial has as many distinct roots as its degree. -/
lemma card_roots_toFinset_of_separable {p : ℂ[X]} (hp : p.Separable) :
    p.roots.toFinset.card = p.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hp)]
  exact splits_iff_card_roots.mp (IsAlgClosed.splits p)

/-- **The sheets of `{f = 0}` over `ℂⁿ`.** Let `f` be a monic polynomial in `t` with coefficients
in `ℂ[x₁, …, xₙ]` and `x₀ ∈ ℂⁿ` a point at which `f_{x₀}` is separable. There are functions
`φ_r`, one for each root `r` of `f_{x₀}`, with `φ_r(x₀) = r`, holomorphic near `x₀`, such that
near `x₀` the roots of `f_x` are the pairwise distinct values `φ_r(x)`. -/
theorem exists_sheets {f : (MvPolynomial (Fin n) ℂ)[X]} (hf : f.Monic) {x₀ : Fin n → ℂ}
    (hsep : (f.map (MvPolynomial.eval x₀)).Separable) :
    ∃ φ : ℂ → (Fin n → ℂ) → ℂ, (∀ r, φ r x₀ = r) ∧ ∀ᶠ x in 𝓝 x₀,
      (∀ r ∈ (f.map (MvPolynomial.eval x₀)).roots.toFinset, DifferentiableAt ℂ (φ r) x) ∧
      Set.InjOn (fun r ↦ φ r x) (f.map (MvPolynomial.eval x₀)).roots.toFinset ∧
      (f.map (MvPolynomial.eval x)).roots.toFinset =
        (f.map (MvPolynomial.eval x₀)).roots.toFinset.image fun r ↦ φ r x := by
  classical
  set R₀ := (f.map (MvPolynomial.eval x₀)).roots.toFinset
  set F := fun u : (Fin n → ℂ) × ℂ ↦ (f.map (MvPolynomial.eval u.1)).eval u.2
  have hex : ∀ r : ℂ, ∃ ψ : (Fin n → ℂ) → ℂ, ψ x₀ = r ∧
      (r ∈ R₀ → ∀ᶠ x in 𝓝 x₀, F (x, ψ x) = 0 ∧ DifferentiableAt ℂ ψ x) := by
    intro r
    by_cases hr : r ∈ R₀
    · have hroot : (f.map (MvPolynomial.eval x₀)).eval r = 0 := by
        have := Multiset.mem_toFinset.mp hr
        exact (mem_roots (hf.map _).ne_zero).mp this
      have hder : (f.map (MvPolynomial.eval x₀)).derivative.eval r ≠ 0 := by
        have := hsep.aeval_derivative_ne_zero (x := r) (by rwa [coe_aeval_eq_eval])
        rwa [coe_aeval_eq_eval] at this
      obtain ⟨ψ, hψ0, hψ⟩ := exists_implicit_root (u := (x₀, r)) (contDiff_eval_map f) hroot
        (by simpa using Polynomial.hasDerivAt (f.map (MvPolynomial.eval x₀)) r) hder
      exact ⟨ψ, hψ0, fun _ ↦ hψ⟩
    · exact ⟨fun _ ↦ r, rfl, fun h ↦ absurd h hr⟩
  choose φ hφ0 hφ using hex
  refine ⟨φ, hφ0, ?_⟩
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ r ∈ R₀, F (x, φ r x) = 0 ∧ DifferentiableAt ℂ (φ r) x :=
    (Filter.eventually_all_finset R₀).mpr fun r hr ↦ hφ r hr
  have hcont : ∀ r ∈ R₀, ContinuousAt (φ r) x₀ := fun r hr ↦
    ((hφ r hr).self_of_nhds).2.continuousAt
  have hinj : ∀ᶠ x in 𝓝 x₀, ∀ p ∈ R₀ ×ˢ R₀, p.1 ≠ p.2 → φ p.1 x ≠ φ p.2 x := by
    refine (Filter.eventually_all_finset _).mpr fun p hp ↦ ?_
    by_cases hne : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ h ↦ absurd hne h
    · obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      have : ContinuousAt (fun x ↦ φ p.1 x - φ p.2 x) x₀ := (hcont _ h1).sub (hcont _ h2)
      filter_upwards [this.eventually_ne (by rw [hφ0, hφ0]; exact sub_ne_zero.mpr hne)]
        with x hx _
      exact sub_ne_zero.mp hx
  filter_upwards [hall, hinj] with x hx hx'
  have hInj : Set.InjOn (fun r ↦ φ r x) R₀ := fun r hr r' hr' h ↦ by
    by_contra hne
    exact hx' (r, r') (Finset.mem_product.mpr ⟨hr, hr'⟩) hne h
  refine ⟨fun r hr ↦ (hx r hr).2, hInj, ?_⟩
  have hsub : R₀.image (fun r ↦ φ r x) ⊆ (f.map (MvPolynomial.eval x)).roots.toFinset := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    exact Multiset.mem_toFinset.mpr ((mem_roots (hf.map _).ne_zero).mpr (hx r hr).1)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injOn hInj, card_roots_toFinset_of_separable hsep,
    hf.natDegree_map, ← hf.natDegree_map (MvPolynomial.eval x)]
  exact (Multiset.toFinset_card_le _).trans (card_roots' _)

end MMP.SmoothLocusConnected
