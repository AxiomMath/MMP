module

public import MMP.Analysis.Complex.FiniteCoveringSheets

/-!
# Holomorphic sheets of a polynomial with holomorphic coefficients

Let `f` be a monic polynomial in one variable `t` whose coefficients `a_i(x)` are holomorphic
functions of `x` near a point `x₀` of a complex Banach space, and suppose that `f_{x₀}` is
separable. Each of the `d = deg f` roots `r` of `f_{x₀}` is simple, so the holomorphic implicit
function theorem gives a function `φ_r`, holomorphic near `x₀`, with `φ_r(x₀) = r` and
`f_x(φ_r(x)) = 0`. Near `x₀` the values `φ_r(x)` are pairwise distinct, and since `f_x` has at
most `d` roots they are all of them: near `x₀`, `{f = 0}` is the union of the `d` disjoint graphs
of the `φ_r`.

This is `MMP.SmoothLocusConnected.exists_sheets` with holomorphic coefficients in
place of polynomial ones.

## Main results

* `MMP.GenericCovering.exists_analytic_implicit_root`: a holomorphic implicit root.
* `MMP.GenericCovering.exists_analytic_sheets`: near a point where `f_x` is
  separable, the roots of `f_x` are the values of `deg f` holomorphic functions.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial Filter Topology Set
open scoped ContDiff

namespace MMP.GenericCovering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **A holomorphic implicit root.** If `F(u) = 0` and `∂F/∂t (u) ≠ 0` for a function
`F : E × ℂ → ℂ` holomorphic at `u`, there is a function `φ`, holomorphic near `u.1`, with
`φ(u.1) = u.2` and `F(x, φ(x)) = 0` near `u.1`. -/
theorem exists_analytic_implicit_root {F : E × ℂ → ℂ} {u : E × ℂ} (hF : ContDiffAt ℂ ω F u)
    (hu : F u = 0) {c : ℂ} (hc : HasDerivAt (fun t ↦ F (u.1, t)) c u.2) (hc0 : c ≠ 0) :
    ∃ φ : E → ℂ, φ u.1 = u.2 ∧ ∀ᶠ x in 𝓝 u.1, F (x, φ x) = 0 ∧ ContDiffAt ℂ ω φ x := by
  have hd : HasDerivAt (fun t ↦ F (u.1, t)) (fderiv ℂ F u (0, 1)) u.2 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ (u.1, t)) ((0 : E), (1 : ℂ)) u.2 :=
      (hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)
    have h2 : HasFDerivAt F (fderiv ℂ F u) (u.1, u.2) :=
      (hF.differentiableAt (by simp)).hasFDerivAt
    exact h2.comp_hasDerivAt u.2 h1
  have hcd : c = fderiv ℂ F u (0, 1) := hc.unique hd
  have if₂ : (fderiv ℂ F u ∘L .inr ℂ E ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc0),
      ContinuousLinearMap.ext_ring ?_⟩
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, hcd]
  refine ⟨hF.implicitFunction (by simp) if₂, hF.implicitFunction_apply_self _ _, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction (by simp) if₂,
    (hF.contDiffAt_implicitFunction (by simp) if₂).eventually (by simp)] with x hx hx'
  exact ⟨hx.trans hu, hx'⟩

variable {R : Type*} [CommRing R]

omit [CompleteSpace E] in
/-- The function `(x, t) ↦ f_x(t)` is holomorphic where the coefficients are. -/
lemma contDiffAt_eval_map (f : R[X]) (ev : E → R →+* ℂ) {x₀ : E}
    (hev : ∀ i, ContDiffAt ℂ ω (fun x ↦ ev x (f.coeff i)) x₀) (t₀ : ℂ) :
    ContDiffAt ℂ ω (fun u : E × ℂ ↦ (f.map (ev u.1)).eval u.2) (x₀, t₀) := by
  have : (fun u : E × ℂ ↦ (f.map (ev u.1)).eval u.2) =
      fun u ↦ ∑ i ∈ Finset.range (f.natDegree + 1), ev u.1 (f.coeff i) * u.2 ^ i := by
    funext u
    rw [eval_map, eval₂_eq_sum_range]
  rw [this]
  exact ContDiffAt.sum fun i _ ↦
    ((hev i).comp (x₀, t₀) contDiffAt_fst).mul (contDiffAt_snd.pow i)

/-- **The holomorphic sheets of `{f = 0}`.** Let `f ∈ R[t]` be monic and `ev : E → (R → ℂ)` a
family of ring maps such that the coefficients `x ↦ ev x (f_i)` of `f_x = f.map (ev x)` are
holomorphic at `x₀`, and suppose `f_{x₀}` is separable. There are functions `φ_r`, one for each
root `r` of `f_{x₀}`, with `φ_r(x₀) = r`, such that near `x₀` they are holomorphic and the roots of
`f_x` are the pairwise distinct values `φ_r(x)`. -/
theorem exists_analytic_sheets {f : R[X]} (hf : f.Monic) (ev : E → R →+* ℂ) {x₀ : E}
    (hev : ∀ i, ContDiffAt ℂ ω (fun x ↦ ev x (f.coeff i)) x₀)
    (hsep : (f.map (ev x₀)).Separable) :
    ∃ φ : ℂ → E → ℂ, (∀ r, φ r x₀ = r) ∧ ∀ᶠ x in 𝓝 x₀,
      (∀ r ∈ (f.map (ev x₀)).roots.toFinset, ContDiffAt ℂ ω (φ r) x) ∧
      Set.InjOn (fun r ↦ φ r x) (f.map (ev x₀)).roots.toFinset ∧
      (f.map (ev x)).roots.toFinset =
        (f.map (ev x₀)).roots.toFinset.image fun r ↦ φ r x := by
  classical
  set R₀ := (f.map (ev x₀)).roots.toFinset
  set F := fun u : E × ℂ ↦ (f.map (ev u.1)).eval u.2
  have hex : ∀ r : ℂ, ∃ ψ : E → ℂ, ψ x₀ = r ∧
      (r ∈ R₀ → ∀ᶠ x in 𝓝 x₀, F (x, ψ x) = 0 ∧ ContDiffAt ℂ ω ψ x) := by
    intro r
    by_cases hr : r ∈ R₀
    · have hroot : (f.map (ev x₀)).eval r = 0 := by
        have := Multiset.mem_toFinset.mp hr
        exact (mem_roots (hf.map _).ne_zero).mp this
      have hder : (f.map (ev x₀)).derivative.eval r ≠ 0 := by
        have := hsep.aeval_derivative_ne_zero (x := r) (by rwa [coe_aeval_eq_eval])
        rwa [coe_aeval_eq_eval] at this
      obtain ⟨ψ, hψ0, hψ⟩ := exists_analytic_implicit_root (u := (x₀, r))
        (contDiffAt_eval_map f ev hev r) hroot
        (by simpa [F] using Polynomial.hasDerivAt (f.map (ev x₀)) r) hder
      exact ⟨ψ, hψ0, fun _ ↦ hψ⟩
    · exact ⟨fun _ ↦ r, rfl, fun h ↦ absurd h hr⟩
  choose φ hφ0 hφ using hex
  refine ⟨φ, hφ0, ?_⟩
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ r ∈ R₀, F (x, φ r x) = 0 ∧ ContDiffAt ℂ ω (φ r) x :=
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
  have hsub : R₀.image (fun r ↦ φ r x) ⊆ (f.map (ev x)).roots.toFinset := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    exact Multiset.mem_toFinset.mpr ((mem_roots (hf.map _).ne_zero).mpr (hx r hr).1)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injOn hInj, SmoothLocusConnected.card_roots_toFinset_of_separable hsep,
    hf.natDegree_map, ← hf.natDegree_map (ev x)]
  exact (Multiset.toFinset_card_le _).trans (card_roots' _)

end MMP.GenericCovering
