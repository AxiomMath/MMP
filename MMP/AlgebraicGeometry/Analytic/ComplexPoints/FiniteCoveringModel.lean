module

public import MMP.Analysis.Complex.FiniteCoveringSheets
public import MMP.Analysis.Complex.LiouvillePolynomialGrowthMv
public import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# The hypersurface model of a finite covering of `ℂⁿ` is connected

Let `f ∈ ℂ[x₁, …, xₙ][t]` be monic and irreducible, and `δ ∈ ℂ[x₁, …, xₙ]` nonzero, such that
`f_x = f(x, ·)` is separable whenever `δ(x) ≠ 0`. Then
`Y = {(x, t) ∈ ℂⁿ × ℂ | δ(x) ≠ 0, f(x, t) = 0}` is connected in the classical topology.

Over `U = {δ ≠ 0}` the projection `Y → U` is a covering with `d = deg f` sheets
(`MMP.SmoothLocusConnected.exists_sheets`). Let `A ⊆ Y` be open and closed. For `x ∈ U` let
`σ_A(x) = ∏ (T - t)`, the product over the roots `t` of `f_x` with `(x, t) ∈ A`. Locally `A` is a
union of sheets, so the coefficients of `σ_A` are holomorphic on `U`; the roots of `f_x` grow at
most polynomially in `x`, hence so do these coefficients; so they are polynomials
(`MMP.exists_mvPolynomial_eq_of_differentiableOn_of_norm_le`). The resulting monic `σ_A ∈ ℂ[x][t]`
divides `f`, so it is `1` or `f`, i.e. `A = ∅` or `A = Y`.

## Main definitions

* `MMP.SmoothLocusConnected.modelHypersurface`: the set `Y`.

## Main results

* `MMP.SmoothLocusConnected.forall_notMem_or_forall_mem`: a relatively clopen
  subset of `Y` is empty or all of `Y`.
* `MMP.SmoothLocusConnected.isPreconnected_modelHypersurface`: `Y` is
  preconnected.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [I. R. Shafarevich, *Basic Algebraic Geometry 2*], Chapter VII, §2.
-/

@[expose] public section

open Polynomial Filter Topology Set

namespace MMP.SmoothLocusConnected

variable {n : ℕ}

/-- Polynomial functions on `ℂⁿ` have polynomial growth. -/
lemma exists_norm_eval_le (P : MvPolynomial (Fin n) ℂ) :
    ∃ C M, 0 ≤ C ∧ ∀ x : Fin n → ℂ, ‖MvPolynomial.eval x P‖ ≤ C * (1 + ‖x‖) ^ M := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, M₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, M₂, hC₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max M₁ M₂, by positivity, fun x ↦ ?_⟩
    have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have e₁ := pow_le_pow_right₀ hx (le_max_left M₁ M₂)
    have e₂ := pow_le_pow_right₀ hx (le_max_right M₁ M₂)
    nlinarith [h₁ x, h₂ x, mul_le_mul_of_nonneg_left e₁ hC₁, mul_le_mul_of_nonneg_left e₂ hC₂]
  | mul_X p i hp =>
    obtain ⟨C, M, hC, h⟩ := hp
    refine ⟨C, M + 1, hC, fun x ↦ ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    have hi : ‖x i‖ ≤ 1 + ‖x‖ := by linarith [norm_le_pi_norm x i]
    exact mul_le_mul (h x) hi (norm_nonneg _) (by positivity)

/-- A polynomial vanishing off a hypersurface `{δ = 0}` is zero. -/
lemma eq_zero_of_eval_eq_zero {δ P : MvPolynomial (Fin n) ℂ} (hδ : δ ≠ 0)
    (h : ∀ x, MvPolynomial.eval x δ ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have := Continuous.ext_on (dense_setOf_eval_ne_zero hδ) (f := fun x ↦ MvPolynomial.eval x P)
    (g := fun _ ↦ 0) (MvPolynomial.continuous_eval P) continuous_const (fun x hx ↦ h x hx)
  exact MvPolynomial.funext fun x ↦ by simpa using congrFun this x

/-- The coefficients of a product of polynomials with holomorphic coefficients are
holomorphic. -/
lemma differentiableAt_coeff_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (I : Finset ι) (P : ι → E → ℂ[X]) {x : E}
    (hP : ∀ i ∈ I, ∀ j, DifferentiableAt ℂ (fun y ↦ (P i y).coeff j) x) (j : ℕ) :
    DifferentiableAt ℂ (fun y ↦ (∏ i ∈ I, P i y).coeff j) x := by
  classical
  induction I using Finset.induction_on generalizing j with
  | empty => simp only [Finset.prod_empty, coeff_one]; exact differentiableAt_const _
  | insert a I ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine DifferentiableAt.fun_sum fun p _ ↦ DifferentiableAt.mul ?_ ?_
    · exact hP a (Finset.mem_insert_self a I) p.1
    · exact ih (fun i hi ↦ hP i (Finset.mem_insert_of_mem hi)) p.2

/-- The coefficients of `X - C (ψ y)` are holomorphic in `y` at any point where `ψ` is. -/
lemma differentiableAt_coeff_X_sub_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ψ : E → ℂ} {x : E} (hψ : DifferentiableAt ℂ ψ x) (j : ℕ) :
    DifferentiableAt ℂ (fun y ↦ (X - C (ψ y)).coeff j) x := by
  simp only [coeff_sub, coeff_X, coeff_C]
  refine (differentiableAt_const _).sub ?_
  split_ifs
  · exact hψ
  · exact differentiableAt_const _

/-- The roots of the specializations `f_x` of a monic `f ∈ ℂ[x][t]` grow at most polynomially
in `x` (Cauchy's bound). -/
lemma exists_norm_root_le {f : (MvPolynomial (Fin n) ℂ)[X]} (hf : f.Monic) :
    ∃ C M, 1 ≤ C ∧ ∀ (x : Fin n → ℂ) (t : ℂ), (f.map (MvPolynomial.eval x)).eval t = 0 →
      ‖t‖ ≤ C * (1 + ‖x‖) ^ M := by
  choose C M hC h using fun i ↦ exists_norm_eval_le (f.coeff i)
  set d := f.natDegree
  refine ⟨∑ i ∈ Finset.range d, C i + 1, ∑ i ∈ Finset.range d, M i,
    by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range d) ↦ hC i], fun x t ht ↦ ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  set p := f.map (MvPolynomial.eval x)
  have hp : p.Monic := hf.map _
  have hlt := IsRoot.norm_lt_cauchyBound hp.ne_zero ht
  have hcb : (cauchyBound p : ℝ) ≤ ∑ i ∈ Finset.range d, ‖MvPolynomial.eval x (f.coeff i)‖ + 1 := by
    rw [cauchyBound, hp.leadingCoeff, nnnorm_one, div_one, hf.natDegree_map]
    push_cast
    gcongr
    have : (Finset.range d).sup (fun i ↦ ‖p.coeff i‖₊) ≤
        ∑ i ∈ Finset.range d, ‖p.coeff i‖₊ :=
      Finset.sup_le fun i hi ↦ Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊)
        (fun _ _ ↦ by simp) hi
    have := NNReal.coe_le_coe.mpr this
    push_cast at this
    simpa only [p, coeff_map] using this
  have hsum : ∑ i ∈ Finset.range d, ‖MvPolynomial.eval x (f.coeff i)‖ ≤
      (∑ i ∈ Finset.range d, C i) * (1 + ‖x‖) ^ (∑ i ∈ Finset.range d, M i) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ (h i x).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx
      (Finset.single_le_sum (f := M) (fun _ _ ↦ Nat.zero_le _) hi)) (hC i)
  have h1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ (∑ i ∈ Finset.range d, M i) := one_le_pow₀ hx
  have : ‖t‖ < (cauchyBound p : ℝ) := by exact_mod_cast hlt
  nlinarith

/-- The coefficients of `∏_{t ∈ S} (T - t)`, for `S` a set of roots of `f_x`, grow at most
polynomially in `x`. -/
lemma exists_norm_coeff_prod_le {f : (MvPolynomial (Fin n) ℂ)[X]} (hf : f.Monic) :
    ∃ K M, ∀ (x : Fin n → ℂ) (S : Finset ℂ), S ⊆ (f.map (MvPolynomial.eval x)).roots.toFinset →
      ∀ j, ‖(∏ t ∈ S, (X - C t)).coeff j‖ ≤ K * (1 + ‖x‖) ^ M := by
  obtain ⟨B, M, hB, h⟩ := exists_norm_root_le hf
  set d := f.natDegree
  refine ⟨B ^ d * d.choose (d / 2), M * d, fun x S hS j ↦ ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hmon : (∏ t ∈ S, (X - C t)).Monic := monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t
  have hdeg : (∏ t ∈ S, (X - C t)).natDegree ≤ d := by
    rw [natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    refine (Finset.card_le_card hS).trans ((Multiset.toFinset_card_le _).trans ?_)
    exact (card_roots' _).trans (hf.natDegree_map _).le
  have hroots : ∀ z ∈ (map (RingHom.id ℂ) (∏ t ∈ S, (X - C t))).roots,
      ‖z‖ ≤ B * (1 + ‖x‖) ^ M := by
    intro z hz
    rw [Polynomial.map_id, roots_prod_X_sub_C] at hz
    have := hS hz
    exact h x z ((mem_roots (hf.map _).ne_zero).mp (Multiset.mem_toFinset.mp this))
  have := coeff_bdd_of_roots_le (RingHom.id ℂ) hmon (IsAlgClosed.splits _) hdeg hroots j
  rw [Polynomial.map_id] at this
  refine this.trans ?_
  have hmax : max (B * (1 + ‖x‖) ^ M) 1 ≤ B * (1 + ‖x‖) ^ M := by
    have : 1 ≤ (1 + ‖x‖) ^ M := one_le_pow₀ hx
    exact max_le le_rfl (by nlinarith)
  rw [pow_mul]
  calc max (B * (1 + ‖x‖) ^ M) 1 ^ d * (d.choose (d / 2) : ℝ)
      ≤ (B * (1 + ‖x‖) ^ M) ^ d * (d.choose (d / 2) : ℝ) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

section Model

variable {f : (MvPolynomial (Fin n) ℂ)[X]} {δ : MvPolynomial (Fin n) ℂ}
  {A : Set ((Fin n → ℂ) × ℂ)}

/-- The hypersurface `{(x, t) | δ(x) ≠ 0, f(x, t) = 0}` of `ℂⁿ × ℂ`. -/
def modelHypersurface (f : (MvPolynomial (Fin n) ℂ)[X]) (δ : MvPolynomial (Fin n) ℂ) :
    Set ((Fin n → ℂ) × ℂ) :=
  {u | MvPolynomial.eval u.1 δ ≠ 0 ∧ (f.map (MvPolynomial.eval u.1)).eval u.2 = 0}

open Classical in
/-- The roots `t` of `f_x` with `(x, t) ∈ A`. -/
noncomputable def rootsIn (f : (MvPolynomial (Fin n) ℂ)[X]) (A : Set ((Fin n → ℂ) × ℂ))
    (x : Fin n → ℂ) : Finset ℂ :=
  (f.map (MvPolynomial.eval x)).roots.toFinset.filter fun t ↦ (x, t) ∈ A

/-- The roots `t` of `f_x` with `(x, t) ∈ A` are roots of `f_x`. -/
lemma rootsIn_subset (x : Fin n → ℂ) :
    rootsIn f A x ⊆ (f.map (MvPolynomial.eval x)).roots.toFinset := by
  classical
  exact Finset.filter_subset _ _

/-- Near a point of `{δ ≠ 0}`, a relatively clopen `A` meets the fibres of the covering in the
values of a fixed set of sheets. -/
lemma exists_eventually_rootsIn_eq (hf : f.Monic)
    (hsep : ∀ x, MvPolynomial.eval x δ ≠ 0 → (f.map (MvPolynomial.eval x)).Separable)
    (hA : ∀ u ∈ modelHypersurface f δ, ∀ᶠ v in 𝓝 u, v ∈ modelHypersurface f δ → (v ∈ A ↔ u ∈ A))
    {x₀ : Fin n → ℂ} (hx₀ : MvPolynomial.eval x₀ δ ≠ 0) :
    ∃ (φ : ℂ → (Fin n → ℂ) → ℂ) (I : Finset ℂ), ∀ᶠ x in 𝓝 x₀,
      (∀ r ∈ I, DifferentiableAt ℂ (φ r) x) ∧ Set.InjOn (fun r ↦ φ r x) I ∧
        rootsIn f A x = I.image fun r ↦ φ r x := by
  classical
  obtain ⟨φ, hφ0, hev⟩ := exists_sheets hf (hsep x₀ hx₀)
  set R₀ := (f.map (MvPolynomial.eval x₀)).roots.toFinset
  refine ⟨φ, R₀.filter fun r ↦ (x₀, r) ∈ A, ?_⟩
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ r ∈ R₀, (x, φ r x) ∈ modelHypersurface f δ →
      ((x, φ r x) ∈ A ↔ (x₀, r) ∈ A) := by
    refine (Filter.eventually_all_finset R₀).mpr fun r hr ↦ ?_
    have hY : (x₀, r) ∈ modelHypersurface f δ :=
      ⟨hx₀, (mem_roots (hf.map _).ne_zero).mp (Multiset.mem_toFinset.mp hr)⟩
    have hc : ContinuousAt (φ r) x₀ := ((hev.self_of_nhds).1 r hr).continuousAt
    have ht : Tendsto (fun x ↦ (x, φ r x)) (𝓝 x₀) (𝓝 (x₀, r)) := by
      have := (continuousAt_id.prodMk hc).tendsto
      rwa [hφ0] at this
    exact ht.eventually (hA _ hY)
  have hU : ∀ᶠ x in 𝓝 x₀, MvPolynomial.eval x δ ≠ 0 :=
    (PolynomialGrowth.isOpen_setOf_eval_ne_zero δ).mem_nhds hx₀
  filter_upwards [hev, hall, hU] with x hx hxA hxU
  obtain ⟨hd, hinj, hroots⟩ := hx
  refine ⟨fun r hr ↦ hd r (Finset.filter_subset _ _ hr), hinj.mono (Finset.filter_subset _ _), ?_⟩
  rw [rootsIn, hroots, Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun r hr ↦ ?_
  have hmem : φ r x ∈ (f.map (MvPolynomial.eval x)).roots.toFinset :=
    hroots ▸ Finset.mem_image_of_mem _ hr
  exact hxA r hr ⟨hxU, (mem_roots (hf.map _).ne_zero).mp (Multiset.mem_toFinset.mp hmem)⟩

/-- **A relatively clopen subset of the model hypersurface is empty or everything.** -/
theorem forall_notMem_or_forall_mem (hf : f.Monic) (hirr : Irreducible f) (hδ : δ ≠ 0)
    (hsep : ∀ x, MvPolynomial.eval x δ ≠ 0 → (f.map (MvPolynomial.eval x)).Separable)
    (hA : ∀ u ∈ modelHypersurface f δ, ∀ᶠ v in 𝓝 u, v ∈ modelHypersurface f δ → (v ∈ A ↔ u ∈ A)) :
    (∀ u ∈ modelHypersurface f δ, u ∉ A) ∨ ∀ u ∈ modelHypersurface f δ, u ∈ A := by
  classical
  set U := {x : Fin n → ℂ | MvPolynomial.eval x δ ≠ 0}
  have hUc : IsPreconnected U := (isPathConnected_setOf_eval_ne_zero hδ).isConnected.isPreconnected
  obtain ⟨x₁, hx₁⟩ := (isPathConnected_setOf_eval_ne_zero hδ).nonempty
  set σ : (Fin n → ℂ) → ℂ[X] := fun x ↦ ∏ t ∈ rootsIn f A x, (X - C t)
  have hσmon : ∀ x, (σ x).Monic := fun x ↦ monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t
  have hσdeg : ∀ x, (σ x).natDegree = (rootsIn f A x).card := fun x ↦ by
    simp only [σ]
    rw [natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t]
    simp
  have hk : ∀ x ∈ U, (rootsIn f A x).card = (rootsIn f A x₁).card := by
    intro x hx
    refine hUc.constant (f := fun x ↦ (rootsIn f A x).card) (fun y hy ↦ ?_) hx hx₁
    obtain ⟨φ, I, hev⟩ := exists_eventually_rootsIn_eq hf hsep hA hy
    have : (fun x ↦ (rootsIn f A x).card) =ᶠ[𝓝 y] fun _ ↦ I.card := by
      filter_upwards [hev] with z hz
      rw [hz.2.2, Finset.card_image_of_injOn hz.2.1]
    exact (continuousAt_const.congr this.symm).continuousWithinAt
  have hσd : ∀ j, DifferentiableOn ℂ (fun x ↦ (σ x).coeff j) U := by
    intro j y hy
    obtain ⟨φ, I, hev⟩ := exists_eventually_rootsIn_eq hf hsep hA hy
    have heq : (fun x ↦ (σ x).coeff j) =ᶠ[𝓝 y]
        fun x ↦ (∏ r ∈ I, (X - C (φ r x))).coeff j := by
      filter_upwards [hev] with z hz
      simp only [σ]
      rw [hz.2.2, Finset.prod_image hz.2.1]
    refine ((differentiableAt_coeff_prod I (fun r x ↦ X - C (φ r x))
      (fun r hr j ↦ differentiableAt_coeff_X_sub_C ((hev.self_of_nhds).1 r hr) j) j).congr_of_eventuallyEq
      heq).differentiableWithinAt
  obtain ⟨K, M, hKM⟩ := exists_norm_coeff_prod_le hf
  have hP := fun j ↦ MMP.exists_mvPolynomial_eq_of_differentiableOn_of_norm_le hδ
    (hσd j) (fun x _ ↦ hKM x _ (rootsIn_subset x) j)
  choose P hP using hP
  set k₀ := (rootsIn f A x₁).card
  set Fσ : (MvPolynomial (Fin n) ℂ)[X] :=
    X ^ k₀ + ∑ i ∈ Finset.range k₀, C (P i) * X ^ i
  have hFm : Fσ.Monic := by
    refine monic_X_pow_add ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ C (P i) * X ^ i) k₀]
    exact degree_sum_fin_lt _
  have hmapF : ∀ x ∈ U, Fσ.map (MvPolynomial.eval x) = σ x := by
    intro x hx
    have h1 := (hσmon x).as_sum
    rw [hσdeg x, hk x hx] at h1
    rw [h1]
    simp only [Fσ, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hP i x hx]
  have hdvd : ∀ x, σ x ∣ f.map (MvPolynomial.eval x) := by
    intro x
    refine (Finset.prod_dvd_prod_of_subset _ _ _ (rootsIn_subset x)).trans ?_
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (f.map (MvPolynomial.eval x)))
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val]
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (Multiset.dedup_le _))
  have hmod : f %ₘ Fσ = 0 := by
    refine Polynomial.ext fun j ↦ ?_
    rw [coeff_zero]
    refine eq_zero_of_eval_eq_zero hδ fun x hx ↦ ?_
    rw [← coeff_map, map_modByMonic _ hFm, hmapF x hx,
      (modByMonic_eq_zero_iff_dvd (hσmon x)).mpr (hdvd x), coeff_zero]
  have hFdeg : Fσ.natDegree = k₀ := by
    rw [← hFm.natDegree_map (MvPolynomial.eval x₁), hmapF x₁ hx₁, hσdeg]
  obtain ⟨q, hq⟩ := (modByMonic_eq_zero_iff_dvd hFm).mp hmod
  have hmemA : ∀ u ∈ modelHypersurface f δ, u ∈ A ↔ u.2 ∈ rootsIn f A u.1 := by
    intro u hu
    rw [rootsIn, Finset.mem_filter, Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero]
    exact ⟨fun h ↦ ⟨hu.2, h⟩, fun h ↦ h.2⟩
  rcases hirr.isUnit_or_isUnit hq with hu | hu
  · left
    have hk0 : k₀ = 0 := hFdeg ▸ natDegree_eq_zero_of_isUnit hu
    intro u hu' huA
    have := (hmemA u hu').mp huA
    rw [Finset.card_eq_zero.mp ((hk u.1 hu'.1).trans hk0)] at this
    exact Finset.notMem_empty _ this
  · right
    have hq0 : q ≠ 0 := hu.ne_zero
    have hkd : k₀ = f.natDegree := by
      rw [hq, natDegree_mul hFm.ne_zero hq0, natDegree_eq_zero_of_isUnit hu, hFdeg, add_zero]
    intro u hu'
    rw [hmemA u hu']
    have hcard : (rootsIn f A u.1).card = (f.map (MvPolynomial.eval u.1)).roots.toFinset.card := by
      rw [hk u.1 hu'.1, hkd, card_roots_toFinset_of_separable (hsep u.1 hu'.1),
        hf.natDegree_map]
    have := Finset.eq_of_subset_of_card_le (rootsIn_subset u.1) hcard.ge
    rw [this, Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero]
    exact hu'.2

/-- **The model hypersurface is connected.** Let `f ∈ ℂ[x₁, …, xₙ][t]` be monic and irreducible,
and `δ ≠ 0` a polynomial such that `f_x` is separable whenever `δ(x) ≠ 0`. Then
`{(x, t) ∈ ℂⁿ × ℂ | δ(x) ≠ 0, f(x, t) = 0}` is preconnected. -/
theorem isPreconnected_modelHypersurface (hf : f.Monic) (hirr : Irreducible f) (hδ : δ ≠ 0)
    (hsep : ∀ x, MvPolynomial.eval x δ ≠ 0 → (f.map (MvPolynomial.eval x)).Separable) :
    IsPreconnected (modelHypersurface f δ) := by
  intro u v hu hv hs ⟨a, haY, hau⟩ ⟨b, hbY, hbv⟩
  by_contra hne
  have hdisj : ∀ w ∈ modelHypersurface f δ, w ∈ u → w ∉ v := fun w hw hwu hwv ↦
    hne ⟨w, hw, hwu, hwv⟩
  have hA : ∀ w ∈ modelHypersurface f δ, ∀ᶠ w' in 𝓝 w, w' ∈ modelHypersurface f δ →
      (w' ∈ u ↔ w ∈ u) := by
    intro w hw
    by_cases hwu : w ∈ u
    · filter_upwards [hu.mem_nhds hwu] with w' hw' _
      exact ⟨fun _ ↦ hwu, fun _ ↦ hw'⟩
    · have hwv : w ∈ v := (hs hw).resolve_left hwu
      filter_upwards [hv.mem_nhds hwv] with w' hw' hw'Y
      exact ⟨fun h ↦ absurd hw' (hdisj w' hw'Y h), fun h ↦ absurd h hwu⟩
  rcases forall_notMem_or_forall_mem hf hirr hδ hsep hA with h | h
  · exact h a haY hau
  · exact hdisj b hbY (h b hbY) hbv

end Model

end MMP.SmoothLocusConnected
