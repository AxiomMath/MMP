module

public import MMP.Analysis.Complex.Dolbeault.DbarLemma

/-!
# Global solvability of `∂̄` on exhaustible domains

Let `D ⊆ ℂⁿ` be open and exhausted by products of compact sets `C₀ ⊆ C₁ ⊆ ⋯`, each in the
interior of the next. Then every `∂̄`-closed smooth `(0, q + 1)`-form `θ` on `D` is `∂̄ u` for a
smooth `(0, q)`-form `u` on `D`, provided, when `q = 0`, that every function holomorphic near
`C_m` is a uniform limit on `C_m` of functions holomorphic on `D` (a Runge property).

By the Dolbeault–Grothendieck lemma, `θ = ∂̄ u_m` near each `C_m`. When `q ≥ 1`, the
difference of two consecutive solutions is closed, hence exact near `C_m`, and subtracting the
`∂̄` of a cut-off primitive makes `u_{m+1} = u_m` near `C_m`; the solutions stabilise. When
`q = 0`, the difference is holomorphic near `C_m`, and subtracting a holomorphic approximant on
`D` makes `|u_{m+1} - u_m| ≤ 2^{-m}` on `C_m`; the solutions converge, with holomorphic
corrections, locally uniformly.

## Main results

* `MMP.Analytic.exists_dbarForm_eq_of_exhaustion`: global solvability of `∂̄`, from
  `MMP.Analytic.exists_dbarForm_eq_of_exhaustion_succ` (degree `≥ 2`) and
  `MMP.Analytic.exists_dbarForm_eq_of_exhaustion_zero` (degree `1`).

## Implementation notes

The one-variable Cauchy transform (`hT`), the regularity of holomorphic functions (`hReg`) and
the holomorphy of locally uniform limits of holomorphic functions (`hLim`) on `ℂⁿ` are
hypotheses, as in `MMP.Analytic.exists_dbarForm_eq_of_dbarForm_eq_zero`.

## References

* [Hörmander, *An introduction to complex analysis in several variables*, Theorem 2.3.3]
-/

@[expose] public section

open Complex Filter Topology Set

open scoped ContDiff

namespace MMP.Analytic

variable {n : ℕ}

section Helpers

/-- The `∂̄` of a form at `z` depends only on the germs of its coefficients at `z`. -/
lemma dbarForm_congr {θ η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (h : ∀ J, θ J =ᶠ[𝓝 z] η J) (I : Finset (Fin n)) :
    dbarForm θ I z = dbarForm η I z :=
  Finset.sum_congr rfl fun j _ => by rw [dbarPartial_congr (h _)]

/-- A product of compact subsets of `ℂ` is compact in `ℂⁿ`. -/
lemma isCompact_setOf_forall_mem {K : Fin n → Set ℂ} (hK : ∀ j, IsCompact (K j)) :
    IsCompact {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j} := by
  have := (isCompact_univ_pi hK).image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ))
  convert this using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ_pi]
  exact ⟨fun h => ⟨WithLp.ofLp z, h, by simp⟩, fun ⟨y, hy, hyz⟩ j => by rw [← hyz]; exact hy j⟩

/-- A function vanishing off a compact subset of an open `N`, smooth on `N`, is smooth. -/
lemma contDiff_of_contDiffOn_of_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℂ} {N Lc : Set F} (hN : IsOpen N) (hLc : IsClosed Lc) (hLcN : Lc ⊆ N)
    (hf : ContDiffOn ℝ ∞ f N) (h0 : ∀ z ∉ Lc, f z = 0) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ N
  · exact hf.contDiffAt (hN.mem_nhds hz)
  · have hev : f =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (hLc.isOpen_compl.mem_nhds fun h => hz (hLcN h)) h0
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The coefficients of a form smooth on an open `V` are real-differentiable at each
point of `V`. -/
lemma differentiableAt_of_forall_contDiffOn {V : Set (EuclideanSpace ℂ (Fin n))} (hV : IsOpen V)
    {u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hu : ∀ I, ContDiffOn ℝ ∞ (u I) V)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ V) (J : Finset (Fin n)) :
    DifferentiableAt ℝ (u J) z :=
  ((hu J).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)

/-- A form concentrated in degree `0` is smooth on `Ω` if its `∅`-coefficient is. -/
lemma contDiffOn_of_contDiffOn_empty {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hη : ∀ J, J ≠ ∅ → η J = 0)
    (hη₀ : ContDiffOn ℝ ∞ (η ∅) Ω) (J : Finset (Fin n)) : ContDiffOn ℝ ∞ (η J) Ω := by
  by_cases hJ : J = ∅
  · subst hJ
    exact hη₀
  · rw [hη J hJ]
    exact contDiffOn_const

/-- The `∂̄` of a form concentrated in degree `0` vanishes where its `∅`-coefficient is
holomorphic. -/
lemma dbarForm_eq_zero_of_differentiableOn {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    {η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hη : ∀ J, J ≠ ∅ → η J = 0)
    (hη₀ : DifferentiableOn ℂ (η ∅) Ω) (I : Finset (Fin n)) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ Ω) : dbarForm η I z = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hJ : I.erase j = ∅
  · rw [hJ, dbarPartial_eq_zero_of_differentiableAt (hη₀.differentiableAt (hΩ.mem_nhds hz)) j,
      mul_zero]
  · rw [hη _ hJ]
    simp [dbarPartial]

/-- A form that, near each point of `D`, agrees with a smooth solution of `∂̄ v = θ` on an open
neighbourhood of that point is a smooth solution of `∂̄ u = θ` on `D`. -/
lemma contDiffOn_and_dbarForm_eq_of_eventuallyEq {D : Set (EuclideanSpace ℂ (Fin n))}
    {θ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (h : ∀ z ∈ D, ∃ V, ∃ v : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ, IsOpen V ∧ z ∈ V ∧
      (∀ I, ContDiffOn ℝ ∞ (v I) V) ∧ (∀ I, ∀ y ∈ V, dbarForm v I y = θ I y) ∧
      ∀ J, u J =ᶠ[𝓝 z] v J) :
    (∀ I, ContDiffOn ℝ ∞ (u I) D) ∧ ∀ I, ∀ z ∈ D, dbarForm u I z = θ I z := by
  refine ⟨fun I z hz => ?_, fun I z hz => ?_⟩ <;>
    obtain ⟨V, v, hV, hzV, hvs, hveq, hev⟩ := h z hz
  · exact (((hvs I).contDiffAt (hV.mem_nhds hzV)).congr_of_eventuallyEq (hev I)).contDiffWithinAt
  · rw [dbarForm_congr hev, hveq I z hzV]

/-- **Telescoping.** If the differences `s (l + 1) - s l` are holomorphic near `C (l + 1)` and
bounded there by `2⁻ˡ`, then on each `C (m + 1)` the limit `s 0 + ∑ₗ (s (l + 1) - s l)` is
`s (m + 1)` plus a function holomorphic on the interior of `C (m + 1)`. -/
theorem exists_eq_add_differentiableOn_of_norm_sub_le {C : ℕ → Set (EuclideanSpace ℂ (Fin n))}
    (hC : Monotone C)
    (hLim : ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))) (F : ℕ → EuclideanSpace ℂ (Fin n) → ℂ)
      (f : EuclideanSpace ℂ (Fin n) → ℂ), IsOpen Ω → (∀ k, DifferentiableOn ℂ (F k) Ω) →
      TendstoLocallyUniformlyOn F f atTop Ω → DifferentiableOn ℂ f Ω)
    {s : ℕ → EuclideanSpace ℂ (Fin n) → ℂ}
    (hhol : ∀ l, ∃ A, IsOpen A ∧ C (l + 1) ⊆ A ∧
      DifferentiableOn ℂ (fun z => s (l + 1) z - s l z) A)
    (hbound : ∀ l, ∀ z ∈ C (l + 1), ‖s (l + 1) z - s l z‖ ≤ (1 / 2 : ℝ) ^ l) :
    ∃ f : EuclideanSpace ℂ (Fin n) → ℂ, ∀ m, ∃ H : EuclideanSpace ℂ (Fin n) → ℂ,
      DifferentiableOn ℂ H (interior (C (m + 1))) ∧ ∀ z ∈ C (m + 1), f z = s (m + 1) z + H z := by
  let dl : ℕ → EuclideanSpace ℂ (Fin n) → ℂ := fun l z => s (l + 1) z - s l z
  have hbd : ∀ m, ∀ z ∈ C (m + 1), ∀ l, ‖dl (l + (m + 1)) z‖ ≤ (1 / 2 : ℝ) ^ l := by
    intro m z hz l
    refine (hbound (l + (m + 1)) z (hC (by omega) hz)).trans ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  refine ⟨fun z => s 0 z + ∑' l, dl l z, fun m =>
    ⟨fun z => ∑' l, dl (l + (m + 1)) z, ?_, fun z hz => ?_⟩⟩
  · refine hLim _ (fun N z => ∑ l ∈ Finset.range N, dl (l + (m + 1)) z) _ isOpen_interior
      (fun N => DifferentiableOn.fun_sum fun l _ => ?_) ?_
    · obtain ⟨A, -, hCA, hA⟩ := hhol (l + (m + 1))
      exact hA.mono (interior_subset.trans ((hC (by omega)).trans hCA))
    · exact ((tendstoUniformlyOn_tsum_nat summable_geometric_two
        fun l z hz => hbd m z hz l).mono interior_subset).tendstoLocallyUniformlyOn
  · have hs : Summable (fun l => dl l z) := (summable_nat_add_iff (m + 1)).1
      (Summable.of_norm_bounded summable_geometric_two (hbd m z hz))
    have htel : ∑ i ∈ Finset.range (m + 1), dl i z = s (m + 1) z - s 0 z :=
      Finset.sum_range_sub (fun l => s l z) (m + 1)
    change s 0 z + ∑' l, dl l z = s (m + 1) z + ∑' l, dl (l + (m + 1)) z
    rw [← hs.sum_add_tsum_nat_add (m + 1), htel]
    ring

/-- **Runge correction.** Two degree-`0` solutions of `∂̄ u = θ`, on `V` and on `V₂ ⊆ D`, differ
by a function holomorphic on `V ∩ V₂`; if it is approximable on `C` by functions holomorphic on
`D`, correcting the second solution makes it `ε`-close to the first on `C`. -/
theorem exists_dbarForm_eq_norm_sub_le_of_runge {D V V₂ C : Set (EuclideanSpace ℂ (Fin n))}
    (hD : IsOpen D) (hV : IsOpen V) (hV₂ : IsOpen V₂) (hV₂D : V₂ ⊆ D) (hCV : C ⊆ V ∩ V₂)
    (hReg : ∀ h : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ h D → ContDiffOn ℝ ∞ h D)
    {ε : ℝ} (hRunge : ∀ h : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ h (V ∩ V₂) →
      ∃ H : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ H D ∧ ∀ z ∈ C, ‖h z - H z‖ < ε)
    {θ u u₂ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hus : ∀ I, ContDiffOn ℝ ∞ (u I) V) (hueq : ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z)
    (hu₂deg : ∀ I : Finset (Fin n), I.card ≠ 0 → u₂ I = 0)
    (hu₂s : ∀ I, ContDiffOn ℝ ∞ (u₂ I) V₂) (hu₂eq : ∀ I, ∀ z ∈ V₂, dbarForm u₂ I z = θ I z) :
    ∃ u' : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ I : Finset (Fin n), I.card ≠ 0 → u' I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u' I) V₂) ∧
      (∀ I, ∀ z ∈ V₂, dbarForm u' I z = θ I z) ∧
      (∃ A, IsOpen A ∧ C ⊆ A ∧ DifferentiableOn ℂ (fun z => u' ∅ z - u ∅ z) A) ∧
      ∀ z ∈ C, ‖u' ∅ z - u ∅ z‖ ≤ ε := by
  have hU : IsOpen (V ∩ V₂) := hV.inter hV₂
  let d : EuclideanSpace ℂ (Fin n) → ℂ := fun z => u₂ ∅ z - u ∅ z
  have hds : ContDiffOn ℝ ∞ d (V ∩ V₂) :=
    ((hu₂s ∅).mono inter_subset_right).sub ((hus ∅).mono inter_subset_left)
  have hdhol : DifferentiableOn ℂ d (V ∩ V₂) := by
    refine (differentiableOn_iff_dbarPartial_eq_zero hU (hds.differentiableOn (by simp))).2
      fun z hz j => ?_
    have h1 := hu₂eq {j} z hz.2
    have h2 := hueq {j} z hz.1
    have hsing : ∀ (η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ)
        (y : EuclideanSpace ℂ (Fin n)), dbarForm η {j} y = dbarPartial j (η ∅) y :=
      fun _ _ => by simp [dbarForm, dolbeaultSign]
    rw [hsing] at h1 h2
    simp only [d]
    rw [dbarPartial_sub (differentiableAt_of_forall_contDiffOn hV₂ hu₂s hz.2 ∅)
      (differentiableAt_of_forall_contDiffOn hV hus hz.1 ∅), h1, h2, sub_self]
  obtain ⟨H, hH, hHa⟩ := hRunge d hdhol
  let Hf : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun J => if J = ∅ then H else 0
  have hHf : ∀ J, J ≠ ∅ → Hf J = 0 := fun J hJ => ite_eq_right hJ
  have hHfs : ∀ J, ContDiffOn ℝ ∞ (Hf J) V₂ := fun J =>
    (contDiffOn_of_contDiffOn_empty hHf (by simpa [Hf] using hReg H hH) J).mono hV₂D
  let u' : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I z => u₂ I z - Hf I z
  have hu'0 : ∀ z, u' ∅ z - u ∅ z = d z - H z := fun z => by
    simp only [u', Hf, d, ite_true]
    ring
  refine ⟨u', fun I hI => ?_, fun I => (hu₂s I).sub (hHfs I), fun I z hz => ?_,
    ⟨V ∩ V₂, hU, hCV, ?_⟩, fun z hz => ?_⟩
  · have hI' : I ≠ ∅ := fun h => hI (by simp [h])
    funext z
    simp [u', Hf, hI', hu₂deg I hI]
  · simp only [u']
    rw [dbarForm_sub (differentiableAt_of_forall_contDiffOn hV₂ hu₂s hz)
      (differentiableAt_of_forall_contDiffOn hV₂ hHfs hz), hu₂eq I z hz,
      dbarForm_eq_zero_of_differentiableOn hD hHf (by simpa [Hf] using hH) I (hV₂D hz), sub_zero]
  · simp only [hu'0]
    exact hdhol.sub (hH.mono (inter_subset_right.trans hV₂D))
  · rw [hu'0]
    exact (hHa z hz).le

end Helpers

section Exhaustion

variable (hT : ∀ (P : Set (Fin n → ℂ)) (L : Set ℂ) (g : ℂ × (Fin n → ℂ) → ℂ),
      IsOpen P → IsCompact L → ContDiffOn ℝ ∞ g (univ ×ˢ P) →
      (∀ ζ ∉ L, ∀ y ∈ P, g (ζ, y) = 0) →
      let u : ℂ × (Fin n → ℂ) → ℂ :=
        fun p => -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, g (ζ, p.2) / (ζ - p.1)
      ContDiffOn ℝ ∞ u (univ ×ˢ P) ∧
      (∀ z : ℂ, ∀ y ∈ P,
        (1 / 2 : ℂ) * (fderiv ℝ (fun w : ℂ => u (w, y)) z 1 +
          Complex.I * fderiv ℝ (fun w : ℂ => u (w, y)) z Complex.I) = g (z, y)) ∧
      (∀ j : Fin n,
        (∀ ζ : ℂ, ∀ y ∈ P, DifferentiableAt ℂ (fun t : ℂ => g (ζ, Function.update y j t)) (y j)) →
        ∀ z : ℂ, ∀ y ∈ P, DifferentiableAt ℂ (fun t : ℂ => u (z, Function.update y j t)) (y j)))

include hT in
/-- **Correction in degree `≥ 1`.** Two solutions of `∂̄ u = θ` in degree `p + 1`, on `V` and on
`V₂`, can be glued: the second, corrected by a `∂̄`-exact form, agrees with the first on a
compact product `C ⊆ V ∩ V₂`. -/
theorem exists_dbarForm_eq_eq_on_of_succ {p : ℕ} {V V₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hV : IsOpen V) (hV₂ : IsOpen V₂) {θ u u₂ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hudeg : ∀ I : Finset (Fin n), I.card ≠ p + 1 → u I = 0) (hus : ∀ I, ContDiffOn ℝ ∞ (u I) V)
    (hueq : ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z)
    (hu₂deg : ∀ I : Finset (Fin n), I.card ≠ p + 1 → u₂ I = 0)
    (hu₂s : ∀ I, ContDiffOn ℝ ∞ (u₂ I) V₂) (hu₂eq : ∀ I, ∀ z ∈ V₂, dbarForm u₂ I z = θ I z)
    {K : Fin n → Set ℂ} (hK : ∀ j, IsCompact (K j))
    (hKV : {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j} ⊆ V ∩ V₂) :
    ∃ u' : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ I : Finset (Fin n), I.card ≠ p + 1 → u' I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u' I) V₂) ∧
      (∀ I, ∀ z ∈ V₂, dbarForm u' I z = θ I z) ∧
      ∀ I, ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j}, u' I z = u I z := by
  let d : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I z => u₂ I z - u I z
  have hds : ∀ I, ContDiffOn ℝ ∞ (d I) (V ∩ V₂) := fun I =>
    ((hu₂s I).mono inter_subset_right).sub ((hus I).mono inter_subset_left)
  have hddeg : ∀ I : Finset (Fin n), I.card ≠ p + 1 → ∀ z ∈ V ∩ V₂, d I z = 0 :=
    fun I hI z _ => by simp [d, hudeg I hI, hu₂deg I hI]
  have hdcl : ∀ I, ∀ z ∈ V ∩ V₂, dbarForm d I z = 0 := by
    intro I z hz
    simp only [d]
    rw [dbarForm_sub (differentiableAt_of_forall_contDiffOn hV₂ hu₂s hz.2)
      (differentiableAt_of_forall_contDiffOn hV hus hz.1), hu₂eq I z hz.2, hueq I z hz.1,
      sub_self]
  obtain ⟨N, hN, hCN, hNU, v, hvdeg, hvs, hveq⟩ :=
    exists_dbarForm_eq_of_dbarForm_eq_zero hT (hV.inter hV₂) hds hddeg hdcl hK hKV
  obtain ⟨ψ, hψs, A, hA, hCA, hAN, hψ1, Lc, hLc, hLcN, hψ0⟩ :=
    exists_contDiff_cutoff (isCompact_setOf_forall_mem hK) hN hCN
  let w : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I z => (ψ z : ℂ) * v I z
  have hws : ∀ I, ContDiff ℝ ∞ (w I) := fun I =>
    contDiff_of_contDiffOn_of_eq_zero hN hLc.isClosed hLcN
      ((ofRealCLM.contDiff.comp hψs).contDiffOn.mul (hvs I)) fun z hz => by
        simp [w, hψ0 z hz]
  let u' : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I z => u₂ I z - dbarForm w I z
  have hwdeg : ∀ I : Finset (Fin n), I.card ≠ p → w I = 0 := fun I hI => by
    funext z
    simp [w, hvdeg I hI]
  refine ⟨u', fun I hI => ?_, fun I => ?_, fun I z hz => ?_, fun I z hz => ?_⟩
  · funext z
    simp [u', hu₂deg I hI, dbarForm_of_degree hwdeg I hI]
  · exact (hu₂s I).sub ((contDiffOn_dbarForm isOpen_univ
      (fun J => (hws J).contDiffOn.of_le top_add_one_le) I).mono (subset_univ _))
  · have hdw : ∀ J, DifferentiableAt ℝ (dbarForm w J) z := fun J =>
      ((contDiffOn_dbarForm isOpen_univ (fun J => (hws J).contDiffOn.of_le top_add_one_le)
        J).contDiffAt univ_mem).differentiableAt (by simp)
    simp only [u']
    rw [dbarForm_sub (differentiableAt_of_forall_contDiffOn hV₂ hu₂s hz) hdw, hu₂eq I z hz,
      dbarForm_dbarForm isOpen_univ (fun J => (hws J).contDiffOn.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) I (mem_univ z), sub_zero]
  · have hzA := hCA hz
    have hev : ∀ J, w J =ᶠ[𝓝 z] v J := fun J =>
      Filter.eventually_of_mem (hA.mem_nhds hzA) fun y hy => by simp [w, hψ1 y hy]
    simp only [u']
    rw [dbarForm_congr hev, hveq I z (hAN hzA)]
    simp [d]

include hT in
/-- **`∂̄` on an exhausted domain, degree `≥ 2`.** If `D` is exhausted by compact products, each
in the interior of the next, every `∂̄`-closed smooth `(0, p + 2)`-form on `D` is `∂̄ u` for a
smooth `(0, p + 1)`-form `u` on `D`. -/
theorem exists_dbarForm_eq_of_exhaustion_succ {D : Set (EuclideanSpace ℂ (Fin n))}
    (hD : IsOpen D) (K : ℕ → Fin n → Set ℂ) (hK : ∀ m j, IsCompact (K m j))
    (hKD : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ D)
    (hKK : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆
      interior {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K (m + 1) j})
    (hcov : ∀ z ∈ D, ∃ m, ∀ j, z j ∈ K m j) (p : ℕ)
    {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hθ : ∀ I, ContDiffOn ℝ ∞ (θ I) D)
    (hdeg : ∀ I : Finset (Fin n), I.card ≠ p + 2 → ∀ z ∈ D, θ I z = 0)
    (hcl : ∀ I, ∀ z ∈ D, dbarForm θ I z = 0) :
    ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ I : Finset (Fin n), I.card ≠ p + 1 → u I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u I) D) ∧
      ∀ I, ∀ z ∈ D, dbarForm u I z = θ I z := by
  set C : ℕ → Set (EuclideanSpace ℂ (Fin n)) :=
    fun m => {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j}
  have hCsucc : ∀ m, C m ⊆ C (m + 1) := fun m => (hKK m).trans interior_subset
  have hCmono : Monotone C := monotone_nat_of_le_succ hCsucc
  have LL : ∀ m, ∃ V, IsOpen V ∧ C m ⊆ V ∧ V ⊆ D ∧
      ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
        (∀ I : Finset (Fin n), I.card ≠ p + 1 → u I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u I) V) ∧
        ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z := fun m =>
    exists_dbarForm_eq_of_dbarForm_eq_zero hT hD hθ hdeg hcl (hK m) (hKD m)
  let Good : ℕ → (Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) → Prop := fun m u =>
    (∀ I : Finset (Fin n), I.card ≠ p + 1 → u I = 0) ∧ ∃ V, IsOpen V ∧ C (m + 1) ⊆ V ∧ V ⊆ D ∧
      (∀ I, ContDiffOn ℝ ∞ (u I) V) ∧ ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z
  have step : ∀ m u, Good m u → ∃ u', Good (m + 1) u' ∧ ∀ I, ∀ z ∈ C (m + 1), u' I z = u I z := by
    rintro m u ⟨hudeg, V, hV, hCV, -, hus, hueq⟩
    obtain ⟨V₂, hV₂, hCV₂, hV₂D, u₂, hu₂deg, hu₂s, hu₂eq⟩ := LL (m + 2)
    obtain ⟨u', hu'deg, hu's, hu'eq, hu'⟩ := exists_dbarForm_eq_eq_on_of_succ hT hV hV₂ hudeg hus
      hueq hu₂deg hu₂s hu₂eq (hK (m + 1)) (subset_inter hCV ((hCsucc (m + 1)).trans hCV₂))
    exact ⟨u', ⟨hu'deg, V₂, hV₂, hCV₂, hV₂D, hu's, hu'eq⟩, hu'⟩
  obtain ⟨V₀, hV₀, hCV₀, hV₀D, u₀, hu₀deg, hu₀s, hu₀eq⟩ := LL 1
  have hu₀ : Good 0 u₀ := ⟨hu₀deg, V₀, hV₀, hCV₀, hV₀D, hu₀s, hu₀eq⟩
  choose next hnext hagree using step
  let seq : ∀ m, {u // Good m u} := fun m =>
    Nat.rec ⟨u₀, hu₀⟩ (fun m s => ⟨next m s.1 s.2, hnext m s.1 s.2⟩) m
  have hstab : ∀ a b, a ≤ b → ∀ I, ∀ z ∈ C a, (seq b).1 I z = (seq a).1 I z := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun _ _ _ => rfl
    | succ b hab ih =>
      exact fun I z hz => (hagree b _ (seq b).2 I z (hCmono (by omega) hz)).trans (ih I z hz)
  classical
  let mz : EuclideanSpace ℂ (Fin n) → ℕ := fun z => if h : ∃ m, z ∈ C m then Nat.find h else 0
  let u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I z => (seq (mz z)).1 I z
  have hu_eq : ∀ m, ∀ I, ∀ z ∈ C m, u I z = (seq m).1 I z := fun m I z hz => by
    have h : ∃ m, z ∈ C m := ⟨m, hz⟩
    have hmz : mz z = Nat.find h := dite_eq_left h
    simp only [u]
    rw [hmz, hstab (Nat.find h) m (Nat.find_min' h hz) I z (Nat.find_spec h)]
  refine ⟨u, fun I hI => funext fun z => (seq (mz z)).2.1 I hI ▸ rfl,
    contDiffOn_and_dbarForm_eq_of_eventuallyEq fun z hz => ?_⟩
  obtain ⟨m, hm⟩ := hcov z hz
  obtain ⟨-, V, hV, hCV, -, hus, hueq⟩ := (seq (m + 1)).2
  exact ⟨V, _, hV, hCV (hCsucc _ (hCsucc m hm)), hus, hueq, fun J => Filter.eventually_of_mem
    (isOpen_interior.mem_nhds (hKK m hm)) fun y hy => hu_eq (m + 1) J y (interior_subset hy)⟩

include hT in
/-- **`∂̄` on an exhausted domain, degree `1`.** Here the exhaustion is assumed to have the Runge
property `hRunge`. -/
theorem exists_dbarForm_eq_of_exhaustion_zero {D : Set (EuclideanSpace ℂ (Fin n))}
    (hD : IsOpen D) (K : ℕ → Fin n → Set ℂ) (hK : ∀ m j, IsCompact (K m j))
    (hKD : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ D)
    (hKK : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆
      interior {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K (m + 1) j})
    (hcov : ∀ z ∈ D, ∃ m, ∀ j, z j ∈ K m j)
    (hReg : ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))) (h : EuclideanSpace ℂ (Fin n) → ℂ),
      IsOpen Ω → DifferentiableOn ℂ h Ω → ContDiffOn ℝ ∞ h Ω)
    (hLim : ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))) (F : ℕ → EuclideanSpace ℂ (Fin n) → ℂ)
      (f : EuclideanSpace ℂ (Fin n) → ℂ), IsOpen Ω → (∀ k, DifferentiableOn ℂ (F k) Ω) →
      TendstoLocallyUniformlyOn F f atTop Ω → DifferentiableOn ℂ f Ω)
    (hRunge : ∀ (m : ℕ) (V : Set (EuclideanSpace ℂ (Fin n))) (h : EuclideanSpace ℂ (Fin n) → ℂ),
      IsOpen V → {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ V →
      DifferentiableOn ℂ h V → ∀ ε : ℝ, 0 < ε → ∃ H : EuclideanSpace ℂ (Fin n) → ℂ,
        DifferentiableOn ℂ H D ∧ ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j},
          ‖h z - H z‖ < ε)
    {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} (hθ : ∀ I, ContDiffOn ℝ ∞ (θ I) D)
    (hdeg : ∀ I : Finset (Fin n), I.card ≠ 0 + 1 → ∀ z ∈ D, θ I z = 0)
    (hcl : ∀ I, ∀ z ∈ D, dbarForm θ I z = 0) :
    ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ I : Finset (Fin n), I.card ≠ 0 → u I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u I) D) ∧
      ∀ I, ∀ z ∈ D, dbarForm u I z = θ I z := by
  set C : ℕ → Set (EuclideanSpace ℂ (Fin n)) :=
    fun m => {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j}
  have hCsucc : ∀ m, C m ⊆ C (m + 1) := fun m => (hKK m).trans interior_subset
  let Good : ℕ → (Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) → Prop := fun m u =>
    (∀ I : Finset (Fin n), I.card ≠ 0 → u I = 0) ∧ ∃ V, IsOpen V ∧ C (m + 1) ⊆ V ∧ V ⊆ D ∧
      (∀ I, ContDiffOn ℝ ∞ (u I) V) ∧ ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z
  have step : ∀ m u, Good m u → ∃ u', Good (m + 1) u' ∧ (∃ A, IsOpen A ∧ C (m + 1) ⊆ A ∧
      DifferentiableOn ℂ (fun z => u' ∅ z - u ∅ z) A) ∧
      ∀ z ∈ C (m + 1), ‖u' ∅ z - u ∅ z‖ ≤ (1 / 2 : ℝ) ^ m := by
    rintro m u ⟨-, V, hV, hCV, -, hus, hueq⟩
    obtain ⟨V₂, hV₂, hCV₂, hV₂D, u₂, hu₂deg, hu₂s, hu₂eq⟩ :=
      exists_dbarForm_eq_of_dbarForm_eq_zero hT hD hθ hdeg hcl (hK (m + 2)) (hKD _)
    have hCV' : C (m + 1) ⊆ V ∩ V₂ := subset_inter hCV ((hCsucc (m + 1)).trans hCV₂)
    obtain ⟨u', hu'deg, hu's, hu'eq, hhol, hle⟩ := exists_dbarForm_eq_norm_sub_le_of_runge hD hV
      hV₂ hV₂D hCV' (fun h hh => hReg D h hD hh) (ε := (1 / 2 : ℝ) ^ m)
      (fun h hh => hRunge (m + 1) _ h (hV.inter hV₂) hCV' hh _ (by positivity))
      hus hueq hu₂deg hu₂s hu₂eq
    exact ⟨u', ⟨hu'deg, V₂, hV₂, hCV₂, hV₂D, hu's, hu'eq⟩, hhol, hle⟩
  obtain ⟨V₀, hV₀, hCV₀, hV₀D, u₀, hu₀deg, hu₀s, hu₀eq⟩ :=
    exists_dbarForm_eq_of_dbarForm_eq_zero hT hD hθ hdeg hcl (hK 1) (hKD 1)
  have hu₀ : Good 0 u₀ := ⟨hu₀deg, V₀, hV₀, hCV₀, hV₀D, hu₀s, hu₀eq⟩
  choose next hnext hhol hbound using step
  let seq : ∀ m, {u // Good m u} := fun m =>
    Nat.rec ⟨u₀, hu₀⟩ (fun m s => ⟨next m s.1 s.2, hnext m s.1 s.2⟩) m
  obtain ⟨f, hf⟩ := exists_eq_add_differentiableOn_of_norm_sub_le
    (monotone_nat_of_le_succ hCsucc) hLim (s := fun l => (seq l).1 ∅)
    (fun l => hhol l (seq l).1 (seq l).2) fun l => hbound l (seq l).1 (seq l).2
  choose Hm hHm_hol hf_eq using hf
  refine ⟨fun J => if J = ∅ then f else 0, fun I hI => ite_eq_right fun h => hI (by simp [h]),
    contDiffOn_and_dbarForm_eq_of_eventuallyEq fun z hz => ?_⟩
  obtain ⟨m, hm⟩ := hcov z hz
  obtain ⟨-, V, hV, hCV, -, hus, hueq⟩ := (seq (m + 1)).2
  let Hf : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun J => if J = ∅ then Hm m else 0
  have hHf : ∀ J, J ≠ ∅ → Hf J = 0 := fun J hJ => ite_eq_right hJ
  have hHfs : ∀ J, ContDiffOn ℝ ∞ (Hf J) (interior (C (m + 1))) := contDiffOn_of_contDiffOn_empty
    hHf (by simpa [Hf] using hReg _ _ isOpen_interior (hHm_hol m))
  refine ⟨V ∩ interior (C (m + 1)), fun J w => (seq (m + 1)).1 J w + Hf J w,
    hV.inter isOpen_interior, ⟨hCV (hCsucc _ (hCsucc m hm)), hKK m hm⟩,
    fun I => ((hus I).mono inter_subset_left).add ((hHfs I).mono inter_subset_right),
    fun I y hy => ?_, fun J => ?_⟩
  · rw [dbarForm_add (differentiableAt_of_forall_contDiffOn hV hus hy.1)
      (differentiableAt_of_forall_contDiffOn isOpen_interior hHfs hy.2), hueq I y hy.1,
      dbarForm_eq_zero_of_differentiableOn isOpen_interior hHf (by simpa [Hf] using hHm_hol m) I
        hy.2, add_zero]
  · refine Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKK m hm)) fun y hy => ?_
    rcases eq_or_ne J ∅ with rfl | hJ
    · simpa [Hf] using hf_eq m y (interior_subset hy)
    · simp [Hf, hJ, (seq (m + 1)).2.1 J fun h => hJ (Finset.card_eq_zero.1 h)]

include hT in
/-- **Global solvability of `∂̄` on an exhausted domain.** If `D ⊆ ℂⁿ` is exhausted by products of
compact sets `C_m ⊆ int C_{m+1}` with the Runge property, every `∂̄`-closed smooth
`(0, q + 1)`-form on `D` is `∂̄ u` for a smooth `(0, q)`-form `u` on `D`. -/
theorem exists_dbarForm_eq_of_exhaustion {D : Set (EuclideanSpace ℂ (Fin n))}
    (hD : IsOpen D) (K : ℕ → Fin n → Set ℂ) (hK : ∀ m j, IsCompact (K m j))
    (hKD : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ D)
    (hKK : ∀ m, {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆
      interior {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K (m + 1) j})
    (hcov : ∀ z ∈ D, ∃ m, ∀ j, z j ∈ K m j)
    (hReg : ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))) (h : EuclideanSpace ℂ (Fin n) → ℂ),
      IsOpen Ω → DifferentiableOn ℂ h Ω → ContDiffOn ℝ ∞ h Ω)
    (hLim : ∀ (Ω : Set (EuclideanSpace ℂ (Fin n))) (F : ℕ → EuclideanSpace ℂ (Fin n) → ℂ)
      (f : EuclideanSpace ℂ (Fin n) → ℂ), IsOpen Ω → (∀ k, DifferentiableOn ℂ (F k) Ω) →
      TendstoLocallyUniformlyOn F f atTop Ω → DifferentiableOn ℂ f Ω)
    (hRunge : ∀ (m : ℕ) (V : Set (EuclideanSpace ℂ (Fin n))) (h : EuclideanSpace ℂ (Fin n) → ℂ),
      IsOpen V → {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j} ⊆ V →
      DifferentiableOn ℂ h V → ∀ ε : ℝ, 0 < ε → ∃ H : EuclideanSpace ℂ (Fin n) → ℂ,
        DifferentiableOn ℂ H D ∧ ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K m j},
          ‖h z - H z‖ < ε)
    (q : ℕ) {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hθ : ∀ I, ContDiffOn ℝ ∞ (θ I) D)
    (hdeg : ∀ I : Finset (Fin n), I.card ≠ q + 1 → ∀ z ∈ D, θ I z = 0)
    (hcl : ∀ I, ∀ z ∈ D, dbarForm θ I z = 0) :
    ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
      (∀ I : Finset (Fin n), I.card ≠ q → u I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u I) D) ∧
      ∀ I, ∀ z ∈ D, dbarForm u I z = θ I z := by
  cases q with
  | zero =>
    exact exists_dbarForm_eq_of_exhaustion_zero hT hD K hK hKD hKK hcov hReg hLim hRunge hθ hdeg
      hcl
  | succ p =>
    exact exists_dbarForm_eq_of_exhaustion_succ hT hD K hK hKD hKK hcov p hθ hdeg hcl

end Exhaustion

end MMP.Analytic
