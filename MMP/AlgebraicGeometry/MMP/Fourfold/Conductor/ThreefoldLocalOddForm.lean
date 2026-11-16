module
public import MMP.AlgebraicGeometry.Analytic.DegreeOneHodgeDecomposition
public import MMP.AlgebraicGeometry.Chow.FirstChernClassTopAdditive
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate

/-!
# thm mmp conductor threefold local odd form

Chain fold of: `thm_mmp_conductor_threefold_local_odd_form`.
-/

/-! ### `thm_mmp_conductor_threefold_local_odd_form` -/

open CategoryTheory Opposite Simplicial AlgebraicGeometry MMP
  MMP.BorelMooreCross MMP.BorelMooreCap MMP.BorelMooreCap
  MMP.LocallyFiniteChain MMP.SingularChain MMP.SingularChain
  MMP.SingularCochain MMP.SingularCochain MMP.Mori MMP.Fourfold
open scoped MMP.SubschemeOver

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Fold06.ThmMmpConductorThreefoldLocalOddForm

/-! ### Linear algebra -/

section LinearAlgebra

private theorem bijective_of_pairing {V H K : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup H] [Module ℚ H] [AddCommGroup K] [Module ℚ K] [FiniteDimensional ℚ K]
    (T : V →ₗ[ℚ] H) (δ : V →ₗ[ℚ] K) (hδ : Function.Bijective δ) (P : H →ₗ[ℚ] K →ₗ[ℚ] ℚ)
    (hP : ∀ h, (∀ b, P h b = 0) → h = 0)
    (hI : ∀ v, (∀ v', P (T v) (δ v') = 0) → v = 0) : Function.Bijective T := by
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hI v fun v' ↦ by rw [hv, map_zero, LinearMap.zero_apply]
  have hPinj : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    exact hP h fun b ↦ by rw [hh, LinearMap.zero_apply]
  let e : V ≃ₗ[ℚ] K := LinearEquiv.ofBijective δ hδ
  haveI : FiniteDimensional ℚ V := LinearEquiv.finiteDimensional e.symm
  haveI : FiniteDimensional ℚ H := Module.Finite.of_injective P hPinj
  have h1 : Module.finrank ℚ H ≤ Module.finrank ℚ V :=
    calc Module.finrank ℚ H ≤ Module.finrank ℚ (K →ₗ[ℚ] ℚ) := LinearMap.finrank_le_finrank_of_injective hPinj
      _ = Module.finrank ℚ K := Subspace.dual_finrank_eq
      _ = Module.finrank ℚ V := e.finrank_eq.symm
  exact ⟨hTinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hTinj) h1)).1 hTinj⟩

/-- **Descent of nondegeneracy from a complexification.** Let `κ : V → V_ℂ` be an injective
`ℚ`-linear map whose image spans `V_ℂ` over `ℂ`, and let the `ℚ`-bilinear form `I` on `V` be the
restriction of a `ℂ`-bilinear form `B` on `V_ℂ`. If `B` has trivial left radical, so has `I`. -/
private theorem eq_zero_of_complexification {V VC : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VC] [Module ℂ VC] (κ : V →+ VC) (hκ : Function.Injective κ)
    (hspan : Submodule.span ℂ (Set.range κ) = ⊤) (B : VC →ₗ[ℂ] VC →ₗ[ℂ] ℂ) (I : V → V → ℚ)
    (hBI : ∀ u v, B (κ u) (κ v) = (I u v : ℂ))
    (hB : ∀ w, (∀ w', B w w' = 0) → w = 0) (u : V) (hu : ∀ v, I u v = 0) : u = 0 := by
  have h : ∀ w' ∈ Submodule.span ℂ (Set.range κ), B (κ u) w' = 0 := fun w' hw' ↦ by
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [hBI, hu, Rat.cast_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have h0 : κ u = 0 := hB _ fun w' ↦ h w' (hspan ▸ Submodule.mem_top)
  exact hκ (h0.trans (map_zero κ).symm)

/-- **The Hodge–Riemann argument for a sum of polarized pieces.** Let `H_P` and `G_k` be complex
vector spaces with conjugations, holomorphic subspaces `Hol` with `H_P = Hol ⊕ \overline{Hol}`,
forms `σ_P` and `θ_k` compatible with conjugation which vanish on pairs of holomorphic classes,
with `i σ_P(h, h̄) > 0` for `h ≠ 0` and `i θ_k(g, ḡ) ≥ 0` for holomorphic `h`, `g`, and restriction
maps `ρ_k, ρ'_k` compatible with all the structure. Then for positive weights `m`, the form
```
∑_P m_P σ_P(w_P, w'_P)
  + ∑_k m_{p k} m_{q k} θ_k(ρ_k w_{p k} - ρ'_k w_{q k}, ρ_k w'_{p k} - ρ'_k w'_{q k})
```
has trivial left radical. -/
private theorem eq_zero_of_hodgeData {ι K : Type*} [Fintype ι] [Fintype K]
    (H : ι → Type*) [∀ P, AddCommGroup (H P)] [∀ P, Module ℂ (H P)]
    (G : K → Type*) [∀ k, AddCommGroup (G k)] [∀ k, Module ℂ (G k)]
    (cH : ∀ P, H P →+ H P) (cG : ∀ k, G k →+ G k)
    (hcH : ∀ P a, cH P (cH P a) = a) (hcG : ∀ k a, cG k (cG k a) = a)
    (HolH : ∀ P, Submodule ℂ (H P)) (HolG : ∀ k, Submodule ℂ (G k))
    (hdec : ∀ P (a : H P), ∃ h ∈ HolH P, ∃ h' ∈ HolH P, a = h + cH P h')
    (m : ι → ℝ) (hm : ∀ P, 0 < m P)
    (σ : ∀ P, H P →ₗ[ℂ] H P →ₗ[ℂ] ℂ)
    (hσc : ∀ P a b, σ P (cH P a) (cH P b) = starRingEnd ℂ (σ P a b))
    (hσHH : ∀ P, ∀ h ∈ HolH P, ∀ h' ∈ HolH P, σ P h h' = 0)
    (hσpos : ∀ P, ∀ h ∈ HolH P, h ≠ 0 → ∃ t : ℝ, 0 < t ∧ Complex.I * σ P h (cH P h) = t)
    (p q : K → ι) (ρ : ∀ k, H (p k) →ₗ[ℂ] G k) (ρ' : ∀ k, H (q k) →ₗ[ℂ] G k)
    (hρc : ∀ k a, ρ k (cH (p k) a) = cG k (ρ k a))
    (hρ'c : ∀ k a, ρ' k (cH (q k) a) = cG k (ρ' k a))
    (hρhol : ∀ k, ∀ h ∈ HolH (p k), ρ k h ∈ HolG k)
    (hρ'hol : ∀ k, ∀ h ∈ HolH (q k), ρ' k h ∈ HolG k)
    (wt : K → ℝ) (hwt : ∀ k, 0 ≤ wt k)
    (θ : ∀ k, G k →ₗ[ℂ] G k →ₗ[ℂ] ℂ)
    (hθc : ∀ k a b, θ k (cG k a) (cG k b) = starRingEnd ℂ (θ k a b))
    (hθHH : ∀ k, ∀ g ∈ HolG k, ∀ g' ∈ HolG k, θ k g g' = 0)
    (hθpos : ∀ k, ∀ g ∈ HolG k, ∃ t : ℝ, 0 ≤ t ∧ Complex.I * θ k g (cG k g) = t)
    (w : ∀ P, H P)
    (hw : ∀ w' : ∀ P, H P, (∑ P, (m P : ℂ) * σ P (w P) (w' P) +
      ∑ k, ((wt k : ℝ) : ℂ) * θ k (ρ k (w (p k)) - ρ' k (w (q k)))
        (ρ k (w' (p k)) - ρ' k (w' (q k)))) = 0) : w = 0 := by
  classical
  -- the form, bilinearly
  let B : (∀ P, H P) →ₗ[ℂ] (∀ P, H P) →ₗ[ℂ] ℂ :=
    ∑ P, (m P : ℂ) • (σ P).compl₁₂ (LinearMap.proj P) (LinearMap.proj P) +
    ∑ k, ((wt k : ℝ) : ℂ) • (θ k).compl₁₂
      (ρ k ∘ₗ LinearMap.proj (p k) - ρ' k ∘ₗ LinearMap.proj (q k))
      (ρ k ∘ₗ LinearMap.proj (p k) - ρ' k ∘ₗ LinearMap.proj (q k))
  have hB : ∀ x y, B x y = ∑ P, (m P : ℂ) * σ P (x P) (y P) +
      ∑ k, ((wt k : ℝ) : ℂ) * θ k (ρ k (x (p k)) - ρ' k (x (q k)))
        (ρ k (y (p k)) - ρ' k (y (q k))) := fun x y ↦ by
    simp [B, LinearMap.sum_apply, smul_eq_mul]
  let c : (∀ P, H P) →+ (∀ P, H P) := Pi.addMonoidHom fun P ↦ (cH P).comp (Pi.evalAddMonoidHom H P)
  have hc : ∀ x P, c x P = cH P (x P) := fun _ _ ↦ rfl
  -- conjugation compatibility of the form
  have hBc : ∀ x y, B (c x) (c y) = starRingEnd ℂ (B x y) := fun x y ↦ by
    rw [hB, hB, map_add, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun P _ ↦ ?_
      rw [hc, hc, hσc, map_mul, Complex.conj_ofReal]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hc, hc, hc, hc, hρc, hρ'c, hρc, hρ'c, ← map_sub, ← map_sub, hθc, map_mul,
        Complex.conj_ofReal]
  set Hol : Set (∀ P, H P) := {x | ∀ P, x P ∈ HolH P}
  have hHH : ∀ x ∈ Hol, ∀ y ∈ Hol, B x y = 0 := fun x hx y hy ↦ by
    rw [hB, Finset.sum_eq_zero fun P _ ↦ by rw [hσHH P _ (hx P) _ (hy P), mul_zero],
      Finset.sum_eq_zero fun k _ ↦ by
        rw [hθHH k _ (sub_mem (hρhol k _ (hx _)) (hρ'hol k _ (hx _))) _
          (sub_mem (hρhol k _ (hy _)) (hρ'hol k _ (hy _))), mul_zero], add_zero]
  have hpos : ∀ x ∈ Hol, B x (c x) = 0 → x = 0 := fun x hx h0 ↦ by
    have hr : ∀ P, ∃ r : ℝ, 0 ≤ r ∧ Complex.I * σ P (x P) (cH P (x P)) = r ∧ (x P ≠ 0 → 0 < r) :=
      fun P ↦ by
        by_cases h : x P = 0
        · exact ⟨0, le_rfl, by rw [h]; simp, fun h' ↦ absurd h h'⟩
        · obtain ⟨t, ht, ht'⟩ := hσpos P _ (hx P) h
          exact ⟨t, ht.le, ht', fun _ ↦ ht⟩
    choose r hr0 hrσ hrpos using hr
    have hs : ∀ k, ∃ s : ℝ, 0 ≤ s ∧ Complex.I * θ k (ρ k (x (p k)) - ρ' k (x (q k)))
        (cG k (ρ k (x (p k)) - ρ' k (x (q k)))) = s := fun k ↦
      hθpos k _ (sub_mem (hρhol k _ (hx _)) (hρ'hol k _ (hx _)))
    choose s hs0 hsθ using hs
    have hsum : ((∑ P, m P * r P + ∑ k, wt k * s k : ℝ) : ℂ) = 0 := by
      have := congrArg (fun z ↦ Complex.I * z) h0
      simp only [mul_zero, hB, mul_add, Finset.mul_sum] at this
      push_cast
      rw [← this]
      congr 1
      · refine Finset.sum_congr rfl fun P _ ↦ ?_
        rw [hc, ← hrσ]; ring
      · refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hc, hc, hρc, hρ'c, ← map_sub, ← hsθ]; push_cast; ring
    have hsum' : ∑ P, m P * r P + ∑ k, wt k * s k = 0 := by exact_mod_cast hsum
    have h1 : 0 ≤ ∑ P, m P * r P :=
      Finset.sum_nonneg fun P _ ↦ mul_nonneg (hm P).le (hr0 P)
    have h2 : 0 ≤ ∑ k, wt k * s k :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (hwt k) (hs0 k)
    have h3 : ∑ P, m P * r P = 0 := by linarith
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun P _ ↦ mul_nonneg (hm P).le (hr0 P)).1 h3
    funext P
    by_contra hP
    have := h4 P (Finset.mem_univ _)
    have := mul_pos (hm P) (hrpos P hP)
    linarith
  -- decompose `w`
  choose h hh h' hh' hw' using hdec
  have hwdec : w = (fun P ↦ h P (w P)) + c (fun P ↦ h' P (w P)) := funext fun P ↦ hw' P (w P)
  set u : ∀ P, H P := fun P ↦ h P (w P)
  set u' : ∀ P, H P := fun P ↦ h' P (w P)
  have hu : u ∈ Hol := fun P ↦ hh P _
  have hu' : u' ∈ Hol := fun P ↦ hh' P _
  have hwB : ∀ y, B w y = 0 := fun y ↦ (hB w y).trans (hw y)
  have hcc : ∀ x, c (c x) = x := fun x ↦ funext fun P ↦ hcH P (x P)
  have e1 : B u (c u) = 0 := by
    have := hwB (c u)
    rw [hwdec, map_add, LinearMap.add_apply, hBc, hHH u' hu' u hu, map_zero, add_zero] at this
    exact this
  have hu0 := hpos u hu e1
  have e2 : B u' (c u') = 0 := by
    have := hwB u'
    rw [hwdec, hu0, map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply, zero_add] at this
    have h5 : B (c u') u' = starRingEnd ℂ (B u' (c u')) := by
      have := hBc u' (c u')
      rwa [hcc] at this
    rw [h5] at this
    simpa using this
  have hu'0 := hpos u' hu' e2
  rw [hwdec]
  change u + c u' = 0
  rw [hu0, hu'0, map_zero, add_zero]

/-- **Descent of the Hodge–Riemann argument to `ℚ`.** Let the complex spaces of
`eq_zero_of_hodgeData` carry rational structures `κ_P : V_P → H_P`, `G_k^ℚ → G_k`, injective with
spanning images, for which the forms and restriction maps are defined over `ℚ`. Then the rational
form `∑_P m_P σ_P^ℚ + ∑_k w_k θ_k^ℚ(ρ - ρ', ρ - ρ')` has trivial left radical. -/
private theorem eq_zero_of_hodgeData_rat {ι K : Type*} [Fintype ι] [Fintype K]
    (H : ι → Type*) [∀ P, AddCommGroup (H P)] [∀ P, Module ℂ (H P)]
    (G : K → Type*) [∀ k, AddCommGroup (G k)] [∀ k, Module ℂ (G k)]
    (Vq : ι → Type*) [∀ P, AddCommGroup (Vq P)] [∀ P, Module ℚ (Vq P)]
    (Gq : K → Type*) [∀ k, AddCommGroup (Gq k)] [∀ k, Module ℚ (Gq k)]
    (κ : ∀ P, Vq P →+ H P) (hκ : ∀ P, Function.Injective (κ P))
    (hspan : ∀ P, Submodule.span ℂ (Set.range (κ P)) = ⊤)
    (κG : ∀ k, Gq k →+ G k)
    (cH : ∀ P, H P →+ H P) (cG : ∀ k, G k →+ G k)
    (hcH : ∀ P a, cH P (cH P a) = a) (hcG : ∀ k a, cG k (cG k a) = a)
    (HolH : ∀ P, Submodule ℂ (H P)) (HolG : ∀ k, Submodule ℂ (G k))
    (hdec : ∀ P (a : H P), ∃ h ∈ HolH P, ∃ h' ∈ HolH P, a = h + cH P h')
    (m : ι → ℚ) (hm : ∀ P, 0 < m P)
    (σ : ∀ P, H P →ₗ[ℂ] H P →ₗ[ℂ] ℂ) (σq : ∀ P, Vq P → Vq P → ℚ)
    (hσq : ∀ P a b, σ P (κ P a) (κ P b) = (σq P a b : ℂ))
    (hσc : ∀ P a b, σ P (cH P a) (cH P b) = starRingEnd ℂ (σ P a b))
    (hσHH : ∀ P, ∀ h ∈ HolH P, ∀ h' ∈ HolH P, σ P h h' = 0)
    (hσpos : ∀ P, ∀ h ∈ HolH P, h ≠ 0 → ∃ t : ℝ, 0 < t ∧ Complex.I * σ P h (cH P h) = t)
    (p q : K → ι) (ρ : ∀ k, H (p k) →ₗ[ℂ] G k) (ρ' : ∀ k, H (q k) →ₗ[ℂ] G k)
    (ρq : ∀ k, Vq (p k) →+ Gq k) (ρq' : ∀ k, Vq (q k) →+ Gq k)
    (hρq : ∀ k a, ρ k (κ (p k) a) = κG k (ρq k a))
    (hρq' : ∀ k a, ρ' k (κ (q k) a) = κG k (ρq' k a))
    (hρc : ∀ k a, ρ k (cH (p k) a) = cG k (ρ k a))
    (hρ'c : ∀ k a, ρ' k (cH (q k) a) = cG k (ρ' k a))
    (hρhol : ∀ k, ∀ h ∈ HolH (p k), ρ k h ∈ HolG k)
    (hρ'hol : ∀ k, ∀ h ∈ HolH (q k), ρ' k h ∈ HolG k)
    (w : K → ℚ) (hw : ∀ k, 0 ≤ w k)
    (θ : ∀ k, G k →ₗ[ℂ] G k →ₗ[ℂ] ℂ) (θq : ∀ k, Gq k → Gq k → ℚ)
    (hθq : ∀ k a b, θ k (κG k a) (κG k b) = (θq k a b : ℂ))
    (hθc : ∀ k a b, θ k (cG k a) (cG k b) = starRingEnd ℂ (θ k a b))
    (hθHH : ∀ k, ∀ g ∈ HolG k, ∀ g' ∈ HolG k, θ k g g' = 0)
    (hθpos : ∀ k, ∀ g ∈ HolG k, ∃ t : ℝ, 0 ≤ t ∧ Complex.I * θ k g (cG k g) = t)
    (x : ∀ P, Vq P)
    (hx : ∀ y : ∀ P, Vq P, ∑ P, m P * σq P (x P) (y P) +
      ∑ k, w k * θq k (ρq k (x (p k)) - ρq' k (x (q k))) (ρq k (y (p k)) - ρq' k (y (q k))) = 0) :
    x = 0 := by
  classical
  let K' : (∀ P, Vq P) →+ (∀ P, H P) :=
    Pi.addMonoidHom fun P ↦ (κ P).comp (Pi.evalAddMonoidHom Vq P)
  have hK' : ∀ v P, K' v P = κ P (v P) := fun _ _ ↦ rfl
  let B : (∀ P, H P) →ₗ[ℂ] (∀ P, H P) →ₗ[ℂ] ℂ :=
    ∑ P, ((m P : ℝ) : ℂ) • (σ P).compl₁₂ (LinearMap.proj P) (LinearMap.proj P) +
    ∑ k, ((w k : ℝ) : ℂ) • (θ k).compl₁₂
      (ρ k ∘ₗ LinearMap.proj (p k) - ρ' k ∘ₗ LinearMap.proj (q k))
      (ρ k ∘ₗ LinearMap.proj (p k) - ρ' k ∘ₗ LinearMap.proj (q k))
  have hB : ∀ a b, B a b = ∑ P, ((m P : ℝ) : ℂ) * σ P (a P) (b P) +
      ∑ k, ((w k : ℝ) : ℂ) * θ k (ρ k (a (p k)) - ρ' k (a (q k)))
        (ρ k (b (p k)) - ρ' k (b (q k))) := fun a b ↦ by
    simp [B, LinearMap.sum_apply, smul_eq_mul]
  refine eq_zero_of_complexification K' ?_ ?_ B (fun u v ↦ ∑ P, m P * σq P (u P) (v P) +
      ∑ k, w k * θq k (ρq k (u (p k)) - ρq' k (u (q k))) (ρq k (v (p k)) - ρq' k (v (q k))))
    ?_ ?_ x hx
  · intro a b hab
    funext P
    exact hκ P (congrFun hab P)
  · rw [eq_top_iff]
    intro a _
    have ha : a = ∑ P, Pi.single P (a P) := (Finset.univ_sum_single a).symm
    rw [ha]
    have key : ∀ P (z : H P), z ∈ Submodule.span ℂ (Set.range (κ P)) →
        (Pi.single P z : ∀ P, H P) ∈ Submodule.span ℂ (Set.range K') := by
      intro P z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨v, rfl⟩ := hz
        refine Submodule.subset_span ⟨Pi.single P v, ?_⟩
        funext Q
        by_cases hQ : Q = P
        · subst hQ; simp [hK']
        · simp [hK', Pi.single_eq_of_ne hQ]
      | zero => simp
      | add z z' _ _ hz hz' => rw [Pi.single_add]; exact add_mem hz hz'
      | smul c z _ hz => rw [Pi.single_smul]; exact Submodule.smul_mem _ c hz
    exact Submodule.sum_mem _ fun P _ ↦ key P (a P) (hspan P ▸ Submodule.mem_top)
  · intro u v
    rw [hB]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun P _ ↦ ?_
      rw [hK', hK', hσq]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hK', hK', hK', hK', hρq, hρq', hρq, hρq', ← map_sub, ← map_sub, hθq]
  · intro a ha
    refine eq_zero_of_hodgeData H G cH cG hcH hcG HolH HolG hdec (fun P ↦ (m P : ℝ))
      (fun P ↦ by exact_mod_cast hm P) σ hσc hσHH hσpos p q ρ ρ' hρc hρ'c hρhol hρ'hol
      (fun k ↦ (w k : ℝ)) (fun k ↦ by exact_mod_cast hw k) θ hθc hθHH hθpos a fun b ↦ ?_
    rw [← hB]
    exact ha b

/-- **Collecting the intersection form along the double curves.** -/
private theorem sum_pairing_eq {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (Vq : ι → Type*) [∀ P, AddCommGroup (Vq P)] [∀ P, Module ℚ (Vq P)]
    (Gq : K → Type*) [∀ k, AddCommGroup (Gq k)] [∀ k, Module ℚ (Gq k)]
    (m : ι → ℚ) (τ : ∀ P Q, Vq P →ₗ[ℚ] Vq Q →ₗ[ℚ] ℚ) (τ' : ∀ P Q, Vq P →ₗ[ℚ] Vq P →ₗ[ℚ] ℚ)
    (hττ' : ∀ P, τ' P P = τ P P) (σq : ∀ P, Vq P →ₗ[ℚ] Vq P →ₗ[ℚ] ℚ)
    (p q : K → ι) (hpq : ∀ k, p k ≠ q k) (n : K → ℚ)
    (ρ : ∀ k, Vq (p k) →ₗ[ℚ] Gq k) (ρ' : ∀ k, Vq (q k) →ₗ[ℚ] Gq k)
    (θ : ∀ k, Gq k →ₗ[ℚ] Gq k →ₗ[ℚ] ℚ)
    (hG4 : ∀ P (x x' : Vq P), ∑ Q, m Q * τ' P Q x x' = σq P x x')
    (hG3 : ∀ (x y : ∀ P, Vq P) (P Q : ι), P ≠ Q → τ P Q (x P) (y Q) =
      -(∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q),
          n k * θ k (ρ k (x (p k))) (ρ' k (y (q k)))) -
        ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P),
          n k * θ k (ρ' k (x (q k))) (ρ k (y (p k))))
    (hG3' : ∀ (x y : ∀ P, Vq P) (P Q : ι), P ≠ Q → τ' P Q (x P) (y P) =
      -(∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q),
          n k * θ k (ρ k (x (p k))) (ρ k (y (p k)))) -
        ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P),
          n k * θ k (ρ' k (x (q k))) (ρ' k (y (q k))))
    (x y : ∀ P, Vq P) :
    ∑ P, ∑ Q, τ P Q (m P • x P) (m Q • y Q) =
      ∑ P, m P * σq P (x P) (y P) +
        ∑ k, (m (p k) * m (q k) * n k) *
          θ k (ρ k (x (p k)) - ρ' k (x (q k))) (ρ k (y (p k)) - ρ' k (y (q k))) := by
  classical
  -- reindexing the sums over pairs of components by the double curves
  have key : ∀ (p q : K → ι) (_ : ∀ k, p k ≠ q k) (F : ι → ι → K → ℚ), ∑ P, ∑ Q ∈ Finset.univ.erase P,
      ∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q), F P Q k = ∑ k, F (p k) (q k) k := by
    intro p q hpq F
    simp_rw [Finset.sum_filter]
    have h1 : ∀ P, ∑ Q ∈ Finset.univ.erase P, ∑ k, (if p k = P ∧ q k = Q then F P Q k else 0) =
        ∑ k, ∑ Q ∈ Finset.univ.erase P, (if p k = P ∧ q k = Q then F P Q k else 0) :=
      fun P ↦ Finset.sum_comm
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h2 : ∀ P, ∑ Q ∈ Finset.univ.erase P, (if p k = P ∧ q k = Q then F P Q k else 0) =
        if p k = P then F P (q k) k else 0 := fun P ↦ by
      by_cases hP : p k = P
      · subst hP
        simp only [true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp [Finset.mem_erase, (hpq k).symm]
      · simp [hP]
    simp_rw [h2]
    simp
  have key' : ∀ F : ι → ι → K → ℚ, ∑ P, ∑ Q ∈ Finset.univ.erase P,
      ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P), F P Q k = ∑ k, F (q k) (p k) k := by
    intro F
    rw [← key q p (fun k ↦ (hpq k).symm) F]
    simp_rw [and_comm]
  -- the diagonal terms
  have hdiag : ∀ P, m P * (m P * τ P P (x P) (y P)) = m P * σq P (x P) (y P) -
      ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ' P Q (x P) (y P) := by
    intro P
    rw [← hG4, ← Finset.add_sum_erase _ _ (Finset.mem_univ P), hττ', mul_add, Finset.mul_sum]
    simp only [mul_assoc]
    ring
  have hsplit : ∀ P, ∑ Q, τ P Q (m P • x P) (m Q • y Q) = m P * (m P * τ P P (x P) (y P)) +
      ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ P Q (x P) (y Q) := by
    intro P
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P)]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun Q _ ↦ by ring
  simp_rw [hsplit, hdiag]
  have hoff : ∀ P, ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ P Q (x P) (y Q) -
      ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ' P Q (x P) (y P) =
      ∑ Q ∈ Finset.univ.erase P, ((∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q),
        m P * m Q * n k * (θ k (ρ k (x (p k))) (ρ k (y (p k))) -
          θ k (ρ k (x (p k))) (ρ' k (y (q k))))) +
        ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P),
          m P * m Q * n k * (θ k (ρ' k (x (q k))) (ρ' k (y (q k))) -
            θ k (ρ' k (x (q k))) (ρ k (y (p k))))) := by
    intro P
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun Q hQ ↦ ?_
    have hPQ : P ≠ Q := (Finset.ne_of_mem_erase hQ).symm
    rw [hG3 x y P Q hPQ, hG3' x y P Q hPQ]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, neg_sub, mul_assoc]
    ring
  have hrw : ∀ P, m P * σq P (x P) (y P) - ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ' P Q (x P) (y P) +
      ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ P Q (x P) (y Q) =
      m P * σq P (x P) (y P) + (∑ Q ∈ Finset.univ.erase P, m P * m Q * τ P Q (x P) (y Q) -
      ∑ Q ∈ Finset.univ.erase P, m P * m Q * τ' P Q (x P) (y P)) := fun P ↦ by ring
  simp_rw [hrw, hoff, Finset.sum_add_distrib]
  rw [key (fun k ↦ p k) q hpq (fun P Q k ↦ m P * m Q * n k * (θ k (ρ k (x (p k))) (ρ k (y (p k))) -
          θ k (ρ k (x (p k))) (ρ' k (y (q k))))),
    key' (fun P Q k ↦ m P * m Q * n k * (θ k (ρ' k (x (q k))) (ρ' k (y (q k))) -
            θ k (ρ' k (x (q k))) (ρ k (y (p k)))))]
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [map_sub, LinearMap.sub_apply]
  ring

end LinearAlgebra

/-! ### The Kronecker pairing on a compact space -/

section Kronecker

variable {Y : TopCat.{0}} [CompactSpace Y]

private lemma finite_support_coeff {n : ℕ} (c : (BM ℚ Y).X n) :
    (Function.support (coeff ℚ c)).Finite := by
  have := (coeff_mem ℚ c).finite_inter_compact (isCompact_univ (X := Y))
  refine this.subset fun σ hσ ↦ ⟨hσ, ?_⟩
  obtain ⟨y, hy⟩ := (compact_nonempty σ).2
  exact ⟨y, hy, trivial⟩

private lemma finsum_pushforwardFun {S T : Type*} (f : S → T) (c : S → ℚ)
    (hc : (Function.support c).Finite) :
    ∑ᶠ τ, pushforwardFun f c τ = ∑ᶠ σ, c σ := by
  classical
  set F := hc.toFinset
  have h1 : ∀ τ, pushforwardFun f c τ = ∑ σ ∈ F, if f σ = τ then c σ else 0 := fun τ ↦
    pushforwardFun_apply_eq_sum f c τ F fun σ hσ _ ↦ by simpa [F] using hσ
  rw [finsum_eq_sum_of_support_subset (s := F.image f), finsum_eq_sum_of_support_subset (s := F)]
  · simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ hσ ↦ ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_image_of_mem f hσ]
  · intro σ hσ; simpa [F] using hσ
  · intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := support_pushforwardFun_subset f c hτ
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem f ((Set.Finite.mem_toFinset _).2 hσ))

variable (Y) in
/-- The augmentation `∑ a_σ σ ↦ ∑ a_σ` on locally finite `0`-chains of a compact space. -/
private noncomputable def aug : (BM ℚ Y).X 0 →ₗ[ℚ] ℚ where
  toFun c := ∑ᶠ σ, coeff ℚ c σ
  map_add' c d := by
    rw [coeff_add]
    exact finsum_add_distrib (finite_support_coeff c) (finite_support_coeff d)
  map_smul' r c := by
    rw [coeff_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
    rfl

private lemma aug_d (u : (BM ℚ Y).X 1) : aug Y (((BM ℚ Y).d 1 0).hom u) = 0 := by
  change ∑ᶠ σ, coeff ℚ (((BM ℚ Y).d (0 + 1) 0).hom u) σ = 0
  rw [coeff_d]
  have hf : ∀ i : Fin 2, (Function.support
      (pushforwardFun ((TopCat.toSSet.obj Y).δ i) (coeff ℚ u))).Finite := fun i ↦
    ((finite_support_coeff u).image _).subset (support_pushforwardFun_subset _ _)
  refine (finsum_congr fun σ ↦ ?_).trans ((finsum_sub_distrib (hf 0) (hf 1)).trans ?_)
  · simp [Fin.sum_univ_two, sub_eq_add_neg]
  · rw [finsum_pushforwardFun _ _ (finite_support_coeff u),
      finsum_pushforwardFun _ _ (finite_support_coeff u), sub_self]

variable (Y) in
/-- The degree `H_0(Y; ℚ) → ℚ` on cycles modulo boundaries, induced by the augmentation. -/
private noncomputable def degQ : HomQ (R := ℚ) Y 0 →ₗ[ℚ] ℚ :=
  (LinearMap.range ((BM ℚ Y).sc 0).moduleCatToCycles).liftQ ((aug Y).comp (Cyc (R := ℚ) Y 0).subtype)
    (fun z hz ↦ by
      obtain ⟨u, hu⟩ := exists_of_mem_bdry hz
      change aug Y z.1 = 0
      rw [← hu]
      exact aug_d u)

variable (Y) in
/-- The degree `H_0(Y; ℚ) → ℚ` of a compact space. -/
private noncomputable def deg : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y 0 →ₗ[ℚ] ℚ :=
  (degQ Y).comp (homologyEquiv ℚ Y 0).toLinearMap

variable (Y) in
/-- The Kronecker pairing `H^n(Y; ℚ) × H_n(Y; ℚ) → ℚ`, `(c, b) ↦ deg (c ∩ b)`. -/
private noncomputable def kron (n : ℕ) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y Set.univ n →ₗ[ℚ]
      borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y n →ₗ[ℚ] ℚ :=
  (borelMooreHomology.capProduct ℚ Y Set.univ n n).compr₂
    ((deg Y).comp (congrDegree ℚ Y (sub_self (n : ℤ))).toLinearMap)

private lemma aug_capChain (n : ℕ) (φ : Simplex Y n → ℚ) (z : (BM ℚ Y).X n) :
    aug Y (capChain ℚ n 0 n (add_zero n) φ z) =
      ∑ᶠ σ, φ (simplexEquiv Y n σ) * coeff ℚ z σ := by
  change ∑ᶠ σ, coeff ℚ (pf ℚ _ (W ℚ _ z)) σ = _
  rw [coeff_pf, finsum_pushforwardFun _ _ ((finite_support_coeff z).subset ?_), coeff_W]
  · refine finsum_congr fun σ ↦ ?_
    congr 2
    have : back n n 0 (by omega) = id := funext fun j ↦ Fin.ext (by simp [back])
    simp only [wt, this, comp_smap_id]
  · intro σ hσ h
    exact hσ (by simp [coeff_W, h])

private lemma deg_congrDegree_capHomQ (A : Set Y) (p q m : ℕ) (hq : q = 0) (h : p + q = m)
    (e : ((q : ℕ) : ℤ) = ((0 : ℕ) : ℤ)) (φ : relCocycles ℚ A p) (z : Cyc (R := ℚ) Y m) :
    deg Y (congrDegree ℚ Y e ((homologyEquiv ℚ Y q).symm
        (capHomQ ℚ A p q m h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk z)))) =
      aug Y (capChain ℚ p 0 m (by omega) φ.1 z.1) := by
  subst hq
  rw [congrDegree_self]
  rw [LinearEquiv.refl_apply, capHomQ_mk, deg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (congrArg (degQ Y) ((homologyEquiv ℚ Y 0).apply_symm_apply _)).trans rfl

private lemma kron_ofCocycle (n : ℕ) (φ : Simplex Y n → ℚ)
    (hφ : φ ∈ relCocycles ℚ (Set.univᶜ : Set Y) n) (z : Cyc (R := ℚ) Y n) :
    kron Y n (cohomologyWithSupports.ofCocycle ℚ Y n φ hφ)
        ((homologyEquiv ℚ Y n).symm (Submodule.Quotient.mk z)) =
      ∑ᶠ σ, φ (simplexEquiv Y n σ) * coeff ℚ z.1 σ := by
  rw [← aug_capChain]
  simp only [kron, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    borelMooreHomology.capProduct_natCast Y Set.univ (le_refl n), LinearEquiv.apply_symm_apply,
    borelMooreHomology.congrDegree_congrDegree_eq, cohomologyWithSupports.ofCocycle]
  rw [show (homologyEquiv ℚ Y n) ((homologyEquiv ℚ Y n).symm (Submodule.Quotient.mk z)) =
    Submodule.Quotient.mk z from LinearEquiv.apply_symm_apply _ _]
  exact deg_congrDegree_capHomQ (Set.univᶜ) n (n - n) n (Nat.sub_self n) (by omega) _ ⟨φ, hφ⟩ z

private lemma deg_symm_mk (z : Cyc (R := ℚ) Y 0) :
    deg Y ((homologyEquiv ℚ Y 0).symm (Submodule.Quotient.mk z)) = aug Y z.1 := by
  rw [deg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (congrArg (degQ Y) ((homologyEquiv ℚ Y 0).apply_symm_apply _)).trans rfl

/-- The degree is invariant under proper push-forward between compact spaces. -/
private lemma deg_pushforward {Y' : TopCat.{0}} [CompactSpace Y'] (f : Y ⟶ Y') (hf : IsProperMap f)
    (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y 0) :
    deg Y' ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf 0).hom z) = deg Y z := by
  obtain ⟨c, rfl⟩ : ∃ c : Cyc (R := ℚ) Y 0,
      (homologyEquiv ℚ Y 0).symm (Submodule.Quotient.mk c) = z := by
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv ℚ Y 0 z)
    exact ⟨c, by rw [hc, LinearEquiv.symm_apply_apply]⟩
  rw [pushforward_eq_homologyMap]
  erw [homologyMap_homologyEquiv_symm_mk ℚ _ 0 c]
  rw [deg_symm_mk c]
  refine (deg_symm_mk _).trans ?_
  change ∑ᶠ τ, pushforwardFun ((TopCat.toSSet.map f).app _) (coeff ℚ c.1) τ = ∑ᶠ σ, coeff ℚ c.1 σ
  exact finsum_pushforwardFun _ _ (finite_support_coeff c.1)

/-- The degree commutes with transport along an equality of degrees, read as `0`. -/
private lemma deg_congrDegree_pushforward {Y' : TopCat.{0}} [CompactSpace Y'] (f : Y ⟶ Y')
    (hf : IsProperMap f) {i : ℤ} (h : i = 0)
    (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y i) :
    deg Y' (congrDegree ℚ Y' h ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf i).hom z)) =
      deg Y (congrDegree ℚ Y h z) := by
  subst h
  exact deg_pushforward f hf z

/-- **The Kronecker pairing of a restricted supported class.** For `v ∈ H³(M, M - X)` and
`b ∈ H₃ X`, `⟨v|_X, b⟩ = deg (j^* v ∩ b)`, the cap product with supports along the inclusion
`j : X → M`. -/
private lemma kron_rationalCohomologyMap_toCohomology {M : TopCat.{0}} {X : Set M}
    [CompactSpace X] [CompactSpace (borelMooreHomology.subsetInclusion X ⁻¹' X)] (hX : IsClosed X)
    (hd' : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion X ⁻¹' X))
    (v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M X 3)
    (b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X) 3) :
    kron (TopCat.of X) 3 ((rationalCohomologyMap (subspaceInclusion M X) 3).hom
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) M X 3).hom v)) b =
      deg (TopCat.of (borelMooreHomology.subsetInclusion X ⁻¹' X))
        (congrDegree ℚ _ (sub_self (3 : ℤ))
          (borelMooreHomology.capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion X)
            hX hd' 3 3 v b)) := by
  have h1 : (rationalCohomologyMap (subspaceInclusion M X) 3).hom
      ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) M X 3).hom v) =
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X)
        (borelMooreHomology.subsetInclusion X ⁻¹' X) 3).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
          (borelMooreHomology.subsetInclusion X) X 3).hom v) :=
    cohomologyWithSupports.pullback_forget_apply ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology.subsetInclusion X) (Set.subset_univ X) 3 v
  simp only [kron, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h1]
  erw [borelMooreHomology.capProduct_toCohomology (TopCat.of X) _ 3 3, ←
    borelMooreHomology.pushforward_subsetInclusion_capProductSupport]
  · exact deg_congrDegree_pushforward _ _ (sub_self (3 : ℤ)) _
  · exact hd'

/-- A linear functional killing the kernel of a linear map of vector spaces factors through it. -/
private lemma exists_comp_eq_of_ker_le {K V U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] (f : V →ₗ[K] K) (g : V →ₗ[K] U)
    (h : LinearMap.ker g ≤ LinearMap.ker f) : ∃ f' : U →ₗ[K] K, f'.comp g = f := by
  let f₀ : LinearMap.range g →ₗ[K] K :=
    ((LinearMap.ker g).liftQ f h).comp (g.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨f', hf'⟩ := LinearMap.exists_extend f₀
  refine ⟨f', LinearMap.ext fun v ↦ ?_⟩
  have := congrArg (fun φ ↦ φ ⟨g v, v, rfl⟩) hf'
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [LinearMap.comp_apply, this]
  simp only [f₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show g.quotKerEquivRange.symm ⟨g v, v, rfl⟩ = Submodule.Quotient.mk v from
    g.quotKerEquivRange.symm_apply_eq.2 rfl, Submodule.liftQ_apply]

/-- **Universal coefficients, injectivity.** A singular cocycle with values in a field which
vanishes on every finite cycle is a coboundary. -/
private lemma exists_coboundary_eq {K : Type*} [Field K] {Z : Type*} [TopologicalSpace Z] (m : ℕ)
    (φ : Simplex Z (m + 1) → K)
    (hφ : ∀ c : Chain K Z (m + 1), bd K m c = 0 → eval φ c = 0) :
    ∃ ψ : Simplex Z m → K, coboundary K m ψ = φ := by
  obtain ⟨f', hf'⟩ := exists_comp_eq_of_ker_le (eval φ) (bd K m) fun c hc ↦ hφ c hc
  refine ⟨fun σ ↦ f' (Finsupp.single σ 1), funext fun σ ↦ ?_⟩
  have hev : (eval (fun σ ↦ f' (Finsupp.single σ 1)) : Chain K Z m →ₗ[K] K) = f' :=
    Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring (by simp)
  rw [coboundary_apply_eq_eval, hev, ← LinearMap.comp_apply, hf', eval_single_one]

section RationalSpanning

variable {Z : Type*} [TopologicalSpace Z]

/-- The boundary of finite chains commutes with additive changes of coefficients. -/
private lemma bd_mapRange {R S : Type*} [CommRing R] [CommRing S] (f : R →+ S) (n : ℕ)
    (c : Chain R Z (n + 1)) :
    bd S n (Finsupp.mapRange f f.map_zero c) = Finsupp.mapRange f f.map_zero (bd R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [Finsupp.mapRange_add f.map_add, map_add, map_add, hc, hd,
      Finsupp.mapRange_add f.map_add]
  | single σ a =>
    rw [Finsupp.mapRange_single]
    simp only [bd, Finsupp.linearCombination_single, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    rw [Finsupp.mapRange_finset_sum f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finsupp.mapRange_single]
    congr 1
    have hR : (-1 : R) ^ (i : ℕ) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : R) := by push_cast; rfl
    have hS : (-1 : S) ^ (i : ℕ) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : S) := by push_cast; rfl
    rw [hR, hS, mul_comm a, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]

/-- **Rational cycles detect complex cycles.** A complex cochain which vanishes on every rational
finite cycle vanishes on every complex finite cycle. -/
private lemma eval_eq_zero_of_forall_rat (n : ℕ) (ψ : Simplex Z (n + 1) → ℂ)
    (hψ : ∀ c : Chain ℚ Z (n + 1), bd ℚ n c = 0 →
      eval ψ (Finsupp.mapRange (algebraMap ℚ ℂ) (map_zero _) c) = 0)
    (c : Chain ℂ Z (n + 1)) (hc : bd ℂ n c = 0) : eval ψ c = 0 := by
  classical
  let V : Submodule ℚ ℂ := Submodule.span ℚ (c '' c.support)
  haveI : FiniteDimensional ℚ V :=
    FiniteDimensional.span_of_finite ℚ ((c.support.finite_toSet).image _)
  let b := Module.finBasis ℚ V
  have hlam : ∀ j, ∃ lam : ℂ →ₗ[ℚ] ℚ, lam.comp V.subtype = b.coord j := fun j ↦
    LinearMap.exists_extend (b.coord j)
  choose lam hlam using hlam
  have hmem : ∀ σ, c σ ∈ V := fun σ ↦ by
    by_cases h : σ ∈ c.support
    · exact Submodule.subset_span ⟨σ, h, rfl⟩
    · rw [Finsupp.notMem_support_iff.1 h]; exact zero_mem _
  have hdec : c = ∑ j, (b j : ℂ) • Finsupp.mapRange (algebraMap ℚ ℂ) (map_zero _)
      (Finsupp.mapRange (lam j) (map_zero _) c) := by
    ext σ
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul]
    have h1 := b.sum_repr ⟨c σ, hmem σ⟩
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have : lam j (c σ) = b.repr ⟨c σ, hmem σ⟩ j := by
      have := congrArg (fun φ ↦ φ ⟨c σ, hmem σ⟩) (hlam j)
      simpa using this
    rw [this, Rat.smul_def, mul_comm]
    rfl
  rw [hdec, map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [map_smul, hψ _ ?_, smul_zero]
  have := bd_mapRange (lam j).toAddMonoidHom n c
  simp only [hc, Finsupp.mapRange_zero] at this
  exact this

/-- **Rational spanning of complex cohomology, on cochains.** If the rational homology of finite
chains is finite dimensional in degree `n + 1`, every complex `(n+1)`-cocycle is a complex linear
combination of rational cocycles up to a coboundary. -/
private lemma exists_rat_cocycles (n : ℕ)
    (hfin : FiniteDimensional ℚ (LinearMap.ker (bd ℚ n : Chain ℚ Z (n + 1) →ₗ[ℚ] _) ⧸
      (LinearMap.range (bd ℚ (n + 1))).comap (LinearMap.ker (bd ℚ n)).subtype))
    (φ : Simplex Z (n + 1) → ℂ) (hφ : coboundary ℂ (n + 1) φ = 0) :
    ∃ (m : ℕ) (e : Fin m → Simplex Z (n + 1) → ℚ) (a : Fin m → ℂ) (ψ : Simplex Z n → ℂ),
      (∀ k, coboundary ℚ (n + 1) (e k) = 0) ∧
        φ = ∑ k, a k • (fun σ ↦ (e k σ : ℂ)) + coboundary ℂ n ψ := by
  classical
  set Zc := LinearMap.ker (bd ℚ n : Chain ℚ Z (n + 1) →ₗ[ℚ] _)
  set Bd := (LinearMap.range (bd ℚ (n + 1))).comap Zc.subtype
  let H := Zc ⧸ Bd
  let bH := Module.finBasis ℚ H
  -- complexification of a rational chain
  let κ : Chain ℚ Z (n + 1) →+ Chain ℂ Z (n + 1) :=
    Finsupp.mapRange.addMonoidHom (algebraMap ℚ ℂ).toAddMonoidHom
  have hevκ : ∀ (e : Simplex Z (n + 1) → ℚ) (z : Chain ℚ Z (n + 1)),
      eval (fun σ ↦ (e σ : ℂ)) (κ z) = (eval e z : ℂ) := fun e z ↦ by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, Rat.cast_add]
    | single σ q => simp [κ]
  -- the functional `z ↦ φ(z)` on rational cycles, killing boundaries
  let Φ : Zc →ₗ[ℚ] ℂ :=
    ((eval φ).toAddMonoidHom.comp (κ.comp Zc.subtype.toAddMonoidHom)).toRatLinearMap
  have hΦ : Bd ≤ LinearMap.ker Φ := fun z hz ↦ by
    obtain ⟨u, hu⟩ := hz
    change eval φ (κ z.1) = 0
    rw [show z.1 = bd ℚ (n + 1) u from hu.symm]
    have := bd_mapRange (algebraMap ℚ ℂ).toAddMonoidHom (n + 1) u
    change eval φ (κ (bd ℚ (n + 1) u)) = 0
    rw [show κ (bd ℚ (n + 1) u) = bd ℂ (n + 1)
      (Finsupp.mapRange (algebraMap ℚ ℂ) (map_zero _) u) from this.symm, ← eval_coboundary, hφ]
    simp
  let Φb : H →ₗ[ℚ] ℂ := Bd.liftQ Φ hΦ
  -- rational cocycles dual to a basis of `H`
  have hg : ∀ k, ∃ g : Chain ℚ Z (n + 1) →ₗ[ℚ] ℚ,
      g.comp Zc.subtype = (bH.coord k).comp Bd.mkQ := fun k ↦ LinearMap.exists_extend _
  choose g hg using hg
  let e : Fin (Module.finrank ℚ H) → Simplex Z (n + 1) → ℚ := fun k σ ↦ g k (Finsupp.single σ 1)
  have hev : ∀ k, (eval (e k) : Chain ℚ Z (n + 1) →ₗ[ℚ] ℚ) = g k := fun k ↦
    Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring (by simp [e])
  have he : ∀ k, coboundary ℚ (n + 1) (e k) = 0 := fun k ↦ funext fun τ ↦ by
    rw [coboundary_apply_eq_eval, hev]
    have hz : bd ℚ (n + 1) (Finsupp.single τ 1) ∈ Zc := by
      rw [LinearMap.mem_ker, bd_bd]
    have := congrArg (fun F ↦ F ⟨_, hz⟩) (hg k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (by
      show Zc.subtype ⟨_, hz⟩ ∈ LinearMap.range (bd ℚ (n + 1))
      exact ⟨Finsupp.single τ 1, rfl⟩), map_zero]
    rfl
  set a : Fin (Module.finrank ℚ H) → ℂ := fun k ↦ Φb (bH k)
  set ψ' := φ - ∑ k, a k • (fun σ ↦ (e k σ : ℂ))
  have hsum : ∀ (f : Fin (Module.finrank ℚ H) → Simplex Z (n + 1) → ℂ) (c : Chain ℂ Z (n + 1)),
      eval (∑ k, a k • f k) c = ∑ k, a k * eval (f k) c := fun f c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, ← Finset.sum_add_distrib]; simp [mul_add]
    | single σ r =>
      simp only [Finsupp.linearCombination_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hψ' : ∀ c : Chain ℂ Z (n + 1), bd ℂ n c = 0 → eval ψ' c = 0 := by
    refine eval_eq_zero_of_forall_rat n ψ' fun z hz ↦ ?_
    change eval ψ' (κ z) = 0
    have hrepr := bH.sum_repr (Bd.mkQ ⟨z, hz⟩)
    have h1 : eval φ (κ z) = Φb (Bd.mkQ ⟨z, hz⟩) := rfl
    have h2 : ∀ k, (eval (e k) z : ℂ) = (bH.repr (Bd.mkQ ⟨z, hz⟩) k : ℂ) := fun k ↦ by
      rw [hev]
      have := congrArg (fun F ↦ F ⟨z, hz⟩) (hg k)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]; rfl
    have h3 : Φb (Bd.mkQ ⟨z, hz⟩) =
        ∑ k, (bH.repr (Bd.mkQ ⟨z, hz⟩) k : ℂ) * Φb (bH k) := by
      conv_lhs => rw [← hrepr]
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, Rat.smul_def]
    simp only [ψ', eval_sub_cochain, hsum, hevκ, h2, h1]
    rw [h3, sub_eq_zero]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  obtain ⟨ψ, hψ⟩ := exists_coboundary_eq n ψ' hψ'
  refine ⟨_, e, a, ψ, he, ?_⟩
  rw [hψ]
  exact (add_sub_cancel _ _).symm

end RationalSpanning

private lemma mem_vanishing_compl_univ {K : Type*} [CommRing K] {Z : TopCat.{0}} {n : ℕ}
    (φ : Simplex Z n → K) : φ ∈ vanishing K n (Set.univᶜ : Set Z) :=
  fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

/-- A finite cycle is a locally finite cycle. -/
private lemma ofFinsupp_mem_cyc (m : ℕ) (c : Chain ℚ Y (m + 1)) (hc : bd ℚ m c = 0) :
    (borelMooreHomology.ofFinsupp c : (BM ℚ Y).X (m + 1)) ∈ Cyc (R := ℚ) Y (m + 1) := by
  rw [mem_cyc_iff]
  exact (borelMooreHomology.d_ofFinsupp c).trans (by rw [hc]; rfl)

/-- The pairing of a cocycle with the class of a finite cycle is the evaluation. -/
private lemma kron_ofCocycle_ofFinsupp (m : ℕ) (φ : Simplex Y (m + 1) → ℚ)
    (hφ : φ ∈ relCocycles ℚ (Set.univᶜ : Set Y) (m + 1)) (c : Chain ℚ Y (m + 1))
    (hc : bd ℚ m c = 0) :
    kron Y (m + 1) (cohomologyWithSupports.ofCocycle ℚ Y (m + 1) φ hφ)
        ((homologyEquiv ℚ Y (m + 1)).symm (Submodule.Quotient.mk
          ⟨borelMooreHomology.ofFinsupp c, ofFinsupp_mem_cyc m c hc⟩)) =
      eval φ c := by
  classical
  refine (kron_ofCocycle (m + 1) φ hφ ⟨_, ofFinsupp_mem_cyc m c hc⟩).trans ?_
  change ∑ᶠ σ, φ (simplexEquiv Y (m + 1) σ) * c (simplexEquiv Y (m + 1) σ) = _
  rw [finsum_comp_equiv (simplexEquiv Y (m + 1)) (f := fun τ ↦ φ τ * c τ),
    finsum_eq_sum_of_support_subset (s := c.support) _ fun τ hτ ↦ by
      simpa using right_ne_zero_of_mul hτ,
    Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun τ _ ↦ by rw [smul_eq_mul, mul_comm]

/-- On a compact space the homology of finite chains injects into Borel–Moore homology, so it is
finite dimensional when Borel–Moore homology is. -/
private lemma finiteDimensional_finiteChainHomology (m : ℕ)
    [FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y ((m + 1 : ℕ) : ℤ))] :
    FiniteDimensional ℚ (LinearMap.ker (bd ℚ m : Chain ℚ Y (m + 1) →ₗ[ℚ] _) ⧸
      (LinearMap.range (bd ℚ (m + 1))).comap (LinearMap.ker (bd ℚ m)).subtype) := by
  classical
  set Zc := LinearMap.ker (bd ℚ m : Chain ℚ Y (m + 1) →ₗ[ℚ] _)
  let L : Zc →ₗ[ℚ] HomQ (R := ℚ) Y (m + 1) :=
    { toFun := fun z ↦ Submodule.Quotient.mk
        ⟨borelMooreHomology.ofFinsupp z.1, ofFinsupp_mem_cyc m z.1 z.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : (LinearMap.range (bd ℚ (m + 1))).comap Zc.subtype ≤ LinearMap.ker L := by
    rintro z ⟨u, hu⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 (mem_bdry_of _ (borelMooreHomology.ofFinsupp u) ?_)
    rw [borelMooreHomology.d_ofFinsupp]
    exact congrArg borelMooreHomology.ofFinsupp hu
  let Lb := ((LinearMap.range (bd ℚ (m + 1))).comap Zc.subtype).liftQ L hL
  have hinj : Function.Injective Lb := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H z => ?_
    obtain ⟨u, hu⟩ := exists_of_mem_bdry ((Submodule.Quotient.mk_eq_zero _).1 hx)
    have hfu := finite_support_coeff u
    have hu' : borelMooreHomology.ofFinsupp (bd ℚ (m + 1) (borelMooreHomology.toFinsupp u hfu)) =
        borelMooreHomology.ofFinsupp z.1 := by
      rw [← borelMooreHomology.d_ofFinsupp, borelMooreHomology.ofFinsupp_toFinsupp u hfu]
      exact hu
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨_, BorelMooreCap.ofFinsupp_injective hu'⟩
  haveI : FiniteDimensional ℚ (HomQ (R := ℚ) Y (m + 1)) :=
    Module.Finite.equiv (homologyEquiv ℚ Y (m + 1))
  exact Module.Finite.of_injective Lb hinj

/-- **Rational classes span complex cohomology** on a compact space with finite dimensional
rational homology. -/
private theorem mem_span_range_mapCoeff (m : ℕ)
    [FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y ((m + 1 : ℕ) : ℤ))]
    (h : MMP.Analytic.singularCohomology ℂ Y (m + 1)) :
    h ∈ Submodule.span ℂ (Set.range (MMP.Analytic.singularCohomology.mapCoeff (algebraMap ℚ ℂ) (Y := Y) (m + 1))) := by
  classical
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq (m + 1) h
  haveI := finiteDimensional_finiteChainHomology (Y := Y) m
  obtain ⟨k, e, a, ψ, he, hφe⟩ := exists_rat_cocycles m this φ hφ.2
  let L : relCocycles ℂ (Set.univᶜ : Set Y) (m + 1) →ₗ[ℂ] MMP.Analytic.singularCohomology ℂ Y (m + 1) :=
    (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y) (m + 1)).symm.toLinearMap ∘ₗ
      Submodule.mkQ _
  have hL : ∀ (χ : Simplex Y (m + 1) → ℂ) (hχ : χ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (m + 1)),
      cohomologyWithSupports.ofCocycle ℂ Y (m + 1) χ hχ = L ⟨χ, hχ⟩ := fun _ _ ↦ rfl
  have hmem : ∀ i, (fun σ ↦ (e i σ : ℂ)) ∈ relCocycles ℂ (Set.univᶜ : Set Y) (m + 1) := fun i ↦
    MMP.Analytic.singularCohomology.cochainMap_mem_relCocycles (algebraMap ℚ ℂ)
      ⟨mem_vanishing_compl_univ _, he i⟩
  have hδ : coboundary ℂ m ψ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (m + 1) :=
    ⟨mem_vanishing_compl_univ _, coboundary_coboundary m ψ⟩
  have hsplit : (⟨φ, hφ⟩ : relCocycles ℂ (Set.univᶜ : Set Y) (m + 1)) =
      ∑ i, a i • ⟨_, hmem i⟩ + ⟨_, hδ⟩ :=
    Subtype.ext <| by
      simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] using hφe
  have hL0 : L ⟨_, hδ⟩ = 0 := by
    simp only [L, LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨ψ, mem_vanishing_compl_univ ψ, rfl⟩
  rw [hL, hsplit, map_add, hL0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range.2 ⟨
    cohomologyWithSupports.ofCocycle ℚ Y (m + 1) (e i)
      (show e i ∈ relCocycles ℚ (Set.univᶜ : Set Y) (m + 1) from
        ⟨mem_vanishing_compl_univ _, he i⟩), ?_⟩))
  rw [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle]
  rfl

/-- **Universal coefficients over `ℚ` on a compact space.** A class in `H^{m+1}(Y; ℚ)` which pairs
to zero with every class in `H_{m+1}(Y; ℚ)` vanishes. -/
private theorem eq_zero_of_forall_kron_eq_zero (m : ℕ)
    (h : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y Set.univ (m + 1 : ℕ))
    (hh : ∀ b, kron Y (m + 1) h b = 0) : h = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq (m + 1) h
  obtain ⟨ψ, hψ⟩ := exists_coboundary_eq m φ fun c hc ↦ by
    rw [← kron_ofCocycle_ofFinsupp m φ hφ c hc]
    exact hh _
  rw [cohomologyWithSupports.ofCocycle, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨ψ, mem_vanishing_compl_univ ψ, hψ⟩

end Kronecker

section PointDegree

open MMP.FundamentalClass

variable {Y : TopCat.{0}} [Subsingleton Y]

/-- On a space with at most one point, the class of a `0`-simplex is locally the class of every
`0`-simplex at every point. -/
private lemma isLocallyClassOf_single (σ₀ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌))
    (z₀ : Cyc (R := ℚ) Y 0) (hz₀ : z₀.1 = singleChain ℚ σ₀) (y : Y) (Δ : Simplex Y 0) :
    IsLocallyClassOf ℚ ((homologyEquiv ℚ Y 0).symm (Submodule.Quotient.mk z₀)) y Δ := by
  classical
  intro z hz φ hφ
  let z' : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).cycles 0 :=
    ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).sc 0).moduleCatCyclesIso.inv.hom z₀
  have hz'₀ : ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).sc 0).moduleCatCyclesIso.hom.hom z' =
      z₀ := by
    change (((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).sc 0).moduleCatCyclesIso.inv ≫
      ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).sc 0).moduleCatCyclesIso.hom).hom z₀ = z₀
    rw [Iso.inv_hom_id]; rfl
  have hc : (homologyEquiv ℚ Y 0).symm (Submodule.Quotient.mk z₀) =
      (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) Y 0).inv
        ((borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).homologyπ 0 z') := by
    refine ((homologyEquiv ℚ Y 0).symm_apply_eq).2 ?_
    refine Eq.trans ?_ (homologyEquiv_eq_mk z' (by
      change _ = ((borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) Y 0).inv ≫
        (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) Y 0).hom).hom _
      rw [Iso.inv_hom_id]; rfl)).symm
    exact congrArg _ hz'₀.symm
  have hz' : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).homologyπ 0 z =
      (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).homologyπ 0 z' := by
    rw [hz, hc]
    change ((borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) Y 0).inv ≫
      (borelMooreHomologyIsoOfNat ℚ (ModuleCat.of ℚ ℚ) Y 0).hom).hom _ = _
    rw [Iso.inv_hom_id]; rfl
  have hi : (borelMooreChainComplex ℚ (ModuleCat.of ℚ ℚ) Y).iCycles 0 z' = singleChain ℚ σ₀ := by
    rw [← coe_moduleCatCyclesIso_hom, hz'₀, hz₀]
  rw [localPairing_eq_of_homologyπ_eq hz' hφ, hi, localPairing, coe_singleChain,
    finsum_eq_single _ σ₀ (fun σ hσ ↦ by rw [Pi.single_eq_of_ne hσ, zero_mul]),
    Pi.single_eq_same, one_mul]
  exact congrArg φ (Subsingleton.elim _ _)

/-- The class of the point is a fundamental class of a zero-dimensional complex variety with one
complex point. -/
private lemma isVarietyFundamentalClass_single {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
    (hn : ((0 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    [Subsingleton (UnderlyingSpace ℂ V)]
    (σ₀ : (TopCat.toSSet.obj (TopCat.of (UnderlyingSpace ℂ V))).obj (op ⦋0⦌))
    (z₀ : Cyc (R := ℚ) (TopCat.of (UnderlyingSpace ℂ V)) 0) (hz₀ : z₀.1 = singleChain ℚ σ₀) :
    IsVarietyFundamentalClass ℚ hn
      ((homologyEquiv ℚ (TopCat.of (UnderlyingSpace ℂ V)) 0).symm (Submodule.Quotient.mk z₀)) := by
  letI := UnderlyingSpace.regularChartedSpace (𝕜 := ℂ) hn
  intro e he x v hv hvt
  exact IsLocallyClassOf.restrict _ (IsLocallyClassOf.restrict _
    (isLocallyClassOf_single σ₀ z₀ hz₀ _ _))

/-- **The fundamental class of the point has degree one.** -/
private lemma deg_eq_one_of_isVarietyFundamentalClass_spec
    (h0 : ((0 : ℕ) : WithBot ℕ∞) = topologicalKrullDim (Spec (.of ℂ)))
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))
      (2 * 0 : ℕ)} (hμ : IsVarietyFundamentalClass ℚ h0 μ) :
    deg (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) μ = 1 := by
  classical
  haveI : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ by
    apply Subtype.ext
    rw [MMP.specOverSpec_over_self, Category.comp_id] at ha hb
    exact ha.trans hb.symm⟩
  let p₀ : UnderlyingSpace ℂ (Spec (.of ℂ)) :=
    ⟨𝟙 _, by rw [Category.id_comp]; exact MMP.specOverSpec_over_self ℂ⟩
  let σ₀ : (TopCat.toSSet.obj (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))).obj (op ⦋0⦌) :=
    ((TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))).toSSetObjEquiv (op ⦋0⦌)).symm
      (ContinuousMap.const _ p₀)
  let z₀ : Cyc (R := ℚ) (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) 0 :=
    ⟨singleChain ℚ σ₀, by
      rw [mem_cyc_iff, (BM ℚ (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))).shape 0 (0 - 1)
        (by simp)]
      rfl⟩
  have hf := isVarietyFundamentalClass_single h0 σ₀ z₀ rfl
  rw [hμ.eq hf, deg_symm_mk]
  change ∑ᶠ σ, coeff ℚ (singleChain ℚ σ₀) σ = 1
  rw [finsum_eq_single _ σ₀ (fun σ hσ ↦ by
    change (Pi.single σ₀ (1 : ℚ) : _ → ℚ) σ = 0
    rw [Pi.single_eq_of_ne hσ])]
  change (Pi.single σ₀ (1 : ℚ) : _ → ℚ) σ₀ = 1
  rw [Pi.single_eq_same]

/-- **The cycle class of the generic point is the fundamental class.** On a complex variety `V`
of dimension `k`, the Stacks cycle class `cl_V(ξ_V)` of the generic point is `cl(V)`: the closure
of `ξ_V` is `V` itself. -/
private lemma pointCycleClass_genericPoint_eq {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] {k : ℕ}
    (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) (genericPoint V) = k)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hk μ) :
    Chow.pointCycleClass ℚ (genericPoint V) hx = μ := by
  haveI := Stacks.Chow.isIntegral_integralComponentAt (genericPoint V)
  set i := (Stacks.Chow.integralComponentAt (genericPoint V)).subschemeι
  have hrange : Set.range (𝟙 V : V ⟶ V) = Set.range i := by
    rw [Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt,
      (genericPoint_spec V).def]
    simp
  have hker : (𝟙 V : V ⟶ V).ker = i.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange]
  obtain ⟨φ, hφ, hφi⟩ : ∃ φ : _ ⟶ V, IsIso φ ∧ φ ≫ 𝟙 V = i :=
    ⟨_, IsClosedImmersion.isIso_lift (𝟙 V) i hker, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Category.comp_id] at hφi
  haveI : IsIso i := hφi ▸ hφ
  have hc := (existsUnique_isVarietyFundamentalClass ℚ
    (Chow.natCast_eq_dimension_integralComponentAt (genericPoint V) hx)).choose_spec.1
  exact (IsVarietyFundamentalClass.pushforward_of_isIso i hk hc).eq hμ

/-- **The Stacks cycle class of the point has degree one.** -/
private lemma deg_pointCycleClass_spec (x : Spec (.of ℂ))
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) x = (0 : ℕ)) :
    deg (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) (Chow.pointCycleClass ℚ x hx) = 1 := by
  have h0 : ((0 : ℕ) : WithBot ℕ∞) = topologicalKrullDim (Spec (.of ℂ)) := by
    change _ = topologicalKrullDim (PrimeSpectrum ℂ)
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]; rfl
  obtain ⟨μ₀, hμ₀, -, -⟩ := existsUnique_isVarietyFundamentalClass (R := ℚ) h0
  obtain rfl : x = genericPoint (Spec (.of ℂ)) := Subsingleton.elim _ _
  rw [pointCycleClass_genericPoint_eq h0 hx hμ₀]
  exact deg_eq_one_of_isVarietyFundamentalClass_spec h0 hμ₀

end PointDegree

/-! ### Complex integrals and the Hodge forms -/

section ComplexIntegral

variable {Y : TopCat.{0}}

/-- A rational finite chain, with complex coefficients. -/
private noncomputable abbrev chainC {n : ℕ} (z : Chain ℚ Y n) : Chain ℂ Y n :=
  Finsupp.mapRange (algebraMap ℚ ℂ) (map_zero _) z

/-- Evaluation of complex cochains on a fixed complex chain, as a linear map in the cochain. -/
private noncomputable def evalAt {n : ℕ} (c : Chain ℂ Y n) : (Simplex Y n → ℂ) →ₗ[ℂ] ℂ where
  toFun φ := eval φ c
  map_add' φ ψ := by
    simp only [Finsupp.linearCombination_apply, Pi.add_apply, smul_add]
    exact Finsupp.sum_add
  map_smul' a φ := by
    simp only [Finsupp.linearCombination_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ ↦ by ring

/-- **Integration of complex classes over a rational cycle**: `[φ] ↦ ∑_σ φ(σ) z_σ`, which kills
coboundaries since `z` is a cycle. -/
private noncomputable def intCycle (m : ℕ) (z : Chain ℚ Y (m + 1)) (hz : bd ℚ m z = 0) :
    cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) Y Set.univ ((m + 1 : ℕ) : ℤ) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ _ ((evalAt (chainC z)).comp
      (relCocycles ℂ (Set.univᶜ : Set Y) (m + 1)).subtype) (by
    rintro ⟨φ, hφ⟩ ⟨ψ, -, hψ⟩
    change eval φ (chainC z) = 0
    have hφψ : φ = coboundary ℂ m ψ := hψ.symm
    rw [hφψ, eval_coboundary]
    have := bd_mapRange (algebraMap ℚ ℂ).toAddMonoidHom m z
    change eval ψ (bd ℂ m (chainC z)) = 0
    rw [show bd ℂ m (chainC z) = 0 from this.trans (by rw [hz]; exact Finsupp.mapRange_zero)]
    simp)).comp
    (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y) (m + 1)).toLinearMap

private lemma intCycle_ofCocycle (m : ℕ) (z : Chain ℚ Y (m + 1)) (hz : bd ℚ m z = 0)
    (φ : Simplex Y (m + 1) → ℂ) (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) (m + 1)) :
    intCycle m z hz (cohomologyWithSupports.ofCocycle ℂ Y (m + 1) φ hφ) = eval φ (chainC z) := by
  simp only [intCycle, cohomologyWithSupports.ofCocycle, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.liftQ_apply]
  rfl

private lemma eval_castCochain_chainC {n : ℕ} (φ : Simplex Y n → ℚ) (z : Chain ℚ Y n) :
    eval (fun σ ↦ (φ σ : ℂ)) (chainC z) = (eval φ z : ℂ) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [chainC] at hx hy ⊢
    rw [Finsupp.mapRange_add (fun _ _ ↦ map_add _ _ _), map_add, map_add, hx, hy, Rat.cast_add]
  | single σ q => simp

private lemma eval_conj_chainC {n : ℕ} (φ : Simplex Y n → ℂ) (z : Chain ℚ Y n) :
    eval (fun σ ↦ starRingEnd ℂ (φ σ)) (chainC z) = starRingEnd ℂ (eval φ (chainC z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [chainC] at hx hy ⊢
    rw [Finsupp.mapRange_add (fun _ _ ↦ map_add _ _ _), map_add, map_add, hx, hy, map_add]
  | single σ q => simp [mul_comm]

end ComplexIntegral

section ComplexIntegral2

variable {Y : TopCat.{0}}

private lemma intCycle_mapCoeff_conj (m : ℕ) (z : Chain ℚ Y (m + 1)) (hz : bd ℚ m z = 0)
    (x : cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) Y Set.univ ((m + 1 : ℕ) : ℤ)) :
    intCycle m z hz (MMP.Analytic.singularCohomology.mapCoeff (starRingEnd ℂ) (m + 1) x) =
      starRingEnd ℂ (intCycle m z hz x) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq (m + 1) x
  rw [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle, intCycle_ofCocycle, intCycle_ofCocycle]
  exact eval_conj_chainC φ z

private lemma mapCoeff_mapCoeff {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (n : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (n : ℤ)) :
    MMP.Analytic.singularCohomology.mapCoeff g n (MMP.Analytic.singularCohomology.mapCoeff f n x) =
      MMP.Analytic.singularCohomology.mapCoeff (g.comp f) n x := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq n x
  simp only [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle]
  rfl

private lemma mapCoeff_conj_conj (n : ℕ)
    (x : cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) Y Set.univ (n : ℤ)) :
    MMP.Analytic.singularCohomology.mapCoeff (starRingEnd ℂ) n
      (MMP.Analytic.singularCohomology.mapCoeff (starRingEnd ℂ) n x) = x := by
  rw [mapCoeff_mapCoeff]
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq n x
  rw [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle]
  exact cohomologyWithSupports.ofCocycle_congr (by ext; simp) _ _

variable [CompactSpace Y]

private lemma intCycle_mapCoeff_rat (m : ℕ) (z : Chain ℚ Y (m + 1)) (hz : bd ℚ m z = 0)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y Set.univ ((m + 1 : ℕ) : ℤ)) :
    intCycle m z hz (MMP.Analytic.singularCohomology.mapCoeff (algebraMap ℚ ℂ) (m + 1) x) =
      (kron Y (m + 1) x ((homologyEquiv ℚ Y (m + 1)).symm (Submodule.Quotient.mk
          ⟨borelMooreHomology.ofFinsupp z, ofFinsupp_mem_cyc m z hz⟩)) : ℂ) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq (m + 1) x
  rw [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle, intCycle_ofCocycle,
    kron_ofCocycle_ofFinsupp m φ hφ z hz]
  exact eval_castCochain_chainC φ z

/-- Every class in the homology of a compact space is the class of a finite cycle. -/
private lemma exists_finite_cycle (m : ℕ)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y ((m + 1 : ℕ) : ℤ)) :
    ∃ (z : Chain ℚ Y (m + 1)) (hz : bd ℚ m z = 0),
      (homologyEquiv ℚ Y (m + 1)).symm (Submodule.Quotient.mk
        ⟨borelMooreHomology.ofFinsupp z, ofFinsupp_mem_cyc m z hz⟩) = μ := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv ℚ Y (m + 1) μ)
  have hfc := finite_support_coeff c.1
  set z := borelMooreHomology.toFinsupp c.1 hfc
  have hz' : borelMooreHomology.ofFinsupp z = c.1 := borelMooreHomology.ofFinsupp_toFinsupp _ hfc
  have hz : bd ℚ m z = 0 := by
    apply BorelMooreCap.ofFinsupp_injective
    have h1 := borelMooreHomology.d_ofFinsupp (R := ℚ) (X := Y) z
    rw [hz'] at h1
    have h2 := (mem_cyc_iff _).1 c.2
    exact h1.symm.trans (h2.trans rfl)
  have hcz : (⟨borelMooreHomology.ofFinsupp z, ofFinsupp_mem_cyc m z hz⟩ :
      Cyc (R := ℚ) Y (m + 1)) = c := Subtype.ext hz'
  refine ⟨z, hz, ?_⟩
  refine ((homologyEquiv ℚ Y (m + 1)).symm_apply_eq).2 (Eq.trans ?_ hc)
  congr 1

end ComplexIntegral2

section CupCoeff

variable {Y : TopCat.{0}}

private lemma mapCoeff_cupNatUniv {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i j : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (i : ℤ))
    (y : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (j : ℤ)) :
    MMP.Analytic.singularCohomology.mapCoeff f (i + j) (MMP.cupNatUniv R Y i j x y) =
      MMP.cupNatUniv S Y i j (MMP.Analytic.singularCohomology.mapCoeff f i x)
        (MMP.Analytic.singularCohomology.mapCoeff f j y) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq i x
  obtain ⟨ψ, hψ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq j y
  simp only [MMP.Analytic.singularCohomology.mapCoeff_ofCocycle,
    MMP.cupNatUniv_ofCocycle Y i j _ _,
    MMP.Analytic.singularCohomology.mapCoeff_ofCocycle]
  exact cohomologyWithSupports.ofCocycle_congr (by ext σ; simp [cup_apply, map_mul]) _ _

end CupCoeff

section DeRhamLinear

open MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

/-- Evaluation of sections over `U` at a `ℂ`-point of `U`, as a ring homomorphism. -/
private noncomputable def evalHom (U : V.Opens)
    (x : ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) : Γ(V, U) →+* ℂ :=
  (x.1.hom.appLE U ⊤ x.2.ge ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom

private lemma eval_eq_evalHom (U : V.Opens) (f : Γ(V, U))
    (x : ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) :
    ComplexPoints.eval U f x = evalHom U x f := rfl

private lemma evalHom_algebraMap (U : V.Opens)
    (x : ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) (c : ℂ) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
    evalHom U x (algebraMap ℂ Γ(V, U) c) = c := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
  have key : ∀ (e₁ : U ≤ (V ↘ Spec (.of ℂ)) ⁻¹ᵁ ⊤) (e₂ : ⊤ ≤ x.1.hom ⁻¹ᵁ U),
      (V ↘ Spec (.of ℂ)).appLE ⊤ U e₁ ≫ x.1.hom.appLE U ⊤ e₂ = 𝟙 _ := by
    intro e₁ e₂
    rw [Scheme.Hom.appLE_comp_appLE]
    have h : x.1.hom ≫ (V ↘ Spec (.of ℂ)) = 𝟙 _ := x.1.2
    have hid : ∀ (g : Spec (.of ℂ) ⟶ Spec (.of ℂ)) (_ : g = 𝟙 _) (e : (⊤ : (Spec (.of ℂ)).Opens) ≤ g ⁻¹ᵁ ⊤),
        g.appLE ⊤ ⊤ e = 𝟙 _ := by
      rintro g rfl e
      erw [Scheme.Hom.appLE_eq_app]
      simp
    exact hid _ h _
  have e : evalHom U x (algebraMap ℂ Γ(V, U) c) =
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ ((V ↘ Spec (.of ℂ)).appLE ⊤ U (by simp) ≫
        x.1.hom.appLE U ⊤ x.2.ge) ≫ (Scheme.ΓSpecIso (.of ℂ)).hom).hom c := rfl
  rw [e]
  erw [key]
  simp

/-- **The line integrand of a Kähler differential does not depend on its presentation.** Let
`γ` be a path of `ℂ`-points of `U` along which every section is differentiable at `t`. Two
presentations `∑ fⱼ dgⱼ = ∑ f'ₖ dg'ₖ` of the same form give the same value
`∑ fⱼ(γ t) (gⱼ ∘ γ)'(t)`: the map `h ↦ (h ∘ γ)'(t)` is a derivation into `ℂ`, through the
evaluation at `γ t`, so it factors through the Kähler differentials. -/
private theorem sum_eval_mul_deriv_eq (U : V.Opens)
    (γ : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) (t : ℝ)
    (hd : ∀ h : Γ(V, U), DifferentiableAt ℝ (fun s ↦ evalHom U (γ s) h) t)
    {m m' : ℕ} (f g : Fin m → Γ(V, U)) (f' g' : Fin m' → Γ(V, U))
    (heq : letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
      ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1 (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j)) =
        ∑ k, f' k • exteriorPower.ιMulti Γ(V, U) 1
          (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g' k))) :
    ∑ j, evalHom U (γ t) (f j) * deriv (fun s ↦ evalHom U (γ s) (g j)) t =
      ∑ k, evalHom U (γ t) (f' k) * deriv (fun s ↦ evalHom U (γ s) (g' k)) t := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
  letI : Module Γ(V, U) ℂ := (evalHom U (γ t)).toModule
  have hsmul : ∀ (a : Γ(V, U)) (z : ℂ), a • z = evalHom U (γ t) a * z := fun _ _ ↦ rfl
  haveI : IsScalarTower ℂ Γ(V, U) ℂ := ⟨fun c a z ↦ by
    rw [hsmul, hsmul, Algebra.smul_def, map_mul, evalHom_algebraMap, smul_eq_mul]
    ring⟩
  let δ : Γ(V, U) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ deriv (fun s ↦ evalHom U (γ s) h) t
      map_add' := fun a b ↦ by
        simp only [map_add]
        exact deriv_add (hd a) (hd b)
      map_smul' := fun c a ↦ by
        simp only [Algebra.smul_def, map_mul, evalHom_algebraMap, RingHom.id_apply, smul_eq_mul]
        exact congrFun (deriv_const_mul_field' c) t }
  let d : Derivation ℂ Γ(V, U) ℂ := Derivation.mk' δ fun a b ↦ by
    change deriv (fun s ↦ evalHom U (γ s) (a * b)) t =
      evalHom U (γ t) a * deriv (fun s ↦ evalHom U (γ s) b) t +
        evalHom U (γ t) b * deriv (fun s ↦ evalHom U (γ s) a) t
    simp only [map_mul]
    rw [deriv_fun_mul (hd a) (hd b)]
    ring
  have hL : ∀ (n : ℕ) (f g : Fin n → Γ(V, U)),
      (d.liftKaehlerDifferential ∘ₗ (exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ]).toLinearMap)
        (∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
          (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) =
      ∑ j, evalHom U (γ t) (f j) * deriv (fun s ↦ evalHom U (γ s) (g j)) t := fun n f g ↦ by
    simp only [map_sum, map_smul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      exteriorPower.oneEquiv_ιMulti, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  rw [← hL, heq, hL]

section Analysis

/-- A `C¹` function on `[0, 1]` is differentiable at interior points. -/
private lemma differentiableAt_of_contDiffOn {F : ℝ → ℂ} (hF : ContDiffOn ℝ 1 F (Set.Icc 0 1))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : DifferentiableAt ℝ F t :=
  (hF.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds ht.1 ht.2)

/-- The line integrand `G · F'` of a continuous `G` and a `C¹` function `F` on `[0, 1]` is
integrable. -/
private lemma intervalIntegrable_mul_deriv {F G : ℝ → ℂ} (hF : ContDiffOn ℝ 1 F (Set.Icc 0 1))
    (hG : ContinuousOn G (Set.Icc 0 1)) :
    IntervalIntegrable (fun t ↦ G t * deriv F t) MeasureTheory.volume 0 1 := by
  have hc : ContinuousOn (fun t ↦ G t * derivWithin F (Set.Icc 0 1) t) (Set.Icc 0 1) :=
    hG.mul (hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)
  have hi := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (zero_le_one' ℝ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at hi ⊢
  refine hi.congr_fun_ae ?_
  have h1 : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := MeasureTheory.Measure.ae_ne _ _
  filter_upwards [MeasureTheory.ae_restrict_of_ae h1, MeasureTheory.ae_restrict_mem measurableSet_Ioc]
    with t ht1 ht
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]

end Analysis

section DeRham

variable (V) in
/-- The de Rham class predicate of `MMP.Analytic.hodgeDecomposition_one_of_isProjectiveVariety`:
`α` is the class of a cocycle whose values on smooth chart `1`-simplices are the line integrals
of `ω`. -/
private def IsDeRhamClass'
    (ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (α : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) : Prop :=
  ∃ (φ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1 → ℂ)
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set (Analytification.space (V ↘ Spec (.of ℂ)))) 1),
    α = cohomologyWithSupports.ofCocycle ℂ _ 1 φ hφ ∧
    ∀ (U : V.affineOpens) (m : ℕ) (f g : Fin m → Γ(V, U)),
      (letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens);
        MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
          (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) →
      ∀ (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
        (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) (U : V.Opens)),
        (∀ h : Γ(V, U), ContDiffOn ℝ 1 (fun t : ℝ ↦ ComplexPoints.eval (U : V.Opens) h
          ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)),
            hσ _⟩) (Set.Icc 0 1)) →
        φ σ = ∫ t in (0 : ℝ)..1, ∑ j,
          ComplexPoints.eval (U : V.Opens) (f j)
            ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)),
              hσ _⟩ *
          deriv (fun s : ℝ ↦ ComplexPoints.eval (U : V.Opens) (g j)
            ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one s)),
              hσ _⟩) t

/-- Every algebraic `1`-form on an affine open is a finite sum `∑ fⱼ dgⱼ`. -/
private lemma exists_presentation (U : V.Opens)
    (w : letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
      ⋀[Γ(V, U)]^1 Ω[Γ(V, U)⁄ℂ]) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
    ∃ (m : ℕ) (f g : Fin m → Γ(V, U)), w = ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
      (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j)) := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
  classical
  have hx : exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ] w ∈
      Submodule.span Γ(V, U) (Set.range (KaehlerDifferential.D ℂ Γ(V, U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  let e := c.support.equivFin
  refine ⟨c.support.card, fun j ↦ c (e.symm j), fun j ↦ (e.symm j : Γ(V, U)), ?_⟩
  apply (exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ]).injective
  rw [← hc, map_sum]
  simp only [map_smul, exteriorPower.oneEquiv_ιMulti]
  rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact (Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl).symm

end DeRham

section Closure

/-- The path `t ↦ σ(t)` of `ℂ`-points of `U` traced by a chart `1`-simplex. -/
private noncomputable abbrev simplexPath (U : V.Opens) (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
    (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) (t : ℝ) :
    ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U :=
  ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)), hσ _⟩

/-- The line integral `∫₀¹ ∑ fⱼ(σ t) (gⱼ ∘ σ)'(t) dt` of a presentation along a simplex. -/
private noncomputable def lineIntegral (U : V.Opens)
    (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
    (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) {m : ℕ}
    (f g : Fin m → Γ(V, U)) : ℂ :=
  ∫ t in (0 : ℝ)..1, ∑ j, ComplexPoints.eval U (f j) (simplexPath U σ hσ t) *
    deriv (fun s : ℝ ↦ ComplexPoints.eval U (g j) (simplexPath U σ hσ s)) t

private lemma lineIntegral_congr (U : V.Opens)
    (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
    (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U)
    (hsm : ∀ h : Γ(V, U), ContDiffOn ℝ 1
      (fun t : ℝ ↦ ComplexPoints.eval U h (simplexPath U σ hσ t)) (Set.Icc 0 1))
    {m m' : ℕ} (f g : Fin m → Γ(V, U)) (f' g' : Fin m' → Γ(V, U))
    (heq : letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
      ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1 (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j)) =
        ∑ k, f' k • exteriorPower.ιMulti Γ(V, U) 1
          (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g' k))) :
    lineIntegral U σ hσ f g = lineIntegral U σ hσ f' g' := by
  refine intervalIntegral.integral_congr_ae ?_
  have h1 : ∀ᵐ t ∂MeasureTheory.volume, t ≠ (1 : ℝ) := MeasureTheory.Measure.ae_ne _ _
  filter_upwards [h1] with t ht1 ht
  rw [Set.uIoc_of_le (zero_le_one' ℝ)] at ht
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  exact sum_eval_mul_deriv_eq U (simplexPath U σ hσ) t
    (fun h ↦ differentiableAt_of_contDiffOn (hsm h) ht') f g f' g' heq

private lemma lineIntegral_append (U : V.Opens)
    (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
    (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U)
    (hsm : ∀ h : Γ(V, U), ContDiffOn ℝ 1
      (fun t : ℝ ↦ ComplexPoints.eval U h (simplexPath U σ hσ t)) (Set.Icc 0 1))
    {m m' : ℕ} (f g : Fin m → Γ(V, U)) (f' g' : Fin m' → Γ(V, U)) :
    lineIntegral U σ hσ (Fin.append f f') (Fin.append g g') =
      lineIntegral U σ hσ f g + lineIntegral U σ hσ f' g' := by
  have hint : ∀ (n : ℕ) (f g : Fin n → Γ(V, U)), IntervalIntegrable
      (fun t ↦ ∑ j, ComplexPoints.eval U (f j) (simplexPath U σ hσ t) *
        deriv (fun s : ℝ ↦ ComplexPoints.eval U (g j) (simplexPath U σ hσ s)) t)
      MeasureTheory.volume 0 1 := fun n f g ↦ by
    have := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (Finset.univ : Finset (Fin n))
      (f := fun j t ↦ ComplexPoints.eval U (f j) (simplexPath U σ hσ t) *
        deriv (fun s : ℝ ↦ ComplexPoints.eval U (g j) (simplexPath U σ hσ s)) t)
      fun j _ ↦ intervalIntegrable_mul_deriv (hsm (g j)) ((hsm (f j)).continuousOn)
    refine this.congr fun t _ ↦ ?_
    simp [Finset.sum_apply]
  unfold lineIntegral
  rw [← intervalIntegral.integral_add (hint m f g) (hint m' f' g')]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

end Closure

section DeRhamClosure

private lemma ofCocycle_add {Y : TopCat.{0}} {n : ℕ} (φ ψ : Simplex Y n → ℂ)
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) n) (hψ : ψ ∈ relCocycles ℂ (Set.univᶜ : Set Y) n) :
    cohomologyWithSupports.ofCocycle ℂ Y n (φ + ψ) (add_mem hφ hψ) =
      cohomologyWithSupports.ofCocycle ℂ Y n φ hφ + cohomologyWithSupports.ofCocycle ℂ Y n ψ hψ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_add]; rfl

private lemma ofCocycle_smul {Y : TopCat.{0}} {n : ℕ} (c : ℂ) (φ : Simplex Y n → ℂ)
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) n) :
    cohomologyWithSupports.ofCocycle ℂ Y n (c • φ) (Submodule.smul_mem _ c hφ) =
      c • cohomologyWithSupports.ofCocycle ℂ Y n φ hφ := by
  simp only [cohomologyWithSupports.ofCocycle, ← map_smul]; rfl

private lemma ofCocycle_zero {Y : TopCat.{0}} {n : ℕ} :
    cohomologyWithSupports.ofCocycle ℂ Y n 0 (zero_mem _) = 0 := by
  simp only [cohomologyWithSupports.ofCocycle]
  rw [show (⟨0, zero_mem _⟩ : relCocycles ℂ (Set.univᶜ : Set Y) n) = 0 from rfl,
    Submodule.Quotient.mk_zero, map_zero]

set_option maxRecDepth 10000 in
/-- De Rham classes are additive in the form. -/
private theorem isDeRhamClass_add
    {ω ω' : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α α' : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1}
    (h : IsDeRhamClass' V ω α) (h' : IsDeRhamClass' V ω' α') :
    IsDeRhamClass' V (ω + ω') (α + α') := by
  obtain ⟨φ, hφ, rfl, H⟩ := h
  obtain ⟨φ', hφ', rfl, H'⟩ := h'
  refine ⟨φ + φ', add_mem hφ hφ', (ofCocycle_add φ φ' hφ hφ').symm,
    fun U m f g hrep σ hσ hsm ↦ ?_⟩
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  obtain ⟨m1, f1, g1, h1⟩ := exists_presentation (U : V.Opens)
    (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
      (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω))
  obtain ⟨m2, f2, g2, h2⟩ := exists_presentation (U : V.Opens)
    (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
      (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω'))
  have e1 := H U m1 f1 g1 h1 σ hσ hsm
  have e2 := H' U m2 f2 g2 h2 σ hσ hsm
  change φ σ + φ' σ = lineIntegral (U : V.Opens) σ hσ f g
  rw [e1, e2]
  change lineIntegral (U : V.Opens) σ hσ f1 g1 + lineIntegral (U : V.Opens) σ hσ f2 g2 = _
  rw [← lineIntegral_append (U : V.Opens) σ hσ hsm]
  refine lineIntegral_congr (U : V.Opens) σ hσ hsm _ _ _ _ ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← h1, ← h2, ← hrep, ← map_add, ← map_add]

/-- The zero form has the zero class. -/
private theorem isDeRhamClass_zero : IsDeRhamClass' V 0 0 := by
  refine ⟨0, zero_mem _, ofCocycle_zero.symm, fun U m f g hrep σ hσ hsm ↦ ?_⟩
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  change 0 = lineIntegral (U : V.Opens) σ hσ f g
  rw [lineIntegral_congr (U : V.Opens) σ hσ hsm f g (Fin.elim0 : Fin 0 → Γ(V, U)) Fin.elim0
    (by rw [← hrep, map_zero, map_zero]; simp)]
  simp [lineIntegral]

private lemma presheaf_map_algebraMap (U : V.Opens) (c : ℂ) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (⊤ : V.Opens)
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
    V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (algebraMap ℂ Γ(V, ⊤) c) =
      algebraMap ℂ Γ(V, U) c := by
  change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (V ↘ Spec (.of ℂ)).appLE ⊤ ⊤ _ ≫
    V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom c =
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (V ↘ Spec (.of ℂ)).appLE ⊤ U _).hom c
  rw [Scheme.Hom.appLE_map]

set_option maxRecDepth 10000 in
/-- De Rham classes are `ℂ`-linear in the form. -/
private theorem isDeRhamClass_smul
    {ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (h : IsDeRhamClass' V ω α) (c : ℂ) :
    ∃ ω', IsDeRhamClass' V ω' (c • α) := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (⊤ : V.Opens)
  obtain ⟨φ, hφ, rfl, H⟩ := h
  refine ⟨algebraMap ℂ Γ(V, ⊤) c • ω, c • φ, Submodule.smul_mem _ c hφ,
    (ofCocycle_smul c φ hφ).symm, fun U m f g hrep σ hσ hsm ↦ ?_⟩
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  obtain ⟨m1, f1, g1, h1⟩ := exists_presentation (U : V.Opens)
    (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
      (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω))
  have e1 := H U m1 f1 g1 h1 σ hσ hsm
  change c * φ σ = lineIntegral (U : V.Opens) σ hσ f g
  rw [e1]
  change c * lineIntegral (U : V.Opens) σ hσ f1 g1 = _
  have hc : c * lineIntegral (U : V.Opens) σ hσ f1 g1 =
      lineIntegral (U : V.Opens) σ hσ (fun j ↦ algebraMap ℂ Γ(V, U) c * f1 j) g1 := by
    unfold lineIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [Finset.mul_sum, eval_eq_evalHom, map_mul, evalHom_algebraMap, mul_assoc]
  rw [hc]
  refine lineIntegral_congr (U : V.Opens) σ hσ hsm _ _ _ _ ?_
  rw [← hrep]
  have hres : ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE (le_top : (U : V.Opens) ≤ ⊤)).op (algebraMap ℂ Γ(V, ⊤) c • ω) =
      (V.presheaf.map (homOfLE (le_top : (U : V.Opens) ≤ ⊤)).op (algebraMap ℂ Γ(V, ⊤) c)) •
        ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : (U : V.Opens) ≤ ⊤)).op ω :=
    Stacks.ProjectiveFromSections.resM_smul le_top _ _
  rw [hres, presheaf_map_algebraMap, map_smul, h1, Finset.smul_sum]
  simp only [smul_smul]

end DeRhamClosure

end DeRhamLinear

section HodgePackage

open MMP.Analytic

variable (V : Scheme.{0}) [V.Over (Spec (.of ℂ))]

/-- The holomorphic classes `H^{1,0}(V)`: the de Rham classes of global `1`-forms. -/
private noncomputable def holClasses :
    Submodule ℂ (analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) where
  carrier := {α | ∃ ω, IsDeRhamClass' V ω α}
  add_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ ↦ ⟨_, isDeRhamClass_add h h'⟩
  zero_mem' := ⟨0, isDeRhamClass_zero⟩
  smul_mem' := fun c _ ⟨_, h⟩ ↦ isDeRhamClass_smul h c

/-- Complex conjugation of coefficients on `H¹(V^an; ℂ)`. -/
private noncomputable abbrev conjH :
    analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →+
      analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 :=
  (singularCohomology.mapCoeff (Y := Analytification.space (V ↘ Spec (.of ℂ)))
    (starRingEnd ℂ) 1).toAddMonoidHom

variable {V}

set_option maxRecDepth 10000 in
private lemma hodge_decomposition {n : ℕ} (hn : n = 1 ∨ n = 2)
    [AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension n (V ↘ Spec (.of ℂ))]
    (a : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) :
    ∃ h ∈ holClasses V, ∃ h' ∈ holClasses V, a = h + conjH V h' := by
  have H := hodgeDecomposition_one_of_isProjectiveVariety hn (X := V)
  obtain ⟨⟨ω, η⟩, ⟨x, y, hx, hy, hxy⟩, -⟩ := H.2.2.1 a
  exact ⟨x, ⟨ω, hx⟩, y, ⟨η, hy⟩, hxy⟩

end HodgePackage

section HodgeForms

open MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

/-- The surface form `(a, b) ↦ ∫ a ∪ b ∪ c` on `H¹(V^an; ℂ)`, integrated over a rational
`4`-cycle `z`. -/
private noncomputable def surfaceForm (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (3 + 1))
    (hz : bd ℚ 3 z = 0) (c : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 2) :
    analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →ₗ[ℂ]
      analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →ₗ[ℂ] ℂ :=
  (MMP.cupNatUniv ℂ (Analytification.space (V ↘ Spec (.of ℂ))) 1 1).compr₂
    ((intCycle 3 z hz).comp
      ((MMP.cupNatUniv ℂ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1) 2).flip c))

/-- The curve form `(a, b) ↦ ∫ a ∪ b` on `H¹(V^an; ℂ)`, integrated over a rational `2`-cycle. -/
private noncomputable def curveForm (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1))
    (hz : bd ℚ 1 z = 0) :
    analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →ₗ[ℂ]
      analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →ₗ[ℂ] ℂ :=
  (MMP.cupNatUniv ℂ (Analytification.space (V ↘ Spec (.of ℂ))) 1 1).compr₂
    (intCycle 1 z hz)

private lemma surfaceForm_apply (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (3 + 1))
    (hz : bd ℚ 3 z = 0) (c : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 2)
    (a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) :
    surfaceForm z hz c a b = intCycle 3 z hz
      (MMP.cupNatUniv ℂ _ (1 + 1) 2
        (MMP.cupNatUniv ℂ _ 1 1 a b) c) := rfl

private lemma curveForm_apply (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1))
    (hz : bd ℚ 1 z = 0) (a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) :
    curveForm z hz a b = intCycle 1 z hz (MMP.cupNatUniv ℂ _ 1 1 a b) := rfl

/-- The product `a ∪ b ∪ c` in the cohomology ring is the homogeneous class in degree four. -/
private lemma of_mul_of_mul_of (a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1)
    (c : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 2) :
    (DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
        (Analytification.space (V ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) 1 a *
      DirectSum.of _ 1 b * DirectSum.of _ 2 c : CohomologyRing ℂ _) =
      DirectSum.of _ ((1 + 1) + 2) (MMP.cupNatUniv ℂ _ (1 + 1) 2
        (MMP.cupNatUniv ℂ _ 1 1 a b) c) := by
  rw [CohomologyRing.of_mul_of, CohomologyRing.of_mul_of]

end HodgeForms

section HodgeProps

open MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

private lemma of_injective_eq {i : ℕ}
    {x y : cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) (Analytification.space (V ↘ Spec (.of ℂ)))
      Set.univ (i : ℕ)}
    (h : (DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
      (Analytification.space (V ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) i x : CohomologyRing ℂ _) =
      DirectSum.of _ i y) : x = y :=
  DirectSum.of_injective i h

set_option maxRecDepth 10000 in
/-- **Holomorphic classes pair to zero by type** on a surface. -/
private lemma surfaceForm_hol [AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (V ↘ Spec (.of ℂ))]
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (3 + 1)) (hz : bd ℚ 3 z = 0)
    (L : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L]
    {a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1}
    (ha : a ∈ holClasses V) (hb : b ∈ holClasses V) :
    surfaceForm z hz (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
      (algebraicFirstChernClass L)) a b = 0 := by
  have h4 := (hodgeDecomposition_one_of_isProjectiveVariety (n := 2) (Or.inr rfl)
    (X := V)).2.2.2.1 a b ha hb L
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h4
  rw [of_mul_of_mul_of] at h4
  have h0 := of_injective_eq (V := V) (h4.trans (map_zero (DirectSum.of _ ((1 + 1) + 2))).symm)
  rw [surfaceForm_apply]
  erw [h0]
  exact map_zero _

end HodgeProps

section HodgeProps2

open MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

private lemma smul_of {i : ℕ} (r : ℂ)
    (x : cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) (Analytification.space (V ↘ Spec (.of ℂ)))
      Set.univ (i : ℕ)) :
    r • (DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
      (Analytification.space (V ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) i x : CohomologyRing ℂ _) =
      DirectSum.of _ i (r • x) := by
  rw [← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, map_smul]

set_option maxRecDepth 10000 in
/-- **Positivity of the surface form on holomorphic classes**: `i ∫ h ∪ h̄ ∪ c₁(L) > 0` for an
ample `L` with `∫ c₁(L)² > 0`. -/
private lemma surfaceForm_pos [AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (V ↘ Spec (.of ℂ))]
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (3 + 1)) (hz : bd ℚ 3 z = 0)
    (L : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L)
    (hd : ∃ d : ℝ, 0 < d ∧ intCycle 3 z hz (MMP.cupNatUniv ℂ _ 2 2
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))) = d)
    {h : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (hh : h ∈ holClasses V)
    (h0 : h ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ Complex.I * surfaceForm z hz (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
      (algebraicFirstChernClass L)) h (conjH V h) = t := by
  obtain ⟨ω, hω⟩ := hh
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact h0 (((hodgeDecomposition_one_of_isProjectiveVariety (n := 2) (Or.inr rfl)
      (X := V)).2.1 0).unique hω isDeRhamClass_zero)
  obtain ⟨t, ht, heq⟩ := (hodgeDecomposition_one_of_isProjectiveVariety (n := 2) (Or.inr rfl)
    (X := V)).2.2.2.2.1 ω h hω0 hω L hL
  obtain ⟨d, hd0, hdd⟩ := hd
  set c := singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, sq] at heq
  change Complex.I • (DirectSum.of _ 1 h * DirectSum.of _ 1 (conjH V h) * DirectSum.of _ 2 c :
    CohomologyRing ℂ _) = (t : ℂ) • (DirectSum.of _ 2 c * DirectSum.of _ 2 c) at heq
  rw [of_mul_of_mul_of, CohomologyRing.of_mul_of, smul_of, smul_of] at heq
  have heq' := of_injective_eq (V := V) (i := 4) heq
  refine ⟨t * d, mul_pos ht hd0, ?_⟩
  rw [surfaceForm_apply, ← smul_eq_mul, ← map_smul]
  erw [heq', map_smul, hdd]
  push_cast
  rfl

end HodgeProps2

section HodgeProps3

open MMP.Analytic

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

/-- An integral class is real: conjugation fixes its image in complex cohomology. -/
private lemma mapCoeff_conj_intCast {Y : TopCat.{0}} (n : ℕ)
    (c : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) Y Set.univ (n : ℤ)) :
    singularCohomology.mapCoeff (starRingEnd ℂ) n (singularCohomology.mapCoeff (Int.castRingHom ℂ) n c) =
      singularCohomology.mapCoeff (Int.castRingHom ℂ) n c := by
  rw [mapCoeff_mapCoeff, show (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from
    RingHom.ext_int _ _]

set_option maxRecDepth 10000 in
/-- The surface form is real: it commutes with conjugation. -/
private lemma surfaceForm_conj
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (3 + 1)) (hz : bd ℚ 3 z = 0)
    (c₀ : cohomologyWithSupports ℤ (ModuleCat.of ℤ ℤ) (Analytification.space (V ↘ Spec (.of ℂ)))
      Set.univ ((2 : ℕ) : ℤ))
    (a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) :
    surfaceForm z hz (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c₀) (conjH V a) (conjH V b) =
      starRingEnd ℂ (surfaceForm z hz (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c₀) a b) := by
  rw [surfaceForm_apply, surfaceForm_apply]
  have h1 := mapCoeff_cupNatUniv (Y := Analytification.space (V ↘ Spec (.of ℂ)))
    (starRingEnd ℂ) 1 1 a b
  have h2 := mapCoeff_cupNatUniv (Y := Analytification.space (V ↘ Spec (.of ℂ)))
    (starRingEnd ℂ) (1 + 1) 2 (MMP.cupNatUniv ℂ _ 1 1 a b)
    (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c₀)
  rw [mapCoeff_conj_intCast] at h2
  change intCycle 3 z hz (MMP.cupNatUniv ℂ _ (1 + 1) 2
    (MMP.cupNatUniv ℂ _ 1 1 (singularCohomology.mapCoeff (starRingEnd ℂ) 1 a)
      (singularCohomology.mapCoeff (starRingEnd ℂ) 1 b))
    (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 c₀)) = _
  rw [← h1, ← h2]
  exact intCycle_mapCoeff_conj 3 z hz _

set_option maxRecDepth 10000 in
/-- The curve form is real. -/
private lemma curveForm_conj
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1)) (hz : bd ℚ 1 z = 0)
    (a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) :
    curveForm z hz (conjH V a) (conjH V b) = starRingEnd ℂ (curveForm z hz a b) := by
  rw [curveForm_apply, curveForm_apply]
  have h1 := mapCoeff_cupNatUniv (Y := Analytification.space (V ↘ Spec (.of ℂ)))
    (starRingEnd ℂ) 1 1 a b
  change intCycle 1 z hz (MMP.cupNatUniv ℂ _ 1 1
    (singularCohomology.mapCoeff (starRingEnd ℂ) 1 a)
      (singularCohomology.mapCoeff (starRingEnd ℂ) 1 b)) = _
  rw [← h1]
  exact intCycle_mapCoeff_conj 1 z hz _

set_option maxRecDepth 10000 in
/-- **Holomorphic classes pair to zero by type** on a curve. -/
private lemma curveForm_hol [AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (.of ℂ))]
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1)) (hz : bd ℚ 1 z = 0)
    (L : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L]
    {a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1}
    (ha : a ∈ holClasses V) (hb : b ∈ holClasses V) : curveForm z hz a b = 0 := by
  have h4 := (hodgeDecomposition_one_of_isProjectiveVariety (n := 1) (Or.inl rfl)
    (X := V)).2.2.2.1 a b ha hb L
  simp only [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, mul_one] at h4
  rw [CohomologyRing.of_mul_of] at h4
  have h0 := of_injective_eq (V := V) (h4.trans (map_zero (DirectSum.of _ (1 + 1))).symm)
  rw [curveForm_apply]
  erw [h0]
  exact map_zero _

set_option maxRecDepth 10000 in
/-- **Non-negativity of the curve form on holomorphic classes**: `i ∫ h ∪ h̄ ≥ 0`. -/
private lemma curveForm_nonneg [AlgebraicGeometry.IsProjectiveVariety ℂ (V ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 1 (V ↘ Spec (.of ℂ))]
    (z : Chain ℚ (Analytification.space (V ↘ Spec (.of ℂ))) (1 + 1)) (hz : bd ℚ 1 z = 0)
    (L : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L)
    (hd : ∃ d : ℝ, 0 < d ∧ intCycle 1 z hz
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) = d)
    {h : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (hh : h ∈ holClasses V) :
    ∃ t : ℝ, 0 ≤ t ∧ Complex.I * curveForm z hz h (conjH V h) = t := by
  by_cases h0 : h = 0
  · exact ⟨0, le_rfl, by rw [h0]; simp⟩
  obtain ⟨ω, hω⟩ := hh
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact h0 (((hodgeDecomposition_one_of_isProjectiveVariety (n := 1) (Or.inl rfl)
      (X := V)).2.1 0).unique hω isDeRhamClass_zero)
  obtain ⟨t, ht, heq⟩ := (hodgeDecomposition_one_of_isProjectiveVariety (n := 1) (Or.inl rfl)
    (X := V)).2.2.2.2.1 ω h hω0 hω L hL
  obtain ⟨d, hd0, hdd⟩ := hd
  set c := singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)
  simp only [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, mul_one, pow_one] at heq
  change Complex.I • (DirectSum.of _ 1 h * DirectSum.of _ 1 (conjH V h) : CohomologyRing ℂ _) =
    (t : ℂ) • DirectSum.of _ 2 c at heq
  rw [CohomologyRing.of_mul_of, smul_of, smul_of] at heq
  have heq' := of_injective_eq (V := V) (i := 2) heq
  refine ⟨t * d, (mul_pos ht hd0).le, ?_⟩
  rw [curveForm_apply, ← smul_eq_mul, ← map_smul]
  erw [heq', map_smul, hdd]
  push_cast
  rfl

end HodgeProps3

section HodgeRadical

open MMP.Analytic

/-- Cup products of degree-one classes anticommute. -/
private lemma cupNatUniv_one_one_comm {R : Type} [CommRing R] (Y : TopCat.{0})
    (a b : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ ((1 : ℕ) : ℤ)) :
    MMP.cupNatUniv R Y 1 1 b a = - MMP.cupNatUniv R Y 1 1 a b := by
  have hc := cohomologyWithSupports.cup_comm R Y isClosed_univ isClosed_univ
    ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) a b
  simp only [MMP.cupNatUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
  have hs : (((-1 : Rˣ) ^ (((1 : ℕ) : ℤ) * ((1 : ℕ) : ℤ)) : Rˣ) : R) = -1 := by norm_num
  rw [hs, neg_one_smul] at hc
  rw [← map_neg, ← hc, cohomologyWithSupports.congrIndex_congrIndex]

/-- Rational degree-one classes of a compact space are determined by their complex images. -/
private lemma injective_mapCoeff_rat_one {Y : TopCat.{0}} [CompactSpace Y] :
    Function.Injective (singularCohomology.mapCoeff (Y := Y) (algebraMap ℚ ℂ) (0 + 1)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ eq_zero_of_forall_kron_eq_zero 0 x fun b ↦ ?_
  obtain ⟨z, hz, rfl⟩ := exists_finite_cycle 0 b
  have h := intCycle_mapCoeff_rat 0 z hz x
  rw [hx, map_zero] at h
  exact_mod_cast h.symm

/-- The class in `H_{m+1}(Y; ℚ)` of a finite rational cycle. -/
private noncomputable abbrev cycleClass {Y : TopCat.{0}} [CompactSpace Y] (m : ℕ) (z : Chain ℚ Y (m + 1))
    (hz : bd ℚ m z = 0) : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y ((m + 1 : ℕ) : ℤ) :=
  (homologyEquiv ℚ Y (m + 1)).symm (Submodule.Quotient.mk
    ⟨borelMooreHomology.ofFinsupp z, ofFinsupp_mem_cyc m z hz⟩)

/-- Rational `H¹` of the analytic space of a complex scheme. -/
private abbrev H1Q (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] : Type :=
  cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (Analytification.space (V ↘ Spec (.of ℂ))) Set.univ
    ((1 : ℕ) : ℤ)

/-- Pull-back of rational `H¹` along the analytification of a morphism over `ℂ`. -/
private noncomputable abbrev pullH1 {V V' : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [V'.Over (Spec (.of ℂ))] (f : V' ⟶ V) (hf : f ≫ (V ↘ Spec (.of ℂ)) = V' ↘ Spec (.of ℂ)) :
    H1Q V →ₗ[ℚ] H1Q V' :=
  (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
    Set.univ ((1 : ℕ) : ℤ)).hom

/-- Pull-back of complex `H¹` along the analytification of a morphism over `ℂ`. -/
private noncomputable abbrev pullH1C {V V' : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [V'.Over (Spec (.of ℂ))] (f : V' ⟶ V) (hf : f ≫ (V ↘ Spec (.of ℂ)) = V' ↘ Spec (.of ℂ)) :
    analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →ₗ[ℂ]
      analyticSingularCohomology ℂ (V' ↘ Spec (.of ℂ)) 1 :=
  (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
    (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
    Set.univ ((1 : ℕ) : ℤ)).hom

private lemma mapCoeff_pullH1 {R S : Type} [CommRing R] [CommRing S] (f₀ : R →+* S)
    {V V' : Scheme.{0}} [V.Over (Spec (.of ℂ))] [V'.Over (Spec (.of ℂ))] (f : V' ⟶ V)
    (hf : f ≫ (V ↘ Spec (.of ℂ)) = V' ↘ Spec (.of ℂ))
    (x : singularCohomology R (Analytification.space (V ↘ Spec (.of ℂ))) 1) :
    singularCohomology.mapCoeff f₀ 1 ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
      Set.univ ((1 : ℕ) : ℤ)).hom x) =
    (cohomologyWithSupports.pullback S (ModuleCat.of S S)
      (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
      Set.univ ((1 : ℕ) : ℤ)).hom (singularCohomology.mapCoeff f₀ 1 x) :=
  singularCohomology.mapCoeff_relativeSingularCohomology_map f₀ _ _ 1 x

set_option maxRecDepth 10000 in
/-- **The Hodge index argument on the components.** Let `E_P` be smooth projective surfaces and
`C_k` smooth projective curves with maps `g_k : C_k → E_{p k}`, `g'_k : C_k → E_{q k}`, rational
cycles `z_P`, `w_k` on their analytic spaces, and ample line bundles `L_P` on `E_P`, `N_k` on
`C_k` of positive degree on these cycles. Let rational forms `τ_{PQ}` on `H¹(E_P) × H¹(E_Q)` and
`τ'_{PQ}` on `H¹(E_P)` satisfy, with positive weights `m` and non-negative weights `n`, the
identities `∑_Q m_Q τ'_{PQ}(x, x') = ∫_{z_P} x ∪ x' ∪ c₁(L_P)` and, for `P ≠ Q`, the curve
identities `τ_{PQ}(x, y) = -∑_k n_k ∫_{w_k} x|_{C_k} ∪ y|_{C_k}` (and similarly for `τ'`). Then
the form `(x, y) ↦ ∑_{P,Q} τ_{PQ}(m_P x_P, m_Q y_Q)` has trivial left radical. -/
private theorem eq_zero_of_hodgeRadical {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K]
    (E : ι → Scheme.{0}) [∀ P, (E P).Over (Spec (.of ℂ))]
    [∀ P, AlgebraicGeometry.IsProjectiveVariety ℂ (E P ↘ Spec (.of ℂ))]
    [∀ P, SmoothOfRelativeDimension 2 (E P ↘ Spec (.of ℂ))]
    [∀ P, CompactSpace (Analytification.space (E P ↘ Spec (.of ℂ)))]
    [∀ P, FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (Analytification.space (E P ↘ Spec (.of ℂ))) ((0 + 1 : ℕ) : ℤ))]
    (C : K → Scheme.{0}) [∀ k, (C k).Over (Spec (.of ℂ))]
    [∀ k, AlgebraicGeometry.IsProjectiveVariety ℂ (C k ↘ Spec (.of ℂ))]
    [∀ k, SmoothOfRelativeDimension 1 (C k ↘ Spec (.of ℂ))]
    [∀ k, CompactSpace (Analytification.space (C k ↘ Spec (.of ℂ)))]
    [∀ k, FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (Analytification.space (C k ↘ Spec (.of ℂ))) ((0 + 1 : ℕ) : ℤ))]
    (p q : K → ι) (hpq : ∀ k, p k ≠ q k)
    (g : ∀ k, C k ⟶ E (p k)) (hg : ∀ k, g k ≫ (E (p k) ↘ Spec (.of ℂ)) = C k ↘ Spec (.of ℂ))
    (g' : ∀ k, C k ⟶ E (q k)) (hg' : ∀ k, g' k ≫ (E (q k) ↘ Spec (.of ℂ)) = C k ↘ Spec (.of ℂ))
    (z : ∀ P, Chain ℚ (Analytification.space (E P ↘ Spec (.of ℂ))) (3 + 1))
    (hz : ∀ P, bd ℚ 3 (z P) = 0)
    (w : ∀ k, Chain ℚ (Analytification.space (C k ↘ Spec (.of ℂ))) (1 + 1))
    (hw : ∀ k, bd ℚ 1 (w k) = 0)
    (L : ∀ P, (E P).Modules)
    [∀ P, SheafOfModules.IsInvertible (E P).presheaf (E P).ringCatSheaf.2 (L P)]
    (hL : ∀ P, MMP.Intersection.IsAmple ℂ (L P))
    (hLd : ∀ P, ∃ d : ℝ, 0 < d ∧ intCycle 3 (z P) (hz P) (MMP.cupNatUniv ℂ _ 2 2
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (L P)))
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (L P)))) = d)
    (N : ∀ k, (C k).Modules)
    [∀ k, SheafOfModules.IsInvertible (C k).presheaf (C k).ringCatSheaf.2 (N k)]
    (hN : ∀ k, MMP.Intersection.IsAmple ℂ (N k))
    (hNd : ∀ k, ∃ d : ℝ, 0 < d ∧ intCycle 1 (w k) (hw k)
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (N k))) = d)
    (m : ι → ℚ) (hm : ∀ P, 0 < m P) (n : K → ℚ) (hn : ∀ k, 0 ≤ n k)
    (τ : ∀ P Q, H1Q (E P) →ₗ[ℚ] H1Q (E Q) →ₗ[ℚ] ℚ)
    (τ' : ∀ P Q, H1Q (E P) →ₗ[ℚ] H1Q (E P) →ₗ[ℚ] ℚ) (hττ' : ∀ P, τ' P P = τ P P)
    (hG4 : ∀ P (x x' : H1Q (E P)), ∑ Q, m Q * τ' P Q x x' =
      kron _ (3 + 1) (MMP.cupNatUniv ℚ _ (1 + 1) 2
        (MMP.cupNatUniv ℚ _ 1 1 x x')
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass (L P))))
        (cycleClass 3 (z P) (hz P)))
    (hG3 : ∀ (x y : ∀ P, H1Q (E P)) (P Q : ι), P ≠ Q → τ P Q (x P) (y Q) =
      -(∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q),
          n k * kron _ (1 + 1) (MMP.cupNatUniv ℚ _ 1 1
            (pullH1 (g k) (hg k) (x (p k))) (pullH1 (g' k) (hg' k) (y (q k))))
            (cycleClass 1 (w k) (hw k))) -
        ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P),
          n k * kron _ (1 + 1) (MMP.cupNatUniv ℚ _ 1 1
            (pullH1 (g' k) (hg' k) (x (q k))) (pullH1 (g k) (hg k) (y (p k))))
            (cycleClass 1 (w k) (hw k)))
    (hG3' : ∀ (x y : ∀ P, H1Q (E P)) (P Q : ι), P ≠ Q → τ' P Q (x P) (y P) =
      -(∑ k ∈ Finset.univ.filter (fun k ↦ p k = P ∧ q k = Q),
          n k * kron _ (1 + 1) (MMP.cupNatUniv ℚ _ 1 1
            (pullH1 (g k) (hg k) (x (p k))) (pullH1 (g k) (hg k) (y (p k))))
            (cycleClass 1 (w k) (hw k))) -
        ∑ k ∈ Finset.univ.filter (fun k ↦ p k = Q ∧ q k = P),
          n k * kron _ (1 + 1) (MMP.cupNatUniv ℚ _ 1 1
            (pullH1 (g' k) (hg' k) (x (q k))) (pullH1 (g' k) (hg' k) (y (q k))))
            (cycleClass 1 (w k) (hw k)))
    (x : ∀ P, H1Q (E P))
    (hx : ∀ y : ∀ P, H1Q (E P), ∑ P, ∑ Q, τ P Q (m P • x P) (m Q • y Q) = 0) : x = 0 := by
  classical
  let cL : ∀ P, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (Analytification.space (E P ↘ Spec (.of ℂ))) Set.univ ((2 : ℕ) : ℤ) := fun P ↦
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass (L P))
  let θ : ∀ k, H1Q (C k) →ₗ[ℚ] H1Q (C k) →ₗ[ℚ] ℚ := fun k ↦
    (MMP.cupNatUniv ℚ _ 1 1).compr₂
      ((kron _ (1 + 1)).flip (cycleClass 1 (w k) (hw k)))
  let σq : ∀ P, H1Q (E P) →ₗ[ℚ] H1Q (E P) →ₗ[ℚ] ℚ := fun P ↦
    (MMP.cupNatUniv ℚ _ 1 1).compr₂
      (((kron _ (3 + 1)).flip (cycleClass 3 (z P) (hz P))).comp
        ((MMP.cupNatUniv ℚ _ (1 + 1) 2).flip (cL P)))
  have hsum := fun y : ∀ P, H1Q (E P) ↦ sum_pairing_eq (fun P ↦ H1Q (E P)) (fun k ↦ H1Q (C k)) m τ τ' hττ' σq p q
    hpq n (fun k ↦ pullH1 (g k) (hg k)) (fun k ↦ pullH1 (g' k) (hg' k)) θ hG4 hG3 hG3' x y
  have hcL : ∀ P, singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (L P)) =
      singularCohomology.mapCoeff (algebraMap ℚ ℂ) 2 (cL P) := fun P ↦ by
    simp only [cL]
    rw [mapCoeff_mapCoeff, show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
      RingHom.ext_int _ _]
  refine eq_zero_of_hodgeData_rat
    (fun P ↦ analyticSingularCohomology ℂ (E P ↘ Spec (.of ℂ)) 1)
    (fun k ↦ analyticSingularCohomology ℂ (C k ↘ Spec (.of ℂ)) 1)
    (fun P ↦ H1Q (E P)) (fun k ↦ H1Q (C k))
    (fun P ↦ (singularCohomology.mapCoeff (algebraMap ℚ ℂ) (0 + 1)).toAddMonoidHom)
    (fun P ↦ injective_mapCoeff_rat_one)
    (fun P ↦ eq_top_iff.2 fun h _ ↦ mem_span_range_mapCoeff 0 h)
    (fun k ↦ (singularCohomology.mapCoeff (algebraMap ℚ ℂ) (0 + 1)).toAddMonoidHom)
    (fun P ↦ conjH (E P)) (fun k ↦ conjH (C k))
    (fun P a ↦ mapCoeff_conj_conj 1 a) (fun k a ↦ mapCoeff_conj_conj 1 a)
    (fun P ↦ holClasses (E P)) (fun k ↦ holClasses (C k))
    (fun P a ↦ hodge_decomposition (Or.inr rfl) a) m hm
    (fun P ↦ surfaceForm (z P) (hz P)
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (L P))))
    (fun P a b ↦ σq P a b) ?hσq (fun P a b ↦ surfaceForm_conj _ _ _ a b)
    (fun P h hh h' hh' ↦ surfaceForm_hol _ _ (L P) hh hh')
    (fun P h hh h0 ↦ surfaceForm_pos _ _ (L P) (hL P) (hLd P) hh h0) p q
    (fun k ↦ pullH1C (g k) (hg k)) (fun k ↦ pullH1C (g' k) (hg' k))
    (fun k ↦ (pullH1 (g k) (hg k)).toAddMonoidHom) (fun k ↦ (pullH1 (g' k) (hg' k)).toAddMonoidHom)
    (fun k a ↦ (mapCoeff_pullH1 (algebraMap ℚ ℂ) (g k) (hg k) a).symm)
    (fun k a ↦ (mapCoeff_pullH1 (algebraMap ℚ ℂ) (g' k) (hg' k) a).symm)
    (fun k a ↦ (mapCoeff_pullH1 (starRingEnd ℂ) (g k) (hg k) a).symm)
    (fun k a ↦ (mapCoeff_pullH1 (starRingEnd ℂ) (g' k) (hg' k) a).symm)
    ?hρhol ?hρ'hol (fun k ↦ m (p k) * m (q k) * n k)
    (fun k ↦ mul_nonneg (mul_nonneg (hm _).le (hm _).le) (hn k))
    (fun k ↦ curveForm (w k) (hw k)) (fun k a b ↦ θ k a b) ?hθq (fun k a b ↦ curveForm_conj _ _ a b)
    (fun k g hg g' hg' ↦ curveForm_hol _ _ (N k) hg hg')
    (fun k g hg ↦ curveForm_nonneg _ _ (N k) (hN k) (hNd k) hg) x fun y ↦ ?_
  case hσq =>
    intro P a b
    change intCycle 3 (z P) (hz P) (MMP.cupNatUniv ℂ _ (1 + 1) 2
      (MMP.cupNatUniv ℂ _ 1 1 (singularCohomology.mapCoeff (algebraMap ℚ ℂ) 1 a)
        (singularCohomology.mapCoeff (algebraMap ℚ ℂ) 1 b))
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass (L P)))) = _
    rw [hcL, ← mapCoeff_cupNatUniv, ← mapCoeff_cupNatUniv, intCycle_mapCoeff_rat]
    rfl
  case hρhol =>
    rintro k h ⟨ω, hω⟩
    exact ((hodgeDecomposition_one_of_isProjectiveVariety (n := 2) (Or.inr rfl)
      (X := E (p k))).2.2.2.2.2 (Or.inl rfl) (C k) (g k) (hg k) ω h hω).1
  case hρ'hol =>
    rintro k h ⟨ω, hω⟩
    exact ((hodgeDecomposition_one_of_isProjectiveVariety (n := 2) (Or.inr rfl)
      (X := E (q k))).2.2.2.2.2 (Or.inl rfl) (C k) (g' k) (hg' k) ω h hω).1
  case hθq =>
    intro k a b
    change intCycle 1 (w k) (hw k) (MMP.cupNatUniv ℂ _ 1 1
      (singularCohomology.mapCoeff (algebraMap ℚ ℂ) 1 a)
      (singularCohomology.mapCoeff (algebraMap ℚ ℂ) 1 b)) = _
    rw [← mapCoeff_cupNatUniv, intCycle_mapCoeff_rat]
    rfl
  rw [← hx y, hsum y]
  rfl

end HodgeRadical

/-! ### Reduction to the nondegeneracy of the intersection form -/

section Reduction

/-- Pull-back along a homeomorphism is injective on cohomology. -/
private lemma injective_rationalCohomologyMap {X X' : TopCat.{0}} (e : X ⟶ X') (e' : X' ⟶ X)
    (h : e' ≫ e = 𝟙 X') (q : ℕ) : Function.Injective (rationalCohomologyMap e q).hom := by
  have := congrArg (fun g ↦ (rationalCohomologyMap g q).hom) h
  simp only [rationalCohomologyMap_comp, rationalCohomologyMap_id, ModuleCat.hom_comp,
    ModuleCat.hom_id] at this
  exact Function.LeftInverse.injective (g := (rationalCohomologyMap e' q).hom)
    fun x ↦ congrArg (fun φ ↦ φ x) this

/-- **Bijectivity from a nondegenerate pairing.** Let `i : E → M` be an embedding of a compact
space onto a closed subset `E` of `M` with Alexander duality `H^3(M, M - E) ≅ H_3 E` and `H_3 E`
finite dimensional. If the pairing `(v, v') ↦ ⟨(v|_E), v' ∩ μ⟩` on `H^3(M, M - E)` has trivial
left radical, then `H^3(M, M - E) → H^3 M → H^3 E` is bijective. -/
private theorem bijective_of_radical {M EC : TopCat.{0}} (i : EC ⟶ M)
    (hi : Topology.IsEmbedding i) {Ec : Set M} [CompactSpace Ec] (hEc : Set.range i = Ec)
    (hcl : IsClosed Ec)
    (hd : HasProperNeighbourhoodDeformations Ec)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) M ((2 * 3 : ℕ) : ℤ))
    (hk : ((3 : ℕ) : ℤ) = ((2 * 3 : ℕ) : ℤ) - (3 : ℤ))
    (hδ : Function.Bijective (borelMooreHomology.dualityMap ℚ hcl hd μ 3))
    (hfin : FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of Ec) 3))
    (hrad : ∀ v, (∀ v', kron (TopCat.of Ec) 3
        ((rationalCohomologyMap (subspaceInclusion M Ec) 3).hom
          ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) M Ec 3).hom v))
        (borelMooreHomology.dualityMap ℚ hcl hd μ 3
          (cohomologyWithSupports.congrIndex ℚ M rfl hk v')) = 0) → v = 0) :
    Function.Bijective (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) M Ec 3 ≫
      rationalCohomologyMap i 3).hom := by
  subst hEc
  let e : TopCat.of (Set.range i) ⟶ EC := TopCat.ofHom (hi.toHomeomorph.symm : C(_, EC))
  let e' : EC ⟶ TopCat.of (Set.range i) := TopCat.ofHom (hi.toHomeomorph : C(EC, _))
  have hee' : e' ≫ e = 𝟙 EC := by ext x; simp [e, e']
  have hei : e ≫ i = subspaceInclusion M (Set.range i) := by
    ext x
    change i (hi.toHomeomorph.symm x) = x.1
    conv_rhs => rw [← hi.toHomeomorph.apply_symm_apply x]
    rfl
  refine bijective_of_pairing _
    ((borelMooreHomology.dualityMap ℚ hcl hd μ 3).comp
      (cohomologyWithSupports.congrIndex ℚ M rfl hk).toLinearMap)
    (hδ.comp (cohomologyWithSupports.congrIndex ℚ M rfl hk).bijective)
    ((kron (TopCat.of (Set.range i)) 3).comp (rationalCohomologyMap e 3).hom)
    (fun h hh ↦ injective_rationalCohomologyMap e e' hee' 3
      ((eq_zero_of_forall_kron_eq_zero 2 _ hh).trans (map_zero _).symm))
    (fun v hv ↦ hrad v fun v' ↦ ?_)
  have h2 : rationalCohomologyMap (subspaceInclusion M (Set.range i)) 3 =
      rationalCohomologyMap i 3 ≫ rationalCohomologyMap e 3 :=
    hei ▸ rationalCohomologyMap_comp e i 3
  have := hv v'
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ModuleCat.hom_comp] at this
  simp only [h2, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact this

end Reduction

/-! ### Finite dimensionality of the homology of a projective complex scheme -/

section FiniteHomology

open AlgebraicTopology Limits
open scoped TensorProduct

/-- Extension of scalars `ℤ → ℚ` is additive. -/
private lemma additive_extendScalars :
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap ℤ ℚ)).Additive :=
  ⟨fun {_ _ _ _} => by
    ext x; simp [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map']; rfl⟩

/-- A chain complex of finite-dimensional `ℚ`-vector spaces has finite-dimensional homology. -/
private lemma finiteDimensional_homology {K : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (h : ∀ i, FiniteDimensional ℚ (K.X i)) (k : ℕ) : FiniteDimensional ℚ (K.homology k) := by
  have : FiniteDimensional ℚ (K.cycles k) :=
    Module.Finite.of_injective (K.iCycles k).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ k).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The rational singular homology of the complex realization of an H-projective scheme over `ℂ`
is finite-dimensional. -/
private lemma finiteDimensional_homology_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjectiveMorphism sX) (k : ℕ) :
    FiniteDimensional ℚ ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (MMP.Analytic.ComplexPoints.analyticSpace sX)).homology k) := by
  obtain ⟨⟨C, hC, -, ⟨e⟩⟩, -⟩ :=
    MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sX hX
  let F := ModuleCat.extendScalars.{0, 0, 0} (algebraMap ℤ ℚ)
  have : F.Additive := additive_extendScalars
  let e' := F.mapHomotopyEquiv e
  let i₁ := (SSet.chainComplexFunctorObjCompMapIso F (ModuleCat.of ℤ ℤ)).app
    (TopCat.toSSet.obj (MMP.Analytic.ComplexPoints.analyticSpace sX))
  let i₂ : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso
  let i₃ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).mapIso i₂).app
    (TopCat.toSSet.obj (MMP.Analytic.ComplexPoints.analyticSpace sX))
  have hfin : ∀ i, FiniteDimensional ℚ (((F.mapHomologicalComplex _).obj C).X i) := fun i ↦
    have := (hC i).2
    inferInstanceAs (FiniteDimensional ℚ (ℚ ⊗[ℤ] C.X i))
  have := finiteDimensional_homology hfin k
  let j := e'.toHomologyIso k ≪≫ (HomologicalComplex.homologyFunctor _ _ k).mapIso (i₁ ≪≫ i₃)
  exact Module.Finite.equiv j.toLinearEquiv

section BorelMoore

open MMP MMP.LocallyFiniteChain

variable (Y : TopCat.{0})

/-- A finitely supported family of simplices is locally finite. -/
private lemma isLocallyFiniteSet_of_finite {S : Type*} {car : S → Set Y} {s : Set S}
    (hs : s.Finite) : IsLocallyFiniteSet car s :=
  fun _ ↦ ⟨Set.univ, Filter.univ_mem, hs.subset fun _ hτ ↦ hτ.1⟩

/-- Finite singular chains, as locally finite singular chains. -/
private noncomputable def finsuppToLF (n : SimplexCategoryᵒᵖ) :
    ((TopCat.toSSet.obj Y).obj n →₀ ℚ) →ₗ[ℚ]
      lfChains ℚ (ModuleCat.of ℚ ℚ) (singularSimplexImage Y (n := n)) :=
  (Finsupp.lcoeFun).codRestrict _ fun f ↦
    isLocallyFiniteSet_of_finite Y f.hasFiniteSupport

/-- On a compact space every locally finite chain is finite. -/
private lemma bijective_finsuppToLF [CompactSpace Y] (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (finsuppToLF Y n) := by
  refine ⟨fun f g h ↦ Finsupp.ext fun σ ↦ congr_fun (congrArg Subtype.val h) σ, fun c ↦ ?_⟩
  have hfin : (Function.support c.1).Finite := by
    refine (c.2.finite_inter_compact isCompact_univ).subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := nonempty_singularSimplexImage σ
    exact ⟨y, hy, trivial⟩
  exact ⟨Finsupp.ofSupportFinite c.1 hfin, Subtype.ext rfl⟩

/-- The coproduct of copies of `ℚ` indexed by `S` is `S →₀ ℚ`. -/
private noncomputable def sigmaIsoFinsupp (S : Type) :
    (∐ fun _ : S ↦ ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℚ (S →₀ ℚ) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (ModuleCat.finsuppCoconeIsColimit ℚ ℚ S)

@[reassoc]
private lemma ι_sigmaIsoFinsupp_hom {S : Type} (σ : S) :
    Sigma.ι _ σ ≫ (sigmaIsoFinsupp S).hom = ModuleCat.ofHom (Finsupp.lsingle σ) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk σ)

private lemma sigmaIsoFinsupp_hom_ι_apply {S : Type} (σ : S) (q : ℚ) :
    (sigmaIsoFinsupp S).hom.hom ((Sigma.ι (fun _ : S ↦ ModuleCat.of ℚ ℚ) σ).hom q) =
      Finsupp.single σ q := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ι_sigmaIsoFinsupp_hom]
  rfl

/-- The comparison from singular chains (as a coproduct) to locally finite chains. -/
private noncomputable def toLF :
    ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj
      (TopCat.toSSet.obj Y) ⟶ locallyFiniteSingularChains ℚ (ModuleCat.of ℚ ℚ) Y where
  app n := (sigmaIsoFinsupp _).hom ≫ ModuleCat.ofHom (finsuppToLF Y n)
  naturality n m θ := by
    dsimp [sigmaConst]
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    simp only [Sigma.ι_comp_map'_assoc, Category.id_comp]
    refine ModuleCat.hom_ext (LinearMap.ext_ring (Subtype.ext (funext fun τ ↦ ?_)))
    change ((sigmaIsoFinsupp _).hom.hom ((Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.obj Y).map θ σ)).hom 1) : (TopCat.toSSet.obj Y).obj m →₀ ℚ) τ =
      pushforwardFun ((TopCat.toSSet.obj Y).map θ)
        ⇑((sigmaIsoFinsupp _).hom.hom ((Sigma.ι (fun _ ↦ ModuleCat.of ℚ ℚ) σ).hom 1)) τ
    rw [sigmaIsoFinsupp_hom_ι_apply, sigmaIsoFinsupp_hom_ι_apply]
    classical
    rw [pushforwardFun_apply_eq_sum _ _ τ {σ} fun σ' h _ ↦ by
      by_contra h'
      exact h (Finsupp.single_eq_of_ne (by simpa using h'))]
    simp [Finsupp.single_apply]

private lemma isIso_toLF_app [CompactSpace Y] (n : SimplexCategoryᵒᵖ) :
    IsIso ((toLF Y).app n) := by
  change IsIso ((sigmaIsoFinsupp _ ≪≫
    (LinearEquiv.ofBijective _ (bijective_finsuppToLF Y n)).toModuleIso).hom)
  infer_instance

/-- On a compact space, Borel–Moore homology is singular homology. -/
private noncomputable def borelMooreHomologyIso [CompactSpace Y] (k : ℕ) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k ≅
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y).homology k :=
  have : IsIso (toLF Y) := by
    have := isIso_toLF_app Y
    exact NatIso.isIso_of_isIso_app _
  borelMooreHomologyIsoOfNat ℚ _ Y k ≪≫ (HomologicalComplex.homologyFunctor _ _ k).mapIso
    ((alternatingFaceMapComplex _).mapIso (asIso (toLF Y))).symm

end BorelMoore

end FiniteHomology

/-! ### Decomposition along the components -/

section Components

open borelMooreHomology

/-- The preimage of a closed set under the inclusion of a compact set is compact. -/
private lemma compactSpace_preimage_subsetInclusion {M : TopCat.{0}} {A B : Set M} [CompactSpace B]
    (hA : IsClosed A) : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
  isCompact_iff_compactSpace.1 (hA.preimage (borelMooreHomology.subsetInclusion B).hom.continuous).isCompact

/-- The pairing `(c, y) ↦ deg (j_B^* c ∩ y)` of a class with supports in `A ⊆ M` against a class
on a compact closed `B ⊆ M`, `j_B : B → M` the inclusion. -/
private noncomputable def compPairing {M : TopCat.{0}} {A B : Set M} [CompactSpace B]
    (hA : IsClosed A) (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' A))
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A (((2 * 3 : ℕ) : ℤ) - 3))
    (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) 3) : ℚ :=
  haveI : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
    isCompact_iff_compactSpace.1 (hA.preimage (borelMooreHomology.subsetInclusion B).hom.continuous).isCompact
  deg (TopCat.of (borelMooreHomology.subsetInclusion B ⁻¹' A)) (congrDegree ℚ _ (by norm_num)
    (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion B) hA hd _ 3 c y))

/-- For `B ⊆ X` the inclusion of `B` pulls `X` back to everything. -/
private lemma preimage_subsetInclusion_eq_univ {M : TopCat.{0}} {B X : Set M} (h : B ⊆ X) :
    borelMooreHomology.subsetInclusion B ⁻¹' X = Set.univ :=
  Set.eq_univ_of_forall fun b ↦ h b.2

/-- **One term of the decomposition.** For closed `A, B ⊆ X ⊆ M` and `c ∈ H³(M, M - A)`,
`y ∈ H₃ B`, `deg (j_X^* (c|_X) ∩ ι_* y) = deg (j_B^* c ∩ y)`. -/
private lemma deg_capProductSupportPullback_forget_pushforward {M : TopCat.{0}} {X A B : Set M}
    [CompactSpace X] [CompactSpace B] [CompactSpace (borelMooreHomology.subsetInclusion X ⁻¹' X)]
    (hX : IsClosed X) (hA : IsClosed A) (hB : IsClosed B) (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hXd' : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion X ⁻¹' X))
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' A))
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A (((2 * 3 : ℕ) : ℤ) - 3))
    (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) 3) :
    deg (TopCat.of (borelMooreHomology.subsetInclusion X ⁻¹' X)) (congrDegree ℚ _ (by norm_num)
      (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion X) hX hXd' _ 3
        ((cohomologyWithSupports.forget ℚ _ M hAX _).hom c)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset hBX)
          (isProperMap_subsetInclusionOfSubset hB hBX) 3).hom y))) =
      compPairing hA hd c y := by
  have hBX' : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' X) :=
    (preimage_subsetInclusion_eq_univ hBX) ▸ hasProperNeighbourhoodDeformations_univ _
  haveI : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' X) :=
    isCompact_iff_compactSpace.1 (hX.preimage (borelMooreHomology.subsetInclusion B).hom.continuous).isCompact
  haveI : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
    isCompact_iff_compactSpace.1 (hA.preimage (borelMooreHomology.subsetInclusion B).hom.continuous).isCompact
  let ρ : TopCat.of (borelMooreHomology.subsetInclusion B ⁻¹' X) ⟶
      TopCat.of (borelMooreHomology.subsetInclusion X ⁻¹' X) :=
    TopCat.ofHom ⟨fun p ↦ ⟨⟨p.1.1, hBX p.1.2⟩, p.2⟩, by fun_prop⟩
  have hρp : IsProperMap ρ := by
    have hψ : Topology.IsClosedEmbedding (fun p : borelMooreHomology.subsetInclusion X ⁻¹' X ↦
        (p.1.1 : M)) :=
      hX.isClosedEmbedding_subtypeVal.comp
        (hX.preimage continuous_subtype_val).isClosedEmbedding_subtypeVal
    have hψρ : Topology.IsClosedEmbedding ((fun p : borelMooreHomology.subsetInclusion X ⁻¹' X ↦
        (p.1.1 : M)) ∘ ρ) :=
      hB.isClosedEmbedding_subtypeVal.comp
        (hX.preimage continuous_subtype_val).isClosedEmbedding_subtypeVal
    exact ((hψ.of_comp_iff).1 hψρ).isProperMap
  have h3 := pushforward_capProductSupportPullback_of_comp_eq ℚ (subsetInclusionOfSubset hBX)
    (isProperMap_subsetInclusionOfSubset hB hBX) (borelMooreHomology.subsetInclusion X)
    (borelMooreHomology.subsetInclusion B) rfl hX hXd' hBX' ρ (fun _ ↦ rfl) hρp _ 3
    ((cohomologyWithSupports.forget ℚ _ M hAX _).hom c) y
  have h2 := capProductSupportPullback_eq_pushforward_of_forget_eq ℚ
    (borelMooreHomology.subsetInclusion B) (borelMooreHomology.subsetInclusion B) hA hX hd hBX'
    (Set.preimage_mono hAX) (v := c) (v' := (cohomologyWithSupports.forget ℚ _ M hAX _).hom c)
    (cohomologyWithSupports.pullback_forget_apply ℚ _ _ hAX _ c).symm 3 y
  rw [← h3, h2, compPairing, deg_congrDegree_pushforward, deg_congrDegree_pushforward]

/-- Transport of the supported cap product along an equality of cohomological degrees. -/
private lemma deg_capProductSupportPullback_congrIndex {M : TopCat.{0}} {X B : Set M}
    [CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' X)] (hX : IsClosed X)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' X))
    {j j' k : ℤ} (h : j = j') (e : k - j = 0) (e' : k - j' = 0)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M X j)
    (b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) k) :
    deg _ (congrDegree ℚ _ e (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion B)
        hX hd j k c b)) =
      deg _ (congrDegree ℚ _ e' (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion B)
        hX hd j' k (cohomologyWithSupports.congrIndex ℚ M rfl h c) b)) := by
  subst h
  rfl

/-- **Reduction to the components.** Let `X ⊆ M` be compact and closed with Alexander duality in
degree three, and let `X` be covered by closed `A_P` with duality, compatible with forgetting
supports, such that `⊕ H₃(A_P) → H₃(X)` is onto. If the component pairings
`∑_{P,Q} deg (j_{A_Q}^* c_P ∩ y_Q)` detect `∑_P c_P`, then the pairing
`(v, v') ↦ ⟨v|_X, v' ∩ μ⟩` on `H³(M, M - X)` has trivial left radical. -/
private theorem radical_of_components {M : TopCat.{0}} {X : Set M} [CompactSpace X]
    [CompactSpace (borelMooreHomology.subsetInclusion X ⁻¹' X)] (hX : IsClosed X)
    (hXd : HasProperNeighbourhoodDeformations X)
    (hXd' : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion X ⁻¹' X))
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) M ((2 * 3 : ℕ) : ℤ))
    (hk : ((3 : ℕ) : ℤ) = ((2 * 3 : ℕ) : ℤ) - (3 : ℤ))
    (hδ : Function.Bijective (dualityMap ℚ hX hXd μ 3))
    {ι : Type} [Fintype ι] (A : ι → Set M) [∀ P, CompactSpace (A P)] (hA : ∀ P, IsClosed (A P))
    (hAX : ∀ P, A P ⊆ X) (hAd : ∀ P, HasProperNeighbourhoodDeformations (A P))
    (hAd' : ∀ P Q, HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion (A Q) ⁻¹' A P))
    (hδA : ∀ P, Function.Surjective (dualityMap ℚ (hA P) (hAd P) μ 3))
    (hnat : ∀ P c, (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (hAX P))
        (isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) 3).hom
          (dualityMap ℚ (hA P) (hAd P) μ 3 c) =
        dualityMap ℚ hX hXd μ 3 ((cohomologyWithSupports.forget ℚ _ M (hAX P) _).hom c))
    (hsum : ∀ b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X) 3,
      ∃ x : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) 3,
        ∑ P, (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (hAX P))
          (isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) 3).hom (x P) = b)
    (hloc : ∀ c : ∀ P, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M (A P) (((2 * 3 : ℕ) : ℤ) - 3),
      (∀ y : ∀ Q, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A Q)) 3,
        ∑ P, ∑ Q, compPairing (hA P) (hAd' P Q) (c P) (y Q) = 0) →
      ∑ P, (cohomologyWithSupports.forget ℚ _ M (hAX P) _).hom (c P) = 0)
    (v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M X 3)
    (hv : ∀ v', kron (TopCat.of X) 3 ((rationalCohomologyMap (subspaceInclusion M X) 3).hom
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) M X 3).hom v))
        (dualityMap ℚ hX hXd μ 3 (cohomologyWithSupports.congrIndex ℚ M rfl hk v')) = 0) :
    v = 0 := by
  classical
  set e := cohomologyWithSupports.congrIndex ℚ M (S := Xᶜ) rfl hk
  obtain ⟨x, hx⟩ := hsum (dualityMap ℚ hX hXd μ 3 (e v))
  choose c hc using fun P ↦ hδA P (x P)
  have hv'' : e v = ∑ P, (cohomologyWithSupports.forget ℚ _ M (hAX P) _).hom (c P) := by
    apply hδ.1
    rw [map_sum, ← hx]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [← hnat P, hc P]
  refine e.injective ((hv''.trans (hloc c fun y ↦ ?_)).trans (map_zero e).symm)
  obtain ⟨w, hw⟩ := hδ.2 (∑ Q, (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (hAX Q))
    (isProperMap_subsetInclusionOfSubset (hA Q) (hAX Q)) 3).hom (y Q))
  have h0 := hv (e.symm w)
  rw [LinearEquiv.apply_symm_apply, hw, kron_rationalCohomologyMap_toCohomology hX hXd'] at h0
  have h1 := deg_capProductSupportPullback_congrIndex hX hXd' hk (by norm_num) (by norm_num) v
    (∑ Q, (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (hAX Q))
      (isProperMap_subsetInclusionOfSubset (hA Q) (hAX Q)) 3).hom (y Q))
  erw [h1] at h0
  change deg _ (congrDegree ℚ _ _ (capProductSupportPullback ℚ _ hX hXd' _ 3 (e v) _)) = 0 at h0
  rw [hv''] at h0
  rw [← h0]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ ↦ Finset.sum_congr rfl fun P _ ↦ ?_
  exact (deg_capProductSupportPullback_forget_pushforward hX (hA P) (hA Q) (hAX P) (hAX Q) hXd'
    (hAd' P Q) (c P) (y Q)).symm

end Components

/-! ### The pairing of two components as a cup product -/

section Formula

open borelMooreHomology Set

variable (Y : TopCat.{0}) [CompactSpace Y] in
/-- The degree of a class in `H_i Y`, `i = 0`. -/
private noncomputable def degAt {i : ℤ} (h : i = 0) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y i →ₗ[ℚ] ℚ :=
  (deg Y).comp (congrDegree ℚ Y h).toLinearMap

private lemma degAt_congrDegree {Y : TopCat.{0}} [CompactSpace Y] {i i' : ℤ} (h : i = i')
    (h' : i' = 0) (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y i) :
    degAt Y h' (congrDegree ℚ Y h x) = degAt Y (h.trans h') x := by
  subst h; rfl

private lemma degAt_pushforward {Y Y' : TopCat.{0}} [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ Y') (hf : IsProperMap f) {i : ℤ} (h : i = 0)
    (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y i) :
    degAt Y' h ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf i).hom x) = degAt Y h x :=
  deg_congrDegree_pushforward f hf h x

/-- The inclusion `A ∩ B → A`. -/
private abbrev interLeft {M : TopCat.{0}} (A B : Set M) : TopCat.of (A ∩ B : Set M) ⟶ TopCat.of A :=
  subsetInclusionOfSubset (Set.inter_subset_left : A ∩ B ⊆ A)

/-- The inclusion `A ∩ B → B`. -/
private abbrev interRight {M : TopCat.{0}} (A B : Set M) : TopCat.of (A ∩ B : Set M) ⟶ TopCat.of B :=
  subsetInclusionOfSubset (Set.inter_subset_right : A ∩ B ⊆ B)

/-- The class `j_A^* η ∩ [A] ∈ H_{k-j}(A ∩ B)` for `η ∈ H^j(M, M - B)` and `[A] ∈ H_k A`. -/
private noncomputable def gysinClass {M : TopCat.{0}} {A B : Set M} (hA : IsClosed A) (hB : IsClosed B)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B)) (j k : ℤ)
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B j)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) k) :
    borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A ∩ B : Set M)) (k - j) :=
  (pushforward ℚ (ModuleCat.of ℚ ℚ) (preimageInterHom A B) (isProperMap_preimageInterHom hA hB)
    (k - j)).hom (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion A) hB hd j k η a)

private lemma hpnd_univ_inter (Y : TopCat.{0}) :
    HasProperNeighbourhoodDeformations (univ ∩ univ : Set Y) := by
  rw [inter_self]; exact hasProperNeighbourhoodDeformations_univ _

private lemma hpnd_preimage_univ (Y : TopCat.{0}) :
    HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (univ : Set Y) ⁻¹' (univ : Set Y)) := by
  rw [preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _

/-- `x ∩ (y ∩ m) = (x ∪ y) ∩ m` for absolute classes. -/
private lemma capProduct_capProduct_univ (Y : TopCat.{0}) (i j k : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ i)
    (y : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j)
    (m : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    capProduct ℚ Y univ i (k - j) x (capProduct ℚ Y univ j k y m) =
      congrDegree ℚ Y (by ring)
        (capProduct ℚ Y (univ ∩ univ) (i + j) k
          (cohomologyWithSupports.cup ℚ Y isClosed_univ isClosed_univ i j x y) m) :=
  capProduct_capProduct_eq_capProduct_cup ℚ Y isClosed_univ isClosed_univ
    (hasProperNeighbourhoodDeformations_univ _) (hasProperNeighbourhoodDeformations_univ _)
    (hpnd_univ_inter Y) (hpnd_preimage_univ Y) i j k x y m

/-- Capping with a product in the cohomology ring is the iterated cap product:
`(a ∪ b) ∩ m = a ∩ (b ∩ m)`. -/
private lemma capProduct_cupNatUniv (Y : TopCat.{0}) (i j : ℕ) (k : ℤ)
    (a : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ (i : ℤ))
    (b : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ (j : ℤ))
    (m : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    capProduct ℚ Y univ ((i + j : ℕ) : ℤ) k (MMP.cupNatUniv ℚ Y i j a b) m =
      congrDegree ℚ Y (by push_cast; ring)
        (capProduct ℚ Y univ i (k - j) a (capProduct ℚ Y univ j k b m)) := by
  rw [capProduct_capProduct_univ, MMP.cupNatUniv, LinearMap.compr₂_apply,
    LinearEquiv.coe_coe, capProduct_congrIndex, congrDegree_congrDegree]

/-- **Graded commutativity of iterated cap products** with absolute classes:
`x ∩ (y ∩ m) = (-1)^{ij} y ∩ (x ∩ m)`. -/
private lemma capProduct_capProduct_comm (Y : TopCat.{0}) (i j k : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ i)
    (y : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j)
    (m : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    capProduct ℚ Y univ i (k - j) x (capProduct ℚ Y univ j k y m) =
      (((-1 : ℚˣ) ^ (i * j) : ℚˣ) : ℚ) • congrDegree ℚ Y (by ring)
        (capProduct ℚ Y univ j (k - i) y (capProduct ℚ Y univ i k x m)) := by
  have hc := cohomologyWithSupports.cup_comm ℚ Y isClosed_univ isClosed_univ i j x y
  have hs : (((-1 : ℚˣ) ^ (i * j) : ℚˣ) : ℚ) * (((-1 : ℚˣ) ^ (i * j) : ℚˣ) : ℚ) = 1 := by
    rw [← Units.val_mul, ← mul_zpow, neg_one_mul, neg_neg, one_zpow, Units.val_one]
  have hc' : cohomologyWithSupports.cup ℚ Y isClosed_univ isClosed_univ i j x y =
      (((-1 : ℚˣ) ^ (i * j) : ℚˣ) : ℚ) • cohomologyWithSupports.congrIndex ℚ Y
        (congrArg compl (Set.inter_comm univ univ)) (add_comm j i)
        (cohomologyWithSupports.cup ℚ Y isClosed_univ isClosed_univ j i y x) := by
    rw [hc, smul_smul, hs, one_smul]
  rw [capProduct_capProduct_univ, capProduct_capProduct_univ, hc', LinearMap.map_smul₂,
    capProduct_congrIndex, map_smul, congrDegree_congrDegree, congrDegree_congrDegree]

private lemma capProduct_congrDegree_right (Y : TopCat.{0}) (X : Set Y) (j : ℤ) {k k' : ℤ}
    (h : k = k') (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y X j)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    capProduct ℚ Y X j k' c (congrDegree ℚ Y h a) =
      congrDegree ℚ Y (by rw [h]) (capProduct ℚ Y X j k c a) := by
  subst h; rfl

private lemma pullback_univ_congr {Y' Y : TopCat.{0}} {f g : Y' ⟶ Y} (h : f = g) (j : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j) :
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ j).hom x :
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y' univ j) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g univ j).hom x := by
  subst h; rfl

private lemma pullback_univ_comp {Y'' Y' Y : TopCat.{0}} (f : Y'' ⟶ Y') (g : Y' ⟶ Y) (j : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j) :
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (f ≫ g) univ j).hom x :
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y'' univ j) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ j).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g univ j).hom x) := by
  rw [cohomologyWithSupports.pullback_comp]; rfl

private lemma capProduct_preimage_univ {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (j k : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y' k) :
    capProduct ℚ Y' (f ⁻¹' univ) j k ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ j).hom x) a =
      capProduct ℚ Y' univ j k ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ j).hom x) a :=
  rfl

/-- `compPairing` is the degree of a cap product on the compact set `B`. -/
private lemma compPairing_eq_degAt {M : TopCat.{0}} {A B : Set M} [CompactSpace B]
    (hA : IsClosed A)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' A))
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A (((2 * 3 : ℕ) : ℤ) - 3))
    (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) 3) :
    compPairing hA hd c y = degAt (TopCat.of B) (by norm_num)
      (capProduct ℚ (TopCat.of B) univ _ 3
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B)
          (borelMooreHomology.subsetInclusion B ⁻¹' A) _).hom
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (borelMooreHomology.subsetInclusion B) A _).hom c)) y) := by
  haveI : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
    compactSpace_preimage_subsetInclusion hA
  erw [capProduct_toCohomology (TopCat.of B) _ _ 3]
  rw [← pushforward_subsetInclusion_capProductSupport ℚ (TopCat.of B)
    (hA.preimage (borelMooreHomology.subsetInclusion B).hom.continuous) hd]
  erw [degAt_pushforward]
  rw [← capProductSupportPullback_apply]
  · rfl
  · exact hA

/-- **The intersection pairing on two components.** -/
private theorem compPairing_capProduct_eq {M : TopCat.{0}} {A B : Set M} [CompactSpace A]
    [CompactSpace B] (hA : IsClosed A) (hB : IsClosed B)
    (hAd : HasProperNeighbourhoodDeformations A) (hBd : HasProperNeighbourhoodDeformations B)
    (hABd : HasProperNeighbourhoodDeformations (A ∩ B))
    (hBAd : HasProperNeighbourhoodDeformations (B ∩ A))
    (hA'B : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (hB'A : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' A))
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) M ((2 * 3 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4)
    (b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) 4)
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (hη : capProductSupport ℚ M hB hBd 2 ((2 * 3 : ℕ) : ℤ) η μ = congrDegree ℚ _ (by norm_num) b)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A (((2 * 3 : ℕ) : ℤ) - 3))
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) univ 1)
    (hc : capProductSupport ℚ M hA hAd _ ((2 * 3 : ℕ) : ℤ) c μ =
      congrDegree ℚ _ (by norm_num) (capProduct ℚ (TopCat.of A) univ 1 4 u a))
    (v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) univ 1) :
    haveI : CompactSpace (A ∩ B : Set M) :=
      isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace A›).inter_right hB)
    compPairing hA hB'A c (congrDegree ℚ _ (by norm_num) (capProduct ℚ (TopCat.of B) univ 1 4 v b)) =
      - degAt (TopCat.of (A ∩ B : Set M)) (by norm_num)
        (capProduct ℚ (TopCat.of (A ∩ B : Set M)) univ 1 (4 - 2 - 1)
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interRight A B) univ 1).hom v)
          (capProduct ℚ (TopCat.of (A ∩ B : Set M)) univ 1 (4 - 2)
            ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom u)
            (gysinClass hA hB hA'B 2 4 η a))) := by
  haveI : CompactSpace (A ∩ B : Set M) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace A›).inter_right hB)
  set cB := (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B)
    (borelMooreHomology.subsetInclusion B ⁻¹' A) _).hom
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology.subsetInclusion B) A _).hom c) with hcB
  rw [compPairing_eq_degAt, ← hcB, capProduct_congrDegree_right, degAt_congrDegree,
    capProduct_capProduct_comm]
  have hs3 : (((-1 : ℚˣ) ^ ((((2 * 3 : ℕ) : ℤ) - 3) * 1) : ℚˣ) : ℚ) = -1 := by norm_num
  rw [hs3, map_smul, neg_one_smul, degAt_congrDegree, neg_inj]
  -- the class `j_B^* c ∩ b`, via the swap of the two cap products
  have hX_BA : IsClosed (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
    hA.preimage (borelMooreHomology.subsetInclusion B).hom.continuous
  haveI : CompactSpace (borelMooreHomology.subsetInclusion B ⁻¹' A) :=
    compactSpace_preimage_subsetInclusion hA
  have hb : b = congrDegree ℚ _ (by norm_num) (capProductSupport ℚ M hB hBd 2 _ η μ) := by
    rw [hη, congrDegree_congrDegree, congrDegree_self]; rfl
  have K1 : capProduct ℚ (TopCat.of B) univ _ 4 cB b =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (borelMooreHomology.subsetInclusion
        (borelMooreHomology.subsetInclusion B ⁻¹' A)) (isProperMap_subsetInclusion hX_BA) _).hom
        (congrDegree ℚ _ (by norm_num) (capProductSupportPullback ℚ
          (borelMooreHomology.subsetInclusion B) hA hB'A _ (((2 * 3 : ℕ) : ℤ) - 2) c
          (capProductSupport ℚ M hB hBd 2 _ η μ))) := by
    rw [hcB]
    erw [capProduct_toCohomology (TopCat.of B) _ _ 4]
    rw [← pushforward_subsetInclusion_capProductSupport ℚ (TopCat.of B) hX_BA hB'A, hb,
      capProductSupport_congrDegree_right, pushforward_congrDegree, pushforward_congrDegree,
      ← capProductSupportPullback_apply]
  -- the swap of the two cap products (Fulton §19.1, (8))
  have hs6 : (-1 : ℚˣ) ^ ((((2 * 3 : ℕ) : ℤ) - 3) * 2) = 1 := by norm_num
  have K2 := pushforward_capProductSupportPullback_capProductSupport_comm ℚ M hA hB hAd hBd hABd
    hBAd hB'A hA'B ((2 * 3 : ℕ) : ℤ) hs6 c η μ
  have hincl : borelMooreHomology.subsetInclusion (borelMooreHomology.subsetInclusion B ⁻¹' A) =
      (preimageInterHom B A ≫ subsetInclusionOfSubset (inter_comm B A).le) ≫ interRight A B := by
    ext x; rfl
  have hpBA : IsProperMap (preimageInterHom B A ≫ subsetInclusionOfSubset (inter_comm B A).le) :=
    (isProperMap_subsetInclusionOfSubset (hB.inter hA) (inter_comm B A).le).comp
      (isProperMap_preimageInterHom hB hA)
  have hpR : IsProperMap (interRight A B) :=
    isProperMap_subsetInclusionOfSubset (hA.inter hB) Set.inter_subset_right
  rw [K1, pushforward_congr (R := ℚ) hincl _ (hpR.comp hpBA), pushforward_comp_apply' _ _ _ hpBA hpR,
    pushforward_congrDegree, K2]
  -- `c ∩ μ = u ∩ a`, and the cap product with `j_A^* η` of an absolute cap product
  have hX_AB : IsClosed (borelMooreHomology.subsetInclusion A ⁻¹' B) :=
    hB.preimage (borelMooreHomology.subsetInclusion A).hom.continuous
  have hU := hasProperNeighbourhoodDeformations_univ (TopCat.of A)
  have hDS : HasProperNeighbourhoodDeformations
      ((borelMooreHomology.subsetInclusion A ⁻¹' B) ∩ univ : Set (TopCat.of A)) := by
    rw [inter_univ]; exact hA'B
  have hSD : HasProperNeighbourhoodDeformations
      (univ ∩ (borelMooreHomology.subsetInclusion A ⁻¹' B) : Set (TopCat.of A)) := by
    rw [univ_inter]; exact hA'B
  have hSD' : HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (univ : Set (TopCat.of A)) ⁻¹'
        (borelMooreHomology.subsetInclusion A ⁻¹' B)) :=
    hA'B.preimage_homeomorph (Homeomorph.Set.univ _)
  have hDS' : HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (borelMooreHomology.subsetInclusion A ⁻¹' B) ⁻¹'
        (univ : Set (TopCat.of A))) := by
    rw [preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _
  have hs2 : (-1 : ℚˣ) ^ ((2 : ℤ) * 1) = 1 := by norm_num
  have K3 := capProductSupport_capProduct_eq ℚ (TopCat.of A) hX_AB isClosed_univ hA'B hU hDS hSD
    hSD' hDS' 4 hs2 ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology.subsetInclusion A) B 2).hom η) u a
  rw [hc, capProductSupportPullback_congrDegree_apply, capProductSupportPullback_apply, K3]
  have hmap : borelMooreHomology.subsetInclusion (borelMooreHomology.subsetInclusion A ⁻¹' B) =
      preimageInterHom A B ≫ interLeft A B := by ext x; rfl
  have hpAB := isProperMap_preimageInterHom hA hB
  rw [pullback_univ_congr hmap, pullback_univ_comp]
  have P1 := pushforward_capProduct_pullback ℚ (preimageInterHom A B) hpAB isClosed_univ
    (hasProperNeighbourhoodDeformations_univ _)
    (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial) 1 (4 - 2)
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom u)
    ((capProductSupport ℚ (TopCat.of A) hX_AB hA'B 2 4)
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusion A) B 2).hom η) a)
  simp only [pushforward_congrDegree, congrDegree_congrDegree]
  erw [P1]
  have P2 := pushforward_capProduct_pullback ℚ (interRight A B) hpR isClosed_univ
    (hasProperNeighbourhoodDeformations_univ _)
    (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial) 1 (4 - 2 - 1) v
    ((capProduct ℚ (TopCat.of (A ∩ B : Set M)) univ 1 (4 - 2))
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom u)
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (preimageInterHom A B) hpAB (4 - 2)).hom
        ((capProductSupport ℚ (TopCat.of A) hX_AB hA'B 2 4)
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (borelMooreHomology.subsetInclusion A) B 2).hom η) a)))
  rw [capProduct_congrDegree_right, degAt_congrDegree, ← P2, degAt_pushforward]
  rw [gysinClass, capProductSupportPullback_apply, capProduct_preimage_univ]

end Formula

/-! ### Transport along homeomorphisms -/

section Transport

open borelMooreHomology Set

/-- **Cap products are natural for homeomorphisms**: `φ_* (φ^* x ∩ m) = x ∩ φ_* m`. -/
private lemma pushforward_capProduct_pullback_homeomorph {Y Y' : TopCat.{0}} (φ : Y ≃ₜ Y')
    (j k : ℤ) (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y' univ j)
    (m : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(Y, Y'))) φ.isProperMap (k - j)).hom
        (capProduct ℚ Y univ j k
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(Y, Y')))
            univ j).hom x) m) =
      capProduct ℚ Y' univ j k x
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(Y, Y'))) φ.isProperMap k).hom m) :=
  pushforward_capProduct_pullback ℚ _ φ.isProperMap isClosed_univ
    (hasProperNeighbourhoodDeformations_univ _)
    (hasProperNeighbourhoodDeformations_of_forall_mem fun _ ↦ trivial) j k x m

/-- **Poincaré duality transported along homeomorphisms.** Let `μ ∈ H_4 Y` be a class such that
`c ↦ c ∩ μ`, `H¹ Y → H₃ Y`, is surjective, and `φ : Y ≃ A`, `g : Y ≃ Y'` homeomorphisms. Then every
`y ∈ H₃ A` is `ψ^* x ∩ φ_* μ` for a class `x ∈ H¹ Y'`, `ψ = g ∘ φ⁻¹ : A → Y'`. -/
private theorem exists_capProduct_pullback_eq {Y A Y' : TopCat.{0}} (φ : Y ≃ₜ A) (g : Y ≃ₜ Y')
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y 4)
    (hμ : Function.Surjective fun c ↦ capProduct ℚ Y univ 1 4 c μ)
    (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) A (4 - 1)) :
    ∃ x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y' univ 1,
      y = capProduct ℚ A univ 1 4
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((φ.symm.trans g : A ≃ₜ Y') : C(A, Y'))) univ 1).hom x)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(Y, A))) φ.isProperMap 4).hom μ) := by
  obtain ⟨c, hc⟩ := hμ ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ.symm : C(A, Y)))
    φ.symm.isProperMap _).hom y)
  refine ⟨(cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
    (TopCat.ofHom (g.symm : C(Y', Y))) univ 1).hom c, ?_⟩
  have hmap : TopCat.ofHom ((φ.symm.trans g : A ≃ₜ Y') : C(A, Y')) ≫
      TopCat.ofHom (g.symm : C(Y', Y)) = TopCat.ofHom (φ.symm : C(A, Y)) := by
    ext a; simp
  have hmap' : TopCat.ofHom (φ : C(Y, A)) ≫ TopCat.ofHom (φ.symm : C(A, Y)) = 𝟙 Y := by
    ext a; simp
  rw [← pullback_univ_comp, pullback_univ_congr hmap]
  have key := (pushforward_capProduct_pullback_homeomorph φ 1 4
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ.symm : C(A, Y)))
      univ 1).hom c) μ).symm
  rw [← pullback_univ_comp, pullback_univ_congr hmap', cohomologyWithSupports.pullback_id] at key
  erw [key]
  change y = (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(Y, A))) φ.isProperMap _).hom
    (capProduct ℚ Y univ 1 4 c μ)
  have hc' : capProduct ℚ Y univ 1 4 c μ = (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (φ.symm : C(A, Y))) φ.symm.isProperMap _).hom y := hc
  erw [hc', ← pushforward_comp_apply']
  have hmap'' : TopCat.ofHom (φ.symm : C(A, Y)) ≫ TopCat.ofHom (φ : C(Y, A)) = 𝟙 A := by
    ext a; simp
  rw [pushforward_congr (R := ℚ) hmap'' _ (by simpa using isProperMap_id), pushforward_id]
  rfl

end Transport

/-! ### Reduction of the component pairings to the components -/

section PairingReduction

open borelMooreHomology Set

/-- The Gysin class `j_A^* η ∩ [A]`, pushed forward to `A`, is the cap product with the image of
`j_A^* η` in `H^j A`. -/
private lemma pushforward_interLeft_gysinClass {M : TopCat.{0}} {A B : Set M} (hA : IsClosed A)
    (hB : IsClosed B)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) ((4 : ℕ) : ℤ)) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (interLeft A B)
        (isProperMap_subsetInclusionOfSubset (hA.inter hB) inter_subset_left) (4 - 2)).hom
        (gysinClass hA hB hd 2 4 η a) =
      capProduct ℚ (TopCat.of A) univ 2 4
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A)
          (borelMooreHomology.subsetInclusion A ⁻¹' B) 2).hom
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (borelMooreHomology.subsetInclusion A) B 2).hom η)) a := by
  unfold gysinClass
  have hX : IsClosed (borelMooreHomology.subsetInclusion A ⁻¹' B) :=
    hB.preimage (borelMooreHomology.subsetInclusion A).hom.continuous
  have hmap : preimageInterHom A B ≫ interLeft A B =
      borelMooreHomology.subsetInclusion (borelMooreHomology.subsetInclusion A ⁻¹' B) := by
    ext; rfl
  rw [← pushforward_comp_apply', pushforward_congr (R := ℚ) hmap _ (isProperMap_subsetInclusion hX),
    capProductSupportPullback_apply, pushforward_subsetInclusion_capProductSupport]
  exact (capProduct_toCohomology (TopCat.of A) _ 2 4 _ a).symm

/-- **Projection formula for two degree-one classes**: the degree of
`f^* v ∩ (f^* u ∩ z)` is the degree of `v ∩ (u ∩ f_* z)`. -/
private lemma degAt_capProduct_pullback {Y Y' : TopCat.{0}} [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ Y') (hf : IsProperMap f)
    (u v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y' univ 1)
    (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (4 - 2)) :
    degAt Y (by norm_num) (capProduct ℚ Y univ 1 (4 - 2 - 1)
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ 1).hom v)
      (capProduct ℚ Y univ 1 (4 - 2)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ 1).hom u) z)) =
    degAt Y' (by norm_num) (capProduct ℚ Y' univ 1 (4 - 2 - 1) v
      (capProduct ℚ Y' univ 1 (4 - 2) u ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf (4 - 2)).hom z))) := by
  have hpd : HasProperNeighbourhoodDeformations (f ⁻¹' (univ : Set Y')) := by
    rw [preimage_univ]; exact hasProperNeighbourhoodDeformations_univ _
  rw [← degAt_pushforward f hf]
  erw [pushforward_capProduct_pullback ℚ f hf isClosed_univ
      (hasProperNeighbourhoodDeformations_univ _) hpd 1 (4 - 2 - 1) v,
    pushforward_capProduct_pullback ℚ f hf isClosed_univ
      (hasProperNeighbourhoodDeformations_univ _) hpd 1 (4 - 2) u]

/-- **The degree of a triple cap product is a Kronecker pairing.** Along a homeomorphism
`ψ : A ≅ X`, `deg (ψ^* x' ∩ (ψ^* x ∩ (ψ^* c ∩ a))) = ⟨x' ∪ x ∪ c, ψ_* a⟩`. -/
private lemma degAt_capProduct_homeomorph {A X : TopCat.{0}} [CompactSpace A] [CompactSpace X]
    (ψ : A ≃ₜ X) (x x' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((1 : ℕ) : ℤ))
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((2 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) A ((4 : ℕ) : ℤ)) :
    degAt A (by norm_num) (capProduct ℚ A univ ((1 : ℕ) : ℤ)
      (((4 : ℕ) : ℤ) - ((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
        univ ((1 : ℕ) : ℤ)).hom x')
      (capProduct ℚ A univ ((1 : ℕ) : ℤ) (((4 : ℕ) : ℤ) - ((2 : ℕ) : ℤ))
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
          univ ((1 : ℕ) : ℤ)).hom x)
        (capProduct ℚ A univ ((2 : ℕ) : ℤ) ((4 : ℕ) : ℤ)
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
            univ ((2 : ℕ) : ℤ)).hom c) a))) =
    degAt X (by norm_num) (capProduct ℚ X univ ((1 + 1 + 2 : ℕ) : ℤ) ((4 : ℕ) : ℤ)
      (MMP.cupNatUniv ℚ X (1 + 1) 2 (MMP.cupNatUniv ℚ X 1 1 x' x) c)
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
        ((4 : ℕ) : ℤ)).hom a)) := by
  rw [← degAt_pushforward (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap]
  erw [pushforward_capProduct_pullback_homeomorph, pushforward_capProduct_pullback_homeomorph,
    pushforward_capProduct_pullback_homeomorph]
  set b := (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
        ((4 : ℕ) : ℤ)).hom a
  have h1 := capProduct_cupNatUniv X (1 + 1) 2 ((4 : ℕ) : ℤ)
    (MMP.cupNatUniv ℚ X 1 1 x' x) c b
  have h2 := capProduct_cupNatUniv X 1 1 (((4 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) x' x
    (capProduct ℚ X univ ((2 : ℕ) : ℤ) ((4 : ℕ) : ℤ) c b)
  rw [h1, degAt_congrDegree, h2, degAt_congrDegree]

/-- **The degree of a double cap product is a Kronecker pairing.** Along a homeomorphism
`ψ : A ≅ X`, `deg (ψ^* x' ∩ (ψ^* x ∩ a)) = ⟨x' ∪ x, ψ_* a⟩` for degree-one classes. -/
private lemma degAt_capProduct_homeomorph₂ {A X : TopCat.{0}} [CompactSpace A] [CompactSpace X]
    (ψ : A ≃ₜ X) (x x' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((1 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) A ((2 : ℕ) : ℤ)) :
    degAt A (by norm_num) (capProduct ℚ A univ ((1 : ℕ) : ℤ) (((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
        univ ((1 : ℕ) : ℤ)).hom x')
      (capProduct ℚ A univ ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
          univ ((1 : ℕ) : ℤ)).hom x) a)) =
    degAt X (by norm_num) (capProduct ℚ X univ ((1 + 1 : ℕ) : ℤ) ((2 : ℕ) : ℤ)
      (MMP.cupNatUniv ℚ X 1 1 x' x)
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
        ((2 : ℕ) : ℤ)).hom a)) := by
  rw [← degAt_pushforward (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap]
  erw [pushforward_capProduct_pullback_homeomorph, pushforward_capProduct_pullback_homeomorph]
  set b := (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
    ((2 : ℕ) : ℤ)).hom a
  have h1 := capProduct_cupNatUniv X 1 1 ((2 : ℕ) : ℤ) x' x b
  rw [h1, degAt_congrDegree]

/-- The swap `B ∩ A → A ∩ B`. -/
private abbrev interSwap {M : TopCat.{0}} (A B : Set M) :
    TopCat.of (B ∩ A : Set M) ⟶ TopCat.of (A ∩ B : Set M) :=
  subsetInclusionOfSubset (inter_comm B A).le

/-- **Symmetry of the Gysin classes** (Fulton §19.1, (8)): if `η_A ∩ μ = [A]` and `η_B ∩ μ = [B]`
for classes of even degree, then `j_A^* η_B ∩ [A] = j_B^* η_A ∩ [B]` in `H(A ∩ B)`. -/
private theorem gysinClass_comm {M : TopCat.{0}} {A B : Set M} (hA : IsClosed A)
    (hB : IsClosed B) (hAd : HasProperNeighbourhoodDeformations A)
    (hBd : HasProperNeighbourhoodDeformations B)
    (hABd : HasProperNeighbourhoodDeformations (A ∩ B))
    (hBAd : HasProperNeighbourhoodDeformations (B ∩ A))
    (hA'B : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (hB'A : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion B ⁻¹' A))
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) M ((2 * 3 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4)
    (b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) 4)
    (ηA : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A 2)
    (ηB : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (hηA : capProductSupport ℚ M hA hAd 2 ((2 * 3 : ℕ) : ℤ) ηA μ = congrDegree ℚ _ (by norm_num) a)
    (hηB : capProductSupport ℚ M hB hBd 2 ((2 * 3 : ℕ) : ℤ) ηB μ = congrDegree ℚ _ (by norm_num) b) :
    gysinClass hA hB hA'B 2 4 ηB a =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (interSwap A B)
        (isProperMap_subsetInclusionOfSubset (hB.inter hA) (inter_comm B A).le) (4 - 2)).hom
        (gysinClass hB hA hB'A 2 4 ηA b) := by
  have hs : (-1 : ℚˣ) ^ ((2 : ℤ) * 2) = 1 := by norm_num
  have K := pushforward_capProductSupportPullback_capProductSupport_comm ℚ M hA hB hAd hBd hABd
    hBAd hB'A hA'B ((2 * 3 : ℕ) : ℤ) hs ηA ηB μ
  rw [hηA, hηB] at K
  unfold gysinClass
  have e1 : ∀ (k k' : ℤ) (h : k = k') (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) k),
      capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion B) hA hB'A 2 k' ηA
        (congrDegree ℚ _ h x) = congrDegree ℚ _ (by rw [h])
        (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion B) hA hB'A 2 k ηA x) := by
    intro k k' h x; subst h; rfl
  have e2 : ∀ (k k' : ℤ) (h : k = k') (x : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) k),
      capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion A) hB hA'B 2 k' ηB
        (congrDegree ℚ _ h x) = congrDegree ℚ _ (by rw [h])
        (capProductSupportPullback ℚ (borelMooreHomology.subsetInclusion A) hB hA'B 2 k ηB x) := by
    intro k k' h x; subst h; rfl
  rw [e1, e2, pushforward_congrDegree, pushforward_congrDegree, congrDegree_congrDegree,
    pushforward_comp_apply'] at K
  exact ((congrDegree ℚ _ _).injective K).symm

end PairingReduction

/-- **Transport of a decomposition along homeomorphisms.** If `E ≅ X` and `E_P ≅ A_P`
compatibly with maps `j_P : E_P → E` and the inclusions `A_P ⊆ X`, and `⊕ H_k(E_P) → H_k(E)` is
onto, then so is `⊕ H_k(A_P) → H_k(X)`. -/
private lemma exists_sum_pushforward_eq_of_homeomorph {M : TopCat.{0}} {ι : Type} [Fintype ι]
    {E : TopCat.{0}} {EP : ι → TopCat.{0}} {X : Set M} {A : ι → Set M} (hA : ∀ P, IsClosed (A P))
    (hAX : ∀ P, A P ⊆ X) (φ : E ≃ₜ X) (φP : ∀ P, EP P ≃ₜ A P) (j : ∀ P, EP P ⟶ E)
    (hj : ∀ P, IsProperMap (j P)) (hcomm : ∀ P x, ((φP P x : A P) : M) = (φ (j P x) : M)) (k : ℤ)
    (hsurj : ∀ b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) E k,
      ∃ x : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (EP P) k,
        ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (j P) (hj P) k).hom (x P) = b)
    (b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X) k) :
    ∃ x : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) k,
      ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusionOfSubset (hAX P))
        (borelMooreHomology.isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) k).hom (x P) = b := by
  let F : E ⟶ TopCat.of X := TopCat.ofHom (φ : C(E, X))
  let G : TopCat.of X ⟶ E := TopCat.ofHom (φ.symm : C(X, E))
  let FP : ∀ P, EP P ⟶ TopCat.of (A P) := fun P ↦ TopCat.ofHom (φP P : C(EP P, A P))
  have hF : IsProperMap F := φ.isProperMap
  have hG : IsProperMap G := φ.symm.isProperMap
  have hFP : ∀ P, IsProperMap (FP P) := fun P ↦ (φP P).isProperMap
  obtain ⟨x', hx'⟩ := hsurj ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) G hG k).hom b)
  refine ⟨fun P ↦ (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (FP P) (hFP P) k).hom (x' P),
    ?_⟩
  have hsq : ∀ P, FP P ≫ borelMooreHomology.subsetInclusionOfSubset (hAX P) = j P ≫ F := fun P ↦ by
    ext x
    exact hcomm P x
  have hGF : G ≫ F = 𝟙 _ := by
    ext x
    simp [F, G]
  calc ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusionOfSubset (hAX P))
        (borelMooreHomology.isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) k).hom
          ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (FP P) (hFP P) k).hom (x' P))
      = ∑ P, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) F hF k).hom
          ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (j P) (hj P) k).hom (x' P)) := by
        refine Finset.sum_congr rfl fun P _ ↦ ?_
        rw [← borelMooreHomology.pushforward_comp_apply', ← borelMooreHomology.pushforward_comp_apply',
          borelMooreHomology.pushforward_congr (R := ℚ) (hsq P)]
    _ = b := by
        rw [← map_sum, hx', ← borelMooreHomology.pushforward_comp_apply',
          borelMooreHomology.pushforward_congr (R := ℚ) hGF _ (by simpa using isProperMap_id),
          borelMooreHomology.pushforward_id]
        rfl

/-! ### The geometric input -/

section Geometry

/-- The local ring at a `ℂ`-point of an algebraic scheme smooth of relative dimension `d` over
`ℂ` has dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_smoothOfRelativeDimension {U : Scheme.{0}}
    [U.Over (Spec (.of ℂ))] [LocallyOfFiniteType (U ↘ Spec (.of ℂ))] [QuasiCompact (U ↘ Spec (.of ℂ))] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    ringKrullDim (U.presheaf.stalk (p.toHom (IsLocalRing.closedPoint ℂ))) = d := by
  haveI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of ℂ))
  haveI : IsClosedImmersion (p.toHom ≫ U ↘ Spec (.of ℂ)) := by
    rw [p.toHom_comp_over]
    infer_instance
  haveI : IsClosedImmersion p.toHom := IsClosedImmersion.of_comp p.toHom (U ↘ Spec (.of ℂ))
  have h := MMP.ringKrullDim_stalk_eq_add_of_smoothOfRelativeDimension p.toHom
    (U ↘ Spec (.of ℂ)) (n := d)
    (IsLocalRing.closedPoint ℂ)
  have h0 : ∀ x : Spec (.of ℂ), ringKrullDim ((Spec (.of ℂ)).presheaf.stalk x) = 0 := by
    intro x
    haveI : x.asIdeal.IsPrime := x.isPrime
    rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of ℂ) x).commRingCatIsoToRingEquiv,
      IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal, Ideal.eq_bot_of_prime x.asIdeal]
    simp
  rw [h0] at h
  simpa using h

/-- A complex scheme `W` has dimension `d` when an affine open `V ∋ x` is smooth of relative
dimension `d` over `ℂ`. -/
private theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension_opens {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsIntegral W] {V : W.Opens}
    [V.toScheme.Over (Spec (.of ℂ))] [V.ι.IsOver (Spec (.of ℂ))] [IsAffine V.toScheme]
    [LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ))] [QuasiCompact (V.toScheme ↘ Spec (.of ℂ))]
    [IsSeparated (V.toScheme ↘ Spec (.of ℂ))] {d : ℕ}
    [SmoothOfRelativeDimension d (V.toScheme ↘ Spec (.of ℂ))] {x : W} (hx : x ∈ V) :
    topologicalKrullDim W = d := by
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton
    (⟨⟨x, hx⟩, trivial⟩ : (Set.univ : Set V.toScheme).Nonempty)
  let p : UnderlyingSpace ℂ V.toScheme :=
    (UnderlyingSpace.equivClosedPoints V.toScheme).symm ⟨y, hy⟩
  have hp : p.toHom (IsLocalRing.closedPoint ℂ) = y := by
    rw [← UnderlyingSpace.equivClosedPoints_apply, Equiv.apply_symm_apply]
  have h1 := ringKrullDim_stalk_eq_of_smoothOfRelativeDimension d p
  have h2 := UnderlyingSpace.ringKrullDim_stalk_eq_dimension (UnderlyingSpace.map V.ι p)
  rw [UnderlyingSpace.toHom_map] at h2
  change ringKrullDim (W.presheaf.stalk (V.ι (p.toHom (IsLocalRing.closedPoint ℂ)))) = _ at h2
  rw [hp] at h1 h2
  have h3 : ringKrullDim (V.toScheme.presheaf.stalk y) =
      ringKrullDim (W.presheaf.stalk (V.ι y)) :=
    ringKrullDim_eq_of_ringEquiv (V.stalkIso y).commRingCatIsoToRingEquiv
  rw [h3, h2] at h1
  change topologicalKrullDim W = _ at h1
  exact_mod_cast h1

/-- A smooth separated integral complex scheme of dimension `n` is smooth of relative dimension `n`
over `ℂ`. -/
private theorem smoothOfRelativeDimension_of_isSmoothScheme {W : Scheme.{0}} {n : ℕ}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsIntegral W] [IsSeparated (W ↘ Spec (.of ℂ))]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = n) :
    SmoothOfRelativeDimension n (W ↘ Spec (.of ℂ)) := by
  haveI : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hst⟩ := Smooth.exists_isStandardSmooth (W ↘ Spec (.of ℂ)) x
  letI := ((W ↘ Spec (.of ℂ)).appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst.out
  have hr : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((W ↘ Spec (.of ℂ)).appLE U V e).hom := ⟨ι, σ, inferInstance, inferInstance, P, rfl⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  suffices hr3 : P.dimension = n from hr3 ▸ hr
  -- the open `V` as a scheme, smooth of relative dimension `P.dimension`
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ W ↘ Spec (.of ℂ)⟩
  haveI hVo : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine V.toScheme := hV
  haveI : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ W ↘ Spec (.of ℂ)))
  haveI : QuasiCompact (V.toScheme ↘ Spec (.of ℂ)) :=
    (quasiCompact_iff_compactSpace _).mpr inferInstance
  haveI : IsSeparated (V.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsSeparated (V.ι ≫ W ↘ Spec (.of ℂ)))
  haveI : SmoothOfRelativeDimension P.dimension (V.toScheme ↘ Spec (.of ℂ)) := by
    constructor
    intro y
    have e' : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ W ↘ Spec (.of ℂ)) ⁻¹ᵁ U := fun z _ ↦ e z.2
    refine ⟨U, hU, ⊤, isAffineOpen_top _, trivial, e', ?_⟩
    have e'' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ ↦ z.2
    change RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((V.ι ≫ W ↘ Spec (.of ℂ)).appLE U ⊤ e').hom
    rw [← Scheme.Hom.appLE_comp_appLE V.ι (W ↘ Spec (.of ℂ)) U V ⊤ e e'']
    haveI : IsIso (V.ι.appLE V ⊤ e'') := by
      rw [Scheme.Opens.ι_appLE, show (homOfLE (Set.image_subset_iff.mpr e'') : V.ι ''ᵁ ⊤ ⟶ V) =
          eqToHom V.ι_image_top from Subsingleton.elim _ _]
      exact (W.presheaf.mapIso (eqToIso V.ι_image_top).op).isIso_hom
    exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := P.dimension)).cancel_right_isIso
      ((W ↘ Spec (.of ℂ)).appLE U V e) (V.ι.appLE V ⊤ e'')).2 hr
  have h := topologicalKrullDim_eq_of_smoothOfRelativeDimension_opens (d := P.dimension) hx
  rw [hdim] at h
  exact_mod_cast h.symm

/-- An integral quasi-projective complex scheme is a quasi-projective variety. -/
private theorem isQuasiProjectiveVariety {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsIntegral W]
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ))) :
    IsQuasiProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := by
  haveI : IsSeparated (W ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hWqp
  haveI : AlgebraicGeometry.IsVariety ℂ (W ↘ Spec (.of ℂ)) := {}
  exact ⟨hWqp⟩

/-- The support of a divisor which is the fibre of a projective morphism over a closed point is
proper over `ℂ`. -/
private theorem isProper_suppIdeal_subschemeι {W S : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [S.Over (Spec (.of ℂ))] {f : W ⟶ S} [f.IsOver (Spec (.of ℂ))]
    (hSqp : Stacks.HProjective.IsQuasiProjective (S ↘ Spec (.of ℂ)))
    (hf : IsProjectiveMorphism f) (x : S) (hx : IsClosed {x}) (D : Divisor W)
    (hfibre : (D.supp : Set W) = f.base ⁻¹' {x}) :
    IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))) := by
  haveI : LocallyOfFiniteType (S ↘ Spec (.of ℂ)) := hSqp.1.1
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  have hg : Set.range (D.suppIdeal.subschemeι ≫ f) ⊆ {x} := by
    rintro _ ⟨z, rfl⟩
    have hz : D.suppIdeal.subschemeι z ∈ Set.range D.suppIdeal.subschemeι := ⟨z, rfl⟩
    have hsupp : (D.suppIdeal.support : Set W) = D.supp :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp] at hz
    exact (Set.ext_iff.1 hfibre _).1 hz
  haveI : IsReduced D.suppIdeal.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have := MMP.Mori.isProper_comp_of_range_subset_singleton (S ↘ Spec (.of ℂ))
    (D.suppIdeal.subschemeι ≫ f) hx hg
  rwa [Category.assoc, CategoryTheory.comp_over f (Spec (.of ℂ))] at this

/-- The complex points of a proper complex scheme form a compact space. -/
private theorem compactSpace_underlyingSpace_of_isProper {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsProper (Z ↘ Spec (.of ℂ))] : CompactSpace (UnderlyingSpace ℂ Z) := by
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  haveI : (Z ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) := ⟨Category.comp_id _⟩
  haveI : LocallyOfFiniteType (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  haveI : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    ⟨fun p q ↦ UnderlyingSpace.ext (by
      rw [← Category.comp_id p.toHom, ← Category.comp_id q.toHom]
      exact p.toHom_comp_over.trans q.toHom_comp_over.symm)⟩
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) (Z ↘ Spec (.of ℂ))
  exact ⟨by simpa using hp.isCompact_preimage (isCompact_univ (X := UnderlyingSpace ℂ (Spec (.of ℂ))))⟩

/-- A closed subset of a closed subset proper over `ℂ` is proper over `ℂ`, with its reduced
structure. -/
private theorem isProper_vanishingIdeal_subschemeι_of_le {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    {Z Z' : TopologicalSpace.Closeds W} (h : Z ≤ Z')
    (hZ' : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z').subschemeι ≫ (W ↘ Spec (.of ℂ)))) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ (W ↘ Spec (.of ℂ))) := by
  have hle : Scheme.IdealSheafData.vanishingIdeal Z' ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
    Scheme.IdealSheafData.vanishingIdeal_antimono h
  rw [← Scheme.IdealSheafData.inclusion_subschemeι hle] at ⊢
  haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle ≫
      (Scheme.IdealSheafData.vanishingIdeal Z').subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]; infer_instance
  haveI : IsClosedImmersion (Scheme.IdealSheafData.inclusion hle) :=
    IsClosedImmersion.of_comp _ (Scheme.IdealSheafData.vanishingIdeal Z').subschemeι
  rw [Category.assoc]
  infer_instance

/-- **Ampleness on the fibre.** If `L` is ample relative to `f : W ⟶ S`, its restriction to a
closed subscheme of `W` lying over a point `x` of `S` is ample. -/
private theorem isAmple_pullback_subschemeι_of_isRelativelyAmple {W S : Scheme.{0}} {f : W ⟶ S}
    (L : W.Modules) [Stacks.Ample.IsInvertibleModule W L] (hL : IsRelativelyAmple f L) (x : S)
    (I : W.IdealSheafData) (hI : (I.support : Set W) ⊆ f.base ⁻¹' {x})
    [Stacks.Ample.IsInvertibleModule I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj L)] :
    Stacks.Ample.IsAmple I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  obtain ⟨V, -, hxV, hamp⟩ := hL x
  set U := f ⁻¹ᵁ V
  have hrange : Set.range I.subschemeι ⊆ Set.range U.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι]
    intro w hw
    have : f w = x := hI hw
    change f w ∈ V
    rw [this]; exact hxV
  let g := IsOpenImmersion.lift U.ι I.subschemeι hrange
  have hg : g ≫ U.ι = I.subschemeι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (g ≫ U.ι) := by rw [hg]; infer_instance
  haveI : IsClosedImmersion g := IsClosedImmersion.of_comp g U.ι
  haveI : Stacks.Ample.IsInvertibleModule U
      ((RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback U.ι L
  haveI : Stacks.Ample.IsInvertibleModule U ((Scheme.Modules.pullback U.ι).obj L) := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule I.subscheme
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj L)) := inferInstance
  have h0 := (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hamp
  have h1 := Scheme.Modules.isAmple_of_iso
    ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback U.ι).app L) h0
  have h2 := Scheme.Modules.isAmple_pullback_of_isClosedImmersion g _ h1
  refine (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
    (Scheme.Modules.isAmple_of_iso ?_ h2)
  exact ((Scheme.Modules.pullbackComp g U.ι).app L).trans (eqToIso (by rw [hg]))

/-- The rational Borel–Moore homology of the complex points of a projective complex scheme is
finite dimensional in every degree. -/
private theorem finiteDimensional_borelMooreHomology_of_isProjectiveMorphism {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (hZ : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (k : ℕ) :
    FiniteDimensional ℚ
      (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Z)) k) := by
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hZ
  haveI := compactSpace_underlyingSpace_of_isProper (Z := Z)
  let e := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := Z)
  haveI : CompactSpace (MMP.Analytic.ComplexPoints.analyticSpace (Z ↘ Spec (.of ℂ))) :=
    e.symm.compactSpace
  haveI := finiteDimensional_homology_analyticSpace (Z ↘ Spec (.of ℂ)) hZ k
  haveI : FiniteDimensional ℚ (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (MMP.Analytic.ComplexPoints.analyticSpace (Z ↘ Spec (.of ℂ))) k) :=
    Module.Finite.equiv (borelMooreHomologyIso _ k).symm.toLinearEquiv
  have hb := MMP.borelMooreHomology.bijective_pushforward_homeomorph ℚ
    (Y := MMP.Analytic.ComplexPoints.analyticSpace (Z ↘ Spec (.of ℂ)))
    (Y' := TopCat.of (UnderlyingSpace ℂ Z)) e (k : ℤ)
  exact Module.Finite.of_surjective _ hb.2

/-- The analytic space of a projective complex scheme is compact, with finite dimensional rational
homology in every degree. -/
private theorem compactSpace_and_finiteDimensional_analyticSpace {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (hZ : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) :
    CompactSpace (MMP.Analytic.Analytification.space (Z ↘ Spec (.of ℂ))) ∧
      ∀ k : ℕ, FiniteDimensional ℚ (MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (MMP.Analytic.Analytification.space (Z ↘ Spec (.of ℂ))) k) := by
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hZ
  haveI := compactSpace_underlyingSpace_of_isProper (Z := Z)
  let e := MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := Z)
  haveI : CompactSpace (MMP.Analytic.ComplexPoints.analyticSpace (Z ↘ Spec (.of ℂ))) :=
    e.symm.compactSpace
  refine ⟨e.symm.compactSpace, fun k ↦ ?_⟩
  haveI := finiteDimensional_homology_analyticSpace (Z ↘ Spec (.of ℂ)) hZ k
  exact Module.Finite.equiv (borelMooreHomologyIso _ k).symm.toLinearEquiv

/-- A closed embedding of schemes preserves heights of points. -/
private theorem height_apply_of_isClosedEmbedding {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f) (y : X) :
    Order.height (f y) = Order.height y := by
  have hle : ∀ a b : X, f a ≤ f b ↔ a ≤ b := fun a b ↦ by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact hf.isInducing.specializes_iff
  let g : Set.Iic y ↪o Set.Iic (f y) :=
    { toFun := fun z ↦ ⟨f z.1, (hle _ _).2 z.2⟩
      inj' := fun a b h ↦ Subtype.ext (hf.injective (congrArg Subtype.val h))
      map_rel_iff' := fun {a b} ↦ hle a.1 b.1 }
  have hsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    have hsp : f y ⤳ w := Scheme.le_iff_specializes.1 hw
    have hmem : w ∈ Set.range f :=
      hsp.mem_closed hf.isClosed_range ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hmem
    exact ⟨⟨z, (hle _ _).1 hw⟩, rfl⟩
  have e := Order.krullDim_eq_of_orderIso (OrderIso.ofSurjective g hsurj)
  rw [← Order.height_eq_krullDim_Iic, ← Order.height_eq_krullDim_Iic] at e
  exact_mod_cast e.symm

/-- A prime divisor on an integral algebraic complex scheme of dimension three is a surface. -/
private theorem topologicalKrullDim_primeDivisor_subscheme {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] (hdim : topologicalKrullDim W = 3)
    (P : MMP.Mori.PrimeDivisor W) : topologicalKrullDim P.idealSheaf.subscheme = 2 := by
  haveI := P.integral
  haveI : LocallyOfFiniteType (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (P.idealSheaf.subschemeι ≫ W ↘ Spec (.of ℂ))
    infer_instance
  set E := P.idealSheaf.subscheme
  have hE : topologicalKrullDim E = Order.krullDim E :=
    Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints
  have hW : Order.krullDim W = 3 := by
    rw [← hdim]; exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  have h := MMP.height_add_coheight_eq_krullDim ℂ (genericPoint E)
  have hc : Order.coheight (genericPoint E) = 0 :=
    Order.coheight_eq_zero.2 fun _ _ ↦
      (Scheme.le_iff_specializes).2 ((genericPoint_spec E).specializes trivial)
  rw [hc, add_zero] at h
  rw [hE, ← h]
  have hh := height_apply_of_isClosedEmbedding P.idealSheaf.subschemeι
    P.idealSheaf.subschemeι.isClosedEmbedding (genericPoint E)
  change Order.height P.genericPoint = Order.height (genericPoint E) at hh
  rw [← hh]
  have h3 := MMP.height_add_coheight_eq_krullDim ℂ P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hW] at h3
  have h4 : Order.height P.genericPoint + 1 = (3 : ℕ∞) :=
    WithBot.coe_injective (h3.trans rfl)
  have : Order.height P.genericPoint = 2 := by
    induction h' : Order.height P.genericPoint using ENat.recTopCoe with
    | top => rw [h'] at h4; simp at h4
    | coe a =>
      rw [h'] at h4
      have : a + 1 = 3 := by exact_mod_cast h4
      norm_cast; omega
  rw [this]; rfl

/-- A reduced closed subscheme supported in a closed subset which is proper over `ℂ` (with its
reduced structure) is proper over `ℂ`. -/
private theorem isProper_subschemeι_of_subset {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    (I : W.IdealSheafData) [IsReduced I.subscheme] (Z : TopologicalSpace.Closeds W)
    (hIZ : (I.support : Set W) ⊆ Z)
    (hZ : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ (W ↘ Spec (.of ℂ)))) :
    IsProper (I.subschemeι ≫ (W ↘ Spec (.of ℂ))) := by
  have hker : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    intro w hw
    have hw' : w ∈ closure (Set.range I.subschemeι) := hw
    rw [Scheme.IdealSheafData.range_subschemeι, I.support.isClosed.closure_eq] at hw'
    exact hIZ hw'
  let g := IsClosedImmersion.lift (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    I.subschemeι hker
  have hg : g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = I.subschemeι :=
    IsClosedImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := by
    rw [hg]; infer_instance
  haveI : IsClosedImmersion g :=
    IsClosedImmersion.of_comp g (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [← hg, Category.assoc]
  infer_instance

/-- **The components of an antiample snc fibre are smooth projective surfaces.** -/
private theorem component_isProjectiveMorphism_and_isSmoothScheme {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    (hdim : topologicalKrullDim W = 3) (D : Divisor W) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hprop : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hamp : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (P : D.support) :
    IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      IsProjectiveMorphism (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      IsSmoothScheme (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim P.1.idealSheaf.subscheme = 2 := by
  haveI := P.1.integral
  have hprP : IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    isProper_subschemeι_of_subset P.1.idealSheaf D.supp
      (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 P.2)) hprop
  haveI := hprP
  exact ⟨hprP, Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isProjectiveMorphism_of_isAmple _ _
      (hamp P.1 P.2), hsnc.1 P.1 P.2, topologicalKrullDim_primeDivisor_subscheme hdim P.1⟩

/-- **The components of an antiample snc fibre are smooth projective surfaces**, with the instances
of the Hodge decomposition and of Poincaré duality. -/
private theorem component_instances {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    (hdim : topologicalKrullDim W = 3) (D : Divisor W) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hprop : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hamp : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (P : D.support) :
    AlgebraicGeometry.IsProjectiveVariety ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      SmoothOfRelativeDimension 2 (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      IsIntegral P.1.idealSheaf.subscheme := by
  haveI := P.1.integral
  obtain ⟨hpr, hproj, hsmP, hdimP⟩ :=
    component_isProjectiveMorphism_and_isSmoothScheme hdim D hsnc hprop hamp P
  haveI := hpr
  haveI : AlgebraicGeometry.IsVariety ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := {}
  haveI := smoothOfRelativeDimension_of_isSmoothScheme hsmP hdimP
  exact ⟨⟨hproj⟩, inferInstance, inferInstance⟩

/-- **The curves over the double curves are smooth projective curves**, on which the restriction
of `𝒪(-D)` is ample. -/
private theorem curve_instances {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    (hdim : topologicalKrullDim W = 3) (D : Divisor W) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hprop : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hamp : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    (P : D.support) {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η)
    (hP : P ∈ MMP.Fourfold.comps D η) :
    IsProper ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      IsProjectiveMorphism
        ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      AlgebraicGeometry.IsProjectiveVariety ℂ
        ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      SmoothOfRelativeDimension 1
        ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme = 1 ∧
      Stacks.Ample.IsAmple (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme
        ((Scheme.Modules.pullback (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι).obj
          ((Scheme.Modules.pullback P.1.idealSheaf.subschemeι).obj (-D).divisorialSheaf)) := by
  haveI := P.1.integral
  obtain ⟨hpr, hproj, hsmP, hdimP⟩ :=
    component_isProjectiveMorphism_and_isSmoothScheme hdim D hsnc hprop hamp P
  haveI := hpr
  set C := MMP.Fourfold.curveDiv hsnc hdim P hη hP
  haveI := C.integral
  haveI : IsProper (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change IsProper (C.idealSheaf.subschemeι ≫ P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    infer_instance
  have hamp' := Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite
    C.idealSheaf.subschemeι _ (hamp P.1 P.2)
  have hprojC : IsProjectiveMorphism (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isProjectiveMorphism_of_isAmple _ _ hamp'
  haveI : AlgebraicGeometry.IsVariety ℂ (C.idealSheaf.subscheme ↘ Spec (.of ℂ)) := {}
  have h2 := MMP.Fourfold.krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have hdim1 := MMP.Fourfold.topologicalKrullDim_primeDivisor_eq h2 C
  haveI := smoothOfRelativeDimension_of_isSmoothScheme (n := 1)
    (MMP.Fourfold.isSmoothScheme_curveDiv hsnc hdim P hη hP) (by rw [hdim1]; rfl)
  exact ⟨inferInstance, hprojC, ⟨hprojC⟩, inferInstance, hdim1, hamp'⟩

/-- On a proper scheme over `ℂ`, an ample invertible module in the sense of Stacks is ample in the
sense of the Hodge decomposition (a positive power is very ample). -/
private lemma intersectionIsAmple_of_isAmple {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (hM : Stacks.Ample.IsAmple X M) : MMP.Intersection.IsAmple ℂ M := by
  have htfae := Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of ℂ)) M
  obtain ⟨d, hd, h5⟩ := (htfae.out 1 5).1 hM
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X M d
  exact ⟨d, hd, MMP.Resolution.Bridges.isVeryAmple_of_hasImmersionTwistOver ℂ _ _ eP h5⟩

end Geometry

/-! ### First Chern classes of divisorial sheaves -/

section ChernDivisor

open MMP.Analytic

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X] [CompactSpace X]

/-- On a smooth scheme every divisorial sheaf is invertible. -/
private lemma isInvertible_divisorialSheaf_of_isSmoothScheme
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) (N : Divisor X) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N.divisorialSheaf :=
  (MMP.Fourfold.isCartier_of_isSmoothScheme hsm N).isInvertibleModule_divisorialSheaf

/-- **Additivity of the first Chern class** of divisorial sheaves on a smooth scheme:
`c₁(𝒪(N + N')) = c₁(𝒪(N)) + c₁(𝒪(N'))`. -/
private theorem algebraicFirstChernClass_divisorialSheaf_add
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) (N N' : Divisor X) :
    @algebraicFirstChernClass X _ (N + N').divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm (N + N')) =
      @algebraicFirstChernClass X _ N.divisorialSheaf
          (isInvertible_divisorialSheaf_of_isSmoothScheme hsm N) +
        @algebraicFirstChernClass X _ N'.divisorialSheaf
          (isInvertible_divisorialSheaf_of_isSmoothScheme hsm N') := by
  have hN := MMP.Fourfold.isCartier_of_isSmoothScheme hsm N
  have hN' := MMP.Fourfold.isCartier_of_isSmoothScheme hsm N'
  haveI := isInvertible_divisorialSheaf_of_isSmoothScheme hsm N
  haveI := isInvertible_divisorialSheaf_of_isSmoothScheme hsm N'
  haveI := isInvertible_divisorialSheaf_of_isSmoothScheme hsm (N + N')
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
        N.divisorialSheaf).obj N'.divisorialSheaf) :=
    hN.isInvertibleModule_tensorSheaf hN'
  have e := algebraicFirstChernClass_eq_of_iso (hN.divisorialSheafTensorIso hN')
  rw [algebraicFirstChernClass_sheafTensor] at e
  exact e.symm

/-- The first Chern class of the trivial divisorial sheaf vanishes. -/
private theorem algebraicFirstChernClass_divisorialSheaf_zero
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) :
    @algebraicFirstChernClass X _ (0 : Divisor X).divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm 0) = 0 := by
  have h := algebraicFirstChernClass_divisorialSheaf_add hsm (0 : Divisor X) 0
  simp only [add_zero] at h
  exact left_eq_add.mp h

/-- `c₁(𝒪(-N)) = -c₁(𝒪(N))`. -/
private theorem algebraicFirstChernClass_divisorialSheaf_neg
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) (N : Divisor X) :
    @algebraicFirstChernClass X _ (-N).divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm (-N)) =
      -@algebraicFirstChernClass X _ N.divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm N) := by
  have h := algebraicFirstChernClass_divisorialSheaf_add hsm (-N) N
  simp only [neg_add_cancel] at h
  rw [algebraicFirstChernClass_divisorialSheaf_zero hsm] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- `c₁(𝒪(∑ᵢ nᵢ Nᵢ)) = ∑ᵢ nᵢ c₁(𝒪(Nᵢ))`. -/
private theorem algebraicFirstChernClass_divisorialSheaf_sum
    (hsm : IsSmoothScheme (X ↘ Spec (.of ℂ))) {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (N : ι → Divisor X) :
    @algebraicFirstChernClass X _ (∑ i ∈ s, n i • N i).divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm _) =
      ∑ i ∈ s, n i • @algebraicFirstChernClass X _ (N i).divisorialSheaf
        (isInvertible_divisorialSheaf_of_isSmoothScheme hsm (N i)) := by
  classical
  have hsmul : ∀ (k : ℕ) (N : Divisor X),
      @algebraicFirstChernClass X _ (k • N).divisorialSheaf
          (isInvertible_divisorialSheaf_of_isSmoothScheme hsm _) =
        k • @algebraicFirstChernClass X _ N.divisorialSheaf
          (isInvertible_divisorialSheaf_of_isSmoothScheme hsm N) := by
    intro k N
    induction k with
    | zero => simpa using algebraicFirstChernClass_divisorialSheaf_zero hsm
    | succ k ih =>
      rw [succ_nsmul, algebraicFirstChernClass_divisorialSheaf_add hsm, ih, succ_nsmul]
  induction s using Finset.induction_on with
  | empty => simpa using algebraicFirstChernClass_divisorialSheaf_zero hsm
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, algebraicFirstChernClass_divisorialSheaf_add hsm,
      ih, hsmul]

end ChernDivisor

/-! ### Localized first Chern classes -/

section Localized

open borelMooreHomology Set

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The complex points of a closed subscheme, as the points of `X(ℂ)` over its support. -/
private noncomputable def subschemePointsHomeomorph (I : X.IdealSheafData) :
    UnderlyingSpace ℂ I.subscheme ≃ₜ UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set X) :=
  (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion I.subschemeι).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [UnderlyingSpace.range_map_of_isClosedImmersion,
      Scheme.IdealSheafData.range_subschemeι]))

/-- `σ⁻¹(0(X(ℂ))) = Z(σ)(ℂ)` for a morphism `σ : X ⟶ 𝐕(ℰ)` over `ℂ`, read on `TopCat`. -/
private lemma preimage_range_zeroSection_eq {E : X.Modules} [E.IsQuasicoherent]
    (σ : X ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))] :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E)) =
      UnderlyingSpace.pointsOver (K := ℂ) ((MMP.Modules.zeroLocus E σ).support : Set X) :=
  MMP.Modules.preimage_mapFun_range_zeroSection σ

/-- `σ⁻¹(0(X(ℂ)))` is closed in `X(ℂ)`. -/
private lemma isClosed_preimage_range_zeroSection' {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    {E : Y.Modules} [E.IsQuasicoherent] (σ : Y ⟶ MMP.Modules.totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] :
    IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) :=
  (MMP.Modules.isClosed_range_zeroSection (E := E)).preimage
    (UnderlyingSpace.map (K := ℂ) σ).continuous

/-- The pull-back `f^*σ` of a section vanishes exactly over `f⁻¹(σ⁻¹(0))`, on complex points. -/
private lemma preimage_zeroLocus_pullbackSectionMap {X' : Scheme.{0}} [X'.Over (Spec (.of ℂ))]
    (f : X' ⟶ X) [f.IsOver (Spec (.of ℂ))] {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ MMP.Modules.totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) :
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (MMP.Modules.pullbackSectionMap f hσp))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ)
          (MMP.Modules.zeroSection ((Scheme.Modules.pullback f).obj E))) =
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)).hom ⁻¹'
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) :=
  MMP.Modules.preimage_zeroLocus_of_comp σ _ (MMP.Modules.baseChangeMap_proj f E)
    (MMP.Modules.isFibrewiseIso_baseChangeMap f E 1)
    (MMP.Modules.pullbackSectionMap_baseChangeMap f hσp)

/-- The localized first Chern class `σ^* u_ℰ` of a section `σ` of the line bundle `𝐕(ℰ)` of a
Stacks module `ℰ`, locally free of rank one, with supports in the points over its zero scheme
`I`. -/
private noncomputable def localizedClass {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : X ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))] (I : X.IdealSheafData)
    (hI : MMP.Modules.zeroLocus E σ = I) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
      (UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set X)) ((2 * 1 : ℕ) : ℤ) :=
  cohomologyWithSupports.congrIndex ℚ _
    (congrArg compl (by rw [← hI]; exact preimage_range_zeroSection_eq σ)) rfl
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
      (range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom
      (MMP.Modules.thomClass ℚ E 1))

/-- The cycle class of the Stacks cycle `[V]_k` of a complex variety `V` of dimension `k` is its
fundamental class. -/
private theorem cycleClass_cycleAssociatedToClosedSubscheme_id_eq {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] {k : ℕ}
    (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    {μV : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hμV : IsVarietyFundamentalClass ℚ hk μV) :
    MMP.Chow.cycleClass ℚ k (Stacks.Chow.cycleAssociatedToClosedSubscheme
      (Stacks.Chow.fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (𝟙 V) k) = μV := by
  have hη : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (V ↘ Spec (.of ℂ)) (_root_.genericPoint V) = (k : ℤ) :=
    Stacks.Chow.relativeDimension_fieldChowSituation_genericPoint (V ↘ Spec (.of ℂ)) hk.symm
  have hcyc : Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation ℂ)
      (V ↘ Spec (.of ℂ)) (𝟙 V) k = Stacks.Chow.pointCycle (Stacks.Chow.fieldChowSituation ℂ)
        (V ↘ Spec (.of ℂ)) k (_root_.genericPoint V) hη := by
    refine Subtype.ext ?_
    ext y
    rw [Stacks.Chow.pointCycle_apply]
    by_cases hy : y = _root_.genericPoint V
    · subst hy
      rw [if_pos rfl]
      exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint _ _
        (𝟙 V) k hη
    · rw [if_neg hy]
      exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne _ _ (𝟙 V) k hy
  rw [hcyc, MMP.Chow.cycleClass_pointCycle]
  have hbot : Stacks.Chow.integralComponentAt (_root_.genericPoint V) = ⊥ :=
    Scheme.IdealSheafData.eq_bot_of_support_eq_top' _ (TopologicalSpace.Closeds.ext (by
      rw [Stacks.Chow.coe_support_integralComponentAt, TopologicalSpace.Closeds.coe_top]
      exact genericPoint_spec V))
  haveI : IsIso (Stacks.Chow.integralComponentAt (_root_.genericPoint V)).subschemeι := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.IdealSheafData.ker_subschemeι, hbot]
  exact (hμV.eq (IsVarietyFundamentalClass.pushforward_of_isIso
    (Stacks.Chow.integralComponentAt (_root_.genericPoint V)).subschemeι hk
    (existsUnique_isVarietyFundamentalClass ℚ
      (MMP.Chow.natCast_eq_dimension_integralComponentAt _ hη)).choose_spec.1)).symm

/-- **Fulton's Lemma 19.1.3 for a reduced zero scheme**: the localized Chern class of a section
whose zero scheme is the variety `I` is dual to the fundamental class of `I`. -/
private theorem capProductSupport_localizedClass [IsIntegral X] [IsNormal X]
    {k : ℕ} (hn : ((k + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X)) (2 * (k + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hn μ) (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hk : ((k : ℕ) : WithBot ℕ∞) = topologicalKrullDim I.subscheme)
    {μI : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ I.subscheme)) (2 * k : ℕ)}
    (hμI : IsVarietyFundamentalClass ℚ hk μI)
    {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : X ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) (hσ0 : σ ≠ MMP.Modules.zeroSection E)
    (hI : MMP.Modules.zeroLocus E σ = I) :
    capProductSupport ℚ _ (UnderlyingSpace.isClosed_pointsOver I.support.isClosed)
        (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver X I.support)
        ((2 * 1 : ℕ) : ℤ) ((2 * (k + 1) : ℕ) : ℤ) (localizedClass σ I hI) μ =
      congrDegree ℚ _ (by push_cast; ring)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph I : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ I.subscheme, UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set X))))
          (subschemePointsHomeomorph I).isProperMap (2 * k : ℕ)).hom μI) := by
  subst hI
  have h1 : (pushforward ℚ (ModuleCat.of ℚ ℚ) (MMP.Modules.zeroLocusHom σ)
      (MMP.Modules.isProperMap_zeroLocusHom σ) (2 * k : ℕ)).hom μI =
      congrDegree ℚ _ (by push_cast; ring) (MMP.Modules.localizedTopChernCap σ ℚ 1 _ μ) := by
    have h := MMP.Modules.LocalizedFirstChernFormula.of_isNormal ℚ hn hσp hσ0 μ hμ
    rw [cycleClass_cycleAssociatedToClosedSubscheme_id_eq hk hμI] at h
    exact h
  have hS := isClosed_preimage_range_zeroSection' σ
  unfold localizedClass
  rw [capProductSupport_congrIndex ℚ _ hS _ (MMP.Modules.hasProperNeighbourhoodDeformations_preimage σ)
    _ (preimage_range_zeroSection_eq σ)]
  have h2 : capProductSupport ℚ _ hS (MMP.Modules.hasProperNeighbourhoodDeformations_preimage σ)
      ((2 * 1 : ℕ) : ℤ) ((2 * (k + 1) : ℕ) : ℤ)
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom
          (MMP.Modules.thomClass ℚ E 1)) μ =
      MMP.Modules.localizedTopChernCap σ ℚ 1 _ μ := by
    rw [MMP.Modules.localizedTopChernCap, capProductSupportPullback_apply]
  rw [h2, (congrDegree_eq_iff_eq_congrDegree_symm ℚ _ _ _ _).1 h1.symm, pushforward_congrDegree,
    congrDegree_congrDegree, ← pushforward_comp_apply']
  have hmap : MMP.Modules.zeroLocusHom σ ≫ subsetInclusionOfSubset
      (preimage_range_zeroSection_eq σ).le =
      TopCat.ofHom ((subschemePointsHomeomorph (MMP.Modules.zeroLocus E σ) : _ ≃ₜ _) :
        C(UnderlyingSpace ℂ (MMP.Modules.zeroLocus E σ).subscheme,
          UnderlyingSpace.pointsOver (K := ℂ) ((MMP.Modules.zeroLocus E σ).support : Set X))) := by
    ext p; rfl
  rw [pushforward_congr (R := ℚ) hmap _
    (subschemePointsHomeomorph (MMP.Modules.zeroLocus E σ)).isProperMap]

private lemma toCohomology_congrIndex {Y : TopCat.{0}} {S S' : Set Y} (h : Sᶜ = S'ᶜ) (j : ℤ)
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y S j) :
    (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y S' j).hom
        (cohomologyWithSupports.congrIndex ℚ Y h rfl x) =
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y S j).hom x := by
  obtain rfl : S = S' := compl_injective h
  rfl

/-- **The forgotten localized class is the first Chern class**: for a section `σ` of `𝐕(𝓝^∨)`,
`𝓝` invertible, the localized class `σ^* u` forgets to `c₁(𝓝)`. -/
private theorem toCohomology_localizedClass {N : X.Modules} [Stacks.Ample.IsInvertibleModule X N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (σ : X ⟶ MMP.Modules.totalSpace (Scheme.Modules.dual N)) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj (Scheme.Modules.dual N) = 𝟙 X)
    (I : X.IdealSheafData) (hI : MMP.Modules.zeroLocus _ σ = I) :
    (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
        (UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set X)) ((2 * 1 : ℕ) : ℤ)).hom
        (localizedClass σ I hI) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
          TopCat.of (UnderlyingSpace ℂ X) ⟶ MMP.Analytic.Analytification.space (X ↘ Spec (.of ℂ))) univ 2).hom
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (MMP.Analytic.algebraicFirstChernClass N)) := by
  unfold localizedClass
  rw [toCohomology_congrIndex]
  exact MMP.Modules.toCohomology_pullback_thomClass_dual ℚ N hσp

end Localized

/-! ### The assembly of the radical argument -/

section Assembly

open borelMooreHomology Set

/-- The pairing `(u, v) ↦ deg (v|_{A ∩ B} ∩ (u|_{A ∩ B} ∩ (j_A^* η ∩ [A])))` of degree-one classes
on two compact closed sets, against the Gysin class of `η ∈ H²(M, M - B)` on `[A]`. -/
private noncomputable def tauPair {M : TopCat.{0}} {A B : Set M} [CompactSpace A]
    (hA : IsClosed A) (hB : IsClosed B)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4)
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) univ 1)
    (v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) univ 1) : ℚ :=
  haveI : CompactSpace (A ∩ B : Set M) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace A›).inter_right hB)
  degAt (TopCat.of (A ∩ B : Set M)) (by norm_num)
    (capProduct ℚ (TopCat.of (A ∩ B : Set M)) univ 1 (4 - 2 - 1)
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interRight A B) univ 1).hom v)
      (capProduct ℚ (TopCat.of (A ∩ B : Set M)) univ 1 (4 - 2)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom u)
        (gysinClass hA hB hd 2 4 η a)))

/-- The bilinear form `(u, v) ↦ deg (v ∩ (u ∩ z))` of degree-one classes against a class `z` of
degree two on a compact space. -/
private noncomputable def capPair (Y : TopCat.{0}) [CompactSpace Y]
    (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (4 - 2)) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ 1 →ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ 1 →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun u v ↦ degAt Y (by norm_num)
    (capProduct ℚ Y univ 1 (4 - 2 - 1) v (capProduct ℚ Y univ 1 (4 - 2) u z)))
    (fun u u' v ↦ by simp only [map_add, LinearMap.add_apply])
    (fun r u v ↦ by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun u v v' ↦ by simp only [map_add, LinearMap.add_apply])
    (fun r u v ↦ by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])

/-- `capPair` with its degrees written as natural numbers. -/
private lemma capPair_apply (Y : TopCat.{0}) [CompactSpace Y]
    (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (4 - 2))
    (u v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ 1) :
    capPair Y z u v = degAt Y (by norm_num) (capProduct ℚ Y univ ((1 : ℕ) : ℤ)
      (((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) v (capProduct ℚ Y univ ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) u z)) :=
  rfl

/-- `capPair` is additive in the class. -/
private lemma capPair_sum (Y : TopCat.{0}) [CompactSpace Y] {κ : Type} (s : Finset κ)
    (z : κ → borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (4 - 2))
    (u v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ 1) :
    capPair Y (∑ k ∈ s, z k) u v = ∑ k ∈ s, capPair Y (z k) u v := by
  simp only [capPair, LinearMap.mk₂_apply, map_sum]

/-- **Projection formula for `capPair`.** -/
private lemma capPair_pushforward {Y Y' : TopCat.{0}} [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ Y') (hf : IsProperMap f) (z : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y (4 - 2))
    (u v : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y' univ 1) :
    capPair Y' ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf (4 - 2)).hom z) u v =
      capPair Y z ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ 1).hom u)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ 1).hom v) :=
  (degAt_capProduct_pullback f hf u v z).symm

set_option maxRecDepth 10000 in
/-- **`capPair` along a homeomorphism is a Kronecker pairing.** -/
private lemma capPair_homeomorph {A X : TopCat.{0}} [CompactSpace A] [CompactSpace X]
    (ψ : A ≃ₜ X) (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) A ((2 : ℕ) : ℤ))
    (x x' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((1 : ℕ) : ℤ)) :
    capPair A a
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
          univ ((1 : ℕ) : ℤ)).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
          univ ((1 : ℕ) : ℤ)).hom x') =
      -kron X (1 + 1) (MMP.cupNatUniv ℚ X 1 1 x x')
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
          ((2 : ℕ) : ℤ)).hom a) := by
  refine (capPair_apply A a _ _).trans ?_
  rw [degAt_capProduct_homeomorph₂, cupNatUniv_one_one_comm X x x']
  simp only [map_neg, LinearMap.neg_apply]
  rfl

set_option maxRecDepth 10000 in
/-- **The pairing against the class of a curve.** For a proper map `j : C → Y` and a
homeomorphism `ψ : C ≅ X`, if the restrictions `j^* u`, `j^* v` are `ψ^* x`, `ψ^* x'`, then
`capPair Y (j_* μ) u v = -⟨x ∪ x', ψ_* μ⟩`. -/
private lemma capPair_pushforward_eq_neg_kron {Y Y₁ Y₂ Y₁' Y₂' C X : TopCat.{0}} [CompactSpace Y]
    [CompactSpace C] [CompactSpace X] (j : C ⟶ Y) (hj : IsProperMap j) (ψ : C ≃ₜ X)
    (i₁ : Y ⟶ Y₁) (i₁' : Y₁ ⟶ Y₁') (i₂ : Y ⟶ Y₂) (i₂' : Y₂ ⟶ Y₂') (f₁ : X ⟶ Y₁')
    (f₂ : X ⟶ Y₂') (h₁ : j ≫ i₁ ≫ i₁' = TopCat.ofHom (ψ : C(C, X)) ≫ f₁)
    (h₂ : j ≫ i₂ ≫ i₂' = TopCat.ofHom (ψ : C(C, X)) ≫ f₂)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) C ((2 * 1 : ℕ) : ℤ))
    (x₁ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y₁' univ ((1 : ℕ) : ℤ))
    (x₂ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y₂' univ ((1 : ℕ) : ℤ)) :
    capPair Y (congrDegree ℚ Y (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) j hj ((2 * 1 : ℕ) : ℤ)).hom μ))
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) i₁ univ 1).hom
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) i₁' univ 1).hom x₁))
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) i₂ univ 1).hom
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) i₂' univ 1).hom x₂)) =
      -kron X (1 + 1) (MMP.cupNatUniv ℚ X 1 1
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f₁ univ ((1 : ℕ) : ℤ)).hom x₁)
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f₂ univ ((1 : ℕ) : ℤ)).hom x₂))
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(C, X))) ψ.isProperMap
          ((2 * 1 : ℕ) : ℤ)).hom μ) := by
  have e₁ := (congrArg (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) j univ 1).hom
    (pullback_univ_comp i₁ i₁' 1 x₁).symm).trans ((pullback_univ_comp j (i₁ ≫ i₁') 1 x₁).symm.trans
      ((pullback_univ_congr h₁ 1 x₁).trans (pullback_univ_comp _ f₁ 1 x₁)))
  have e₂ := (congrArg (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) j univ 1).hom
    (pullback_univ_comp i₂ i₂' 1 x₂).symm).trans ((pullback_univ_comp j (i₂ ≫ i₂') 1 x₂).symm.trans
      ((pullback_univ_congr h₂ 1 x₂).trans (pullback_univ_comp _ f₂ 1 x₂)))
  rw [← pushforward_congrDegree_apply]
  refine (capPair_pushforward j hj _ _ _).trans ?_
  refine (congrArg₂ (α := cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) C univ 1)
    (β := cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) C univ 1)
    (fun u v ↦ capPair C (congrDegree ℚ C (by norm_num) μ) u v) e₁ e₂).trans ?_
  exact (capPair_homeomorph ψ (congrDegree ℚ C (by norm_num) μ) _ _).trans rfl

/-- The pairing `tauPair` as a bilinear form. -/
private noncomputable def tauForm {M : TopCat.{0}} {A B : Set M} [CompactSpace A]
    (hA : IsClosed A) (hB : IsClosed B)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) univ 1 →ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of B) univ 1 →ₗ[ℚ] ℚ :=
  haveI : CompactSpace (A ∩ B : Set M) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace A›).inter_right hB)
  (capPair (TopCat.of (A ∩ B : Set M)) (gysinClass hA hB hd 2 4 η a)).compl₁₂
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interRight A B) univ 1).hom

/-- The pairing `(u, u') ↦ deg (u'|_{A ∩ B} ∩ (u|_{A ∩ B} ∩ (j_A^* η ∩ [A])))` of two degree-one
classes on `A`. -/
private noncomputable def tauForm' {M : TopCat.{0}} {A B : Set M} [CompactSpace A]
    (hA : IsClosed A) (hB : IsClosed B)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' B))
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M B 2)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) univ 1 →ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) univ 1 →ₗ[ℚ] ℚ :=
  haveI : CompactSpace (A ∩ B : Set M) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace A›).inter_right hB)
  (capPair (TopCat.of (A ∩ B : Set M)) (gysinClass hA hB hd 2 4 η a)).compl₁₂
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (interLeft A B) univ 1).hom

/-- On the diagonal the two pairings agree. -/
private lemma tauForm'_self {M : TopCat.{0}} {A : Set M} [CompactSpace A] (hA : IsClosed A)
    (hd : HasProperNeighbourhoodDeformations (borelMooreHomology.subsetInclusion A ⁻¹' A))
    (η : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M A 2)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) 4) :
    tauForm' hA hA hd η a = tauForm hA hA hd η a := by
  have h : interRight A A = interLeft A A := by ext; rfl
  unfold tauForm' tauForm
  rw [h]

set_option maxRecDepth 10000 in
/-- **The diagonal identity for the component pairings.** If the restrictions of the dual classes
`η_Q` to `A_P ≅ X` add up, with weights `m_Q`, to `-ψ^* c`, then
`∑_Q m_Q τ'_{PQ}(ψ^* x, ψ^* x') = ⟨x ∪ x' ∪ c, ψ_* [A_P]⟩`. -/
private theorem sum_tauForm'_eq_kron {M : TopCat.{0}} {ι : Type} [Fintype ι] (A : ι → Set M)
    [∀ P, CompactSpace (A P)] (hA : ∀ P, IsClosed (A P))
    (hA'B : ∀ P Q, HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (A P) ⁻¹' A Q))
    (η : ∀ Q, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M (A Q) 2)
    (P : ι) (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) 4) (m : ι → ℚ)
    {X : TopCat.{0}} [CompactSpace X] (ψ : A P ≃ₜ X)
    (cX : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((2 : ℕ) : ℤ))
    (hsum : ∑ Q, m Q • (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P))
        (borelMooreHomology.subsetInclusion (A P) ⁻¹' A Q) 2).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
          (borelMooreHomology.subsetInclusion (A P)) (A Q) 2).hom (η Q)) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X)))
        univ 2).hom (-cX))
    (x x' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ ((1 : ℕ) : ℤ)) :
    ∑ Q, m Q * tauForm' (hA P) (hA Q) (hA'B P Q) (η Q) a
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X)))
          univ 1).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X)))
          univ 1).hom x') =
      kron X (3 + 1) (MMP.cupNatUniv ℚ X (1 + 1) 2
        (MMP.cupNatUniv ℚ X 1 1 x x') cX)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X))) ψ.isProperMap 4).hom a) := by
  set u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) univ 1 :=
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X)))
      univ 1).hom x
  set u' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) univ 1 :=
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A P, X)))
      univ 1).hom x'
  -- each pairing is read on `A_P`
  have hterm : ∀ Q, tauForm' (hA P) (hA Q) (hA'B P Q) (η Q) a u u' =
      degAt (TopCat.of (A P)) (by norm_num) (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2 - 1) u'
        (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2) u
          (capProduct ℚ (TopCat.of (A P)) univ 2 4
            ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P))
              (borelMooreHomology.subsetInclusion (A P) ⁻¹' A Q) 2).hom
              ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
                (borelMooreHomology.subsetInclusion (A P)) (A Q) 2).hom (η Q))) a))) := by
    intro Q
    haveI : CompactSpace (A P ∩ A Q : Set M) := isCompact_iff_compactSpace.1
      ((isCompact_iff_compactSpace.2 (inferInstance : CompactSpace (A P))).inter_right (hA Q))
    rw [← pushforward_interLeft_gysinClass (hA P) (hA Q) (hA'B P Q) (η Q) a]
    exact degAt_capProduct_pullback (interLeft (A P) (A Q))
      (isProperMap_subsetInclusionOfSubset ((hA P).inter (hA Q)) inter_subset_left) u u' _
  simp only [hterm]
  have hlin : ∀ (ζ : ι → cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) univ 2),
      ∑ Q, m Q * degAt (TopCat.of (A P)) (by norm_num)
        (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2 - 1) u'
          (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2) u
            (capProduct ℚ (TopCat.of (A P)) univ 2 4 (ζ Q) a))) =
      degAt (TopCat.of (A P)) (by norm_num)
        (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2 - 1) u'
          (capProduct ℚ (TopCat.of (A P)) univ 1 (4 - 2) u
            (capProduct ℚ (TopCat.of (A P)) univ 2 4 (∑ Q, m Q • ζ Q) a))) := by
    intro ζ
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hlin, hsum]
  erw [degAt_capProduct_homeomorph ψ x x' (-cX) a]
  rw [cupNatUniv_one_one_comm X x x']
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rfl

/-- **The radical argument, assembled.** Let compact closed sets `A_P` of `M` carry classes
`[A_P] ∈ H₄(A_P)` with dual classes `η_P`, and degree-one classes `V_P → H¹(A_P)` realising
Poincaré duality on `A_P`. If the double sum of the pairings `tauPair` is, after scaling by
positive weights `m`, a rational form `B` with trivial left radical, then every
`c_P ∈ H³(M, M - A_P)` killed by the component pairings has `c_P ∩ μ = 0`. -/
private theorem capProductSupport_eq_zero_of_tauPair {M : TopCat.{0}} {ι : Type} [Fintype ι]
    (A : ι → Set M) [∀ P, CompactSpace (A P)] (hA : ∀ P, IsClosed (A P))
    (hAd : ∀ P, HasProperNeighbourhoodDeformations (A P))
    (hABd : ∀ P Q, HasProperNeighbourhoodDeformations (A P ∩ A Q))
    (hA'B : ∀ P Q, HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (A P) ⁻¹' A Q))
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) M ((2 * 3 : ℕ) : ℤ))
    (a : ∀ P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) 4)
    (η : ∀ Q, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M (A Q) 2)
    (hη : ∀ Q, capProductSupport ℚ M (hA Q) (hAd Q) 2 ((2 * 3 : ℕ) : ℤ) (η Q) μ =
      congrDegree ℚ _ (by norm_num) (a Q))
    (Vq : ι → Type) [∀ P, AddCommGroup (Vq P)] [∀ P, Module ℚ (Vq P)]
    (ιV : ∀ P, Vq P →ₗ[ℚ] cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) univ 1)
    (hPD : ∀ P (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) (4 - 1)),
      ∃ x, y = capProduct ℚ (TopCat.of (A P)) univ 1 4 (ιV P x) (a P))
    (m : ι → ℚ) (hm : ∀ P, 0 < m P) (Bq : (∀ P, Vq P) → (∀ P, Vq P) → ℚ)
    (hBq : ∀ x y, ∑ P, ∑ Q, tauPair (hA P) (hA Q) (hA'B P Q) (η Q) (a P)
      (ιV P (m P • x P)) (ιV Q (m Q • y Q)) = Bq x y)
    (hrad : ∀ x, (∀ y, Bq x y = 0) → x = 0)
    (c : ∀ P, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) M (A P) (((2 * 3 : ℕ) : ℤ) - 3))
    (hc : ∀ y : ∀ Q, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A Q)) 3,
      ∑ P, ∑ Q, compPairing (hA P) (hA'B Q P) (c P) (y Q) = 0) (P : ι) :
    capProductSupport ℚ M (hA P) (hAd P) _ ((2 * 3 : ℕ) : ℤ) (c P) μ = 0 := by
  classical
  have hu : ∀ P, ∃ u : Vq P, capProductSupport ℚ M (hA P) (hAd P) _ ((2 * 3 : ℕ) : ℤ) (c P) μ =
      congrDegree ℚ _ (by norm_num) (capProduct ℚ (TopCat.of (A P)) univ 1 4 (ιV P u) (a P)) :=
    fun P ↦ by
      obtain ⟨u, hu⟩ := hPD P (congrDegree ℚ _ (by norm_num)
        (capProductSupport ℚ M (hA P) (hAd P) _ ((2 * 3 : ℕ) : ℤ) (c P) μ))
      refine ⟨u, ?_⟩
      rw [← hu, congrDegree_congrDegree, congrDegree_self]
      rfl
  choose u hu using hu
  have hx := hrad (fun P ↦ (m P)⁻¹ • u P) fun y ↦ by
    rw [← hBq]
    have hmu : ∀ P, m P • ((m P)⁻¹ • u P) = u P := fun P ↦ by
      rw [smul_smul, mul_inv_cancel₀ (hm P).ne', one_smul]
    simp only [hmu]
    have h0 := hc fun Q ↦ congrDegree ℚ _ (by norm_num)
      (capProduct ℚ (TopCat.of (A Q)) univ 1 4 (ιV Q (m Q • y Q)) (a Q))
    have hT : ∀ P Q, compPairing (hA P) (hA'B Q P) (c P) (congrDegree ℚ _ (by norm_num)
        (capProduct ℚ (TopCat.of (A Q)) univ 1 4 (ιV Q (m Q • y Q)) (a Q))) =
        - tauPair (hA P) (hA Q) (hA'B P Q) (η Q) (a P) (ιV P (u P)) (ιV Q (m Q • y Q)) :=
      fun P Q ↦ compPairing_capProduct_eq (hA P) (hA Q) (hAd P) (hAd Q) (hABd P Q) (hABd Q P)
        (hA'B P Q) (hA'B Q P) μ (a P) (a Q) (η Q) (hη Q) (c P) (ιV P (u P)) (hu P) _
    simp only [hT, Finset.sum_neg_distrib, neg_eq_zero] at h0
    exact h0
  have hu0 : u P = 0 := by
    have := congrFun hx P
    simp only [Pi.zero_apply] at this
    rw [smul_eq_zero] at this
    exact this.resolve_left (inv_ne_zero (hm P).ne')
  rw [hu P, hu0]
  simp

end Assembly

/-! ### The Gysin classes of the double curves -/

section DoubleCurveGysin

open borelMooreHomology Set UnderlyingSpace

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- Transporting the support of a class along an equality transports its pulled-back cap
product along the corresponding equality of preimages. -/
private lemma capProductSupportPullback_congrIndex {Y' Y : TopCat.{0}} (f : Y' ⟶ Y)
    {S S' : Set Y} (hS : IsClosed S) (hS' : IsClosed S')
    (hd : HasProperNeighbourhoodDeformations (f ⁻¹' S))
    (hd' : HasProperNeighbourhoodDeformations (f ⁻¹' S')) (h : S = S') (j k : ℤ)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y S j)
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y' k) :
    capProductSupportPullback ℚ f hS' hd' j k
        (cohomologyWithSupports.congrIndex ℚ Y (congrArg compl h) rfl c) a =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (preimage_mono h.le))
        (isProperMap_subsetInclusionOfSubset (hS.preimage f.hom.continuous) _) (k - j)).hom
        (capProductSupportPullback ℚ f hS hd j k c a) := by
  subst h
  change _ = (pushforward ℚ (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (f ⁻¹' S))) _ (k - j)).hom _
  rw [pushforward_id]
  rfl

/-- The map from the zero locus of the restriction of a section to `I` into the points over
`I ∩ J`, `J` the zero scheme. -/
private noncomputable def zeroLocusInterHom (I : X.IdealSheafData) {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ MMP.Modules.totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) (J : X.IdealSheafData)
    (hσ : MMP.Modules.zeroLocus E σ = J) :
    TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (MMP.Modules.pullbackSectionMap I.subschemeι hσp))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection ((Scheme.Modules.pullback I.subschemeι).obj E)))) ⟶
    TopCat.of (pointsOver (K := ℂ) (I.support : Set X) ∩ pointsOver (K := ℂ) (J.support : Set X) :
      Set (UnderlyingSpace ℂ X)) :=
  TopCat.ofHom ⟨fun p ↦ ⟨UnderlyingSpace.map (K := ℂ) I.subschemeι p.1, by
      rw [mem_pointsOver, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩, by
      have h1 : p.1 ∈ (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) I.subschemeι)).hom ⁻¹'
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹'
            range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) := by
        rw [← preimage_zeroLocus_pullbackSectionMap I.subschemeι hσp]
        exact p.2
      have h2 : UnderlyingSpace.map (K := ℂ) I.subschemeι p.1 ∈
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E)) := h1
      rw [preimage_range_zeroSection_eq, hσ] at h2
      exact h2⟩,
    ((UnderlyingSpace.map (K := ℂ) I.subschemeι).continuous.comp
      continuous_subtype_val).subtype_mk _⟩

private lemma isProperMap_zeroLocusInterHom (I : X.IdealSheafData) {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ MMP.Modules.totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) (J : X.IdealSheafData)
    (hσ : MMP.Modules.zeroLocus E σ = J) :
    IsProperMap (zeroLocusInterHom I hσp J hσ) := by
  refine isProperMap_of_comp_of_t2 (zeroLocusInterHom I hσp J hσ).hom.continuous
    continuous_subtype_val ?_
  exact (UnderlyingSpace.isProperMap_map (K := ℂ) I.subschemeι).comp
    (isClosed_preimage_range_zeroSection'
      (MMP.Modules.pullbackSectionMap I.subschemeι hσp)).isProperMap_subtypeVal

/-- **The Gysin class of a localized class**: for a section `σ` of a line bundle with zero scheme
`J` and the fundamental class `μ` of a closed subscheme `I`, `j_I^* (σ^* u) ∩ [I]` is the
localized top Chern class of the restriction of `σ` to `I`, read in `H(I(ℂ) ∩ J(ℂ))`. -/
private theorem gysinClass_localizedClass_eq (I : X.IdealSheafData) {E : X.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ MMP.Modules.totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) (J : X.IdealSheafData)
    (hσ : MMP.Modules.zeroLocus E σ = J)
    (hd : HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ X))
        (pointsOver (K := ℂ) (I.support : Set X)) ⁻¹' pointsOver (K := ℂ) (J.support : Set X)))
    (μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ I.subscheme)) 4) :
    gysinClass (M := TopCat.of (UnderlyingSpace ℂ X)) (isClosed_pointsOver I.support.isClosed) (isClosed_pointsOver J.support.isClosed)
        hd 2 4 (localizedClass σ J hσ)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph I : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ I.subscheme, pointsOver (K := ℂ) (I.support : Set X))))
          (subschemePointsHomeomorph I).isProperMap 4).hom μE) =
      congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (zeroLocusInterHom I hσp J hσ)
          (isProperMap_zeroLocusInterHom I hσp J hσ) (4 - (2 * 1 : ℕ))).hom
          (MMP.Modules.localizedTopChernCap (MMP.Modules.pullbackSectionMap I.subschemeι hσp) ℚ 1 4 μE)) := by
  subst hσ
  set A : Set (TopCat.of (UnderlyingSpace ℂ X)) := pointsOver (K := ℂ) (I.support : Set X)
  set B : Set (TopCat.of (UnderlyingSpace ℂ X)) :=
    pointsOver (K := ℂ) ((MMP.Modules.zeroLocus E σ).support : Set X)
  have hA : IsClosed A := isClosed_pointsOver I.support.isClosed
  have hB : IsClosed B := isClosed_pointsOver (MMP.Modules.zeroLocus E σ).support.isClosed
  set F : TopCat.of (UnderlyingSpace ℂ I.subscheme) ⟶ TopCat.of (UnderlyingSpace ℂ X) :=
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) I.subschemeι)
  have hF : TopCat.ofHom ((subschemePointsHomeomorph I : _ ≃ₜ _) :
      C(UnderlyingSpace ℂ I.subscheme, pointsOver (K := ℂ) (I.support : Set X))) ≫
      borelMooreHomology.subsetInclusion A = F := by
    ext; rfl
  -- the zero locus of `(MMP.Modules.pullbackSectionMap I.subschemeι hσp)` is `F⁻¹ B`
  have hZτ : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (MMP.Modules.pullbackSectionMap I.subschemeι hσp))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection ((Scheme.Modules.pullback I.subschemeι).obj E))) = F ⁻¹' B := by
    rw [preimage_zeroLocus_pullbackSectionMap I.subschemeι hσp]
    change F ⁻¹' ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) = _
    rw [preimage_range_zeroSection_eq]
  have hd' : HasProperNeighbourhoodDeformations (F ⁻¹' B) :=
    hZτ ▸ MMP.Modules.hasProperNeighbourhoodDeformations_preimage (MMP.Modules.pullbackSectionMap I.subschemeι hσp)
  let ρ₁ : TopCat.of (F ⁻¹' B) ⟶
      TopCat.of (borelMooreHomology.subsetInclusion A ⁻¹' B) :=
    TopCat.ofHom ⟨fun x ↦ ⟨subschemePointsHomeomorph I x.1, x.2⟩,
      ((subschemePointsHomeomorph I).continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hρ₁p : IsProperMap ρ₁ := by
    refine isProperMap_of_comp_of_t2 ρ₁.hom.continuous continuous_subtype_val ?_
    exact (subschemePointsHomeomorph I).isProperMap.comp
      (hB.preimage F.hom.continuous).isProperMap_subtypeVal
  have key1 := pushforward_capProductSupportPullback_of_comp_eq ℚ
    (TopCat.ofHom ((subschemePointsHomeomorph I : _ ≃ₜ _) :
      C(UnderlyingSpace ℂ I.subscheme, pointsOver (K := ℂ) (I.support : Set X))))
    (subschemePointsHomeomorph I).isProperMap (borelMooreHomology.subsetInclusion A) F hF hB hd hd'
    ρ₁ (fun _ ↦ rfl) hρ₁p 2 4 (localizedClass σ (MMP.Modules.zeroLocus E σ) rfl) μE
  unfold gysinClass
  rw [← key1, ← pushforward_comp_apply']
  have hS0 : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) :=
    isClosed_preimage_range_zeroSection' σ
  have hd'' : HasProperNeighbourhoodDeformations
      (F ⁻¹' ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)).hom ⁻¹' range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E)))) := by
    rw [preimage_range_zeroSection_eq]; exact hd'
  unfold localizedClass
  have e1 := capProductSupportPullback_congrIndex F hS0 hB hd'' hd'
    (preimage_range_zeroSection_eq σ) 2 4
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
      (range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom (MMP.Modules.thomClass ℚ E 1)) μE
  refine (congrArg (fun z ↦ (pushforward ℚ (ModuleCat.of ℚ ℚ)
    (ρ₁ ≫ preimageInterHom A B) ((isProperMap_preimageInterHom hA hB).comp hρ₁p) (4 - 2)).hom z)
    e1).trans ?_
  have hZle := (preimage_zeroLocus_pullbackSectionMap I.subschemeι hσp).le
  have hτc : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (MMP.Modules.pullbackSectionMap I.subschemeι hσp))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection ((Scheme.Modules.pullback I.subschemeι).obj E)))) :=
    isClosed_preimage_range_zeroSection' (MMP.Modules.pullbackSectionMap I.subschemeι hσp)
  have h42 : (4 : ℤ) - ((2 * 1 : ℕ) : ℤ) = 4 - 2 := by norm_num
  have e2 : capProductSupportPullback ℚ F hS0 hd'' 2 4
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
        (range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection E))) ((2 * 1 : ℕ) : ℤ)).hom
          (MMP.Modules.thomClass ℚ E 1)) μE =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset hZle)
        (isProperMap_subsetInclusionOfSubset hτc hZle) (4 - 2)).hom
        (congrDegree ℚ _ h42 (MMP.Modules.localizedTopChernCap (MMP.Modules.pullbackSectionMap I.subschemeι hσp) ℚ 1 4 μE)) := by
    rw [pushforward_congrDegree]
    have f1 := MMP.Modules.forget_pullback_thomClass_of_comp ℚ σ
      (MMP.Modules.pullbackSectionMap I.subschemeι hσp) (MMP.Modules.baseChangeMap_proj _ E)
      (MMP.Modules.isFibrewiseIso_baseChangeMap _ E 1)
      (MMP.Modules.pullbackSectionMap_baseChangeMap _ hσp)
    have f2 := pushforward_subsetInclusionOfSubset_capProductSupport ℚ
      (TopCat.of (UnderlyingSpace ℂ I.subscheme)) hτc (hS0.preimage F.hom.continuous)
      (MMP.Modules.hasProperNeighbourhoodDeformations_preimage (MMP.Modules.pullbackSectionMap I.subschemeι hσp)) hd'' hZle
      ((2 * 1 : ℕ) : ℤ) 4
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (MMP.Modules.pullbackSectionMap I.subschemeι hσp)))
        (range (UnderlyingSpace.map (K := ℂ) (MMP.Modules.zeroSection ((Scheme.Modules.pullback I.subschemeι).obj E))))
        ((2 * 1 : ℕ) : ℤ)).hom (MMP.Modules.thomClass ℚ ((Scheme.Modules.pullback I.subschemeι).obj E) 1)) μE
    have f3 := f2.trans (congrArg (fun c ↦ (capProductSupport ℚ
      (TopCat.of (UnderlyingSpace ℂ I.subscheme)) (hS0.preimage F.hom.continuous) hd''
      ((2 * 1 : ℕ) : ℤ) 4) c μE) f1)
    exact f3.symm
  rw [← pushforward_comp_apply', e2]
  refine (pushforward_comp_apply' ℚ (subsetInclusionOfSubset hZle) _
    (isProperMap_subsetInclusionOfSubset hτc hZle) _ (4 - 2) _).symm.trans ?_
  rw [pushforward_congrDegree_apply]
  congr 1

/-- **The intersection of two components is reduced** on either of them: in snc coordinates its
ideal is generated by one regular parameter. -/
private lemma isReduced_comap_component {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (P Q : D.support) (hQP : Q ≠ P) :
    IsReduced (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).subscheme := by
  haveI : IsLocallyNoetherian P.1.idealSheaf.subscheme := inferInstance
  refine MMP.Resolution.isReduced_subscheme_of_stalk_eq_span_parameter _ fun y hy ↦ ?_
  obtain ⟨m, w, c, hw, hc, -⟩ := MMP.Fourfold.exists_component_coordinates hsnc P y
  exact ⟨m, w, c ⟨⟨Q, hQP⟩, hy⟩, hw, hc ⟨⟨Q, hQP⟩, hy⟩⟩

/-- **The double curves are components of the intersection**: on the component `E_P`, a point of
`E_P ∩ E_Q` specializing to the generic point of the curve over a double curve is that generic
point. -/
private lemma eq_genericPoint_curveDiv_of_specializes {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P Q : D.support)
    (hQP : Q ≠ P) {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η)
    (hP : P ∈ MMP.Fourfold.comps D η) {y : P.1.idealSheaf.subscheme}
    (hy : y ∈ (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support)
    (hyx : y ⤳ (MMP.Fourfold.curveDiv hsnc hdim P hη hP).genericPoint) :
    y = (MMP.Fourfold.curveDiv hsnc hdim P hη hP).genericPoint := by
  set C := MMP.Fourfold.curveDiv hsnc hdim P hη hP
  haveI := P.1.integral
  by_contra hne
  have h2 := MMP.Fourfold.krullDim_eq_two_of_mem_comps hsnc hdim P hη hP
  have hx1 := MMP.Fourfold.height_genericPoint_primeDivisor h2 C
  have hlt : C.genericPoint < y := lt_of_le_not_ge ((Scheme.le_iff_specializes).2 hyx)
    fun h' ↦ hne (hyx.antisymm ((Scheme.le_iff_specializes).1 h')).eq
  have hh := Order.height_strictMono hlt (by rw [hx1]; exact ENat.one_lt_top)
  rw [hx1] at hh
  have hform := MMP.height_add_coheight_eq_krullDim ℂ y
  rw [h2] at hform
  have hy2 : Order.height y + Order.coheight y = 2 := WithBot.coe_injective (hform.trans rfl)
  have hcy : Order.coheight y = 0 := by
    have h2le : 2 ≤ Order.height y := Order.add_one_le_of_lt hh
    by_contra hc
    have h1 : 1 ≤ Order.coheight y := ENat.one_le_iff_ne_zero.2 hc
    have h3 := add_le_add h2le h1
    rw [hy2] at h3
    exact absurd h3 (by decide)
  have hgen : y = genericPoint P.1.idealSheaf.subscheme := by
    have hle : y ≤ genericPoint P.1.idealSheaf.subscheme :=
      (Scheme.le_iff_specializes).2 ((genericPoint_spec _).specializes trivial)
    have hge := Order.coheight_eq_zero.1 hcy hle
    exact (((Scheme.le_iff_specializes).1 hge).antisymm ((Scheme.le_iff_specializes).1 hle)).eq
  rw [hgen, MMP.Resolution.mem_support_comap_iff] at hy
  exact hQP (Subtype.ext (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hy).symm)

open Classical in
/-- **Stacks 02QU for a reduced scheme**: if every irreducible component of a reduced complex
scheme `Z` has delta-dimension `k`, the cycle `[Z]_k` is the sum of the prime cycles of the
generic points of the components (each component has multiplicity one). -/
private theorem cycleAssociatedToClosedSubscheme_id_eq_sum {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [IsReduced Z] [Fintype (irreducibleComponents Z)]
    {k : ℕ} (hj : ∀ j : irreducibleComponents Z,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Z ↘ Spec (.of ℂ)) (MMP.Chow.componentGenericPoint j) = k) :
    Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation ℂ)
        (Z ↘ Spec (.of ℂ)) (𝟙 Z) k =
      ∑ j, Stacks.Chow.pointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k
        (MMP.Chow.componentGenericPoint j) (hj j) := by
  have hinj : ∀ j j' : irreducibleComponents Z,
      MMP.Chow.componentGenericPoint j = MMP.Chow.componentGenericPoint j' → j = j' :=
    fun j j' h ↦ Subtype.ext ((MMP.Chow.closure_componentGenericPoint j).symm.trans
      (h ▸ MMP.Chow.closure_componentGenericPoint j'))
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  simp only [AddSubmonoidClass.coe_finset_sum, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, Stacks.Chow.pointCycle_apply]
  by_cases hy : ∃ j, MMP.Chow.componentGenericPoint j = y
  · obtain ⟨j, rfl⟩ := hy
    have hξ := MMP.componentGenericPoint_mem_genericPoints j
    have e1 : (Stacks.Chow.cycleAssociatedToClosedSubscheme (Stacks.Chow.fieldChowSituation ℂ)
        (Z ↘ Spec (.of ℂ)) (𝟙 Z) k).1 (MMP.Chow.componentGenericPoint j) = 1 := by
      refine (Stacks.Chow.cycleAssociatedToClosedSubscheme_apply (Stacks.Chow.fieldChowSituation ℂ)
        (Z ↘ Spec (.of ℂ)) (𝟙 Z) k ⟨_, hξ⟩ (hj j)).trans ?_
      rw [Stacks.Chow.componentMultiplicity_eq_length_stalk,
        AlgebraicGeometry.length_stalk_eq_one_of_isMax
          (Stacks.Chow.isMax_of_mem_genericPoints ⟨_, hξ⟩)]
      rfl
    rw [e1, Finset.sum_eq_single j (fun j' _ hj' ↦ if_neg fun h ↦ hj' (hinj _ _ h).symm)
      (fun h ↦ absurd (Finset.mem_univ j) h), if_pos rfl]
  · rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero]
    · exact (Finset.sum_eq_zero fun j _ ↦ if_neg fun h ↦ hy ⟨j, h.symm⟩).symm
    · rintro ⟨ξ, hξy, -⟩
      refine hy ⟨⟨closure {ξ.1}, ξ.2⟩, ?_⟩
      have h1 : IsGenericPoint (MMP.Chow.componentGenericPoint ⟨closure {ξ.1}, ξ.2⟩)
          (closure {ξ.1}) := MMP.Chow.closure_componentGenericPoint _
      exact (h1.eq isGenericPoint_closure).trans hξy

/-- Two equal ideal sheaves carry the same push-forward of a fundamental class. -/
private lemma pushforward_fundamentalClass_congr {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {I J : Z.IdealSheafData} (h : I = J)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme]
    [T2Space (UnderlyingSpace ℂ I.subscheme)] [T2Space (UnderlyingSpace ℂ J.subscheme)]
    {k : ℕ} {hI : (k : WithBot ℕ∞) = topologicalKrullDim I.subscheme}
    {hJ : (k : WithBot ℕ∞) = topologicalKrullDim J.subscheme}
    {cI : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ I.subscheme))
      (2 * k : ℕ)}
    {cJ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ J.subscheme))
      (2 * k : ℕ)}
    (hcI : IsVarietyFundamentalClass ℚ hI cI) (hcJ : IsVarietyFundamentalClass ℚ hJ cJ) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) I.subschemeι))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * k : ℕ)).hom cI =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) J.subschemeι))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * k : ℕ)).hom cJ := by
  subst h
  rw [hcI.eq hcJ]

/-- The cycle class of the generic point of a component `Z'` is the push-forward of the
fundamental class of `Z'` with its reduced structure. -/
private lemma pointCycleClass_componentGenericPoint_eq {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] (j : irreducibleComponents Z) {k : ℕ}
    (hj : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) (MMP.Chow.componentGenericPoint j) = k)
    [IsIntegral (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent j).toScheme]
    {hk : (k : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent j).toScheme}
    {c : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent j).toScheme))
        (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass ℚ hk c) :
    MMP.Chow.pointCycleClass ℚ (MMP.Chow.componentGenericPoint j) hj =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent j).ι))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * k : ℕ)).hom c :=
  pushforward_fundamentalClass_congr (J := (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent j).ideal)
    (MMP.integralComponentAt_componentGenericPoint j)
    (existsUnique_isVarietyFundamentalClass ℚ
      (MMP.Chow.natCast_eq_dimension_integralComponentAt _ hj)).choose_spec.1 hc

open Classical in
/-- **Fulton's Lemma 19.1.3 for a reduced zero scheme**, as a sum over its one-dimensional
components: for a section `τ ≠ 0` of a line bundle on a normal surface, with reduced zero scheme
`Z`, `τ^* u ∩ [Y]` is the sum of the fundamental classes of the one-dimensional components of
`Z`. -/
private theorem localizedTopChernCap_eq_sum {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [IsComplexScheme Y] [IsIntegral Y] [IsNormal Y]
    (hn : ((1 + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y)) (2 * (1 + 1) : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hn μ) {L : Y.Modules} [L.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} L 1]
    (τ : Y ⟶ MMP.Modules.totalSpace L) [τ.IsOver (Spec (.of ℂ))]
    (hτp : τ ≫ MMP.Modules.proj L = 𝟙 Y) (hτ : τ ≠ MMP.Modules.zeroSection L)
    [IsReduced (MMP.Modules.zeroLocus L τ).subscheme]
    [Fintype (irreducibleComponents (MMP.Modules.zeroLocus L τ).subscheme)]
    (c : ∀ V : {V : MMP.Intersection.Scheme.Subvariety (MMP.Modules.zeroLocus L τ).subscheme // V.HasDim ((1 : ℕ) : ℤ)},
      borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ V.1.toScheme)) (2 * 1 : ℕ))
    (hc : ∀ V : {V : MMP.Intersection.Scheme.Subvariety (MMP.Modules.zeroLocus L τ).subscheme // V.HasDim ((1 : ℕ) : ℤ)},
      IsVarietyFundamentalClass ℚ ((MMP.Intersection.hasDim_natCast_iff _).mp V.2).symm (c V)) :
    MMP.Modules.localizedTopChernCap τ ℚ 1 (2 * (1 + 1) : ℕ) μ =
      congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (MMP.Modules.zeroLocusHom τ)
          (MMP.Modules.isProperMap_zeroLocusHom τ) (2 * 1 : ℕ)).hom
          (∑ Z : irreducibleComponents (MMP.Modules.zeroLocus L τ).subscheme,
            if h : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z).HasDim ((1 : ℕ) : ℤ) then
              (pushforward ℚ (ModuleCat.of ℚ ℚ)
                (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
                  (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z).ι))
                (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 1 : ℕ)).hom (c ⟨_, h⟩)
            else 0)) := by
  have hj := fun j ↦ MMP.Modules.relativeDimension_componentGenericPoint_zeroLocus hn hτp hτ j
  have key : (pushforward ℚ (ModuleCat.of ℚ ℚ) (MMP.Modules.zeroLocusHom τ)
      (MMP.Modules.isProperMap_zeroLocusHom τ) (2 * 1 : ℕ)).hom
        (MMP.Chow.cycleClass ℚ 1 (Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ)
          ((MMP.Modules.zeroLocus L τ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) ((1 : ℕ) : ℤ))) =
      congrDegree ℚ _ (by norm_num) (MMP.Modules.localizedTopChernCap τ ℚ 1 _ μ) :=
    MMP.Modules.LocalizedFirstChernFormula.of_isNormal ℚ hn hτp hτ μ hμ
  have hfund : MMP.Chow.cycleClass ℚ 1 (Stacks.Chow.cycleAssociatedToClosedSubscheme
      (Stacks.Chow.fieldChowSituation ℂ)
      ((MMP.Modules.zeroLocus L τ).subscheme ↘ Spec (.of ℂ)) (𝟙 _) ((1 : ℕ) : ℤ)) =
      ∑ Z : irreducibleComponents (MMP.Modules.zeroLocus L τ).subscheme,
        if h : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z).HasDim ((1 : ℕ) : ℤ) then
          (pushforward ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
              (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z).ι))
            (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 1 : ℕ)).hom (c ⟨_, h⟩)
        else 0 := by
    rw [cycleAssociatedToClosedSubscheme_id_eq_sum hj, map_sum]
    refine Finset.sum_congr rfl fun Z _ ↦ ?_
    have h : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z).HasDim ((1 : ℕ) : ℤ) := by
      obtain ⟨n, hn1, hd⟩ := MMP.Modules.hasDim_irreducibleComponent_zeroLocus ℂ hn hτp hτ Z
      refine ⟨n, hn1, (MMP.topologicalKrullDim_subscheme_eq_support _).trans ?_⟩
      rw [MMP.Intersection.Scheme.Subvariety.ideal_ofIrreducibleComponent,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hd
    rw [dif_pos h, MMP.Chow.cycleClass_pointCycle]
    exact pointCycleClass_componentGenericPoint_eq Z (hj Z) (hc ⟨_, h⟩)
  rw [hfund] at key
  rw [key, congrDegree_congrDegree, congrDegree_self]
  rfl

/-- **A one-dimensional component of `E_P ∩ E_Q` is the curve over a double curve** through `P`
and `Q`. -/
private lemma exists_curveDiv_of_component {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P Q : D.support)
    (hQP : Q ≠ P) (Z : P.1.idealSheaf.subscheme.IdealSheafData)
    (hZ : Z = Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι)
    (Z' : irreducibleComponents Z.subscheme)
    (hV : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ)) :
    ∃ (η : W) (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η),
      Q ∈ MMP.Fourfold.comps D η ∧
        Z.subschemeι (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').genericPoint =
          (MMP.Fourfold.curveDiv hsnc hdim P hη hP).genericPoint := by
  set y := Z.subschemeι (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').genericPoint
  haveI := MMP.Fourfold.locallyOfFiniteType_component P
  have hy1 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) y = ((1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ 1 ?_
    have h := MMP.Intersection.Scheme.Subvariety.dim_eq_height_genericPoint (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z')
    have h1 : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').dim = ((1 : ℕ) : WithBot ℕ∞) :=
      (MMP.Intersection.hasDim_natCast_iff 1).1 hV
    rw [h1, ← height_apply_of_isClosedEmbedding Z.subschemeι Z.subschemeι.isClosedEmbedding] at h
    rw [AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height]
    exact h.symm
  have hyZ : y ∈ (Z.support : Set _) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
  have hQ : P.1.idealSheaf.subschemeι y ∈ Q.1.support := by
    have hyZ' : y ∈ (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support := hZ ▸ hyZ
    rw [MMP.Resolution.mem_support_comap_iff] at hyZ'
    exact hyZ'
  obtain ⟨hη, hP, hVeq⟩ := MMP.Fourfold.exists_eq_genericPoint_curveDiv hsnc hdim P y hy1 hQP hQ
  exact ⟨_, hη, hP, MMP.Fourfold.mem_comps.2 hQ, hVeq⟩

/-- **The curve over a double curve through `P` and `Q` is a one-dimensional component of
`E_P ∩ E_Q`.** -/
private lemma exists_component_of_curveDiv {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P Q : D.support)
    (hQP : Q ≠ P) (Z : P.1.idealSheaf.subscheme.IdealSheafData)
    (hZ : Z = Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    (hQ : Q ∈ MMP.Fourfold.comps D η) :
    ∃ Z' : irreducibleComponents Z.subscheme,
      (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ) ∧
        Z.subschemeι (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').genericPoint =
          (MMP.Fourfold.curveDiv hsnc hdim P hη hP).genericPoint := by
  haveI := P.1.integral
  set C := MMP.Fourfold.curveDiv hsnc hdim P hη hP
  have hy : C.genericPoint ∈ (Z.support : Set _) := by
    rw [hZ]; exact MMP.Fourfold.genericPoint_curveDiv_mem_comap hsnc hdim P hη hP hQ
  rw [← Scheme.IdealSheafData.range_subschemeι] at hy
  obtain ⟨ζ, hζ⟩ := hy
  refine ⟨⟨irreducibleComponent ζ, irreducibleComponent_mem_irreducibleComponents ζ⟩, ?_⟩
  set V := MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent
    ⟨irreducibleComponent ζ, irreducibleComponent_mem_irreducibleComponents ζ⟩
  have hspec : V.genericPoint ⤳ ζ := by
    rw [specializes_iff_mem_closure, MMP.Intersection.Scheme.Subvariety.closure_genericPoint_ofIrreducibleComponent]
    exact mem_irreducibleComponent
  have hmem' : Z.subschemeι V.genericPoint ∈ (Z.support : Set _) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨_, rfl⟩
  have hmem : Z.subschemeι V.genericPoint ∈
      (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support := hZ ▸ hmem'
  have heq : Z.subschemeι V.genericPoint = C.genericPoint :=
    eq_genericPoint_curveDiv_of_specializes hsnc hdim P Q hQP hη hP hmem
      (hζ ▸ hspec.map Z.subschemeι.continuous)
  refine ⟨?_, heq⟩
  rw [MMP.Intersection.Scheme.Subvariety.HasDim]
  refine (MMP.Intersection.hasDim_natCast_iff (T := V.toScheme) 1).2 ?_
  have h := MMP.Intersection.Scheme.Subvariety.dim_eq_height_genericPoint V
  rw [← height_apply_of_isClosedEmbedding Z.subschemeι Z.subschemeι.isClosedEmbedding, heq,
    MMP.Fourfold.height_genericPoint_primeDivisor
      (MMP.Fourfold.krullDim_eq_two_of_mem_comps hsnc hdim P hη hP) C] at h
  exact h

/-- Two reduced closed subschemes with the same points are isomorphic over the ambient scheme. -/
private lemma exists_isIso_comp_eq_of_range_eq {Y Z₁ Z₂ : Scheme.{0}} [IsReduced Z₁]
    [IsReduced Z₂] (i₁ : Z₁ ⟶ Y) (i₂ : Z₂ ⟶ Y) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h : Set.range i₁ = Set.range i₂) : ∃ φ : Z₂ ⟶ Z₁, IsIso φ ∧ φ ≫ i₁ = i₂ := by
  have hk : i₁.ker = i₂.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    simp only [h]
  exact ⟨_, IsClosedImmersion.isIso_lift i₁ i₂ hk, IsClosedImmersion.lift_fac _ _ _⟩

/-- The points of a closed subscheme `C` of `I` lying over `J`, mapped into `I(ℂ) ∩ J(ℂ)`. -/
private noncomputable def subschemeInterHom (I J : X.IdealSheafData)
    (C : I.subscheme.IdealSheafData)
    (hC : ∀ x : C.subscheme, I.subschemeι (C.subschemeι x) ∈ J.support) :
    TopCat.of (UnderlyingSpace ℂ C.subscheme) ⟶
      TopCat.of (pointsOver (K := ℂ) (I.support : Set X) ∩ pointsOver (K := ℂ) (J.support : Set X) :
        Set (UnderlyingSpace ℂ X)) :=
  TopCat.ofHom ⟨fun p ↦ ⟨UnderlyingSpace.map (K := ℂ) I.subschemeι
      (UnderlyingSpace.map (K := ℂ) C.subschemeι p), by
      rw [mem_pointsOver, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩, hC _⟩,
    ((UnderlyingSpace.map (K := ℂ) I.subschemeι).continuous.comp
      (UnderlyingSpace.map (K := ℂ) C.subschemeι).continuous).subtype_mk _⟩

private lemma isProperMap_subschemeInterHom (I J : X.IdealSheafData)
    (C : I.subscheme.IdealSheafData)
    (hC : ∀ x : C.subscheme, I.subschemeι (C.subschemeι x) ∈ J.support) :
    IsProperMap (subschemeInterHom I J C hC) :=
  isProperMap_of_comp_of_t2 (subschemeInterHom I J C hC).hom.continuous continuous_subtype_val
    ((UnderlyingSpace.isProperMap_map (K := ℂ) I.subschemeι).comp
      (UnderlyingSpace.isProperMap_map (K := ℂ) C.subschemeι))

/-- **Transport of a fundamental class along an isomorphism of curves.** If a closed subscheme
`C` of `I` is isomorphic over `I` to a subvariety `V` of the zero scheme of `σ|_I`, the
fundamental class of `V` and that of `C` have the same image in `H(I(ℂ) ∩ J(ℂ))`. -/
private lemma pushforward_fundamentalClass_eq_of_isIso (I : X.IdealSheafData)
    {E : X.Modules} [E.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : X ⟶ MMP.Modules.totalSpace E} [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 X) (J : X.IdealSheafData)
    (hσ : MMP.Modules.zeroLocus E σ = J)
    (V : MMP.Intersection.Scheme.Subvariety (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap I.subschemeι hσp)).subscheme)
    [IsIntegral V.toScheme]
    (hV : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V.toScheme)
    {cV : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ V.toScheme))
      (2 * 1 : ℕ)} (hcV : IsVarietyFundamentalClass ℚ hV cV)
    (C : I.subscheme.IdealSheafData) [IsIntegral C.subscheme]
    (hC : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim C.subscheme)
    {μC : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ C.subscheme))
      (2 * 1 : ℕ)} (hμC : IsVarietyFundamentalClass ℚ hC μC)
    (hmem : ∀ x : C.subscheme, I.subschemeι (C.subschemeι x) ∈ J.support)
    (φ : C.subscheme ⟶ V.toScheme) [IsIso φ]
    (hφ : φ ≫ V.ι ≫ (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap I.subschemeι hσp)).subschemeι = C.subschemeι) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (zeroLocusInterHom I hσp J hσ)
        (isProperMap_zeroLocusInterHom I hσp J hσ) (2 * 1 : ℕ)).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ)
        (MMP.Modules.zeroLocusHom (MMP.Modules.pullbackSectionMap I.subschemeι hσp))
        (MMP.Modules.isProperMap_zeroLocusHom _) (2 * 1 : ℕ)).hom
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) V.ι))
          (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 1 : ℕ)).hom cV)) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (subschemeInterHom I J C hmem)
        (isProperMap_subschemeInterHom I J C hmem) (2 * 1 : ℕ)).hom μC := by
  haveI : φ.IsOver (Spec (.of ℂ)) := ⟨by
    rw [← CategoryTheory.comp_over (f := V.ι) (S := Spec (.of ℂ)),
      ← CategoryTheory.comp_over (f := (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap I.subschemeι hσp)).subschemeι)
        (S := Spec (.of ℂ)), reassoc_of% hφ, CategoryTheory.comp_over]⟩
  have hcV' := hcV.eq (IsVarietyFundamentalClass.pushforward_of_isIso φ hV hμC)
  rw [hcV', ← pushforward_comp_apply', ← pushforward_comp_apply', ← pushforward_comp_apply']
  refine pushforward_apply_congr ℚ ?_ _ _ _ _
  ext p
  change ((((p.toHom ≫ φ) ≫ V.ι) ≫ (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap I.subschemeι hσp)).subschemeι) ≫
    I.subschemeι) = (p.toHom ≫ C.subschemeι) ≫ I.subschemeι
  simp only [Category.assoc, reassoc_of% hφ]

/-- The curve over a double curve through `P` lies on every component `E_Q` through it. -/
private lemma subschemeι_curveDiv_mem {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P : D.support)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    {Q : D.support} (hQ : Q ∈ MMP.Fourfold.comps D η)
    (x : (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme) :
    P.1.idealSheaf.subschemeι ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι x) ∈
      Q.1.idealSheaf.support := by
  have hy : (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι x ∈
      ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).support : Set _) := by
    have h : _ ∈ Set.range (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι :=
      ⟨x, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at h
    exact h
  exact ((MMP.Fourfold.mem_support_curveDiv_iff hsnc hdim P hη hP _).1 hy).mem_closed
    Q.1.idealSheaf.support.isClosed (MMP.Fourfold.mem_comps.1 hQ)

/-- The double curves through two given components. -/
private abbrev DoubleCurveThrough {W : Scheme.{0}} (D : Divisor W) (P Q : D.support) : Type :=
  {k : {η : W // MMP.Fourfold.IsDoubleCurve D η} //
    P ∈ MMP.Fourfold.comps D k.1 ∧ Q ∈ MMP.Fourfold.comps D k.1}

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The Gysin class of `E_Q` on `[E_P]` is the sum of the curves over the double curves through
`P` and `Q`**: `j_P^* η_Q ∩ [E_P] = ∑_C [C]` in `H(E_P(ℂ) ∩ E_Q(ℂ))`. -/
private theorem gysinClass_localizedClass_eq_sum_curveDiv {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hQP : Q ≠ P)
    [IsIntegral P.1.idealSheaf.subscheme] [IsNormal P.1.idealSheaf.subscheme]
    [CompactSpace P.1.idealSheaf.subscheme]
    (hn : ((1 + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) (2 * (1 + 1) : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E : W.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = Q.1.idealSheaf)
    (hd : HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ W))
        (pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W)) ⁻¹'
          pointsOver (K := ℂ) (Q.1.idealSheaf.support : Set W)))
    [∀ k : DoubleCurveThrough D P Q, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme]
    (hk : ∀ k : DoubleCurveThrough D P Q, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D P Q, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme))
      (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k)) :
    gysinClass (M := TopCat.of (UnderlyingSpace ℂ W))
        (isClosed_pointsOver P.1.idealSheaf.support.isClosed)
        (isClosed_pointsOver Q.1.idealSheaf.support.isClosed) hd 2 4
        (localizedClass σ Q.1.idealSheaf hσ)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph P.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ P.1.idealSheaf.subscheme,
              pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph P.1.idealSheaf).isProperMap 4).hom μE) =
      ∑ k : DoubleCurveThrough D P Q, congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (subschemeInterHom P.1.idealSheaf Q.1.idealSheaf
          (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf
            (subschemeι_curveDiv_mem hsnc hdim P k.1.2 k.2.1 k.2.2))
          (isProperMap_subschemeInterHom _ _ _ _) (2 * 1 : ℕ)).hom (μC k)) := by
  classical
  have hZ : (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)) = Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι := by
    rw [MMP.Modules.zeroLocus_pullbackSectionMap, hσ]
  haveI : IsReduced (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme := by
    rw [hZ]; exact isReduced_comap_component hsnc P Q hQP
  haveI : IsLocallyNoetherian P.1.idealSheaf.subscheme := inferInstance
  haveI : CompactSpace (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme :=
    (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι.isClosedEmbedding.compactSpace
  haveI : IsNoetherian (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme := {}
  haveI : Fintype (irreducibleComponents (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).fintype
  have hτ : MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp ≠
      MMP.Modules.zeroSection ((Scheme.Modules.pullback P.1.idealSheaf.subschemeι).obj E) := fun h ↦ by
    haveI := P.1.integral
    have h0 : MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp) = ⊥ := by
      rw [h, MMP.Modules.zeroLocus_zeroSection]
    have hg : genericPoint P.1.idealSheaf.subscheme ∈ (Q.1.idealSheaf.comap P.1.idealSheaf.subschemeι).support := by
      rw [← hZ, h0, Scheme.IdealSheafData.support_bot]; trivial
    rw [MMP.Resolution.mem_support_comap_iff] at hg
    exact hQP (Subtype.ext (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hg).symm)
  choose c hc _ using fun V : {V : MMP.Intersection.Scheme.Subvariety (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme // V.HasDim ((1 : ℕ) : ℤ)} ↦
    existsUnique_isVarietyFundamentalClass (R := ℚ) ((MMP.Intersection.hasDim_natCast_iff _).mp V.2).symm
  have e1 := gysinClass_localizedClass_eq P.1.idealSheaf hσp Q.1.idealSheaf hσ hd μE
  have e2 := localizedTopChernCap_eq_sum hn hμE (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)
    (MMP.Modules.pullbackSectionMap_proj _ hσp) hτ c hc
  rw [e1]
  erw [e2]
  rw [pushforward_congrDegree_apply, congrDegree_congrDegree_apply]
  simp only [map_sum]
  -- the double curve of a one-dimensional component
  choose ηf hηf hPf hQf hgen using fun (Z' : irreducibleComponents (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme)
      (hV : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ)) ↦
    exists_curveDiv_of_component hsnc hdim P Q hQP (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)) hZ Z' hV
  let i' : ∀ Z' : irreducibleComponents (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme,
      (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ) →
        DoubleCurveThrough D P Q :=
    fun Z' hV ↦ ⟨⟨ηf Z' hV, hηf Z' hV⟩, hPf Z' hV, hQf Z' hV⟩
  have himg : ∀ Z' hV, P.1.idealSheaf.subschemeι ((MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι
      (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').genericPoint) = ηf Z' hV := fun Z' hV ↦ by
    rw [hgen Z' hV, MMP.Fourfold.curveDiv_genericPoint]
  have hterm : ∀ (Z' : irreducibleComponents (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subscheme)
      (hV : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ)), (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (zeroLocusInterHom P.1.idealSheaf hσp Q.1.idealSheaf hσ)
        (isProperMap_zeroLocusInterHom P.1.idealSheaf hσp Q.1.idealSheaf hσ) (2 * 1 : ℕ)).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (MMP.Modules.zeroLocusHom (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp))
        (MMP.Modules.isProperMap_zeroLocusHom (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)) (2 * 1 : ℕ)).hom
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').ι))
          (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 1 : ℕ)).hom
          (c ⟨MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z', hV⟩))) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) (subschemeInterHom P.1.idealSheaf Q.1.idealSheaf
          (MMP.Fourfold.curveDiv hsnc hdim P (hηf Z' hV) (hPf Z' hV)).idealSheaf
            (subschemeι_curveDiv_mem hsnc hdim P (hηf Z' hV) (hPf Z' hV) (hQf Z' hV)))
          (isProperMap_subschemeInterHom P.1.idealSheaf Q.1.idealSheaf
            (MMP.Fourfold.curveDiv hsnc hdim P (hηf Z' hV) (hPf Z' hV)).idealSheaf
            (subschemeι_curveDiv_mem hsnc hdim P (hηf Z' hV) (hPf Z' hV) (hQf Z' hV)))
          (2 * 1 : ℕ)).hom (μC ⟨⟨ηf Z' hV, hηf Z' hV⟩, hPf Z' hV, hQf Z' hV⟩) := by
    intro Z' hV
    haveI := (MMP.Fourfold.curveDiv hsnc hdim P (hηf Z' hV) (hPf Z' hV)).integral
    have hrange : Set.range ((MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').ι ≫
        (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι) = Set.range
          (MMP.Fourfold.curveDiv hsnc hdim P (hηf Z' hV) (hPf Z' hV)).idealSheaf.subschemeι := by
      have h1 : Set.range ((MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').ι ≫
          (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι) = (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι ''
            Set.range (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').ι := by
        rw [← Set.range_comp]; rfl
      rw [h1, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι]
      change (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι ''
        ((MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').support : Set _) = _
      rw [← MMP.Intersection.Scheme.Subvariety.closure_genericPoint,
        ← (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι.isClosedEmbedding.closure_image_eq,
        Set.image_singleton, hgen Z' hV]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure _).symm
    obtain ⟨φ, hφi, hφ⟩ := exists_isIso_comp_eq_of_range_eq _ _ hrange
    haveI := hφi
    exact pushforward_fundamentalClass_eq_of_isIso P.1.idealSheaf hσp Q.1.idealSheaf hσ
      (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z') _ (hc ⟨_, hV⟩) _ (hk ⟨⟨ηf Z' hV, hηf Z' hV⟩, hPf Z' hV, hQf Z' hV⟩)
      (hμC ⟨⟨ηf Z' hV, hηf Z' hV⟩, hPf Z' hV, hQf Z' hV⟩) _ φ hφ
  refine Finset.sum_bij_ne_zero (fun Z' _ h ↦ i' Z' ?_) (fun _ _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · by_contra hn
    exact h (by rw [dif_neg hn, map_zero, map_zero, map_zero])
  · intro Z1 _ h1 Z2 _ h2 heq
    have hη : ηf Z1 _ = ηf Z2 _ := congrArg (fun k : DoubleCurveThrough D P Q ↦ k.1.1) heq
    have hgp := (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)).subschemeι.isClosedEmbedding.injective
      (P.1.idealSheaf.subschemeι.isClosedEmbedding.injective
        ((himg Z1 _).trans (hη.trans (himg Z2 _).symm)))
    apply Subtype.ext
    rw [← MMP.Intersection.Scheme.Subvariety.closure_genericPoint_ofIrreducibleComponent Z1,
      ← MMP.Intersection.Scheme.Subvariety.closure_genericPoint_ofIrreducibleComponent Z2, hgp]
  · intro k _ hk
    obtain ⟨Z', hV, hg⟩ :=
      exists_component_of_curveDiv hsnc hdim P Q hQP (MMP.Modules.zeroLocus _ (MMP.Modules.pullbackSectionMap P.1.idealSheaf.subschemeι hσp)) hZ k.1.2 k.2.1 k.2.2
    have hik : i' Z' hV = k := by
      apply Subtype.ext; apply Subtype.ext
      change ηf Z' hV = k.1.1
      rw [← himg Z' hV, hg, MMP.Fourfold.curveDiv_genericPoint]
    refine ⟨Z', Finset.mem_univ _, ?_, hik⟩
    have hik' : (⟨⟨ηf Z' hV, hηf Z' hV⟩, hPf Z' hV, hQf Z' hV⟩ : DoubleCurveThrough D P Q) = k :=
      hik
    subst hik'
    rw [dif_pos hV, hterm Z' hV]
    exact hk
  · intro Z' _ hne
    by_cases hV : (MMP.Intersection.Scheme.Subvariety.ofIrreducibleComponent Z').HasDim ((1 : ℕ) : ℤ)
    · simp only [dif_pos hV, i']
      exact congrArg (congrDegree ℚ _ _) (hterm Z' hV)
    · exfalso
      apply hne
      rw [dif_neg hV, map_zero, map_zero, map_zero]

end DoubleCurveGysin

/-! ### Positivity of the self-intersection of an ample line bundle on a surface -/

section SurfacePositivity

open scoped MMP.SubschemeOver

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The point of `Spec ℂ` has delta-dimension zero. -/
private lemma relativeDimension_spec_point (x : Spec (.of ℂ)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) x = ((0 : ℕ) : ℤ) := by
  refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ _ x 0 ?_
  have hcl : closure ({x} : Set (Spec (.of ℂ))) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)
  rw [hcl, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum ℂ) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- **The degree of a zero-cycle class is the degree of its cycle class** (Fulton, §19.1), on a
complex scheme proper over `ℂ`: push both to `Spec ℂ`, where the class of the point has degree
one. -/
private lemma degAt_chowCycleClass_eq_chowDegree {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [IsComplexScheme Y] [IsProper (Y ↘ Spec (.of ℂ))] [CompactSpace (UnderlyingSpace ℂ Y)]
    (a : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      ((0 : ℕ) : ℤ)) :
    degAt (TopCat.of (UnderlyingSpace ℂ Y)) (by norm_num) (MMP.Chow.chowCycleClass ℚ 0 a) =
      (Stacks.Chow.chowDegree (Stacks.Chow.fieldChowSituation ℂ)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_eq_zero ℂ) (Y ↘ Spec (.of ℂ))
        (IsLocalRing.closedPoint ℂ) a : ℚ) := by
  classical
  induction a using QuotientAddGroup.induction_on with
  | H α =>
  haveI : (Y ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  have hp := MMP.Chow.cycleClass_properPushforward ℚ (Y ↘ Spec (.of ℂ)) α
  set β := Stacks.Chow.properPushforward (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
    (Spec (.of ℂ) ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (comp_over _ _) ((0 : ℕ) : ℤ) α
  have hcongr : ∀ (s s' : Spec (.of ℂ) ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s]
      [LocallyOfFiniteType s'] (_ : s = s') (hf : (Y ↘ Spec (.of ℂ)) ≫ s = Y ↘ Spec (.of ℂ))
      (hf' : (Y ↘ Spec (.of ℂ)) ≫ s' = Y ↘ Spec (.of ℂ)),
      (Stacks.Chow.properPushforward (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) s
        (Y ↘ Spec (.of ℂ)) hf 0 α).1 =
      (Stacks.Chow.properPushforward (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) s'
        (Y ↘ Spec (.of ℂ)) hf' 0 α).1 := by
    intro s s' _ _ e _ _
    subst e
    rfl
  have hdeg : Stacks.Chow.chowDegree (Stacks.Chow.fieldChowSituation ℂ)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_eq_zero ℂ)
      (Y ↘ Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ) (QuotientAddGroup.mk α) =
      β.1 (IsLocalRing.closedPoint ℂ) := by
    have e1 := Stacks.Chow.chowDegree_mk (Stacks.Chow.fieldChowSituation ℂ)
      (Stacks.Chow.fieldChowSituation_dimensionFunction_eq_zero ℂ) (Y ↘ Spec (.of ℂ))
      (IsLocalRing.closedPoint ℂ) α
    refine e1.trans ?_
    exact congrFun (congrArg DFunLike.coe
      (hcongr _ _ (MMP.specOverSpec_over_self ℂ).symm (Category.comp_id _) (comp_over _ _))) _
  refine Eq.trans ?_ (congrArg (fun z : ℤ ↦ (z : ℚ)) hdeg).symm
  rw [MMP.Chow.chowCycleClass_mk,
    ← degAt_pushforward (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (Y ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _)]
  erw [← hp]
  suffices h : ∀ q : Spec (.of ℂ), degAt (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))
      (by norm_num) (MMP.Chow.cycleClass ℚ 0 β) = ((β.1 q : ℤ) : ℚ) from h _
  intro q
  have hβ : MMP.Chow.cycleToFinsupp β = Finsupp.single q (β.1 q) := by
    refine Finsupp.ext fun y ↦ ?_
    obtain rfl : y = q := Subsingleton.elim _ _
    rw [MMP.Chow.cycleToFinsupp_apply, Finsupp.single_eq_same]
  have hcl : MMP.Chow.cycleClass ℚ 0 β = β.1 q • MMP.Chow.pointCycleClassOrZero ℚ 0 q := by
    change Finsupp.linearCombination ℤ (MMP.Chow.pointCycleClassOrZero ℚ 0)
      (MMP.Chow.cycleToFinsupp β) = _
    rw [hβ, Finsupp.linearCombination_single]
  rw [hcl, MMP.Chow.pointCycleClassOrZero, dif_pos (relativeDimension_spec_point q), map_zsmul]
  have h1 : degAt (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) (by norm_num)
      (MMP.Chow.pointCycleClass ℚ q (relativeDimension_spec_point q)) = 1 :=
    deg_pointCycleClass_spec q (relativeDimension_spec_point q)
  rw [h1, zsmul_eq_mul, mul_one]

/-- The iterated cap product `a ↦ c₁ᵗᵒᵖ(A) ∩ ⋯ ∩ c₁ᵗᵒᵖ(A) ∩ a : H_{2d} → H_0`. -/
private noncomputable def iterTopCap {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (d : ℕ) :
    MMP.Chow.BMHomology ℚ X (2 * d) →ₗ[ℚ] MMP.Chow.BMHomology ℚ X (2 * 0) :=
  Nat.rec (motive := fun d ↦ MMP.Chow.BMHomology ℚ X (2 * d) →ₗ[ℚ] MMP.Chow.BMHomology ℚ X (2 * 0))
    LinearMap.id (fun d f ↦ f ∘ₗ MMP.Chow.firstChernClassTopCap ℚ A d) d

/-- **The degree of `c₁(A)^d ∩ a` is the degree of `c₁ᵗᵒᵖ(A)^d ∩ cl(a)`** (Fulton 19.2), on a
complex scheme proper over `ℂ` with an ample invertible module `A`. -/
private theorem capDegree_eq_degAt_iterTopCap {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))] [CompactSpace (UnderlyingSpace ℂ X)]
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A) :
    ∀ (d : ℕ) (a : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      d),
      haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A :=
        ‹Stacks.Ample.IsInvertibleModule X A›
      ((AlgebraicGeometry.capDegree ℂ (X ↘ Spec (.of ℂ)) (fun _ : Fin d ↦ A) a : ℤ) : ℚ) =
        degAt (TopCat.of (UnderlyingSpace ℂ X)) (by norm_num)
          (iterTopCap A d (MMP.Chow.chowCycleClass ℚ d a)) := by
  intro d
  induction d with
  | zero =>
    intro a
    rw [AlgebraicGeometry.capDegree_zero]
    exact (degAt_chowCycleClass_eq_chowDegree a).symm
  | succ d ih =>
    intro a
    have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A :=
      ‹Stacks.Ample.IsInvertibleModule X A›
    rw [AlgebraicGeometry.capDegree_succ]
    refine (ih _).trans ?_
    refine congrArg (degAt _ _) (congrArg (iterTopCap A d) ?_)
    refine QuotientAddGroup.induction_on a fun α ↦ ?_
    change MMP.Chow.chowCycleClass ℚ d
      ((Stacks.Chow.invCap (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) A).capOnChow
        (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (d : ℤ)
          (QuotientAddGroup.mk' _ α)) = _
    rw [Stacks.Chow.invCap_capOnChow_mk]
    have e := MMP.Chow.chowCycleClass_firstChernClassCapOfInvertible ℚ A d A hA α
    dsimp only at e
    rw [e, MMP.Chow.chowCycleClass_mk]

open borelMooreHomology in
private lemma capProduct_univ_congrDegree {Y : TopCat.{0}} (j : ℤ) {k k' : ℤ} (h : k = k')
    (x : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y Set.univ j)
    (m : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    capProduct ℚ Y Set.univ j k' x (BorelMooreCross.congrDegree ℚ Y h m) =
      BorelMooreCross.congrDegree ℚ Y (by rw [h]) (capProduct ℚ Y Set.univ j k x m) := by
  subst h
  rfl

open borelMooreHomology in
/-- **The degree of a double cap product of degree-two classes is a Kronecker pairing**:
along a homeomorphism `ψ : A ≅ X`, `deg (ψ^* x' ∩ (ψ^* x ∩ a)) = ⟨x' ∪ x, ψ_* a⟩`. -/
private lemma degAt_capProduct_capProduct_homeomorph {A X : TopCat.{0}} [CompactSpace A]
    [CompactSpace X] (ψ : A ≃ₜ X)
    (x x' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X Set.univ (2 * 1 : ℕ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) A (2 * 2 : ℕ)) :
    degAt A (by norm_num) (BorelMooreCross.congrDegree ℚ A
      (by norm_num : ((2 * 1 : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * 0 : ℕ) : ℤ))
      (capProduct ℚ A Set.univ (2 * 1 : ℕ) (2 * 1 : ℕ)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
          Set.univ (2 * 1 : ℕ)).hom x')
        (BorelMooreCross.congrDegree ℚ A
          (by norm_num : ((2 * 2 : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ) = ((2 * 1 : ℕ) : ℤ))
          (capProduct ℚ A Set.univ (2 * 1 : ℕ) (2 * 2 : ℕ)
            ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X)))
              Set.univ (2 * 1 : ℕ)).hom x) a)))) =
      kron X (2 * 1 + 2 * 1) (MMP.cupNatUniv ℚ X (2 * 1) (2 * 1) x' x)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap
          (2 * 2 : ℕ)).hom a) := by
  rw [← degAt_pushforward (TopCat.ofHom (ψ : C(A, X))) ψ.isProperMap,
    pushforward_congrDegree_apply,
    pushforward_capProduct_pullback_homeomorph ψ ((2 * 1 : ℕ) : ℤ) ((2 * 1 : ℕ) : ℤ) x',
    pushforward_congrDegree_apply,
    pushforward_capProduct_pullback_homeomorph ψ ((2 * 1 : ℕ) : ℤ) ((2 * 2 : ℕ) : ℤ) x a]
  rw [kron, LinearMap.compr₂_apply, capProduct_cupNatUniv, capProduct_univ_congrDegree,
    degAt_congrDegree]
  rfl

end SurfacePositivity

/-! ### Positivity on curves -/

section CurvePositivity

open borelMooreHomology Set

set_option maxRecDepth 10000 in
/-- **The topological degree of an ample line bundle on a smooth projective curve is positive.**
The Kronecker pairing of `c₁(N)` with the fundamental class of `C^an` is `deg N`. -/
private theorem kron_algebraicFirstChernClass_eq {C : Scheme.{0}} [C.Over (Spec (.of ℂ))]
    [IsComplexScheme C] [IsIntegral C] [IsProper (C ↘ Spec (.of ℂ))]
    (hsm : IsSmoothScheme (C ↘ Spec (.of ℂ))) (hdim1 : topologicalKrullDim C = 1)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ)))
    (N : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N]
    (hC1 : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim C)
    {μC : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ C)) (2 * 1 : ℕ)}
    (hμC : IsVarietyFundamentalClass ℚ hC1 μC)
    [CompactSpace (MMP.Analytic.Analytification.space (C ↘ Spec (.of ℂ)))] :
    haveI := compactSpace_underlyingSpace_of_isProper (Z := C)
    kron (MMP.Analytic.Analytification.space (C ↘ Spec (.of ℂ))) (1 + 1)
      (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (MMP.Analytic.algebraicFirstChernClass N))
      ((pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm :
          C(UnderlyingSpace ℂ C, MMP.Analytic.Analytification.space (C ↘ Spec (.of ℂ)))))
        (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm.isProperMap
        (2 * 1 : ℕ)).hom μC) =
      (AlgebraicGeometry.invertibleCurveDegree ℂ (C ↘ Spec (.of ℂ)) hdim1.le N : ℚ) := by
  haveI := compactSpace_underlyingSpace_of_isProper (Z := C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of ℂ))
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of ℂ))
  haveI : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (C ↘ Spec (.of ℂ)) (genericPoint C) = ((1 : ℕ) : ℤ) := by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ 1 ?_
    have hcl : closure ({genericPoint C} : Set C) = Set.univ := (genericPoint_spec C).def
    rw [hcl, (Homeomorph.Set.univ C).isHomeomorph.topologicalKrullDim_eq, hdim1]
    rfl
  have h := MMP.Fourfold.pushforward_capProductPullback_eq_invertibleCurveDegree_smul hsm hdim1
    hproj N (genericPoint C) hξ (genericPoint (Spec (.of ℂ)))
  rw [pointCycleClass_genericPoint_eq hC1 _ hμC] at h
  have h2 := congrArg (deg (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))))) h
  rw [map_smul, deg_pointCycleClass_spec, smul_eq_mul] at h2
  have h3 := (deg_pushforward (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (C ↘ Spec (.of ℂ))))
    (UnderlyingSpace.isProperMap_map (K := ℂ) _) _).symm.trans (h2.trans (mul_one _))
  refine Eq.trans ?_ h3
  simp only [kron, LinearMap.compr₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have key := pushforward_capProduct_pullback_homeomorph
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := C)).symm 2 ((2 * 1 : ℕ) : ℤ)
    (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (MMP.Analytic.algebraicFirstChernClass N)) μC
  change deg _ (congrDegree ℚ _ (by norm_num) (capProduct ℚ _ univ 2 ((2 * 1 : ℕ) : ℤ) _ _)) = _
  rw [← key, deg_congrDegree_pushforward]
  rfl

end CurvePositivity

/-! ### The intersection form on the components -/

section Core

open borelMooreHomology Set

/-- The complex points `E_P(ℂ) ⊆ W(ℂ)` of a component `E_P` of a divisor. -/
private abbrev compPoints {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] (D : Divisor W)
    (P : D.support) : Set (TopCat.of (UnderlyingSpace ℂ W)) :=
  UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W)

private lemma isClosed_compPoints {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] (D : Divisor W)
    (P : D.support) : IsClosed (compPoints D P) :=
  UnderlyingSpace.isClosed_pointsOver P.1.idealSheaf.support.isClosed

private lemma hasProperNeighbourhoodDeformations_compPoints {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] (D : Divisor W) (P Q : D.support) :
    HasProperNeighbourhoodDeformations
      (borelMooreHomology.subsetInclusion (compPoints D Q) ⁻¹' compPoints D P) :=
  UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_pointsOver W
    Q.1.idealSheaf.support P.1.idealSheaf.support

/-- The homeomorphism `E(ℂ) ⊇ A ≅ E^an` of the points over the support of a closed subscheme with
the analytic space of the subscheme. -/
private noncomputable def compAn {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] (I : W.IdealSheafData) :
    TopCat.of (UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set W)) ⟶
      MMP.Analytic.Analytification.space (I.subscheme ↘ Spec (.of ℂ)) :=
  TopCat.ofHom (((subschemePointsHomeomorph I).symm.trans
    MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm : _ ≃ₜ _) : C(_, _))

/-- The inclusion `A ⊆ W(ℂ) ≅ W^an` is the realization of `I.subschemeι` on `A ≅ E^an`. -/
private lemma subsetInclusion_comp_an {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] (I : W.IdealSheafData) :
    borelMooreHomology.subsetInclusion (UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set W)) ≫
      (TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
        TopCat.of (UnderlyingSpace ℂ W) ⟶ MMP.Analytic.Analytification.space (W ↘ Spec (.of ℂ))) =
    compAn I ≫ TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize I.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩ := by
  ext x
  obtain ⟨y, rfl⟩ := (subschemePointsHomeomorph I).surjective x
  change (UnderlyingSpace.map (K := ℂ) I.subschemeι y).toHom = _
  simp [compAn, UnderlyingSpace.toHom_map]
  rfl

/-- **The restricted classes of the components add up to `c₁(𝒪(D))`.** Let `η_Q` be the localized
class of a section of `𝒪(E_Q)` with zero scheme `E_Q`, for the components `E_Q` of `D = ∑ m_Q E_Q`.
On the points `A_P ≅ E_P^an` of a component, `∑_Q m_Q j_P^* η_Q = -c₁(𝒪(-D)|_{E_P})` in `H²`. -/
private theorem sum_toCohomology_pullback_localizedClass {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W] [CompactSpace W]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P)
    (L : D.support → W.Modules) [∀ Q, Stacks.Ample.IsInvertibleModule W (L Q)]
    [∀ Q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L Q)]
    (σ : ∀ Q, W ⟶ MMP.Modules.totalSpace (Scheme.Modules.dual (L Q)))
    [∀ Q, (σ Q).IsOver (Spec (.of ℂ))] (hσp : ∀ Q, σ Q ≫ MMP.Modules.proj _ = 𝟙 W)
    (hσ : ∀ Q, MMP.Modules.zeroLocus _ (σ Q) = Q.1.idealSheaf)
    (e : ∀ Q, L Q ≅ MMP.Mori.Divisor.divisorialSheaf (Finsupp.single Q.1 (1 : ℤ)))
    (P : D.support) :
    haveI := isInvertible_divisorialSheaf_of_isSmoothScheme hsm (-D)
    ∑ Q, (D.coeff Q.1 : ℚ) • (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (compPoints D P))
        (borelMooreHomology.subsetInclusion (compPoints D P) ⁻¹' compPoints D Q)
        ((2 * 1 : ℕ) : ℤ)).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
          (borelMooreHomology.subsetInclusion (compPoints D P)) (compPoints D Q)
          ((2 * 1 : ℕ) : ℤ)).hom (localizedClass (σ Q) Q.1.idealSheaf (hσ Q))) =
      -(cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) Set.univ 2).hom
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (MMP.Analytic.algebraicFirstChernClass
            ((Scheme.Modules.pullback P.1.idealSheaf.subschemeι).obj (-D).divisorialSheaf))) := by
  classical
  haveI := isInvertible_divisorialSheaf_of_isSmoothScheme hsm (-D)
  set ε : TopCat.of (UnderlyingSpace ℂ W) ⟶ MMP.Analytic.Analytification.space (W ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨_, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ with hε
  let c : Divisor W → MMP.Analytic.singularCohomology ℤ
      (MMP.Analytic.Analytification.space (W ↘ Spec (.of ℂ))) 2 := fun N ↦
    @MMP.Analytic.algebraicFirstChernClass W _ N.divisorialSheaf
      (isInvertible_divisorialSheaf_of_isSmoothScheme hsm N)
  -- each term
  have hterm : ∀ Q : D.support, (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (compPoints D P))
        (borelMooreHomology.subsetInclusion (compPoints D P) ⁻¹' compPoints D Q)
        ((2 * 1 : ℕ) : ℤ)).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
          (borelMooreHomology.subsetInclusion (compPoints D P)) (compPoints D Q)
          ((2 * 1 : ℕ) : ℤ)).hom (localizedClass (σ Q) Q.1.idealSheaf (hσ Q))) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusion (compPoints D P) ≫ ε) Set.univ 2).hom
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (c (Finsupp.single Q.1 (1 : ℤ)))) := by
    intro Q
    rw [cohomologyWithSupports.toCohomology_pullback_eq_map, toCohomology_localizedClass (σ Q) (hσp Q)]
    have hc := @MMP.Analytic.algebraicFirstChernClass_eq_of_iso W _ _ _
      inferInstance
      (isInvertible_divisorialSheaf_of_isSmoothScheme hsm _) (e Q)
    rw [hc, pullback_univ_comp]
    rfl
  rw [Finset.sum_congr rfl fun Q _ ↦ by rw [hterm Q]]
  -- the sum of the divisor classes
  have hD' : ∑ Q : D.support, (D.coeff Q.1).toNat • (Finsupp.single Q.1 (1 : ℤ) : Divisor W) = D := by
    conv_rhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum, ← Finset.sum_coe_sort D.support]
    refine Finset.sum_congr rfl fun Q _ ↦ ?_
    rw [Finsupp.smul_single, nsmul_eq_mul, mul_one, Int.toNat_of_nonneg (hD Q.1)]
    rfl
  have hsum : ∑ Q : D.support, (D.coeff Q.1).toNat • c (Finsupp.single Q.1 (1 : ℤ)) = - c (-D) := by
    have h1 := algebraicFirstChernClass_divisorialSheaf_sum hsm Finset.univ
      (fun Q : D.support ↦ (D.coeff Q.1).toNat) (fun Q ↦ (Finsupp.single Q.1 (1 : ℤ) : Divisor W))
    have h2 := algebraicFirstChernClass_divisorialSheaf_neg hsm (-D)
    simp only [neg_neg] at h2
    change c (∑ Q : D.support, (D.coeff Q.1).toNat • (Finsupp.single Q.1 (1 : ℤ) : Divisor W)) =
      _ at h1
    rw [hD'] at h1
    rw [← h1]
    exact h2
  have hsmul : ∀ Q : D.support, (D.coeff Q.1 : ℚ) •
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusion (compPoints D P) ≫ ε) Set.univ 2).hom
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (c (Finsupp.single Q.1 (1 : ℤ)))) =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusion (compPoints D P) ≫ ε) Set.univ 2).hom
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          ((D.coeff Q.1).toNat • c (Finsupp.single Q.1 (1 : ℤ)))) := by
    intro Q
    rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (hD Q.1)).symm
  refine (Finset.sum_congr rfl fun Q _ ↦ hsmul Q).trans ?_
  rw [← map_sum, ← map_sum, hsum, map_neg, map_neg,
    pullback_univ_congr (subsetInclusion_comp_an P.1.idealSheaf), pullback_univ_comp]
  congr 2
  rw [MMP.Analytic.algebraicFirstChernClass_pullback P.1.idealSheaf.subschemeι
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize P.1.idealSheaf.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩) (fun _ ↦ rfl) (-D).divisorialSheaf]
  exact (MMP.Analytic.singularCohomology.mapCoeff_relativeSingularCohomology_map
    (Int.castRingHom ℚ) _ _ 2 _).symm

/-- The analytic realization of a morphism over `ℂ`, read on underlying spaces, is the map of
underlying spaces. -/
private lemma realize_homeomorphUnderlyingSpace_symm {V V' : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [V'.Over (Spec (.of ℂ))] (f : V ⟶ V') [f.IsOver (Spec (.of ℂ))]
    (hf : f ≫ (V' ↘ Spec (.of ℂ)) = V ↘ Spec (.of ℂ)) (p : UnderlyingSpace ℂ V) :
    MMP.Analytic.ComplexPoints.realize f hf
        (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm p) =
      MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm
        (UnderlyingSpace.map (K := ℂ) f p) := by
  apply MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.injective
  apply UnderlyingSpace.ext
  rw [Homeomorph.apply_symm_apply, MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace_apply,
    MMP.Analytic.ComplexPoints.realize_hom, UnderlyingSpace.toHom_map,
    ← MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace_apply, Homeomorph.apply_symm_apply]

/-- The curve over a double curve through `P` and `Q` lies on `E_Q`, scheme-theoretically. -/
private lemma ker_subschemeι_le_ker_curveDiv {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P : D.support)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    {Q : D.support} (hQ : Q ∈ MMP.Fourfold.comps D η) :
    Q.1.idealSheaf.subschemeι.ker ≤
      ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫
        P.1.idealSheaf.subschemeι).ker := by
  haveI := (MMP.Fourfold.curveDiv hsnc hdim P hη hP).integral
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
  intro w hw
  refine closure_minimal ?_ Q.1.idealSheaf.support.isClosed hw
  rintro _ ⟨y, rfl⟩
  exact subschemeι_curveDiv_mem hsnc hdim P hη hP hQ y

/-- The inclusion of the curve over a double curve through `P` and `Q` into `E_Q`. -/
private noncomputable abbrev curveDivToComp {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P : D.support)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    {Q : D.support} (hQ : Q ∈ MMP.Fourfold.comps D η) :
    (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ⟶ Q.1.idealSheaf.subscheme :=
  IsClosedImmersion.lift Q.1.idealSheaf.subschemeι
    ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫ P.1.idealSheaf.subschemeι)
    (ker_subschemeι_le_ker_curveDiv hsnc hdim P hη hP hQ)

private lemma curveDivToComp_comp_over {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P : D.support)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    {Q : D.support} (hQ : Q ∈ MMP.Fourfold.comps D η) :
    curveDivToComp hsnc hdim P hη hP hQ ≫ (Q.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) =
      (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme ↘ Spec (.of ℂ) := by
  change curveDivToComp hsnc hdim P hη hP hQ ≫ Q.1.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ)) =
    ((MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι ≫
      P.1.idealSheaf.subschemeι) ≫ (W ↘ Spec (.of ℂ))
  rw [← Category.assoc, IsClosedImmersion.lift_fac]

/-- The curve over a double curve, mapped into `E_Q` and then into `W`, is the curve in `E_P`
mapped into `W`. -/
private lemma map_curveDivToComp {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3) (P : D.support)
    {η : W} (hη : MMP.Fourfold.IsDoubleCurve D η) (hP : P ∈ MMP.Fourfold.comps D η)
    {Q : D.support} (hQ : Q ∈ MMP.Fourfold.comps D η)
    [(curveDivToComp hsnc hdim P hη hP hQ).IsOver (Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subscheme) :
    UnderlyingSpace.map (K := ℂ) Q.1.idealSheaf.subschemeι
        (UnderlyingSpace.map (K := ℂ) (curveDivToComp hsnc hdim P hη hP hQ) p) =
      UnderlyingSpace.map (K := ℂ) P.1.idealSheaf.subschemeι
        (UnderlyingSpace.map (K := ℂ) (MMP.Fourfold.curveDiv hsnc hdim P hη hP).idealSheaf.subschemeι p) := by
  apply UnderlyingSpace.ext
  simp only [UnderlyingSpace.toHom_map, Category.assoc, IsClosedImmersion.lift_fac]

/-- A point of `E_I(ℂ) ⊆ W(ℂ)` lying under a point `p` of a scheme `Z` over `E_I` is, in the
analytic space of `E_I`, the realization of `p`. -/
private lemma compAn_eq_realize {W Z : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [Z.Over (Spec (.of ℂ))] (I : W.IdealSheafData) (g : Z ⟶ I.subscheme)
    [g.IsOver (Spec (.of ℂ))] (hg : g ≫ (I.subscheme ↘ Spec (.of ℂ)) = Z ↘ Spec (.of ℂ))
    (x : UnderlyingSpace.pointsOver (K := ℂ) (I.support : Set W)) (p : UnderlyingSpace ℂ Z)
    (hx : (x : UnderlyingSpace ℂ W) =
      UnderlyingSpace.map (K := ℂ) I.subschemeι (UnderlyingSpace.map (K := ℂ) g p)) :
    compAn I x = MMP.Analytic.ComplexPoints.realize g hg
      (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm p) := by
  rw [realize_homeomorphUnderlyingSpace_symm]
  change MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm
    ((subschemePointsHomeomorph I).symm x) = _
  congr 1
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext hx

set_option maxRecDepth 10000 in
open Classical in
/-- **The pairing of two components is a sum over their double curves**: for `P ≠ Q`,
`τ_{PQ}(x, y) = -∑_C ⟨x|_C ∪ y|_C, [C]⟩`, the sum over the curves `C ⊆ E_P` over the double
curves through `P` and `Q`. -/
private theorem tauForm_compAn_eq_sum {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hQP : Q ≠ P)
    [IsIntegral P.1.idealSheaf.subscheme] [IsNormal P.1.idealSheaf.subscheme]
    [CompactSpace P.1.idealSheaf.subscheme] [CompactSpace (compPoints D P)]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) (2 * 2 : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E : W.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = Q.1.idealSheaf)
    [∀ k : DoubleCurveThrough D P Q, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme]
    [∀ k : DoubleCurveThrough D P Q, CompactSpace (MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))]
    (hk : ∀ k : DoubleCurveThrough D P Q, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D P Q, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ
        (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)) (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k))
    (x : H1Q P.1.idealSheaf.subscheme) (y : H1Q Q.1.idealSheaf.subscheme) :
    tauForm (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P)
        (localizedClass σ Q.1.idealSheaf hσ)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph P.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ P.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph P.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom μE)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn Q.1.idealSheaf) univ 1).hom
          y) =
      ∑ k : DoubleCurveThrough D P Q, -kron (MMP.Analytic.Analytification.space
          ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))
          (1 + 1)
        (MMP.cupNatUniv ℚ _ 1 1
          (pullH1 (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl x)
          (pullH1 (curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2)
            (curveDivToComp_comp_over hsnc hdim P k.1.2 k.2.1 k.2.2) y))
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm :
              C(_, _)))
          (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm.isProperMap
          (2 * 1 : ℕ)).hom (μC k)) := by
  haveI : ∀ k : DoubleCurveThrough D P Q, CompactSpace (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme) := fun k ↦
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := _)).compactSpace
  have e := gysinClass_localizedClass_eq_sum_curveDiv hsnc hdim P Q hQP hn hμE σ hσp hσ
    (hasProperNeighbourhoodDeformations_compPoints D Q P) hk μC hμC
  haveI : CompactSpace (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace (compPoints D P)›).inter_right
      (isClosed_compPoints D Q))
  refine (congrArg (fun z ↦ capPair (TopCat.of (compPoints D P ∩ compPoints D Q : Set _)) z
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interRight (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn Q.1.idealSheaf) univ 1).hom
          y))) e).trans ?_
  refine (capPair_sum _ _ _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  haveI : (curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2).IsOver (Spec (.of ℂ)) :=
    ⟨curveDivToComp_comp_over hsnc hdim P k.1.2 k.2.1 k.2.2⟩
  refine capPair_pushforward_eq_neg_kron
    (Y := TopCat.of (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))))
    (C := TopCat.of (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme))
    (X := MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ))) _ _
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
      (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (interRight (compPoints D P) (compPoints D Q)) (compAn Q.1.idealSheaf)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize (curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2)
      (curveDivToComp_comp_over hsnc hdim P k.1.2 k.2.1 k.2.2),
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩) ?_ ?_ (μC k) x y
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl _ p rfl
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize Q.1.idealSheaf
      (curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2) (curveDivToComp_comp_over hsnc hdim P k.1.2 k.2.1 k.2.2) _ p
      (map_curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2 p).symm

open Classical in
/-- **The Gysin class of `E_Q` on `[E_P]` through the curves on `E_Q`.** By the symmetry of the
Gysin classes (`gysinClass_comm`), `j_P^* η_Q ∩ [E_P]` is the sum of the curves `C ⊆ E_Q` over
the double curves through `P` and `Q`, read in `E_P(ℂ) ∩ E_Q(ℂ)`. -/
private theorem gysinClass_localizedClass_eq_sum_curveDiv_swap {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hPQ : P ≠ Q)
    [IsIntegral Q.1.idealSheaf.subscheme] [IsNormal Q.1.idealSheaf.subscheme]
    [CompactSpace Q.1.idealSheaf.subscheme]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Q.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ Q.1.idealSheaf.subscheme)) (2 * 2 : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E E' : W.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E' 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = P.1.idealSheaf)
    (σ' : W ⟶ MMP.Modules.totalSpace E') [σ'.IsOver (Spec (.of ℂ))]
    (hσ' : MMP.Modules.zeroLocus E' σ' = Q.1.idealSheaf)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) ((2 * 3 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D P)) 4)
    (hηP : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D P)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ P.1.idealSheaf hσ) μ = congrDegree ℚ _ (by norm_num) a)
    (hηQ : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D Q)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W Q.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ' Q.1.idealSheaf hσ') μ = congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph Q.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ Q.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (Q.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph Q.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom μE))
    [∀ k : DoubleCurveThrough D Q P, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme]
    (hk : ∀ k : DoubleCurveThrough D Q P, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D Q P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ
        (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)) (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k)) :
    gysinClass (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P) 2 4
        (localizedClass σ' Q.1.idealSheaf hσ') a =
      ∑ k : DoubleCurveThrough D Q P, congrDegree ℚ _ (by norm_num) ((pushforward ℚ (ModuleCat.of ℚ ℚ)
        (subschemeInterHom Q.1.idealSheaf P.1.idealSheaf
          (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf
          (subschemeι_curveDiv_mem hsnc hdim Q k.1.2 k.2.1 k.2.2) ≫
            interSwap (compPoints D P) (compPoints D Q))
        ((isProperMap_subsetInclusionOfSubset ((isClosed_compPoints D Q).inter
          (isClosed_compPoints D P)) (inter_comm _ _).le).comp
          (isProperMap_subschemeInterHom _ _ _ _)) ((2 * 1 : ℕ) : ℤ)).hom (μC k)) := by
  have hc := gysinClass_comm (isClosed_compPoints D P) (isClosed_compPoints D Q)
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support)
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W Q.1.idealSheaf.support)
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W
      (P.1.idealSheaf.support ⊓ Q.1.idealSheaf.support))
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W
      (Q.1.idealSheaf.support ⊓ P.1.idealSheaf.support))
    (hasProperNeighbourhoodDeformations_compPoints D Q P)
    (hasProperNeighbourhoodDeformations_compPoints D P Q) μ a _ _ _ hηP hηQ
  have e := gysinClass_localizedClass_eq_sum_curveDiv hsnc hdim Q P hPQ hn hμE σ hσp hσ
    (hasProperNeighbourhoodDeformations_compPoints D P Q) hk μC hμC
  refine hc.trans (((congrArg (pushforward ℚ (ModuleCat.of ℚ ℚ) (interSwap _ _)
    (isProperMap_subsetInclusionOfSubset ((isClosed_compPoints D Q).inter (isClosed_compPoints D P))
      (inter_comm _ _).le) (4 - 2)).hom e).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun k _ ↦ ?_))
  rw [pushforward_comp_apply', pushforward_congrDegree_apply]

set_option maxRecDepth 10000 in
open Classical in
/-- **The pairing of two components through the double curves on the second.** By the symmetry
of the Gysin classes, for `P ≠ Q`, `τ_{PQ}(x, y) = -∑_C ⟨x|_C ∪ y|_C, [C]⟩`, the sum over the
curves `C ⊆ E_Q` over the double curves through `P` and `Q`. -/
private theorem tauForm_compAn_eq_sum_swap {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hPQ : P ≠ Q)
    [IsIntegral Q.1.idealSheaf.subscheme] [IsNormal Q.1.idealSheaf.subscheme]
    [CompactSpace Q.1.idealSheaf.subscheme] [CompactSpace (compPoints D P)]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Q.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ Q.1.idealSheaf.subscheme)) (2 * 2 : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E E' : W.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E' 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = P.1.idealSheaf)
    (σ' : W ⟶ MMP.Modules.totalSpace E') [σ'.IsOver (Spec (.of ℂ))]
    (hσ' : MMP.Modules.zeroLocus E' σ' = Q.1.idealSheaf)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) ((2 * 3 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D P)) 4)
    (hηP : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D P)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ P.1.idealSheaf hσ) μ = congrDegree ℚ _ (by norm_num) a)
    (hηQ : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D Q)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W Q.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ' Q.1.idealSheaf hσ') μ = congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph Q.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ Q.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (Q.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph Q.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom μE))
    [∀ k : DoubleCurveThrough D Q P, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme]
    [∀ k : DoubleCurveThrough D Q P, CompactSpace (MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))]
    (hk : ∀ k : DoubleCurveThrough D Q P, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D Q P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ
        (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)) (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k))
    (x : H1Q P.1.idealSheaf.subscheme) (y : H1Q Q.1.idealSheaf.subscheme) :
    tauForm (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P)
        (localizedClass σ' Q.1.idealSheaf hσ') a
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn Q.1.idealSheaf) univ 1).hom
          y) =
      ∑ k : DoubleCurveThrough D Q P, -kron (MMP.Analytic.Analytification.space
          ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))
          (1 + 1)
        (MMP.cupNatUniv ℚ _ 1 1
          (pullH1 (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
            (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) x)
          (pullH1 (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subschemeι rfl y))
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm :
              C(_, _)))
          (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm.isProperMap
          (2 * 1 : ℕ)).hom (μC k)) := by
  haveI : ∀ k : DoubleCurveThrough D Q P, CompactSpace (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme) := fun k ↦
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := _)).compactSpace
  haveI : CompactSpace (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2
      ‹CompactSpace (compPoints D P)›).inter_right (isClosed_compPoints D Q))
  refine (congrArg (fun z ↦ capPair (TopCat.of (compPoints D P ∩ compPoints D Q : Set _)) z
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interRight (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn Q.1.idealSheaf) univ 1).hom
          y))) (gysinClass_localizedClass_eq_sum_curveDiv_swap hsnc hdim P Q hPQ hn hμE σ hσp hσ σ' hσ'
      μ a hηP hηQ hk μC hμC)).trans ?_
  refine (capPair_sum _ _ _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  haveI : (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2).IsOver (Spec (.of ℂ)) :=
    ⟨curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2⟩
  refine capPair_pushforward_eq_neg_kron
    (Y := TopCat.of (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))))
    (C := TopCat.of (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme))
    (X := MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ))) _ _
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
      (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (interRight (compPoints D P) (compPoints D Q)) (compAn Q.1.idealSheaf)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
      (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2),
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩) ?_ ?_ (μC k) x y
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2) (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) _ p
      (map_curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2 p).symm
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize Q.1.idealSheaf
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subschemeι rfl _ p rfl

set_option maxRecDepth 10000 in
open Classical in
/-- **The diagonal pairing of a component along another is a sum over their double curves**:
for `P ≠ Q` and `x, y ∈ H¹(E_P)`, `τ'_{PQ}(x, y) = -∑_C ⟨x|_C ∪ y|_C, [C]⟩`, the sum over the
curves `C ⊆ E_P` over the double curves through `P` and `Q`. -/
private theorem tauForm'_compAn_eq_sum {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hQP : Q ≠ P)
    [IsIntegral P.1.idealSheaf.subscheme] [IsNormal P.1.idealSheaf.subscheme]
    [CompactSpace P.1.idealSheaf.subscheme] [CompactSpace (compPoints D P)]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim P.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) (2 * 2 : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E : W.Modules} [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = Q.1.idealSheaf)
    [∀ k : DoubleCurveThrough D P Q, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme]
    [∀ k : DoubleCurveThrough D P Q, CompactSpace (MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))]
    (hk : ∀ k : DoubleCurveThrough D P Q, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D P Q, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ
        (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)) (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k))
    (x y : H1Q P.1.idealSheaf.subscheme) :
    tauForm' (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P)
        (localizedClass σ Q.1.idealSheaf hσ)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph P.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ P.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph P.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom μE)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom
          y) =
      ∑ k : DoubleCurveThrough D P Q, -kron (MMP.Analytic.Analytification.space
          ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))
          (1 + 1)
        (MMP.cupNatUniv ℚ _ 1 1
          (pullH1 (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl x)
          (pullH1 (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl y))
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm :
              C(_, _)))
          (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm.isProperMap
          (2 * 1 : ℕ)).hom (μC k)) := by
  haveI : ∀ k : DoubleCurveThrough D P Q, CompactSpace (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme) := fun k ↦
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := _)).compactSpace
  have e := gysinClass_localizedClass_eq_sum_curveDiv hsnc hdim P Q hQP hn hμE σ hσp hσ
    (hasProperNeighbourhoodDeformations_compPoints D Q P) hk μC hμC
  haveI : CompactSpace (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace (compPoints D P)›).inter_right
      (isClosed_compPoints D Q))
  refine (congrArg (fun z ↦ capPair (TopCat.of (compPoints D P ∩ compPoints D Q : Set _)) z
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom
          y))) e).trans ?_
  refine (capPair_sum _ _ _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  haveI : (curveDivToComp hsnc hdim P k.1.2 k.2.1 k.2.2).IsOver (Spec (.of ℂ)) :=
    ⟨curveDivToComp_comp_over hsnc hdim P k.1.2 k.2.1 k.2.2⟩
  refine capPair_pushforward_eq_neg_kron
    (Y := TopCat.of (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))))
    (C := TopCat.of (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme))
    (X := MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ))) _ _
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
      (X := (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme)).symm
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl,
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩) ?_ ?_ (μC k) x y
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl _ p rfl
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subschemeι rfl _ p rfl

set_option maxRecDepth 10000 in
open Classical in
/-- **The diagonal pairing through the double curves on the second component.** By the symmetry
of the Gysin classes, for `P ≠ Q` and `x, y ∈ H¹(E_P)`, `τ'_{PQ}(x, y) = -∑_C ⟨x|_C ∪ y|_C, [C]⟩`,
the sum over the curves `C ⊆ E_Q` over the double curves through `P` and `Q`. -/
private theorem tauForm'_compAn_eq_sum_swap {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] {D : Divisor W}
    (hsnc : D.IsSNC (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    [Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η}] (P Q : D.support) (hPQ : P ≠ Q)
    [IsIntegral Q.1.idealSheaf.subscheme] [IsNormal Q.1.idealSheaf.subscheme]
    [CompactSpace Q.1.idealSheaf.subscheme] [CompactSpace (compPoints D P)]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Q.1.idealSheaf.subscheme)
    {μE : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ Q.1.idealSheaf.subscheme)) (2 * 2 : ℕ)}
    (hμE : IsVarietyFundamentalClass ℚ hn μE) {E E' : W.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E' 1]
    (σ : W ⟶ MMP.Modules.totalSpace E) [σ.IsOver (Spec (.of ℂ))]
    (hσp : σ ≫ MMP.Modules.proj E = 𝟙 W) (hσ : MMP.Modules.zeroLocus E σ = P.1.idealSheaf)
    (σ' : W ⟶ MMP.Modules.totalSpace E') [σ'.IsOver (Spec (.of ℂ))]
    (hσ' : MMP.Modules.zeroLocus E' σ' = Q.1.idealSheaf)
    (μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) ((2 * 3 : ℕ) : ℤ))
    (a : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D P)) 4)
    (hηP : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D P)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ P.1.idealSheaf hσ) μ = congrDegree ℚ _ (by norm_num) a)
    (hηQ : capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W)) (isClosed_compPoints D Q)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W Q.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (localizedClass σ' Q.1.idealSheaf hσ') μ = congrDegree ℚ _ (by norm_num)
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((subschemePointsHomeomorph Q.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ Q.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (Q.1.idealSheaf.support : Set W))))
          (subschemePointsHomeomorph Q.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom μE))
    [∀ k : DoubleCurveThrough D Q P, IsIntegral
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme]
    [∀ k : DoubleCurveThrough D Q P, CompactSpace (MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))]
    (hk : ∀ k : DoubleCurveThrough D Q P, ((1 : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)
    (μC : ∀ k : DoubleCurveThrough D Q P, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ
        (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)) (2 * 1 : ℕ))
    (hμC : ∀ k, IsVarietyFundamentalClass ℚ (hk k) (μC k))
    (x y : H1Q P.1.idealSheaf.subscheme) :
    tauForm' (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P)
        (localizedClass σ' Q.1.idealSheaf hσ') a
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x)
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom
          y) =
      ∑ k : DoubleCurveThrough D Q P, -kron (MMP.Analytic.Analytification.space
          ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ)))
          (1 + 1)
        (MMP.cupNatUniv ℚ _ 1 1
          (pullH1 (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
            (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) x)
          (pullH1 (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
            (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) y))
        ((pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm :
              C(_, _)))
          (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm.isProperMap
          (2 * 1 : ℕ)).hom (μC k)) := by
  haveI : ∀ k : DoubleCurveThrough D Q P, CompactSpace (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme) := fun k ↦
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := _)).compactSpace
  haveI : CompactSpace (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))) :=
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2
      ‹CompactSpace (compPoints D P)›).inter_right (isClosed_compPoints D Q))
  refine (congrArg (fun z ↦ capPair (TopCat.of (compPoints D P ∩ compPoints D Q : Set _)) z
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom x))
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (interLeft (compPoints D P) (compPoints D Q)) univ 1).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom
          y))) (gysinClass_localizedClass_eq_sum_curveDiv_swap hsnc hdim P Q hPQ hn hμE σ hσp hσ σ' hσ'
      μ a hηP hηQ hk μC hμC)).trans ?_
  refine (capPair_sum _ _ _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  haveI : (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2).IsOver (Spec (.of ℂ)) :=
    ⟨curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2⟩
  refine capPair_pushforward_eq_neg_kron
    (Y := TopCat.of (compPoints D P ∩ compPoints D Q : Set (TopCat.of (UnderlyingSpace ℂ W))))
    (C := TopCat.of (UnderlyingSpace ℂ
      (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme))
    (X := MMP.Analytic.Analytification.space
      ((MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ))) _ _
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
      (X := (MMP.Fourfold.curveDiv hsnc hdim Q k.1.2 k.2.1).idealSheaf.subscheme)).symm
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (interLeft (compPoints D P) (compPoints D Q)) (compAn P.1.idealSheaf)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
      (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2),
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩)
    (TopCat.ofHom ⟨MMP.Analytic.ComplexPoints.realize (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2)
      (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2),
      MMP.Analytic.ComplexPoints.continuous_realize _ _⟩) ?_ ?_ (μC k) x y
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2) (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) _ p
      (map_curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2 p).symm
  · exact ConcreteCategory.hom_ext _ _ fun p ↦ compAn_eq_realize P.1.idealSheaf
      (curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2) (curveDivToComp_comp_over hsnc hdim Q k.1.2 k.2.1 k.2.2) _ p
      (map_curveDivToComp hsnc hdim Q k.1.2 k.2.1 k.2.2 p).symm

/-- A sum over a subtype is the sum over the corresponding filter. -/
private lemma sum_subtype_eq_sum_filter {K M : Type*} [Fintype K] [AddCommMonoid M]
    {A : K → Prop} [Fintype {k // A k}] {B : K → Prop} [DecidablePred B]
    (hAB : ∀ k, A k ↔ B k) (T : {k // A k} → M) (T' : K → M)
    (hT : ∀ k (h : A k), T ⟨k, h⟩ = T' k) :
    ∑ k', T k' = ∑ k ∈ Finset.univ.filter B, T' k := by
  refine Finset.sum_bij (fun k' _ ↦ k'.1)
    (fun k' _ ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, (hAB _).1 k'.2⟩)
    (fun _ _ _ _ h ↦ Subtype.ext h) (fun k hk ↦ ?_) (fun k' _ ↦ hT k'.1 k'.2)
  exact ⟨⟨k, (hAB k).2 (Finset.mem_filter.1 hk).2⟩, Finset.mem_univ _, rfl⟩

private lemma mem_and_mem_of_eq_pair {α : Type*} [DecidableEq α] {s : Finset α} {a b P Q : α}
    (hs : s = {a, b}) (h : a = P ∧ b = Q) : P ∈ s ∧ Q ∈ s := by
  rw [hs, ← h.1, ← h.2]
  exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

/-- Two distinct elements of a pair `{a, b}` with `f a < f b` are `a` and `b` in the order
of `f`. -/
private lemma eq_and_eq_of_mem_pair {α β : Type*} [DecidableEq α] [LinearOrder β] (f : α → β)
    {a b P Q : α} (hab : f a < f b) (hP : P ∈ ({a, b} : Finset α))
    (hQ : Q ∈ ({a, b} : Finset α)) (hPQ : f P < f Q) : a = P ∧ b = Q := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · exact absurd hPQ (lt_irrefl _)
  · exact ⟨rfl, rfl⟩
  · exact absurd (hPQ.trans hab) (lt_irrefl _)
  · exact absurd hPQ (lt_irrefl _)

set_option maxRecDepth 20000 in
/-- **The self-intersection of an ample line bundle on a surface is positive**:
`∫_S c₁(L)² > 0` for an ample invertible sheaf `L` on a complex surface `S`, proper over `ℂ`.
The degree `deg(c₁(L)² ∩ [S]_2)` is positive (Stacks 0BEV), and by Fulton's Proposition 19.2 it is
`∫ c₁ᵗᵒᵖ(L) ∩ (c₁ᵗᵒᵖ(L) ∩ cl(S))`. -/
private theorem kron_cup_algebraicFirstChernClass_pos {S : Scheme.{0}} [S.Over (Spec (.of ℂ))]
    [IsComplexScheme S] [IsIntegral S] [IsProper (S ↘ Spec (.of ℂ))]
    [CompactSpace (UnderlyingSpace ℂ S)]
    [CompactSpace (MMP.Analytic.Analytification.space (S ↘ Spec (.of ℂ)))]
    (hn : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim S)
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ S)) (2 * 2 : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ hn μ) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    [Stacks.Ample.IsInvertibleModule S L] (hL : Stacks.Ample.IsAmple S L) :
    0 < kron (MMP.Analytic.Analytification.space (S ↘ Spec (.of ℂ))) (2 * 1 + 2 * 1)
      (MMP.cupNatUniv ℚ _ (2 * 1) (2 * 1)
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (MMP.Analytic.algebraicFirstChernClass L))
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (MMP.Analytic.algebraicFirstChernClass L)))
      ((pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := S)).symm :
          C(_, _)))
        (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := S)).symm.isProperMap
        (2 * 2 : ℕ)).hom μ) := by
  have hL' : Scheme.Modules.IsAmple S L := (Stacks.AmpleBridge.isAmple_iff_isAmple S L).mp hL
  have hZ : topologicalKrullDim S = ((2 : ℕ) : WithBot ℕ∞) := hn.symm
  have hpos := AlgebraicGeometry.intersectionNumber_pos ℂ (S ↘ Spec (.of ℂ)) (𝟙 S) 2 hZ
    (fun _ ↦ L) fun _ ↦ hL'
  rw [AlgebraicGeometry.intersectionNumber_eq_capDegree_of_le ℂ 2 (S ↘ Spec (.of ℂ)) (𝟙 S)
    hZ.le (fun _ ↦ L)] at hpos
  have key := capDegree_eq_degAt_iterTopCap L hL 2
    (QuotientAddGroup.mk' _ (Stacks.Chow.cycleAssociatedToClosedSubscheme
      (Stacks.Chow.fieldChowSituation ℂ) (S ↘ Spec (.of ℂ)) (𝟙 S) ((2 : ℕ) : ℤ)))
  rw [QuotientAddGroup.mk'_apply] at key hpos
  rw [MMP.Chow.chowCycleClass_mk, cycleClass_cycleAssociatedToClosedSubscheme_id_eq hn hμ] at key
  have h4 := degAt_capProduct_capProduct_homeomorph
    (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace (X := S)).symm
    (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (MMP.Analytic.algebraicFirstChernClass L))
    (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (MMP.Analytic.algebraicFirstChernClass L)) μ
  have hc : MMP.Chow.firstChernClassTop ℚ L =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (MMP.Modules.complexPointsHom S)
        Set.univ 2).hom (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (MMP.Analytic.algebraicFirstChernClass L)) :=
    MMP.Modules.topFirstChernClass_dual ℚ L
  have hfin := key.trans (Eq.trans (by
    simp only [iterTopCap, MMP.Chow.firstChernClassTopCap, LinearMap.comp_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, hc]
    rfl) h4)
  rw [← hfin]
  exact_mod_cast hpos

/-- A scheme smooth over a field is normal: its local rings are regular. -/
private theorem isNormal_of_smooth {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [Smooth f] :
    IsNormal S where
  stalk_isDomain x :=
    have := isRegularLocalRing_stalk_of_smooth_over_field f x
    (AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing _).1
  stalk_normal x :=
    have := isRegularLocalRing_stalk_of_smooth_over_field f x
    (AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing _).2

/-- **A prime divisor on a smooth variety is the zero scheme of a section of an invertible
module**: the canonical section `1` of Stacks' invertible sheaf `𝒪_W(S)` of the effective Cartier
divisor `S` (Stacks Tag 01WS) is non-zero, its Stacks zero scheme is `S`, and `𝒪_W(S)` is the
divisorial sheaf of `S`. -/
private theorem exists_globalSection_zeroScheme_eq {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W] [CompactSpace W]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (S : MMP.Mori.PrimeDivisor W) :
    ∃ (L : W.Modules) (_ : Stacks.Ample.IsInvertibleModule W L) (s : Γ(L, ⊤)), s ≠ 0 ∧
      Stacks.Divisors.zeroScheme W L s = S.idealSheaf ∧
        Nonempty (L ≅ MMP.Mori.Divisor.divisorialSheaf (Finsupp.single S (1 : ℤ))) := by
  haveI hcart : Stacks.Divisors.IsEffectiveCartierDivisor S.idealSheaf :=
    MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm S
  obtain ⟨e⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' S
    hcart (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)
  let L : W.Modules := Stacks.Divisors.modulesInvertibleSheaf S.idealSheaf
  let e' : MMP.Mori.Divisor.divisorialSheaf (Finsupp.single S (1 : ℤ)) ≅ L := e
  haveI hL : Stacks.Ample.IsInvertibleModule W L :=
    Stacks.Divisors.isInvertible_invertibleSheaf S.idealSheaf
  let t : Γ(L, ⊤) := Stacks.Divisors.canonicalSection S.idealSheaf
  have hZ : Stacks.Divisors.zeroScheme W L t = S.idealSheaf :=
    Stacks.Divisors.zeroScheme_canonicalSection' S.idealSheaf
  refine ⟨L, hL, t, ?_, hZ, ⟨e'.symm⟩⟩
  intro h0
  have hbot : Stacks.Divisors.zeroScheme W L t = ⊥ := by
    rw [h0]
    refine le_antisymm (fun U => ?_) bot_le
    refine le_trans (Scheme.IdealSheafData.ideal_ofIdeals_le _ U) ?_
    show Ideal.span _ ≤ (⊥ : Ideal Γ(W, U.1))
    rw [Ideal.span_le]
    rintro a ⟨φ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_bot, map_zero, map_zero]
  have hS : S.idealSheaf = ⊥ := hZ.symm.trans hbot
  have hcl : closure ({S.genericPoint} : Set W) = Set.univ := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support, hS, Scheme.IdealSheafData.support_bot]
    rfl
  have hmax : IsMax S.genericPoint := fun y _ ↦ by
    change S.genericPoint ⤳ y
    rw [specializes_iff_mem_closure, hcl]
    exact Set.mem_univ _
  have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint S
  rw [Order.coheight_eq_zero.2 hmax] at h1
  exact zero_ne_one h1

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 20000 in
/-- **Nondegeneracy of the intersection form on the components.** For classes
`c_P ∈ H³(W, W - E_P)` on the components `E_P` of an antiample snc fibre, if
`∑_{P,Q} deg (j_{E_Q}^* c_P ∩ y_Q) = 0` for all `y_Q ∈ H₃(E_Q)`, then every `c_P ∩ [W]`
vanishes. -/
private theorem dualityMap_eq_zero_of_forall_compPairing {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ)))
    (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hprop : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))))
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hamp : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf))
    [SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W)) ((2 * 3 : ℕ) : ℤ)}
    (hμ : IsVarietyFundamentalClass ℚ
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := W) 3) μ)
    [∀ P : D.support, CompactSpace (compPoints D P)]
    (c : ∀ P : D.support, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ W)) (compPoints D P) (((2 * 3 : ℕ) : ℤ) - 3))
    (hc : ∀ y : ∀ Q : D.support,
        borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D Q)) 3,
      ∑ P, ∑ Q, compPairing (isClosed_compPoints D P) (hasProperNeighbourhoodDeformations_compPoints D P Q)
        (c P) (y Q) = 0)
    (P : D.support) :
    borelMooreHomology.dualityMap ℚ (isClosed_compPoints D P)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support) μ 3
      (c P) = 0 := by
  classical
  haveI : IsSeparated (W ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hWqp
  haveI : AlgebraicGeometry.IsVariety ℂ (W ↘ Spec (.of ℂ)) := {}
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  -- the components `E_P`
  have hci := component_instances hdim D hsnc hprop hamp
  have hcp := component_isProjectiveMorphism_and_isSmoothScheme hdim D hsnc hprop hamp
  haveI : ∀ P : D.support,
      AlgebraicGeometry.IsProjectiveVariety ℂ (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    fun P ↦ (hci P).1
  haveI : ∀ P : D.support, SmoothOfRelativeDimension 2 (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    fun P ↦ (hci P).2.1
  haveI : ∀ P : D.support, IsIntegral P.1.idealSheaf.subscheme :=
    fun P ↦ (hci P).2.2
  haveI : ∀ P : D.support,
      CompactSpace (MMP.Analytic.Analytification.space (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))) :=
    fun P ↦ (compactSpace_and_finiteDimensional_analyticSpace (hcp P).2.1).1
  haveI : ∀ P : D.support, FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (MMP.Analytic.Analytification.space (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))
      ((0 + 1 : ℕ) : ℤ)) :=
    fun P ↦ (compactSpace_and_finiteDimensional_analyticSpace (hcp P).2.1).2 (0 + 1)
  -- the dual classes `η_Q` of the components
  have hsec := fun Q : D.support ↦ exists_globalSection_zeroScheme_eq hsm Q.1
  choose LQ hLi s hs0 hsZ he using hsec
  haveI : ∀ Q, Stacks.Ample.IsInvertibleModule W (LQ Q) := hLi
  haveI : ∀ Q, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (LQ Q) := hLi
  haveI : ∀ P : D.support, IsNormal P.1.idealSheaf.subscheme := fun P ↦
    haveI := SmoothOfRelativeDimension.smooth (n := 2) (f := P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    isNormal_of_smooth (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
  let σ : ∀ Q : D.support, W ⟶ MMP.Modules.totalSpace (Scheme.Modules.dual (LQ Q)) :=
    fun Q ↦ MMP.Modules.globalSectionMap (LQ Q) (s Q)
  haveI : ∀ Q, (σ Q).IsOver (Spec (.of ℂ)) := fun Q ↦
    MMP.Modules.isOver_globalSectionMap (LQ Q) (s Q)
  have hσp : ∀ Q, σ Q ≫ MMP.Modules.proj _ = 𝟙 W := fun Q ↦
    MMP.Modules.globalSectionMap_proj (LQ Q) (s Q)
  have hσ0 : ∀ Q, σ Q ≠ MMP.Modules.zeroSection _ := fun Q h ↦
    hs0 Q (MMP.Modules.eq_zero_of_globalSectionMap_eq_zeroSection (LQ Q) (s Q) h)
  have hσ : ∀ Q, MMP.Modules.zeroLocus _ (σ Q) = Q.1.idealSheaf := fun Q ↦
    (MMP.Modules.zeroLocus_globalSectionMap (LQ Q) (s Q)).trans (hsZ Q)
  let η : ∀ Q : D.support, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ W)) (compPoints D Q) 2 := fun Q ↦
    localizedClass (σ Q) Q.1.idealSheaf (hσ Q)
  -- the fundamental classes `[E_P]`
  have hfund := fun P : D.support ↦ existsUnique_isVarietyFundamentalClass (R := ℚ)
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := P.1.idealSheaf.subscheme) 2)
  choose μE hμE _ using hfund
  let a : ∀ P : D.support, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (compPoints D P)) 4 := fun P ↦
    (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ((subschemePointsHomeomorph P.1.idealSheaf : _ ≃ₜ _) :
        C(UnderlyingSpace ℂ P.1.idealSheaf.subscheme,
          UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W))))
      (subschemePointsHomeomorph P.1.idealSheaf).isProperMap (2 * 2 : ℕ)).hom (μE P)
  have hη : ∀ Q : D.support, capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ W))
      (isClosed_compPoints D Q)
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W Q.1.idealSheaf.support) 2
      ((2 * 3 : ℕ) : ℤ) (η Q) μ = congrDegree ℚ _ (by norm_num) (a Q) := fun Q ↦
    capProductSupport_localizedClass (k := 2)
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := W) 3) hμ Q.1.idealSheaf
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Q.1.idealSheaf.subscheme) 2)
      (hμE Q) (σ Q) (hσp Q) (hσ0 Q) (hσ Q)
  -- Poincaré duality on the components
  let ιV : ∀ P : D.support, H1Q P.1.idealSheaf.subscheme →ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D P)) univ 1 := fun P ↦
    (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (compAn P.1.idealSheaf) univ 1).hom
  have hPD : ∀ P (y : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (compPoints D P)) (4 - 1)),
      ∃ x, y = capProduct ℚ (TopCat.of (compPoints D P)) univ 1 4 (ιV P x) (a P) := fun P y ↦
    exists_capProduct_pullback_eq (Y := TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme))
      (A := TopCat.of (compPoints D P))
      (Y' := MMP.Analytic.Analytification.space (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))
      (subschemePointsHomeomorph P.1.idealSheaf)
      MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm (μE P)
      (bijective_capProduct_univ_of_isVarietyFundamentalClass (hμE P) 1).2 y
  -- the multiplicities
  let m : D.support → ℚ := fun P ↦ (D.coeff P.1 : ℚ)
  have hm : ∀ P, 0 < m P := fun P ↦ by
    have h1 : D.coeff P.1 ≠ 0 := Finsupp.mem_support_iff.1 P.2
    show (0 : ℚ) < (D.coeff P.1 : ℚ)
    exact_mod_cast lt_of_le_of_ne (hD P.1) (Ne.symm h1)
  have hABd : ∀ P Q : D.support, HasProperNeighbourhoodDeformations (compPoints D P ∩ compPoints D Q) :=
    fun P Q ↦ UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W
      (P.1.idealSheaf.support ⊓ Q.1.idealSheaf.support)
  have key := capProductSupport_eq_zero_of_tauPair (compPoints D) (isClosed_compPoints D)
    (fun P ↦ UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support)
    hABd (fun P Q ↦ hasProperNeighbourhoodDeformations_compPoints D Q P) μ a η hη
    (fun P ↦ H1Q P.1.idealSheaf.subscheme) ιV hPD m hm _ (fun _ _ ↦ rfl) ?hrad c hc P
  · simp only [borelMooreHomology.dualityMap, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [key, map_zero]
  case hrad =>
    intro x hx
    haveI : ∀ P : D.support, CompactSpace P.1.idealSheaf.subscheme := fun P ↦ by
      haveI := (hcp P).1
      exact QuasiCompact.compactSpace_of_compactSpace (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ))
    -- the double curves, each oriented from the smaller component to the larger
    letI : Fintype {η : W // MMP.Fourfold.IsDoubleCurve D η} :=
      (MMP.Fourfold.finite_doubleCurve hsnc hdim (D := D)).fintype
    let e := Fintype.equivFin D.support
    have hpq : ∀ k : {η : W // MMP.Fourfold.IsDoubleCurve D η}, ∃ P Q : D.support, P ≠ Q ∧
        MMP.Fourfold.comps D k.1 = {P, Q} ∧ e P < e Q := by
      intro k
      obtain ⟨A, B, hAB, hAB'⟩ :=
        Finset.card_eq_two.1 (MMP.Fourfold.IsDoubleCurve.card_comps hsnc hdim k.2)
      rcases lt_or_gt_of_ne (e.injective.ne hAB) with h | h
      · exact ⟨A, B, hAB, hAB', h⟩
      · exact ⟨B, A, hAB.symm, by rw [hAB', Finset.pair_comm], h⟩
    choose p q hpqne hcomps hlt using hpq
    have hpm : ∀ k, p k ∈ MMP.Fourfold.comps D k.1 := fun k ↦ by rw [hcomps]; simp
    have hqm : ∀ k, q k ∈ MMP.Fourfold.comps D k.1 := fun k ↦ by rw [hcomps]; simp
    let Cd := fun k : {η : W // MMP.Fourfold.IsDoubleCurve D η} ↦
      MMP.Fourfold.curveDiv hsnc hdim (p k) k.2 (hpm k)
    have hcurve := fun k ↦ curve_instances hdim D hsnc hprop hamp (p k) k.2 (hpm k)
    haveI : ∀ k, AlgebraicGeometry.IsProjectiveVariety ℂ
        ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun k ↦ (hcurve k).2.2.1
    haveI : ∀ k, SmoothOfRelativeDimension 1 ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
      fun k ↦ (hcurve k).2.2.2.1
    haveI : ∀ k, CompactSpace (MMP.Analytic.Analytification.space
        ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ))) :=
      fun k ↦ (compactSpace_and_finiteDimensional_analyticSpace (hcurve k).2.1).1
    haveI : ∀ k, FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (MMP.Analytic.Analytification.space ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)))
        ((0 + 1 : ℕ) : ℤ)) :=
      fun k ↦ (compactSpace_and_finiteDimensional_analyticSpace (hcurve k).2.1).2 (0 + 1)
    -- the inclusions of the curves into the two components through them
    let g := fun k ↦ (Cd k).idealSheaf.subschemeι
    let g' := fun k ↦ curveDivToComp hsnc hdim (p k) k.2 (hpm k) (hqm k)
    -- the cycles of the components and of the curves on their analytic spaces
    let ψ := fun P : D.support ↦ ((subschemePointsHomeomorph P.1.idealSheaf).symm.trans
      MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm :
        compPoints D P ≃ₜ MMP.Analytic.Analytification.space
          (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))
    choose z hz hzc using fun P : D.support ↦ exists_finite_cycle 3
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ P : C(compPoints D P,
          MMP.Analytic.Analytification.space (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))))
        (ψ P).isProperMap 4).hom (a P))
    haveI : ∀ k, IsIntegral (Cd k).idealSheaf.subscheme := fun k ↦ (Cd k).integral
    choose μC hμC _ using fun k ↦ existsUnique_isVarietyFundamentalClass (R := ℚ)
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := (Cd k).idealSheaf.subscheme) 1)
    choose w hw hwc using fun k ↦ exists_finite_cycle 1
      ((pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
          (X := (Cd k).idealSheaf.subscheme)).symm :
          C(UnderlyingSpace ℂ (Cd k).idealSheaf.subscheme, MMP.Analytic.Analytification.space
            ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)))))
        (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
          (X := (Cd k).idealSheaf.subscheme)).symm.isProperMap (2 * 1 : ℕ)).hom (μC k))
    -- the ample line bundles
    let L := fun P : D.support ↦
      (Scheme.Modules.pullback P.1.idealSheaf.subschemeι).obj (-D).divisorialSheaf
    have hL : ∀ P, MMP.Intersection.IsAmple ℂ (L P) := fun P ↦ by
      haveI := (hcp P).1
      exact intersectionIsAmple_of_isAmple _ (hamp P.1 P.2)
    let N := fun k ↦ (Scheme.Modules.pullback (g k)).obj (L (p k))
    have hN : ∀ k, MMP.Intersection.IsAmple ℂ (N k) := fun k ↦ by
      haveI := (hcurve k).1
      exact intersectionIsAmple_of_isAmple _ (hcurve k).2.2.2.2.2
    have hLd : ∀ P, ∃ d : ℝ, 0 < d ∧ intCycle 3 (z P) (hz P) (MMP.cupNatUniv ℂ _ 2 2
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (MMP.Analytic.algebraicFirstChernClass (L P)))
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (MMP.Analytic.algebraicFirstChernClass (L P)))) = d := fun P ↦ by
      haveI : CompactSpace (UnderlyingSpace ℂ P.1.idealSheaf.subscheme) :=
        (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
          (X := P.1.idealSheaf.subscheme)).compactSpace
      have hpos := kron_cup_algebraicFirstChernClass_pos
        (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := P.1.idealSheaf.subscheme) 2)
        (hμE P) (L P) (hamp P.1 P.2)
      refine ⟨_, Rat.cast_pos.2 hpos, ?_⟩
      have hc : MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (MMP.Analytic.algebraicFirstChernClass (L P)) =
          MMP.Analytic.singularCohomology.mapCoeff (algebraMap ℚ ℂ) 2
            (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (MMP.Analytic.algebraicFirstChernClass (L P))) := by
        rw [mapCoeff_mapCoeff, show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ
          from RingHom.ext_int _ _]
      rw [hc, ← mapCoeff_cupNatUniv]
      refine (intCycle_mapCoeff_rat 3 (z P) (hz P) _).trans ?_
      have hmap : TopCat.ofHom ((subschemePointsHomeomorph P.1.idealSheaf : _ ≃ₜ _) :
            C(UnderlyingSpace ℂ P.1.idealSheaf.subscheme,
              UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W))) ≫
          TopCat.ofHom (ψ P : C(compPoints D P, MMP.Analytic.Analytification.space
            (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)))) =
          TopCat.ofHom ((MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := P.1.idealSheaf.subscheme)).symm : C(_, _)) :=
        ConcreteCategory.hom_ext _ _ fun y ↦ by
          change MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.symm
            ((subschemePointsHomeomorph P.1.idealSheaf).symm
              (subschemePointsHomeomorph P.1.idealSheaf y)) = _
          rw [Homeomorph.symm_apply_apply]
          rfl
      have hpush := (pushforward_comp_apply' ℚ _ _
        (subschemePointsHomeomorph P.1.idealSheaf).isProperMap (ψ P).isProperMap
        ((2 * 2 : ℕ) : ℤ) (μE P)).symm.trans
        (congrArg (fun f ↦ ModuleCat.Hom.hom f (μE P)) (pushforward_congr (R := ℚ) hmap _
          (MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace
            (X := P.1.idealSheaf.subscheme)).symm.isProperMap ((2 * 2 : ℕ) : ℤ)))
      rw [hzc P]
      refine (congrArg (fun t ↦ ((kron _ (3 + 1) _ t : ℚ) : ℂ)) hpush).trans ?_
      push_cast
      rfl
    have hNd : ∀ k, ∃ d : ℝ, 0 < d ∧ intCycle 1 (w k) (hw k)
        (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (MMP.Analytic.algebraicFirstChernClass (N k))) = d := fun k ↦ by
      haveI := (Cd k).integral
      haveI := (hcurve k).1
      have hdim1 := (hcurve k).2.2.2.2.1
      have hpos : 0 < AlgebraicGeometry.invertibleCurveDegree ℂ
          ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)) hdim1.le (N k) := by
        haveI : IsProper (g k ≫ ((p k).1.idealSheaf.subscheme ↘ Spec (.of ℂ))) := (hcurve k).1
        exact MMP.Fourfold.degreeOn_pos_of_isAmple ((p k).1.idealSheaf.subscheme ↘ Spec (.of ℂ))
          (g k) hdim1 (L (p k)) (hamp (p k).1 (p k).2)
      refine ⟨(AlgebraicGeometry.invertibleCurveDegree ℂ
          ((Cd k).idealSheaf.subscheme ↘ Spec (.of ℂ)) hdim1.le (N k) : ℝ),
        by exact_mod_cast hpos, ?_⟩
      have hc : MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (MMP.Analytic.algebraicFirstChernClass (N k)) =
          MMP.Analytic.singularCohomology.mapCoeff (algebraMap ℚ ℂ) (1 + 1)
            (MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (MMP.Analytic.algebraicFirstChernClass (N k))) := by
        rw [mapCoeff_mapCoeff, show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ
          from RingHom.ext_int _ _]
      rw [hc, intCycle_mapCoeff_rat, hwc k,
        kron_algebraicFirstChernClass_eq (MMP.Fourfold.isSmoothScheme_curveDiv hsnc hdim (p k) k.2
          (hpm k)) hdim1 (hcurve k).2.2.1 (N k) _ (hμC k)]
      push_cast
      rfl
    -- the curves over the double curves through two given components
    have hcPQ := fun (P Q : D.support) (k : DoubleCurveThrough D P Q) ↦
      curve_instances hdim D hsnc hprop hamp P k.1.2 k.2.1
    haveI : ∀ (P Q : D.support) (k : DoubleCurveThrough D P Q), IsIntegral
        (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme := fun P _ k ↦
      (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).integral
    haveI : ∀ (P Q : D.support) (k : DoubleCurveThrough D P Q),
        CompactSpace (MMP.Analytic.Analytification.space
          ((MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme ↘ Spec (.of ℂ))) :=
      fun P Q k ↦ (compactSpace_and_finiteDimensional_analyticSpace (hcPQ P Q k).2.1).1
    have hkPQ : ∀ (P Q : D.support) (k : DoubleCurveThrough D P Q), ((1 : ℕ) : WithBot ℕ∞) =
        topologicalKrullDim (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme :=
      fun P Q k ↦
        haveI := (hcPQ P Q k).2.2.1
        haveI := (hcPQ P Q k).2.2.2.1
        natCast_eq_dimension_of_isVariety (K := ℂ)
          (MMP.Fourfold.curveDiv hsnc hdim P k.1.2 k.2.1).idealSheaf.subscheme 1
    choose μC' hμC' _ using fun P Q k ↦
      existsUnique_isVarietyFundamentalClass (R := ℚ) (hkPQ P Q k)
    -- for `e P < e Q`, the double curves through `P` and `Q` are those running from `P` to `Q`
    have hthrough : ∀ {P Q : D.support}, e P < e Q → ∀ k,
        P ∈ MMP.Fourfold.comps D k.1 ∧ Q ∈ MMP.Fourfold.comps D k.1 ↔ p k = P ∧ q k = Q :=
      fun hlt' k ↦ ⟨fun h ↦ eq_and_eq_of_mem_pair e (hlt k) (hcomps k ▸ h.1) (hcomps k ▸ h.2) hlt',
        mem_and_mem_of_eq_pair (hcomps k)⟩
    have hnone : ∀ {P Q : D.support}, e P < e Q →
        (Finset.univ.filter fun k ↦ p k = Q ∧ q k = P) = ∅ := fun hlt' ↦
      Finset.filter_false_of_mem fun k _ hk ↦ by
        have h := hlt k
        rw [hk.1, hk.2] at h
        exact lt_asymm hlt' h
    -- the forms
    let τ := fun P Q : D.support ↦
      (tauForm (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P) (η Q) (a P)).compl₁₂ (ιV P) (ιV Q)
    let τ' := fun P Q : D.support ↦
      (tauForm' (isClosed_compPoints D P) (isClosed_compPoints D Q)
        (hasProperNeighbourhoodDeformations_compPoints D Q P) (η Q) (a P)).compl₁₂ (ιV P) (ιV P)
    have hττ' : ∀ P, τ' P P = τ P P := fun P ↦ by
      simp only [τ, τ']
      rw [tauForm'_self]
    refine eq_zero_of_hodgeRadical (fun P : D.support ↦ P.1.idealSheaf.subscheme)
      (fun k ↦ (Cd k).idealSheaf.subscheme) p q hpqne g (fun _ ↦ rfl) g'
      (fun k ↦ curveDivToComp_comp_over hsnc hdim (p k) k.2 (hpm k) (hqm k)) z hz w hw L hL hLd
      N hN hNd m hm (fun _ ↦ 1) (fun _ ↦ zero_le_one) τ τ' hττ' ?hG4 ?hG3 ?hG3' x hx
    case hG4 =>
      intro P y y'
      have h4 := sum_toCohomology_pullback_localizedClass hsm D hD LQ σ hσp hσ (fun Q ↦ (he Q).some) P
      rw [show cycleClass 3 (z P) (hz P) = _ from hzc P]
      exact sum_tauForm'_eq_kron (compPoints D) (isClosed_compPoints D)
        (fun P Q ↦ hasProperNeighbourhoodDeformations_compPoints D Q P) η P (a P) m (ψ P) _
        (h4.trans (map_neg _ _).symm) y y'
    case hG3 =>
      intro x y P Q hPQ
      simp only [τ, ιV, LinearMap.compl₁₂_apply]
      rcases lt_or_gt_of_ne (e.injective.ne hPQ) with hlt' | hlt'
      · -- the double curves run from `P` to `Q`
        rw [hnone hlt', Finset.sum_empty, sub_zero]
        refine (tauForm_compAn_eq_sum hsnc hdim P Q (Ne.symm hPQ)
          (natCast_eq_dimension_of_isVariety (K := ℂ)
            (Y := P.1.idealSheaf.subscheme) 2) (hμE P) (σ Q) (hσp Q) (hσ Q) (hkPQ P Q) (μC' P Q) (hμC' P Q)
          (x P) (y Q)).trans ?_
        rw [← Finset.sum_neg_distrib]
        refine sum_subtype_eq_sum_filter (hthrough hlt') _ _ fun k h ↦ ?_
        obtain ⟨rfl, rfl⟩ := (hthrough hlt' k).1 h
        rw [one_mul, (hμC' _ _ ⟨k, h⟩).eq (hμC k), ← hwc k]
      · -- the double curves run from `Q` to `P`
        rw [hnone hlt', Finset.sum_empty, neg_zero, zero_sub]
        refine (tauForm_compAn_eq_sum_swap hsnc hdim P Q hPQ
          (natCast_eq_dimension_of_isVariety (K := ℂ)
            (Y := Q.1.idealSheaf.subscheme) 2) (hμE Q) (σ P) (hσp P) (hσ P) (σ Q) (hσ Q) μ (a P) (hη P)
          (hη Q) (hkPQ Q P) (μC' Q P) (hμC' Q P) (x P) (y Q)).trans ?_
        rw [← Finset.sum_neg_distrib]
        refine sum_subtype_eq_sum_filter (hthrough hlt') _ _ fun k h ↦ ?_
        obtain ⟨rfl, rfl⟩ := (hthrough hlt' k).1 h
        rw [one_mul, (hμC' _ _ ⟨k, h⟩).eq (hμC k), ← hwc k]
    case hG3' =>
      intro x y P Q hPQ
      simp only [τ', ιV, LinearMap.compl₁₂_apply]
      rcases lt_or_gt_of_ne (e.injective.ne hPQ) with hlt' | hlt'
      · -- the double curves run from `P` to `Q`
        rw [hnone hlt', Finset.sum_empty, sub_zero]
        refine (tauForm'_compAn_eq_sum hsnc hdim P Q (Ne.symm hPQ)
          (natCast_eq_dimension_of_isVariety (K := ℂ)
            (Y := P.1.idealSheaf.subscheme) 2) (hμE P) (σ Q) (hσp Q) (hσ Q) (hkPQ P Q) (μC' P Q) (hμC' P Q)
          (x P) (y P)).trans ?_
        rw [← Finset.sum_neg_distrib]
        refine sum_subtype_eq_sum_filter (hthrough hlt') _ _ fun k h ↦ ?_
        obtain ⟨rfl, rfl⟩ := (hthrough hlt' k).1 h
        rw [one_mul, (hμC' _ _ ⟨k, h⟩).eq (hμC k), ← hwc k]
      · -- the double curves run from `Q` to `P`
        rw [hnone hlt', Finset.sum_empty, neg_zero, zero_sub]
        refine (tauForm'_compAn_eq_sum_swap hsnc hdim P Q hPQ
          (natCast_eq_dimension_of_isVariety (K := ℂ)
            (Y := Q.1.idealSheaf.subscheme) 2) (hμE Q) (σ P) (hσp P) (hσ P) (σ Q) (hσ Q) μ (a P) (hη P)
          (hη Q) (hkPQ Q P) (μC' Q P) (hμC' Q P) (x P) (y P)).trans ?_
        rw [← Finset.sum_neg_distrib]
        refine sum_subtype_eq_sum_filter (hthrough hlt') _ _ fun k h ↦ ?_
        obtain ⟨rfl, rfl⟩ := (hthrough hlt' k).1 h
        rw [one_mul, (hμC' _ _ ⟨k, h⟩).eq (hμC k), ← hwc k]

end Core

private theorem solution {W S : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsNormal S]
    [IsIntegral W] [IsIntegral S]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3)
    (hSqp : Stacks.HProjective.IsQuasiProjective (S ↘ Spec (.of ℂ)))
    (f : W ⟶ S) [f.IsOver (Spec (.of ℂ))] (hf : IsProjectiveMorphism f)
    (x : S) (hx : IsClosed {x})
    (hiso : IsIso (f ∣_ ⟨{x}ᶜ, hx.isOpen_compl⟩))
    (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hfibre : (D.supp : Set W) = f.base ⁻¹' {x})
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : IsRelativelyAmple f (-D).divisorialSheaf) :
    Function.Bijective
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W))
          (Set.range (UnderlyingSpace.map (K := ℂ) D.suppIdeal.subschemeι)) 3 ≫
        rationalCohomologyMap
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) D.suppIdeal.subschemeι)) 3).hom := by
  classical
  set ι := D.suppIdeal.subschemeι
  haveI : IsSeparated (W ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hWqp
  haveI : SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_of_isSmoothScheme hsm hdim
  have hqp : IsQuasiProjectiveVariety ℂ (W ↘ Spec (.of ℂ)) := isQuasiProjectiveVariety hWqp
  have hprop : IsProper (D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ))) :=
    isProper_suppIdeal_subschemeι hSqp hf x hx D hfibre
  obtain ⟨μ, hμ, -⟩ := existsUnique_isVarietyFundamentalClass (R := ℚ)
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := W) 3)
  have hSD := MMP.Analytic.supportedDuality_of_isQuasiProjectiveVariety hqp
    (pointCycleClass_genericPoint_eq _ _ hμ) D.supp hprop
  have hEc : Set.range (UnderlyingSpace.map (K := ℂ) ι) = UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) := by
    rw [UnderlyingSpace.range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      DivisorWithCoeffs.suppIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IsProper (D.suppScheme ↘ Spec (.of ℂ)) := hprop
  haveI := compactSpace_underlyingSpace_of_isProper (Z := D.suppScheme)
  haveI : CompactSpace (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W)) := by
    rw [← hEc]
    exact isCompact_iff_compactSpace.mp (isCompact_range (UnderlyingSpace.map ι).continuous)
  -- the components `E_P` of `E`
  have hX : IsClosed (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W))) := UnderlyingSpace.isClosed_pointsOver D.supp.isClosed
  haveI := compactSpace_preimage_subsetInclusion (M := TopCat.of (UnderlyingSpace ℂ W))
    (A := (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W)))) (B := (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W)))) hX
  let A : D.support → Set (TopCat.of (UnderlyingSpace ℂ W)) := fun P ↦
    UnderlyingSpace.pointsOver (K := ℂ) (P.1.idealSheaf.support : Set W)
  have hA : ∀ P, IsClosed (A P) := fun P ↦
    UnderlyingSpace.isClosed_pointsOver P.1.idealSheaf.support.isClosed
  have hAX : ∀ P, A P ⊆ (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W))) := fun P ↦ UnderlyingSpace.pointsOver_mono
    (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 P.2))
  haveI : ∀ P, CompactSpace (A P) := fun P ↦
    isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2 ‹CompactSpace (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W)))›).of_isClosed_subset
      (hA P) (hAX P))
  have hpropP : ∀ P : D.support, IsProper ((Scheme.IdealSheafData.vanishingIdeal
      P.1.idealSheaf.support).subschemeι ≫ (W ↘ Spec (.of ℂ))) := fun P ↦
    isProper_vanishingIdeal_subschemeι_of_le
      (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 P.2)) hprop
  have hSDP := fun P : D.support ↦
    MMP.Analytic.supportedDuality_of_isQuasiProjectiveVariety hqp
      (pointCycleClass_genericPoint_eq _ _ hμ) P.1.idealSheaf.support
      (hpropP P)
  have hk : ((3 : ℕ) : ℤ) = ((2 * 3 : ℕ) : ℤ) - (3 : ℤ) := by norm_num
  have hδX : Function.Bijective (@borelMooreHomology.dualityMap ℚ _
      (TopCat.of (UnderlyingSpace ℂ W)) (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W))) (2 * 3) hX
      (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W D.supp) μ 3) := hSD.1 3
  have hAd : ∀ P : D.support, HasProperNeighbourhoodDeformations (A P) := fun P ↦
    UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W P.1.idealSheaf.support
  have hδA : ∀ P : D.support, Function.Surjective (@borelMooreHomology.dualityMap ℚ _
      (TopCat.of (UnderlyingSpace ℂ W)) (A P) (2 * 3) (hA P) (hAd P) μ 3) := fun P ↦ ((hSDP P).1 3).2
  have hnat : ∀ (P : D.support) c, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (borelMooreHomology.subsetInclusionOfSubset (hAX P))
      (borelMooreHomology.isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) 3).hom
        (@borelMooreHomology.dualityMap ℚ _ (TopCat.of (UnderlyingSpace ℂ W)) (A P) (2 * 3) (hA P)
          (hAd P) μ 3 c) =
      @borelMooreHomology.dualityMap ℚ _ (TopCat.of (UnderlyingSpace ℂ W)) (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W))) (2 * 3) hX
        (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W D.supp) μ 3
        ((cohomologyWithSupports.forget ℚ _ _ (hAX P) _).hom c) := fun P c ↦
    (hSDP P).2.1 D.supp (DivisorWithCoeffs.support_subset_supp
      (Finsupp.mem_support_iff.1 P.2)) 3 c
  -- the inclusions `j_P : E_P → E` and the decomposition of `H₃ E`
  have hker : ∀ P : D.support,
      D.suppIdeal.subschemeι.ker ≤ P.1.idealSheaf.subschemeι.ker := fun P ↦ by
    haveI := P.1.integral
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    intro w hw
    have hw' : w ∈ closure (Set.range P.1.idealSheaf.subschemeι) := hw
    rw [Scheme.IdealSheafData.range_subschemeι, P.1.idealSheaf.support.isClosed.closure_eq] at hw'
    exact DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 P.2) hw'
  let j : ∀ P : D.support, P.1.idealSheaf.subscheme ⟶ D.suppScheme := fun P ↦
    IsClosedImmersion.lift D.suppIdeal.subschemeι P.1.idealSheaf.subschemeι (hker P)
  have hj : ∀ P, j P ≫ D.suppIdeal.subschemeι = P.1.idealSheaf.subschemeι := fun P ↦
    IsClosedImmersion.lift_fac _ _ _
  haveI : ∀ P, (j P).IsOver (Spec (.of ℂ)) := fun P ↦ ⟨by
    change j P ≫ D.suppIdeal.subschemeι ≫ (W ↘ Spec (.of ℂ)) =
      P.1.idealSheaf.subschemeι ≫ (W ↘ Spec (.of ℂ))
    rw [← Category.assoc, hj]⟩
  haveI : ∀ P, IsClosedImmersion (j P) := fun P ↦ by
    haveI : IsClosedImmersion (j P ≫ D.suppIdeal.subschemeι) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp (j P) D.suppIdeal.subschemeι
  haveI : ∀ P, IsProper (j P) := fun P ↦ inferInstance
  have hamp : ∀ P ∈ D.support, Stacks.Ample.IsAmple P.idealSheaf.subscheme
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj (-D).divisorialSheaf) := fun P hP ↦
    isAmple_pullback_subschemeι_of_isRelativelyAmple _ hample x P.idealSheaf fun w hw ↦ by
      rw [← hfibre]
      exact DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hP) hw
  have hfib := bijective_sum_pushforward_rationalHomology_three hsm hdim D hD hsnc hprop hamp j hj
  have hEcP : ∀ P : D.support,
      Set.range (UnderlyingSpace.map (K := ℂ) P.1.idealSheaf.subschemeι) = A P := fun P ↦ by
    rw [UnderlyingSpace.range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι]
  let φ := (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion ι).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hEc)
  let φP := fun P : D.support ↦ (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion
    P.1.idealSheaf.subschemeι).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (hEcP P))
  have hsum := exists_sum_pushforward_eq_of_homeomorph (M := TopCat.of (UnderlyingSpace ℂ W))
    (E := TopCat.of (UnderlyingSpace ℂ D.suppScheme))
    (EP := fun P : D.support ↦ TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) hA hAX φ φP
    (fun P ↦ TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (j P)))
    (fun P ↦ UnderlyingSpace.isProperMap_map (K := ℂ) (j P))
    (fun P z ↦ by
      change UnderlyingSpace.map (K := ℂ) P.1.idealSheaf.subschemeι z =
        UnderlyingSpace.map (K := ℂ) ι (UnderlyingSpace.map (K := ℂ) (j P) z)
      refine UnderlyingSpace.ext ?_
      rw [UnderlyingSpace.toHom_map, UnderlyingSpace.toHom_map, UnderlyingSpace.toHom_map,
        Category.assoc, hj P]) 3
    (fun b ↦ by
      obtain ⟨y, hy⟩ := hfib.2 b
      exact ⟨y, by simpa using hy⟩)
  have hrc := @radical_of_components (TopCat.of (UnderlyingSpace ℂ W)) (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) : Set (TopCat.of (UnderlyingSpace ℂ W))) _ _ hX
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W D.supp)
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_pointsOver W D.supp D.supp) μ
    hk hδX D.support _ A _ hA hAX hAd
    (fun P Q ↦ UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_pointsOver W
      Q.1.idealSheaf.support P.1.idealSheaf.support)
    hδA hnat
  -- `H₃ E` is finite dimensional
  haveI : ∀ P : D.support, IsProper (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun P ↦ by
    rw [← CategoryTheory.comp_over (j P) (Spec (.of ℂ))]
    infer_instance
  have hprojP : ∀ P : D.support, IsProjectiveMorphism (P.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    fun P ↦ Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isProjectiveMorphism_of_isAmple _ _
      (hamp P.1 P.2)
  haveI : ∀ P : D.support, FiniteDimensional ℚ
      (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) 3) := fun P ↦ by
    haveI hfd : FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) 3) :=
      finiteDimensional_borelMooreHomology_of_isProjectiveMorphism (hprojP P) 3
    have hb := MMP.borelMooreHomology.bijective_pushforward_homeomorph ℚ
      (Y := TopCat.of (UnderlyingSpace ℂ P.1.idealSheaf.subscheme)) (Y' := TopCat.of (A P))
      (φP P) 3
    exact Module.Finite.of_surjective _ hb.2
  have hfin : FiniteDimensional ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W))) 3) := by
    refine Module.Finite.of_surjective (∑ P : D.support,
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (borelMooreHomology.subsetInclusionOfSubset (hAX P))
        (borelMooreHomology.isProperMap_subsetInclusionOfSubset (hA P) (hAX P)) 3).hom ∘ₗ
      LinearMap.proj (R := ℚ)
        (φ := fun P : D.support ↦ borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (A P)) 3) P)
      fun b ↦ ?_
    obtain ⟨x, hx⟩ := hsum b
    exact ⟨x, by simpa using hx⟩
  rw [hEc]
  refine bijective_of_radical (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ι))
    (UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion ι).isEmbedding hEc
    (UnderlyingSpace.isClosed_pointsOver D.supp.isClosed)
    (UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver W D.supp)
    μ (by norm_num) (hSD.1 3) hfin fun v hv ↦ hrc hsum (fun c hc ↦ ?_) v hv
  have hc0 : ∀ P, c P = 0 := fun P ↦ ((hSDP P).1 3).1 ((dualityMap_eq_zero_of_forall_compPairing
    hsm hdim hWqp D hD hsnc hprop hamp hμ c hc P).trans (map_zero _).symm)
  simp [hc0]

end MMP.Fold06.ThmMmpConductorThreefoldLocalOddForm

open CategoryTheory AlgebraicGeometry MMP
open scoped MMP.SubschemeOver

namespace MMP.Fourfold

open MMP.Mori

/-- **The local odd intersection form at an isolated threefold point.** Let `f : W ⟶ S` be a
projective morphism of quasi-projective complex varieties of dimension three, with `W` smooth and
`S` normal, which is an isomorphism over `S ∖ {x}` for a closed point `x`. Let `D` be an effective
snc divisor on `W` with `-D` ample relative to `f` and whose support `E` is the fibre `f⁻¹ {x}`.
Then the natural map `H³_E(W(ℂ), ℚ) → H³(E(ℂ), ℚ)`, forgetting supports and restricting to
`E(ℂ)`, is bijective. -/
@[mmp "thm_mmp_conductor_threefold_local_odd_form"]
public theorem bijective_toCohomology_comp_rationalCohomologyMap_three {W S : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]
    [IsComplexScheme W] [IsLocallyNoetherian W] [IsNormal W] [IsNormal S]
    [IsIntegral W] [IsIntegral S]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3)
    (hSqp : Stacks.HProjective.IsQuasiProjective (S ↘ Spec (.of ℂ)))
    (f : W ⟶ S) [f.IsOver (Spec (.of ℂ))] (hf : IsProjectiveMorphism f)
    (x : S) (hx : IsClosed {x})
    (hiso : IsIso (f ∣_ ⟨{x}ᶜ, hx.isOpen_compl⟩))
    (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hfibre : (D.supp : Set W) = f.base ⁻¹' {x})
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : IsRelativelyAmple f (-D).divisorialSheaf) :
    Function.Bijective
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ W))
          (Set.range (UnderlyingSpace.map (K := ℂ) D.suppIdeal.subschemeι)) 3 ≫
        rationalCohomologyMap
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) D.suppIdeal.subschemeι)) 3).hom :=
  MMP.Fold06.ThmMmpConductorThreefoldLocalOddForm.solution hsm hdim hWqp hSdim hSqp f hf x hx hiso D hD hsnc hfibre hample

end MMP.Fourfold
