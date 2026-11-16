module

public import MMP.Analysis.Complex.HolomorphicCompactConvergence
import MMP.Analysis.Complex.CauchyTransformRungeMontel

/-!
# Density of restriction maps of holomorphic functions (Runge)

Let `D ⊆ ℂⁿ` be open and `W' ⊆ W ⊆ D` open. Suppose every nonempty compact subset of `W'` lies in a
block `∏ᵢ [aᵢ, bᵢ] × [cᵢ, dᵢ]` (with `aᵢ < bᵢ`, `cᵢ < dᵢ`) contained in `W'`; this holds for every
open box `W'`. Then the restriction `𝒪_D(W) → 𝒪_D(W')` has dense range for the topology of compact
convergence: by Runge's theorem a function holomorphic near a block is a uniform limit of
polynomials on it, and polynomials are holomorphic on `W`.

## Main results

* `MMP.Analytic.denseRange_holomorphic_restrict`: the density statement above.
* `MMP.Analytic.exists_block_of_isCompact_subset_box`: a nonempty compact subset of an open box
  lies in a nondegenerate closed block inside the box.

## References

* [Grauert–Remmert, *Coherent analytic sheaves*]
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Set
open scoped Manifold ContDiff

namespace MMP.Analytic

variable {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}

/-- A function complex differentiable near a nondegenerate block of `ℂⁿ` is uniformly approximated
on the block by entire functions (Runge). -/
theorem exists_differentiable_approx_on_block {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsOpen S)
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f S) {a b c d : Fin n → ℝ}
    (hab : ∀ i, a i < b i) (hcd : ∀ i, c i < d i)
    (hB : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)} ⊆ S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : EuclideanSpace ℂ (Fin n) → ℂ, Differentiable ℂ p ∧
      ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)},
        ‖f z - p z‖ < ε := by
  set e := EuclideanSpace.equiv (Fin n) ℂ
  let K : Fin n → Set ℂ := fun j => Complex.re ⁻¹' Icc (a j) (b j) ∩ Complex.im ⁻¹' Icc (c j) (d j)
  have hKS : univ.pi K ⊆ e.symm ⁻¹' S := fun w hw => hB fun i => hw i (mem_univ i)
  obtain ⟨s, cf, hsβ, happ⟩ := (MMP.Gaga.cauchyTransform_runge_montel).2.1 n K ∅ 0 (by simp)
    (fun j _ => Or.inl ⟨_, _, _, _, hab j, hcd j, rfl⟩) (e.symm ⁻¹' S) (f ∘ e.symm)
    (hS.preimage e.symm.continuous) hKS (hf.comp e.symm.differentiableOn (fun _ h => h)) ε hε
  let P : (Fin n → ℂ) → ℂ := fun w => ∑ β ∈ s, cf β * ∏ j, (w j - (0 : Fin n → ℂ) j) ^ β j
  have hP : Differentiable ℂ P := by
    classical
    refine Differentiable.fun_sum fun β hβ => (differentiable_const _).mul fun w => ?_
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℂ (fun w : Fin n → ℂ => (w j - (0 : Fin n → ℂ) j) ^ β j) w := fun j _ =>
      (((differentiable_apply j).sub_const _).zpow
        (Or.inr (hsβ β hβ j (notMem_empty j)))) w
    exact (HasFDerivAt.finsetProd fun j hj' => (hj j hj').hasFDerivAt).differentiableAt
  refine ⟨P ∘ e, hP.comp e.differentiable, fun z hz => ?_⟩
  simpa [P, e] using happ (e z) fun i _ => hz i

/-- A real function continuous on a nonempty compact set and mapping it into `(a, b)` maps it
into a nondegenerate closed subinterval `[a', b'] ⊆ (a, b)`. -/
theorem exists_Icc_of_isCompact_mapsTo_Ioo {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (hKne : K.Nonempty) {g : α → ℝ} (hg : ContinuousOn g K) {a b : ℝ}
    (hKab : ∀ z ∈ K, g z ∈ Ioo a b) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ ∀ z ∈ K, g z ∈ Icc a' b' := by
  obtain ⟨z₁, hz₁, hmin⟩ := hK.exists_isMinOn hKne hg
  obtain ⟨z₂, hz₂, hmax⟩ := hK.exists_isMaxOn hKne hg
  have h₁ := hKab z₁ hz₁
  have h₂ := hKab z₂ hz₂
  have h₁₂ : g z₁ ≤ g z₂ := hmin hz₂
  refine ⟨(a + g z₁) / 2, (g z₂ + b) / 2, by linarith [h₁.1], by linarith [h₁.1, h₂.2],
    by linarith [h₂.2], fun z hz => ⟨?_, ?_⟩⟩
  · have : g z₁ ≤ g z := hmin hz
    linarith [h₁.1]
  · have : g z ≤ g z₂ := hmax hz
    linarith [h₂.2]

/-- A nonempty compact subset of an open box of `ℂⁿ` lies in a nondegenerate closed block inside
the box. -/
theorem exists_block_of_isCompact_subset_box {K : Set (EuclideanSpace ℂ (Fin n))}
    (hK : IsCompact K) (hKne : K.Nonempty) (a b c d : Fin n → ℝ)
    (hKB : K ⊆ {z | ∀ i, z i ∈ Ioo (a i) (b i) ×ℂ Ioo (c i) (d i)}) :
    ∃ a' b' c' d' : Fin n → ℝ, (∀ i, a' i < b' i) ∧ (∀ i, c' i < d' i) ∧
      K ⊆ {z | ∀ i, z i ∈ Icc (a' i) (b' i) ×ℂ Icc (c' i) (d' i)} ∧
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Icc (a' i) (b' i) ×ℂ Icc (c' i) (d' i)} ⊆
        {z | ∀ i, z i ∈ Ioo (a i) (b i) ×ℂ Ioo (c i) (d i)} := by
  have hre : ∀ i, ∃ a' b' : ℝ, a i < a' ∧ a' < b' ∧ b' < b i ∧
      ∀ z ∈ K, (z i).re ∈ Icc a' b' := fun i =>
    exists_Icc_of_isCompact_mapsTo_Ioo hK hKne
      (Complex.continuous_re.comp (PiLp.continuous_apply 2 _ i)).continuousOn fun z hz => (hKB hz i).1
  have him : ∀ i, ∃ c' d' : ℝ, c i < c' ∧ c' < d' ∧ d' < d i ∧
      ∀ z ∈ K, (z i).im ∈ Icc c' d' := fun i =>
    exists_Icc_of_isCompact_mapsTo_Ioo hK hKne
      (Complex.continuous_im.comp (PiLp.continuous_apply 2 _ i)).continuousOn fun z hz => (hKB hz i).2
  choose a' b' ha hab hb hKre using hre
  choose c' d' hc hcd hd hKim using him
  refine ⟨a', b', c', d', hab, hcd, fun z hz i => ⟨hKre i z hz, hKim i z hz⟩, fun z hz i => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
  exact ⟨⟨by linarith [ha i], by linarith [hb i]⟩, by linarith [hc i], by linarith [hd i]⟩

/-- **Density of restrictions (Runge).** If every nonempty compact subset of `W'` lies in a
nondegenerate block contained in `W'`, the restriction `𝒪_D(W) → 𝒪_D(W')` has dense range for the
topologies of compact convergence. -/
theorem denseRange_holomorphic_restrict {W W' : Opens (TopCat.of D)} (h : W' ≤ W)
    (hblock : ∀ K : Set (EuclideanSpace ℂ (Fin n)), IsCompact K → K.Nonempty →
      K ⊆ range (openInclusion W') →
      ∃ a b c d : Fin n → ℝ, (∀ i, a i < b i) ∧ (∀ i, c i < d i) ∧
        K ⊆ {z | ∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)} ∧
        {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Icc (a i) (b i) ×ℂ Icc (c i) (d i)} ⊆
          range (openInclusion W')) :
    @DenseRange _ (holomorphicCompactConvergence W').toTopologicalSpace _
      (𝒪[n, D].presheaf.map (homOfLE h).op).hom := by
  letI := holomorphicCompactConvergence W'
  intro f
  have hbasis := ((UniformOnFun.hasBasis_nhds_of_basis W' ℂ {K : Set W' | IsCompact K}
    (holomorphicToUniformOnFun W' f) ⟨∅, isCompact_empty⟩
    (fun K hK L hL => ⟨K ∪ L, hK.union hL, subset_union_left, subset_union_right⟩)
    Metric.uniformity_basis_dist).comap (holomorphicToUniformOnFun W'))
  rw [← nhds_induced] at hbasis
  refine (mem_closure_iff_nhds_basis hbasis).2 ?_
  rintro ⟨K, ε⟩ ⟨hK : IsCompact K, hε : 0 < ε⟩
  have hemb := isOpenEmbedding_openInclusion W'
  obtain ⟨p, hp, hpK⟩ : ∃ p : EuclideanSpace ℂ (Fin n) → ℂ, Differentiable ℂ p ∧
      ∀ x ∈ K, ‖Function.extend (openInclusion W') f 0 (openInclusion W' x) -
        p (openInclusion W' x)‖ < ε := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, differentiable_const 0, fun x hx => by simp [hKe] at hx⟩
    obtain ⟨a, b, c, d, hab, hcd, hKB, hBW⟩ := hblock _ (hK.image hemb.continuous)
      (hKne.image _) (image_subset_range _ _)
    obtain ⟨p, hp, hpB⟩ := exists_differentiable_approx_on_block hemb.isOpen_range
      ((contMDiff_iff_differentiableOn_extend W' f).1 f.2) hab hcd hBW hε
    exact ⟨p, hp, fun x hx => hpB _ (hKB (mem_image_of_mem _ hx))⟩
  have hpW : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞
      (fun w : W => p (openInclusion W w)) := by
    rw [contMDiff_iff_differentiableOn_extend]
    refine hp.differentiableOn.congr ?_
    rintro _ ⟨w, rfl⟩
    exact (isOpenEmbedding_openInclusion W).injective.extend_apply _ 0 w
  refine ⟨_, ⟨⟨fun w : W => p (openInclusion W w), hpW⟩, rfl⟩, fun x hx => ?_⟩
  have := hpK x hx
  rw [hemb.injective.extend_apply] at this
  change dist (p (openInclusion W' x)) (f x) < ε
  rwa [dist_comm, dist_eq_norm]

end MMP.Analytic
