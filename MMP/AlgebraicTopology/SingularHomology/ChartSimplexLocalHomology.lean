module

public import MMP.AlgebraicTopology.SingularHomology.LocalHomologyHomotopy
public import MMP.AlgebraicTopology.SingularHomology.OrientedSimplexPath

/-!
# The local orientation of a chart is independent of the oriented simplex

Let `e` be a chart of a space `M` with values in a real vector space `H` oriented by a basis
`b`, and let `x` be a point of the domain of `e`. For any two affine simplices `Δ`, `Δ'` of the
image of `e`, around `e x` and positively oriented for `b`, the singular simplices `e⁻¹ ∘ Δ` and
`e⁻¹ ∘ Δ'` have the same class in the local homology `H_n(M, M - x; ℤ)`. So the local
orientation of `M` at `x` defined by `e` does not depend on the simplex, and `H_n(M, M - x)`
is detected by any one of them.

Both simplices are first shrunk towards `e x` inside themselves; the shrunk simplices are then
joined by a path of oriented simplices around `e x`
(`MMP.ThomClass.joinedIn_isOrientedSimplexAroundZero`), small enough to stay in
the image of `e`. Each of these deformations is a homotopy of simplices whose boundary avoids
`e x`, so it preserves the local homology class
(`MMP.FundamentalClass.isLocallyHomologous_of_homotopy`).

## Main results

* `MMP.FundamentalClass.isLocallyHomologous_of_orientedFamily`: a continuous
  family of oriented simplices around `e x` in the image of `e` preserves the local class.
* `MMP.FundamentalClass.isLocallyHomologous_of_isOrientedSimplexAroundZero`: any
  two oriented simplices of a chart around `e x` are locally homologous at `x`.
-/

@[expose] public noncomputable section

open Set Topology Filter
open MMP.SingularChain MMP.ThomClass

namespace MMP

namespace FundamentalClass

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] {M : Type*} [TopologicalSpace M] {n : ℕ}

/-- The coordinate `1` of a point of the standard `1`-simplex lies in `[0, 1]`. -/
lemma stdSimplex_coord_mem_Icc (u : stdSimplex ℝ (Fin 2)) :
    (u : Fin 2 → ℝ) 1 ∈ Icc (0 : ℝ) 1 := by
  have hs : (u : Fin 2 → ℝ) 0 + (u : Fin 2 → ℝ) 1 = 1 := by
    have : ∑ k, (u : Fin 2 → ℝ) k = 1 := u.2.2
    rwa [Fin.sum_univ_two] at this
  have h0 : 0 ≤ (u : Fin 2 → ℝ) 0 := u.2.1 0
  exact ⟨u.2.1 1, by linarith⟩

/-- A continuous family `γ s`, `s ∈ [0, 1]`, of oriented simplices around `0`, translated to
`e x` and contained in the image of the chart `e`, preserves the local homology class at `x` of
`e⁻¹ ∘ (e x + Δ(γ s))`. -/
theorem isLocallyHomologous_of_orientedFamily (e : OpenPartialHomeomorph M H) {x : M}
    (hx : x ∈ e.source) {b : Module.Basis (Fin n) ℝ H} (γ : ℝ → Fin (n + 1) → H)
    (hγc : Continuous γ) (hγ : ∀ s ∈ Icc (0 : ℝ) 1, IsOrientedSimplexAroundZero b (γ s))
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ stdSimplex ℝ (Fin (n + 1)),
      e x + ∑ k, t k • γ s k ∈ e.target)
    {σ₀ σ₁ : Simplex M n}
    (h0 : ∀ t, σ₀ t = e.symm (e x + ∑ k, (t : Fin (n + 1) → ℝ) k • γ 0 k))
    (h1 : ∀ t, σ₁ t = e.symm (e x + ∑ k, (t : Fin (n + 1) → ℝ) k • γ 1 k)) :
    IsLocallyHomologous x σ₀ σ₁ := by
  set Γ : stdSimplex ℝ (Fin (n + 1)) × stdSimplex ℝ (Fin 2) → H := fun z ↦
    e x + ∑ k, (z.1 : Fin (n + 1) → ℝ) k • γ ((z.2 : Fin 2 → ℝ) 1) k
  have hΓc : Continuous Γ := continuous_const.add (continuous_finsetSum _ fun k _ ↦
    ((continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)).smul
      ((continuous_apply k).comp (hγc.comp ((continuous_apply 1).comp
        (continuous_subtype_val.comp continuous_snd)))))
  have hΓT : ∀ z, Γ z ∈ e.target := fun z ↦ hT _ (stdSimplex_coord_mem_Icc z.2) _ z.1.2
  let F : C(stdSimplex ℝ (Fin (n + 1)) × stdSimplex ℝ (Fin 2), M) :=
    ⟨fun z ↦ e.symm (Γ z), e.continuousOn_symm.comp_continuous hΓc hΓT⟩
  have hF : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, (t : Fin (n + 1) → ℝ) i = 0) →
      ∀ s, F (t, s) ≠ x := by
    rintro t ⟨i, hi⟩ s hts
    have : Γ (t, s) = e x := by
      rw [← e.right_inv (hΓT (t, s))]
      exact congrArg e hts
    exact (hγ _ (stdSimplex_coord_mem_Icc s)).sum_smul_ne_zero t hi (add_eq_left.1 this)
  have h := isLocallyHomologous_of_homotopy F hF
  have e0 : F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (stdSimplex.vertex 0))) =
      σ₀ := by
    ext1 t
    rw [h0]
    simp [F, Γ]
  have e1 : F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (stdSimplex.vertex 1))) =
      σ₁ := by
    ext1 t
    rw [h1]
    simp [F, Γ]
  rwa [e0, e1] at h

/-- A compact set `K` shrunk towards `p` by a small enough factor lies in any neighbourhood of
`p`. -/
lemma exists_smul_mem_of_isCompact {K : Set H} (hK : IsCompact K) (p : H) {W : Set H}
    (hW : W ∈ 𝓝 p) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ y ∈ K, p + ε • y ∈ W := by
  have hev : ∀ᶠ c : ℝ in 𝓝 0, ∀ y ∈ K, p + c • y ∈ W := by
    refine hK.eventually_forall_of_forall_eventually fun y _ ↦ ?_
    have hcont : Continuous fun z : ℝ × H ↦ p + z.1 • z.2 :=
      continuous_const.add (continuous_fst.smul continuous_snd)
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨c, hcW, hc0, hc1⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioc_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact ⟨c, hc0, hc1, hcW⟩

/-- Shrinking an oriented simplex around `p` towards `p`, inside itself. -/
lemma isLocallyHomologous_shrink (e : OpenPartialHomeomorph M H) {x : M} (hx : x ∈ e.source)
    {b : Module.Basis (Fin n) ℝ H} {v : Fin (n + 1) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ e.target) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {σ₀ σ₁ : Simplex M n} (h0 : ∀ t, σ₀ t = e.symm (affineSimplex v t))
    (h1 : ∀ t, σ₁ t = e.symm (e x + ∑ k, (t : Fin (n + 1) → ℝ) k • (ε • (v k - e x)))) :
    IsLocallyHomologous x σ₀ σ₁ := by
  set a : Fin (n + 1) → H := fun k ↦ v k - e x
  obtain ⟨τ, hτ0, hτ1, hτv⟩ := hv.1
  have hpv : ∑ k, τ k • v k = e x := by
    have : ∑ k, τ k • (v k - e x) = ∑ k, τ k • v k - e x := by
      simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hτ1]
    rw [this] at hτv
    exact sub_eq_zero.1 hτv
  refine isLocallyHomologous_of_orientedFamily e hx (b := b)
    (fun s ↦ ((1 - s) + s * ε) • a) (continuous_pi fun k ↦
      (((continuous_const.sub continuous_id).add (continuous_id.mul continuous_const)).smul
        continuous_const)) (fun s ⟨hs0, hs1⟩ ↦ hv.smul (by nlinarith)) ?_ (fun t ↦ ?_) (fun t ↦ ?_)
  · rintro s ⟨hs0, hs1⟩ t ht
    set l := (1 - s) + s * ε
    have hl0 : 0 ≤ l := by nlinarith
    have hl1 : l ≤ 1 := by nlinarith
    refine hvt ⟨⟨fun k ↦ (1 - l) * τ k + l * t k, fun k ↦ ?_, ?_⟩, ?_⟩
    · exact add_nonneg (mul_nonneg (by linarith) (hτ0 k).le) (mul_nonneg hl0 (ht.1 k))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hτ1, ht.2]
      ring
    · rw [affineSimplex_apply]
      have hts : ∑ k, t k = 1 := ht.2
      change ∑ k, ((1 - l) * τ k + l * t k) • v k = e x + ∑ k, t k • (l • a k)
      have hR : ∑ k, t k • (l • a k) = l • ∑ k, t k • v k - l • e x := by
        simp only [a, smul_sub, Finset.sum_sub_distrib, smul_comm (t _) l, ← Finset.smul_sum,
          ← Finset.sum_smul, hts, one_smul]
      have hL : ∑ k, ((1 - l) * τ k + l * t k) • v k = (1 - l) • e x + l • ∑ k, t k • v k := by
        simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hpv]
      rw [hR, hL]
      module
  · rw [h0, affineSimplex_apply]
    congr 1
    have hts : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
    simp [a, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hts]
  · rw [h1]
    simp [a]

/-- **The local orientation of a chart does not depend on the oriented simplex.** For a chart
`e` with values in `H` oriented by `b`, a point `x` of its domain and two affine simplices `Δ`,
`Δ'` of the image of `e` around `e x`, positively oriented for `b`, the singular simplices
`e⁻¹ ∘ Δ` and `e⁻¹ ∘ Δ'` of `M` are locally homologous at `x`. -/
theorem isLocallyHomologous_of_isOrientedSimplexAroundZero (e : OpenPartialHomeomorph M H)
    {x : M} (hx : x ∈ e.source) {b : Module.Basis (Fin n) ℝ H} {v w : Fin (n + 1) → H}
    (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - e x)
    (hvt : range (affineSimplex v) ⊆ e.target)
    (hw : IsOrientedSimplexAroundZero b fun k ↦ w k - e x)
    (hwt : range (affineSimplex w) ⊆ e.target) {σ₀ σ₁ : Simplex M n}
    (h0 : ∀ t, σ₀ t = e.symm (affineSimplex v t)) (h1 : ∀ t, σ₁ t = e.symm (affineSimplex w t)) :
    IsLocallyHomologous x σ₀ σ₁ := by
  set p := e x
  obtain ⟨δ, hδ⟩ := joinedIn_isOrientedSimplexAroundZero b hv hw
  set K : Set H := (fun z : ℝ × (Fin (n + 1) → ℝ) ↦ ∑ k, z.2 k • δ.extend z.1 k) ''
    (Icc (0 : ℝ) 1 ×ˢ stdSimplex ℝ (Fin (n + 1)))
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_stdSimplex ℝ _)).image
    (continuous_finsetSum _ fun k _ ↦ ((continuous_apply k).comp continuous_snd).smul
      ((continuous_apply k).comp (δ.continuous_extend.comp continuous_fst)))
  obtain ⟨ε, hε0, hε1, hεK⟩ := exists_smul_mem_of_isCompact hK p
    (e.open_target.mem_nhds (e.map_source hx))
  let σv : Simplex M n := ⟨fun t ↦ e.symm (p + ∑ k, (t : Fin (n + 1) → ℝ) k • (ε • (v k - p))),
    e.continuousOn_symm.comp_continuous (continuous_const.add (continuous_finsetSum _
      fun k _ ↦ ((continuous_apply k).comp continuous_subtype_val).smul continuous_const))
      fun t ↦ by
        simpa [Finset.smul_sum, smul_comm ε] using
          hεK _ ⟨(0, t), ⟨⟨le_rfl, zero_le_one⟩, t.2⟩, rfl⟩⟩
  let σw : Simplex M n := ⟨fun t ↦ e.symm (p + ∑ k, (t : Fin (n + 1) → ℝ) k • (ε • (w k - p))),
    e.continuousOn_symm.comp_continuous (continuous_const.add (continuous_finsetSum _
      fun k _ ↦ ((continuous_apply k).comp continuous_subtype_val).smul continuous_const))
      fun t ↦ by
        simpa [Finset.smul_sum, smul_comm ε] using
          hεK _ ⟨(1, t), ⟨⟨zero_le_one, le_rfl⟩, t.2⟩, rfl⟩⟩
  have hA := isLocallyHomologous_shrink e hx hv hvt hε0 hε1 (σ₁ := σv) h0 (fun t ↦ rfl)
  have hB := isLocallyHomologous_shrink e hx hw hwt hε0 hε1 (σ₁ := σw) h1 (fun t ↦ rfl)
  have hC : IsLocallyHomologous x σv σw := by
    refine isLocallyHomologous_of_orientedFamily e hx (b := b) (fun s ↦ ε • δ.extend s)
      (continuous_pi fun k ↦ continuous_const.smul ((continuous_apply k).comp δ.continuous_extend))
      (fun s hs ↦ Path.extend_apply δ hs ▸ (hδ _).smul hε0) ?_ (fun t ↦ ?_)
      (fun t ↦ ?_)
    · intro s hs t ht
      simpa [Finset.smul_sum, smul_comm ε] using hεK _ ⟨(s, t), ⟨hs, ht⟩, rfl⟩
    · simp only [σv, Path.extend_zero, Pi.smul_apply]
      rfl
    · simp only [σw, Path.extend_one, Pi.smul_apply]
      rfl
  exact hA.trans (hC.trans hB.symm)

end FundamentalClass

end MMP
