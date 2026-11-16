module

public import MMP.AlgebraicTopology.OrientationClass.Point
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology
public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains

/-!
# Orientation-preserving homeomorphisms with differentiable chart expressions (Fulton, §19.1)

A homeomorphism `φ : M ≃ₜ M'` of real `n`-manifolds whose chart expressions `e' ∘ φ ∘ e⁻¹` are
differentiable at every point with derivative of positive determinant (for the orienting bases
`b`, `b'`) is orientation preserving: the local degree of a map at a point is that of its
derivative (`MMP.FundamentalClass.isLocallyHomologous_of_hasFDerivAt`), and the
local class of a chart simplex does not depend on the oriented simplex. This is the orientation
step of (B2) of `lem_ext_c19_orientation_class_cap_fundamental` (a holomorphic map of complex
manifolds with bijective derivative preserves the complex orientations).

## Main results

* `MMP.FundamentalClass.IsLocallyHomologous.map`: continuous injective maps
  preserve local homology classes.
* `MMP.FundamentalClass.isOrientationPreserving_of_hasFDerivAt`.
-/

@[expose] public noncomputable section

open Set Topology Metric

universe u

namespace MMP

open ThomClass SingularChain

namespace FundamentalClass

/-- **Continuous injective maps preserve local homology classes**: if `σ₁` and `σ₂` have the
same class in `H_n(X, X - x; ℤ)` and `f : X → Y` is continuous and injective, then `f ∘ σ₁`
and `f ∘ σ₂` have the same class in `H_n(Y, Y - f x; ℤ)`. -/
lemma IsLocallyHomologous.map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    {n : ℕ} {σ₁ σ₂ : Simplex X n} (h : IsLocallyHomologous x σ₁ σ₂) (f : C(X, Y))
    (hf : Function.Injective f) : IsLocallyHomologous (f x) (f.comp σ₁) (f.comp σ₂) := by
  obtain ⟨c, d, hd, h⟩ := h
  refine ⟨postcomp ℤ f (n + 1) c, postcomp ℤ f n d,
    postcomp_mem_inside f (U := ({x}ᶜ : Set X)) (V := ({f x}ᶜ : Set Y))
      (fun y (hy : y ≠ x) (hfy : f y = f x) ↦ hy (hf hfy)) hd, ?_⟩
  have := congrArg (postcomp ℤ f n) h
  rwa [map_sub, map_add, postcomp_single, postcomp_single, postcomp_bd] at this

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H'] {M M' : Type u} [TopologicalSpace M]
  [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H' M']

/-- **A homeomorphism with orientation-preserving derivatives is orientation preserving.** If in
every pair of charts `e` of `M` at `x` and `e'` of `M'` at `φ x` the chart expression
`e' ∘ φ ∘ e⁻¹` is differentiable at `e x` with a derivative of positive determinant for the
bases `b`, `b'`, then `φ` is orientation preserving from `b` to `b'`. -/
theorem isOrientationPreserving_of_hasFDerivAt {n : ℕ} (b : Module.Basis (Fin n) ℝ H)
    (b' : Module.Basis (Fin n) ℝ H') (φ : M ≃ₜ M')
    (hφ : ∀ e ∈ atlas H M, ∀ e' ∈ atlas H' M', ∀ x ∈ e.source, φ x ∈ e'.source →
      ∃ D : H →L[ℝ] H', HasFDerivAt (fun y ↦ e' (φ (e.symm y))) D (e x) ∧
        0 < b'.det ((D : H → H') ∘ b)) :
    IsOrientationPreserving b b' φ := by
  intro e he e' he' x hx hx' v hv hvt v' hv' hvt'
  obtain ⟨D, hD, hdet⟩ := hφ e he e' he' x hx hx'
  set p := e x
  set q := e' (φ x)
  set W : Set H := e.target ∩ (fun y ↦ φ (e.symm y)) ⁻¹' e'.source
  have hc : ContinuousOn (fun y ↦ φ (e.symm y)) e.target :=
    φ.continuous.comp_continuousOn e.continuousOn_symm
  have hWo : IsOpen W := hc.isOpen_inter_preimage e.open_target e'.open_source
  have hpW : p ∈ W := ⟨e.map_source hx, by
    change φ (e.symm (e x)) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'⟩
  have hfc : ContinuousOn (fun y ↦ e' (φ (e.symm y))) W :=
    e'.continuousOn.comp (hc.mono inter_subset_left) fun y hy ↦ hy.2
  have hq : (fun y ↦ e' (φ (e.symm y))) p = q := by
    change e' (φ (e.symm (e x))) = e' (φ x)
    rw [e.left_inv hx]
  obtain ⟨δ, hδ, hloc⟩ := isLocallyHomologous_of_hasFDerivAt (X := M') b b' e'.open_target
    e'.continuousOn_symm e'.symm.injOn (hWo.mem_nhds hpW) hfc hq (e'.map_source hx') hD hdet
  obtain ⟨w, hw, hwt⟩ := exists_isOrientedSimplexAroundZero_subset b p
    (Filter.inter_mem (ball_mem_nhds p hδ) (hWo.mem_nhds hpW))
  have hwW : ∀ t, affineSimplex w t ∈ W := fun t ↦ (hwt ⟨t, rfl⟩).2
  have hwe : range (affineSimplex w) ⊆ e.target := fun _ ⟨t, ht⟩ ↦ ht ▸ (hwW t).1
  obtain ⟨hO, hrel⟩ := hloc w hw fun _ ⟨t, ht⟩ ↦ ht ▸ (hwt ⟨t, rfl⟩).1
  set v'' : Fin (n + 1) → H' := fun k ↦ q + D (w k - p)
  have hO' : range (affineSimplex v'') ⊆ e'.target := fun _ ⟨t, ht⟩ ↦ ht ▸ hO t
  -- step 1: `e⁻¹ ∘ Δ_v` and `e⁻¹ ∘ Δ_w` are locally homologous at `x`, hence so are their images
  have h1 := (isLocallyHomologous_of_isOrientedSimplexAroundZero e hx hv hvt hw hwe
    (σ₀ := inclChainSimplex (chartOpens e) (chartSimplex e v hvt))
    (σ₁ := chartSimplexOf e w hwe) (fun t ↦ rfl) (fun t ↦ rfl)).map (φ : C(M, M')) φ.injective
  -- step 2: the local degree of the chart expression at `p`
  have h2 := hrel ((φ : C(M, M')).comp (chartSimplexOf e w hwe)) (chartSimplexOf e' v'' hO')
    (fun t ↦ by
      change φ (e.symm (affineSimplex w t)) = e'.symm (e' (φ (e.symm (affineSimplex w t))))
      rw [e'.left_inv (hwW t).2]) (fun t ↦ rfl)
  rw [e'.left_inv hx'] at h2
  -- step 3: two oriented simplices in the chart `e'`
  have hv'' : IsOrientedSimplexAroundZero b' fun k ↦ v'' k - e' (φ x) := by
    have := hw.map_linearMap (D : H →ₗ[ℝ] H') hdet
    convert this using 1
    funext k
    simp [v'', q]
  have h3 := isLocallyHomologous_of_isOrientedSimplexAroundZero e' hx' hv'' hO' hv' hvt'
    (σ₀ := chartSimplexOf e' v'' hO')
    (σ₁ := inclChainSimplex (chartOpens e') (chartSimplex e' v' hvt')) (fun t ↦ rfl)
    (fun t ↦ rfl)
  exact h1.trans (h2.trans h3)

end FundamentalClass

end MMP
