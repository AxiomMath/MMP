module

public import MMP.AlgebraicTopology.OrientationClass.Submanifold
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Homotopy
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
/-!
# The orientation class does not depend on the tubular neighbourhood (Fulton, §19.1)

Let `M ⊆ P` and let `φ, φ' : N, N' → P` be tubular neighbourhoods of `M` compatible with the
complex orientations (`TubularNeighbourhood.IsOrientationCompatible`). Then a class
`u ∈ H^{2d}(P, P - M)` pulls back to a Thom class along `φ` exactly when it does along `φ'`:
the orientation class `u_{M,P}` of `MMP.IsOrientationClass` does not depend on the
tubular neighbourhood (Fulton, §19.1; Bott–Tu, §6).

The proof is local on `M`. A Thom class is detected on the oriented affine simplices around `0`
in the fibres; by a radial homotopy in the fibre (which avoids the zero section off `0`) it
suffices to test small simplices. Fix `x ∈ M`, the chart `e` at `x`, and the tangent cone `W` of
`M` at `x` in `e`, a complex subspace. Changing the complex frame of `N_x` we may assume that the
fibre derivatives `L, L'` of `φ, φ'` at `x` agree modulo `W`; let `π : E → ℂ^d` be the projection
along `W` with `π ∘ L' = id`, so also `π ∘ L = id`. Near `x`, `M` lies in every cone
`‖π (z - e x)‖ ≤ ε ‖z - e x‖` (the tangent cone lies in `W = ker π`), while the straight-line
homotopy `(1 - s) e φ(x, v) + s e φ'(x, v) = e x + (1 - s) L v + s L' v + o(v)` has
`π`-component `v + o(v)`; so for `v ≠ 0` small it never meets `M`. Homotopy invariance of
relative cohomology then identifies the values of a relative cocycle on the two fibre simplices.

## Main results

* `MMP.exists_norm_le_of_tangentConeAt_subset_ker`: a set lies near `x` in every
  cone around a closed subspace containing its tangent cone.
* `MMP.isThomClass_thomPullback_of_isOrientationCompatible`: Thom classes pull
  back to Thom classes along the change of tubular neighbourhood.
* `MMP.isOrientationClass_iff_of_isOrientationCompatible`: **the orientation class
  does not depend on the tubular neighbourhood**.
* `MMP.TubularNeighbourhood.injective_thomPullback`: for `M` closed, the map
  `H^j(P, P - M) → H^j(N, N - 0_N)` is injective (excision).
* `MMP.IsOrientationClass.eq`: **the orientation class is unique** (`M` closed).

## Implementation notes

The model `E` of `P` is finite-dimensional (compactness of its unit sphere gives the cone
estimate). The tangent cone of `M` in the chart is the subspace `W` of
`TubularNeighbourhood.IsOrientationCompatible`; it is what makes the two fibre derivatives
comparable.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [R. Bott, L. Tu, *Differential forms in algebraic topology*][botttu1982], §6.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Filter Topology Metric Finsupp

universe u

namespace MMP

section TangentCone

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The tangent cone of a set contained in a closed subspace `V`, at a point of `V`, lies in
`V`. -/
theorem tangentConeAt_subset_of_subset_submodule (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    {s : Set E} {x : E} (hs : s ⊆ V) (hx : x ∈ V) : tangentConeAt ℝ s x ⊆ V := by
  intro y hy
  obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  refine hV.mem_of_tendsto hcd ?_
  filter_upwards [hds] with n hn
  have : d n ∈ V := by simpa using V.sub_mem (hs hn) hx
  exact V.smul_mem _ this

/-- **A set lies near `x` in every cone around a subspace containing its tangent cone**: if the
tangent cone of `s` at `x` lies in the kernel of `π`, then for every `ε > 0` the points `z ∈ s`
near `x` satisfy `‖π (z - x)‖ ≤ ε ‖z - x‖` (compactness of the unit sphere). -/
theorem exists_norm_le_of_tangentConeAt_subset_ker [FiniteDimensional ℝ E] {s : Set E} {x : E}
    (p : E →L[ℝ] G) (hT : tangentConeAt ℝ s x ⊆ LinearMap.ker (p : E →ₗ[ℝ] G))
    {ε : ℝ} (hε : 0 < ε) : ∃ ρ > 0, ∀ z ∈ s, ‖z - x‖ < ρ → ‖p (z - x)‖ ≤ ε * ‖z - x‖ := by
  by_contra! h
  choose z hzs hzρ hzp using fun n : ℕ ↦ h (1 / (n + 1)) Nat.one_div_pos_of_nat
  set d : ℕ → E := fun n ↦ z n - x
  have hd0 : Tendsto d atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hzρ n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdne : ∀ n, d n ≠ 0 := fun n hn ↦ by
    have := hzp n
    simp only [d] at hn
    simp [hn] at this
  set w : ℕ → E := fun n ↦ ‖d n‖⁻¹ • d n
  have hw : ∀ n, w n ∈ sphere (0 : E) 1 := fun n ↦ by
    simp [w, norm_smul, hdne n]
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hw
  have haT : a ∈ tangentConeAt ℝ s x := by
    refine mem_tangentConeAt_of_seq atTop (fun n ↦ ‖d (φ n)‖⁻¹) (d ∘ φ)
      (hd0.comp hφ.tendsto_atTop) (Eventually.of_forall fun n ↦ ?_) ha
    simpa [d] using hzs (φ n)
  have hpa : p a = 0 := hT haT
  have hlow : ∀ n, ε ≤ ‖p (w n)‖ := fun n ↦ by
    rw [map_smul, norm_smul, norm_inv, norm_norm, le_inv_mul_iff₀ (norm_pos_iff.2 (hdne n))]
    simpa [d, mul_comm] using (hzp n).le
  have hlim : Tendsto (fun n ↦ ‖p ((w ∘ φ) n)‖) atTop (𝓝 ‖p a‖) :=
    ((p.continuous.tendsto a).comp ha).norm
  have : ε ≤ ‖p a‖ := ge_of_tendsto hlim (Eventually.of_forall fun n ↦ hlow (φ n))
  rw [hpa, norm_zero] at this
  linarith

end TangentCone

namespace SingularCochain

open SingularChain

variable {R : Type u} [CommRing R] {Y' Y : TopCat.{u}} {f g : Y' ⟶ Y} {A' : Set Y'} {A : Set Y}

/-- **Homotopic simplices take the same value on a relative cocycle**: if `H` is a homotopy from
`f` to `g` carrying `A' × [0, 1]` into `A`, and `σ` is a simplex of `Y'` whose boundary lies in
`A'`, then a relative cocycle `α` of `(Y, A)` takes the same value on `f ∘ σ` and on `g ∘ σ`. -/
theorem eval_comp_eq_of_homotopy (H : TopCat.Homotopy f g) (hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ A)
    (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) {n : ℕ} {α : Simplex Y n → R}
    (hα : α ∈ relCocycles R A n) (σ : Simplex Y' n)
    (hσ : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, t i = 0) → σ t ∈ A') :
    eval α (single (f.hom.comp σ) 1) = eval α (single (g.hom.comp σ) 1) := by
  have h := congrArg (fun c ↦ c (Submodule.Quotient.mk ⟨α, hα⟩))
    (relCohomologyMap_eq_of_homotopy (R := R) H hH hf hg n)
  simp only [relCohomologyMap_mk] at h
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h
  have hd := eval_single_eq_zero_of_mem_relCoboundaries (R := R) σ hσ _ h
  simp only [Submodule.coe_subtype, map_sub] at hd
  exact sub_eq_zero.1 (by simpa [linearCombination_single, cochainPullback] using hd)

end SingularCochain

section LocalComparison

open SingularChain SingularCochain

/-- The two estimates behind the comparison of tubular neighbourhoods: for `p ∘ L = p ∘ L' = id`
and errors `a, b` of size at most `η ‖v‖`, the convex combination
`w = (1 - s) (a + L v) + s (b + L' v)` has `‖w‖ ≤ (η + ‖L‖ + ‖L'‖) ‖v‖` and
`‖v‖ ≤ ‖p w‖ + ‖p‖ η ‖v‖`. -/
theorem norm_le_and_le_of_comp_eq_id {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L L' : V →L[ℝ] E) (p : E →L[ℝ] V) (hpL : ∀ v, p (L v) = v) (hpL' : ∀ v, p (L' v) = v)
    {η : ℝ} {a b : E} {v : V} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ‖a‖ ≤ η * ‖v‖) (hb : ‖b‖ ≤ η * ‖v‖) :
    ‖(1 - s) • (a + L v) + s • (b + L' v)‖ ≤ (η + ‖L‖ + ‖L'‖) * ‖v‖ ∧
      ‖v‖ ≤ ‖p ((1 - s) • (a + L v) + s • (b + L' v))‖ + ‖p‖ * (η * ‖v‖) := by
  have h1s : 0 ≤ 1 - s := by linarith
  have hLv := L.le_opNorm v
  have hL'v := L'.le_opNorm v
  constructor
  · calc ‖(1 - s) • (a + L v) + s • (b + L' v)‖
        ≤ (1 - s) * (‖a‖ + ‖L v‖) + s * (‖b‖ + ‖L' v‖) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg h1s]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) h1s
          · rw [norm_smul, Real.norm_of_nonneg hs0]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hs0
      _ ≤ (1 - s) * (η * ‖v‖ + ‖L‖ * ‖v‖) + s * (η * ‖v‖ + ‖L'‖ * ‖v‖) := by gcongr
      _ ≤ (η + ‖L‖ + ‖L'‖) * ‖v‖ := by
          have := norm_nonneg v
          have := norm_nonneg L
          have := norm_nonneg L'
          nlinarith [mul_nonneg h1s (mul_nonneg (norm_nonneg L') (norm_nonneg v)),
            mul_nonneg hs0 (mul_nonneg (norm_nonneg L) (norm_nonneg v))]
  · have hp : p ((1 - s) • (a + L v) + s • (b + L' v)) = v + ((1 - s) • p a + s • p b) := by
      simp only [map_add, map_smul, hpL, hpL']
      module
    have hab : ‖(1 - s) • p a + s • p b‖ ≤ ‖p‖ * (η * ‖v‖) := by
      calc ‖(1 - s) • p a + s • p b‖ ≤ (1 - s) * ‖p a‖ + s * ‖p b‖ := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_smul, Real.norm_of_nonneg h1s]
            · rw [norm_smul, Real.norm_of_nonneg hs0]
        _ ≤ (1 - s) * (‖p‖ * (η * ‖v‖)) + s * (‖p‖ * (η * ‖v‖)) := by
            gcongr
            · exact (p.le_opNorm a).trans (by gcongr)
            · exact (p.le_opNorm b).trans (by gcongr)
        _ = ‖p‖ * (η * ‖v‖) := by ring
    rw [hp]
    have := norm_sub_le (v + ((1 - s) • p a + s • p b)) ((1 - s) • p a + s • p b)
    simp only [add_sub_cancel_right] at this
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P}

omit [FiniteDimensional ℝ E] [ChartedSpace E P] in
/-- **Straight-line homotopy in a chart.** If on `ball 0 δ` the segment between `e ∘ A` and
`e ∘ B` stays in the target of `e` and its image under `e.symm` avoids `M` off `0`, then for
singular simplices `σ` of `ball 0 δ` whose boundary avoids `0`, every relative cocycle of
`(P, P - M)` takes the same value on `A ∘ σ` and `B ∘ σ`. -/
theorem eval_comp_eq_of_straightLine {r : ℕ} (e : OpenPartialHomeomorph P E)
    (A B : C(Fin r → ℂ, P)) {δ : ℝ}
    (key : ∀ v : Fin r → ℂ, v ∈ ball (0 : Fin r → ℂ) δ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      A v ∈ e.source ∧ B v ∈ e.source ∧
      (1 - s) • e (A v) + s • e (B v) ∈ e.target ∧
      (v ≠ 0 → e.symm ((1 - s) • e (A v) + s • e (B v)) ∉ M))
    {R : Type u} [CommRing R] {n : ℕ} {α : Simplex P n → R} (hα : α ∈ relCocycles R Mᶜ n)
    (σ : Simplex (Fin r → ℂ) n) (hσδ : range σ ⊆ ball 0 δ)
    (hσ0 : ∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, t i = 0) → σ t ≠ 0) :
    eval α (single (A.comp σ) 1) = eval α (single (B.comp σ) 1) := by
  let Y' : TopCat.{u} := TopCat.of (ULift.{u} (ball (0 : Fin r → ℂ) δ))
  have hdown : Continuous fun w : Y' ↦ (w.down : Fin r → ℂ) :=
    continuous_subtype_val.comp continuous_uliftDown
  let f : Y' ⟶ P := TopCat.ofHom ⟨fun w ↦ A w.down.1, A.continuous.comp hdown⟩
  let g : Y' ⟶ P := TopCat.ofHom ⟨fun w ↦ B w.down.1, B.continuous.comp hdown⟩
  have hkey : ∀ (q : unitInterval × Y'), _ := fun q ↦ key q.2.down.1 q.2.down.2 q.1 q.1.2.1 q.1.2.2
  have heA : Continuous fun w : Y' ↦ e (A w.down.1) :=
    e.continuousOn.comp_continuous (A.continuous.comp hdown) fun w ↦
      (key w.down.1 w.down.2 0 le_rfl zero_le_one).1
  have heB : Continuous fun w : Y' ↦ e (B w.down.1) :=
    e.continuousOn.comp_continuous (B.continuous.comp hdown) fun w ↦
      (key w.down.1 w.down.2 0 le_rfl zero_le_one).2.1
  have hzc : Continuous fun q : unitInterval × Y' ↦
      (1 - (q.1 : ℝ)) • e (A q.2.down.1) + (q.1 : ℝ) • e (B q.2.down.1) :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (heA.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (heB.comp continuous_snd))
  let H : TopCat.Homotopy f g :=
    { toFun := fun q ↦ e.symm ((1 - (q.1 : ℝ)) • e (A q.2.down.1) + (q.1 : ℝ) • e (B q.2.down.1))
      continuous_toFun := e.continuousOn_symm.comp_continuous hzc fun q ↦ (hkey q).2.2.1
      map_zero_left := fun w ↦ by
        simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
        exact e.left_inv (key w.down.1 w.down.2 0 le_rfl zero_le_one).1
      map_one_left := fun w ↦ by
        simp only [Set.Icc.coe_one, sub_self, one_smul, zero_smul, zero_add]
        exact e.left_inv (key w.down.1 w.down.2 0 le_rfl zero_le_one).2.1 }
  let A' : Set Y' := {w | (w.down : Fin r → ℂ) ≠ 0}
  have hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ Mᶜ := fun y hy t ↦ (hkey (t, y)).2.2.2 hy
  have hf : A' ⊆ f ⁻¹' Mᶜ := fun y hy ↦ by
    have := hH y hy 0
    rwa [H.apply_zero] at this
  have hg : A' ⊆ g ⁻¹' Mᶜ := fun y hy ↦ by
    have := hH y hy 1
    rwa [H.apply_one] at this
  let σ' : Simplex Y' n := ⟨fun t ↦ ULift.up ⟨σ t, hσδ ⟨t, rfl⟩⟩,
    continuous_uliftUp.comp (σ.continuous.subtype_mk _)⟩
  exact eval_comp_eq_of_homotopy H hH hf hg hα σ' fun t ht ↦ hσ0 t ht

/-- **Local comparison of two transversal discs.** Let `A, B : ℂ^r → P` send `0` to `x`, be
differentiable at `0` in the chart `e` at `x` with derivatives `L, L'`, and let `p : E → ℂ^r`
be a linear map with `p ∘ L = p ∘ L' = id` whose kernel contains the tangent cone of `M` at `x`
in `e`. Then for small singular simplices `σ` of `ℂ^r` whose boundary avoids `0`, every relative
cocycle of `(P, P - M)` takes the same value on `A ∘ σ` and `B ∘ σ`: the straight-line homotopy
between `e ∘ A` and `e ∘ B` avoids `M` off `0`. -/
theorem exists_eval_comp_eq_of_hasFDerivAt {x : P} {r : ℕ} (A B : C(Fin r → ℂ, P))
    (hA0 : A 0 = x) (hB0 : B 0 = x) {L L' : (Fin r → ℂ) →L[ℝ] E}
    (hA : HasFDerivAt (fun v ↦ chartAt E x (A v)) L 0)
    (hB : HasFDerivAt (fun v ↦ chartAt E x (B v)) L' 0)
    (p : E →L[ℝ] (Fin r → ℂ)) (hpL : ∀ v, p (L v) = v) (hpL' : ∀ v, p (L' v) = v)
    (hT : tangentConeAt ℝ (chartAt E x '' (M ∩ (chartAt E x).source)) (chartAt E x x) ⊆
      LinearMap.ker (p : E →ₗ[ℝ] (Fin r → ℂ))) :
    ∃ δ > 0, ∀ (R : Type u) [CommRing R] {n : ℕ} {α : Simplex P n → R},
      α ∈ relCocycles R Mᶜ n → ∀ σ : Simplex (Fin r → ℂ) n, range σ ⊆ ball 0 δ →
      (∀ t : stdSimplex ℝ (Fin (n + 1)), (∃ i, t i = 0) → σ t ≠ 0) →
      eval α (single (A.comp σ) 1) = eval α (single (B.comp σ) 1) := by
  set e := chartAt E x
  have hxs : x ∈ e.source := mem_chart_source E x
  set C : ℝ := ‖L‖ + ‖L'‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨ρ, hρ, hcone⟩ := exists_norm_le_of_tangentConeAt_subset_ker p hT
    (ε := 1 / (4 * C)) (by positivity)
  obtain ⟨ρt, hρt, hball⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hxs)
  set η : ℝ := 1 / (2 * (‖p‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by positivity)]; linarith [norm_nonneg p]
  have hpη : ‖p‖ * η ≤ 1 / 2 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [norm_nonneg p]
  have hAs : A ⁻¹' e.source ∈ 𝓝 (0 : Fin r → ℂ) :=
    A.continuous.continuousAt.preimage_mem_nhds (by rw [hA0]; exact e.open_source.mem_nhds hxs)
  have hBs : B ⁻¹' e.source ∈ 𝓝 (0 : Fin r → ℂ) :=
    B.continuous.continuousAt.preimage_mem_nhds (by rw [hB0]; exact e.open_source.mem_nhds hxs)
  obtain ⟨δ₀, hδ₀, hδ₀s⟩ := Metric.mem_nhds_iff.1
    (((hA.isLittleO.bound hηpos).and (hB.isLittleO.bound hηpos)).and (inter_mem hAs hBs))
  set δ := min δ₀ (min ρ ρt / C)
  have hδpos : 0 < δ := lt_min hδ₀ (div_pos (lt_min hρ hρt) hCpos)
  have key : ∀ v : Fin r → ℂ, v ∈ ball (0 : Fin r → ℂ) δ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      A v ∈ e.source ∧ B v ∈ e.source ∧
      (1 - s) • e (A v) + s • e (B v) ∈ e.target ∧
      (v ≠ 0 → e.symm ((1 - s) • e (A v) + s • e (B v)) ∉ M) := by
    intro v hv s hs0 hs1
    have hv0 : v ∈ ball (0 : Fin r → ℂ) δ₀ := ball_subset_ball (min_le_left _ _) hv
    obtain ⟨⟨ha, hb⟩, hAv, hBv⟩ := hδ₀s hv0
    have ha' : ‖e (A v) - e x - L v‖ ≤ η * ‖v‖ := by simpa [hA0] using ha
    have hb' : ‖e (B v) - e x - L' v‖ ≤ η * ‖v‖ := by simpa [hB0] using hb
    obtain ⟨h1, h2⟩ := norm_le_and_le_of_comp_eq_id L L' p hpL hpL' hs0 hs1 ha' hb'
    have hz : (1 - s) • e (A v) + s • e (B v) - e x = (1 - s) • (e (A v) - e x - L v + L v) +
        s • (e (B v) - e x - L' v + L' v) := by module
    rw [← hz] at h1 h2
    have hvδ : ‖v‖ < δ := by simpa using hv
    have hvρ : C * ‖v‖ < min ρ ρt := by
      rw [mul_comm, ← lt_div_iff₀ hCpos]; exact hvδ.trans_le (min_le_right _ _)
    have hzC : ‖(1 - s) • e (A v) + s • e (B v) - e x‖ ≤ C * ‖v‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (by rw [hC]; linarith) (norm_nonneg _))
    have hzt : (1 - s) • e (A v) + s • e (B v) ∈ e.target := hball (by
      rw [mem_ball, dist_eq_norm]
      exact hzC.trans_lt (hvρ.trans_le (min_le_right _ _)))
    refine ⟨hAv, hBv, hzt, fun hv0 hM ↦ ?_⟩
    have hmem : (1 - s) • e (A v) + s • e (B v) ∈ e '' (M ∩ e.source) :=
      ⟨e.symm _, ⟨hM, e.map_target hzt⟩, e.right_inv hzt⟩
    have hc := hcone _ hmem (hzC.trans_lt (hvρ.trans_le (min_le_left _ _)))
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have h3 : 1 / (4 * C) * ‖(1 - s) • e (A v) + s • e (B v) - e x‖ ≤ ‖v‖ / 4 :=
      (mul_le_mul_of_nonneg_left hzC (by positivity)).trans_eq (by field_simp)
    have h4 : ‖p‖ * (η * ‖v‖) ≤ ‖v‖ / 2 := by rw [← mul_assoc]; nlinarith
    linarith
  exact ⟨δ, hδpos, fun R _ n α hα σ hσδ hσ0 ↦
    eval_comp_eq_of_straightLine e A B key hα σ hσδ hσ0⟩

end LocalComparison

section Scaling

open SingularChain SingularCochain ThomClass

variable {r : ℕ}

/-- The affine simplex with vertices scaled by `c` is the scaling by `c` of the affine simplex. -/
lemma affineSimplex_smul {n : ℕ} (c : ℝ) (v : Fin (n + 1) → (Fin r → ℂ))
    (t : stdSimplex ℝ (Fin (n + 1))) : affineSimplex (c • v) t = c • affineSimplex v t := by
  simp only [affineSimplex_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _

/-- Every affine simplex can be shrunk by some `c > 0` into a given ball around `0`. -/
lemma exists_range_affineSimplex_smul_subset_ball {n : ℕ} (v : Fin (n + 1) → (Fin r → ℂ))
    {δ : ℝ} (hδ : 0 < δ) : ∃ c : ℝ, 0 < c ∧ range (affineSimplex (c • v)) ⊆ ball 0 δ := by
  set K := ∑ k, ‖v k‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [mem_ball_zero_iff, affineSimplex_smul, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hle : ‖affineSimplex v t‖ ≤ K := by
    rw [affineSimplex_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    have h0 : (0 : ℝ) ≤ t k := t.2.1 k
    have h1 : t k ≤ 1 := by
      have := Finset.single_le_sum (fun j _ ↦ t.2.1 j) (Finset.mem_univ k)
      rw [t.2.2] at this
      exact this
    rw [norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  calc δ / (K + 1) * ‖affineSimplex v t‖ ≤ δ / (K + 1) * K := by gcongr
    _ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

variable {P : TopCat.{u}} {M : Set P}

/-- **Radial invariance**: if `A : ℂ^r → P` meets `M` only at `0`, a relative cocycle of
`(P, P - M)` takes the same value on `A ∘ Δ` and on `A ∘ (c Δ)`, for an affine simplex `Δ`
around `0` and `c > 0`. -/
theorem eval_comp_affineSimplex_smul (A : C(Fin r → ℂ, P)) (hA : ∀ v, A v ∈ M → v = 0)
    (R : Type u) [CommRing R] {n : ℕ} {α : Simplex P n → R} (hα : α ∈ relCocycles R Mᶜ n)
    {b : Module.Basis (Fin n) ℝ (Fin r → ℂ)} {v : Fin (n + 1) → (Fin r → ℂ)}
    (hv : IsOrientedSimplexAroundZero b v) {c : ℝ} (hc : 0 < c) :
    eval α (single (A.comp (affineSimplex v)) 1) =
      eval α (single (A.comp (affineSimplex (c • v))) 1) := by
  let Y' : TopCat.{u} := TopCat.of (ULift.{u} (Fin r → ℂ))
  let f : Y' ⟶ P := TopCat.ofHom ⟨fun w ↦ A w.down, A.continuous.comp continuous_uliftDown⟩
  let g : Y' ⟶ P := TopCat.ofHom ⟨fun w ↦ A (c • w.down),
    A.continuous.comp (continuous_uliftDown.const_smul c)⟩
  have hpos : ∀ s : unitInterval, 0 < 1 - (s : ℝ) + (s : ℝ) * c := fun s ↦ by
    have h0 := s.2.1
    have h1 := s.2.2
    rcases eq_or_lt_of_le h1 with h | h
    · rw [h]
      linarith
    · nlinarith [mul_nonneg h0 hc.le]
  let H : TopCat.Homotopy f g :=
    { toFun := fun q ↦ A ((1 - (q.1 : ℝ) + (q.1 : ℝ) * c) • q.2.down)
      continuous_toFun := A.continuous.comp (((continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).smul
        (continuous_uliftDown.comp continuous_snd))
      map_zero_left := fun w ↦ by simp [f]
      map_one_left := fun w ↦ by simp [g] }
  let A' : Set Y' := {w | w.down ≠ 0}
  have hH : ∀ y ∈ A', ∀ t, H (t, y) ∈ Mᶜ := fun y hy t hM ↦
    hy ((smul_eq_zero.1 (hA _ hM)).resolve_left (hpos t).ne')
  have hf : A' ⊆ f ⁻¹' Mᶜ := fun y hy ↦ by
    have := hH y hy 0
    rwa [H.apply_zero] at this
  have hg : A' ⊆ g ⁻¹' Mᶜ := fun y hy ↦ by
    have := hH y hy 1
    rwa [H.apply_one] at this
  let σ' : Simplex Y' n := ⟨fun t ↦ ULift.up (affineSimplex v t),
    continuous_uliftUp.comp (affineSimplex v).continuous⟩
  have := eval_comp_eq_of_homotopy H hH hf hg hα σ' fun t ht ↦ hv.affineSimplex_ne_zero t ht
  convert this using 3 <;> ext t
  · rfl
  · exact congrArg A (affineSimplex_smul c v t)

end Scaling

section Bridge

open SingularChain SingularCochain ThomClass

variable {P : TopCat.{u}} {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- The value of the pull-back `φ^* u ∈ H^{2d}(N, N - 0_N)` on a fibre simplex is the value of a
representing relative cocycle of `u` on its image under `φ`. -/
theorem relEval_thomPullback (φ : TubularNeighbourhood F N)
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    {α : Simplex P (2 * Module.finrank ℂ F) → R}
    (hα : α ∈ relCocycles R (Mᶜ : Set P) (2 * Module.finrank ℂ F))
    (hrep : relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u =
      Submodule.Quotient.mk ⟨α, hα⟩) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x)
    {v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v) :
    relEval (R := R) (single (fibreSimplex F x ψ v) 1)
      (eval_single_eq_zero_of_mem_relCoboundaries _
        (fibreSimplex_notMem_range_zeroSection F x ψ hv))
      (relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F N)) _ _
        ((φ.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u)) =
      eval α (single (φ.toHom.hom.comp (fibreSimplex F x ψ v)) 1) := by
  have h₁ : (φ.toHom ⁻¹' M)ᶜ ⊆ φ.toHom ⁻¹' (Mᶜ : Set P) := fun _ hx ↦ hx
  have h₂ : (range (zeroSection F N))ᶜ ⊆
      (𝟙 (TopCat.of (TotalSpace F N))) ⁻¹' (φ.toHom ⁻¹' M)ᶜ :=
    compl_subset_compl.mpr φ.preimage_eq_range_zeroSection.subset
  have e2 := relativeSingularCohomologyEquiv_map (R := R) φ.toHom h₁ (2 * Module.finrank ℂ F) u
  have e1 := relativeSingularCohomologyEquiv_map (R := R) (𝟙 (TopCat.of (TotalSpace F N))) h₂
    (2 * Module.finrank ℂ F)
    ((relativeSingularCohomology.map R (ModuleCat.of R R) φ.toHom h₁
      (2 * Module.finrank ℂ F : ℕ)).hom u)
  refine (congrArg (relEval (R := R) (single (fibreSimplex F x ψ v) 1) _)
    (e1.trans (congrArg _ e2))).trans ?_
  rw [hrep, relCohomologyMap_mk, relCohomologyMap_mk, relEval_mk]
  simp only [linearCombination_single, one_smul]
  rfl

/-- The pull-back `φ^* u` is a Thom class exactly when a representing relative cocycle of `u`
takes the value `1` on the image under `φ` of every oriented fibre simplex around `0`. -/
theorem isThomClass_thomPullback_iff (φ : TubularNeighbourhood F N)
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    {α : Simplex P (2 * Module.finrank ℂ F) → R}
    (hα : α ∈ relCocycles R (Mᶜ : Set P) (2 * Module.finrank ℂ F))
    (hrep : relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u =
      Submodule.Quotient.mk ⟨α, hα⟩) :
    IsThomClass (R := R) F N ((φ.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u) ↔
      ∀ (x : M) (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x)
        (v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ)),
        IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v →
        eval α (single (φ.toHom.hom.comp (fibreSimplex F x ψ v)) 1) = 1 :=
  forall₄_congr fun x ψ v hv ↦ by rw [relEval_thomPullback R φ hα hrep x ψ hv]

end Bridge

section FrameChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {r : ℕ}

/-- The complex linear isomorphism `ℂ^r ≅ E / W` induced by a real linear injection `L` with image
complementary to the complex subspace `W` and complex linear modulo `W`. -/
def quotientEquivOfIsCompl (W : Submodule ℂ E) (L : (Fin r → ℂ) →L[ℝ] E)
    (hc : IsCompl (LinearMap.range (L : (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hinj : Function.Injective L) (hl : ∀ (c : ℂ) v, L (c • v) - c • L v ∈ W) :
    (Fin r → ℂ) ≃ₗ[ℂ] E ⧸ W :=
  LinearEquiv.ofBijective
    { toFun := fun v ↦ W.mkQ (L v)
      map_add' := fun v w ↦ by simp
      map_smul' := fun c v ↦ by
        simp only [Submodule.mkQ_apply, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        exact (Submodule.Quotient.eq W).2 (hl c v) }
    ⟨fun v w h ↦ hinj (by
      have h' : L v - L w ∈ W := (Submodule.Quotient.eq W).1 h
      have hr : L v - L w ∈ LinearMap.range (L : (Fin r → ℂ) →ₗ[ℝ] E) :=
        ⟨v - w, by simp⟩
      exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hc.disjoint) _ hr h')),
    fun q ↦ by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective W q
      obtain ⟨y, ⟨v, rfl⟩, w, hw, rfl⟩ :=
        Submodule.mem_sup.1 (hc.codisjoint.eq_top.symm ▸ Submodule.mem_top : z ∈ _)
      refine ⟨v, (Submodule.Quotient.eq W).2 ?_⟩
      simpa using W.neg_mem hw⟩

omit [FiniteDimensional ℂ E] in
/-- `quotientEquivOfIsCompl W L hc hinj hl` sends `v` to the class of `L v` modulo `W`. -/
lemma quotientEquivOfIsCompl_apply (W : Submodule ℂ E) (L : (Fin r → ℂ) →L[ℝ] E) (hc hinj hl)
    (v : Fin r → ℂ) : quotientEquivOfIsCompl W L hc hinj hl v = W.mkQ (L v) :=
  rfl

/-- **Frame change.** Let `L, L' : ℂ^r → E` be real linear injections, complex linear modulo a
complex subspace `W` and with images complementary to `W`, and let `h` be a complex linear
automorphism of `ℂ^r`. There are a complex linear automorphism `k` of `ℂ^r` with
`L ∘ k ≡ L' ∘ h` modulo `W`, and a real linear map `p : E → ℂ^r` killing `W` with
`p ∘ L ∘ k = p ∘ L' ∘ h = id`. -/
theorem exists_frameChange (W : Submodule ℂ E) (L L' : (Fin r → ℂ) →L[ℝ] E)
    (hc : IsCompl (LinearMap.range (L : (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hc' : IsCompl (LinearMap.range (L' : (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hinj : Function.Injective L) (hinj' : Function.Injective L')
    (hl : ∀ (c : ℂ) v, L (c • v) - c • L v ∈ W) (hl' : ∀ (c : ℂ) v, L' (c • v) - c • L' v ∈ W)
    (h : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ)) :
    ∃ (k : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ)) (p : E →L[ℝ] (Fin r → ℂ)),
      (∀ v, p (L (k v)) = v) ∧ (∀ v, p (L' (h v)) = v) ∧ ∀ w ∈ W, p w = 0 := by
  set A := quotientEquivOfIsCompl W L hc hinj hl
  set A' := quotientEquivOfIsCompl W L' hc' hinj' hl'
  let k : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) :=
    ((h.toLinearEquiv.trans A').trans A.symm).toContinuousLinearEquiv
  have hk : ∀ v, L (k v) - L' (h v) ∈ W := fun v ↦ by
    have : A (k v) = A' (h v) := by simp [k]
    rw [quotientEquivOfIsCompl_apply, quotientEquivOfIsCompl_apply] at this
    exact (Submodule.Quotient.eq W).1 this
  let eL := LinearEquiv.ofInjective (L' : (Fin r → ℂ) →ₗ[ℝ] E) hinj'
  let p₀ : E →ₗ[ℝ] (Fin r → ℂ) :=
    (h.symm.toLinearEquiv.restrictScalars ℝ : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ)) ∘ₗ
      (eL.symm : _ →ₗ[ℝ] (Fin r → ℂ)) ∘ₗ Submodule.projectionOnto _ _ hc'
  have hp₀L' : ∀ v, p₀ (L' v) = h.symm v := fun v ↦ by
    set y : LinearMap.range (L' : (Fin r → ℂ) →ₗ[ℝ] E) := ⟨L' v, LinearMap.mem_range_self _ v⟩
    have h1 : Submodule.projectionOnto _ _ hc' (L' v) = y :=
      Submodule.projectionOnto_apply_left hc' y
    have h2 : eL.symm y = v := hinj'
      (LinearEquiv.ofInjective_symm_apply (L' : (Fin r → ℂ) →ₗ[ℝ] E) (h := hinj') y)
    simp only [p₀, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, h2]
    rfl
  have hp₀W : ∀ w ∈ W, p₀ w = 0 := fun w hw ↦ by
    have h1 : Submodule.projectionOnto _ _ hc' w = 0 :=
      Submodule.projectionOnto_apply_right hc' ⟨w, hw⟩
    simp [p₀, h1]
  let p : E →L[ℝ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap p₀
  have hp : ∀ w, p w = p₀ w := fun w ↦ rfl
  have hpW : ∀ w ∈ W, p w = 0 := fun w hw ↦ (hp w).trans (hp₀W w hw)
  have hpL' : ∀ v, p (L' (h v)) = v := fun v ↦ by
    rw [hp, hp₀L', ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨k, p, fun v ↦ ?_, hpL', hpW⟩
  have : L (k v) = L' (h v) + (L (k v) - L' (h v)) := by abel
  rw [this, map_add, hpL', hpW _ (hk v), add_zero]

end FrameChange

section Independent

open SingularChain SingularCochain ThomClass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  {N' : M → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
  [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace F N')] [FiberBundle F N']
  [_root_.VectorBundle ℂ F N']
  (R : Type u) [CommRing R]

/-- The fibre disc `v ↦ φ(ψ v)` of a tubular neighbourhood at `x`, as a continuous map
`ℂ^d → P`. -/
def TubularNeighbourhood.fibreDisc (φ : TubularNeighbourhood F N) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x) : C(Fin (Module.finrank ℂ F) → ℂ, P) :=
  φ.toHom.hom.comp ((⟨TotalSpace.mk x, FiberBundle.continuous_totalSpaceMk F N x⟩ :
    C(N x, TotalSpace F N)).comp (ψ : C(Fin (Module.finrank ℂ F) → ℂ, N x)))

/-- The fibre disc sends `v` to `φ` applied to the point `ψ v` of the fibre over `x`. -/
lemma TubularNeighbourhood.fibreDisc_apply (φ : TubularNeighbourhood F N) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x) (v : Fin (Module.finrank ℂ F) → ℂ) :
    φ.fibreDisc x ψ v = φ (TotalSpace.mk x (ψ v)) :=
  rfl

/-- The fibre disc at `x` sends `0` to `x`. -/
lemma TubularNeighbourhood.fibreDisc_zero (φ : TubularNeighbourhood F N) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x) : φ.fibreDisc x ψ 0 = x := by
  rw [fibreDisc_apply, map_zero]
  exact φ.map_zeroSection x

/-- The fibre disc meets `M` only at `0`. -/
lemma TubularNeighbourhood.eq_zero_of_fibreDisc_mem (φ : TubularNeighbourhood F N) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x) (v : Fin (Module.finrank ℂ F) → ℂ)
    (hv : φ.fibreDisc x ψ v ∈ M) : v = 0 := by
  have h : TotalSpace.mk x (ψ v) ∈ φ ⁻¹' M := hv
  rw [φ.preimage_eq_range_zeroSection] at h
  obtain ⟨y, hy⟩ := h
  have hyx : y = x := congrArg TotalSpace.proj hy
  subst hyx
  rw [zeroSection, TotalSpace.mk_inj] at hy
  exact ψ.map_eq_zero_iff.1 hy.symm

/-- **Thom classes pull back to Thom classes along a change of tubular neighbourhood**: if
`φ, φ'` are tubular neighbourhoods of `M` compatible with the complex orientations and `φ^* u` is
a Thom class, so is `φ'^* u`. -/
theorem isThomClass_thomPullback_of_isOrientationCompatible (φ : TubularNeighbourhood F N)
    (φ' : TubularNeighbourhood F N') (hφ : φ.IsOrientationCompatible (E := E))
    (hφ' : φ'.IsOrientationCompatible (E := E))
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsThomClass (R := R) F N ((φ.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u)) :
    IsThomClass (R := R) F N' ((φ'.thomPullback R (2 * Module.finrank ℂ F : ℕ)).hom u) := by
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u)
  rw [isThomClass_thomPullback_iff R φ hα hrep.symm] at hu
  rw [isThomClass_thomPullback_iff R φ' hα hrep.symm]
  intro x ψ' v hv
  obtain ⟨ψ₀, L, hL, hinj, W, hTW, hc, hl⟩ := hφ x
  obtain ⟨ψ'₀, L', hL', hinj', W', hTW', hc', hl'⟩ := hφ' x
  have hWW : W' = W := SetLike.coe_injective (hTW'.symm.trans hTW)
  rw [hWW] at hc' hl'
  obtain ⟨k, p, hpL, hpL', hpW⟩ :=
    exists_frameChange W L L' hc hc' hinj hinj' hl hl' (ψ'.trans ψ'₀.symm)
  let A := φ.fibreDisc x (k.trans ψ₀)
  let B := φ'.fibreDisc x ψ'
  let h := ψ'.trans ψ'₀.symm
  let kL : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ F) → ℂ) :=
    (k : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ F) → ℂ)).restrictScalars ℝ
  let hL₁ : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ F) → ℂ) :=
    (h : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ F) → ℂ)).restrictScalars ℝ
  have hA : HasFDerivAt (fun v ↦ chartAt E (x : P) (A v)) (L.comp kL) 0 := by
    have hL0 : HasFDerivAt (fun v ↦ chartAt E (x : P) (φ (TotalSpace.mk x (ψ₀ v)))) L (kL 0) := by
      rw [map_zero]
      exact hL
    exact hL0.comp 0 kL.hasFDerivAt
  have hB : HasFDerivAt (fun v ↦ chartAt E (x : P) (B v)) (L'.comp hL₁) 0 := by
    have hL0 : HasFDerivAt (fun v ↦ chartAt E (x : P) (φ' (TotalSpace.mk x (ψ'₀ v)))) L'
        (hL₁ 0) := by
      rw [map_zero]
      exact hL'
    have hfun : (fun v ↦ chartAt E (x : P) (B v)) =
        (fun v ↦ chartAt E (x : P) (φ' (TotalSpace.mk x (ψ'₀ v)))) ∘ hL₁ := funext fun w ↦ by
      simp [B, TubularNeighbourhood.fibreDisc_apply, hL₁, h]
    rw [hfun]
    exact hL0.comp 0 hL₁.hasFDerivAt
  have hT : tangentConeAt ℝ (chartAt E (x : P) '' (M ∩ (chartAt E (x : P)).source))
      (chartAt E (x : P) x) ⊆ LinearMap.ker (p : E →ₗ[ℝ] (Fin (Module.finrank ℂ F) → ℂ)) := by
    rw [hTW]
    exact fun w hw ↦ LinearMap.mem_ker.2 (hpW w hw)
  obtain ⟨δ, hδ, hloc⟩ := exists_eval_comp_eq_of_hasFDerivAt (M := M) A B
    (φ.fibreDisc_zero x _) (φ'.fibreDisc_zero x _) hA hB p (fun w ↦ hpL w)
    (fun w ↦ hpL' w) hT
  obtain ⟨c, hc0, hcδ⟩ := exists_range_affineSimplex_smul_subset_ball v hδ
  calc eval α (single (φ'.toHom.hom.comp (fibreSimplex F x ψ' v)) 1)
      = eval α (single (B.comp (affineSimplex v)) 1) := rfl
    _ = eval α (single (B.comp (affineSimplex (c • v))) 1) :=
      eval_comp_affineSimplex_smul B (φ'.eq_zero_of_fibreDisc_mem x ψ') R hα hv hc0
    _ = eval α (single (A.comp (affineSimplex (c • v))) 1) :=
      (hloc R hα _ hcδ fun t ht ↦ (hv.smul hc0).affineSimplex_ne_zero t ht).symm
    _ = eval α (single (φ.toHom.hom.comp (fibreSimplex F x (k.trans ψ₀) (c • v))) 1) := rfl
    _ = 1 := hu x _ _ (hv.smul hc0)

/-- **The orientation class does not depend on the tubular neighbourhood** (Fulton, §19.1;
Bott–Tu, §6): for tubular neighbourhoods `φ, φ'` of `M` compatible with the complex
orientations, `u` is the orientation class relative to `φ` exactly when it is relative to
`φ'`. -/
theorem isOrientationClass_iff_of_isOrientationCompatible (φ : TubularNeighbourhood F N)
    (φ' : TubularNeighbourhood F N') (hφ : φ.IsOrientationCompatible (E := E))
    (hφ' : φ'.IsOrientationCompatible (E := E))
    (u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)) :
    IsOrientationClass E R φ u ↔ IsOrientationClass E R φ' u :=
  ⟨fun h ↦ ⟨hφ', isThomClass_thomPullback_of_isOrientationCompatible R φ φ' hφ hφ' h.2⟩,
    fun h ↦ ⟨hφ, isThomClass_thomPullback_of_isOrientationCompatible R φ' φ hφ' hφ h.2⟩⟩

/-- The orientation class relative to `φ` is the orientation class relative to every tubular
neighbourhood compatible with the complex orientations. -/
theorem IsOrientationClass.of_isOrientationCompatible {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (φ' : TubularNeighbourhood F N')
    (hφ' : φ'.IsOrientationCompatible (E := E)) : IsOrientationClass E R φ' u :=
  (isOrientationClass_iff_of_isOrientationCompatible R φ φ' hu.1 hφ' u).1 hu

end Independent

section Unique

open ThomClass

variable {P : TopCat.{u}} {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

omit [FiniteDimensional ℂ F] in
/-- Equal maps of pairs induce equal maps on relative singular cohomology with coefficients
in `R`, whatever the proofs that they map `A'` into `A`. -/
lemma relativeSingularCohomology.map_congr' {Y' Y : TopCat.{u}} {f g : Y' ⟶ Y} {A' : Set Y'}
    {A : Set Y} (e : f = g) (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map R (ModuleCat.of R R) f hf j =
      relativeSingularCohomology.map R (ModuleCat.of R R) g hg j := by
  subst e
  rfl

/-- **Excision for a tubular neighbourhood**: for `M` closed, the map
`H^j(P, P - M) → H^j(N, N - 0_N)` of a tubular neighbourhood is injective (it is the composite of
the excision isomorphism onto `φ(N)` and the pull-back along the homeomorphism `N ≅ φ(N)`). -/
theorem TubularNeighbourhood.injective_thomPullback (φ : TubularNeighbourhood F N)
    (hM : IsClosed M) (j : ℤ) : Function.Injective (φ.thomPullback R j).hom := by
  set V : Set P := range φ
  have hV : IsOpen V := φ.isOpenEmbedding.isOpen_range
  have hMV : M ⊆ V := fun y hy ↦ ⟨zeroSection F N ⟨y, hy⟩, φ.map_zeroSection ⟨y, hy⟩⟩
  let h := φ.isOpenEmbedding.isEmbedding.toHomeomorph
  let e : TopCat.of (TotalSpace F N) ⟶ TopCat.of V := TopCat.ofHom ⟨h, h.continuous⟩
  let e' : TopCat.of V ⟶ TopCat.of (TotalSpace F N) := TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hcomp : φ.toHom = e ≫ subspaceInclusion P V := by
    ext v
    rfl
  have he : (range (zeroSection F N))ᶜ ⊆ e ⁻¹' ((subspaceInclusion P V) ⁻¹' M)ᶜ :=
    fun v hv hvM ↦ hv (φ.preimage_eq_range_zeroSection ▸ (hvM : φ v ∈ M))
  have he' : ((subspaceInclusion P V) ⁻¹' M)ᶜ ⊆ e' ⁻¹' (range (zeroSection F N))ᶜ := by
    intro y hy hz
    refine hy ?_
    have : φ (h.symm y) ∈ M := (φ.preimage_eq_range_zeroSection.symm ▸ hz :
      h.symm y ∈ φ ⁻¹' M)
    have hy' : φ (h.symm y) = (y : P) := congrArg Subtype.val (h.apply_symm_apply y)
    change (y : P) ∈ M
    rwa [← hy']
  have hι : ((subspaceInclusion P V) ⁻¹' M)ᶜ ⊆ (subspaceInclusion P V) ⁻¹' (Mᶜ : Set P) :=
    fun _ hx ↦ hx
  have hthom : φ.thomPullback R j = relativeSingularCohomology.map R (ModuleCat.of R R)
      (subspaceInclusion P V) hι j ≫
        relativeSingularCohomology.map R (ModuleCat.of R R) e he j := by
    have h₁ : (φ.toHom ⁻¹' M)ᶜ ⊆ φ.toHom ⁻¹' (Mᶜ : Set P) := fun _ hx ↦ hx
    have h₂ : (range (zeroSection F N))ᶜ ⊆
        (𝟙 (TopCat.of (TotalSpace F N))) ⁻¹' (φ.toHom ⁻¹' M)ᶜ :=
      compl_subset_compl.mpr φ.preimage_eq_range_zeroSection.subset
    have h0 := relativeSingularCohomology.map_comp R (ModuleCat.of R R)
      (𝟙 (TopCat.of (TotalSpace F N))) φ.toHom h₂ h₁ j
    change relativeSingularCohomology.map R (ModuleCat.of R R) φ.toHom h₁ j ≫
      relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 _) h₂ j = _
    rw [← h0]
    exact (relativeSingularCohomology.map_congr' R (by rw [Category.id_comp, hcomp]) _ _ j).trans
      (relativeSingularCohomology.map_comp R (ModuleCat.of R R) e (subspaceInclusion P V) he hι j)
  rw [hthom]
  have hexc := cohomologyWithSupports.isIso_pullback_subspaceInclusion R hV hM hMV j
  have hinj₁ : Function.Injective (cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (subspaceInclusion P V) M j).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).1 hexc).1
  have hinj₂ : Function.Injective (relativeSingularCohomology.map R (ModuleCat.of R R) e he j).hom
      := by
    refine Function.LeftInverse.injective
      (g := (relativeSingularCohomology.map R (ModuleCat.of R R) e' he' j).hom) fun x ↦ ?_
    have h1 := relativeSingularCohomology.map_comp R (ModuleCat.of R R) e' e he' he j
    have hee : e' ≫ e = 𝟙 (TopCat.of V) := TopCat.ext fun y ↦ h.apply_symm_apply y
    have h2 : relativeSingularCohomology.map R (ModuleCat.of R R) (e' ≫ e)
        (fun _ hx ↦ he (he' hx)) j = 𝟙 _ :=
      (relativeSingularCohomology.map_congr' R hee (fun _ hx ↦ he (he' hx))
        (fun _ hx ↦ hx) j).trans (relativeSingularCohomology.map_id R (ModuleCat.of R R)
          (TopCat.of V) ((subspaceInclusion P V) ⁻¹' M)ᶜ j)
    exact congrArg (fun ψ ↦ ψ.hom x) (h1.symm.trans h2)
  exact hinj₂.comp hinj₁

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [ChartedSpace E P]
  {N' : M → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
  [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace F N')] [FiberBundle F N']
  [_root_.VectorBundle ℂ F N']

/-- **The orientation class is unique** (Fulton, §19.1): for `M` closed, the orientation classes
relative to any two tubular neighbourhoods compatible with the complex orientations are
equal. -/
theorem IsOrientationClass.eq (hM : IsClosed M) {φ : TubularNeighbourhood F N}
    {φ' : TubularNeighbourhood F N'}
    {u u' : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (hu' : IsOrientationClass E R φ' u') : u = u' := by
  have hu'' := hu'.of_isOrientationCompatible R φ hu.1
  exact φ.injective_thomPullback R hM _
    ((existsUnique_isThomClass (R := R) F N).unique hu.2 hu''.2)

end Unique

end MMP
