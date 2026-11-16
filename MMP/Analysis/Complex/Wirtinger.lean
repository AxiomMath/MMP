module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Wirtinger derivatives and the Cauchy–Riemann equations on `ℂⁿ`

For a function `f : ℂⁿ → ℂ` that is real differentiable at `z`, the *Wirtinger derivative*
`∂f/∂z̄ⱼ (z) = ½ (Df(z) eⱼ + i · Df(z) (i eⱼ))` measures the failure of the real derivative
`Df(z)` to be complex linear in the `j`-th direction. A real differentiable function all of whose
Wirtinger derivatives vanish at `z` is complex differentiable at `z` (the Cauchy–Riemann
equations), and the Wirtinger derivatives of a `C²` function commute.

Also, a normed algebra `𝔸` over a nontrivially normed field `𝕜` is a smooth ring for the model
`𝓘(𝕜, 𝔸)`; in particular `ℂ` is a smooth ring as a real manifold, which makes the smooth complex
valued functions on a real manifold a sheaf of rings.

## Main definitions

* `MMP.Analytic.dbarPartial`: the Wirtinger derivative `∂/∂z̄ⱼ` on `EuclideanSpace ℂ (Fin n)`.

## Main results

* `MMP.Analytic.differentiableAt_of_fderiv_smul_I`: a real differentiable map between complex
  normed spaces whose derivative commutes with multiplication by `i` is complex differentiable.
* `MMP.Analytic.differentiableAt_of_dbarPartial_eq_zero`: the Cauchy–Riemann equations.
* `MMP.Analytic.dbarPartial_eq_zero_of_differentiableAt`: the converse.
* `MMP.Analytic.dbarPartial_comm`: Wirtinger derivatives of a `C²` function commute.
* `MMP.Analytic.contDiffOn_complex_of_dbarPartial_eq_zero`: a real `C^∞` function annihilated
  by `∂̄` on an open set is complex `C^∞` there.
-/

@[expose] public section

open Complex

open scoped Manifold ContDiff

namespace MMP.Analytic

/-- A normed algebra is a smooth ring for the model `𝓘(𝕜, 𝔸)`: multiplication is a bounded
bilinear map. -/
instance contMDiffRing_modelWithCornersSelf {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : WithTop ℕ∞} :
    ContMDiffRing 𝓘(𝕜, 𝔸) n 𝔸 :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps, chartAt_self_eq]
      rw [contDiffOn_univ]
      exact contDiff_mul }

section CauchyRiemann

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A real continuous linear map between complex vector spaces commuting with `i` is complex
linear. -/
noncomputable def complexLinearOfCommI (L : E →L[ℝ] F) (h : ∀ v, L (I • v) = I • L v) :
    E →L[ℂ] F where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := by
    have hv : c • v = (c.re : ℂ) • v + (c.im : ℂ) • (I • v) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    have hLv : c • L v = (c.re : ℂ) • L v + (c.im : ℂ) • (I • L v) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    simp only [RingHom.id_apply]
    rw [hv, hLv, L.map_add, Complex.coe_smul, Complex.coe_smul, L.map_smul, L.map_smul, h,
      Complex.coe_smul, Complex.coe_smul]
  cont := L.continuous

/-- The complex linear map `complexLinearOfCommI L h` agrees with `L` pointwise. -/
@[simp]
lemma complexLinearOfCommI_apply (L : E →L[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) (v : E) : complexLinearOfCommI L h v = L v := rfl

/-- Restricting the scalars of `complexLinearOfCommI L h` to `ℝ` recovers `L`. -/
@[simp]
lemma restrictScalars_complexLinearOfCommI (L : E →L[ℝ] F)
    (h : ∀ v, L (I • v) = I • L v) : (complexLinearOfCommI L h).restrictScalars ℝ = L := rfl

/-- A real differentiable map between complex normed spaces whose derivative commutes with
multiplication by `i` is complex differentiable, with the same derivative. -/
theorem hasFDerivAt_complexLinearOfCommI {f : E → F} {z : E} (hf : DifferentiableAt ℝ f z)
    (h : ∀ v, fderiv ℝ f z (I • v) = I • fderiv ℝ f z v) :
    HasFDerivAt f (complexLinearOfCommI (fderiv ℝ f z) h) z :=
  hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt rfl

/-- A real differentiable map between complex normed spaces whose derivative commutes with
multiplication by `i` is complex differentiable. -/
theorem differentiableAt_of_fderiv_smul_I {f : E → F} {z : E} (hf : DifferentiableAt ℝ f z)
    (h : ∀ v, fderiv ℝ f z (I • v) = I • fderiv ℝ f z v) : DifferentiableAt ℂ f z :=
  (hasFDerivAt_complexLinearOfCommI hf h).differentiableAt

end CauchyRiemann

section Wirtinger

variable {n : ℕ}

/-- The Wirtinger derivative `∂f/∂z̄ⱼ (z) = ½ (Df(z) eⱼ + i · Df(z) (i eⱼ))` of a function on
`ℂⁿ = EuclideanSpace ℂ (Fin n)`, with `Df(z)` the real derivative. -/
noncomputable def dbarPartial (j : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z (EuclideanSpace.single j 1) +
    I * fderiv ℝ f z (EuclideanSpace.single j I))

/-- The Wirtinger derivative `∂f/∂z̄ⱼ (z)` vanishes if and only if
`Df(z) (i eⱼ) = i · Df(z) eⱼ`. -/
lemma dbarPartial_eq_zero_iff (j : Fin n) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    dbarPartial j f z = 0 ↔
      fderiv ℝ f z (EuclideanSpace.single j I) = I * fderiv ℝ f z (EuclideanSpace.single j 1) := by
  unfold dbarPartial
  constructor <;> intro h
  · linear_combination (-2 * I) * h + fderiv ℝ f z (EuclideanSpace.single j I) * I_sq
  · linear_combination (I / 2) * h + (1 / 2 : ℂ) * fderiv ℝ f z (EuclideanSpace.single j 1) * I_sq

/-- Scalar multiplication of a basis vector of `ℂⁿ`. -/
lemma smul_euclideanSpace_single (j : Fin n) (c a : ℂ) :
    c • EuclideanSpace.single j a = EuclideanSpace.single j (c * a) := by
  ext k
  by_cases h : k = j <;> simp [h]

/-- `ℂⁿ` is spanned over `ℝ` by the vectors `eⱼ` and `i eⱼ`. -/
lemma span_real_single_one_single_I :
    Submodule.span ℝ (Set.range (fun j : Fin n => EuclideanSpace.single j (1 : ℂ)) ∪
      Set.range (fun j : Fin n => EuclideanSpace.single j I)) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = ∑ j, ((v j).re • EuclideanSpace.single j (1 : ℂ) +
      (v j).im • EuclideanSpace.single j I) := by
    ext k
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, WithLp.ofLp_sum,
      Finset.sum_apply]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [ite_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im (v k)).symm
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, rfl⟩))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))

/-- **Cauchy–Riemann.** A function on `ℂⁿ` that is real differentiable at `z` with vanishing
Wirtinger derivatives `∂f/∂z̄ⱼ (z)` is complex differentiable at `z`. -/
theorem differentiableAt_of_dbarPartial_eq_zero {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f z)
    (h : ∀ j, dbarPartial j f z = 0) : DifferentiableAt ℂ f z := by
  refine differentiableAt_of_fderiv_smul_I hf fun v => ?_
  set L := fderiv ℝ f z
  let S : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    { carrier := {v | L (I • v) = I • L v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_add, L.map_add, L.map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_comm, L.map_smul, L.map_smul, ha, smul_comm] }
  have hS : Submodule.span ℝ (Set.range (fun j : Fin n => EuclideanSpace.single j (1 : ℂ)) ∪
      Set.range (fun j : Fin n => EuclideanSpace.single j I)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · change L (I • EuclideanSpace.single j (1 : ℂ)) = I • L (EuclideanSpace.single j 1)
      rw [smul_euclideanSpace_single, mul_one, smul_eq_mul]
      exact (dbarPartial_eq_zero_iff j f z).1 (h j)
    · change L (I • EuclideanSpace.single j I) = I • L (EuclideanSpace.single j I)
      have hj := (dbarPartial_eq_zero_iff j f z).1 (h j)
      have hII : I • EuclideanSpace.single j I = (-1 : ℝ) • EuclideanSpace.single j (1 : ℂ) := by
        rw [smul_euclideanSpace_single, Complex.I_mul_I]
        ext k
        by_cases hk : k = j <;> simp [hk]
      rw [hII, L.map_smul, smul_eq_mul, hj, ← mul_assoc, Complex.I_mul_I]
      simp [L]
  exact hS (span_real_single_one_single_I ▸ Submodule.mem_top)

/-- A complex differentiable function has vanishing Wirtinger derivatives. -/
theorem dbarPartial_eq_zero_of_differentiableAt {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℂ f z) (j : Fin n) :
    dbarPartial j f z = 0 := by
  rw [dbarPartial_eq_zero_iff, hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_euclideanSpace_single, mul_one]

/-- A real differentiable function on an open set is complex differentiable there iff all its
Wirtinger derivatives vanish there. -/
theorem differentiableOn_iff_dbarPartial_eq_zero {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) :
    DifferentiableOn ℂ f U ↔ ∀ z ∈ U, ∀ j, dbarPartial j f z = 0 :=
  ⟨fun h z hz j => dbarPartial_eq_zero_of_differentiableAt (h.differentiableAt (hU.mem_nhds hz)) j,
    fun h z hz => (differentiableAt_of_dbarPartial_eq_zero
      (hf.differentiableAt (hU.mem_nhds hz)) (h z hz)).differentiableWithinAt⟩

/-- The derivative of a Wirtinger derivative, in terms of the second real derivative. -/
lemma hasFDerivAt_dbarPartial (k : Fin n) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    HasFDerivAt (dbarPartial k f)
      ((1 / 2 : ℂ) • ((fderiv ℝ (fderiv ℝ f) z).flip (EuclideanSpace.single k 1) +
        I • (fderiv ℝ (fderiv ℝ f) z).flip (EuclideanSpace.single k I))) z := by
  have h1 := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single k (1 : ℂ)) z)
  have h2 := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single k I) z)
  have := ((h1.add (h2.const_smul I)).const_smul (1 / 2 : ℂ))
  simp only [ContinuousLinearMap.comp_zero, zero_add] at this
  have heq : dbarPartial k f = (1 / 2 : ℂ) • ((fun y => fderiv ℝ f y (EuclideanSpace.single k 1))
      + I • fun y => fderiv ℝ f y (EuclideanSpace.single k I)) := by
    funext y
    simp only [dbarPartial, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rwa [heq]

/-- Wirtinger derivatives of a `C²` function commute. -/
theorem dbarPartial_comm (j k : Fin n) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 2 f z) :
    dbarPartial j (dbarPartial k f) z = dbarPartial k (dbarPartial j f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs : IsSymmSndFDerivAt ℝ f z :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [dbarPartial, dbarPartial, (hasFDerivAt_dbarPartial k hd).fderiv,
    (hasFDerivAt_dbarPartial j hd).fderiv]
  simp only [FunLike.coe_smul, FunLike.coe_add,
    Pi.smul_apply, Pi.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hs (EuclideanSpace.single j 1) (EuclideanSpace.single k 1),
    hs (EuclideanSpace.single j I) (EuclideanSpace.single k 1),
    hs (EuclideanSpace.single j 1) (EuclideanSpace.single k I),
    hs (EuclideanSpace.single j I) (EuclideanSpace.single k I)]
  ring

section Holomorphy

open Filter Topology

/-- A complex linear functional `L` on `ℂⁿ` is `∑ₖ L(eₖ) · zₖ`, the sum of the coordinate
projections weighted by its values on the standard basis. -/
lemma clm_eq_sum_single_smul_proj (L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
    L = ∑ k, L (EuclideanSpace.single k 1) •
      (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) := by
  ext1 v
  have hv : v = ∑ k, v k • EuclideanSpace.single k (1 : ℂ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, mul_comm]

/-- The derivative in direction `v` of `w ↦ Df(w) u` is the second derivative `D²f(z) v u`. -/
lemma fderiv_fderiv_apply {f : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hd : DifferentiableAt ℝ (fderiv ℝ f) z) (u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => fderiv ℝ f w u) z v = fderiv ℝ (fderiv ℝ f) z v u := by
  rw [fderiv_clm_apply hd (differentiableAt_const u)]
  simp

/-- A directional derivative of a smooth function annihilated by `∂̄` is annihilated by `∂̄`. -/
lemma dbarPartial_fderiv_apply_eq_zero {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hcr : ∀ z ∈ U, ∀ j, dbarPartial j f z = 0) (v : EuclideanSpace ℂ (Fin n))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) (j : Fin n) :
    dbarPartial j (fun w => fderiv ℝ f w v) z = 0 := by
  have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hfz.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ f z :=
    hfz.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hloc : (fun w => fderiv ℝ f w (EuclideanSpace.single j I)) =ᶠ[𝓝 z]
      fun w => I * fderiv ℝ f w (EuclideanSpace.single j 1) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw =>
      (dbarPartial_eq_zero_iff j f w).1 (hcr w hw j)
  have hd1 : DifferentiableAt ℝ (fun w => fderiv ℝ f w (EuclideanSpace.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have hsw : ∀ u, fderiv ℝ (fun w => fderiv ℝ f w v) z u =
      fderiv ℝ (fun w => fderiv ℝ f w u) z v := fun u => by
    rw [fderiv_fderiv_apply hd, fderiv_fderiv_apply hd, hs]
  rw [dbarPartial_eq_zero_iff, hsw, hsw, hloc.fderiv_eq, fderiv_const_mul hd1]
  simp

/-- **Smooth solutions of the Cauchy–Riemann equations are holomorphic**: a real `C^∞` function
on an open `U ⊆ ℂⁿ` all of whose Wirtinger derivatives vanish on `U` is complex `C^∞` on `U`. -/
theorem contDiffOn_complex_of_dbarPartial_eq_zero {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hcr : ∀ z ∈ U, ∀ j, dbarPartial j f z = 0) : ContDiffOn ℂ ∞ f U := by
  rw [contDiffOn_infty]
  intro m
  induction m generalizing f with
  | zero => exact contDiffOn_zero.2 hf.continuousOn
  | succ m ih =>
    have hdC : DifferentiableOn ℂ f U :=
      (differentiableOn_iff_dbarPartial_eq_zero hU (hf.differentiableOn (by simp))).2 hcr
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
    let g : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun k w =>
      fderiv ℝ f w (EuclideanSpace.single k 1)
    have hg : ∀ k, ContDiffOn ℂ m (g k) U := fun k =>
      ih (hfd.clm_apply contDiffOn_const) fun z hz j =>
        dbarPartial_fderiv_apply_eq_zero hU hf hcr _ hz j
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hdC, by simp, ?_⟩
    have hsum : ContDiffOn ℂ m (fun z => ∑ k ∈ Finset.univ, g k z •
        (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)) U :=
      ContDiffOn.sum fun k _ => (hg k).smul contDiffOn_const
    refine hsum.congr fun z hz => ?_
    have hz' : DifferentiableAt ℂ f z := hdC.differentiableAt (hU.mem_nhds hz)
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ f z)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, hz'.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars']

end Holomorphy

end Wirtinger

end MMP.Analytic
