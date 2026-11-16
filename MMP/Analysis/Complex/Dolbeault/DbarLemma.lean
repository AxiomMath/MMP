module

public import MMP.Analysis.Complex.Dolbeault.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder

/-!
# The Dolbeault–Grothendieck lemma

Let `U ⊆ ℂⁿ` be open and `ω` a smooth `(0, q + 1)`-form on `U` with `∂̄ ω = 0`. Then every point
of `U` has an open neighbourhood `V ⊆ U` on which `ω = ∂̄ u` for a smooth `(0, q)`-form `u`.

The proof is by induction on the largest index `k` such that `dz̄_k` occurs in `ω`. Write
`ω = dz̄_k ∧ α + β` where neither `α` nor `β` involves `dz̄_k`. Closedness of `ω` forces the
coefficients of `α` to be holomorphic in the variables `z_j`, `j > k`. Solving
`∂G_J/∂z̄_k = χ(z_k) α_J` in the single variable `z_k`, with a cutoff `χ` equal to `1` near the
point and the other variables as parameters, gives coefficients `G_J` that are again holomorphic
in `z_j` for `j > k`; then `ω - ∂̄ G` only involves `dz̄_0, …, dz̄_{k-1}` near the point, and the
induction hypothesis applies.

The one-variable equation is solved by the Cauchy transform
`u(z, y) = -(1/π) ∫ g(ζ, y) / (ζ - z) dA(ζ)` of a smooth function `g` compactly supported in `ζ`:
it is smooth, satisfies `∂u/∂z̄ = g`, and is holomorphic in each parameter in which `g` is. These
three properties are taken as a hypothesis `hT` of the results below.

## Main results

* `MMP.Analytic.exists_dbarPartial_eq_of_cauchyTransform`: the one-variable equation
  `∂G/∂z̄_k = f` with holomorphic dependence on the other variables, near any point.
* `MMP.Analytic.exists_dbarForm_eq_of_dbarForm_eq_zero`: the Dolbeault–Grothendieck lemma for
  coefficient families.
* `MMP.Analytic.exists_dbarSections_eq_of_dbarSections_eq_zero`: the same for sections of the
  sheaves `ℰ^{0,q}`.

## Implementation notes

Points of `ℂⁿ` are split as `(z_k, y)` with `y : Fin n → ℂ` the full coordinate vector whose
`k`-th entry is ignored (`MMP.Analytic.insertCoord`, `MMP.Analytic.splitCoord`), so that the
parameter space of the Cauchy transform is `Fin n → ℂ`.

## References

* [Hörmander, *An introduction to complex analysis in several variables*, Theorem 2.3.3]
* [Griffiths–Harris, *Principles of algebraic geometry*, Ch. 0, §2]
-/

@[expose] public section

open Complex Filter Topology Set

open scoped ContDiff Manifold

namespace MMP.Analytic

variable {n : ℕ}

section Coordinates

/-- The point of `ℂⁿ` with `k`-th coordinate `p.1` and the other coordinates those of `p.2`. -/
noncomputable def insertCoord (k : Fin n) (p : ℂ × (Fin n → ℂ)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 p.2 + EuclideanSpace.single k (p.1 - p.2 k)

/-- The `k`-th coordinate of `w`, together with the coordinate vector of `w` with its `k`-th
coordinate replaced by `c`. -/
noncomputable def splitCoord (k : Fin n) (c : ℂ) (w : EuclideanSpace ℂ (Fin n)) :
    ℂ × (Fin n → ℂ) :=
  (w k, WithLp.ofLp (w + EuclideanSpace.single k (c - w k)))

/-- The `i`-th coordinate of `insertCoord k p` is `p.1` if `i = k` and `p.2 i` otherwise. -/
lemma insertCoord_apply (k : Fin n) (p : ℂ × (Fin n → ℂ)) (i : Fin n) :
    insertCoord k p i = if i = k then p.1 else p.2 i := by
  by_cases h : i = k <;> simp [insertCoord, h]

/-- The `i`-th entry of `(splitCoord k c w).2` is `c` if `i = k` and `w i` otherwise. -/
lemma splitCoord_snd_apply (k : Fin n) (c : ℂ) (w : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (splitCoord k c w).2 i = if i = k then c else w i := by
  by_cases h : i = k <;> simp [splitCoord, h]

/-- For `j ≠ k`, the `j`-th entry of `(splitCoord k c w).2` is `w j`. -/
lemma splitCoord_snd_apply_of_ne {k j : Fin n} (hjk : j ≠ k) (c : ℂ)
    (w : EuclideanSpace ℂ (Fin n)) : (splitCoord k c w).2 j = w j := by
  rw [splitCoord_snd_apply, ite_eq_right hjk]

/-- `insertCoord k` is a left inverse of `splitCoord k c`. -/
lemma insertCoord_splitCoord (k : Fin n) (c : ℂ) (w : EuclideanSpace ℂ (Fin n)) :
    insertCoord k (splitCoord k c w) = w := by
  ext i
  rw [insertCoord_apply, splitCoord_snd_apply]
  by_cases h : i = k <;> simp [h, splitCoord]

/-- Replacing the `k`-th coordinate of `w` by `t` replaces the first component of
`splitCoord k c w` by `t` and leaves the second unchanged. -/
lemma splitCoord_add_single_self (k : Fin n) (c : ℂ) (w : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    splitCoord k c (w + EuclideanSpace.single k (t - w k)) = (t, (splitCoord k c w).2) := by
  refine Prod.ext (by simp [splitCoord]) ?_
  funext i
  rw [splitCoord_snd_apply, splitCoord_snd_apply]
  by_cases h : i = k <;> simp [h]

/-- For `j ≠ k`, replacing the `j`-th coordinate of `w` by `t` updates the `j`-th entry of the
second component of `splitCoord k c w` to `t`. -/
lemma splitCoord_add_single_of_ne {k j : Fin n} (hjk : j ≠ k) (c : ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    splitCoord k c (w + EuclideanSpace.single j (t - w j)) =
      (w k, Function.update (splitCoord k c w).2 j t) := by
  refine Prod.ext (by simp [splitCoord, Ne.symm hjk]) ?_
  funext i
  rw [splitCoord_snd_apply]
  dsimp only
  by_cases h : i = j
  · subst h; simp [hjk]
  · rw [Function.update_of_ne h, splitCoord_snd_apply]
    by_cases h' : i = k <;> simp [h, h']

/-- For `j ≠ k`, updating the `j`-th entry of `y` to `t` changes `insertCoord k (ζ, y)` by
`(t - y j)` in the `j`-th coordinate. -/
lemma insertCoord_update_of_ne {k j : Fin n} (hjk : j ≠ k) (ζ : ℂ) (y : Fin n → ℂ) (t : ℂ) :
    insertCoord k (ζ, Function.update y j t) =
      insertCoord k (ζ, y) + EuclideanSpace.single j (t - y j) := by
  ext i
  simp only [PiLp.add_apply, insertCoord_apply]
  by_cases h : i = j
  · subst h; simp [hjk]
  · by_cases h' : i = k <;> simp [h, h', Ne.symm hjk]

/-- Changing the first component from `ζ'` to `ζ` changes `insertCoord k (·, y)` by `ζ - ζ'` in
the `k`-th coordinate. -/
lemma insertCoord_eq_add (k : Fin n) (ζ ζ' : ℂ) (y : Fin n → ℂ) :
    insertCoord k (ζ, y) = insertCoord k (ζ', y) + EuclideanSpace.single k (ζ - ζ') := by
  ext i
  simp only [PiLp.add_apply, insertCoord_apply]
  by_cases h : i = k <;> simp [h]

/-- `insertCoord k` is real smooth. -/
lemma contDiff_insertCoord (k : Fin n) {m : WithTop ℕ∞} : ContDiff ℝ m (insertCoord k) := by
  have h1 : ContDiff ℝ m
      (fun p : ℂ × (Fin n → ℂ) => (WithLp.toLp 2 p.2 : EuclideanSpace ℂ (Fin n))) :=
    PiLp.contDiff_toLp.comp contDiff_snd
  have h2 : ContDiff ℝ m
      (fun p : ℂ × (Fin n → ℂ) => (p.1 - p.2 k) • EuclideanSpace.single k (1 : ℂ)) :=
    (contDiff_fst.sub ((contDiff_apply ℝ (fun _ : Fin n ↦ ℂ) k).comp contDiff_snd)).fun_smul contDiff_const
  have e : insertCoord k = fun p : ℂ × (Fin n → ℂ) =>
      (WithLp.toLp 2 p.2 : EuclideanSpace ℂ (Fin n)) +
        (p.1 - p.2 k) • EuclideanSpace.single k (1 : ℂ) := by
    funext p; simp [insertCoord, smul_euclideanSpace_single]
  rw [e]; exact h1.add h2

/-- `splitCoord k c` is real smooth. -/
lemma contDiff_splitCoord (k : Fin n) (c : ℂ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (splitCoord k c) := by
  have hk : ContDiff ℝ m (fun w : EuclideanSpace ℂ (Fin n) => w k) :=
    ((EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  have h2 : ContDiff ℝ m
      (fun w : EuclideanSpace ℂ (Fin n) => (c - w k) • EuclideanSpace.single k (1 : ℂ)) :=
    (contDiff_const.sub hk).fun_smul contDiff_const
  have e : splitCoord k c = fun w : EuclideanSpace ℂ (Fin n) =>
      (w k, WithLp.ofLp (w + (c - w k) • EuclideanSpace.single k (1 : ℂ))) := by
    funext w; simp [splitCoord, smul_euclideanSpace_single]
  rw [e]
  exact hk.prodMk (PiLp.contDiff_ofLp.comp (contDiff_id.add h2))

end Coordinates

section CoordinateLines

/-- The real derivative at `c` of the `j`-th coordinate line `t ↦ p + (t - c) e_j` is
`v ↦ v e_j`. -/
lemma hasFDerivAt_add_single (p : EuclideanSpace ℂ (Fin n)) (j : Fin n) (c : ℂ) :
    HasFDerivAt (fun t : ℂ => p + EuclideanSpace.single j (t - c))
      ((ContinuousLinearMap.id ℝ ℂ).smulRight (EuclideanSpace.single j (1 : ℂ))) c := by
  have h := (((hasFDerivAt_id (𝕜 := ℝ) c).sub_const c).smul_const
    (EuclideanSpace.single j (1 : ℂ))).const_add p
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [smul_euclideanSpace_single]

/-- The derivative of `f` along the `j`-th coordinate line through `p`. -/
lemma hasFDerivAt_comp_add_single {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {p : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f p) (j : Fin n) (c : ℂ) :
    HasFDerivAt (fun t : ℂ => f (p + EuclideanSpace.single j (t - c)))
      ((fderiv ℝ f p).comp ((ContinuousLinearMap.id ℝ ℂ).smulRight
        (EuclideanSpace.single j (1 : ℂ)))) c := by
  have hp : p + EuclideanSpace.single j (c - c) = p := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f p) (p + EuclideanSpace.single j (c - c)) := by
    rw [hp]; exact hf.hasFDerivAt
  exact hf'.comp c (hasFDerivAt_add_single p j c)

/-- The derivative of `f` along the `j`-th coordinate line through `p`, applied to `v`, is the
derivative of `f` at `p` applied to `v e_j`. -/
lemma fderiv_comp_add_single_apply {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {p : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f p) (j : Fin n) (c v : ℂ) :
    fderiv ℝ (fun t : ℂ => f (p + EuclideanSpace.single j (t - c))) c v =
      fderiv ℝ f p (EuclideanSpace.single j v) := by
  rw [(hasFDerivAt_comp_add_single hf j c).fderiv]
  simp [smul_euclideanSpace_single]

/-- A real differentiable function with `∂f/∂z̄ⱼ (p) = 0` is complex differentiable along the
`j`-th coordinate line through `p`. -/
lemma differentiableAt_comp_add_single {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {p : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f p) {j : Fin n}
    (h : dbarPartial j f p = 0) (c : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => f (p + EuclideanSpace.single j (t - c))) c := by
  have hd := (hasFDerivAt_comp_add_single hf j c).differentiableAt
  refine differentiableAt_of_fderiv_smul_I hd fun v => ?_
  rw [fderiv_comp_add_single_apply hf, fderiv_comp_add_single_apply hf]
  have h1 := (dbarPartial_eq_zero_iff j f p).1 h
  have hv : ∀ w : ℂ, EuclideanSpace.single j w =
      w.re • EuclideanSpace.single j (1 : ℂ) + w.im • EuclideanSpace.single j I := by
    intro w
    ext i; by_cases hi : i = j <;> simp [hi]
  rw [hv (I • v), hv v, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.real_smul]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Conversely, complex differentiability along the `j`-th coordinate line gives
`∂f/∂z̄ⱼ (p) = 0`. -/
lemma dbarPartial_eq_zero_of_differentiableAt_comp_add_single {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {p : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f p) {j : Fin n} {c : ℂ}
    (h : DifferentiableAt ℂ (fun t : ℂ => f (p + EuclideanSpace.single j (t - c))) c) :
    dbarPartial j f p = 0 := by
  rw [dbarPartial_eq_zero_iff, ← fderiv_comp_add_single_apply hf j c,
    ← fderiv_comp_add_single_apply hf j c, h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]

end CoordinateLines

section FormAlgebra

/-- `∂f/∂z̄ⱼ (z) = 0` when `f` vanishes near `z`. -/
lemma dbarPartial_eq_zero_of_eventuallyEq_zero {j : Fin n} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (h : f =ᶠ[𝓝 z] fun _ => 0) : dbarPartial j f z = 0 := by
  rw [dbarPartial_congr h]
  simp [dbarPartial]

/-- At a point where `f` and `g` are real differentiable, `∂(f - g)/∂z̄ⱼ = ∂f/∂z̄ⱼ - ∂g/∂z̄ⱼ`. -/
lemma dbarPartial_sub {j : Fin n} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (fun w => f w - g w) z = dbarPartial j f z - dbarPartial j g z := by
  simp only [dbarPartial, fderiv_fun_sub hf hg]
  simp; ring

/-- `∂̄` of a sum of coefficient families, differentiable at `z`, is the sum of their `∂̄` at
`z`. -/
lemma dbarForm_add {θ η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hθ : ∀ J, DifferentiableAt ℝ (θ J) z)
    (hη : ∀ J, DifferentiableAt ℝ (η J) z) (I : Finset (Fin n)) :
    dbarForm (fun J w => θ J w + η J w) I z = dbarForm θ I z + dbarForm η I z := by
  simp only [dbarForm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbarPartial_add (hθ _) (hη _)]
  ring

/-- `∂̄` of a difference of coefficient families, differentiable at `z`, is the difference of
their `∂̄` at `z`. -/
lemma dbarForm_sub {θ η : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hθ : ∀ J, DifferentiableAt ℝ (θ J) z)
    (hη : ∀ J, DifferentiableAt ℝ (η J) z) (I : Finset (Fin n)) :
    dbarForm (fun J w => θ J w - η J w) I z = dbarForm θ I z - dbarForm η I z := by
  simp only [dbarForm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbarPartial_sub (hθ _) (hη _)]
  ring

/-- The sign `dolbeaultSign j I` squares to `1`. -/
lemma dolbeaultSign_mul_self (j : Fin n) (I : Finset (Fin n)) :
    dolbeaultSign j I * dolbeaultSign j I = 1 := by
  simp only [dolbeaultSign, ← mul_pow]
  norm_num

/-- The sign `dolbeaultSign j I` is nonzero. -/
lemma dolbeaultSign_ne_zero (j : Fin n) (I : Finset (Fin n)) : dolbeaultSign j I ≠ 0 :=
  pow_ne_zero _ (by norm_num)

end FormAlgebra

section OneVariable

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

/-- A product of open subsets of `ℂ` is open in `ℂⁿ`. -/
lemma isOpen_setOf_forall_mem {W : Fin n → Set ℂ} (hW : ∀ j, IsOpen (W j)) :
    IsOpen {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j =>
    (hW j).preimage (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous

/-- A smooth cutoff on a finite-dimensional real normed space: equal to `1` on an open
neighbourhood `W'` of a compact `L` and vanishing off a compact subset of a given open `W ⊇ L`. -/
lemma exists_contDiff_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {L W : Set F} (hL : IsCompact L) (hW : IsOpen W) (hLW : L ⊆ W) :
    ∃ χ : F → ℝ, ContDiff ℝ ∞ χ ∧ ∃ W' : Set F, IsOpen W' ∧ L ⊆ W' ∧ W' ⊆ W ∧
      (∀ z ∈ W', χ z = 1) ∧ ∃ Lc : Set F, IsCompact Lc ∧ Lc ⊆ W ∧ ∀ z ∉ Lc, χ z = 0 := by
  have : ProperSpace F := FiniteDimensional.proper_real F
  obtain ⟨δ, hδ, hsub⟩ := hL.exists_cthickening_subset_open hW hLW
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, F) (n := ⊤)
    hL.isClosed (s := L) (t := Metric.thickening δ L)
    (by rw [Metric.isOpen_thickening.interior_eq]; exact Metric.self_subset_thickening hδ L)
  obtain ⟨U₀, hU₀, hLU₀, hU₀1⟩ := mem_nhdsSet_iff_exists.1 h1
  exact ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, U₀ ∩ Metric.thickening δ L,
    hU₀.inter Metric.isOpen_thickening,
    fun z hz => ⟨hLU₀ hz, Metric.self_subset_thickening hδ L hz⟩,
    fun z hz => hsub (Metric.thickening_subset_cthickening _ _ hz.2), fun z hz => hU₀1 hz.1,
    Metric.cthickening δ L, hL.cthickening, hsub,
    fun z hz => h0 z fun h => hz (Metric.thickening_subset_cthickening _ _ h)⟩

/-- If `ζ ∈ W k` and `y j ∈ W j` for `j ≠ k`, then `insertCoord k (ζ, y)` lies in `∏ W_j`. -/
lemma insertCoord_mem_setOf_forall_mem {W : Fin n → Set ℂ} {k : Fin n} {y : Fin n → ℂ}
    (hy : ∀ j, j ≠ k → y j ∈ W j) {ζ : ℂ} (hζ : ζ ∈ W k) :
    insertCoord k (ζ, y) ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j} := by
  intro j
  rw [insertCoord_apply]
  by_cases hj : j = k
  · subst hj
    simpa using hζ
  · simpa [hj] using hy j hj

/-- A smooth cutoff `χ(ζ)`, supported in a compact `Lc ⊆ W k`, times `f ∘ insertCoord k` is
smooth on `univ ×ˢ {y | ∀ j ≠ k, y j ∈ W j}` when `f` is smooth on `∏ W_j`. -/
lemma contDiffOn_cutoff_mul_comp_insertCoord {W : Fin n → Set ℂ} (hW : ∀ j, IsOpen (W j))
    {k : Fin n} {χ : ℂ → ℝ} (hχs : ContDiff ℝ ∞ χ) {Lc : Set ℂ} (hLc : IsCompact Lc)
    (hLcW : Lc ⊆ W k) (hχ0 : ∀ z ∉ Lc, χ z = 0) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z | ∀ j, z j ∈ W j}) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (Fin n → ℂ) => (χ p.1 : ℂ) * f (insertCoord k p))
      (univ ×ˢ {y | ∀ j, j ≠ k → y j ∈ W j}) := by
  rintro ⟨ζ, y⟩ ⟨-, hy⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hζ : ζ ∈ W k
  · exact ((ofRealCLM.contDiff.comp hχs).contDiffAt.comp _ contDiffAt_fst).mul
      ((hf.contDiffAt ((isOpen_setOf_forall_mem hW).mem_nhds
        (insertCoord_mem_setOf_forall_mem hy hζ))).comp _ (contDiff_insertCoord k).contDiffAt)
  · have ho : IsOpen {p : ℂ × (Fin n → ℂ) | p.1 ∈ Lcᶜ} :=
      hLc.isClosed.isOpen_compl.preimage continuous_fst
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [ho.mem_nhds (show ζ ∈ Lcᶜ from fun h => hζ (hLcW h))] with p hp
    simp [hχ0 p.1 hp]

/-- For `j ≠ k`, if `f` is smooth on `∏ W_j` and holomorphic in `z_j` there, then
`t ↦ χ(ζ) f(insertCoord k (ζ, update y j t))` is complex differentiable at `y j`, for a cutoff
`χ` vanishing off `Lc ⊆ W k`. -/
lemma differentiableAt_cutoff_mul_comp_insertCoord_update {W : Fin n → Set ℂ}
    (hW : ∀ j, IsOpen (W j)) {k j : Fin n} (hjk : j ≠ k) {χ : ℂ → ℝ} {Lc : Set ℂ}
    (hLcW : Lc ⊆ W k) (hχ0 : ∀ z ∉ Lc, χ z = 0) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z | ∀ j, z j ∈ W j})
    (hfj : ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}, dbarPartial j f z = 0)
    (ζ : ℂ) {y : Fin n → ℂ} (hy : ∀ j, j ≠ k → y j ∈ W j) :
    DifferentiableAt ℂ
      (fun t : ℂ => (χ ζ : ℂ) * f (insertCoord k (ζ, Function.update y j t))) (y j) := by
  by_cases hζ : ζ ∈ W k
  · have hpU := insertCoord_mem_setOf_forall_mem hy hζ
    have hfd : DifferentiableAt ℝ f (insertCoord k (ζ, y)) :=
      (hf.contDiffAt ((isOpen_setOf_forall_mem hW).mem_nhds hpU)).differentiableAt (by simp)
    refine ((differentiableAt_comp_add_single hfd (hfj _ hpU) (y j)).const_mul
      ((χ ζ : ℝ) : ℂ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [insertCoord_update_of_ne hjk]
  · simp only [hχ0 ζ fun h => hζ (hLcW h), Complex.ofReal_zero, zero_mul]
    exact differentiableAt_const _

include hT in
/-- **`∂̄` in one variable with parameters.** Let `W₀, …, W_{n-1} ⊆ ℂ` be open and `L ⊆ W_k`
compact. There is an open `W'` with `L ⊆ W' ⊆ W_k` such that every smooth `f` on the product
`Ω = ∏ W_j` is `∂G/∂z̄_k` at the points of `Ω` with `z_k ∈ W'`, for a smooth `G` on `Ω` which is
holomorphic in `z_j` (`j ≠ k`) whenever `f` is. -/
theorem exists_dbarPartial_eq_of_cauchyTransform {W : Fin n → Set ℂ} (hW : ∀ j, IsOpen (W j))
    (k : Fin n) {L : Set ℂ} (hL : IsCompact L) (hLW : L ⊆ W k) :
    ∃ W' : Set ℂ, IsOpen W' ∧ L ⊆ W' ∧ W' ⊆ W k ∧
      ∀ f : EuclideanSpace ℂ (Fin n) → ℂ, ContDiffOn ℝ ∞ f {z | ∀ j, z j ∈ W j} →
        ∃ G : EuclideanSpace ℂ (Fin n) → ℂ, ContDiffOn ℝ ∞ G {z | ∀ j, z j ∈ W j} ∧
          (∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}, z k ∈ W' →
            dbarPartial k G z = f z) ∧
          ∀ j ≠ k, (∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j},
            dbarPartial j f z = 0) →
            ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}, dbarPartial j G z = 0 := by
  set U := {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}
  have hU : IsOpen U := isOpen_setOf_forall_mem hW
  obtain ⟨χ, hχs, W', hW', hLW', hW'W, hχ1, Lc, hLc, hLcW, hχ0⟩ :=
    exists_contDiff_cutoff hL (hW k) hLW
  refine ⟨W', hW', hLW', hW'W, fun f hf => ?_⟩
  let P : Set (Fin n → ℂ) := {y | ∀ j, j ≠ k → y j ∈ W j}
  have hP : IsOpen P := by
    simp only [P, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hW j).preimage (continuous_apply j)
  have hsplit : ∀ w ∈ U, (splitCoord k 0 w).2 ∈ P := fun w hw j hj => by
    rw [splitCoord_snd_apply_of_ne hj]
    exact hw j
  let g : ℂ × (Fin n → ℂ) → ℂ := fun p => χ p.1 * f (insertCoord k p)
  have hsupp : ∀ ζ ∉ Lc, ∀ y ∈ P, g (ζ, y) = 0 := by
    intro ζ hζ y _
    simp [g, hχ0 ζ hζ]
  obtain ⟨hTs, hTd, hTh⟩ := hT P Lc g hP hLc
    (contDiffOn_cutoff_mul_comp_insertCoord hW hχs hLc hLcW hχ0 hf) hsupp
  set T : ℂ × (Fin n → ℂ) → ℂ :=
    fun p => -(1 / (Real.pi : ℂ)) * ∫ ζ : ℂ, g (ζ, p.2) / (ζ - p.1)
  let G : EuclideanSpace ℂ (Fin n) → ℂ := fun w => T (splitCoord k 0 w)
  have hGs : ContDiffOn ℝ ∞ G U :=
    hTs.comp (contDiff_splitCoord k 0).contDiffOn fun w hw => ⟨trivial, hsplit w hw⟩
  have hGd : ∀ z ∈ U, DifferentiableAt ℝ G z := fun z hz =>
    (hGs.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  refine ⟨G, hGs, fun z hz hzk => ?_, fun j hjk hfj z hz => ?_⟩
  · unfold dbarPartial
    rw [← fderiv_comp_add_single_apply (hGd z hz) k (z k),
      ← fderiv_comp_add_single_apply (hGd z hz) k (z k)]
    have e : (fun t => G (z + EuclideanSpace.single k (t - z k))) =
        fun t => T (t, (splitCoord k 0 z).2) :=
      funext fun t => by simp only [G, splitCoord_add_single_self]
    rw [e, hTd (z k) _ (hsplit z hz)]
    simp only [g]
    rw [show ((z k, (splitCoord k 0 z).2) : ℂ × (Fin n → ℂ)) = splitCoord k 0 z from rfl,
      insertCoord_splitCoord, hχ1 _ hzk, Complex.ofReal_one, one_mul]
  · refine dbarPartial_eq_zero_of_differentiableAt_comp_add_single (hGd z hz) (c := z j) ?_
    have e : (fun t => G (z + EuclideanSpace.single j (t - z j))) =
        fun t => T (z k, Function.update (splitCoord k 0 z).2 j t) :=
      funext fun t => by simp only [G, splitCoord_add_single_of_ne hjk]
    rw [e]
    have := hTh j (fun ζ _ hy =>
      differentiableAt_cutoff_mul_comp_insertCoord_update hW hjk hLcW hχ0 hf hfj ζ hy)
      (z k) (splitCoord k 0 z).2 (hsplit z hz)
    rwa [splitCoord_snd_apply_of_ne hjk] at this

section Induction

/-- If `θ` is `∂̄`-closed and its coefficients vanish whenever an index `> k` occurs, then for
`J ⊆ {i < k}` the coefficient `θ_{k ∪ J}` is holomorphic in `z_j` for every `j > k`. -/
lemma dbarPartial_insert_eq_zero_of_dbarForm_eq_zero {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} {k : Fin n}
    (hvan : ∀ I : Finset (Fin n), (∃ i ∈ I, (k : ℕ) < i) → ∀ z ∈ U, θ I z = 0)
    (hcl : ∀ I, ∀ z ∈ U, dbarForm θ I z = 0) {J : Finset (Fin n)} (hJ : ∀ i ∈ J, (i : ℕ) < k)
    {j : Fin n} (hj : (k : ℕ) < j) {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) :
    dbarPartial j (θ (insert k J)) z = 0 := by
  have hjJ : j ∉ insert k J := by
    rw [Finset.mem_insert, not_or]
    exact ⟨fun h => by rw [h] at hj; exact lt_irrefl _ hj,
      fun h => absurd (hJ j h) (by omega)⟩
  have h := hcl (insert j (insert k J)) z hz
  unfold dbarForm at h
  rw [Finset.sum_eq_single j, Finset.erase_insert hjJ] at h
  · exact (mul_eq_zero.1 h).resolve_left (dolbeaultSign_ne_zero _ _)
  · intro i hi hij
    refine mul_eq_zero_of_right _ (dbarPartial_eq_zero_of_eventuallyEq_zero ?_)
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hvan _ ⟨j, Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_insert_self _ _⟩, hj⟩ w hw
  · exact fun h => absurd (Finset.mem_insert_self _ _) h

/-- The correction step of the induction: let `Gf_J = ε(k, J) G_J` for `|J| = q` and
`J ⊆ {i < k}`, and `Gf_J = 0` otherwise, where `∂G_J/∂z̄_k = θ_{k ∪ J}` and `G_J` is holomorphic
in `z_j` for `j > k`. If `θ` has degree `q + 1` and vanishes whenever an index `> k` occurs, then
`θ_I = (∂̄ Gf)_I` at `z` whenever `I` contains an index `≥ k`. -/
lemma eq_dbarForm_of_exists_le {q : ℕ} {k : Fin n}
    {θ G Gf : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hpos : ∀ J : Finset (Fin n), J.card = q ∧ (∀ i ∈ J, (i : ℕ) < k) →
      Gf J = fun w => dolbeaultSign k J * G J w)
    (hneg : ∀ J : Finset (Fin n), ¬ (J.card = q ∧ ∀ i ∈ J, (i : ℕ) < k) → Gf J = 0)
    (hGz : ∀ J, DifferentiableAt ℝ (G J) z)
    (hGd : ∀ J : Finset (Fin n), J.card = q ∧ (∀ i ∈ J, (i : ℕ) < k) →
      dbarPartial k (G J) z = θ (insert k J) z)
    (hGh : ∀ J : Finset (Fin n), J.card = q ∧ (∀ i ∈ J, (i : ℕ) < k) →
      ∀ j : Fin n, (k : ℕ) < j → dbarPartial j (G J) z = 0)
    (hvan : ∀ I : Finset (Fin n), (∃ i ∈ I, (k : ℕ) < i) → θ I z = 0)
    (hdeg : ∀ I : Finset (Fin n), I.card ≠ q + 1 → θ I z = 0)
    {I : Finset (Fin n)} (hI : ∃ i ∈ I, (k : ℕ) ≤ i) : θ I z = dbarForm Gf I z := by
  obtain ⟨i, hiI, hki⟩ := hI
  unfold dbarForm
  by_cases hA : ∃ i' ∈ I, (k : ℕ) < i'
  · obtain ⟨i', hi'I, hki'⟩ := hA
    rw [hvan I ⟨i', hi'I, hki'⟩]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    by_cases hc : (I.erase j).card = q ∧ ∀ i ∈ I.erase j, (i : ℕ) < k
    · have hji' : j = i' := by
        by_contra hne
        have := hc.2 i' (Finset.mem_erase.2 ⟨Ne.symm hne, hi'I⟩)
        omega
      subst hji'
      rw [hpos _ hc, dbarPartial_const_mul _ (hGz _), hGh _ hc j hki']
      ring
    · rw [hneg _ hc]
      exact mul_eq_zero_of_right _
        (dbarPartial_eq_zero_of_eventuallyEq_zero (Filter.Eventually.of_forall fun _ => rfl))
  · push Not at hA
    have hik : i = k := Fin.ext (le_antisymm (hA i hiI) hki)
    rw [hik] at hiI
    rw [Finset.sum_eq_single k]
    · by_cases hc : (I.erase k).card = q ∧ ∀ i ∈ I.erase k, (i : ℕ) < k
      · rw [hpos _ hc, dbarPartial_const_mul _ (hGz _), hGd _ hc, Finset.insert_erase hiI,
          ← mul_assoc, dolbeaultSign_mul_self, one_mul]
      · have hcard : (I.erase k).card ≠ q := by
          intro hq
          refine hc ⟨hq, fun i' hi' => ?_⟩
          have h1 := hA i' (Finset.mem_of_mem_erase hi')
          have h3 : (i' : ℕ) ≠ k := fun h => Finset.ne_of_mem_erase hi' (Fin.ext h)
          omega
        have hI : I.card ≠ q + 1 := by
          rw [← Finset.card_erase_add_one hiI]
          omega
        rw [hdeg I hI, hneg _ hc]
        exact (mul_eq_zero_of_right _ (dbarPartial_eq_zero_of_eventuallyEq_zero
          (Filter.Eventually.of_forall fun _ => rfl))).symm
    · intro j hj hji
      have hc : ¬ ((I.erase j).card = q ∧ ∀ i ∈ I.erase j, (i : ℕ) < k) := fun hc =>
        lt_irrefl _ (hc.2 k (Finset.mem_erase.2 ⟨Ne.symm hji, hiI⟩))
      rw [hneg _ hc]
      exact mul_eq_zero_of_right _
        (dbarPartial_eq_zero_of_eventuallyEq_zero (Filter.Eventually.of_forall fun _ => rfl))
    · exact fun h => absurd hiI h

include hT in
/-- The inductive step of the Dolbeault–Grothendieck lemma: a closed form on a product of open
sets of `ℂ` only involving `dz̄_i` with `i < k` is exact on a smaller product of open sets
containing a given product of compact sets. -/
theorem exists_dbarForm_eq_of_lt (q k : ℕ) :
    ∀ {W : Fin n → Set ℂ}, (∀ j, IsOpen (W j)) →
    ∀ {K : Fin n → Set ℂ}, (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ W j) →
    ∀ {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ},
      (∀ I, ContDiffOn ℝ ∞ (θ I) {z | ∀ j, z j ∈ W j}) →
      (∀ I : Finset (Fin n), I.card ≠ q + 1 → ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j},
        θ I z = 0) →
      (∀ I : Finset (Fin n), (∃ i ∈ I, k ≤ (i : ℕ)) →
        ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}, θ I z = 0) →
      (∀ I, ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}, dbarForm θ I z = 0) →
      ∃ W' : Fin n → Set ℂ, (∀ j, IsOpen (W' j)) ∧ (∀ j, K j ⊆ W' j) ∧ (∀ j, W' j ⊆ W j) ∧
        ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
          (∀ I : Finset (Fin n), I.card ≠ q → u I = 0) ∧
          (∀ I, ContDiffOn ℝ ∞ (u I) {z | ∀ j, z j ∈ W' j}) ∧
          ∀ I, ∀ z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W' j}, dbarForm u I z = θ I z := by
  induction k with
  | zero =>
    intro W hW K hK hKW θ hθ hdeg hvan hcl
    refine ⟨W, hW, hKW, fun _ => subset_rfl, 0, fun _ _ => rfl, fun _ => contDiffOn_const, ?_⟩
    intro I z hz
    rw [show dbarForm (0 : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ) I z = 0 by
      simp [dbarForm, dbarPartial]]
    by_cases hI : I.card = q + 1
    · obtain ⟨i, hi⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
      exact (hvan I ⟨i, hi, Nat.zero_le _⟩ z hz).symm
    · exact (hdeg I hI z hz).symm
  | succ k ih =>
    intro W hW K hK hKW θ hθ hdeg hvan hcl
    by_cases hkn : k < n
    swap
    · exact ih hW hK hKW hθ hdeg (fun I ⟨i, hi, hki⟩ =>
        absurd (lt_of_lt_of_le i.2 (not_lt.1 hkn)) (not_lt.2 hki)) hcl
    set kk : Fin n := ⟨k, hkn⟩
    set U := {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j}
    have hU : IsOpen U := isOpen_setOf_forall_mem hW
    obtain ⟨W'k, hW'k, hKW'k, hW'kW, hsol⟩ :=
      exists_dbarPartial_eq_of_cauchyTransform hT hW kk (hK kk) (hKW kk)
    set W₁ : Fin n → Set ℂ := Function.update W kk W'k
    have hW₁ : ∀ j, IsOpen (W₁ j) :=
      (Function.forall_update_iff W fun _ s => IsOpen s).2 ⟨hW'k, fun j _ => hW j⟩
    have hW₁W : ∀ j, W₁ j ⊆ W j :=
      (Function.forall_update_iff W fun j s => s ⊆ W j).2 ⟨hW'kW, fun _ _ => subset_rfl⟩
    have hKW₁ : ∀ j, K j ⊆ W₁ j :=
      (Function.forall_update_iff W fun j s => K j ⊆ s).2 ⟨hKW'k, fun j _ => hKW j⟩
    set V₀ := {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W₁ j}
    have hV₀ : IsOpen V₀ := isOpen_setOf_forall_mem hW₁
    have hV₀U : V₀ ⊆ U := fun z hz j => hW₁W j (hz j)
    choose G hGs0 hGd0 hGh0 using fun J : Finset (Fin n) => hsol (θ (insert kk J)) (hθ _)
    have hGs : ∀ J, ContDiffOn ℝ ∞ (G J) V₀ := fun J => (hGs0 J).mono hV₀U
    have hGd : ∀ J, ∀ z ∈ V₀, dbarPartial kk (G J) z = θ (insert kk J) z := fun J z hz =>
      hGd0 J z (hV₀U hz) (by simpa [W₁] using hz kk)
    have hGh : ∀ J, ∀ j ≠ kk, (∀ z ∈ U, dbarPartial j (θ (insert kk J)) z = 0) →
        ∀ z ∈ V₀, dbarPartial j (G J) z = 0 := fun J j hj h z hz => hGh0 J j hj h z (hV₀U hz)
    classical
    let cond : Finset (Fin n) → Prop := fun J => J.card = q ∧ ∀ i ∈ J, (i : ℕ) < k
    let Gf : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun J =>
      if cond J then fun w => dolbeaultSign kk J * G J w else 0
    have hGf_pos : ∀ J, cond J → Gf J = fun w => dolbeaultSign kk J * G J w :=
      fun J hJ => ite_eq_left hJ
    have hGf_neg : ∀ J, ¬ cond J → Gf J = 0 := fun J hJ => ite_eq_right hJ
    have hGfs : ∀ J, ContDiffOn ℝ ∞ (Gf J) V₀ := by
      intro J
      by_cases hJ : cond J
      · rw [hGf_pos J hJ]
        exact contDiffOn_const.mul (hGs J)
      · rw [hGf_neg J hJ]
        exact contDiffOn_const
    have hGfdeg : ∀ J : Finset (Fin n), J.card ≠ q → Gf J = 0 :=
      fun J hJ => hGf_neg J fun h => hJ h.1
    have hdiffU : ∀ J, ∀ z ∈ U, DifferentiableAt ℝ (θ J) z := fun J z hz =>
      ((hθ J).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hdiffG : ∀ J, ∀ z ∈ V₀, DifferentiableAt ℝ (Gf J) z := fun J z hz =>
      ((hGfs J).contDiffAt (hV₀.mem_nhds hz)).differentiableAt (by simp)
    let θ' : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ := fun I w => θ I w - dbarForm Gf I w
    have hdG : ∀ I, ContDiffOn ℝ ∞ (dbarForm Gf I) V₀ := fun I =>
      contDiffOn_dbarForm hV₀ (fun J => (hGfs J).of_le top_add_one_le) I
    have hθ's : ∀ I, ContDiffOn ℝ ∞ (θ' I) V₀ := fun I => ((hθ I).mono hV₀U).sub (hdG I)
    have hθ'deg : ∀ I : Finset (Fin n), I.card ≠ q + 1 → ∀ z ∈ V₀, θ' I z = 0 := by
      intro I hI z hz
      simp only [θ', hdeg I hI z (hV₀U hz), dbarForm_of_degree hGfdeg I hI, Pi.zero_apply,
        sub_zero]
    have hθ'cl : ∀ I, ∀ z ∈ V₀, dbarForm θ' I z = 0 := by
      intro I z hz
      have hdd : ∀ J, DifferentiableAt ℝ (dbarForm Gf J) z := fun J =>
        ((hdG J).contDiffAt (hV₀.mem_nhds hz)).differentiableAt (by simp)
      simp only [θ']
      rw [dbarForm_sub (fun J => hdiffU J z (hV₀U hz)) hdd, hcl I z (hV₀U hz),
        dbarForm_dbarForm hV₀
          (fun J => (hGfs J).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) I hz]
      simp
    have hθ'van : ∀ I : Finset (Fin n), (∃ i ∈ I, k ≤ (i : ℕ)) → ∀ z ∈ V₀, θ' I z = 0 := by
      intro I hI z hz
      simp only [θ', sub_eq_zero]
      exact eq_dbarForm_of_exists_le (k := kk) hGf_pos hGf_neg
        (fun J => (hGs J).differentiableOn (by simp) z hz |>.differentiableAt (hV₀.mem_nhds hz))
        (fun J _ => hGd J z hz)
        (fun J hc j hj => hGh J j (fun h => by rw [h] at hj; exact lt_irrefl _ hj)
          (fun _ hw => dbarPartial_insert_eq_zero_of_dbarForm_eq_zero (k := kk) hU hvan hcl
            hc.2 hj hw) z hz)
        (fun I hI => hvan I hI z (hV₀U hz)) (fun I hI => hdeg I hI z (hV₀U hz)) hI
    obtain ⟨W', hW', hKW', hW'W₁, u', hu'deg, hu's, hu'eq⟩ :=
      ih hW₁ hK hKW₁ hθ's hθ'deg hθ'van hθ'cl
    have hVV₀ : {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W' j} ⊆ V₀ :=
      fun z hz j => hW'W₁ j (hz j)
    have hV : IsOpen {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W' j} := isOpen_setOf_forall_mem hW'
    refine ⟨W', hW', hKW', fun j => (hW'W₁ j).trans (hW₁W j), fun I w => u' I w + Gf I w,
      fun I hI => ?_, fun I => (hu's I).add ((hGfs I).mono hVV₀), fun I z hz => ?_⟩
    · funext w
      simp [hu'deg I hI, hGfdeg I hI]
    · have hdu : ∀ J, DifferentiableAt ℝ (u' J) z := fun J =>
        ((hu's J).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
      rw [dbarForm_add hdu (fun J => hdiffG J z (hVV₀ hz)), hu'eq I z hz]
      simp [θ']

/-- **Tube lemma.** A product of compact subsets of `ℂ` inside an open `U ⊆ ℂⁿ` lies in a product
of open subsets of `ℂ` inside `U`. -/
lemma exists_isOpen_forall_mem_subset {K : Fin n → Set ℂ} (hK : ∀ j, IsCompact (K j))
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hKU : {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j} ⊆ U) :
    ∃ W : Fin n → Set ℂ, (∀ j, IsOpen (W j)) ∧ (∀ j, K j ⊆ W j) ∧
      {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ W j} ⊆ U := by
  let K' : Set (Fin n → ℂ) := Set.univ.pi K
  have hK' : IsCompact K' := isCompact_univ_pi hK
  let U' : Set (Fin n → ℂ) := (fun y => (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage (PiLp.continuous_toLp 2 _)
  have hK'U' : K' ⊆ U' := fun y hy => hKU fun j => hy j (Set.mem_univ _)
  obtain ⟨δ, hδ, hth⟩ := hK'.exists_thickening_subset_open hU' hK'U'
  refine ⟨fun j => Metric.thickening (δ / 2) (K j), fun j => Metric.isOpen_thickening,
    fun j => Metric.self_subset_thickening (by positivity) _, fun z hz => ?_⟩
  choose p hp hpd using fun j => Metric.mem_thickening_iff.1 (hz j)
  have hdist : dist (WithLp.ofLp z) p < δ := by
    rw [dist_pi_lt_iff hδ]
    exact fun j => (hpd j).trans (by linarith)
  simpa [U'] using hth (Metric.mem_thickening_iff.2 ⟨p, fun j _ => hp j, hdist⟩)

include hT in
/-- **The Dolbeault–Grothendieck lemma.** A `∂̄`-closed smooth `(0, q + 1)`-form on an open
`U ⊆ ℂⁿ` is `∂̄`-exact on an open neighbourhood of any product of compact sets contained in
`U`. -/
theorem exists_dbarForm_eq_of_dbarForm_eq_zero {q : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) {θ : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ}
    (hθ : ∀ I, ContDiffOn ℝ ∞ (θ I) U)
    (hdeg : ∀ I : Finset (Fin n), I.card ≠ q + 1 → ∀ z ∈ U, θ I z = 0)
    (hcl : ∀ I, ∀ z ∈ U, dbarForm θ I z = 0) {K : Fin n → Set ℂ} (hK : ∀ j, IsCompact (K j))
    (hKU : {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j} ⊆ U) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧
      {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ K j} ⊆ V ∧ V ⊆ U ∧
      ∃ u : Finset (Fin n) → EuclideanSpace ℂ (Fin n) → ℂ,
        (∀ I : Finset (Fin n), I.card ≠ q → u I = 0) ∧ (∀ I, ContDiffOn ℝ ∞ (u I) V) ∧
        ∀ I, ∀ z ∈ V, dbarForm u I z = θ I z := by
  obtain ⟨W, hW, hKW, hWU⟩ := exists_isOpen_forall_mem_subset hK hU hKU
  obtain ⟨W', hW', hKW', hW'W, u, hudeg, hus, hueq⟩ := exists_dbarForm_eq_of_lt hT q n hW hK hKW
    (fun I => (hθ I).mono hWU) (fun I hI z hz => hdeg I hI z (hWU hz))
    (fun _ ⟨i, _, hi⟩ => absurd i.2 (not_lt.2 hi)) (fun I z hz => hcl I z (hWU hz))
  exact ⟨_, isOpen_setOf_forall_mem hW', fun z hz j => hKW' j (hz j),
    fun z hz => hWU fun j => hW'W j (hz j), u, hudeg, hus, hueq⟩

include hT in
/-- **The Dolbeault–Grothendieck lemma for sections of `ℰ^{0,q}`.** A section of `ℰ^{0,q+1}`
over an open `U` with `∂̄ s = 0` is, near every point of `U`, the `∂̄` of a section of
`ℰ^{0,q}`. -/
theorem exists_dbarSections_eq_of_dbarSections_eq_zero (q : ℕ)
    (U : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))) (s : dolbeaultSections n (q + 1) U)
    (hs : dbarSections n (q + 1) U s = 0) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ U) :
    ∃ (V : TopologicalSpace.Opens (EuclideanSpace ℂ (Fin n))) (_ : x ∈ V) (hVU : V ≤ U)
      (t : dolbeaultSections n q V), dbarSections n q V t = dolbeaultRestrict n (q + 1) hVU s := by
  have hcl : ∀ I, ∀ z ∈ (U : Set (EuclideanSpace ℂ (Fin n))), dbarForm s.1 I z = 0 := by
    intro I z hz
    simpa [dbarSections_apply, Set.indicator_of_mem hz] using
      congrArg (fun t : dolbeaultSections n (q + 1 + 1) U => t.1 I z) hs
  have hxK : {z : EuclideanSpace ℂ (Fin n) | ∀ j, z j ∈ ({x j} : Set ℂ)} = {x} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨PiLp.ext, fun h j => by rw [h]⟩
  obtain ⟨V, hV, hxV, hVU, u, hudeg, hus, hueq⟩ :=
    exists_dbarForm_eq_of_dbarForm_eq_zero hT U.isOpen s.2.2.1
      (fun I hI z _ => by rw [s.2.1 I hI]; rfl) hcl (K := fun j => {x j})
      (fun _ => isCompact_singleton) (by rw [hxK]; exact Set.singleton_subset_iff.2 hx)
  rw [hxK, Set.singleton_subset_iff] at hxV
  have hmem : (fun I => V.indicator (u I)) ∈ dolbeaultSections n q V :=
    ⟨fun I hI => by simp [hudeg I hI],
      fun I => (hus I).congr fun z hz => Set.indicator_of_mem hz _,
      fun I z hz => Set.indicator_of_notMem hz _⟩
  refine ⟨⟨V, hV⟩, hxV, hVU, ⟨_, hmem⟩, Subtype.ext ?_⟩
  funext I z
  change V.indicator (dbarForm (fun J => V.indicator (u J)) I) z = V.indicator (s.1 I) z
  by_cases hz : z ∈ V
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, dbarForm_indicator hV _ I hz,
      hueq I z hz]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

end Induction

end OneVariable

end MMP.Analytic
