module

public import MMP.Geometry.Manifold.SmoothLevelSet
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The zero set of a submersive presentation is a submersion level set

Let `𝕜` be `ℝ` or `ℂ` and let `P` be a submersive presentation of a `𝕜`-algebra `S`: generators
`x_i` (`i ∈ ι`) and relations `f_j` (`j ∈ σ`) with `S = 𝕜[x_i] / (f_j)`, such that the Jacobian
`det (∂f_j/∂x_{m(i)})_{i,j}` with respect to a subfamily `m : σ ↪ ι` of the variables is a unit
in `S`. Then the polynomial map `F = (f_j)_j : 𝕜^ι → 𝕜^σ` is a submersion at each of its zeros:
on the zero set the Jacobian determinant does not vanish, since `det · g - 1` lies in the ideal of
the relations for some polynomial `g`.

The derivative of the evaluation of a polynomial `p` at `x` is `v ↦ ∑ᵢ (∂p/∂xᵢ)(x) vᵢ`.

## Main definitions

* `MMP.SubmersivePresentationLevelSet.polyDeriv p x`: the linear map
  `v ↦ ∑ᵢ (∂p/∂xᵢ)(x) vᵢ`.
* `MMP.SubmersivePresentationLevelSet.relMap P`: the polynomial map
  `x ↦ (f_j(x))_j`.

## Main results

* `MMP.SubmersivePresentationLevelSet.hasStrictFDerivAt_eval`: the derivative of
  `x ↦ p(x)` is `polyDeriv p x`.
* `MMP.SubmersivePresentationLevelSet.surjective_fderiv_relMap`: at a zero of the
  relations, the derivative of `relMap P` is surjective.
* `MMP.SubmersivePresentationLevelSet.isSubmersionOn_relMap`: `relMap P` is an
  analytic submersion on `𝕜^ι` in the sense of `MMP.SmoothLevelSet.IsSubmersionOn`,
  so its zero set is a manifold of dimension `|ι| - |σ|`.
-/

@[expose] public noncomputable section

open MvPolynomial Set

namespace MMP

namespace SubmersivePresentationLevelSet

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The linear map `v ↦ ∑ᵢ (∂p/∂xᵢ)(x) vᵢ`, the derivative of `p` at `x`. -/
def polyDeriv (p : MvPolynomial ι 𝕜) (x : ι → 𝕜) : (ι → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

/-- `polyDeriv p x` sends `v` to `∑ᵢ (∂p/∂xᵢ)(x) * vᵢ`. -/
lemma polyDeriv_apply (p : MvPolynomial ι 𝕜) (x v : ι → 𝕜) :
    polyDeriv p x v = ∑ i, eval x (pderiv i p) * v i := by
  simp [polyDeriv]

/-- The derivative of the evaluation `x ↦ p(x)` of a polynomial is `v ↦ ∑ᵢ (∂p/∂xᵢ)(x) vᵢ`. -/
theorem hasStrictFDerivAt_eval (p : MvPolynomial ι 𝕜) (x : ι → 𝕜) :
    HasStrictFDerivAt (fun y ↦ eval y p) (polyDeriv p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h0 : polyDeriv (C a) x = 0 := by
      ext v
      simp [polyDeriv_apply]
    simpa [h0] using hasStrictFDerivAt_const a x
  | add p q hp hq =>
    simp only [eval_add]
    refine (hp.add hq).congr_fderiv ?_
    ext v
    simp [polyDeriv_apply, Finset.sum_add_distrib, add_mul]
  | mul_X p n hp =>
    have hX : HasStrictFDerivAt (fun y : ι → 𝕜 ↦ y n) (ContinuousLinearMap.proj n) x :=
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) n).hasStrictFDerivAt
    simp only [eval_mul, eval_X]
    refine (hp.mul hX).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, polyDeriv_apply, pderiv_mul, pderiv_X,
      map_add, map_mul, eval_X, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    · rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp

/-- The evaluation `x ↦ p(x)` of a polynomial is `C^n` for every `n`. -/
theorem contDiff_eval (p : MvPolynomial ι 𝕜) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n fun y : ι → 𝕜 ↦ eval y p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply 𝕜 (fun _ => 𝕜) i)

variable {S : Type*} [CommRing S] [Algebra 𝕜 S] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The polynomial map `x ↦ (f_j(x))_j` given by the relations of a presentation. -/
def relMap (P : Algebra.Presentation 𝕜 S ι σ) (x : ι → 𝕜) : σ → 𝕜 :=
  fun j ↦ eval x (P.relation j)

/-- The strict derivative of `relMap P` at `x` is `v ↦ (polyDeriv (P.relation j) x v)_j`. -/
theorem hasStrictFDerivAt_relMap (P : Algebra.Presentation 𝕜 S ι σ) (x : ι → 𝕜) :
    HasStrictFDerivAt (relMap P) (ContinuousLinearMap.pi fun j ↦ polyDeriv (P.relation j) x) x :=
  hasStrictFDerivAt_pi.mpr fun j ↦ hasStrictFDerivAt_eval _ x

/-- The polynomial map `relMap P` is `C^n` for every `n`. -/
theorem contDiff_relMap (P : Algebra.Presentation 𝕜 S ι σ) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (relMap P) :=
  contDiff_pi.mpr fun j ↦ contDiff_eval _

/-- The derivative of `relMap P` at `x` is `v ↦ (polyDeriv (P.relation j) x v)_j`. -/
theorem fderiv_relMap (P : Algebra.Presentation 𝕜 S ι σ) (x : ι → 𝕜) :
    fderiv 𝕜 (relMap P) x = ContinuousLinearMap.pi fun j ↦ polyDeriv (P.relation j) x :=
  (hasStrictFDerivAt_relMap P x).hasFDerivAt.fderiv

/-- A polynomial in the ideal of the relations vanishes on their common zeros. -/
lemma eval_eq_zero_of_mem_ker (P : Algebra.Presentation 𝕜 S ι σ) {x : ι → 𝕜}
    (hx : relMap P x = 0) {q : P.Ring} (hq : q ∈ P.ker) : eval x q = 0 := by
  rw [← P.span_range_relation_eq_ker] at hq
  refine (Ideal.span_le (I := RingHom.ker (eval x))).mpr ?_ hq
  rintro _ ⟨j, rfl⟩
  exact congrFun hx j

/-- On the zero set of the relations of a submersive presentation, the Jacobian determinant does
not vanish. -/
theorem eval_det_jacobiMatrix_ne_zero (P : Algebra.SubmersivePresentation 𝕜 S ι σ) {x : ι → 𝕜}
    (hx : relMap P.toPresentation x = 0) : eval x P.jacobiMatrix.det ≠ 0 := by
  obtain ⟨u, hu⟩ := P.jacobian_isUnit.exists_right_inv
  obtain ⟨g, rfl⟩ := P.algebraMap_surjective u
  have hmem : P.jacobiMatrix.det * g - 1 ∈ P.ker := by
    rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub, map_mul, map_one,
      ← P.algebraMap_apply, ← P.algebraMap_apply, ← P.jacobian_eq_jacobiMatrix_det, hu, sub_self]
  have := eval_eq_zero_of_mem_ker P.toPresentation hx hmem
  rw [map_sub, map_mul, map_one, sub_eq_zero] at this
  exact left_ne_zero_of_mul_eq_one this

/-- At a zero of the relations of a submersive presentation, the derivative of `relMap` is
surjective. -/
theorem surjective_fderiv_relMap (P : Algebra.SubmersivePresentation 𝕜 S ι σ) {x : ι → 𝕜}
    (hx : relMap P.toPresentation x = 0) :
    Function.Surjective (fderiv 𝕜 (relMap P.toPresentation) x) := by
  classical
  intro t
  have hM : IsUnit (P.jacobiMatrix.map (eval x)).transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    exact (eval_det_jacobiMatrix_ne_zero P hx).isUnit
  obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM t
  refine ⟨fun i ↦ ∑ k, if P.map k = i then w k else 0, ?_⟩
  rw [fderiv_relMap, ← hw]
  funext j
  simp only [ContinuousLinearMap.pi_apply, polyDeriv_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.map_apply, P.jacobiMatrix_apply, Finset.mul_sum, mul_ite,
    mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The polynomial map of the relations of a submersive presentation over `𝕜` is an analytic
submersion at each of its zeros; so its zero set in `𝕜^ι` is a manifold of dimension
`|ι| - |σ|` (`MMP.SmoothLevelSet.isManifold`). -/
theorem isSubmersionOn_relMap (P : Algebra.SubmersivePresentation 𝕜 S ι σ) {n : WithTop ℕ∞}
    (hn : 1 ≤ n) : SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) n univ (relMap P.toPresentation) where
  isOpen := isOpen_univ
  contDiffOn := (contDiff_relMap _).contDiffOn
  one_le := hn
  surjective x hx := surjective_fderiv_relMap P hx.2

end SubmersivePresentationLevelSet

end MMP
