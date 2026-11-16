module

public import MMP.AlgebraicTopology.OrientationClass.Point
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Thom classes of trivial complex vector bundles (Fulton, §19.1)

The first step of Thom's theorem (Milnor–Stasheff, Thm. 10.4): a trivial complex vector bundle
`X × F → X` has a Thom class.

**The fibre.** On `ℂ^r` there is a relative cocycle `α ∈ Z^{2r}(ℂ^r, ℂ^r - 0; R)` taking the
value `1` on every affine simplex around `0` positively oriented for the real basis
`e₁, i e₁, …, e_r, i e_r`: the local orientation class at `0` of the complex manifold `ℂ^r`
(`MMP.exists_isChartOrientedCocycle`). As a complex linear automorphism `M` of `ℂ^r`
has real determinant `|det_ℂ M|² > 0`, it carries such simplices to such simplices, so `α` takes
the value `1` on `M ∘ Δ` as well.

**The trivial bundle.** Fix a complex frame `ψ₀ : ℂ^r ≅ F`. The pull-back of `α` along
`(x, f) ↦ ψ₀⁻¹ f`, a map of pairs `(X × F, X × F - 0) → (ℂ^r, ℂ^r - 0)`, is a Thom class: on the
fibre simplex `ψ ∘ Δ` at `x`, for a complex frame `ψ` and an oriented simplex `Δ`, it is
`α (ψ₀⁻¹ ψ ∘ Δ) = 1`.

## Main results

* `MMP.ThomClass.exists_relCocycles_eval_affineSimplex`: the oriented cocycle `α`.
* `MMP.ThomClass.eval_comp_affineSimplex_eq_one`: `α` takes the value `1` on `M ∘ Δ` for a
  complex linear automorphism `M`.
* `MMP.ThomClass.exists_isThomClass_trivial`: a trivial complex vector bundle has
  a Thom class.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §10, Case 1.
-/

@[expose] public noncomputable section

open Finsupp Set Bundle

universe u

namespace MMP

namespace ThomClass

open SingularChain SingularCochain FundamentalClass

variable {R : Type*} [CommRing R]

/-- A constant `0`-cochain is a cocycle: its coboundary vanishes. -/
lemma coboundary_zero_const {Y : Type*} [TopologicalSpace Y] (c : R) :
    coboundary R 0 (fun _ : Simplex Y 0 ↦ c) = 0 := by
  funext σ
  simp [coboundary_apply, Fin.sum_univ_two]

/-- **The local orientation cocycle of `ℂ^r` at `0`**, for any real basis `b`: a relative
cocycle of `(ℂ^r, ℂ^r - 0)` taking the value `1` on every affine simplex around `0` positively
oriented for `b`. -/
theorem exists_relCocycles_eval_affineSimplex_of_basis {r n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Fin r → ℂ)) :
    ∃ α ∈ relCocycles R ({0}ᶜ : Set (Fin r → ℂ)) n, ∀ v : Fin (n + 1) → (Fin r → ℂ),
      IsOrientedSimplexAroundZero b v → eval α (single (affineSimplex v) 1) = 1 := by
  cases n with
  | zero =>
    have hsub : Subsingleton (Fin r → ℂ) := by
      have h0 := Module.finrank_eq_card_basis b
      rw [Fintype.card_fin] at h0
      exact Module.finrank_zero_iff.1 h0
    refine ⟨fun _ ↦ 1, ⟨fun σ hσ ↦ ?_, coboundary_zero_const 1⟩, fun v _ ↦ ?_⟩
    · exact absurd (Subsingleton.elim _ _) (hσ (mem_range_self (stdSimplex.vertex 0)))
    · simp [eval, linearCombination_single]
  | succ m =>
    obtain ⟨α, hα, h1⟩ := exists_isChartOrientedCocycle (R := R)
      (isOrientedAtlas_of_isManifold_complex (E := Fin r → ℂ) (Fin r → ℂ)) b 0
    refine ⟨α, hα, fun v hv ↦ ?_⟩
    have h := h1 (chartAt (Fin r → ℂ) (0 : Fin r → ℂ)) (chart_mem_atlas _ _)
      (mem_chart_source _ _) v (by simpa [chartAt_self_eq] using hv) (by simp [chartAt_self_eq])
    convert h using 3
    ext1 t
    simp [chartSimplexOf_apply, chartAt_self_eq]

/-- **The local orientation cocycle of `ℂ^r` at `0`**: a relative cocycle of `(ℂ^r, ℂ^r - 0)`
taking the value `1` on every affine simplex around `0` positively oriented for the real basis
`e₁, i e₁, …, e_r, i e_r` given by the complex structure. -/
theorem exists_relCocycles_eval_affineSimplex (r : ℕ) :
    ∃ α ∈ relCocycles R ({0}ᶜ : Set (Fin r → ℂ)) (2 * r),
      ∀ v : Fin (2 * r + 1) → (Fin r → ℂ),
        IsOrientedSimplexAroundZero (complexOrientationBasis r) v →
          eval α (single (affineSimplex v) 1) = 1 :=
  exists_relCocycles_eval_affineSimplex_of_basis (complexOrientationBasis r)

/-- An oriented cocycle of `(ℂ^r, ℂ^r - 0)` takes the value `1` on the image `M ∘ Δ` of an
oriented simplex `Δ` around `0` under a complex linear automorphism `M`: the real determinant of
`M` is `|det_ℂ M|² > 0`. -/
theorem eval_comp_affineSimplex_eq_one {r : ℕ} {α : Simplex (Fin r → ℂ) (2 * r) → R}
    (hα : ∀ v : Fin (2 * r + 1) → (Fin r → ℂ),
      IsOrientedSimplexAroundZero (complexOrientationBasis r) v →
        eval α (single (affineSimplex v) 1) = 1)
    (M : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ)) {v : Fin (2 * r + 1) → (Fin r → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis r) v) :
    eval α (single ((M : C(Fin r → ℂ, Fin r → ℂ)).comp (affineSimplex v)) 1) = 1 := by
  set L : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    ((M : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)).restrictScalars ℝ).toLinearMap
  have hdet : 0 < (complexOrientationBasis r).det (L ∘ complexOrientationBasis r) := by
    rw [basis_det_comp_self, det_restrictScalars_real, Complex.normSq_pos]
    exact (LinearEquiv.isUnit_det' (M.toLinearEquiv)).ne_zero
  have hσ : (M : C(Fin r → ℂ, Fin r → ℂ)).comp (affineSimplex v) = affineSimplex (L ∘ v) := by
    ext1 t
    simp only [ContinuousMap.comp_apply, affineSimplex_apply, Function.comp_apply]
    change M (∑ k, (t : Fin (2 * r + 1) → ℝ) k • v k) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (M.toLinearMap.restrictScalars ℝ).map_smul _ _
  rw [hσ]
  exact hα _ (hv.map_linearMap L hdet)

section Trivial

variable (R : Type u) [CommRing R] {B : Type u} [TopologicalSpace B] (F : Type u)
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The map `(x, f) ↦ ψ₀⁻¹ f` from the total space of the trivial bundle `B × F` to `ℂ^r`, for a
complex frame `ψ₀ : ℂ^r ≅ F`. -/
def trivialFrameCoord (ψ₀ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F) :
    C(TotalSpace F (Trivial B F), Fin (Module.finrank ℂ F) → ℂ) :=
  ⟨fun e ↦ ψ₀.symm e.2, ψ₀.symm.continuous.comp (Trivial.homeomorphProd B F).continuous.snd⟩

omit [FiniteDimensional ℂ F] in
@[simp]
theorem trivialFrameCoord_apply (ψ₀ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F)
    (e : TotalSpace F (Trivial B F)) : trivialFrameCoord F ψ₀ e = ψ₀.symm e.2 :=
  rfl

/-- **A trivial complex vector bundle has a Thom class** (Milnor–Stasheff, §10, Case 1). -/
theorem exists_isThomClass_trivial :
    ∃ u, IsThomClass (R := R) F (Trivial B F) u := by
  set r := Module.finrank ℂ F
  let ψ₀ : (Fin r → ℂ) ≃L[ℂ] F := ContinuousLinearEquiv.ofFinrankEq (by simp [r])
  obtain ⟨α, hα, h1⟩ := exists_relCocycles_eval_affineSimplex (R := R) r
  set p := trivialFrameCoord F (B := B) ψ₀
  let β : Simplex (TotalSpace F (Trivial B F)) (2 * r) → R := fun τ ↦ α (p.comp τ)
  have hβ : β ∈ relCocycles R (range (zeroSection F (Trivial B F)))ᶜ (2 * r) := by
    refine ⟨fun τ hτ ↦ hα.1 _ ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩ h0
      refine hτ ⟨t, rfl⟩ ⟨(τ t).proj, ?_⟩
      have h0' : ψ₀.symm (τ t).2 = 0 := h0
      have : (τ t).2 = 0 := by simpa using congrArg ψ₀ h0'
      change TotalSpace.mk (τ t).proj 0 = τ t
      rw [← this]
    · change coboundary R (2 * r) β = 0
      funext τ
      have := congrFun hα.2 (p.comp τ)
      simp only [coboundary_apply, Pi.zero_apply] at this ⊢
      simpa [β, ContinuousMap.comp_assoc] using this
  refine ⟨(relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F (Trivial B F))) _ _).symm
    (Submodule.Quotient.mk ⟨β, hβ⟩), fun x ψ v hv ↦ ?_⟩
  rw [LinearEquiv.apply_symm_apply, relEval_mk]
  change eval β (single (fibreSimplex F x ψ v) 1) = 1
  have hc : p.comp (fibreSimplex F x ψ v) =
      ((ψ.trans ψ₀.symm : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ)) : C(Fin r → ℂ, Fin r → ℂ)).comp
        (affineSimplex v) := by
    ext1 t
    rfl
  have := eval_comp_affineSimplex_eq_one h1 (ψ.trans ψ₀.symm) hv
  rw [← hc] at this
  simpa [eval, linearCombination_single, β] using this

end Trivial

end ThomClass

end MMP
