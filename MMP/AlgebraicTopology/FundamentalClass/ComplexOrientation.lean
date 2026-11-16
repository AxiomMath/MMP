module

public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
public import MMP.AlgebraicTopology.PoincareDuality.Vanishing
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
/-!
# Orientation of complex manifolds, and Borel–Moore homology of a finite disjoint union

Let `M` be a complex manifold of complex dimension `m` which is the disjoint union of finitely
many connected open subsets `M₁, …, M_r`. Fulton (proof of Lemma 19.1.1) shows `H_i M = 0` for
`i > 2m`: `H_i M ≅ ⨁_l H_i M_l`; each `M_l` is a connected real `2m`-manifold, oriented by its
complex structure, so by Poincaré duality `H_i M_l ≅ H^{2m - i}(M_l)`, which vanishes for
`i > 2m`. This file contains the two steps of that argument which do not use duality.

The complex structure orients `M`: a transition map `φ` of a holomorphic atlas is complex
differentiable with invertible derivative, and the real determinant of a complex linear map `L`
is `|det_ℂ L|² > 0`, so `φ` preserves the orientation of the underlying real vector space.

The Borel–Moore homology of a finite disjoint union of open subsets vanishes in a degree as soon
as that of every member does.

## Main definitions

* `MMP.IsOrientedAtlas`: the atlas of a charted space over a real normed space
  has differentiable transition maps with positive Jacobian determinant.

## Main results

* `MMP.det_restrictScalars_real`: `det_ℝ L = |det_ℂ L|²`.
* `MMP.isOrientedAtlas_of_isManifold_complex`: a complex manifold is oriented by
  its complex structure.
* `MMP.borelMooreHomology.isZero_of_isZero_disjoint_cover`: `H_i Y = 0` if
  `H_i Y_l = 0` for every member `Y_l` of a finite disjoint open cover of `Y`.
* `MMP.borelMooreHomology.isZero_of_complexManifold`: `H_i M = 0` for `i > 2m`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and the proof of Lemma 19.1.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Manifold Topology Function

universe u

namespace MMP

section Orientation

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M]

/-- The atlas of a charted space `M` over a real normed space `H` is *oriented*: every transition
map `e⁻¹ ≫ e'` between two of its charts is differentiable at every point of its domain, with
positive Jacobian determinant. -/
def IsOrientedAtlas : Prop :=
  ∀ e ∈ atlas H M, ∀ e' ∈ atlas H M, ∀ x ∈ (e.symm ≫ₕ e').source,
    DifferentiableAt ℝ (e.symm ≫ₕ e') x ∧
      0 < LinearMap.det (fderiv ℝ (e.symm ≫ₕ e') x : H →ₗ[ℝ] H)

end Orientation

section ComplexOrientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real determinant of a complex linear endomorphism `L` of a complex vector space is
`|det_ℂ L|²`. -/
lemma det_restrictScalars_real (L : E →L[ℂ] E) :
    LinearMap.det ((L.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      Complex.normSq (LinearMap.det (L : E →ₗ[ℂ] E)) := by
  rw [← Algebra.norm_complex_apply, ← LinearMap.det_restrictScalars]
  rfl

/-- A map of the groupoid of `C¹` maps of a complex normed space is complex differentiable on its
domain. -/
lemma differentiableAt_of_mem_contDiffGroupoid {f : OpenPartialHomeomorph E E}
    (hf : f ∈ contDiffGroupoid 1 𝓘(ℂ, E)) {x : E} (hx : x ∈ f.source) :
    DifferentiableAt ℂ f x := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hf
  have h : ContDiffOn ℂ 1 f f.source := by simpa [contDiffPregroupoid] using hf.1
  exact ((h x hx).contDiffAt (f.open_source.mem_nhds hx)).differentiableAt one_ne_zero

/-- A map `f` of the groupoid of `C¹` maps of a finite-dimensional complex normed space has, at
every point of its domain, a real derivative of positive determinant. -/
lemma det_fderiv_pos_of_mem_contDiffGroupoid [FiniteDimensional ℂ E]
    {f : OpenPartialHomeomorph E E} (hf : f ∈ contDiffGroupoid 1 𝓘(ℂ, E)) {x : E}
    (hx : x ∈ f.source) :
    DifferentiableAt ℝ f x ∧ 0 < LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E) := by
  have hd := differentiableAt_of_mem_contDiffGroupoid hf hx
  have hd' : DifferentiableAt ℂ f.symm (f x) :=
    differentiableAt_of_mem_contDiffGroupoid ((contDiffGroupoid 1 𝓘(ℂ, E)).symm hf)
      (f.map_source hx)
  refine ⟨hd.restrictScalars ℝ, ?_⟩
  rw [hd.fderiv_restrictScalars ℝ, det_restrictScalars_real, Complex.normSq_pos]
  -- `f⁻¹ ∘ f = id` near `x`, so `D(f⁻¹)(f x) ∘ Df(x) = 1` and `det Df(x) ≠ 0`.
  have hcomp : (fderiv ℂ f.symm (f x)).comp (fderiv ℂ f x) = ContinuousLinearMap.id ℂ E := by
    rw [← fderiv_comp x hd' hd, ← fderiv_id (𝕜 := ℂ) (x := x)]
    exact Filter.EventuallyEq.fderiv_eq (f.eventually_left_inverse hx)
  have hdet : LinearMap.det (fderiv ℂ f.symm (f x) : E →ₗ[ℂ] E) *
      LinearMap.det (fderiv ℂ f x : E →ₗ[ℂ] E) = 1 := by
    rw [← LinearMap.det_comp]
    change LinearMap.det ((fderiv ℂ f.symm (f x)).comp (fderiv ℂ f x) : E →ₗ[ℂ] E) = 1
    rw [hcomp]
    exact LinearMap.det_id
  exact right_ne_zero_of_mul_eq_one hdet

/-- **A complex manifold is oriented by its complex structure**: the transition maps of the atlas
of a `C¹` complex manifold modelled on a finite-dimensional complex normed space have positive
real Jacobian determinant. -/
lemma isOrientedAtlas_of_isManifold_complex [FiniteDimensional ℂ E] (M : Type*)
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M] : IsOrientedAtlas E M :=
  fun _ he _ he' _ hx ↦
    det_fderiv_pos_of_mem_contDiffGroupoid (HasGroupoid.compatible he he') hx

end ComplexOrientation

namespace borelMooreHomology

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- Let the Hausdorff space `Y` be the disjoint union of finitely many open subsets `U l`. If
`H_i (U l) = 0` for every `l`, then `H_i Y = 0`. -/
theorem isZero_of_isZero_disjoint_cover {Y : TopCat.{u}} [T2Space Y] {ι : Type} [Fintype ι]
    (U : ι → TopologicalSpace.Opens Y) (hdisj : Pairwise (Disjoint on fun l ↦ (U l : Set Y)))
    (hcover : ∀ y, ∃ l, y ∈ U l) {i : ℤ}
    (h : ∀ l, IsZero (borelMooreHomology R M (TopCat.of (U l)) i)) :
    IsZero (borelMooreHomology R M Y i) := by
  refine IsZero.of_iso ?_ (disjointUnionIso R M U hdisj hcover i).symm
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext _ _ fun l ↦ (h l).eq_of_tgt _ _

/-- **The Borel–Moore homology of a complex manifold of complex dimension `m` vanishes above
degree `2m`** (Fulton, proof of Lemma 19.1.1). The manifold `M`, modelled on `ℂ^m`, is Hausdorff
and second countable (the standard convention); it is a real `2m`-manifold through the real
basis `e₁, i e₁, …, e_m, i e_m` of `ℂ^m`. Fulton's hypothesis that `M` is a finite disjoint
union of connected open subsets, and the holomorphy of the atlas, are not needed. -/
theorem isZero_of_complexManifold {m : ℕ} {M' : Type u} [TopologicalSpace M'] [T2Space M']
    [SecondCountableTopology M'] [ChartedSpace (Fin m → ℂ) M'] {i : ℤ} (hi : (2 * m : ℕ) < i) :
    IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of M') i) :=
  isZero_of_dim_lt R (ThomClass.complexOrientationBasis m) hi

end borelMooreHomology

end MMP
