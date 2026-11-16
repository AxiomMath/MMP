module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import MMP.AlgebraicTopology.OrientationClass.CapLocalDegree
public import MMP.AlgebraicTopology.OrientationClass.CapComplexBasis
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety

/-!
# Holomorphic diffeomorphisms preserve complex orientations (Fulton, §19.1)

Let `φ : M → M'` be a `C^k` (`k ≥ 1`) diffeomorphism of complex manifolds, modelled on complex
vector spaces `E`, `E'` of the same dimension `r`. In charts `e` of `M` and `e'` of `M'` the
expression `e' ∘ φ ∘ e⁻¹` is complex differentiable, and its derivative is injective: the chart
expression of `φ⁻¹` is a local inverse, and the chain rule makes the composite of the
derivatives the identity. An injective complex linear map has positive real determinant for the
real bases `c₁, i c₁, …, c_r, i c_r` attached to complex bases, so `φ` is orientation preserving
for the complex orientations of `M` and `M'`.

This is the step "`f|_{U_i} : U_i → U` is biholomorphic, so `(f|_{U_i})_* μ_{U_i} = μ_U`" of
the proof of Fulton, Lemma 19.1.2.

## Main results

* `MMP.diffeomorph_exists_hasFDerivAt_injective`: the chart expression of a diffeomorphism of
  complex manifolds has an injective complex derivative.
* `MMP.diffeomorph_isOrientationPreserving_complexRealBasis`: a diffeomorphism of complex manifolds
  is orientation preserving for the complex orientations given by complex bases.
* `MMP.diffeomorph_isOrientationPreserving_euclideanComplexOrientationBasis`: the same on the
  Euclidean model `EuclideanSpace ℂ (Fin n)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Lemma 19.1.2.
-/

@[expose] public noncomputable section

open Set Topology Manifold

universe u

namespace MMP.FundamentalClass

/-- The basis `e₁, i e₁, …, e_n, i e_n` of `EuclideanSpace ℂ (Fin n)` is the real basis attached
to its standard complex basis. -/
lemma euclideanComplexOrientationBasis_eq_complexRealBasis (n : ℕ) :
    euclideanComplexOrientationBasis n =
      complexRealBasis (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))) := by
  rw [complexRealBasis, Module.Basis.equivFun_ofEquivFun]
  rfl

end MMP.FundamentalClass

namespace MMP

open MMP.FundamentalClass

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace E M] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E) 1 M] [IsManifold 𝓘(ℂ, E') 1 M']
  {k : WithTop ℕ∞}

/-- **The chart expression of a diffeomorphism has an injective complex derivative.** For a
`C^k` diffeomorphism `φ` (`k ≥ 1`) of complex manifolds and charts `e` of `M` at `x` and `e'` of
`M'` at `φ x`, the map `e' ∘ φ ∘ e⁻¹` has, at `e x`, a complex derivative which is injective. -/
theorem diffeomorph_exists_hasFDerivAt_injective
    (φ : Diffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E') M M' k) (hk : 1 ≤ k)
    {e : OpenPartialHomeomorph M E} (he : e ∈ atlas E M)
    {e' : OpenPartialHomeomorph M' E'} (he' : e' ∈ atlas E' M') {x : M} (hx : x ∈ e.source)
    (hx' : φ x ∈ e'.source) :
    ∃ D : E →L[ℂ] E', HasFDerivAt (fun y ↦ e' (φ (e.symm y))) D (e x) ∧
      Function.Injective D := by
  have hem := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, E)) (n := 1) he
  have hem' := IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, E')) (n := 1) he'
  have hφ := (φ.contMDiff.of_le hk) x
  have hψ := (φ.symm.contMDiff.of_le hk) (φ x)
  rw [contMDiffAt_iff_of_mem_maximalAtlas hem hem' hx hx'] at hφ
  rw [contMDiffAt_iff_of_mem_maximalAtlas hem' hem hx'
    (by rwa [φ.symm_apply_apply])] at hψ
  set f : E → E' := fun y ↦ e' (φ (e.symm y))
  set g : E' → E := fun z ↦ e (φ.symm (e'.symm z))
  have hφ' : ContDiffWithinAt ℂ 1 f (range 𝓘(ℂ, E)) (e x) := hφ.2
  have hψ' : ContDiffWithinAt ℂ 1 g (range 𝓘(ℂ, E')) (e' (φ x)) := hψ.2
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at hφ' hψ'
  have hf : DifferentiableAt ℂ f (e x) := hφ'.differentiableAt one_ne_zero
  have hfx : f (e x) = e' (φ x) := by simp only [f, e.left_inv hx]
  have hg : DifferentiableAt ℂ g (f (e x)) := hfx ▸ hψ'.differentiableAt one_ne_zero
  -- `g ∘ f = id` near `e x`
  have hW : ∀ᶠ y in 𝓝 (e x), g (f y) = y := by
    have hc : ContinuousAt (fun y ↦ φ (e.symm y)) (e x) :=
      φ.continuous.continuousAt.comp (e.continuousAt_symm (e.map_source hx))
    have h1 : ∀ᶠ y in 𝓝 (e x), φ (e.symm y) ∈ e'.source :=
      hc.preimage_mem_nhds (by simpa only [e.left_inv hx] using e'.open_source.mem_nhds hx')
    filter_upwards [h1, e.open_target.mem_nhds (e.map_source hx)] with y hy1 hy2
    simp only [f, g, e'.left_inv hy1, φ.symm_apply_apply, e.right_inv hy2]
  have heq := (hg.hasFDerivAt.comp (e x) hf.hasFDerivAt).unique
    ((hasFDerivAt_id (e x)).congr_of_eventuallyEq hW)
  exact ⟨fderiv ℂ f (e x), hf.hasFDerivAt,
    Function.LeftInverse.injective (g := fderiv ℂ g (f (e x))) fun v ↦
      ContinuousLinearMap.ext_iff.mp heq v⟩

/-- **Diffeomorphisms of complex manifolds preserve complex orientations.** A `C^k`
diffeomorphism (`k ≥ 1`) of complex manifolds modelled on `E` and `E'`, with complex bases `c`
of `E` and `c'` of `E'` of the same length, is orientation preserving for the real bases
`complexRealBasis c` and `complexRealBasis c'`. -/
theorem diffeomorph_isOrientationPreserving_complexRealBasis {r : ℕ} (c : Module.Basis (Fin r) ℂ E)
    (c' : Module.Basis (Fin r) ℂ E') [FiniteDimensional ℂ E]
    (φ : Diffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E') M M' k) (hk : 1 ≤ k) :
    IsOrientationPreserving (complexRealBasis c) (complexRealBasis c') φ.toHomeomorph :=
  isOrientationPreserving_of_hasFDerivAt _ _ _ fun _ he _ he' _ hx hx' ↦
    let ⟨D, hD, hinj⟩ := diffeomorph_exists_hasFDerivAt_injective φ hk he he' hx hx'
    ⟨D.restrictScalars ℝ, hD.restrictScalars ℝ,
      complexRealBasis_det_pos c c' (L := (D : E →ₗ[ℂ] E')) hinj⟩

/-- **Diffeomorphisms of complex manifolds modelled on `ℂⁿ` preserve the complex
orientations** `e₁, i e₁, …, e_n, i e_n` of the Euclidean model. -/
theorem diffeomorph_isOrientationPreserving_euclideanComplexOrientationBasis {n : ℕ} {N N' : Type u}
    [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace (EuclideanSpace ℂ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) N']
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 N]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 1 N']
    (φ : Diffeomorph 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) N N' k)
    (hk : 1 ≤ k) :
    IsOrientationPreserving (euclideanComplexOrientationBasis n)
      (euclideanComplexOrientationBasis n) φ.toHomeomorph := by
  rw [euclideanComplexOrientationBasis_eq_complexRealBasis]
  exact diffeomorph_isOrientationPreserving_complexRealBasis _ _ φ hk

end MMP
