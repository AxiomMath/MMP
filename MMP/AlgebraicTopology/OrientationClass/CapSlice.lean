module

public import MMP.AlgebraicTopology.OrientationClass.CapProduct

/-!
# Pulling back orientation classes along slice parametrizations (Fulton, §19.1)

Let `u` be the orientation class of `M ⊆ P` and `f : P' → P` continuous, with `M' = f⁻¹(M)`
carrying a tubular neighbourhood `φ'`. If `f` carries every fibre disc of `φ'` to a *transversal
disc* of `M` (differentiable at `0` in the chart of `P`, with an injective derivative complementary
to the tangent cone of `M` and complex linear modulo it), then `f^* u` is the orientation class of
`M'` relative to `φ'`. This is the disc criterion
`MMP.IsOrientationClass.eval_comp_affineSimplex_eq_one` read along `f`; it needs no
differentiability of `f` away from the fibre discs, and is the form used for the slice
parametrization `X × F → P` of step (A) of the cap-product formula `u_{M,P} ∩ μ_P = μ_M`.

## Main results

* `MMP.IsOrientationClass.map_of_fibreDisc`: the disc criterion read along `f`, and its special
  case `MMP.IsOrientationClass.pullback_of_fibreDisc` for `M' = f⁻¹(M)`.
* `MMP.IsOrientationClass.map_eq_pullback_prSnd`: for a map `f : X × F → P` with
  `f⁻¹(M) ⊆ X × {0}` and `f (y, 0) ∈ M`, whose fibre discs `w ↦ f (y, ψ w)` are transversal
  discs of `M`, `f^* u = pr^* u₀`.
-/

@[expose] public noncomputable section

open Set Bundle

universe u

namespace MMP

open SingularCochain ThomClass BorelMooreCap

section FibreDisc

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {P P' : TopCat.{u}} [ChartedSpace E P] [ChartedSpace E' P'] {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- **Pull-back of the orientation class along a map sending fibre discs to transversal discs.**
Let `u` be the orientation class of `M ⊆ P`, `f : P' → P` continuous with `f⁻¹(M) ⊆ M'` and
`f(M') ⊆ M`, and `φ'` a tubular neighbourhood of `M'` in `P'` of the same rank, compatible with the
complex orientations. If for every `x' ∈ M'` and every complex frame `ψ'` of `N'_{x'}` the disc
`w ↦ f (φ' (ψ' w))` is differentiable at `0` in the chart of `P` at `f x'`, with an injective
derivative complementary to the tangent cone `W` of `M` at `f x'` and complex linear modulo `W`,
then `f^* u ∈ H^{2d}(P', P' - M')` is the orientation class of `M'` relative to `φ'`. -/
theorem IsOrientationClass.map_of_fibreDisc (f : P' ⟶ P) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) {M' : Set P'} (h : M'ᶜ ⊆ f ⁻¹' Mᶜ)
    (hM' : ∀ x ∈ M', f x ∈ M)
    {N' : M' → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
    [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace F N')] [FiberBundle F N']
    [_root_.VectorBundle ℂ F N'] (φ' : TubularNeighbourhood (P := P') F N')
    (hφ' : φ'.IsOrientationCompatible (E := E'))
    (hdisc : ∀ (x' : M') (ψ' : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N' x'),
      ∃ L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E,
        HasFDerivAt (fun w ↦ chartAt E (f x') (f (φ'.fibreDisc x' ψ' w))) L 0 ∧
        Function.Injective L ∧
        ∃ W : Submodule ℂ E,
          tangentConeAt ℝ (chartAt E (f x') '' (M ∩ (chartAt E (f x')).source))
            (chartAt E (f x') (f x')) = W ∧
          IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
            (W.restrictScalars ℝ) ∧
          ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W) :
    IsOrientationClass E' R φ'
      ((relativeSingularCohomology.map R (ModuleCat.of R R) f h
        (2 * Module.finrank ℂ F : ℕ)).hom u) := by
  refine ⟨hφ', ?_⟩
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u)
  have hα' : cochainPullback R f (2 * Module.finrank ℂ F) α ∈
      relCocycles R (M'ᶜ : Set P') (2 * Module.finrank ℂ F) :=
    cochainPullback_mem_relCocycles f h hα
  have hrep' : relativeSingularCohomologyEquiv R (M'ᶜ : Set P') (2 * Module.finrank ℂ F)
      ((relativeSingularCohomology.map R (ModuleCat.of R R) f h
        (2 * Module.finrank ℂ F : ℕ)).hom u) =
      Submodule.Quotient.mk ⟨cochainPullback R f (2 * Module.finrank ℂ F) α, hα'⟩ :=
    (relativeSingularCohomologyEquiv_map (R := R) f h (2 * Module.finrank ℂ F) u).trans
      (by rw [← hrep, relCohomologyMap_mk])
  rw [isThomClass_thomPullback_iff R φ' hα' hrep']
  intro x' ψ' v hv
  rw [eval_cochainPullback_single]
  obtain ⟨L, hA, hinj, W, hTW, hc, hl⟩ := hdisc x' ψ'
  exact hu.eval_comp_affineSimplex_eq_one R hα hrep.symm (hM' _ x'.2)
    (f.hom.comp (φ'.fibreDisc x' ψ'))
    (congrArg f (φ'.fibreDisc_zero x' ψ'))
    (fun w hw ↦ φ'.eq_zero_of_fibreDisc_mem x' ψ' w (not_not.1 fun hn ↦ h hn hw))
    hA hinj W hTW hc hl hv

/-- The case `M' = f⁻¹(M)` of `IsOrientationClass.map_of_fibreDisc`: `f^* u` is the orientation
class of `f⁻¹(M)` relative to `φ'`. -/
theorem IsOrientationClass.pullback_of_fibreDisc (f : P' ⟶ P) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {N' : (f ⁻¹' M : Set P') → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
    [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace F N')] [FiberBundle F N']
    [_root_.VectorBundle ℂ F N'] (φ' : TubularNeighbourhood (P := P') F N')
    (hφ' : φ'.IsOrientationCompatible (E := E'))
    (hdisc : ∀ (x' : (f ⁻¹' M : Set P')) (ψ' : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N' x'),
      ∃ L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E,
        HasFDerivAt (fun w ↦ chartAt E (f x') (f (φ'.fibreDisc x' ψ' w))) L 0 ∧
        Function.Injective L ∧
        ∃ W : Submodule ℂ E,
          tangentConeAt ℝ (chartAt E (f x') '' (M ∩ (chartAt E (f x')).source))
            (chartAt E (f x') (f x')) = W ∧
          IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
            (W.restrictScalars ℝ) ∧
          ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W) :
    IsOrientationClass E' R φ'
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f M
        (2 * Module.finrank ℂ F : ℕ)).hom u) :=
  hu.map_of_fibreDisc R f (fun _ hx ↦ hx) (fun _ hx ↦ hx) φ' hφ' hdisc

end FibreDisc

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P}
  (X : TopCat.{u})
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- **Step (A) of `u_{M,P} ∩ μ_P = μ_M`: the pull-back of `u` along a slice parametrization.**
Let `u` be the orientation class of `M ⊆ P` and `f : X × F → P` continuous with
`f⁻¹(M) ⊆ X × {0}` and `f (y, 0) ∈ M`, whose fibre discs `w ↦ f (y, ψ w)` (for complex frames
`ψ : ℂ^d ≅ F`) are transversal discs of `M` at `f (y, 0)`, `X` being charted on some complex
space `HX` (the charts of `X` play no role). Then `f^* u = pr^* u₀` in
`H^{2d}(X × F, X × (F - 0))`, for the local orientation class `u₀` of `F` at `0`. -/
theorem IsOrientationClass.map_eq_pullback_prSnd (HX : Type*) [NormedAddCommGroup HX]
    [NormedSpace ℂ HX] [FiniteDimensional ℂ HX] [ChartedSpace HX X]
    (f : TopCat.of (X × TopCat.of F) ⟶ P) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (h : (zeroSlice X F)ᶜ ⊆ f ⁻¹' Mᶜ)
    (hM : ∀ y : X, f (y, 0) ∈ M)
    (hdisc : ∀ (y : X) (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F),
      ∃ L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E,
        HasFDerivAt (fun w ↦ chartAt E (f (y, 0)) (f (y, ψ w))) L 0 ∧
        Function.Injective L ∧
        ∃ W : Submodule ℂ E,
          tangentConeAt ℝ (chartAt E (f (y, 0)) '' (M ∩ (chartAt E (f (y, 0))).source))
            (chartAt E (f (y, 0)) (f (y, 0))) = W ∧
          IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
            (W.restrictScalars ℝ) ∧
          ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
      (2 * Module.finrank ℂ F : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) f h
        (2 * Module.finrank ℂ F : ℕ)).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X (TopCat.of F)) {0}
        (2 * Module.finrank ℂ F : ℕ)).hom u₀ := by
  let := prodChartedSpaceModel HX X F
  have hM' : ∀ x ∈ zeroSlice X F, f x ∈ M := by
    rintro ⟨y, w⟩ hw
    obtain rfl : w = 0 := mem_singleton_iff.1 hw
    exact hM y
  exact (hu.map_of_fibreDisc (E' := HX × F) R f h hM' (sliceTubularNeighbourhood X F)
    (isOrientationCompatible_sliceTubularNeighbourhood X F) (by
      rintro ⟨⟨y, w⟩, hw⟩ ψ
      obtain rfl : w = 0 := mem_singleton_iff.1 hw
      exact hdisc y ψ)).eq_pullback_prSnd X R hu₀

end Slice

end MMP
