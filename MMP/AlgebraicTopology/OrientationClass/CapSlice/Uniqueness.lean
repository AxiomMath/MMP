module

public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Orientation
public import MMP.AlgebraicTopology.OrientationClass.CapUniqueness

/-!
# The fundamental class of `P` near a slice (Fulton, §19.1)

In the situation of `MMP.isOrientationPreserving_sliceCoreHomeomorph`, with `U`
connected and second countable, the push-forward along `f : Ω ≅ f(Ω)`
(`Ω = U × ball(0, 1/2)`) of any fundamental class of `Ω` for a complex orientation of `E' × F`
is the restriction `μ_P|_{f(Ω)}` of the fundamental class of `P`: both are fundamental classes of
the connected manifold `f(Ω)`.

## Main results

* `MMP.IsFundamentalClass.eq_of_connectedSpace_of_pos`: uniqueness of the
  fundamental class of a connected manifold of positive dimension `n`.
* `MMP.pushforward_sliceCoreHomeomorph_eq_restrict`: the push-forward of a fundamental class of
  `Ω` along `f` is the restriction of the fundamental class of `P` to `f(Ω)`.
-/

@[expose] public noncomputable section

open Set Topology Manifold

universe u

namespace MMP

open FundamentalClass

/-- **Uniqueness of the fundamental class**, in positive dimension `n`: on a connected, Hausdorff,
second countable real `n`-manifold, `0 < n`, any two fundamental classes for the same basis are
equal. -/
theorem IsFundamentalClass.eq_of_connectedSpace_of_pos {R : Type u} [CommRing R] {H : Type*}
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H]
    [T2Space H] {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ChartedSpace H Y]
    [SecondCountableTopology Y] [ConnectedSpace Y] {n : ℕ} (hn : 0 < n)
    {b : Module.Basis (Fin n) ℝ H}
    {μ μ' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Y) n}
    (hμ : IsFundamentalClass R b μ) (hμ' : IsFundamentalClass R b μ') : μ' = μ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  exact hμ.eq_of_connectedSpace hμ'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : Type u} [TopologicalSpace P] [T2Space P] [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ChartedSpace E' U]

omit [FiniteDimensional ℂ F] [T2Space U] in
/-- For `U` connected, the open set `U × ball(0, 1/2)` of `U × F` is connected. -/
lemma isConnected_sliceCore [ConnectedSpace U] :
    IsConnected (sliceCore U F : Set (U × F)) := by
  have h : (sliceCore U F : Set (U × F)) = univ ×ˢ Metric.ball (0 : F) (1 / 2) := by
    ext p
    simp [sliceCore]
  rw [h]
  exact isConnected_univ.prod ((convex_ball _ _).isConnected (Metric.nonempty_ball.2
    (by norm_num)))

variable (R : Type u) [CommRing R]

/-- In the situation of `isOrientationPreserving_sliceCoreHomeomorph`, with `U` connected and
second countable and `E` of positive dimension: the push-forward along `f : Ω ≅ f(Ω)` of a
fundamental class of `Ω = U × ball(0, 1/2)` for the complex orientation `complexRealBasis c` of
`E' × F` is the restriction to `f(Ω)` of the fundamental class of `P`. -/
theorem pushforward_sliceCoreHomeomorph_eq_restrict [SecondCountableTopology U]
    [ConnectedSpace U] (hE : 0 < Module.finrank ℂ E) {f : U × F → P} (hf : IsOpenEmbedding f)
    (g : OpenPartialHomeomorph U E') (hatlas : ∀ c ∈ atlas E' U, c = g)
    {e : OpenPartialHomeomorph P E} (he : e ∈ atlas E P) {γ : E' → E} (K : F →L[ℂ] E)
    (hfe : ∀ y w, ‖w‖ < 1 / 2 → γ (g y) + K w ∈ e.target ∧ f (y, w) = e.symm (γ (g y) + K w))
    (hγ : ∀ y, DifferentiableAt ℂ γ (g y) ∧
      Function.Bijective ((fderiv ℂ γ (g y)).coprod K))
    (c : Module.Basis (Fin (Module.finrank ℂ E)) ℂ (E' × F))
    {μΩ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (sliceCore U F))
      (2 * Module.finrank ℂ E : ℕ)}
    (hμΩ : IsFundamentalClass (H := ModelProd E' F) R
      (complexRealBasis c : Module.Basis _ ℝ (E' × F)) μΩ)
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass R (complexOrientationBasisOf E) μP) :
    borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (sliceCoreHomeomorph hf : C(sliceCore U F, sliceCoreImage hf)))
        (sliceCoreHomeomorph hf).isProperMap _ μΩ =
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of P) (sliceCoreImage hf)
        _ μP := by
  have h1 := hμΩ.pushforward_homeomorph R (sliceCoreHomeomorph hf)
    (isOrientationPreserving_sliceCoreHomeomorph hf g hatlas he K hfe hγ _
      fun L hL ↦ by
        rw [complexOrientationBasisOf_eq_complexRealBasis]
        exact complexRealBasis_det_pos c _ hL)
  have h2 := hμP.restrict (sliceCoreImage hf)
  have : ConnectedSpace (sliceCore U F) :=
    isConnected_iff_connectedSpace.1 isConnected_sliceCore
  have : ConnectedSpace (sliceCoreImage hf) :=
    (sliceCoreHomeomorph hf).surjective.connectedSpace (sliceCoreHomeomorph hf).continuous
  have : SecondCountableTopology (sliceCoreImage hf) :=
    (sliceCoreHomeomorph hf).symm.isEmbedding.secondCountableTopology
  exact (h1.eq_of_connectedSpace_of_pos (by omega) h2).symm

end MMP
