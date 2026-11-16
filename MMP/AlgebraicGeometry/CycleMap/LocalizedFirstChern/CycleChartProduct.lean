module

public import MMP.AlgebraicGeometry.CycleMap.LocalizedFirstChern.CycleChart
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartHolomorphic

/-!
# The cycle class of a subvariety in a chart of the ambient variety (Fulton, §19.1)

Let `i : V → D` and `j : D → X` be closed immersions of complex schemes, `V` a variety of
dimension `k`, `e_X` an algebraic chart of `X(ℂ)` with values in `ℂⁿ`, and `W ⊆ D(ℂ)` an open
set contained in `i(V_reg(ℂ))` and mapped by `j` into the source of `e_X`. Suppose
`φ : W ≃ₜ B` is a homeomorphism onto a complex manifold of dimension `k` which, in each chart
`e'` of `B`, reads near each point of `W` as `π ∘ e_X ∘ j` for a map `π : ℂⁿ → ℂᵏ`
differentiable at the point, and that a map `ρ` differentiable on `e_X(j(W))` vanishes there,
with `(ρ, π)` of injective derivative. (In a product chart `ψ ∘ e_X` of `X(ℂ)` in which `W` is
the zero fibre of the first coordinate, `ρ` and `π` are the two components of `ψ`.) Then
`φ ∘ i` is holomorphic with injective derivative in the algebraic charts of `V`: the composite
`V → X` is holomorphic and immersive in algebraic charts
(`IsAlgebraicChart.contDiffAt_comp_mapFun`, `IsAlgebraicChart.injective_fderiv_comp_mapFun`),
and the derivative of `ρ ∘ e_X ∘ j ∘ i ∘ e⁻¹ = 0` kills the kernel of `π`. Hence
`φ_* ((i_* cl(V))|_W) = μ_B`.

## Main results

* `MMP.UnderlyingSpace.exists_injective_hasFDerivAt_of_eventuallyEq_comp`: the
  chart hypothesis of
  `MMP.IsVarietyFundamentalClass.pushforward_restrict_pushforward_eq_of_hasFDerivAt`
  holds for such `φ`.
* `MMP.IsVarietyFundamentalClass.pushforward_restrict_pushforward_eq_of_chart`:
  `φ_* ((i_* cl(V))|_W) = μ_B`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP.Intersection.Scheme (dimension)

namespace UnderlyingSpace

open MMP.UnderlyingSpace

variable {D V X : Scheme.{0}} [D.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))]
  [X.Over (Spec (.of ℂ))] (i : V ⟶ D) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]
  (j : D ⟶ X) [IsClosedImmersion j] [j.IsOver (Spec (.of ℂ))] {k n : ℕ}
  {eX : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))}
  {W : Opens (UnderlyingSpace ℂ D)} {B : Type} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℂ (Fin k)) B] (φ : W ≃ₜ B)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (ρ : EuclideanSpace ℂ (Fin n) → G)

omit [IsClosedImmersion i] [IsClosedImmersion j] in
/-- The map on complex points induced by a composite `i ≫ j` is the composite of the induced
maps. -/
lemma _root_.MMP.UnderlyingSpace.mapFun_comp_apply (q : UnderlyingSpace ℂ V) :
    mapFun (i ≫ j) q = mapFun j (mapFun i q) :=
  UnderlyingSpace.ext (Category.assoc _ _ _).symm

open Classical in
/-- **`φ ∘ i` is holomorphic and immersive in algebraic charts** when `φ` is read, in the charts
of `B`, as `π ∘ e_X ∘ j` for a chart `e_X` of the ambient `X(ℂ)`, with `ρ ∘ e_X ∘ j = 0` on `W`
and `(ρ, π)` of injective derivative: for every algebraic chart `e` of `V(ℂ)` and chart `e'` of
`B`, the chart expression `e' ∘ φ ∘ i ∘ e⁻¹` (extended by `0` off `W`) has an injective complex
derivative at `e(q)`. -/
theorem _root_.MMP.UnderlyingSpace.exists_injective_hasFDerivAt_of_eventuallyEq_comp
    (heX : IsAlgebraicChart eX)
    (hWX : ∀ p : W, mapFun j p.1 ∈ eX.source) (hρ : ∀ p : W, ρ (eX (mapFun j p.1)) = 0)
    (hρd : ∀ p : W, DifferentiableAt ℂ ρ (eX (mapFun j p.1)))
    (hπ : ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ p : W, φ p ∈ e'.source →
      ∃ π : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin k),
        (∀ᶠ p' in 𝓝 p, e' (φ p') = π (eX (mapFun j p'.1))) ∧
        DifferentiableAt ℂ π (eX (mapFun j p.1)) ∧
        Function.Injective (fderiv ℂ (fun z ↦ (ρ z, π z)) (eX (mapFun j p.1)))) :
    ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ V) (EuclideanSpace ℂ (Fin k)),
      IsAlgebraicChart e → ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ q ∈ e.source,
      q ∈ regularPart ℂ V → ∀ hq : mapFun i q ∈ W, φ ⟨mapFun i q, hq⟩ ∈ e'.source →
      ∃ L : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k), Function.Injective L ∧
        HasFDerivAt (fun y ↦ if h : mapFun i (e.symm y) ∈ W then e' (φ ⟨_, h⟩) else 0) L
          (e q) := by
  intro e he e' he' q hqe _ hq hφq
  set p : W := ⟨mapFun i q, hq⟩
  obtain ⟨π, hev, hπd, hinj⟩ := hπ e' he' p hφq
  set F : EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin n) :=
    fun y ↦ eX (mapFun (i ≫ j) (e.symm y))
  have hq' : mapFun (i ≫ j) q ∈ eX.source := by
    rw [mapFun_comp_apply]
    exact hWX p
  have hFd : DifferentiableAt ℂ F (e q) :=
    (he.contDiffAt_comp_mapFun (i ≫ j) heX hqe hq').differentiableAt (by simp)
  have hFinj : Function.Injective (fderiv ℂ F (e q)) :=
    he.injective_fderiv_comp_mapFun (i ≫ j) heX hqe hq'
  have hFq : F (e q) = eX (mapFun j p.1) := by
    simp only [F, e.left_inv hqe, mapFun_comp_apply, p]
  obtain ⟨S, hSsub, hSo, hpS⟩ := mem_nhds_iff.1 hev
  have hO : IsOpen (Subtype.val '' S : Set (UnderlyingSpace ℂ D)) := W.2.isOpenMap_subtype_val S hSo
  set N := e.target ∩ e.symm ⁻¹' (mapFun i ⁻¹' (Subtype.val '' S))
  have hN : N ∈ 𝓝 (e q) :=
    (e.isOpen_inter_preimage_symm (hO.preimage (continuous_mapFun i))).mem_nhds
      ⟨e.map_source hqe, by rw [mem_preimage, e.left_inv hqe]; exact ⟨p, hpS, rfl⟩⟩
  have hNW : ∀ y ∈ N, ∃ p' ∈ S, p'.1 = mapFun i (e.symm y) := fun y hy ↦ hy.2
  have hG : (fun y ↦ if h : mapFun i (e.symm y) ∈ W then e' (φ ⟨_, h⟩) else 0) =ᶠ[𝓝 (e q)]
      fun y ↦ π (F y) := by
    filter_upwards [hN] with y hy
    obtain ⟨p', hp'S, hp'⟩ := hNW y hy
    have hyW : mapFun i (e.symm y) ∈ W := hp' ▸ p'.2
    rw [dite_eq_left hyW]
    have hpp : (⟨mapFun i (e.symm y), hyW⟩ : W) = p' := Subtype.ext hp'.symm
    rw [hpp, hSsub hp'S]
    simp only [F, mapFun_comp_apply, hp']
  have hρF : (fun y ↦ ρ (F y)) =ᶠ[𝓝 (e q)] fun _ ↦ (0 : G) := by
    filter_upwards [hN] with y hy
    obtain ⟨p', -, hp'⟩ := hNW y hy
    simp only [F, mapFun_comp_apply, ← hp']
    exact hρ p'
  have hπd' : DifferentiableAt ℂ π (F (e q)) := hFq ▸ hπd
  have hρd' : DifferentiableAt ℂ ρ (F (e q)) := hFq ▸ hρd p
  refine ⟨(fderiv ℂ π (F (e q))).comp (fderiv ℂ F (e q)), fun w₁ w₂ hw ↦ ?_,
    (hπd'.hasFDerivAt.comp (e q) hFd.hasFDerivAt).congr_of_eventuallyEq hG⟩
  apply hFinj
  have hρ0 : (fderiv ℂ ρ (F (e q))).comp (fderiv ℂ F (e q)) = 0 := by
    rw [← fderiv_comp _ hρd' hFd]
    exact (hρF.fderiv_eq (𝕜 := ℂ)).trans (fderiv_const_apply _)
  have hinj' := hinj
  rw [← hFq, DifferentiableAt.fderiv_prodMk hρd' hπd'] at hinj'
  apply hinj'
  have h1 := congrArg (fun L ↦ L w₁) hρ0
  have h2 := congrArg (fun L ↦ L w₂) hρ0
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at h1 h2 hw
  simp only [ContinuousLinearMap.prod_apply, h1, h2, hw]

end UnderlyingSpace

section CycleClass

open borelMooreHomology

variable (R : Type) [CommRing R] {D V X : Scheme.{0}} [D.Over (Spec (.of ℂ))] [IsComplexScheme D]
  [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] [X.Over (Spec (.of ℂ))]
  (i : V ⟶ D) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]
  (j : D ⟶ X) [IsClosedImmersion j] [j.IsOver (Spec (.of ℂ))]

/-- **The cycle class of a subvariety in a chart of the ambient variety** (Fulton, §19.1). Let
`i : V → D`, `j : D → X` be closed immersions, `V` a complex variety of dimension `k`,
`c = cl(V)`, `W ⊆ D(ℂ)` open with `W ⊆ i(V_reg(ℂ))`, `e_X` an algebraic chart of `X(ℂ)` whose
source contains `j(W)`, and `φ : W ≃ₜ B` a homeomorphism onto a connected Hausdorff complex
manifold of dimension `k` with fundamental class `μ_B`. Suppose that in each chart `e'` of `B`,
`φ` reads near each point of `W` as `π ∘ e_X ∘ j`, with `π` differentiable there, and that a map
`ρ`, differentiable on `e_X(j(W))` and vanishing there, makes `(ρ, π)` of injective derivative.
Then `φ_* ((i_* c)|_W) = μ_B`. -/
theorem _root_.MMP.IsVarietyFundamentalClass.pushforward_restrict_pushforward_eq_of_chart {k n : ℕ}
    {hk : (k : WithBot ℕ∞) = dimension V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    {eX : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))}
    (heX : IsAlgebraicChart eX) (hWX : ∀ p : W, mapFun j p.1 ∈ eX.source)
    {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB) (φ : W ≃ₜ B)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (ρ : EuclideanSpace ℂ (Fin n) → G)
    (hρ : ∀ p : W, ρ (eX (mapFun j p.1)) = 0)
    (hρd : ∀ p : W, DifferentiableAt ℂ ρ (eX (mapFun j p.1)))
    (hπ : ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ p : W, φ p ∈ e'.source →
      ∃ π : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin k),
        (∀ᶠ p' in 𝓝 p, e' (φ p') = π (eX (mapFun j p'.1))) ∧
        DifferentiableAt ℂ π (eX (mapFun j p.1)) ∧
        Function.Injective (fderiv ℂ (fun z ↦ (ρ z, π z)) (eX (mapFun j p.1)))) :
    pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap (2 * k : ℕ)
      (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ D)) W (2 * k : ℕ)
        (pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
          (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap (2 * k : ℕ) c)) = μB :=
  hc.pushforward_restrict_pushforward_eq_of_hasFDerivAt R i W hW hμB φ
    (exists_injective_hasFDerivAt_of_eventuallyEq_comp i j φ ρ heX hWX hρ hρd hπ)

end CycleClass

end MMP
