module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.Geometry.Manifold.SmoothLevelSet

/-!
# Algebraic charts on the classical space of a scheme

Let `X` be a scheme over `𝕜 = ℝ` or `ℂ` and `X(𝕜)` its space of `𝕜`-points with the classical
topology. A partial homeomorphism `e` from `X(𝕜)` to a normed space `E` is an *algebraic chart* if

* every regular function `a ∈ Γ(X, V)` is analytic when read through `e`: the function
  `k ↦ a(e⁻¹ k)` is `C^ω` where it is defined, and
* the coordinates of `e` are locally regular functions: near each point of the source of `e`,
  `e = L ∘ (a_1, …, a_r)` for sections `a_i` of `𝒪_X` over an open set and a continuous linear
  map `L : 𝕜^r → E`.

The transition map between two algebraic charts is then analytic: near a point, the coordinates
of the second chart are regular functions, and these are analytic in the first chart. This is how
the charts of `X_reg(ℂ)` coming from different affine opens and presentations are compatible.
Algebraic charts lift along open immersions.

## Main definitions

* `MMP.UnderlyingSpace.IsAlgebraicChart`: the predicate above.

## Main results

* `MMP.UnderlyingSpace.IsAlgebraicChart.contDiffOn_symm_trans`: the transition map
  between two algebraic charts is `C^ω` on its source.
* `MMP.UnderlyingSpace.IsAlgebraicChart.lift_openEmbedding`: an algebraic chart of
  `U(𝕜)`, for an open immersion `U → X`, is an algebraic chart of `X(𝕜)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped ContDiff

universe u

namespace MMP

namespace UnderlyingSpace

section EvalExt

variable {K : Type u} [Field K] [TopologicalSpace K]

/-- The value of `a ∈ Γ(X, V)` at the image of `q` under `j : U → X` is the value of the
pull-back `j^* a` at `q`. -/
lemma evalExt_mapFun {U X : Scheme.{u}} [U.Over (Spec (.of K))] [X.Over (Spec (.of K))]
    (j : U ⟶ X) [j.IsOver (Spec (.of K))] (V : X.Opens) (a : Γ(X, V)) (q : UnderlyingSpace K U) :
    evalExt V a (mapFun j q) = evalExt (j ⁻¹ᵁ V) (j.app V a) q := by
  have e : (mapFun j q).toHom ⁻¹ᵁ V = q.toHom ⁻¹ᵁ (j ⁻¹ᵁ V) := by
    rw [toHom_mapFun, Scheme.Hom.comp_preimage]
  by_cases h : ⊤ ≤ q.toHom ⁻¹ᵁ (j ⁻¹ᵁ V)
  · rw [evalExt_of_le _ h, evalExt_of_le (p := mapFun j q) _ (e ▸ h)]
    exact eval_mapFun j q _ a
  · rw [evalExt, dif_neg (fun h' ↦ h (e ▸ h')), evalExt, dif_neg h]

/-- For `h : V' = V`, the value of the restriction of `a ∈ Γ(X, V)` to `V'` along `eqToHom h`
equals the value of `a`. -/
lemma evalExt_eqToHom {X : Scheme.{u}} [X.Over (Spec (.of K))] {V V' : X.Opens} (h : V' = V)
    (a : Γ(X, V)) : evalExt V' (X.presheaf.map (eqToHom h).op a) = evalExt (K := K) V a := by
  subst h
  simp

end EvalExt

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A partial homeomorphism `e` from `X(𝕜)` to a normed space is an *algebraic chart* if regular
functions are `C^ω` when read through `e⁻¹`, and the coordinates of `e` are, near each point of
its source, a continuous linear function of finitely many regular functions. -/
structure IsAlgebraicChart (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E) : Prop where
  /-- Regular functions are `C^ω` in the chart. -/
  contDiffOn_evalExt (V : X.Opens) (a : Γ(X, V)) :
    ContDiffOn 𝕜 ω (fun k ↦ evalExt V a (e.symm k))
      (e.target ∩ e.symm ⁻¹' {p | ⊤ ≤ p.toHom ⁻¹ᵁ V})
  /-- The coordinates of the chart are locally linear in finitely many regular functions. -/
  exists_eq_evalExt (p : UnderlyingSpace 𝕜 X) (hp : p ∈ e.source) :
    ∃ (V : X.Opens) (ι : Type) (_ : Fintype ι) (a : ι → Γ(X, V)) (L : (ι → 𝕜) →L[𝕜] E),
      ⊤ ≤ p.toHom ⁻¹ᵁ V ∧
        ∀ q ∈ e.source, ⊤ ≤ q.toHom ⁻¹ᵁ V → e q = L fun i ↦ evalExt V (a i) q

namespace IsAlgebraicChart

variable {e e' : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) E}

/-- **Algebraic charts are analytically compatible.** The transition map between two algebraic
charts is `C^ω` on its source. -/
theorem contDiffOn_symm_trans (he : IsAlgebraicChart e) (he' : IsAlgebraicChart e') :
    ContDiffOn 𝕜 ω (e.symm.trans e') (e.symm.trans e').source := by
  intro k hk
  have hk' := hk
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hk'
  obtain ⟨V, ι, _, a, L, hV, hL⟩ := he'.exists_eq_evalExt _ hk'.2
  set S := e.target ∩ e.symm ⁻¹' {p : UnderlyingSpace 𝕜 X | ⊤ ≤ p.toHom ⁻¹ᵁ V}
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage V)
  have hmem : (e.symm.trans e').source ∩ S ∈ 𝓝 k :=
    ((e.symm.trans e').open_source.inter hSo).mem_nhds ⟨hk, hk'.1, hV⟩
  have hF : ContDiffOn 𝕜 ω (fun k ↦ L fun i ↦ evalExt V (a i) (e.symm k)) S :=
    L.contDiff.comp_contDiffOn (contDiffOn_pi.2 fun i ↦ he.contDiffOn_evalExt V (a i))
  refine ContDiffAt.contDiffWithinAt ?_
  refine (hF.contDiffAt (Filter.mem_of_superset hmem Set.inter_subset_right)).congr_of_eventuallyEq
    ?_
  filter_upwards [hmem] with k' hk''
  have h1 := hk''.1
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h1
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  exact hL _ h1.2 hk''.2.2

section Lift

variable {U : Scheme.{u}} [U.Over (Spec (.of 𝕜))] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (.of 𝕜))] {e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 U) E}

/-- **Algebraic charts lift along open immersions.** For an open immersion `j : U → X` over `𝕜`,
an algebraic chart of `U(𝕜)` is an algebraic chart of `X(𝕜)`, through the open embedding
`U(𝕜) → X(𝕜)`. -/
theorem lift_openEmbedding (he : IsAlgebraicChart e) :
    IsAlgebraicChart
      (e.lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion (K := 𝕜) j)) where
  contDiffOn_evalExt V a := by
    have h := he.contDiffOn_evalExt (j ⁻¹ᵁ V) (j.app V a)
    simp only [← evalExt_mapFun] at h
    exact h
  exists_eq_evalExt p hp := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_source] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨W, ι, _, b, L, hW, hL⟩ := he.exists_eq_evalExt q hq
    have hpre : ∀ q' : UnderlyingSpace 𝕜 U, ⊤ ≤ (mapFun j q').toHom ⁻¹ᵁ (j ''ᵁ W) ↔
        ⊤ ≤ q'.toHom ⁻¹ᵁ W := fun q' ↦ by
      rw [toHom_mapFun, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
    have hev : ∀ (c : Γ(U, W)) (q' : UnderlyingSpace 𝕜 U),
        evalExt (j ''ᵁ W) ((j.appIso W).inv c) (mapFun j q') = evalExt W c q' := fun c q' ↦ by
      rw [evalExt_mapFun, Scheme.Hom.appIso_inv_app_apply, evalExt_eqToHom]
    refine ⟨j ''ᵁ W, ι, inferInstance, fun i ↦ (j.appIso W).inv (b i), L, (hpre q).2 hW, ?_⟩
    rintro _ ⟨q', hq', rfl⟩ hq'W
    change e.lift_openEmbedding _ (map j q') = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, hL q' hq' ((hpre q').1 hq'W)]
    exact congrArg L (funext fun i ↦ (hev (b i) q').symm)

end Lift

end IsAlgebraicChart

end UnderlyingSpace

end MMP
