module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksGlue
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksRestrict
public import MMP.Topology.VectorBundle.ProjectionNbhd

/-!
# Existence of orientation data, for Stacks vector bundles

Let `i : X → Y` be a regular imbedding of codimension `d` of complex schemes and `σ : Y ⟶ 𝐕(ℰ)` a
section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank
`e ≥ d`, with `Z(σ) = X`. Embed `𝐕(ℰ)(ℂ)` in `ℂᵐ` (`MMP.Modules.exists_hermitianEmbedding`), and
let `A` be the continuous family of self-adjoint operators which on `X(ℂ)` is the orthogonal
projection onto the normal fibres (`MMP.Modules.exists_normalProjection`). On a neighbourhood
`N ⊇ X(ℂ)`, `A` is close to a continuous family of projections `P` of rank `d`
(`MMP.exists_projectionFamily_nhds`), equal to `A` on `X(ℂ)`, with ranges in `ι(𝐕(ℰ)_y)`; the
image bundle `Q` of `P` (`MMP.ProjectionFamily.bundleCore`) and the map
`𝐕(ℰ)(ℂ)|_N → Q`, `p ↦ P(π p)(ι p)`, are the quotient of an orientation datum: in a chart it is
onto, and at `y ∈ X(ℂ)` it is injective on `N_y`.

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.nonempty_of_section`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Bundle Set Topology

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d e : ℕ}

/-- **Orientation data exist** for a regular imbedding `i` of codimension `d` of complex schemes,
given a section `σ` of the vector bundle `𝐕(ℰ)` of a quasi-coherent `𝒪_Y`-module `ℰ`, finite
locally free of rank `e ≥ d`, with `Z(σ) = X`. -/
theorem nonempty_of_section [IsComplexScheme Y] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d) (le_rank : d ≤ e)
    (E : Y.Modules) [E.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E e]
    (σ : Y ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) :
    Nonempty (RegularImbeddingOrientationDatum i d) := by
  obtain ⟨m, ιE, Φ, hιc, hΦ, hΦi, hΦc⟩ := exists_hermitianEmbedding E e
  obtain ⟨A, hAc, hAsa, hAX, hAE⟩ := exists_normalProjection i hi hσ hs hΦ hΦi hΦc
  obtain ⟨N, hNo, hXN, P, hPA, hPr⟩ := exists_projectionFamily_nhds
    (F := EuclideanSpace ℂ (Fin d)) hAc hAsa (X := range (mapFun i)) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨(hAX x).1, (hAX x).2.1.trans finrank_euclideanSpace_fin.symm⟩)
  have hsurj : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (hyN : y ∈ N),
      Function.Surjective ((P.projL ⟨y, hyN⟩).toLinearMap ∘ₗ (Φ c y).toLinearMap) := by
    intro c y hy hyN f
    obtain ⟨v, hv⟩ := hPr ⟨y, hyN⟩ ((P.frame ⟨y, hyN⟩).symm f).2
    obtain ⟨w, hw⟩ := hAE y c hy v
    refine ⟨w, ?_⟩
    change P.projL ⟨y, hyN⟩ (Φ c y w) = f
    have hw' : Φ c y w = ((P.frame ⟨y, hyN⟩).symm f : EuclideanSpace ℂ (Fin m)) :=
      hw.trans hv
    rw [hw', ProjectionFamily.projL, ContinuousLinearMap.comp_apply, P.toRange_coe,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  refine nonempty_of_quot (F := EuclideanSpace ℂ (Fin d)) (Q := P.bundleCore.Fiber) hi le_rank E
    σ hσ hs finrank_euclideanSpace_fin hNo hXN
    (fun p ↦ ⟨⟨mapFun (proj E) p.1, p.2⟩, P.projL ⟨mapFun (proj E) p.1, p.2⟩ (ιE p.1)⟩) ?_
    (fun _ ↦ rfl) ?_
  · exact P.continuous_mk_projL
      (β := fun p : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ N} ↦
        (⟨mapFun (proj E) p.1, p.2⟩ : N))
      (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _)
      (hιc.comp continuous_subtype_val)
  · intro c y hy hyN
    refine ⟨(P.projL ⟨y, hyN⟩).toLinearMap ∘ₗ (Φ c y).toLinearMap, fun w ↦ ?_,
      hsurj c y hy hyN, ?_⟩
    · have key : ∀ b : N, b = ⟨y, hyN⟩ →
          (⟨b, P.projL b (ιE (chartInv c y hy w))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin d)) P.bundleCore.Fiber) =
            ⟨⟨y, hyN⟩, P.projL ⟨y, hyN⟩ (ιE (chartInv c y hy w))⟩ := by
        rintro b rfl
        rfl
      refine (key _ (Subtype.ext (mapFun_proj_chartInv c y hy w))).trans ?_
      rw [hΦ c y hy w]
      rfl
    · intro hyX
      obtain ⟨x, rfl⟩ : ∃ x, mapFun i x = y := hyX
      rw [Submodule.isCompl_iff_disjoint]
      · rw [Submodule.disjoint_def]
        intro w hwker hwN
        have hL : P ⟨mapFun i x, hyN⟩ (Φ c (mapFun i x) w) = 0 :=
          (P.projL_eq_zero_iff _ _).1 hwker
        rw [hPA _ ⟨x, rfl⟩] at hL
        have hmem : Φ c (mapFun i x) w ∈ LinearMap.range (A (mapFun i x)).toLinearMap := by
          rw [(hAX x).2.2 c hy]
          exact ⟨w, hwN, rfl⟩
        obtain ⟨z, hz⟩ := hmem
        have hfix : A (mapFun i x) (Φ c (mapFun i x) w) = Φ c (mapFun i x) w := by
          change A (mapFun i x) (Φ c (mapFun i x) w) = Φ c (mapFun i x) w
          rw [← hz]
          change (A (mapFun i x) * A (mapFun i x)) z = A (mapFun i x) z
          rw [(hAX x).1.eq]
        refine hΦi c _ hy ?_
        rw [map_zero, ← hfix]
        exact hL
      · have h1 := LinearMap.finrank_range_add_finrank_ker
          ((P.projL ⟨mapFun i x, hyN⟩).toLinearMap ∘ₗ (Φ c (mapFun i x)).toLinearMap)
        rw [LinearMap.range_eq_top.2 (hsurj c _ hy hyN), finrank_top,
          finrank_euclideanSpace_fin] at h1
        rw [finrank_normalFibre i hi hσ hs c x hy]
        exact (h1.symm.trans (add_comm _ _)).le

end RegularImbeddingOrientationDatum

end MMP.Modules
