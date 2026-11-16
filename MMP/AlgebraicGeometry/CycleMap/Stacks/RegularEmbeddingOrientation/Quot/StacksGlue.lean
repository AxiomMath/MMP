module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksFrame
public import MMP.Analysis.InnerProductSpace.PartitionOfUnityGlue

/-!
# The orthogonal projection onto the normal bundle, extended to `Y(ℂ)`, for Stacks bundles

Let `i : X → Y` be a regular imbedding of codimension `d` of complex schemes, `σ : Y ⟶ 𝐕(ℰ)` a
section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank
`e`, with `Z(σ) = X`, and `ι : 𝐕(ℰ)(ℂ) → ℂᵐ` a Hermitian embedding with chart expressions `Φ_c`.
Near each point `x` of `X(ℂ)` the orthogonal projections onto the ranges of the local frames
`K = Φ_c ∘ M` (`MMP.Modules.localFrame`) are continuous; at the points of `X(ℂ)` they are all the
orthogonal projection onto `ι(N_y)`. Glued with a partition of unity subordinate to these
neighbourhoods and to `Y(ℂ) - X(ℂ)` (where the operator is `0`), they give a continuous family
`A` of self-adjoint operators on `ℂᵐ` which on `X(ℂ)` is the orthogonal projection onto `ι(N_y)`,
and whose range at `y` lies in `ι(𝐕(ℰ)_y)`.

## Main results

* `MMP.Modules.exists_normalProjection`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Bundle Set Topology ContinuousLinearMap

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e d m : ℕ}
  {E : Y.Modules} [E.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E e]
  {ιE : UnderlyingSpace ℂ (totalSpace E) → EuclideanSpace ℂ (Fin m)}
  {Φ : Chart E e → UnderlyingSpace ℂ Y → (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)}

/-- **The projection onto the normal bundle, extended to `Y(ℂ)`.** There is a continuous family
`A` of self-adjoint operators on `ℂᵐ` which at each point `y` of `X(ℂ)` is a projection of rank
`d` onto `Φ_c(y)(N_y)` (in every chart `c`), and whose range at every `y ∈ V(ℂ)`, `c = (V, b)`,
lies in `Φ_c(y)(ℂᵉ) = ι(𝐕(ℰ)_y)`. -/
theorem exists_normalProjection [IsComplexScheme Y] (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d) {σ : Y ⟶ totalSpace E}
    (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker)
    (hΦ : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (w : Fin e → ℂ), ιE (chartInv c y hy w) = Φ c y w)
    (hΦi : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y), y ∈ chartBase c →
      Function.Injective (Φ c y))
    (hΦc : ∀ c : Chart E e, ContinuousOn (Φ c) (chartBase c)) :
    ∃ A : UnderlyingSpace ℂ Y → EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      Continuous A ∧ (∀ y, IsSelfAdjoint (A y)) ∧
      (∀ x : UnderlyingSpace ℂ X, IsIdempotentElem (A (mapFun i x)) ∧
        Module.finrank ℂ (LinearMap.range (A (mapFun i x)).toLinearMap) = d ∧
        ∀ (c : Chart E e) (_ : mapFun i x ∈ chartBase c),
          LinearMap.range (A (mapFun i x)).toLinearMap =
            (normalFibre σ c (mapFun i x)).map (Φ c (mapFun i x)).toLinearMap) ∧
      ∀ (y : UnderlyingSpace ℂ Y) (c : Chart E e), y ∈ chartBase c →
        ∀ v, A y v ∈ LinearMap.range (Φ c y).toLinearMap := by
  choose W hWc hxW M G f hP using fun x : UnderlyingSpace ℂ X ↦
    exists_isLocalRegularPresentation_nhds i hi σ hσ hs
      (chartAt E e (mapFun i x)) x (mem_chartBase_chartAt E e _)
  set cx : UnderlyingSpace ℂ X → Chart E e := fun x ↦ chartAt E e (mapFun i x)
  let K : UnderlyingSpace ℂ X → UnderlyingSpace ℂ Y →
      EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin m) := fun x ↦ localFrame Φ (cx x) (M x)
  let S : UnderlyingSpace ℂ X → Set (UnderlyingSpace ℂ Y) := fun x ↦
    chartBase (cx x) ∩ {y | ⊤ ≤ y.toHom ⁻¹ᵁ W x}
  let O : UnderlyingSpace ℂ X → Set (UnderlyingSpace ℂ Y) := fun x ↦
    S x ∩ {y | IsUnit (adjoint (K x y) ∘L K x y)}
  have hKc : ∀ x, ContinuousOn (K x) (S x) := fun x ↦ continuousOn_localFrame hΦc _ _
  have hSo : ∀ x, IsOpen (S x) := fun x ↦
    (isOpen_chartBase _).inter (isOpen_setOf_le_preimage _)
  have : CompleteSpace (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    FiniteDimensional.complete ℂ _
  have : HasSummableGeomSeries (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    instHasSummableGeomSeriesOfCompleteSpace
  have hOo : ∀ x, IsOpen (O x) := fun x ↦
    ((adjoint.continuous.comp_continuousOn (hKc x)).clm_comp (hKc x)).isOpen_inter_preimage
      (hSo x) Units.isOpen
  have hxO : ∀ x, mapFun i x ∈ O x := fun x ↦
    ⟨⟨mem_chartBase_chartAt E e _, hxW x⟩, isUnit_adjoint_comp_self
      (injective_localFrame hΦi (mem_chartBase_chartAt E e _) (hP x x (hxW x)))⟩
  have hcO : ∀ x, ContinuousOn (fun y ↦ rangeProj (K x y)) (O x) := fun x ↦
    continuousOn_rangeProj (hKc x)
  -- the range of `rangeProj (K x y)` at a point `y = i x'` of `X(ℂ)`
  have hrange : ∀ x x' (hx' : mapFun i x' ∈ O x) (c : Chart E e) (_ : mapFun i x' ∈ chartBase c),
      LinearMap.range (rangeProj (K x (mapFun i x'))).toLinearMap =
        (normalFibre σ c (mapFun i x')).map (Φ c (mapFun i x')).toLinearMap := by
    intro x x' hx' c hc
    rw [range_rangeProj hx'.2, range_localFrame (hP x x' hx'.1.2),
      map_normalFibre_eq hΦ i hi hσ hs (cx x) c x' hx'.1.1 hc]
  have hkey : ∀ x x' (hx' : mapFun i x' ∈ O x),
      rangeProj (K x (mapFun i x')) = rangeProj (K x' (mapFun i x')) := by
    intro x x' hx'
    refine eq_of_range_eq_of_isSelfAdjoint (isIdempotentElem_rangeProj hx'.2)
      (isIdempotentElem_rangeProj (hxO x').2) isSelfAdjoint_rangeProj isSelfAdjoint_rangeProj ?_
    rw [hrange x x' hx' (cx x') (hxO x').1.1, hrange x' x' (hxO x') (cx x') (hxO x').1.1]
  -- the cover of `Y(ℂ)` and the partition of unity
  let U : Option (UnderlyingSpace ℂ X) → Set (UnderlyingSpace ℂ Y) := fun a ↦
    a.elim (range (mapFun i))ᶜ O
  have hUo : ∀ a, IsOpen (U a) := by
    rintro (_ | x)
    · exact (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i).isClosed_range.isOpen_compl
    · exact hOo x
  obtain ⟨τ, hτ⟩ := PartitionOfUnity.exists_isSubordinate (X := UnderlyingSpace ℂ Y) isClosed_univ
    U hUo fun y _ ↦ by
      by_cases hy : y ∈ range (mapFun i)
      · obtain ⟨x, rfl⟩ := hy
        exact mem_iUnion.2 ⟨some x, hxO x⟩
      · exact mem_iUnion.2 ⟨none, hy⟩
  let P : Option (UnderlyingSpace ℂ X) → UnderlyingSpace ℂ Y →
      EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) := fun a y ↦
    a.elim 0 fun x ↦ rangeProj (K x y)
  have hAX : ∀ x', glueOperators τ P (mapFun i x') = rangeProj (K x' (mapFun i x')) := by
    intro x'
    refine glueOperators_eq fun a ha ↦ ?_
    rcases a with _ | x
    · exact absurd ⟨x', rfl⟩ (hτ none (subset_tsupport _ ha))
    · exact hkey x x' (hτ (some x) (subset_tsupport _ ha))
  refine ⟨glueOperators τ P, continuous_glueOperators fun a y hy ↦ ?_,
    fun y ↦ isSelfAdjoint_glueOperators fun a _ ↦ ?_, fun x' ↦ ⟨?_, ?_, fun c hc ↦ ?_⟩,
    fun y c hyc v ↦ glueOperators_apply_mem (fun a ha v ↦ ?_) v⟩
  · rcases a with _ | x
    · exact continuousAt_const
    · exact (hcO x).continuousAt ((hOo x).mem_nhds (hτ (some x) hy))
  · rcases a with _ | x
    · exact IsSelfAdjoint.zero _
    · exact isSelfAdjoint_rangeProj
  · rw [hAX]
    exact isIdempotentElem_rangeProj (hxO x').2
  · rw [hAX, range_rangeProj (hxO x').2, LinearMap.finrank_range_of_inj
      (injective_localFrame hΦi (mem_chartBase_chartAt E e _) (hP x' x' (hxW x'))),
      finrank_euclideanSpace_fin]
  · rw [hAX]
    exact hrange x' x' (hxO x') c hc
  · rcases a with _ | x
    · exact Submodule.zero_mem _
    · have hyO : y ∈ O x := hτ (some x) (subset_tsupport _ ha)
      exact range_le_range hΦ (cx x) c hyO.1.1 hyc ⟨_, rfl⟩

end MMP.Modules
