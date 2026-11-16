module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.DiagonalRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# Points of products, and the complex manifold of a smooth variety (generic part)

Facts about the classical topology on the points of schemes over a field.

* For schemes `X`, `T` over a field `K` and a fibre square `P = X ×_K T`, the map
  `P(K) → X(K) × T(K)`, `w ↦ (pr₁ w, pr₂ w)`, is a homeomorphism: it is an embedding, and it is
  onto since `Spec K` has only one `K`-point.
* The underlying space of a complex scheme is metrizable: it embeds in some `ℝᴺ`.
* A smooth variety `T` of relative dimension `n` over `ℂ` (`AlgebraicGeometry.IsSmoothVariety`
  with `SmoothOfRelativeDimension n`) is a complex analytic manifold modelled on `ℂⁿ`, its atlas
  being the algebraic charts; its local rings at `ℂ`-points are regular of dimension `n`.
* A `K`-point `Spec K → T` of a separated `K`-scheme `T` is a closed immersion.

## Main definitions

* `MMP.UnderlyingSpace.homeomorphProdOfIsPullback`: `P(K) ≃ₜ X(K) × T(K)` for a
  fibre square `P = X ×_K T`; `MMP.UnderlyingSpace.homeomorphProd` for the
  chosen fibre product.
* `MMP.UnderlyingSpace.algebraicChartedSpace`: the algebraic charts of `X(𝕜)`, for
  an integral scheme of finite type all of whose `𝕜`-points are regular.

## Main results

* `MMP.UnderlyingSpace.metrizableSpace_of_isComplexScheme`,
  `MMP.UnderlyingSpace.secondCountableTopology_of_isComplexScheme`.
* `MMP.UnderlyingSpace.isManifold_algebraicChartedSpace`,
  `MMP.UnderlyingSpace.isManifold_of_isSmoothVariety`.
* `MMP.UnderlyingSpace.ringKrullDim_stalk_eq_of_smoothOfRelativeDimension`.
* `MMP.UnderlyingSpace.isClosedImmersion_toHom`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

universe u

namespace MMP

open MMP.Intersection.Scheme (dimension)

namespace UnderlyingSpace

section Product

variable {K : Type u} [Field K] {P X T : Scheme.{u}} [P.Over (Spec (.of K))]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {fst : P ⟶ X} {snd : P ⟶ T}
  [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))]

/-- For a fibre square `P = X ×_K T` over `K`, every pair of `K`-points of `X` and `T` comes
from a `K`-point of `P`. -/
theorem surjective_prodMap_of_isPullback
    (H : IsPullback fst snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) :
    Function.Surjective (prodMap (K := K) fst snd) := by
  rintro ⟨a, b⟩
  have hab : a.toHom ≫ X ↘ Spec (.of K) = b.toHom ≫ T ↘ Spec (.of K) := by
    rw [a.toHom_comp_over, b.toHom_comp_over]
  refine ⟨⟨H.lift a.toHom b.toHom hab, ?_⟩, ?_⟩
  · rw [← comp_over fst (Spec (.of K)), ← Category.assoc, H.lift_fst, a.toHom_comp_over]
  · exact Prod.ext (UnderlyingSpace.ext (H.lift_fst _ _ _))
      (UnderlyingSpace.ext (H.lift_snd _ _ _))

variable [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K]

/-- **The points of a product.** For a fibre square `P = X ×_K T` over a topological field `K`,
`w ↦ (pr₁ w, pr₂ w)` is a homeomorphism `P(K) ≃ₜ X(K) × T(K)`. -/
def homeomorphProdOfIsPullback
    (H : IsPullback fst snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) :
    UnderlyingSpace K P ≃ₜ UnderlyingSpace K X × UnderlyingSpace K T :=
  (isEmbedding_prodMap_of_isPullback H).toHomeomorphOfSurjective
    (surjective_prodMap_of_isPullback H)

/-- The homeomorphism `P(K) ≃ₜ X(K) × T(K)` sends `w` to `(pr₁ w, pr₂ w)`. -/
@[simp]
lemma homeomorphProdOfIsPullback_apply
    (H : IsPullback fst snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) (w : UnderlyingSpace K P) :
    homeomorphProdOfIsPullback H w = (mapFun fst w, mapFun snd w) :=
  rfl

/-- A morphism `i : Y → P` into the fibre product, followed by the homeomorphism
`P(K) ≃ₜ X(K) × T(K)`, is the pair of its components. -/
lemma homeomorphProdOfIsPullback_mapFun
    (H : IsPullback fst snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) {Y : Scheme.{u}}
    [Y.Over (Spec (.of K))] (i : Y ⟶ P) [i.IsOver (Spec (.of K))] (y : UnderlyingSpace K Y) :
    homeomorphProdOfIsPullback H (mapFun i y) =
      (mapFun (i ≫ fst) y, mapFun (i ≫ snd) y) := by
  rw [homeomorphProdOfIsPullback_apply]
  exact Prod.ext (UnderlyingSpace.ext (by simp [toHom_mapFun]))
    (UnderlyingSpace.ext (by simp [toHom_mapFun]))

/-- The slice `x ↦ (x, t)`: if `i : X ⟶ P` has first component `𝟙 X` and second component
constant at the `K`-point `t`, then on `K`-points
`homeomorphProdOfIsPullback H (mapFun i x) = (x, t)`. -/
lemma homeomorphProdOfIsPullback_mapFun_of_comp_eq
    (H : IsPullback fst snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) (i : X ⟶ P)
    [i.IsOver (Spec (.of K))] (t : UnderlyingSpace K T) (h₁ : i ≫ fst = 𝟙 X)
    (h₂ : i ≫ snd = (X ↘ Spec (.of K)) ≫ t.toHom) (x : UnderlyingSpace K X) :
    homeomorphProdOfIsPullback H (mapFun i x) = (x, t) := by
  rw [homeomorphProdOfIsPullback_apply]
  refine Prod.ext (UnderlyingSpace.ext ?_) (UnderlyingSpace.ext ?_)
  · rw [toHom_mapFun, toHom_mapFun, Category.assoc, h₁, Category.comp_id]
  · rw [toHom_mapFun, toHom_mapFun, Category.assoc, h₂, ← Category.assoc, x.toHom_comp_over,
      Category.id_comp]

end Product

section CanonicalProduct

variable {K : Type u} [Field K] (X T : Scheme.{u}) [X.Over (Spec (.of K))]
  [T.Over (Spec (.of K))]

/-- The first projection of `X ×_K T` is a morphism over `K`. -/
instance isOver_pullback_fst :
    (Limits.pullback.fst (X ↘ Spec (.of K)) (T ↘ Spec (.of K))).IsOver (Spec (.of K)) :=
  ⟨Limits.pullback.condition⟩

/-- The second projection of `X ×_K T` is a morphism over `K`. -/
instance isOver_pullback_snd :
    (Limits.pullback.snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))).IsOver (Spec (.of K)) :=
  ⟨rfl⟩

variable [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K]

/-- **The points of a product.** `(X ×_K T)(K) ≃ₜ X(K) × T(K)`, `w ↦ (pr₁ w, pr₂ w)`. -/
def homeomorphProd :
    UnderlyingSpace K (Limits.pullback (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) ≃ₜ
      UnderlyingSpace K X × UnderlyingSpace K T :=
  homeomorphProdOfIsPullback (IsPullback.of_hasPullback _ _)

/-- The homeomorphism `(X ×_K T)(K) ≃ₜ X(K) × T(K)` sends `w` to `(pr₁ w, pr₂ w)`. -/
@[simp]
lemma homeomorphProd_apply
    (w : UnderlyingSpace K (Limits.pullback (X ↘ Spec (.of K)) (T ↘ Spec (.of K)))) :
    homeomorphProd X T w =
      (mapFun (Limits.pullback.fst (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) w,
        mapFun (Limits.pullback.snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K))) w) :=
  rfl

end CanonicalProduct

section Metrizable

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The underlying space of a complex scheme is metrizable: it embeds in some `ℝᴺ`
(`exists_isClosedEmbedding_euclideanSpace`). -/
instance metrizableSpace_of_isComplexScheme : MetrizableSpace (UnderlyingSpace ℂ X) := by
  obtain ⟨N, F, hF⟩ := exists_isClosedEmbedding_euclideanSpace X
  exact hF.isEmbedding.metrizableSpace

/-- The underlying space of a complex scheme is second countable. -/
instance secondCountableTopology_of_isComplexScheme :
    SecondCountableTopology (UnderlyingSpace ℂ X) := by
  obtain ⟨N, F, hF⟩ := exists_isClosedEmbedding_euclideanSpace X
  exact hF.isEmbedding.secondCountableTopology

end Metrizable

section Manifold

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))] [QuasiCompact (X ↘ Spec (.of 𝕜))]

/-- The algebraic charts of `X(𝕜)` with values in `𝕜ⁿ`, for an integral `X` of finite type over
`𝕜` with `dimension X = n` all of whose `𝕜`-points are regular. -/
@[instance_reducible]
def algebraicChartedSpace {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X)
    (hreg : ∀ p, p ∈ regularPart 𝕜 X) :
    ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (UnderlyingSpace 𝕜 X) where
  atlas := {e | IsAlgebraicChart e}
  chartAt p := (exists_isAlgebraicChart_of_dimension_eq hn p (hreg p)).choose
  mem_chart_source p := (exists_isAlgebraicChart_of_dimension_eq hn p (hreg p)).choose_spec.1
  chart_mem_atlas p := (exists_isAlgebraicChart_of_dimension_eq hn p (hreg p)).choose_spec.2

/-- A chart lies in the atlas of `algebraicChartedSpace` if and only if it is algebraic. -/
lemma mem_atlas_algebraicChartedSpace_iff {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X)
    (hreg : ∀ p, p ∈ regularPart 𝕜 X)
    (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin n))) :
    e ∈ (algebraicChartedSpace hn hreg).atlas ↔ IsAlgebraicChart e :=
  Iff.rfl

/-- **A variety with only regular points is a manifold.** For a variety `X` of dimension `n`
over `𝕜` all of whose `𝕜`-points are regular, the algebraic charts make `X(𝕜)` a `C^ω` manifold
modelled on `𝕜ⁿ`. -/
theorem isManifold_algebraicChartedSpace {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension X)
    (hreg : ∀ p, p ∈ regularPart 𝕜 X) :
    letI := algebraicChartedSpace hn hreg
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) ω (UnderlyingSpace 𝕜 X) := by
  letI := algebraicChartedSpace hn hreg
  refine isManifold_of_contDiffOn _ _ _ ?_
  intro e e' he he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.range_id, Set.inter_univ, Set.preimage_id_eq, id_eq]
  exact IsAlgebraicChart.contDiffOn_symm_trans he he'

end Manifold

section Dimension

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  [IsSmoothVariety K (X ↘ Spec (.of K))]

/-- A smooth variety over `K` of relative dimension `n` has dimension `n` (Stacks 02NJ). -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of K))] : topologicalKrullDim X = n :=
  AlgebraicGeometry.topologicalKrullDim_eq_of_relativeDimension (X ↘ Spec (.of K))
    (SmoothOfRelativeDimension.relativeDimension n _)

/-- A smooth variety over `K` of dimension `n` is smooth of relative dimension `n` over `K`. -/
theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq {n : ℕ}
    (hn : topologicalKrullDim X = n) : SmoothOfRelativeDimension n (X ↘ Spec (.of K)) := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq (X ↘ Spec (.of K)) n
    fun x => ?_
  have heq : ((X ↘ Spec (.of K)) ⁻¹' {(X ↘ Spec (.of K)) x}) = (Set.univ : Set X) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let e : (X ↘ Spec (.of K)).fiber ((X ↘ Spec (.of K)) x) ≃ₜ X :=
    ((X ↘ Spec (.of K)).fiberHomeo _).trans ((Homeomorph.setCongr heq).trans
      (Homeomorph.Set.univ X))
  rw [topologicalKrullDimAt_eq_of_homeomorph e,
    ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible K X
      (X ↘ Spec (.of K))]
  exact hn

/-- A smooth variety over `K` is smooth of relative dimension `n` over `K` for some `n : ℕ`. -/
theorem exists_smoothOfRelativeDimension :
    ∃ n : ℕ, SmoothOfRelativeDimension n (X ↘ Spec (.of K)) := by
  obtain ⟨n, hn⟩ := Stacks.Intersection.exists_topologicalKrullDim_eq_natCast (X ↘ Spec (.of K))
  exact ⟨n, smoothOfRelativeDimension_of_topologicalKrullDim_eq hn⟩

end Dimension

section Stalk

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  [IsSmoothVariety K (X ↘ Spec (.of K))]

/-- The local ring of a smooth variety at a `K`-point is a regular local ring. -/
theorem isRegularLocalRing_stalk_of_isSmoothVariety (p : UnderlyingSpace K X) :
    IsRegularLocalRing (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint K))) :=
  ((show IsRegular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
    from (isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field (X ↘ Spec (.of K)))).2 _

/-- Every `K`-point of a smooth variety is regular. -/
theorem mem_regularPart_of_isSmoothVariety (p : UnderlyingSpace K X) :
    p ∈ regularPart K X :=
  (mem_regularPart_iff p).2 (isRegularLocalRing_stalk_of_isSmoothVariety p)

/-- Over an algebraically closed field, the local ring of a smooth variety of relative dimension
`n` at a `K`-point has dimension `n`. -/
theorem ringKrullDim_stalk_eq_of_smoothOfRelativeDimension [IsAlgClosed K] {n : ℕ}
    [SmoothOfRelativeDimension n (X ↘ Spec (.of K))] (p : UnderlyingSpace K X) :
    ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint K))) = n :=
  (Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
    (Stacks.Chow.fieldChowSituation K) (fun _ _ ↦ rfl) (X ↘ Spec (.of K)) (𝟙 X) _
    (equivClosedPoints X p).2).symm.trans
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := K) n)

end Stalk

section Smooth

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  [IsSmoothVariety 𝕜 (X ↘ Spec (.of 𝕜))] {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of 𝕜))]

/-- The algebraic charts of a smooth variety `X` of relative dimension `n` over `𝕜`, modelled on
`𝕜ⁿ`. -/
instance chartedSpace_of_isSmoothVariety :
    ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (UnderlyingSpace 𝕜 X) :=
  algebraicChartedSpace (topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := 𝕜) n).symm
    mem_regularPart_of_isSmoothVariety

/-- The charts of a smooth variety are algebraic. -/
theorem isAlgebraicChart_of_mem_atlas
    {e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin n))}
    (he : e ∈ atlas (EuclideanSpace 𝕜 (Fin n)) (UnderlyingSpace 𝕜 X)) :
    IsAlgebraicChart e :=
  he

/-- **A smooth variety of relative dimension `n` over `𝕜` is a `C^ω` manifold** modelled on
`𝕜ⁿ`. -/
instance isManifold_of_isSmoothVariety :
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) ω (UnderlyingSpace 𝕜 X) :=
  isManifold_algebraicChartedSpace (𝕜 := 𝕜) (X := X)
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := 𝕜) n).symm
    mem_regularPart_of_isSmoothVariety

end Smooth

section RegularEmbedding

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (.of K))]
  [IsSeparated (T ↘ Spec (.of K))]

/-- A `K`-point `Spec K ⟶ T` of a separated scheme `T` over `K` is a closed immersion. -/
instance isClosedImmersion_toHom (t : UnderlyingSpace K T) : IsClosedImmersion t.toHom := by
  haveI : IsClosedImmersion (t.toHom ≫ T ↘ Spec (.of K)) := by
    rw [t.toHom_comp_over]; infer_instance
  exact IsClosedImmersion.of_comp t.toHom (T ↘ Spec (.of K))

end RegularEmbedding

end UnderlyingSpace

end MMP
