module

public import MMP.AlgebraicGeometry.Variety.StalkDimensionClosedPoint

/-!
# Euclidean neighbourhoods of regular points

Let `X` be an affine scheme of finite type over `ℂ` (an algebraically closed `RCLike` field) and
`p ∈ X(ℂ)` a point whose image is regular. Near `p` the space `X(ℂ)` is homeomorphic to the zero
set of a polynomial submersion `ℂ^ι → ℂ^σ` of relative dimension `dim 𝒪_{X,p}`, and such a zero
set is locally homeomorphic to `ℂ^{|ι| - |σ|}`. So `p` has a classically open neighbourhood in
`X(ℂ)` homeomorphic to an open subset of `ℂ^{dim 𝒪_{X,p}}`; when `X` is a variety the exponent is
`dim X`.

## Main results

* `MMP.UnderlyingSpace.exists_openPartialHomeomorph_euclidean_of_isAffine`: a
  regular `ℂ`-point of an affine scheme of finite type over `ℂ` is the source of a partial
  homeomorphism onto an open subset of `ℂ^{dim 𝒪_{X,p}}`.
* `MMP.UnderlyingSpace.exists_openPartialHomeomorph_euclidean_dimension_of_isAffine`:
  for an affine variety, the exponent is `dim X`.
* `MMP.UnderlyingSpace.exists_openPartialHomeomorph_euclidean`: for any variety
  `X` over `ℂ`, every point of `X_reg(ℂ)` has an open neighbourhood inside `X_reg(ℂ)`
  homeomorphic to an open subset of `ℂ^{dim X}`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open MMP.Intersection.Scheme (dimension)

universe u

namespace MMP

namespace UnderlyingSpace

section Affine

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]
  [IsAffine X] [Algebra 𝕜 Γ(X, ⊤)] [Algebra.FiniteType 𝕜 Γ(X, ⊤)]

/-- **A regular point has a Euclidean neighbourhood.** Let `X` be an affine scheme of finite
type over `ℂ` (an algebraically closed `RCLike` field) and `p ∈ X(ℂ)` a point whose image is
regular. Then there is a partial homeomorphism from `X(ℂ)` onto an open subset of `ℂ^m`, with
`m = dim 𝒪_{X,p}`, whose (open) source contains `p`. -/
theorem exists_openPartialHomeomorph_euclidean_of_isAffine
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X) (p : UnderlyingSpace 𝕜 X)
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ regularLocus X) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin m))),
      p ∈ e.source ∧ (m : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint 𝕜))) := by
  obtain ⟨g, hg, ι, σ, _, _, _, P, hP, hsub, ⟨φ⟩⟩ :=
    exists_nonvanishingLocus_homeomorph_levelSet hK p hp
  let z := φ ⟨p, hg⟩
  let e₀ := φ.toOpenPartialHomeomorph.trans (SmoothLevelSet.chart hsub z.2)
  refine ⟨_, e₀.lift_openEmbedding (isOpen_nonvanishingLocus g).isOpenEmbedding_subtypeVal, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨⟨p, hg⟩, ?_, rfl⟩
    simp only [e₀, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Homeomorph.toOpenPartialHomeomorph_apply, Set.univ_inter, Set.mem_preimage]
    exact SmoothLevelSet.mem_chart_source hsub z.2
  · rw [← hP]
    simp only [SmoothLevelSet.dim, Module.finrank_fintype_fun_eq_card,
      Algebra.Presentation.dimension, Nat.card_eq_fintype_card]

/-- **Euclidean neighbourhoods of dimension `dim X`.** For an affine variety `X` over `ℂ`, every
regular `ℂ`-point `p` is in the open source of a partial homeomorphism from `X(ℂ)` onto an open
subset of `ℂ^n`, where `n = dim X`. -/
theorem exists_openPartialHomeomorph_euclidean_dimension_of_isAffine
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))]
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X) (p : UnderlyingSpace 𝕜 X)
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ regularLocus X) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin m))),
      p ∈ e.source ∧ (m : WithBot ℕ∞) = dimension X := by
  obtain ⟨m, e, he, hm⟩ := exists_openPartialHomeomorph_euclidean_of_isAffine hK p hp
  exact ⟨m, e, he, hm.trans (ringKrullDim_stalk_eq_dimension p)⟩

end Affine

section Variety

/-- The structure map `K → Γ(X, ⊤)` of an affine scheme locally of finite type over `K` is of
finite type. -/
theorem finiteType_structureRingHom {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsAffine X] [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    (structureRingHom K X).FiniteType := by
  rw [structureRingHom, CommRingCat.hom_comp]
  exact (HasRingHomProperty.appTop @LocallyOfFiniteType (X ↘ Spec (.of K)) inferInstance).comp
    (.of_surjective _ (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)

variable {𝕜 : Type u} [RCLike 𝕜] [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))]

/-- **The regular part of a complex variety is locally Euclidean of dimension `dim X`.** Let `X`
be a variety over `ℂ` (an algebraically closed `RCLike` field). Every `p ∈ X_reg(ℂ)` lies in the
open source of a partial homeomorphism from `X(ℂ)` onto an open subset of `ℂ^n`, `n = dim X`,
whose source consists of regular points. -/
theorem exists_openPartialHomeomorph_euclidean [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))] [QuasiCompact (X ↘ Spec (.of 𝕜))]
    (p : UnderlyingSpace 𝕜 X) (hp : p ∈ regularPart 𝕜 X) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) (EuclideanSpace 𝕜 (Fin m))),
      p ∈ e.source ∧ e.source ⊆ regularPart 𝕜 X ∧ (m : WithBot ℕ∞) = dimension X := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint 𝕜)) (U := ⊤) trivial
  letI : U.toScheme.Over (Spec (.of 𝕜)) := ⟨U.ι ≫ X ↘ Spec (.of 𝕜)⟩
  haveI : U.ι.IsOver (Spec (.of 𝕜)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of 𝕜)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of 𝕜)))
  letI : Algebra 𝕜 Γ(U, ⊤) := (structureRingHom 𝕜 U).toAlgebra
  haveI : Algebra.FiniteType 𝕜 Γ(U, ⊤) := finiteType_structureRingHom
  obtain ⟨q, hq⟩ : p ∈ Set.range (mapFun (K := 𝕜) U.ι) := by
    rwa [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, Scheme.Opens.opensRange_ι,
      top_le_preimage_iff]
  have hx : p.toHom (IsLocalRing.closedPoint 𝕜) = U.ι (q.toHom (IsLocalRing.closedPoint 𝕜)) := by
    rw [← hq, toHom_mapFun]
    rfl
  let y := q.toHom (IsLocalRing.closedPoint 𝕜)
  let φ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have hreg : y ∈ regularLocus U := by
    have h := (mem_regularPart_iff p).mp hp
    rw [hx] at h
    haveI : IsRegularLocalRing (X.presheaf.stalk (U.ι y)) := h
    exact IsRegularLocalRing.of_ringEquiv (R := X.presheaf.stalk (U.ι y)) φ.symm
  obtain ⟨m, e, hqe, hm⟩ := exists_openPartialHomeomorph_euclidean_of_isAffine rfl q hreg
  refine ⟨m, (e.lift_openEmbedding (isOpenEmbedding_map_of_isOpenImmersion U.ι)).restrOpen _
    isOpen_regularPart, ?_, Set.inter_subset_right, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨⟨q, hqe, hq⟩, hp⟩
  · rw [hm, ringKrullDim_eq_of_ringEquiv φ, ← ringKrullDim_stalk_eq_dimension p]
    exact congrArg (fun x ↦ ringKrullDim (X.presheaf.stalk x)) hx.symm

end Variety

end UnderlyingSpace

end MMP
