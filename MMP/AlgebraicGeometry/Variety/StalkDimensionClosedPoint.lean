module

public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointLocalChart
public import MMP.AlgebraicGeometry.Variety.Basic

/-!
# The local ring at a closed point of a variety has the dimension of the variety

Let `X` be a variety over a field `K`. At every closed point `x` of `X` the local ring
`𝒪_{X,x}` has Krull dimension `dim X` (Stacks 02QO, over the base `Spec K` with the zero
dimension function). When `K` is algebraically closed the closed points are the `K`-points, so
this holds at every point of the underlying space `X(K)`.

Combined with the local charts at regular points, this says: near a regular `ℂ`-point of an
affine variety `X` of dimension `n`, the space `X(ℂ)` is homeomorphic to the level set of a
polynomial submersion of relative dimension exactly `n`.

## Main results

* `MMP.ringKrullDim_stalk_eq_dimension_of_isClosed`: `dim 𝒪_{X,x} = dim X` at a
  closed point `x` of a variety `X`.
* `MMP.UnderlyingSpace.ringKrullDim_stalk_eq_dimension`: the same at the point of
  `X` underlying a `K`-point, `K` algebraically closed.
* `MMP.UnderlyingSpace.exists_nonvanishingLocus_homeomorph_levelSet_dimension`:
  a regular `ℂ`-point of an affine variety of dimension `n` has a classically open neighbourhood
  homeomorphic to the level set of a polynomial submersion of relative dimension `n`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Appendix B.1.
* [The Stacks project, Tag 02QO][stacks-project]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open MMP.Intersection.Scheme (dimension)

universe u

namespace MMP

/-- **The local ring at a closed point of a variety has the dimension of the variety.** -/
theorem ringKrullDim_stalk_eq_dimension_of_isClosed (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = dimension X :=
  (Stacks.Chow.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
    (Stacks.Chow.fieldChowSituation K) (fun _ _ ↦ rfl) (X ↘ Spec (.of K)) (𝟙 X) x hx).symm

namespace UnderlyingSpace

/-- Over an algebraically closed field, the local ring of a variety `X` at (the point underlying)
any `K`-point has Krull dimension `dim X`. -/
theorem ringKrullDim_stalk_eq_dimension {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))] (p : UnderlyingSpace K X) :
    ringKrullDim (X.presheaf.stalk (p.toHom (IsLocalRing.closedPoint K))) = dimension X :=
  ringKrullDim_stalk_eq_dimension_of_isClosed K X _ (equivClosedPoints X p).2

/-- **Local charts of dimension `dim X` at a regular point.** Let `X` be an affine variety over
`ℂ` (an algebraically closed `RCLike` field) and `p ∈ X(ℂ)` a point whose image is regular.
Then there are `g ∈ Γ(X, ⊤)` with `g(p) ≠ 0` and a submersive presentation `P` of `Γ(X, ⊤)_g`
of relative dimension `dim X`, and the open neighbourhood `{g ≠ 0}` of `p` in `X(ℂ)` is
homeomorphic to the zero set of the relation map of `P`, a submersion on `ℂ^ι`. -/
theorem exists_nonvanishingLocus_homeomorph_levelSet_dimension {𝕜 : Type u} [RCLike 𝕜]
    [IsAlgClosed 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of 𝕜))] [QuasiCompact (X ↘ Spec (.of 𝕜))] [IsAffine X]
    [Algebra 𝕜 Γ(X, ⊤)] [Algebra.FiniteType 𝕜 Γ(X, ⊤)]
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X) (p : UnderlyingSpace 𝕜 X)
    (hp : p.toHom (IsLocalRing.closedPoint 𝕜) ∈ regularLocus X) :
    ∃ g : Γ(X, ⊤), p ∈ nonvanishingLocus 𝕜 g ∧
      ∃ (ι σ : Type) (_ : Fintype ι) (_ : Fintype σ) (_ : DecidableEq σ)
        (P : Algebra.SubmersivePresentation 𝕜 (Localization.Away g) ι σ),
        (P.dimension : WithBot ℕ∞) = dimension X ∧
        SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) ⊤ Set.univ
          (SubmersivePresentationLevelSet.relMap P.toPresentation) ∧
        Nonempty (nonvanishingLocus 𝕜 g ≃ₜ SmoothLevelSet.levelSet Set.univ
          (SubmersivePresentationLevelSet.relMap P.toPresentation)) := by
  obtain ⟨g, hg, ι, σ, i1, i2, i3, P, hP, hsub, hhom⟩ :=
    exists_nonvanishingLocus_homeomorph_levelSet hK p hp
  exact ⟨g, hg, ι, σ, i1, i2, i3, P, hP.trans (ringKrullDim_stalk_eq_dimension p), hsub, hhom⟩

end UnderlyingSpace

end MMP
