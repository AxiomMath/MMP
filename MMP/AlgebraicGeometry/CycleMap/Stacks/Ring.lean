module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RingDiagonal
public import MMP.AlgebraicGeometry.CycleMap.RingDiagonalSwap
public import MMP.AlgebraicGeometry.Chow.SelfIntersectionUnit
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksExists

/-!
# The cycle class map is multiplicative on Stacks' Chow groups (Fulton, Corollary 19.2(b))

Let `X` be a non-singular complex variety of dimension `n` (`AlgebraicGeometry.IsSmoothVariety`
with `SmoothOfRelativeDimension n`), with fundamental class `μ_X = cl([X]) ∈ H_{2n} X`. For
`x ∈ A_k X` and `y ∈ A_l X` of Stacks' Chow groups with `cl(y) = d ∩ μ_X`, `d ∈ H^{2q} X`,
`l + q = n`, the cycle class of the Stacks intersection product `x · y`
(`Stacks.Chow.selfIntersectionProduct`, Stacks 0FC0, formed with the Gysin class
`δ^! = c(δ, 𝒩)` of the diagonal, Stacks 0FBK) is `cl(x · y) = d ∩ cl(x)` in `H_{2k-2q} X`
(`MMP.Chow.chowCycleClass_selfIntersectionProduct_eq_capProduct`).

The proof is Fulton's proof of Proposition 19.2 for `f = 1_X`:
`cl(x · y) = u_δ ∩ cl(x × y)` (Theorem 19.2 for `δ`,
`MMP.Chow.pushforward_chowCycleClass_selfIntersectionProduct`), `cl(x × y) = cl(x) × (d ∩ μ_X)`
(Example 19.1.9, `MMP.Chow.chowCycleClass_chowExteriorProduct`), the diagonal swap
`u_δ ∩ (cl(x) × (d ∩ μ_X)) = d ∩ (u_δ ∩ (cl(x) × μ_X))`
(`MMP.borelMooreHomology.pushforward_capProduct_eq_capProductSupportPullback_exteriorProduct`), and
`u_δ ∩ (cl(x) × μ_X) = cl(x · [X]) = cl(x)` (Theorem 19.2 for `δ` and
`MMP.Chow.selfIntersectionProduct_fundamentalChowClass`).

## Main results

* `MMP.Chow.chowCycleClass_selfIntersectionProduct_eq_capProduct`: `cl(x · y) = d ∩ cl(x)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Proposition 19.2 and Corollary 19.2.
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf TensorProduct

namespace MMP.Chow

attribute [local instance] isOver_pullbackDiagonal isClosedImmersion_pullbackDiagonal

/-- `chowGroupCongrDegree` and `chowGroupDegreeEquiv` are the same transport. -/
theorem chowGroupCongrDegree_eq_chowGroupDegreeEquiv {C : ChowSituation.{0}} {Z : Scheme.{0}}
    (s : Z ⟶ C.S) [LocallyOfFiniteType s] {j k : ℤ} (h : j = k) (a : chowGroup C s j) :
    chowGroupCongrDegree C s h a = chowGroupDegreeEquiv C s h a := by
  subst h
  rfl

/-- The cycle class commutes with the transport along an equality of degrees. -/
theorem chowCycleClass_chowGroupCongrDegree (R : Type) [CommRing R] {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] {a b : ℕ} (h : (a : ℤ) = b)
    (z : chowGroup (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) a) :
    chowCycleClass R b (chowGroupCongrDegree (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) h z) =
      BorelMooreCross.congrDegree R _ (by rw [Nat.cast_inj.1 h]) (chowCycleClass R a z) := by
  obtain rfl := Nat.cast_inj.1 h
  rfl

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [IsSmoothVariety ℂ (X ↘ Spec (.of ℂ))] {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
  (R : Type) [CommRing R]

/-- A variety is quasi-compact. -/
theorem compactSpace_of_isSmoothVariety : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))

/-- **The cycle class of a Stacks intersection product** (Fulton, proof of Corollary 19.2(b)).
Let `X` be a non-singular complex variety of dimension `n` with fundamental class
`μ_X = cl([X]_n)`, `x ∈ A_k X`, `y ∈ A_l X` of Stacks' Chow groups, and `d ∈ H^{2q} X` with
`l + q = n` and `cl(y) = d ∩ μ_X`. Then for `k = m + q`, `cl(x · y) = d ∩ cl(x)` in `H_{2m} X`,
for the Stacks intersection product `x · y = δ^!(x × y)` formed with the class `c(δ, 𝒩)` of the
normal sheaf of the diagonal. -/
theorem chowCycleClass_selfIntersectionProduct_eq_capProduct {k l q m : ℕ} (hl : l + q = n)
    (hk : k = m + q)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (y : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) l)
    (d : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) Set.univ
      (2 * q : ℕ))
    (hy : chowCycleClass R l y = BorelMooreCross.congrDegree R _ (by omega)
      (borelMooreHomology.capProduct R _ Set.univ (2 * q : ℕ) (2 * n : ℕ) d
        (chowCycleClass R n (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n)))) :
    chowCycleClass R m
        (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (by omega : (k : ℤ) + l - n = m)
          (selfIntersectionProduct (fieldChowSituation ℂ)
            (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
            (X ↘ Spec (.of ℂ)) n
            (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
              (pullback.diagonal (X ↘ Spec (.of ℂ)))
              (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
              (isRegularClosedImmersionOfCodim_diagonal X n)) k l x y)) =
      BorelMooreCross.congrDegree R _ (by omega)
        (borelMooreHomology.capProduct R _ Set.univ (2 * q : ℕ) (2 * k : ℕ) d
          (chowCycleClass R k x)) := by
  have hΔ := isRegularClosedImmersionOfCodim_diagonal X n
  haveI := compactSpace_of_isSmoothVariety (X := X)
  obtain ⟨u, hu⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (i := (pullback.diagonal (X ↘ Spec (.of ℂ)) :
      X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) hΔ
  set μ := chowCycleClass R n (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n)
  -- `u_δ ∩ (cl(x) × μ_X) = cl(x · [X]) = cl(x)`
  have hunit := pushforward_chowCycleClass_selfIntersectionProduct hΔ R (k := k) (l := n)
    (m := k) rfl hu x (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n)
  rw [chowGroupCongrDegree_eq_chowGroupDegreeEquiv,
    selfIntersectionProduct_fundamentalChowClass hΔ, chowGroupCongrDegree_rfl,
    chowCycleClass_chowExteriorProduct, productClass, borelMooreHomology.pushforward_congrDegree,
    borelMooreHomology.capProductSupportPullback_congrDegree_apply,
    borelMooreHomology.congrDegree_congrDegree] at hunit
  -- the swap
  have hT := borelMooreHomology.pushforward_capProduct_eq_capProductSupportPullback_exteriorProduct
    R (productHomeomorph ℂ X X).symm
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
      (pullback.snd (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))
    map_snd_productHomeomorph_symm _ _ _ _
    (isProperMap_fibreSquarePointsHom (IsPullback.id_vert _)) map_snd_map_diagonal u μ
    (j := ((2 * q : ℕ) : ℤ)) ⟨q, by push_cast; ring⟩ d _ (chowCycleClass R k x) hunit
  apply pushforward_injective_of_isClosedEmbedding _
    (isProperMap_fibreSquarePointsHom (IsPullback.id_vert
      (pullback.diagonal (X ↘ Spec (.of ℂ)) : X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))
    isClosedEmbedding_fibreSquarePointsHom_id_vert surjective_fibreSquarePointsHom_id_vert
    ((2 * m : ℕ) : ℤ)
  rw [pushforward_chowCycleClass_selfIntersectionProduct hΔ R (by omega) hu x y,
    borelMooreHomology.pushforward_congrDegree]
  refine Eq.trans ?_ (congrArg (BorelMooreCross.congrDegree R _ _) hT).symm
  simp only [chowCycleClass_chowGroupCongrDegree, chowCycleClass_chowExteriorProduct]
  simp only [hy, productClass_congrDegree, borelMooreHomology.congrDegree_congrDegree]
  exact congrDegree_capProductSupportPullback_congrDegree _ _ _ _ u _ (by omega) _ _

end MMP.Chow
