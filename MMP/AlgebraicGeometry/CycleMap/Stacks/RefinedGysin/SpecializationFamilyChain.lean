module

public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.HomotopyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.TrivialFamilyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyPoint

/-!
# The cap/cup chain of Fulton's Theorem 19.2, for Stacks orientation classes

Let `T` be a non-singular complex curve, `X` a complex scheme, `M` a scheme over `ℂ` with a
morphism `ρ : M → T` and a closed immersion `e : X × T → M` with `ρ ∘ e = pr₂`. For
`w ∈ H^{2d}(M, M - A)`, `A = e((X × T)(ℂ))`, `a ∈ H_k M` and the orientation classes `u_t`,
`u_{t'}` of two points `t, t' : Spec ℂ → T` in the sense of Stacks regular immersions
(`MMP.Modules.IsRegularImbeddingOrientationClass`), the classes `w|_{M_t} ∩ (ρ^* u_t ∩ a)` and
`w|_{M_{t'}} ∩ (ρ^* u_{t'} ∩ a)`, read in `H_{k-2-2d}(X)` along `A ∩ M_t ≅ X(ℂ)`, agree. This is
the family chain of the Fulton proof (`MMP.UnderlyingSpace.pushforward_interFibre_...`, in
`MMP.AlgebraicGeometry.CycleMap.RefinedGysin.TrivialFamily`) with the orientation classes
of points taken on Stacks' vector bundles: both are the local
orientation class of the Riemann surface `T(ℂ)`
(`MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass`). In the
proof on Stacks' Chow groups, `M = M°` is Stacks' open deformation space, `T = 𝐏¹_ℂ`,
`ρ = MMP.Chow.strictTransformComplToLine` and `e` the trivial family
(`MMP.Chow.lineToStrictTransformCompl`).

## Main results

* `UnderlyingSpace.pushforward_interFibre_capProductSupportPullback_eq_of_stacksOrientationClass`:
  the family chain.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

namespace MMP

namespace UnderlyingSpace

open borelMooreHomology

variable {X T M : Scheme.{0}} [X.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
  [M.Over (Spec (.of ℂ))]
  (e : pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)) ⟶ M) [IsClosedImmersion e]
  [e.IsOver (Spec (.of ℂ))]

variable [IsComplexScheme X] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]

/-- **The cap/cup chain of Fulton's Theorem 19.2, for Stacks orientation classes.** Let `T` be
a non-singular curve, `X` a
complex scheme, `e : X × T → M` a closed immersion and `ρ : M → T` with `ρ ∘ e = pr₂`;
`A = e((X × T)(ℂ))`. For `w ∈ H^{2d}(M, M - A)`, `a ∈ H_k M`, points `t`, `t'` of `T` with
orientation classes `u_t`, `u_{t'}` (`MMP.Modules.IsRegularImbeddingOrientationClass` of
`t : Spec ℂ → T`),
`w|_{M_t} ∩ (ρ^* u_t ∩ a) = w|_{M_{t'}} ∩ (ρ^* u_{t'} ∩ a)` in `H_{k-2-2d}(X)`, both sides read
in `X(ℂ)` along `A ∩ M_t ≅ X(ℂ)`. The sets carrying the cap products are assumed to have
arbitrarily small proper neighbourhood deformations. -/
theorem pushforward_interFibre_capProductSupportPullback_eq_of_stacksOrientationClass
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (R : Type) [CommRing R]
    (ρ : M ⟶ T) [ρ.IsOver (Spec (.of ℂ))] (h : e ≫ ρ = pullback.snd _ _)
    (hAd : HasProperNeighbourhoodDeformations (range (UnderlyingSpace.map (K := ℂ) e)))
    (hZd : ∀ s, HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}))
    (hAZd : ∀ s, HasProperNeighbourhoodDeformations
      (range (UnderlyingSpace.map (K := ℂ) e) ∩ (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}))
    (hd₁ : ∀ s, HasProperNeighbourhoodDeformations
      (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
        ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s}) ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) e)))
    (hd₂ : ∀ s, HasProperNeighbourhoodDeformations
      (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
        (range (UnderlyingSpace.map (K := ℂ) e)) ⁻¹'
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {s})))
    (d : ℕ) (k : ℤ)
    (w : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ M))
      (range (UnderlyingSpace.map (K := ℂ) e)) (2 * d : ℕ))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ M)) k)
    {t t' : UnderlyingSpace ℂ T}
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t'.toHom)) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R t.toHom 1 u)
    (hu' : MMP.Modules.IsRegularImbeddingOrientationClass R t'.toHom 1 u') :
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t})
            (range (UnderlyingSpace.map (K := ℂ) e)) ≫
          subsetInclusionOfSubset (inter_comm _ _).le) ≫
          interFibreProj (X := TopCat.of (UnderlyingSpace ℂ X))
            (T := TopCat.of (UnderlyingSpace ℂ T)) (Y := TopCat.of (UnderlyingSpace ℂ M))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
            (trivialFamilyHomeomorph e) (map_trivialFamilyHomeomorph e ρ h) t)
        ((isProperMap_interFibreProj (X := TopCat.of (UnderlyingSpace ℂ X))
            (T := TopCat.of (UnderlyingSpace ℂ T)) (Y := TopCat.of (UnderlyingSpace ℂ M))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
            (trivialFamilyHomeomorph e) (map_trivialFamilyHomeomorph e ρ h) t).comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)).hom.continuous).inter
              (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range)
            (inter_comm _ _).le).comp
            (isProperMap_preimageInterHom
              (isClosed_singleton.preimage (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)).hom.continuous)
              (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range)))
        (k - (2 * 1 : ℕ) - (2 * d : ℕ))).hom
      (capProductSupportPullback R (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t}))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range (hd₁ t)
        (2 * d : ℕ) (k - (2 * 1 : ℕ)) w
        (capProductSupportPullback R (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
          isClosed_singleton (hZd t) (2 * 1 : ℕ) k
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom u)
          a)) =
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t'})
            (range (UnderlyingSpace.map (K := ℂ) e)) ≫
          subsetInclusionOfSubset (inter_comm _ _).le) ≫
          interFibreProj (X := TopCat.of (UnderlyingSpace ℂ X))
            (T := TopCat.of (UnderlyingSpace ℂ T)) (Y := TopCat.of (UnderlyingSpace ℂ M))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
            (trivialFamilyHomeomorph e) (map_trivialFamilyHomeomorph e ρ h) t')
        ((isProperMap_interFibreProj (X := TopCat.of (UnderlyingSpace ℂ X))
            (T := TopCat.of (UnderlyingSpace ℂ T)) (Y := TopCat.of (UnderlyingSpace ℂ M))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
            (trivialFamilyHomeomorph e) (map_trivialFamilyHomeomorph e ρ h) t').comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)).hom.continuous).inter
              (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range)
            (inter_comm _ _).le).comp
            (isProperMap_preimageInterHom
              (isClosed_singleton.preimage (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)).hom.continuous)
              (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range)))
        (k - (2 * 1 : ℕ) - (2 * d : ℕ))).hom
      (capProductSupportPullback R (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ M))
          ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t'}))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range (hd₁ t')
        (2 * d : ℕ) (k - (2 * 1 : ℕ)) w
        (capProductSupportPullback R (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
          isClosed_singleton (hZd t') (2 * 1 : ℕ) k
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t').le _).hom u')
          a)) := by
  have : ConnectedSpace (TopCat.of (UnderlyingSpace ℂ T)) :=
    connectedSpace_of_isSmoothVariety t
  have key := pushforward_interFibre_capProductSupportPullback_eq_of_isLocalOrientationClass
    (X := TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
    (Y := TopCat.of (UnderlyingSpace ℂ M)) (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ))
    (trivialFamilyHomeomorph e) R (isOrientedAtlas_of_isManifold_complex _) (by norm_num)
    curveOrientationBasis (map_trivialFamilyHomeomorph e ρ h)
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) e).isClosed_range hAd hZd hAZd hd₁ hd₂
    (fun s ↦ hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
      (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
      (EuclideanSpace ℂ (Fin 1)) s)
    ⟨d, by push_cast; ring⟩ k w a
    (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R hT t hu)
    (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R hT t' hu')
  exact key

end UnderlyingSpace

end MMP
