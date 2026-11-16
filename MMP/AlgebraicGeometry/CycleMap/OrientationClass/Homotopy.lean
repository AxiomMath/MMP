module

public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.HomotopySlice
public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.HomotopyGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyPoint
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksChainBaseChange
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksExists
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected

/-!
# Homotopy invariance of the cap product with the orientation class of a slice
(Fulton, Lemma 19.2(c))

Let `T` be a non-singular connected complex curve, `X` a complex scheme and
`i_t : X → X × T`, `i_t(x) = (x, t)`. Then for every `a ∈ H_k(X × T)`,
`u_{i_t} ∩ a ∈ H_{k-2}(X)` is independent of `t ∈ T`.

**Proof.** The square of `i_t`, `X → Spec ℂ`, `pr₂ : X × T → T` and `t : Spec ℂ → T` is cartesian,
`t` is a regular closed immersion of codimension `1` and so is `i_t`, `pr₂` being flat
(`isRegularClosedImmersionOfCodim_slice`); hence `u_{i_t} = pr₂^* u_{t,T}`
(`MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq`), and `u_{t,T}` is the local
orientation class of the complex curve `T(ℂ)` at `t`
(`MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass`).
Transporting along the homeomorphism `(X × T)(ℂ) ≃ₜ X(ℂ) × T(ℂ)` with the projection formula,
`u_{i_t} ∩ a` becomes `pr^* u_{t,T} ∩ b ∈ H_{k-2}(X(ℂ) × {t})`, which does not depend on `t`
(`pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass`).

## Main results

* `MMP.cohomologyWithSupports.pullback_forget_pullback_forget`: pull-backs and forgetful maps
  of cohomology with supports commute.
* `MMP.UnderlyingSpace.hasProperNeighbourhoodDeformations_range_slice`: the image of the slice
  `X(ℂ) × {t}` has arbitrarily small proper neighbourhood deformations.
* `MMP.UnderlyingSpace.pushforward_sliceProj_capProductSupport_eq_fibreProj`: reduction of
  `u_{i_t} ∩ a` to the topological cap product on `X(ℂ) × T(ℂ)`.
* `MMP.UnderlyingSpace.pushforward_sliceProj_capProductSupport_eq`: Fulton's
  Lemma 19.2(c).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Lemma 19.2(c).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

universe u

namespace MMP

namespace cohomologyWithSupports

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- Pull-backs and forgetful maps of cohomology with supports commute: for `f ≫ g = h`,
`f^* (g^* x)`, with supports enlarged along the way, is `h^* x` with enlarged support. -/
lemma pullback_forget_pullback_forget {Y₀ Y₁ Y₂ : TopCat.{u}} (f : Y₂ ⟶ Y₁) (g : Y₁ ⟶ Y₀)
    (h : Y₂ ⟶ Y₀) (e : f ≫ g = h) {A B : Set Y₀} (hAB : A ⊆ B) {C : Set Y₁} (hC : g ⁻¹' B ⊆ C)
    (hD : h ⁻¹' A ⊆ f ⁻¹' C) (j : ℤ) (x : cohomologyWithSupports R M Y₀ A j) :
    (pullback R M f C j).hom ((forget R M Y₁ hC j).hom ((pullback R M g B j).hom
        ((forget R M Y₀ hAB j).hom x))) =
      (forget R M Y₂ hD j).hom ((pullback R M h A j).hom x) := by
  subst e
  simp only [forget, pullback]
  erw [relativeSingularCohomology.map_hom_map_hom, relativeSingularCohomology.map_hom_map_hom,
    relativeSingularCohomology.map_hom_map_hom, relativeSingularCohomology.map_hom_map_hom]
  congr 2

end cohomologyWithSupports

namespace UnderlyingSpace

open borelMooreHomology

variable (X : Scheme.{0}) {T : Scheme.{0}} [X.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]

/-- The projection `X(ℂ) × {t} → X(ℂ)` from the image of the slice, inverse to the slice. -/
def sliceProj (t : UnderlyingSpace ℂ T) :
    TopCat.of (range (UnderlyingSpace.map (K := ℂ) (slice X t))) ⟶
      TopCat.of (UnderlyingSpace ℂ X) :=
  TopCat.ofHom ⟨(sliceHomeomorph X t).symm, (sliceHomeomorph X t).symm.continuous⟩

/-- The projection `sliceProj X t : X(ℂ) × {t} → X(ℂ)` is proper. -/
lemma isProperMap_sliceProj (t : UnderlyingSpace ℂ T) : IsProperMap (sliceProj X t) :=
  (sliceHomeomorph X t).symm.isProperMap

/-- `(X × T)(ℂ) → X(ℂ) × T(ℂ)` as a morphism of `TopCat`. -/
def homeomorphProdHom :
    TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))) ⟶
      TopCat.of (TopCat.of (UnderlyingSpace ℂ X) × TopCat.of (UnderlyingSpace ℂ T)) :=
  TopCat.ofHom ⟨homeomorphProd X T, (homeomorphProd X T).continuous⟩

/-- The map `homeomorphProdHom : (X × T)(ℂ) → X(ℂ) × T(ℂ)` is proper. -/
lemma isProperMap_homeomorphProdHom : IsProperMap (homeomorphProdHom X (T := T)) :=
  (homeomorphProd X T).isProperMap

/-- `X(ℂ) × T(ℂ) → (X × T)(ℂ)`, the inverse of `homeomorphProdHom`. -/
def homeomorphProdInvHom :
    TopCat.of (TopCat.of (UnderlyingSpace ℂ X) × TopCat.of (UnderlyingSpace ℂ T)) ⟶
      TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))) :=
  TopCat.ofHom ⟨(homeomorphProd X T).symm, (homeomorphProd X T).symm.continuous⟩

/-- The map `homeomorphProdInvHom : X(ℂ) × T(ℂ) → (X × T)(ℂ)` is proper. -/
lemma isProperMap_homeomorphProdInvHom : IsProperMap (homeomorphProdInvHom X (T := T)) :=
  (homeomorphProd X T).symm.isProperMap

/-- `homeomorphProdInvHom` is a left inverse of `homeomorphProdHom`. -/
@[reassoc (attr := simp)]
lemma homeomorphProdHom_comp_homeomorphProdInvHom :
    homeomorphProdHom X (T := T) ≫ homeomorphProdInvHom X = 𝟙 _ :=
  ConcreteCategory.hom_ext _ _ fun p ↦ (homeomorphProd X T).symm_apply_apply p

/-- `homeomorphProdInvHom` is a right inverse of `homeomorphProdHom`. -/
@[reassoc (attr := simp)]
lemma homeomorphProdInvHom_comp_homeomorphProdHom :
    homeomorphProdInvHom X (T := T) ≫ homeomorphProdHom X = 𝟙 _ :=
  ConcreteCategory.hom_ext _ _ fun p ↦ (homeomorphProd X T).apply_symm_apply p

/-- The preimage of the slice `X(ℂ) × {t}` under `X(ℂ) × T(ℂ) → (X × T)(ℂ)` is the fibre of the
second projection over `t`. -/
lemma preimage_homeomorphProdInvHom_range_slice (t : UnderlyingSpace ℂ T) :
    homeomorphProdInvHom X ⁻¹' range (UnderlyingSpace.map (K := ℂ) (slice X t)) =
      prodSnd (TopCat.of (UnderlyingSpace ℂ X)) (TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t} := by
  rw [range_map_slice_eq_preimage]
  ext p
  change homeomorphProd X T ((homeomorphProd X T).symm p) ∈
    prodSnd (TopCat.of (UnderlyingSpace ℂ X)) (TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t} ↔ _
  rw [Homeomorph.apply_symm_apply]

variable [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]

/-- The image `X(ℂ) × {t}` of the slice is closed. -/
theorem isClosed_range_slice (t : UnderlyingSpace ℂ T) :
    IsClosed (range (UnderlyingSpace.map (K := ℂ) (slice X t))) := by
  rw [range_map_slice_eq_preimage]
  exact (isClosed_prodSnd_preimage_singleton (TopCat.of (UnderlyingSpace ℂ X))
    (T := TopCat.of (UnderlyingSpace ℂ T)) t).preimage
    (homeomorphProd X T).continuous

variable [IsComplexScheme X]

/-- The image `X(ℂ) × {t}` of the slice has arbitrarily small proper neighbourhood deformations
in `(X × T)(ℂ)`. -/
theorem hasProperNeighbourhoodDeformations_range_slice (t : UnderlyingSpace ℂ T) :
    HasProperNeighbourhoodDeformations (range (UnderlyingSpace.map (K := ℂ) (slice X t))) := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension (K := ℂ) (X := T)
  rw [range_map_slice_eq_preimage]
  exact (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
    (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
    (EuclideanSpace ℂ (Fin n)) t).preimage_homeomorph
    (homeomorphProd X T)

/-- Along `X(ℂ) × T(ℂ) ≅ (X × T)(ℂ)`, the orientation class `u_{i_t}` of the slice pulls back to
`pr^* u_{t,T}`, with supports enlarged to the fibre over `t`. -/
theorem pullback_homeomorphProdInvHom_eq_forget_pullback_prodSnd
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (R : Type) [CommRing R]
    {t : UnderlyingSpace ℂ T}
    {u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))))
      (range (UnderlyingSpace.map (K := ℂ) (slice X t))) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R (slice X t) 1 u)
    {uT : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (huT : MMP.Modules.IsRegularImbeddingOrientationClass R t.toHom 1 uT) :
    (cohomologyWithSupports.pullback R (ModuleCat.of R R) (homeomorphProdInvHom X)
      (range (UnderlyingSpace.map (K := ℂ) (slice X t))) (2 * 1 : ℕ)).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) _
        (preimage_homeomorphProdInvHom_range_slice X t).symm.le (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (prodSnd (TopCat.of (UnderlyingSpace ℂ X)) (TopCat.of (UnderlyingSpace ℂ T))) {t}
            (2 * 1 : ℕ)).hom
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le
            (2 * 1 : ℕ)).hom uT)) := by
  rw [← MMP.Modules.IsRegularImbeddingOrientationClass.pullback_eq R
    (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t)
    (isRegularClosedImmersionOfCodim_slice X hT t) (isPullback_slice X t) huT hu]
  have huT' : uT = (cohomologyWithSupports.forget R (ModuleCat.of R R) _
      (range_map_toHom t).ge _).hom
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom
        uT) := by
    rw [← ModuleCat.comp_apply, ← cohomologyWithSupports.forget_trans,
      cohomologyWithSupports.forget_refl]
    rfl
  conv_lhs => rw [huT']
  refine cohomologyWithSupports.pullback_forget_pullback_forget R (ModuleCat.of R R)
    (homeomorphProdInvHom X) (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
      (pullback.snd (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))))
    (prodSnd (TopCat.of (UnderlyingSpace ℂ X)) (TopCat.of (UnderlyingSpace ℂ T))) ?_ _ _ _ _ _
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  change mapFun (pullback.snd (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))
    ((homeomorphProd X T).symm p) = p.2
  exact congrArg Prod.snd ((homeomorphProd X T).apply_symm_apply p)

/-- **Reduction to the topological statement.** For the slice `i_t : X → X × T` of a non-singular
curve `T`, the image in `H_{k-2}(X)` of `u_{i_t} ∩ a ∈ H_{k-2}(i_t(X))` is the image of
`pr^*(u_{t,T}) ∩ b ∈ H_{k-2}(X(ℂ) × {t})`, `b ∈ H_k(X(ℂ) × T(ℂ))` the image of `a`. -/
theorem pushforward_sliceProj_capProductSupport_eq_fibreProj
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (R : Type) [CommRing R] (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))))) k)
    {t : UnderlyingSpace ℂ T}
    {u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))))
      (range (UnderlyingSpace.map (K := ℂ) (slice X t))) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R (slice X t) 1 u)
    {uT : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (huT : MMP.Modules.IsRegularImbeddingOrientationClass R t.toHom 1 uT) :
    (pushforward R (ModuleCat.of R R) (sliceProj X t) (isProperMap_sliceProj X t)
        (k - (2 * 1 : ℕ))).hom
        (capProductSupport R _ (isClosed_range_slice X t)
          (hasProperNeighbourhoodDeformations_range_slice X t) (2 * 1 : ℕ) k u a) =
      (pushforward R (ModuleCat.of R R)
          (fibreProj (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T)) t)
          (isProperMap_fibreProj _ (T := TopCat.of (UnderlyingSpace ℂ T)) t)
          (k - (2 * 1 : ℕ))).hom
        (capProductSupportPullback R
          (prodSnd (TopCat.of (UnderlyingSpace ℂ X)) (TopCat.of (UnderlyingSpace ℂ T)))
          (isClosed_singleton (X := TopCat.of (UnderlyingSpace ℂ T)) (x := t))
          (hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
            (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
            (EuclideanSpace ℂ (Fin 1)) t) (2 * 1 : ℕ) k
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom uT)
          ((pushforward R (ModuleCat.of R R) (homeomorphProdHom X)
            (isProperMap_homeomorphProdHom X) k).hom a)) := by
  have hf : IsProperMap (homeomorphProdInvHom X (T := T)) := isProperMap_homeomorphProdInvHom X
  have ha : (pushforward R (ModuleCat.of R R) (homeomorphProdInvHom X) hf k).hom
      ((pushforward R (ModuleCat.of R R) (homeomorphProdHom X)
        (isProperMap_homeomorphProdHom X) k).hom a) = a := by
    rw [pushforward_pushforward_apply, pushforward_congr' R
      (homeomorphProdHom_comp_homeomorphProdInvHom X) _ (by simpa using isProperMap_id),
      pushforward_id]
    rfl
  have hfS := preimage_homeomorphProdInvHom_range_slice X t
  have hd := hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
    (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
    (EuclideanSpace ℂ (Fin 1)) t
  have hd' : HasProperNeighbourhoodDeformations
      (homeomorphProdInvHom X ⁻¹' range (UnderlyingSpace.map (K := ℂ) (slice X t))) :=
    hfS ▸ hd
  have h2 := pushforward_restrictPreimage_capProductSupportPullback R (homeomorphProdInvHom X) hf
    (isClosed_range_slice X t) (hasProperNeighbourhoodDeformations_range_slice X t) hd'
    ((2 * 1 : ℕ) : ℤ) k u ((pushforward R (ModuleCat.of R R) (homeomorphProdHom X)
        (isProperMap_homeomorphProdHom X) k).hom a)
  rw [ha] at h2
  rw [← h2]
  refine (pushforward_pushforward_apply R _ (sliceProj X t) _ (isProperMap_sliceProj X t) _
    _).trans ?_
  rw [capProductSupportPullback_apply]
  rw [pullback_homeomorphProdInvHom_eq_forget_pullback_prodSnd X hT R hu huT, capProductSupport_forget_of_eq R _ hfS.symm
    (isClosed_prodSnd_preimage_singleton (TopCat.of (UnderlyingSpace ℂ X))
      (T := TopCat.of (UnderlyingSpace ℂ T)) t) _ hd]
  refine (pushforward_pushforward_apply R _ _ _ _ _ _).trans ?_
  rw [capProductSupportPullback_apply]
  refine congrArg (fun φ ↦ ModuleCat.Hom.hom φ _) (pushforward_congr' R ?_ _ _ _)
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  change mapFun (pullback.fst (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))
    ((homeomorphProd X T).symm p.1) = p.1.1
  exact congrArg Prod.fst ((homeomorphProd X T).apply_symm_apply p.1)

/-- **Fulton, Lemma 19.2(c).** Let `T` be a non-singular connected complex curve, `X` a complex
scheme and `i_t : X → X × T`, `i_t(x) = (x, t)`, for `t ∈ T(ℂ)`. For every
`a ∈ H_k(X × T)`, the class `u_{i_t} ∩ a ∈ H_{k-2}(X)` does not depend on `t`: for the
orientation classes `u`, `u'` of the regular closed immersions `i_t`, `i_{t'}`
(`MMP.Modules.IsRegularImbeddingOrientationClass`), the cap products `u ∩ a ∈ H_{k-2}(i_t(X))` and
`u' ∩ a ∈ H_{k-2}(i_{t'}(X))` (`capProductSupport`) have the same image in `H_{k-2}(X)` under the
identifications `i_t(X) ≅ X`, `i_{t'}(X) ≅ X` (`sliceProj`). -/
theorem pushforward_sliceProj_capProductSupport_eq
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (R : Type) [CommRing R] (k : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))))) k)
    {t t' : UnderlyingSpace ℂ T}
    {u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))))
      (range (UnderlyingSpace.map (K := ℂ) (slice X t))) (2 * 1 : ℕ)}
    {u' : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ)))))
      (range (UnderlyingSpace.map (K := ℂ) (slice X t'))) (2 * 1 : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R (slice X t) 1 u)
    (hu' : MMP.Modules.IsRegularImbeddingOrientationClass R (slice X t') 1 u') :
    (pushforward R (ModuleCat.of R R) (sliceProj X t) (isProperMap_sliceProj X t)
        (k - (2 * 1 : ℕ))).hom
        (capProductSupport R _ (isClosed_range_slice X t)
          (hasProperNeighbourhoodDeformations_range_slice X t) (2 * 1 : ℕ) k u a) =
      (pushforward R (ModuleCat.of R R) (sliceProj X t') (isProperMap_sliceProj X t')
        (k - (2 * 1 : ℕ))).hom
        (capProductSupport R _ (isClosed_range_slice X t')
          (hasProperNeighbourhoodDeformations_range_slice X t') (2 * 1 : ℕ) k u' a) := by
  obtain ⟨uT, huT⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t)
  obtain ⟨uT', huT'⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t')
  rw [pushforward_sliceProj_capProductSupport_eq_fibreProj X hT R k a hu huT,
    pushforward_sliceProj_capProductSupport_eq_fibreProj X hT R k a hu' huT']
  haveI : ConnectedSpace (TopCat.of (UnderlyingSpace ℂ T)) := connectedSpace_of_isSmoothVariety t
  exact pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass R
    (isOrientedAtlas_of_isManifold_complex _) (by norm_num) curveOrientationBasis
    (fun s ↦ hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton
      (TopCat.of (UnderlyingSpace ℂ X)) (T := TopCat.of (UnderlyingSpace ℂ T))
      (EuclideanSpace ℂ (Fin 1)) s) k _
    (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R hT t huT)
    (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R hT t'
      huT')

end UnderlyingSpace

end MMP
