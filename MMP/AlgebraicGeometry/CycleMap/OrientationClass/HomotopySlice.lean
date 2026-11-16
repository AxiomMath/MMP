module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.HomotopyPointGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ChainBaseChangeGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra
public import MMP.AlgebraicGeometry.Pullbacks.Over
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.ComplexScheme

/-!
# The slices `X × {t}` of a product with a curve

For schemes `X`, `T` over a field `K` and a `K`-point `t` of `T`, the *slice*
`i_t : X → X ×_K T`, `x ↦ (x, t)`, is the base change of the point `t : Spec K → T` along the
second projection: the square with sides `i_t`, `X → Spec K`, `pr₂ : X × T → T` and `t` is
cartesian. For `T` a non-singular curve, `t` is a regular closed immersion of codimension one
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim`), hence so is `i_t`,
`pr₂` being flat. On complex points, `i_t` identifies `X(ℂ)` with the closed subset
`X(ℂ) × {t}` of `(X × T)(ℂ) = X(ℂ) × T(ℂ)`.

## Main definitions

* `MMP.UnderlyingSpace.slice`: the slice `i_t : X → X ×_K T`.
* `MMP.UnderlyingSpace.sliceHomeomorph`: `X(ℂ) ≃ₜ i_t(X(ℂ))`.

## Main results

* `MMP.UnderlyingSpace.isPullback_slice`: the cartesian square of `i_t`.
* `MMP.UnderlyingSpace.isRegularClosedImmersionOfCodim_slice`: `i_t` is a regular closed
  immersion of codimension one for a non-singular curve `T`.
* `MMP.UnderlyingSpace.range_map_slice`: `i_t(X(ℂ)) = pr₂⁻¹(t)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology

namespace MMP

namespace UnderlyingSpace

section Slice

variable {K : Type} [Field K] (X : Scheme.{0}) {T : Scheme.{0}} [X.Over (Spec (.of K))]
  [T.Over (Spec (.of K))]

/-- The *slice* `i_t : X → X ×_K T`, `x ↦ (x, t)`, at a `K`-point `t` of `T`. -/
def slice (t : UnderlyingSpace K T) : X ⟶ pullback (X ↘ Spec (.of K)) (T ↘ Spec (.of K)) :=
  pullback.lift (𝟙 X) (X ↘ Spec (.of K) ≫ t.toHom) (by simp)

/-- The slice `i_t` followed by the first projection `X × T → X` is the identity of `X`. -/
@[reassoc (attr := simp)]
lemma slice_fst (t : UnderlyingSpace K T) :
    slice X t ≫ pullback.fst (X ↘ Spec (.of K)) (T ↘ Spec (.of K)) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The slice `i_t` followed by the second projection `X × T → T` is the constant morphism
`X → Spec K → T` at `t`. -/
@[reassoc (attr := simp)]
lemma slice_snd (t : UnderlyingSpace K T) :
    slice X t ≫ pullback.snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K)) =
      X ↘ Spec (.of K) ≫ t.toHom :=
  pullback.lift_snd _ _ _

/-- The slice is a morphism over `K`. -/
instance isOver_slice (t : UnderlyingSpace K T) : (slice X t).IsOver (Spec (.of K)) :=
  ⟨by
    change slice X t ≫ pullback.snd _ _ ≫ T ↘ Spec (.of K) = X ↘ Spec (.of K)
    rw [slice_snd_assoc, t.toHom_comp_over, Category.comp_id]⟩

/-- **The slice is a base change of the point.** The square with sides `i_t : X → X × T`,
`X → Spec K`, `pr₂ : X × T → T` and `t : Spec K → T` is cartesian. -/
theorem isPullback_slice (t : UnderlyingSpace K T) :
    IsPullback (slice X t) (X ↘ Spec (.of K)) (pullback.snd (X ↘ Spec (.of K)) (T ↘ Spec (.of K)))
      t.toHom := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (X ↘ Spec (.of K)) (T ↘ Spec (.of K)))
    (h₂₂ := T ↘ Spec (.of K)) (v₁₃ := X ↘ Spec (.of K)) ?_ (slice_snd X t)
    (IsPullback.of_hasPullback _ _)
  rw [slice_fst, t.toHom_comp_over]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **The slice of a curve is a regular closed immersion of codimension one** (Fulton, proof of
Lemma 19.2(c)): for `T` a non-singular curve over `K`, `i_t : X → X × T` is a regular closed
immersion of codimension one. -/
theorem isRegularClosedImmersionOfCodim_slice [IsSmoothVariety K (T ↘ Spec (.of K))]
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of K))) (t : UnderlyingSpace K T) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim (slice X t) 1 :=
  (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t).of_isPullback
    (isPullback_slice X t).flip

/-- The slice of a curve is a closed immersion. -/
instance isClosedImmersion_slice [IsSmoothVariety K (T ↘ Spec (.of K))]
    (t : UnderlyingSpace K T) : IsClosedImmersion (slice X t) :=
  MorphismProperty.of_isPullback (isPullback_slice X t).flip inferInstance

end Slice

section ComplexSlice

variable (X : Scheme.{0}) {T : Scheme.{0}} [X.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]

/-- On complex points, the slice `i_t` has image `pr₂⁻¹(t)`. -/
theorem range_map_slice (t : UnderlyingSpace ℂ T) :
    range (UnderlyingSpace.map (K := ℂ) (slice X t)) =
      mapFun (pullback.snd (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))) ⁻¹' {t} := by
  rw [range_map_eq_preimage_of_isPullback (isPullback_slice X t), range_map_toHom]

/-- Under `(X × T)(ℂ) ≃ₜ X(ℂ) × T(ℂ)`, the image of the slice `i_t` is `X(ℂ) × {t}`. -/
theorem range_map_slice_eq_preimage (t : UnderlyingSpace ℂ T) :
    range (UnderlyingSpace.map (K := ℂ) (slice X t)) =
      homeomorphProd X T ⁻¹'
        (borelMooreHomology.prodSnd (TopCat.of (UnderlyingSpace ℂ X))
          (TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t}) := by
  rw [range_map_slice]
  rfl

/-- The slice `i_t` identifies `X(ℂ)` with its image. -/
def sliceHomeomorph (t : UnderlyingSpace ℂ T) :
    UnderlyingSpace ℂ X ≃ₜ range (UnderlyingSpace.map (K := ℂ) (slice X t)) where
  toFun x := ⟨UnderlyingSpace.map (K := ℂ) (slice X t) x, mem_range_self x⟩
  invFun p := mapFun (pullback.fst (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))) p.1
  left_inv x := UnderlyingSpace.ext (by
    change (mapFun _ (mapFun (slice X t) x)).toHom = _
    rw [toHom_mapFun, toHom_mapFun, Category.assoc, slice_fst, Category.comp_id])
  right_inv p := by
    obtain ⟨_, x, rfl⟩ := p
    refine Subtype.ext ?_
    change mapFun (slice X t) (mapFun _ (mapFun (slice X t) x)) = mapFun (slice X t) x
    congr 1
    refine UnderlyingSpace.ext ?_
    rw [toHom_mapFun, toHom_mapFun, Category.assoc, slice_fst, Category.comp_id]
  continuous_toFun := (UnderlyingSpace.map (K := ℂ) (slice X t)).continuous.subtype_mk _
  continuous_invFun := (continuous_mapFun _).comp continuous_subtype_val

/-- The inverse of `sliceHomeomorph` is the first projection `(X × T)(ℂ) → X(ℂ)`. -/
@[simp]
lemma sliceHomeomorph_symm_apply (t : UnderlyingSpace ℂ T)
    (p : range (UnderlyingSpace.map (K := ℂ) (slice X t))) :
    (sliceHomeomorph X t).symm p =
      mapFun (pullback.fst (X ↘ Spec (.of ℂ)) (T ↘ Spec (.of ℂ))) p.1 :=
  rfl

end ComplexSlice

end UnderlyingSpace

end MMP
