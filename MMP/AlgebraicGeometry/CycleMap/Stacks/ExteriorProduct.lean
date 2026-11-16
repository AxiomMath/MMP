module
import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic

public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Variety
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Transport
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.ComplexScheme
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.DiagonalSubvarietyProduct

/-!
# The cycle class commutes with exterior products (Fulton, Example 19.1.9)

For complex schemes `X`, `Y` and Stacks' cycles `α ∈ Z_k(X)`, `β ∈ Z_l(Y)` over
`fieldChowSituation ℂ`, the cycle class of the exterior product `α × β` on `X ×_ℂ Y`
(`Stacks.Chow.exteriorProduct`) is the exterior product `cl_X(α) × cl_Y(β)` of Borel–Moore
classes, read on `(X ×_ℂ Y)(ℂ)` through `(X ×_ℂ Y)(ℂ) ≃ₜ X(ℂ) × Y(ℂ)` (`MMP.productClass`).

By bilinearity it suffices to take prime cycles `α = [x]`, `β = [y]`. With `V = closure {x}` and
`W = closure {y}`, the closed subscheme `V ×_ℂ W` of `X ×_ℂ Y` cut out by
`Stacks.Chow.exteriorProductIdeal` is isomorphic to the fibre product of `V` and `W`, a variety
of dimension `k + l` since `ℂ` is algebraically closed (Stacks 05P3, 0AZM). So `[x] × [y]` is the
prime cycle `[z]` of its generic point `z`, and `cl([z])` is the push-forward of the fundamental
class of `V ×_ℂ W`, which is `cl(V) × cl(W)` (`MMP.IsVarietyFundamentalClass.productClass`);
pushing forward to `X ×_ℂ Y` gives `cl_X(x) × cl_Y(y)` (`MMP.pushforward_productClass`).

Stacks' exterior product lands in cycles over the structure morphism `pr₁ ≫ (X ↘ Spec ℂ)` of
`X ×_ℂ Y`, the cycle class map over `X ×_ℂ Y ↘ Spec ℂ = pr₂ ≫ (Y ↘ Spec ℂ)`; the two are equal
(`pullback.condition`), and the statements transport along `Stacks.Chow.cycleGroupStructureCongr`
and `Stacks.Chow.chowGroupCongr`.

## Main results

* `MMP.Chow.exteriorProduct_pointCycle`: `[x] × [y] = [z]` for `z` the generic point of
  `closure {x} ×_ℂ closure {y}`.
* `MMP.Chow.pointCycleClass_productGenericPoint`: `cl([z]) = cl_X(x) × cl_Y(y)`.
* `MMP.Chow.cycleClass_exteriorProduct`: `cl_{X × Y}(α × β) = cl_X(α) × cl_Y(β)` on cycles.
* `MMP.Chow.chowCycleClass_chowExteriorProduct`: the same on Chow groups.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.9.
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 05P3](https://stacks.math.columbia.edu/tag/05P3)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
  MMP MMP.UnderlyingSpace Stacks.Chow

namespace MMP.Chow

/-! ### Point closures as varieties over `ℂ` -/

/-- A complex scheme is separated over `ℂ`: it is a closed subscheme of a smooth variety. -/
theorem isSeparated_of_isComplexScheme (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] : IsSeparated (X ↘ Spec (.of ℂ)) := by
  obtain ⟨M, _, hM, i, hi, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
  rw [← hi.comp_over]
  infer_instance

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Y.Over (Spec (.of ℂ))]
  [IsComplexScheme Y]

/-- The closure of a point of a complex scheme is a variety over `ℂ`. -/
instance isVariety_subschemeι_comp_integralComponentAt (x : X) :
    AlgebraicGeometry.IsVariety ℂ ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ)) := by
  have := isSeparated_of_isComplexScheme X
  have := isIntegral_integralComponentAt x
  exact ⟨⟩

/-! ### The product of two point closures -/

/-- **The product of two point closures is integral** (Stacks 05P3): over the algebraically
closed field `ℂ`, the fibre product of two varieties is a variety. -/
instance isIntegral_pullback_integralComponentAt (x : X) (y : Y) :
    IsIntegral (pullback ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
      ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ))) :=
  (AlgebraicGeometry.isVariety_pullback ℂ
    ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
    ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ))).toIsIntegral

/-- The closed subscheme `closure {x} ×_ℂ closure {y}` of `X ×_ℂ Y` is integral. -/
instance isIntegral_exteriorProductIdeal (x : X) (y : Y) :
    IsIntegral ((integralComponentAt x).comap
      (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
        (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme :=
  have h := IsIntegral.of_isIso (Scheme.IdealSheafData.productSubschemeIso (X ↘ Spec (.of ℂ))
    (Y ↘ Spec (.of ℂ)) (integralComponentAt x) (integralComponentAt y)).inv
  h

/-- The generic point of `closure {x} ×_ℂ closure {y}`, as a point of `X ×_ℂ Y`. -/
def productGenericPoint (x : X) (y : Y) : ↥(pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) :=
  genericPointOf ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))))
    (isIntegral_exteriorProductIdeal x y)

/-- `closure {x} ×_ℂ closure {y}` is the closure of its generic point. -/
theorem integralComponentAt_productGenericPoint (x : X) (y : Y) :
    integralComponentAt (productGenericPoint x y) =
      ((integralComponentAt x).comap (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))) :=
  integralComponentAt_genericPointOf _ (isIntegral_exteriorProductIdeal x y)

/-- The generic point of `closure {x} ×_ℂ closure {y}` projects to `x`. -/
theorem fst_productGenericPoint (x : X) (y : Y) :
    (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))).base (productGenericPoint x y) = x := by
  have h := congrArg (fun q : ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme
          ⟶ X => q.base (genericPoint
        ((integralComponentAt x).comap (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme))
    (Scheme.IdealSheafData.productSubschemeIso_hom_fst_subschemeι (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) (integralComponentAt x) (integralComponentAt y))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [Stacks.Intersection.ReductionToDiagonal.genericPoint_map_of_flat
      (Scheme.IdealSheafData.productSubschemeIso (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
        (integralComponentAt x) (integralComponentAt y)).hom,
    Stacks.Intersection.ReductionToDiagonal.genericPoint_map_of_flat
      (pullback.fst ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
        ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ)))] at h
  exact h.symm.trans (genericPointOf_integralComponentAt x)

/-- The generic point of `closure {x} ×_ℂ closure {y}` projects to `y`. -/
theorem snd_productGenericPoint (x : X) (y : Y) :
    (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))).base (productGenericPoint x y) = y := by
  have h := congrArg (fun q : ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme
          ⟶ Y => q.base (genericPoint
        ((integralComponentAt x).comap (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme))
    (Scheme.IdealSheafData.productSubschemeIso_hom_snd_subschemeι (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) (integralComponentAt x) (integralComponentAt y))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [Stacks.Intersection.ReductionToDiagonal.genericPoint_map_of_flat
      (Scheme.IdealSheafData.productSubschemeIso (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
        (integralComponentAt x) (integralComponentAt y)).hom,
    Stacks.Intersection.ReductionToDiagonal.genericPoint_map_of_flat
      (pullback.snd ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
        ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ)))] at h
  exact h.symm.trans (genericPointOf_integralComponentAt y)

/-- **The dimension of a product of point closures** (Stacks 0AZM):
`dim (closure {x} ×_ℂ closure {y}) = dim closure {x} + dim closure {y}`. -/
theorem topologicalKrullDim_exteriorProductIdeal (x : X) (y : Y) :
    topologicalKrullDim ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme =
      topologicalKrullDim (integralComponentAt x).subscheme +
        topologicalKrullDim (integralComponentAt y).subscheme := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.Hom.homeomorph (Scheme.IdealSheafData.productSubschemeIso (X ↘ Spec (.of ℂ))
        (Y ↘ Spec (.of ℂ)) (integralComponentAt x) (integralComponentAt y)).hom).isHomeomorph,
    topologicalKrullDim_pullback_of_isVariety ℂ
      ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
      ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ))]

/-- The delta-dimension of the generic point of `closure {x} ×_ℂ closure {y}` is the sum of the
delta-dimensions of `x` and `y`. -/
theorem relativeDimension_productGenericPoint (x : X) (y : Y) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
        (productGenericPoint x y) =
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x +
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y := by
  have hva : topologicalKrullDim ((integralComponentAt x).support : Set X) =
      (relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x).toNat := by
    rw [show ((integralComponentAt x).support : Set X) = closure ({x} : Set X) from
      coe_support_integralComponentAt x,
      topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ)) x]
  have hvb : topologicalKrullDim ((integralComponentAt y).support : Set Y) =
      (relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y).toNat := by
    rw [show ((integralComponentAt y).support : Set Y) = closure ({y} : Set Y) from
      coe_support_integralComponentAt y,
      topologicalKrullDim_closure_singleton_eq ℂ (Y ↘ Spec (.of ℂ)) y]
  have hvv : topologicalKrullDim (((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap
          (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).support :
        Set ↥(pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))) =
      (relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
        (productGenericPoint x y)).toNat := by
    rw [show (((integralComponentAt x).comap (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).support :
          Set ↥(pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))) =
          closure ({productGenericPoint x y} :
            Set ↥(pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))) from
        support_eq_closure_genericPointOf _ (isIntegral_exteriorProductIdeal x y),
      topologicalKrullDim_closure_singleton_eq ℂ
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
        (productGenericPoint x y)]
  have hkey := topologicalKrullDim_exteriorProductIdeal x y
  rw [Stacks.Chow.topologicalKrullDim_subscheme, Stacks.Chow.topologicalKrullDim_subscheme,
    Stacks.Chow.topologicalKrullDim_subscheme, hva, hvb, hvv] at hkey
  have hnat : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
        (productGenericPoint x y)).toNat =
      (relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x).toNat +
        (relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ))
          y).toNat := by
    exact_mod_cast hkey
  have ha := relativeDimension_fieldChowSituation_nonneg ℂ (X ↘ Spec (.of ℂ)) x
  have hb := relativeDimension_fieldChowSituation_nonneg ℂ (Y ↘ Spec (.of ℂ)) y
  have hv := relativeDimension_fieldChowSituation_nonneg ℂ
    (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
    (productGenericPoint x y)
  omega

/-! ### The exterior product of two prime cycles -/

open Stacks.Intersection in
/-- **`[x] × [y]` is the prime cycle of the generic point of `closure {x} ×_ℂ closure {y}`**:
over the algebraically closed field `ℂ` this product is integral of delta-dimension
`δ(x) + δ(y)`, so its cycle is its generic point with multiplicity one (Stacks 02QU). -/
theorem exteriorProduct_pointCycle {k l : ℕ} (x : X) (y : Y)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y = l) :
    exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l
        (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
        (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy) =
      pointCycle (fieldChowSituation ℂ)
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ)) (k + l)
        (productGenericPoint x y) (by rw [relativeDimension_productGenericPoint, hx, hy]) := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  change (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l
      (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
      (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy)).1 z =
    (pointCycle (fieldChowSituation ℂ)
      (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ)) (k + l)
      (productGenericPoint x y) _).1 z
  rw [exteriorProduct_apply, pointCycle_apply, pointCycle_apply, pointCycle_apply,
    ExteriorProductProjections.exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme]
  by_cases hz : z = productGenericPoint x y
  · rw [hz, fst_productGenericPoint, snd_productGenericPoint, ite_eq_left rfl, ite_eq_left rfl,
        ite_eq_left rfl,
      one_mul, one_mul]
    refine cycleAssociatedToClosedSubscheme_integral_apply (fieldChowSituation ℂ)
      (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ))
      ((integralComponentAt x).comap (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
      (integralComponentAt y).comap (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))))
      (isIntegral_exteriorProductIdeal x y) ?_
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion]
    exact congrArg (fun m : ℤ => (m : EInt))
      ((relativeDimension_productGenericPoint x y).trans (by rw [hx, hy]))
  · rw [ite_eq_right hz]
    by_cases h1 : (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))).base z = x
    · by_cases h2 : (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))).base z = y
      · rw [h1, h2, ite_eq_left rfl, ite_eq_left rfl, one_mul, one_mul]
        exact cycleAssociatedToClosedSubscheme_integral_apply_of_ne (fieldChowSituation ℂ) _ _
          (isIntegral_exteriorProductIdeal x y) _ hz
      · rw [ite_eq_right h2, mul_zero, zero_mul]
    · rw [ite_eq_right h1, zero_mul, zero_mul]

/-! ### The cycle class of the product of two point closures -/

variable (R : Type) [CommRing R]

/-- **`cl([z]) = cl_X(x) × cl_Y(y)`** for `z` the generic point of `closure {x} ×_ℂ closure {y}`
(Fulton, Example 19.1.9): the fundamental class of `closure {x} ×_ℂ closure {y}` is
`cl(closure {x}) × cl(closure {y})` (`MMP.IsVarietyFundamentalClass.productClass`), and the
exterior product commutes with push-forward (`MMP.pushforward_productClass`). -/
theorem pointCycleClass_productGenericPoint {k l : ℕ} (x : X) (y : Y)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y = l)
    (hz : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) (productGenericPoint x y) =
        ((k + l : ℕ) : ℤ)) :
    pointCycleClass R (productGenericPoint x y) hz =
      productClass R X Y (pointCycleClass R x hx) (pointCycleClass R y hy) := by
  have hzI := integralComponentAt_productGenericPoint x y
  -- the identification `closure {z} = closure {x} ×_ℂ closure {y}` of closed subschemes
  have : IsIso (Scheme.IdealSheafData.inclusion hzI.le) :=
    ⟨⟨Scheme.IdealSheafData.inclusion hzI.ge,
      by rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id],
      by rw [Scheme.IdealSheafData.inclusion_comp, Scheme.IdealSheafData.inclusion_id]⟩⟩
  -- `e : V ×_ℂ W ≅ closure {x} ×_ℂ closure {y}`, `φ : V ×_ℂ W ≅ closure {z}` and
  -- `F : V ×_ℂ W → X ×_ℂ Y`
  obtain ⟨e, he⟩ : ∃ e : pullback ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
      ((integralComponentAt y).subscheme ↘ Spec (.of ℂ)) ≅ ((integralComponentAt x).comap
          (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
        (integralComponentAt y).comap
            (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subscheme,
      e = (Scheme.IdealSheafData.productSubschemeIso (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
        (integralComponentAt x) (integralComponentAt y)).symm := ⟨_, rfl⟩
  have hef : e.hom ≫ ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
        (integralComponentAt y).comap
            (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subschemeι ≫
      pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) =
        pullback.fst _ _ ≫ (integralComponentAt x).subschemeι := by
    subst he
    exact (Iso.inv_comp_eq _).2
      (Scheme.IdealSheafData.productSubschemeIso_hom_fst_subschemeι _ _ _ _).symm
  have hes : e.hom ≫ ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
        (integralComponentAt y).comap
            (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subschemeι ≫
      pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) =
        pullback.snd _ _ ≫ (integralComponentAt y).subschemeι := by
    subst he
    exact (Iso.inv_comp_eq _).2
      (Scheme.IdealSheafData.productSubschemeIso_hom_snd_subschemeι _ _ _ _).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : pullback ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
      ((integralComponentAt y).subscheme ↘ Spec (.of ℂ)) ⟶
      (integralComponentAt (productGenericPoint x y)).subscheme,
      φ = e.hom ≫ Scheme.IdealSheafData.inclusion hzI.le := ⟨_, rfl⟩
  have : IsIso φ := by rw [hφ]; infer_instance
  obtain ⟨F, hF⟩ : ∃ F : pullback ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
      ((integralComponentAt y).subscheme ↘ Spec (.of ℂ)) ⟶
        pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)),
      F = φ ≫ (integralComponentAt (productGenericPoint x y)).subschemeι := ⟨_, rfl⟩
  have hFI : F = e.hom ≫ ((integralComponentAt x).comap
        (pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) ⊔
        (integralComponentAt y).comap
            (pullback.snd (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)))).subschemeι := by
    rw [hF, hφ, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have hFf : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (integralComponentAt x).subschemeι := by
    rw [hFI, Category.assoc]
    exact hef
  have hFs : F ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (integralComponentAt y).subschemeι := by
    rw [hFI, Category.assoc]
    exact hes
  have : F.IsOver (Spec (.of ℂ)) := ⟨by
    change F ≫ pullback.snd _ _ ≫ _ = pullback.snd _ _ ≫ _
    rw [← Category.assoc, hFs, Category.assoc]
    rfl⟩
  have : IsClosedImmersion F := by rw [hFI]; infer_instance
  have : IsProper F := AlgebraicGeometry.isProper_of_isClosedImmersion F
  have : φ.IsOver (Spec (.of ℂ)) := ⟨by
    change φ ≫ (integralComponentAt (productGenericPoint x y)).subschemeι ≫ _ = _
    rw [← Category.assoc, ← hF]
    exact comp_over F (Spec (.of ℂ))⟩
  -- the fundamental classes
  have hdimP : ((k + l : ℕ) : WithBot ℕ∞) =
      topologicalKrullDim ↥(pullback ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
        ((integralComponentAt y).subscheme ↘ Spec (.of ℂ))) :=
          by
    have h := topologicalKrullDim_pullback_of_isVariety ℂ
      ((integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ))
      ((integralComponentAt y).subschemeι ≫ Y ↘ Spec (.of ℂ))
    rw [Nat.cast_add, natCast_eq_dimension_integralComponentAt x hx,
      natCast_eq_dimension_integralComponentAt y hy]
    exact h.symm
  have hcV := (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1
  have hcW := (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt y hy)).choose_spec.1
  have hcZ := (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt (productGenericPoint x y) hz)).choose_spec.1
  have : IsIntegral (pullback ((integralComponentAt x).subscheme ↘ Spec (.of ℂ))
      ((integralComponentAt y).subscheme ↘ Spec (.of ℂ))) :=
    isIntegral_pullback_integralComponentAt x y
  have hS := IsVarietyFundamentalClass.productClass hdimP hcV hcW
  have hφS := hS.pushforward_of_isIso φ
    (natCast_eq_dimension_integralComponentAt (productGenericPoint x y) hz)
  unfold pointCycleClass
  rw [hcZ.eq hφS, ← pushforward_productClass (integralComponentAt x).subschemeι
    (integralComponentAt y).subschemeι F hFf hFs]
  rw [borelMooreHomology.pushforward_comp_apply R _ _ (isProperMap_map (K := ℂ) φ)
    (isProperMap_map (K := ℂ) (integralComponentAt (productGenericPoint x y)).subschemeι)
    ((isProperMap_map (K := ℂ) (integralComponentAt (productGenericPoint x y)).subschemeι).comp
      (isProperMap_map (K := ℂ) φ))]
  refine borelMooreHomology.pushforward_apply_congr R
    (ConcreteCategory.hom_ext _ _ fun p ↦ ?_) _ _ _ _
  refine UnderlyingSpace.ext ?_
  change (p.toHom ≫ φ) ≫ (integralComponentAt (productGenericPoint x y)).subschemeι = p.toHom ≫ F
  rw [Category.assoc, hF]

/-! ### The cycle class of an exterior product -/

omit [IsComplexScheme X] [IsComplexScheme Y] in
variable (X Y) in
/-- The two structure morphisms of `X ×_ℂ Y` to `Spec ℂ`: Stacks' exterior product is read over
`pr₁ ≫ (X ↘ Spec ℂ)`, the cycle class map over `X ×_ℂ Y ↘ Spec ℂ = pr₂ ≫ (Y ↘ Spec ℂ)`. -/
theorem pullback_fst_comp_over :
    pullback.fst (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ) =
      pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ) :=
  pullback.condition

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- `a × b` is additive in `a`. -/
private theorem productClass_add_left {k l : ℕ} (a a' : BMHomology R X (2 * k))
    (b : BMHomology R Y (2 * l)) :
    productClass R X Y (a + a') b = productClass R X Y a b + productClass R X Y a' b := by
  simp only [productClass, TensorProduct.add_tmul, map_add]

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- `a × b` is additive in `b`. -/
private theorem productClass_add_right {k l : ℕ} (a : BMHomology R X (2 * k))
    (b b' : BMHomology R Y (2 * l)) :
    productClass R X Y a (b + b') = productClass R X Y a b + productClass R X Y a b' := by
  simp only [productClass, TensorProduct.tmul_add, map_add]

variable (X Y) in
/-- `a × b`, as a biadditive map. -/
private def productClassAddHom (k l : ℕ) :
    BMHomology R X (2 * k) →+ BMHomology R Y (2 * l) →+
      BMHomology R (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) (2 * (k + l)) :=
  AddMonoidHom.mk' (fun a ↦ AddMonoidHom.mk' (fun b ↦ productClass R X Y a b)
    (productClass_add_right R a)) fun a a' ↦ by
      ext b
      exact productClass_add_left R a a' b

variable {R} in
/-- Two biadditive maps on `Z_k(X) × Z_l(Y)` agreeing on pairs of prime cycles are equal. -/
theorem addMonoidHom_ext_pointCycle {G : Type*} [AddCommGroup G] {k l : ℕ}
    {L M : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+
      CycleGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l →+ G}
    (h : ∀ (x : X) (y : Y)
      (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
      (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y = l),
      L (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
          (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy) =
        M (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
          (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy)) :
    L = M := by
  have h0 : ∀ (x : X) (y : Y),
      L (pointCycleOrZero k x) (pointCycleOrZero l y) =
        M (pointCycleOrZero k x) (pointCycleOrZero l y) := by
    intro x y
    unfold pointCycleOrZero
    split_ifs with hx hy hy
    · exact h x y hx hy
    all_goals simp
  ext α β
  rw [eq_sum_pointCycleOrZero α, eq_sum_pointCycleOrZero β]
  simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, h0]

/-- **The cycle class commutes with exterior products** (Fulton, Example 19.1.9). For complex
schemes `X`, `Y` and Stacks' cycles `α ∈ Z_k(X)`, `β ∈ Z_l(Y)`,
`cl_{X × Y}(α × β) = cl_X(α) × cl_Y(β)`: the exterior product of cycles
(`Stacks.Chow.exteriorProduct`, Stacks 0FBV), read over the structure morphism of `X ×_ℂ Y`, is
carried by the cycle maps to the exterior product of Borel–Moore classes, read on `(X ×_ℂ Y)(ℂ)`
through `(X ×_ℂ Y)(ℂ) ≃ₜ X(ℂ) × Y(ℂ)` (`MMP.productClass`). -/
theorem cycleClass_exteriorProduct {k l : ℕ}
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (β : CycleGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l) :
    cycleClass R (k + l) (cycleGroupStructureCongr (fieldChowSituation ℂ)
        (pullback_fst_comp_over X Y) ((k + l : ℕ) : ℤ)
        (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l α β)) =
      productClass R X Y (cycleClass R k α) (cycleClass R l β) := by
  let L : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+
      CycleGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l →+
        BMHomology R (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) (2 * (k + l)) :=
    (AddMonoidHom.compHom ((cycleClass R (k + l)).comp
      (cycleGroupStructureCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X Y)
        ((k + l : ℕ) : ℤ)).toAddMonoidHom)).comp
      (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l)
  let M : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+
      CycleGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l →+
        BMHomology R (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))) (2 * (k + l)) :=
    (AddMonoidHom.compHom' (cycleClass R l)).comp
      ((productClassAddHom X Y R k l).comp (cycleClass R k))
  have hLM : L = M := addMonoidHom_ext_pointCycle fun x y hx hy ↦ by
    change cycleClass R (k + l) (cycleGroupStructureCongr (fieldChowSituation ℂ)
        (pullback_fst_comp_over X Y) ((k + l : ℕ) : ℤ)
        (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l
          (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
          (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy))) =
      productClass R X Y (cycleClass R k (pointCycle (fieldChowSituation ℂ)
          (X ↘ Spec (.of ℂ)) k x hx))
        (cycleClass R l (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy))
    have hz : relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) (productGenericPoint x y) =
          ((k + l : ℕ) : ℤ) := by
      rw [← (pullback_fst_comp_over X Y), relativeDimension_productGenericPoint, hx, hy,
          Nat.cast_add]
    have hT : cycleGroupStructureCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X Y)
        ((k + l : ℕ) : ℤ)
        (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) k l
          (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)
          (pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l y hy)) =
        pointCycle (fieldChowSituation ℂ)
          (pullback (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
          ((k + l : ℕ) : ℤ)
          (productGenericPoint x y) hz := by
      refine Subtype.ext ?_
      rw [cycleGroupStructureCongr_apply_coe, exteriorProduct_pointCycle]
      rfl
    rw [hT, cycleClass_pointCycle, cycleClass_pointCycle, cycleClass_pointCycle,
      pointCycleClass_productGenericPoint]
  exact DFunLike.congr_fun (DFunLike.congr_fun hLM α) β

/-- Transport along an equality of structure morphisms, on the class of a cycle. -/
theorem chowGroupCongr_mk {Z : Scheme.{0}} {q q' : Z ⟶ (fieldChowSituation ℂ).S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (n : ℤ)
    (α : CycleGroup (fieldChowSituation ℂ) q n) :
    chowGroupCongr (fieldChowSituation ℂ) hq n (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk (cycleGroupStructureCongr (fieldChowSituation ℂ) hq n α) := by
  subst hq
  rfl

/-- **The cycle class commutes with exterior products on Chow groups** (Fulton,
Example 19.1.9): for `a ∈ A_k(X)` and `b ∈ A_l(Y)`, the cycle class of the exterior product
`a × b ∈ A_{k+l}(X ×_ℂ Y)` (`Stacks.Chow.chowExteriorProduct`, Stacks 0FBV), read over the
structure morphism of `X ×_ℂ Y`, is `cl_X(a) × cl_Y(b)`. -/
theorem chowCycleClass_chowExteriorProduct {k l : ℕ}
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (b : chowGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) l) :
    chowCycleClass R (k + l) (chowGroupCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X Y)
        ((k + l : ℕ) : ℤ)
        (chowExteriorProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (X ↘ Spec (.of ℂ))
          (Y ↘ Spec (.of ℂ)) k l (a ⊗ₜ b))) =
      productClass R X Y (chowCycleClass R k a) (chowCycleClass R l b) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [chowCycleClass_mk, chowCycleClass_mk]
  exact (congrArg (chowCycleClass R (k + l)) (chowGroupCongr_mk (pullback_fst_comp_over X Y)
    ((k + l : ℕ) : ℤ) (exteriorProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) k l α β))).trans (cycleClass_exteriorProduct R α β)

end MMP.Chow
