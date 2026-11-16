module

public import MMP.AlgebraicGeometry.Chow.CycleClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PushforwardDegree
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage

/-!
# The cycle class commutes with proper push-forward (Fulton, §19.1)

For a proper morphism `f : X → Y` of complex schemes and a cycle `α` of delta-dimension `k` on
`X` (Stacks' cycles over `fieldChowSituation ℂ`), `cl_Y(f_* α) = f_* cl_X(α)` in `H_{2k}(Y)`.

On a point `x` of delta-dimension `k`, with `V = closure {x}` and `W = closure {f x}`, the
morphism `f` restricts to a proper surjection `g : V → W` (`f(V) = W`, as `f` is closed). If
`f x` has delta-dimension `k`, Lemma 19.1.2 gives `g_* cl(V) = deg(V/W) cl(W)` with
`deg(V/W) = f.residueDegree x`, and Stacks' push-forward is `f_*[x] = deg(V/W) [f x]`
(Stacks 02R4). Otherwise `dim W < k`, so both `g_* cl(V)` and `f_*[x]` vanish.

## Main results

* `MMP.Chow.pushforward_pointCycleClass`: `f_* cl_X(x) = deg(x/f x) cl_Y(f x)` (or `0`).
* `MMP.Chow.properPushforward_pointCycle_eq`: `f_*[x] = deg(x/f x) [f x]` (or `0`).
* `MMP.Chow.cycleClass_properPushforward`: `cl_Y(f_* α) = f_* cl_X(α)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MMP MMP.UnderlyingSpace Stacks.Chow

namespace MMP.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (R : Type) [CommRing R] {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f]

/-- `f` maps the closure of `x` onto the closure of `f x`. -/
theorem map_integralComponentAt (x : X) :
    (integralComponentAt x).map f = integralComponentAt (f.base x) := by
  unfold integralComponentAt
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext y
  change y ∈ closure (f.base '' closure {x}) ↔ y ∈ closure {f.base x}
  rw [f.isClosedMap.closure_image_eq_of_continuous f.base.hom.continuous, closure_closure,
    ← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous f.base.hom.continuous]

/-- The restriction `closure {x} → closure {f x}` of `f`. -/
def integralComponentMap (x : X) :
    (integralComponentAt x).subscheme ⟶ (integralComponentAt (f.base x)).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ f (map_integralComponentAt f x).ge

/-- The restriction of `f` to `closure {x}` followed by the inclusion of `closure {f x}` is the
inclusion of `closure {x}` followed by `f`. -/
@[reassoc (attr := simp)]
theorem integralComponentMap_subschemeι (x : X) :
    integralComponentMap f x ≫ (integralComponentAt (f.base x)).subschemeι =
      (integralComponentAt x).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The restriction `closure {x} → closure {f x}` of `f` is a morphism over `ℂ`. -/
instance (x : X) : (integralComponentMap f x).IsOver (Spec (.of ℂ)) where
  comp_over := by
    change integralComponentMap f x ≫ (integralComponentAt (f.base x)).subschemeι ≫
      Y ↘ Spec (.of ℂ) = (integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ)
    rw [integralComponentMap_subschemeι_assoc, comp_over]

/-- The restriction `closure {x} → closure {f x}` of `f` is proper. -/
instance (x : X) : IsProper (integralComponentMap f x) := by
  have : IsProper (integralComponentMap f x ≫ (integralComponentAt (f.base x)).subschemeι) := by
    rw [integralComponentMap_subschemeι]; infer_instance
  exact IsProper.of_comp _ (integralComponentAt (f.base x)).subschemeι

/-- `closure {x} → closure {f x}` is surjective. -/
theorem surjective_integralComponentMap (x : X) :
    Function.Surjective (integralComponentMap f x) := by
  intro w
  have hw : (integralComponentAt (f.base x)).subschemeι.base w ∈ closure ({f.base x} : Set Y) := by
    rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous
    f.base.hom.continuous] at hw
  obtain ⟨y, hy, hyw⟩ := hw
  rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι] at hy
  obtain ⟨v, rfl⟩ := hy
  refine ⟨v, (integralComponentAt (f.base x)).subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, integralComponentMap_subschemeι, Scheme.Hom.comp_apply, hyw]

/-- The generic point of `closure {x}` lies over `x`. -/
theorem subschemeι_genericPoint (x : X) :
    (integralComponentAt x).subschemeι.base (genericPoint (integralComponentAt x).subscheme) = x := by
  have h := Stacks.Intersection.ExteriorProductProjections.closure_singleton_subschemeι_genericPoint
    (integralComponentAt x)
  rw [coe_support_integralComponentAt] at h
  exact ((specializes_iff_mem_closure.mpr (h ▸ subset_closure rfl)).antisymm
    (specializes_iff_mem_closure.mpr (h.symm ▸ subset_closure rfl))).eq.symm

/-- `deg(V/W)` for `V = closure {x}`, `W = closure {f x}` is the residue degree of `f` at `x`. -/
theorem residueDegree_integralComponentMap (x : X) :
    (integralComponentMap f x).residueDegree (genericPoint (integralComponentAt x).subscheme) =
      f.residueDegree x := by
  have h := AlgebraicGeometry.residueDegree_comp (integralComponentMap f x) (integralComponentAt (f.base x)).subschemeι
    (genericPoint (integralComponentAt x).subscheme)
  rw [integralComponentMap_subschemeι, AlgebraicGeometry.residueDegree_comp, subschemeι_genericPoint,
    residueDegree_eq_one_of_isClosedImmersion (integralComponentAt x).subschemeι,
    residueDegree_eq_one_of_isClosedImmersion (integralComponentAt (f.base x)).subschemeι,
    mul_one, one_mul] at h
  exact h.symm

/-- The delta-dimension does not grow along `f`: `δ(f x) ≤ δ(x)`, as
`δ(x) = δ(f x) + trdeg(κ(x)/κ(f x))`. -/
theorem relativeDimension_map_le (x : X) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) (f.base x) ≤
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x := by
  have h := relativeDimension_comp_eq_add_trdeg (fieldChowSituation ℂ).dimensionFunction
    (Y ↘ Spec (.of ℂ)) f x
  rw [comp_over] at h
  have h' : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x =
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) (f.base x) +
        (Cardinal.toNat (residueTrdeg f x) : ℤ) := h
  omega

/-- The dimension of `closure {y}` is the delta-dimension of `y`. -/
theorem dimension_integralComponentAt (y : Y) :
    topologicalKrullDim (integralComponentAt y).subscheme =
      ((relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) y).toNat :
        WithBot ℕ∞) := by
  have hemb := (integralComponentAt y).subschemeι.isClosedEmbedding.isEmbedding
  have h1 : topologicalKrullDim (integralComponentAt y).subscheme =
      topologicalKrullDim (closure ({y} : Set Y)) := by
    rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    exact hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [h1, topologicalKrullDim_closure_singleton_eq ℂ (Y ↘ Spec (.of ℂ)) y]

/-- `f_V ∘ ι_V = ι_W ∘ g` on complex points, for `g : V = closure {x} → W = closure {f x}`. -/
lemma topCatMap_subschemeι_comp (x : X) :
    TopCat.ofHom (map (K := ℂ) (integralComponentAt x).subschemeι) ≫ TopCat.ofHom (map (K := ℂ) f) =
      TopCat.ofHom (map (K := ℂ) (integralComponentMap f x)) ≫
        TopCat.ofHom (map (K := ℂ) (integralComponentAt (f.base x)).subschemeι) := by
  ext p : 1
  change map (K := ℂ) f (map (K := ℂ) (integralComponentAt x).subschemeι p) =
    map (K := ℂ) (integralComponentAt (f.base x)).subschemeι (map (K := ℂ) (integralComponentMap f x) p)
  refine UnderlyingSpace.ext ?_
  simp only [toHom_map, Category.assoc, integralComponentMap_subschemeι]

/-- **The cycle class of a point is pushed forward to `deg(x/f x)` times the cycle class of its
image** (Fulton, §19.1; zero when `f x` has smaller delta-dimension). -/
theorem pushforward_pointCycleClass {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (pointCycleClass R x hx) =
      (f.residueDegree x : ℤ) • pointCycleClassOrZero R k (f.base x) := by
  classical
  have hμ := (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1
  unfold pointCycleClass
  rw [borelMooreHomology.pushforward_pushforward_eq_comp,
    borelMooreHomology.pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R)
      (topCatMap_subschemeι_comp f x) _
      ((isProperMap_map (K := ℂ) (integralComponentAt (f.base x)).subschemeι).comp
        (isProperMap_map (K := ℂ) (integralComponentMap f x))),
    ← borelMooreHomology.pushforward_pushforward_eq_comp R (ModuleCat.of R R) _ _
      (isProperMap_map (K := ℂ) (integralComponentMap f x))
      (isProperMap_map (K := ℂ) (integralComponentAt (f.base x)).subschemeι)]
  by_cases hd :
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) (f.base x) = k
  · have hμW := (existsUnique_isVarietyFundamentalClass R
      (natCast_eq_dimension_integralComponentAt (f.base x) hd)).choose_spec.1
    rw [pointCycleClassOrZero, dif_pos hd, pointCycleClass,
      IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul (integralComponentMap f x)
        (surjective_integralComponentMap f x) (natCast_eq_dimension_integralComponentAt _ hd) hμ hμW,
      residueDegree_integralComponentMap, map_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  · rw [pointCycleClassOrZero, dif_neg hd, smul_zero]
    have hlt : topologicalKrullDim (integralComponentAt (f.base x)).subscheme <
        topologicalKrullDim (integralComponentAt x).subscheme := by
      rw [dimension_integralComponentAt, ← natCast_eq_dimension_integralComponentAt x hx]
      have hle := relativeDimension_map_le f x
      have h0 := relativeDimension_fieldChowSituation_nonneg ℂ (Y ↘ Spec (.of ℂ)) (f.base x)
      exact_mod_cast (show (relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) (f.base x)).toNat < k by omega)
    rw [pushforward_eq_zero_of_dimension_lt (integralComponentMap f x)
      (natCast_eq_dimension_integralComponentAt x hx) hlt, map_zero]

/-- **Proper push-forward of a prime cycle** (Stacks 02R4): `f_*[x] = deg(x/f x) [f x]` when `f x`
has the delta-dimension `k` of `x`, and `0` otherwise. -/
theorem properPushforward_pointCycle_eq {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    properPushforward (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) k
        (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) =
      if hd : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) (f.base x) = k then
        (f.residueDegree x : ℤ) • pointCycle (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k (f.base x) hd
      else 0 := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [properPushforward_apply, finsum_mem_def,
    finsum_eq_single _ x (fun x' hx' ↦ by simp [pointCycle_apply, hx'])]
  by_cases hd : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) (f.base x) = k
  · rw [dif_pos hd]
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, pointCycle_apply,
      if_true, one_mul, hx, hd]
    by_cases hy : f.base x = y
    · subst hy; simp [pointCycle_apply]
    · simp [pointCycle_apply, hy, Ne.symm hy]
  · rw [dif_neg hd]
    have hne : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x ≠
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) (f.base x) :=
      fun h ↦ hd (h ▸ hx)
    simp [Set.indicator, pointCycle_apply, hne]

section Decomposition

variable {R} {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]

/-- The prime cycle `[x]` of a point of delta-dimension `k`, and `0` at the other points. -/
def pointCycleOrZero (k : ℕ) (x : Z) : CycleGroup (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k :=
  if h : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) x = k
  then pointCycle (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k x h else 0

open Classical in
/-- For `x` of delta-dimension `k`, the coefficient of `pointCycleOrZero k x` at `y` is `1` if
`y = x` and `0` otherwise. -/
theorem pointCycleOrZero_apply {k : ℕ} {x : Z}
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) x = k)
    (y : Z) : (pointCycleOrZero k x).1 y = if y = x then 1 else 0 := by
  simp only [pointCycleOrZero, dif_pos hx, pointCycle_apply]

/-- A cycle on a complex scheme is the finite sum of the prime cycles of its support. -/
theorem eq_sum_pointCycleOrZero {k : ℕ} (α : CycleGroup (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k) :
    α = ∑ x ∈ (finite_support_cycle α).toFinset, α.1 x • pointCycleOrZero k x := by
  classical
  have hS := finite_support_cycle α
  have hmem : ∀ x ∈ hS.toFinset,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) x = k :=
    fun x hx ↦ (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ k α.1).mp α.2 x
      (hS.mem_toFinset.mp hx)
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  simp only [AddSubmonoidClass.coe_finset_sum, AddSubgroupClass.coe_zsmul,
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ hS.toFinset
  · rw [Finset.sum_eq_single y (fun x hx hxy ↦ by
        rw [pointCycleOrZero_apply (hmem x hx), if_neg (Ne.symm hxy), mul_zero])
      (fun h ↦ absurd hy h), pointCycleOrZero_apply (hmem y hy), if_pos rfl, mul_one]
  · rw [Finset.sum_eq_zero fun x hx ↦ by
      rw [pointCycleOrZero_apply (hmem x hx), if_neg fun h : y = x ↦ hy (by rw [h]; exact hx),
        mul_zero]]
    exact Function.notMem_support.mp fun h ↦ hy (hS.mem_toFinset.mpr h)

variable (R) in
/-- The cycle class of `pointCycleOrZero k x` is `pointCycleClassOrZero R k x`. -/
theorem cycleClass_pointCycleOrZero (k : ℕ) (x : Z) :
    cycleClass R k (pointCycleOrZero k x) = pointCycleClassOrZero R k x := by
  unfold pointCycleOrZero pointCycleClassOrZero
  split_ifs with h
  · exact cycleClass_pointCycle R x h
  · exact map_zero _

/-- The cycle class is the finite sum of the cycle classes of the points of the support. -/
theorem cycleClass_eq_sum {k : ℕ} (α : CycleGroup (fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) k) :
    cycleClass R k α =
      ∑ x ∈ (finite_support_cycle α).toFinset, α.1 x • pointCycleClassOrZero R k x := by
  conv_lhs => rw [eq_sum_pointCycleOrZero α]
  simp only [map_sum, map_zsmul, cycleClass_pointCycleOrZero]

end Decomposition

/-- **The cycle class commutes with proper push-forward** (Fulton, §19.1): for a proper
morphism `f : X → Y` of complex schemes and a cycle `α` of delta-dimension `k` on `X`,
`cl_Y(f_* α) = f_* cl_X(α)` in `H_{2k}(Y)`. -/
theorem cycleClass_properPushforward {k : ℕ} (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    cycleClass (X := Y) R k (properPushforward (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
        (comp_over f _) k α) =
      borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
        (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (cycleClass (X := X) R k α) := by
  classical
  let P : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+ CycleGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k :=
    AddMonoidHom.mk' (properPushforward (fieldChowSituation ℂ) _ _ f (comp_over f _) k)
      (properPushforward_add (fieldChowSituation ℂ) _ _ f (comp_over f _) k)
  let F : BMHomology R X (2 * k) →+ BMHomology R Y (2 * k) :=
    (borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
      (isProperMap_map (K := ℂ) f) (2 * k : ℕ)).hom.toAddMonoidHom
  change cycleClass (X := Y) R k (P α) = F (cycleClass (X := X) R k α)
  conv_lhs => rw [eq_sum_pointCycleOrZero α]
  rw [map_sum, map_sum, cycleClass_eq_sum α, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hxk : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ k α.1).mp α.2 x
      ((finite_support_cycle α).mem_toFinset.mp hx)
  rw [map_zsmul, map_zsmul, map_zsmul]
  congr 1
  change cycleClass (X := Y) R k (properPushforward (fieldChowSituation ℂ) _ _ f (comp_over f _) k
    (pointCycleOrZero k x)) = F (pointCycleClassOrZero R k x)
  rw [pointCycleOrZero, dif_pos hxk, pointCycleClassOrZero, dif_pos hxk]
  change _ = borelMooreHomology.pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) f))
    (isProperMap_map (K := ℂ) f) (2 * k : ℕ) (pointCycleClass R x hxk)
  rw [pushforward_pointCycleClass, properPushforward_pointCycle_eq]
  split_ifs with hd
  · rw [map_zsmul, cycleClass_pointCycle, pointCycleClassOrZero, dif_pos hd]
  · rw [map_zero, pointCycleClassOrZero, dif_neg hd, smul_zero]

end MMP.Chow
