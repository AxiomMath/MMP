module

public import MMP.AlgebraicGeometry.Chow.CycleClassRestrict
public import MMP.AlgebraicGeometry.Chow.CycleClassDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage
public import MMP.AlgebraicGeometry.CycleMap.OpenRestriction.Fundamental
public import MMP.AlgebraicTopology.BorelMoore.OpenRestrictionGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial

/-!
# The cycle class map commutes with restriction to open subschemes (Fulton, §19.1)

Let `j : U → X` be an open immersion of complex schemes over `ℂ`. For a cycle `α` of
delta-dimension `k` on `X` (Stacks' cycles over `fieldChowSituation ℂ`), the Borel–Moore
restriction of `cl_X(α)` to the open subset `j(U(ℂ))` of `X(ℂ)` is `cl_U(j^* α)`, read on `U(ℂ)`
through `U(ℂ) ≃ₜ j(U(ℂ))`; here `j^*` is Stacks' restriction of cycles
`Stacks.Chow.cycleGroupRestrict`. The same holds on Chow groups, with
`Stacks.Chow.chowGroupRestrict`.

*Proof* (Fulton). Both sides are additive, so take `α = [x]`. If `x = j z`, then `j^*[x] = [z]`;
the closure of `z` in `U` is the inverse image of the closure of `x`
(`Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion`), so `closure {z} → closure {x}` is
an open immersion of complex varieties of the same dimension, and the fundamental class of
`closure {x}` restricts to that of `closure {z}`
(`MMP.IsVarietyFundamentalClass.pushforward_restrict_opensRangeMap`). If `x ∉ j(U)`, then
`closure {x}` misses the open set `j(U)`, so `j^*[x] = 0` and `cl_X(x)` restricts to `0`.

## Main definitions

* `MMP.Chow.pointClosureOpenMap`: the open immersion `closure {z} → closure {j z}`.

## Main results

* `MMP.Chow.restrict_pointCycleClass_eq_pushforward`,
  `MMP.Chow.restrict_pointCycleClass_eq_zero_of_notMem`: the two cases for a point.
* `MMP.Chow.restrict_cycleClass`: `cl_X(α)|_U = cl_U(j^* α)` on cycles.
* `MMP.Chow.restrict_chowCycleClass`: `cl_X(a)|_U = cl_U(j^* a)` on Chow groups.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
  MMP.UnderlyingSpace MMP.borelMooreHomology MMP.FundamentalClass

namespace MMP.Chow

section PointClosure

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U → X` and a point `z` of `U`, the ideal sheaf of the reduced
closure of `j z` is contained in the image under `j` of that of the closure of `z`. -/
theorem integralComponentAt_le_map (z : U) :
    integralComponentAt (j.base z) ≤ (integralComponentAt z).map j := by
  rw [← comap_integralComponentAt_of_isOpenImmersion j z]
  exact Scheme.IdealSheafData.le_map_comap _ _

/-- The open immersion `closure {z} → closure {j z}` of reduced closures of points, for an open
immersion `j : U → X` and a point `z` of `U`. -/
def pointClosureOpenMap (z : U) :
    (integralComponentAt z).subscheme ⟶ (integralComponentAt (j.base z)).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ j (integralComponentAt_le_map j z)

/-- The map `closure {z} → closure {j z}` followed by the closed immersion into `X` is the closed
immersion into `U` followed by `j`. -/
@[reassoc]
theorem pointClosureOpenMap_subschemeι (z : U) :
    pointClosureOpenMap j z ≫ (integralComponentAt (j.base z)).subschemeι =
      (integralComponentAt z).subschemeι ≫ j :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- If the ideal sheaf `J` on `X` pulls back along the open immersion `j` to `I`, then the induced
map of closed subschemes `V(I) → V(J)` is an open immersion whose image is the inverse image of
`j(U)` in `V(J)`. -/
theorem isOpenImmersion_subschemeMap_and_range_of_comap_eq {J : X.IdealSheafData}
    {I : U.IdealSheafData} (h : J.comap j = I) (H : J ≤ I.map j) :
    IsOpenImmersion (Scheme.IdealSheafData.subschemeMap I J j H) ∧
      Set.range (Scheme.IdealSheafData.subschemeMap I J j H).base =
        J.subschemeι.base ⁻¹' Set.range j.base := by
  subst h
  rw [← J.comapIso_hom_snd j]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, (J.comapIso j).hom.surjective.range_comp,
    IsOpenImmersion.range_pullbackSnd]
  rfl

/-- The map `closure {z} → closure {j z}` is an open immersion. -/
instance (z : U) : IsOpenImmersion (pointClosureOpenMap j z) :=
  (isOpenImmersion_subschemeMap_and_range_of_comap_eq j
    (comap_integralComponentAt_of_isOpenImmersion j z) _).1

/-- The image of `closure {z} → closure {j z}` is the inverse image of `j(U)`. -/
theorem range_pointClosureOpenMap (z : U) :
    Set.range (pointClosureOpenMap j z).base =
      (integralComponentAt (j.base z)).subschemeι.base ⁻¹' Set.range j.base :=
  (isOpenImmersion_subschemeMap_and_range_of_comap_eq j
    (comap_integralComponentAt_of_isOpenImmersion j z) _).2

variable [X.Over (Spec (.of ℂ))] [U.Over (Spec (.of ℂ))] [j.IsOver (Spec (.of ℂ))]

/-- The map `closure {z} → closure {j z}` is a morphism over `Spec ℂ`. -/
instance (z : U) : (pointClosureOpenMap j z).IsOver (Spec (.of ℂ)) where
  comp_over := by
    change pointClosureOpenMap j z ≫ (integralComponentAt (j.base z)).subschemeι ≫
        X ↘ Spec (.of ℂ) = (integralComponentAt z).subschemeι ≫ U ↘ Spec (.of ℂ)
    rw [pointClosureOpenMap_subschemeι_assoc, comp_over]

/-- A point of `U` has the delta-dimension of its image in `X`. -/
theorem relativeDimension_eq_of_isOver (z : U) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (U ↘ Spec (.of ℂ)) z =
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) (j.base z) := by
  rw [← comp_over j (Spec (.of ℂ)), relativeDimension_comp_isOpenImmersion]

/-- The open subset `closure {z}(ℂ)` of `closure {j z}(ℂ)` is the inverse image of `U(ℂ)`. -/
theorem opensRangeMap_pointClosureOpenMap (z : U) :
    (opensRangeMap (pointClosureOpenMap j z) :
      Opens (TopCat.of (UnderlyingSpace ℂ (integralComponentAt (j.base z)).subscheme))) =
      Opens.comap (TopCat.ofHom (map (K := ℂ) (integralComponentAt (j.base z)).subschemeι)).hom
        (opensRangeMap j : Opens (TopCat.of (UnderlyingSpace ℂ X))) := by
  ext p
  change p ∈ Set.range (mapFun (K := ℂ) (pointClosureOpenMap j z)) ↔
    mapFun (integralComponentAt (j.base z)).subschemeι p ∈ Set.range (mapFun (K := ℂ) j)
  rw [range_mapFun_of_isOpenImmersion, range_mapFun_of_isOpenImmersion]
  refine ⟨fun hp x _ ↦ ?_, fun hp x _ ↦ ?_⟩
  · exact (Set.ext_iff.1 (range_pointClosureOpenMap j z) _).1 (hp (Set.mem_univ x))
  · exact (Set.ext_iff.1 (range_pointClosureOpenMap j z) _).2 (hp (Set.mem_univ x))

end PointClosure

variable (R : Type) [CommRing R] {U X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [U.Over (Spec (.of ℂ))] [IsComplexScheme U] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (.of ℂ))]

/-- **The cycle class of a point restricts to the cycle class of its preimage** (Fulton, §19.1):
for a point `z` of `U` of delta-dimension `k`, `cl_X(j z)|_U = cl_U(z)`, with `H_{2k} U` read on
`j(U(ℂ))` through `U(ℂ) ≃ₜ j(U(ℂ))`. -/
theorem restrict_pointCycleClass_eq_pushforward {k : ℕ} (z : U)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      (j.base z) = k)
    (hz : relativeDimension (fieldChowSituation ℂ).dimensionFunction (U ↘ Spec (.of ℂ)) z = k) :
    restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) (opensRangeMap j)
        (2 * k : ℕ) (pointCycleClass R (j.base z) hx) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((homeomorphOpensRangeMap j : C(UnderlyingSpace ℂ U, opensRangeMap j))))
        (homeomorphOpensRangeMap j).isProperMap (2 * k : ℕ) (pointCycleClass R z hz) := by
  obtain ⟨cV, hcV, hV⟩ := isCycleClassOf_pointCycleClass R (j.base z) hx
  obtain ⟨cW, hcW, hW⟩ := isCycleClassOf_pointCycleClass R z hz
  rw [← hV, ← hW]
  have hA := hcV.pushforward_restrict_opensRangeMap R (pointClosureOpenMap j z)
    (natCast_eq_dimension_integralComponentAt z hz)
    (natCast_eq_dimension_integralComponentAt (j.base z) hx)
  obtain rfl := hcW.eq hA
  rw [restrict_pushforward_apply, restrict_eq_pushforward_opensEqMap
    (opensRangeMap_pointClosureOpenMap j z)]
  refine pushforward_pushforward_apply_eq_pushforward_pushforward_pushforward_apply
    _ _ _ _ _ _ _ _ _ _ ?_ _ _
  ext y
  have hy := mapFun_homeomorphOpensRangeMap_symm_apply (pointClosureOpenMap j z) y
  change (y.1 : UnderlyingSpace ℂ (integralComponentAt (j.base z)).subscheme).toHom ≫
      (integralComponentAt (j.base z)).subschemeι =
    (((homeomorphOpensRangeMap (pointClosureOpenMap j z)).symm y).toHom ≫
      (integralComponentAt z).subschemeι) ≫ j
  rw [← hy]
  change (((homeomorphOpensRangeMap (pointClosureOpenMap j z)).symm y).toHom ≫
      pointClosureOpenMap j z) ≫ (integralComponentAt (j.base z)).subschemeι = _
  rw [Category.assoc, Category.assoc, pointClosureOpenMap_subschemeι]

omit [IsComplexScheme U] in
/-- The cycle class of a point outside `j(U)` restricts to zero on `j(U(ℂ))`: the closure of the
point misses the open set `j(U)`. -/
theorem restrict_pointCycleClass_eq_zero_of_notMem {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (hxU : x ∉ Set.range j.base) :
    restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) (opensRangeMap j)
      (2 * k : ℕ) (pointCycleClass R x hx) = 0 := by
  refine restrict_pointCycleClass_eq_zero R x hx _ (Set.disjoint_left.2 fun p hp hp' ↦ ?_)
  change p ∈ Set.range (mapFun (K := ℂ) j) at hp
  rw [range_mapFun_of_isOpenImmersion] at hp
  rw [range_mapFun_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
    coe_support_integralComponentAt] at hp'
  have h1 : p.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base := hp (Set.mem_univ _)
  obtain ⟨y, hy, hyx⟩ := mem_closure_iff.1 hp' _ j.isOpenEmbedding.isOpen_range h1
  rw [Set.mem_singleton_iff] at hyx
  exact hxU (hyx ▸ hy)

/-- **The cycle class map commutes with restriction to open subschemes, on cycles** (Fulton,
§19.1): for an open immersion `j : U → X` of complex schemes over `ℂ` and a cycle `α` of
delta-dimension `k` on `X`, `cl_X(α)|_U = cl_U(j^* α)`, where `j^*` is Stacks' restriction of
cycles and `H_{2k} U` is read on `j(U(ℂ))` through `U(ℂ) ≃ₜ j(U(ℂ))`. -/
theorem restrict_cycleClass {k : ℕ}
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) (opensRangeMap j)
        (2 * k : ℕ) (cycleClass R k α) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((homeomorphOpensRangeMap j : C(UnderlyingSpace ℂ U, opensRangeMap j))))
        (homeomorphOpensRangeMap j).isProperMap (2 * k : ℕ)
        (cycleClass R k (cycleGroupRestrict (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (U ↘ Spec (.of ℂ)) j (comp_over j _) k α)) := by
  classical
  have h := eq_sum_pointCycleOrZero α
  generalize (finite_support_cycle α).toFinset = s at h
  rw [h]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  congr 1
  unfold pointCycleOrZero
  split_ifs with hx
  · rw [cycleClass_pointCycle]
    by_cases hxU : x ∈ Set.range j.base
    · obtain ⟨z, rfl⟩ := hxU
      have hz := (relativeDimension_eq_of_isOver j z).trans hx
      rw [cycleGroupRestrict_pointCycle (x := z) (hx := hx) (hx' := hz), cycleClass_pointCycle]
      exact restrict_pointCycleClass_eq_pushforward R j z hx hz
    · rw [restrict_pointCycleClass_eq_zero_of_notMem R j x hx hxU]
      have h0 : cycleGroupRestrict (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (U ↘ Spec (.of ℂ)) j (comp_over j _) k
          (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) = 0 := by
        refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
        rw [cycleGroupRestrict_apply, pointCycle_apply, if_neg fun h ↦ hxU ⟨y, h⟩]
        rfl
      rw [h0, map_zero, map_zero]
  · simp

/-- **The cycle class map commutes with restriction to open subschemes, on Chow groups**
(Fulton, §19.1): for an open immersion `j : U → X` of complex schemes over `ℂ` and
`a ∈ A_k(X)`, `cl_X(a)|_U = cl_U(j^* a)`, where `j^*` is Stacks' restriction of Chow classes
and `H_{2k} U` is read on `j(U(ℂ))` through `U(ℂ) ≃ₜ j(U(ℂ))`. -/
theorem restrict_chowCycleClass {k : ℕ}
    (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) (opensRangeMap j)
        (2 * k : ℕ) (chowCycleClass R k a) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom ((homeomorphOpensRangeMap j : C(UnderlyingSpace ℂ U, opensRangeMap j))))
        (homeomorphOpensRangeMap j).isProperMap (2 * k : ℕ)
        (chowCycleClass R k (chowGroupRestrict (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (U ↘ Spec (.of ℂ)) j (comp_over j _) k a)) := by
  induction a using QuotientAddGroup.induction_on with
  | H α => exact restrict_cycleClass R j α

end MMP.Chow
