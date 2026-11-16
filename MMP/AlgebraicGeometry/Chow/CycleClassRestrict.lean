module

public import MMP.AlgebraicGeometry.SubschemeOver
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows

/-!
# The cycle class near a point of the support (Fulton, §19.1)

Let `α` be a cycle of delta-dimension `k` on a complex scheme `X` (Stacks' cycles over
`fieldChowSituation ℂ`) and `W ⊆ X(ℂ)` an open set that misses `closure {x'}(ℂ)` for every point
`x' ≠ x` of delta-dimension `k`. Then `cl(α)|_W = α(x) · cl(x)|_W`: the cycle class is the sum of
the classes `α(x') cl(x')`, and `cl(x')` is supported on `closure {x'}(ℂ)`.

## Main results

* `MMP.Chow.restrict_cycleClass_eq_smul`: `cl(α)|_W = α(x) · cl(x)|_W` when `W` misses
  `closure {x'}(ℂ)` for every other point `x'` of delta-dimension `k`.
* `MMP.Chow.restrict_cycleClass_eq_smul_of_irreducibleComponent`: the case of the generic point
  `ξ` of a component `Z` of delta-dimension `k` and `W` missing the other components.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open scoped MMP.SubschemeOver
open AlgebraicGeometry CategoryTheory MMP MMP.UnderlyingSpace Stacks.Chow Set

namespace MMP.Chow

section ComponentGenericPoint

variable {X : Scheme.{0}}

/-- The generic point of an irreducible component. -/
def componentGenericPoint (j : irreducibleComponents X) : X :=
  (j.2.1 : IsIrreducible j.1).genericPoint

/-- The closure of the generic point of an irreducible component is the component. -/
theorem closure_componentGenericPoint (j : irreducibleComponents X) :
    closure ({componentGenericPoint j} : Set X) = j.1 := by
  have h := (j.2.1 : IsIrreducible j.1).isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ j.2).closure_eq] at h
  exact h.def

end ComponentGenericPoint

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The cycle class of a point vanishes on an open set missing the closure of the point. -/
theorem restrict_pointCycleClass_eq_zero {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (W : TopologicalSpace.Opens (UnderlyingSpace ℂ X))
    (hW : Disjoint (W : Set (UnderlyingSpace ℂ X))
      (range (mapFun (K := ℂ) (integralComponentAt x).subschemeι))) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W
      (2 * k : ℕ) (pointCycleClass R x hx) = 0 :=
  borelMooreHomology.restrict_pushforward_eq_zero_of_disjoint R (ModuleCat.of R R)
    (TopCat.ofHom (map (K := ℂ) (integralComponentAt x).subschemeι))
    (isClosedEmbedding_map_of_isClosedImmersion _).isProperMap W hW _ _

/-- **The cycle class near a point of the support** (Fulton, proof of Lemma 19.1.3): if
`W ⊆ X(ℂ)` misses `closure {x'}(ℂ)` for every point `x' ≠ x` of delta-dimension `k`, then
`cl(α)|_W = α(x) · cl(x)|_W`. -/
theorem restrict_cycleClass_eq_smul {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (W : TopologicalSpace.Opens (UnderlyingSpace ℂ X))
    (hW : ∀ x',
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x' = k →
      x' ≠ x → Disjoint (W : Set (UnderlyingSpace ℂ X))
        (range (mapFun (K := ℂ) (integralComponentAt x').subschemeι)))
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W
        (2 * k : ℕ) (cycleClass R k α) =
      α.1 x • borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ X)) W (2 * k : ℕ) (pointCycleClass R x hx) := by
  classical
  have hS := finite_support_cycle α
  have hmem : ∀ y ∈ hS.toFinset,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) y = k :=
    fun y hy ↦ (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ k α.1).mp α.2 y
      (hS.mem_toFinset.mp hy)
  rw [cycleClass_eq_sum α, map_sum]
  have h0 : ∀ y ∈ hS.toFinset, y ≠ x →
      borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W
        (2 * k : ℕ) (α.1 y • pointCycleClassOrZero R k y) = 0 := fun y hy hyx ↦ by
    rw [map_zsmul, pointCycleClassOrZero, dif_pos (hmem y hy),
      restrict_pointCycleClass_eq_zero R y (hmem y hy) W (hW y (hmem y hy) hyx), smul_zero]
  by_cases hxS : x ∈ hS.toFinset
  · rw [Finset.sum_eq_single x h0 (fun h ↦ absurd hxS h), map_zsmul, pointCycleClassOrZero,
      dif_pos hx]
  · have hαx : α.1 x = 0 := Function.notMem_support.mp fun h ↦ hxS (hS.mem_toFinset.mpr h)
    rw [hαx, zero_smul]
    exact Finset.sum_eq_zero fun y hy ↦ h0 y hy fun h ↦ hxS (h ▸ hy)

/-- **The cycle class near the generic point of a component** (Fulton, proof of Lemma 19.1.3):
if `W ⊆ X(ℂ)` misses every other component, then `cl(α)|_W = α(ξ) · cl(ξ)|_W` for the generic
point `ξ` of a component of delta-dimension `k`. -/
theorem restrict_cycleClass_eq_smul_of_irreducibleComponent {k : ℕ} (j : irreducibleComponents X)
    (hj : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      (componentGenericPoint j) = k)
    (W : TopologicalSpace.Opens (UnderlyingSpace ℂ X))
    (hW : ∀ i, i ≠ j → Disjoint (W : Set (UnderlyingSpace ℂ X))
      (range (mapFun (K := ℂ) (irreducibleComponentι X i))))
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    borelMooreHomology.restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) W
        (2 * k : ℕ) (cycleClass R k α) =
      α.1 (componentGenericPoint j) • borelMooreHomology.restrict R (ModuleCat.of R R)
        (Y := TopCat.of (UnderlyingSpace ℂ X)) W (2 * k : ℕ)
          (pointCycleClass R (componentGenericPoint j) hj) := by
  refine restrict_cycleClass_eq_smul R _ hj W (fun x' hx' hne ↦ ?_) α
  obtain ⟨Z', hZ', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x'} : Set X)) isIrreducible_singleton.closure
  by_cases hZj : (⟨Z', hZ'⟩ : irreducibleComponents X) = j
  · exfalso
    have hx'j : x' ∈ j.1 := by
      rw [← hZj]; exact hsub (subset_closure rfl)
    rw [← closure_componentGenericPoint j] at hx'j
    have hlt := relativeDimension_lt_of_specializes (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (specializes_iff_mem_closure.mpr hx'j) (Ne.symm hne)
    omega
  · refine (hW _ hZj).mono_right ?_
    rw [range_mapFun_of_isClosedImmersion, range_mapFun_of_isClosedImmersion,
      Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      range_irreducibleComponentι]
    exact fun p hp ↦ hsub hp

end MMP.Chow
