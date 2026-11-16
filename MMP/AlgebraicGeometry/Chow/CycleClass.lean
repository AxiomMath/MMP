module

public import MMP.AlgebraicGeometry.Chow.RationalCycles
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicGeometry.Chow.CycleClassOf
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension

/-!
# The cycle class of Stacks cycles on a complex scheme

Let `X` be a complex scheme and `C = Stacks.Chow.fieldChowSituation ℂ`. A point `x` of
delta-dimension `k` is the generic point of the integral closed subscheme
`V = Stacks.Chow.integralComponentAt x`, a complex variety of dimension `k` (Stacks 02QO). Its
*cycle class* `cl_X(x) ∈ H_{2k}(X)` is the push-forward along `V → X` of the fundamental class of
`V` (Fulton, §19.1). Extending linearly gives the cycle class map
`MMP.Chow.cycleClass : Z_k(X) →+ H_{2k}(X)` on Stacks' cycles of delta-dimension `k`.

## Main definitions

* `MMP.Chow.pointCycleClass`: the cycle class of the closure of a point of delta-dimension `k`.
* `MMP.Chow.cycleClass`: the cycle class map on `Stacks.Chow.CycleGroup C (X ↘ Spec ℂ) k`.

## Main results

* `MMP.Chow.isCycleClassOf_pointCycleClass`: `cl_X(x)` is a cycle class of `V → X`.
* `MMP.Chow.cycleClass_pointCycle`: the cycle class of the prime cycle `[x]` is `cl_X(x)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MMP MMP.UnderlyingSpace
  Stacks.Chow

namespace MMP.Chow

variable (R : Type) [CommRing R] (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- Borel–Moore homology `H_n(X(ℂ); R)` of the complex points of `X`. -/
abbrev BMHomology (n : ℕ) : Type :=
  borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) n

variable {X}

/-- The integral closed subscheme `closure {x}` of `X`, as a scheme over `ℂ`. -/
instance instOverIntegralComponentAt (x : X) :
    (integralComponentAt x).subscheme.Over (Spec (.of ℂ)) :=
  ⟨(integralComponentAt x).subschemeι ≫ X ↘ Spec (.of ℂ)⟩

/-- The inclusion of `closure {x}` into `X` is a morphism over `ℂ`. -/
instance isOver_subschemeι_integralComponentAt (x : X) :
    (integralComponentAt x).subschemeι.IsOver (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- A closed subscheme of a complex scheme is a complex scheme. -/
theorem isComplexScheme_of_isClosedImmersion {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] : IsComplexScheme Z where
  toLocallyOfFiniteType := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  toQuasiCompact := by
    rw [← comp_over (i) (Spec (.of ℂ))]
    infer_instance
  exists_isClosedImmersion := by
    obtain ⟨V, _, _, j, hj, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := X)
    exact ⟨V, inferInstance, inferInstance, i ≫ j, inferInstance, inferInstance⟩

/-- The integral closed subscheme `closure {x}` of a complex scheme is a complex scheme. -/
instance isComplexScheme_integralComponentAt (x : X) :
    IsComplexScheme (integralComponentAt x).subscheme :=
  isComplexScheme_of_isClosedImmersion (integralComponentAt x).subschemeι

/-- A subvariety of a complex scheme is a complex scheme. -/
instance _root_.MMP.Intersection.Scheme.Subvariety.isComplexScheme_toScheme
    (V : MMP.Intersection.Scheme.Subvariety X) : IsComplexScheme V.toScheme :=
  isComplexScheme_of_isClosedImmersion V.ι

/-- The closed subscheme `closure {x}` is integral. -/
instance isIntegral_integralComponentAt' (x : X) :
    IsIntegral (integralComponentAt x).subscheme :=
  isIntegral_integralComponentAt x

/-- **Stacks 02QO.** The integral closed subscheme attached to a point of delta-dimension `k`
over `fieldChowSituation ℂ` has dimension `k`. -/
theorem natCast_eq_dimension_integralComponentAt {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    (k : WithBot ℕ∞) = topologicalKrullDim (integralComponentAt x).subscheme := by
  have hemb := (integralComponentAt x).subschemeι.isClosedEmbedding.isEmbedding
  have h1 : topologicalKrullDim (integralComponentAt x).subscheme =
      topologicalKrullDim (closure ({x} : Set X)) := by
    rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    exact hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
  rw [h1, topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ)) x, hx]
  rfl

/-- The cycle class `cl_X(x) ∈ H_{2k}(X)` of a point `x` of delta-dimension `k`: the
push-forward of the fundamental class of `closure {x}` along its inclusion. -/
def pointCycleClass {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    BMHomology R X (2 * k) :=
  borelMooreHomology.pushforward R (ModuleCat.of R R)
    (TopCat.ofHom (map (K := ℂ) (integralComponentAt x).subschemeι))
    (isProperMap_map (K := ℂ) (integralComponentAt x).subschemeι) (2 * k : ℕ)
    (existsUnique_isVarietyFundamentalClass R
      (natCast_eq_dimension_integralComponentAt x hx)).choose

/-- `cl_X(x)` is a cycle class of the inclusion of `closure {x}`. -/
theorem isCycleClassOf_pointCycleClass {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    IsCycleClassOf R (integralComponentAt x).subschemeι
      (natCast_eq_dimension_integralComponentAt x hx) (pointCycleClass R x hx) :=
  isCycleClassOf_pushforward (R := R) _ (existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1

/-- The support of a cycle on a quasi-compact scheme is finite. -/
theorem finite_support_cycle {k : ℤ}
    (c : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    (Function.support c.1).Finite := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have := c.1.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ
  simpa using this

/-- A cycle on a complex scheme as a finitely supported function on its points. -/
def cycleToFinsupp {k : ℤ} :
    CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+ (X →₀ ℤ) where
  toFun c := Finsupp.ofSupportFinite c.1 (finite_support_cycle c)
  map_zero' := by ext; simp [Finsupp.ofSupportFinite_coe]
  map_add' a b := by ext; simp [Finsupp.ofSupportFinite_coe]

/-- The value of `cycleToFinsupp c` at `x` is the coefficient of `x` in `c`. -/
@[simp]
theorem cycleToFinsupp_apply {k : ℤ}
    (c : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) (x : X) :
    cycleToFinsupp c x = c.1 x := by
  simp [cycleToFinsupp, Finsupp.ofSupportFinite_coe]

open Classical in
/-- The cycle class `cl_X(x)` of a point, extended by zero to points not of delta-dimension `k`. -/
def pointCycleClassOrZero (k : ℕ) (x : X) : BMHomology R X (2 * k) :=
  if hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k
  then pointCycleClass R x hx else 0

/-- **The cycle class map** `cl_X : Z_k(X) → H_{2k}(X)` on Stacks' cycles of delta-dimension `k`
(Fulton, §19.1): the linear extension of `[x] ↦ cl_X(x)`. -/
def cycleClass (k : ℕ) :
    CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k →+ BMHomology R X (2 * k) :=
  (Finsupp.linearCombination ℤ (pointCycleClassOrZero R k)).toAddMonoidHom.comp cycleToFinsupp

/-- The cycle class of the prime cycle `[x]` is `cl_X(x)`. -/
theorem cycleClass_pointCycle {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    cycleClass R k (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) =
      pointCycleClass R x hx := by
  classical
  have h : cycleToFinsupp (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) =
      Finsupp.single x 1 := by
    ext y
    rw [cycleToFinsupp_apply, pointCycle_apply, Finsupp.single_apply]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [if_neg hyx, if_neg (Ne.symm hyx)]
  change Finsupp.linearCombination ℤ (pointCycleClassOrZero R k)
    (cycleToFinsupp (pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx)) = _
  rw [h, Finsupp.linearCombination_single, one_smul, pointCycleClassOrZero, dif_pos hx]

end MMP.Chow
