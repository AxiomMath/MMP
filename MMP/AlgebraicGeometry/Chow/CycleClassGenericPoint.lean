module

public import MMP.AlgebraicGeometry.Chow.CycleClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PushforwardDegree
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection

/-!
# Points whose closure is the whole scheme

Let `X` be a scheme locally of finite type over a field `K` and `x ∈ X` a point. If the closure
of `x` is `X`, the delta-dimension of `x` over `Stacks.Chow.fieldChowSituation K` is `dim X`;
in particular the generic point of an irreducible `X` has delta-dimension `dim X`. Conversely,
on an integral `X`, a point of delta-dimension `dim X` is the generic point. On a complex variety
`V`, the cycle class `cl_V(x)` of a point whose closure is `V` is the fundamental class of `V`.

## Main results

* `MMP.Chow.relativeDimension_eq_of_closure_eq_univ`,
  `MMP.Chow.relativeDimension_genericPoint_eq`: a point with closure `X` has delta-dimension
  `dim X`.
* `MMP.Chow.closure_eq_univ_of_relativeDimension_eq`: on an integral scheme a point of
  delta-dimension `dim X` has closure `X`.
* `MMP.Chow.pointCycleClass_eq_of_closure_eq_univ`: `cl_V(x) = [V]` when `closure {x} = V`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Chow

namespace MMP.Chow

universe u

section Dimension

variable (K : Type u) [Field K] {X : Scheme.{u}}

/-- A point whose closure is the whole scheme has delta-dimension the dimension of the scheme. -/
theorem relativeDimension_eq_of_closure_eq_univ (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {x : X} (hx : closure ({x} : Set X) = Set.univ) {n : ℕ}
    (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation K).dimensionFunction p x = n :=
  Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    K p x n (by rw [hx, (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hX])

/-- The generic point of an irreducible scheme has delta-dimension the dimension of the
scheme. -/
theorem relativeDimension_genericPoint_eq [IrreducibleSpace X] [QuasiSober X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] {n : ℕ}
    (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation K).dimensionFunction p (genericPoint X) = n :=
  relativeDimension_eq_of_closure_eq_univ K p (genericPoint_spec X).def hX

open Stacks.Intersection in
/-- On an integral scheme of dimension `n` locally of finite type over a field, a point of
delta-dimension `n` is the generic point: its closure is the whole scheme. -/
theorem closure_eq_univ_of_relativeDimension_eq [X.Over (Spec (.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {n : ℕ}
    (hX : topologicalKrullDim X = (n : WithBot ℕ∞)) (x : X)
    (hx : relativeDimension (fieldChowSituation K).dimensionFunction (X ↘ Spec (.of K)) x = n) :
    closure ({x} : Set X) = Set.univ := by
  have : IrreducibleSpace X := irreducibleSpace_of_isIntegral X
  have hh : Order.height x = (n : ℕ∞) := by
    have h := ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      K (X ↘ Spec (.of K)) x n hx
    rw [MMP.topologicalKrullDim_closure_singleton_eq_height] at h
    exact_mod_cast h
  have h1 := MMP.height_add_coheight_eq_krullDim K x
  rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at h1
  change _ = topologicalKrullDim X at h1
  rw [hX, hh] at h1
  have hc : Order.coheight x = 0 := by
    have h2 : (n : ℕ∞) + Order.coheight x = (n : ℕ∞) := by exact_mod_cast h1
    generalize Order.coheight x = c at h2 ⊢
    induction c with
    | top => exact absurd h2 (by rw [add_top]; exact ENat.top_ne_natCast _)
    | coe m => norm_cast at h2 ⊢; omega
  have hmax : IsMax x := Order.coheight_eq_zero.mp hc
  have hxg : x = genericPoint X :=
    (Specializes.antisymm (hmax (genericPoint_specializes x)) (genericPoint_specializes x)).eq
  rw [hxg]
  exact (genericPoint_spec X).def

/-- A closed point of a scheme locally of finite type over a field has delta-dimension zero. -/
theorem relativeDimension_eq_zero_of_isClosed [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {x : X} (hx : IsClosed ({x} : Set X)) :
    relativeDimension (fieldChowSituation K).dimensionFunction
      (X ↘ Spec (.of K)) x = ((0 : ℕ) : ℤ) := by
  have h1 := Stacks.Chow.topologicalKrullDim_closure_singleton_eq K (X ↘ Spec (.of K)) x
  rw [hx.closure_eq] at h1
  haveI : Subsingleton ({x} : Set X) := Set.subsingleton_singleton.coe_sort
  have h2 := @topologicalKrullDim_zero_of_discreteTopology ({x} : Set X) _
    Subsingleton.discreteTopology
  rw [h1] at h2
  have h3 : (relativeDimension (fieldChowSituation K).dimensionFunction
      (X ↘ Spec (.of K)) x).toNat ≤ 0 := by exact_mod_cast h2
  have h0 : (0 : ℤ) ≤ relativeDimension (fieldChowSituation K).dimensionFunction
      (X ↘ Spec (.of K)) x :=
    Stacks.Chow.relativeDimension_nonneg (fieldChowSituation K) (fun _ _ ↦ rfl)
      (X ↘ Spec (.of K)) x
  rw [Nat.cast_zero]
  omega

end Dimension

section CycleClass

variable {R : Type} [CommRing R] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V]
  [IsIntegral V]

/-- **The cycle class of a dense point is the fundamental class**: if the closure of `x` is the
complex variety `V`, then `cl_V(x) = [V]`. -/
theorem pointCycleClass_eq_of_closure_eq_univ {k : ℕ} (x : V)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (V ↘ Spec (.of ℂ)) x = k)
    (hxV : closure ({x} : Set V) = Set.univ) (hk : (k : WithBot ℕ∞) = topologicalKrullDim V)
    {c : MMP.borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V))
      ((2 * k : ℕ) : ℤ)}
    (hc : IsVarietyFundamentalClass R hk c) :
    pointCycleClass R x hx = c := by
  have hsurj : Function.Surjective (integralComponentAt x).subschemeι := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      coe_support_integralComponentAt, hxV]
  unfold pointCycleClass
  rw [IsVarietyFundamentalClass.pushforward_eq_residueDegree_smul _ hsurj hk
    (existsUnique_isVarietyFundamentalClass R
      (natCast_eq_dimension_integralComponentAt x hx)).choose_spec.1 hc,
    residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul]

end CycleClass

end MMP.Chow
