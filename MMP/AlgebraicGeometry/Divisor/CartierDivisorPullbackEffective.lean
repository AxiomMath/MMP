/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullback

/-!
# Effectivity and support of the pull-back of a Cartier divisor

Let `f : X' ⟶ X` be a morphism from an integral scheme whose image is not contained in the support
of a Cartier divisor `A` on `X`. Then the pull-back `f^*A` (`MMP.CartierDivisor.pullback`) is
effective when `A` is, and its support lies over the support of `A` (Fulton, §2.3).

## Main results

* `MMP.CartierDivisor.isEffective_pullback`: the pull-back of an effective divisor is effective.
* `MMP.CartierDivisor.cartierSupport_pullback_subset`: `|f^*A| ⊆ f⁻¹|A|`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.3.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace MMP.CartierDivisor

variable {Y Y' : Scheme.{u}} [IsIntegral Y'] (g : Y' ⟶ Y)

/-- The pull-back of an effective Cartier divisor along `g : Y' ⟶ Y` from an integral scheme with
`g(Y') ⊄ |A|` is effective: a regular local equation `a` of `A` on `U` pulls back to the regular
local equation `g^*a` of `g^*A` on `g⁻¹(U)`. -/
theorem isEffective_pullback {A : Y.CartierDivisor} (hA : MMP.Intersection.IsEffective A)
    (hAg : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport A) :
    MMP.Intersection.IsEffective (pullback g A hAg) := by
  intro x
  obtain ⟨U, hxU, a, hu, hloc⟩ := hA (g x)
  have hη : g (genericPoint Y') ∈ U :=
    MMP.CartierDivisorPullback.genericPoint_mem (V := g ⁻¹ᵁ U) hxU
  have hξ : genericPoint Y' ∈ g ⁻¹ᵁ U := MMP.CartierDivisorPullback.genericPoint_mem hxU
  obtain ⟨a₀, ha₀⟩ := exists_isGermUnit_of_not_range_subset g A hAg hloc hη
  have hstalk : a₀.val = Y.presheaf.germ U _ hη a := by
    apply MMP.CartierDivisorPullback.stalkToTotalQuotient_injective Y
    rw [ha₀, IsUnit.unit_spec]
    exact (MMP.CartierDivisorPullback.stalkToTotalQuotient_germ hη a).symm
  have hval : MMP.Intersection.toTotalQuotient (g ⁻¹ᵁ U) (g.app U a) =
      (MMP.CartierDivisorPullback.ofFunctionField (g ⁻¹ᵁ U)
        (MMP.CartierDivisorPullback.pullbackGerm g a₀) : _) := by
    refine MMP.CartierDivisorPullback.toTotalQuotient_eq_functionFieldToK _ hξ ?_
    change _ = (g.stalkMap (genericPoint Y')).hom a₀.val
    rw [hstalk, Scheme.Hom.germ_stalkMap_apply]
  have hu' : IsUnit (MMP.Intersection.toTotalQuotient (g ⁻¹ᵁ U) (g.app U a)) :=
    hval ▸ Units.isUnit _
  refine ⟨g ⁻¹ᵁ U, hxU, g.app U a, hu', ?_⟩
  rw [show hu'.unit = _ from Units.ext ((IsUnit.unit_spec _).trans hval)]
  exact isLocalEquationOn_pullback g A hAg hloc hη ha₀

/-- The support of a pulled-back Cartier divisor lies over the support of the divisor. -/
theorem cartierSupport_pullback_subset (A : Y.CartierDivisor)
    (hAg : ¬ Set.range g ⊆ MMP.Intersection.cartierSupport A) :
    MMP.Intersection.cartierSupport (pullback g A hAg) ⊆
      g.base ⁻¹' MMP.Intersection.cartierSupport A := by
  intro y hy
  by_contra hgy
  obtain ⟨V, hgyV, -, hV⟩ := (MMP.Intersection.notMem_cartierSupport_iff (U := ⊤) trivial).1 hgy
  have hloc : MMP.Intersection.IsLocalEquationOn A _
      (1 : (Y.totalQuotientSheaf.obj.obj (Opposite.op V))ˣ) := by
    have h0 := MMP.Intersection.cartierClass_map_units V 1
    rw [map_one] at h0
    exact h0.trans hV.symm
  have hyV : y ∈ g ⁻¹ᵁ V := hgyV
  have hη : g (genericPoint Y') ∈ V :=
    MMP.CartierDivisorPullback.genericPoint_mem (V := g ⁻¹ᵁ V) hyV
  have hpb := isLocalEquationOn_pullback g A hAg hloc hη (a := 1)
    (by simp [MMP.CartierDivisorPullback.IsGermUnit])
  have h1 : MMP.CartierDivisorPullback.ofFunctionField (g ⁻¹ᵁ V)
      (MMP.CartierDivisorPullback.pullbackGerm g 1) = 1 := by
    simp [MMP.CartierDivisorPullback.pullbackGerm, MMP.CartierDivisorPullback.ofFunctionField]
  rw [h1, MMP.Intersection.IsLocalEquationOn, MMP.Intersection.cartierClass_one] at hpb
  exact (MMP.Intersection.notMem_cartierSupport_iff (U := ⊤) trivial).2
    ⟨g ⁻¹ᵁ V, hyV, le_top, hpb.symm⟩ hy

end MMP.CartierDivisor
