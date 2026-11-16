module

public import MMP.AlgebraicGeometry.Chow.CycleClass
public import MMP.AlgebraicGeometry.Chow.RationalEquivalenceFibreDifference

/-!
# The cycle class map on rationally trivial cycles

Let `X` be a complex scheme. By Stacks 02S4 (4) a `k`-cycle on `X` rationally equivalent to zero
is a finite sum of fibre differences `[W₀]_k - [W_∞]_k` of integral closed subschemes
`W ⊆ X ×_ℂ ℙ¹_ℂ` (`MMP.Chow.exists_finite_fibreDifferences`). Hence the cycle class map
`MMP.Chow.cycleClass` vanishes on rationally trivial cycles as soon as it vanishes on every such
fibre difference; for the latter, see Fulton §19.1 and
`MMP.Chow.cycleClass_eq_zero_of_isRationallyEquivalentToZero`.

## Main results

* `MMP.Chow.cycleClass_eq_zero_of_forall_fibreDifference`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

namespace MMP.Chow

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- The cycle class of a `k`-cycle rationally equivalent to zero vanishes, provided the cycle
class of the fibre difference `[W₀]_k - [W_∞]_k` vanishes for every integral closed subscheme
`W ⊆ X ×_ℂ ℙ¹_ℂ` of relative dimension `k + 1` contained in neither distinguished section. -/
theorem cycleClass_eq_zero_of_forall_fibreDifference (k : ℕ)
    (h : ∀ W : (projectiveLineProduct (X ↘ Spec (.of ℂ))).IdealSheafData,
      IsIntegral W.subscheme →
      (∀ ξ : genericPoints W.subscheme,
        relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (familyBase (X ↘ Spec (.of ℂ)) W) ξ.1 = k + 1) →
      ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection (X ↘ Spec (.of ℂ))) →
      ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection (X ↘ Spec (.of ℂ))) →
      cycleClass R k (fibreDifference (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k W) = 0)
    (α : CycleGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (hα : IsRationallyEquivalentToZero (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k α) :
    cycleClass R k α = 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  obtain ⟨J, _, W, hInt, hDim, h0, hInf, rfl⟩ :=
    exists_finite_fibreDifferences (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k α hα
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ ↦ h (W j) (hInt j) (hDim j) (h0 j) (hInf j)

end MMP.Chow
