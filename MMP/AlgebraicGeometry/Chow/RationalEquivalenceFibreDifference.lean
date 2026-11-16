module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk

/-!
# Rationally trivial cycles on a quasi-compact scheme are finite sums of fibre differences

Let `C` be a Chow situation and `f : X ⟶ C.S` locally of finite type, with `X` quasi-compact.
Stacks Tag 02S4, part (4) (`Stacks.Chow.exists_familyFibreDifferences`) says that a `k`-cycle
`α` rationally equivalent to zero is, coefficient by coefficient, the locally finite sum over a
family `W j` of integral closed subschemes of `X ×_S ℙ¹_S` (of relative dimension `k + 1`, in
neither distinguished section) of the fibre difference `[W j]₀ - [W j]_∞`.

On a quasi-compact `X` only finitely many members of that family have a nonzero fibre
difference: the carriers of the fibre differences form a locally finite family of subsets of
`X` (`Stacks.Chow.locallyFinite_fibreCarrier`), and on a compact space only finitely many
members of a locally finite family are nonempty (`LocallyFinite.finite_setOf_nonempty`). So the
locally finite sum becomes a finite sum, and `α` is an honest finite sum in
`Stacks.Chow.CycleGroup C f k`.

Each summand is written as Stacks writes it for one member: the proper pushforward along the
first projection `W ⟶ X` (`Stacks.Chow.fibreBaseProjection`, proper because `W` is closed in
`X ×_S ℙ¹_S` and `ℙ¹_S ⟶ S` is proper) of the difference of the cycles of the zero and infinity
divisors of `W`, as closed subschemes of `W`
(`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_zeroDivisor` and its infinity
twin identify these pushforwards with the cycles of the two fibres of `W` read in `X`).

## Main results

* `MMP.Chow.fibreDifference_eq_properPushforward_sub`: for a reduced `W`, the fibre difference
  of `W` on `X` is the proper pushforward of the difference of its two fibre cycles on `W`.
* `MMP.Chow.exists_finite_familyFibreDifferences_coeff`: the finite-index coefficient identity.
* `MMP.Chow.exists_finite_fibreDifferences`: `α` is a finite sum of fibre differences in
  `CycleGroup C f k`.
* `MMP.Chow.exists_finite_familyFibreDifferences`: `α` is a finite sum of proper pushforwards to
  `X` of fibre differences on the members.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace MMP.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- For a reduced closed subscheme `W` of `X ×_S ℙ¹_S`, the fibre difference of `W` on `X` is the
proper pushforward along `W ⟶ X` of the difference of the cycles of the zero and infinity
divisors of `W`, as closed subschemes of `W`. -/
theorem fibreDifference_eq_properPushforward_sub (W : (projectiveLineProduct f).IdealSheafData)
    [IsReduced W.subscheme] :
    fibreDifference C f k W =
      properPushforward C (familyBase f W) f (fibreBaseProjection f W)
        (fibreBaseProjection_comp f W) k
        (cycleAssociatedToClosedSubscheme C (familyBase f W) (zeroDivisor f W).subschemeι k -
          cycleAssociatedToClosedSubscheme C (familyBase f W)
            (infinityDivisor f W).subschemeι k) := by
  rw [properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_zeroDivisor C f W k,
    properPushforward_cycleAssociatedToClosedSubscheme_infinityDivisor C f W k]
  rfl

/-- The family produced by Stacks 02S4 part (4), cut down to the finitely many members whose
fibre carrier is nonempty, still sums coefficientwise to `α`. -/
theorem exists_finite_familyFibreDifferences_coeff [CompactSpace X] (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) :
    ∃ (J : Type u) (_ : Fintype J) (W : J → (projectiveLineProduct f).IdealSheafData),
      (∀ j, IsIntegral (W j).subscheme) ∧
      (∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
      (∀ x : X, α.1 x = ∑ j, (fibreDifference C f k (W j)).1 x) := by
  obtain ⟨J, W, hInt, hDim, h₀, hInf, hLoc, hcoeff⟩ := exists_familyFibreDifferences C f k α hα
  have hfin := (locallyFinite_fibreCarrier C f W hLoc).finite_setOf_nonempty
  set s : Finset J := hfin.toFinset
  refine ⟨s, inferInstance, fun j ↦ W j, fun j ↦ hInt j, fun j ↦ hDim j, fun j ↦ h₀ j,
    fun j ↦ hInf j, fun x ↦ ?_⟩
  rw [hcoeff x, familyFibreDifferenceCoefficient,
    Finset.sum_coe_sort s (fun j ↦ (fibreDifference C f k (W j)).1 x)]
  refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
  rw [Set.Finite.coe_toFinset]
  exact ⟨x, support_fibreDifference_subset C f k (W j) hj⟩

/-- **Stacks 02S4 part (4), on a quasi-compact scheme.** A `k`-cycle rationally equivalent to
zero is a finite sum, in `CycleGroup C f k`, of fibre differences of integral closed subschemes
of `X ×_S ℙ¹_S` of relative dimension `k + 1`, contained in neither distinguished section. -/
theorem exists_finite_fibreDifferences [CompactSpace X] (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) :
    ∃ (J : Type u) (_ : Fintype J) (W : J → (projectiveLineProduct f).IdealSheafData),
      (∀ j, IsIntegral (W j).subscheme) ∧
      (∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
      α = ∑ j, fibreDifference C f k (W j) := by
  obtain ⟨J, _, W, hInt, hDim, h₀, hInf, hcoeff⟩ :=
    exists_finite_familyFibreDifferences_coeff C f k α hα
  refine ⟨J, inferInstance, W, hInt, hDim, h₀, hInf, Subtype.ext ?_⟩
  ext x
  let e : CycleGroup C f k →+ ℤ :=
    { toFun := fun c ↦ c.1 x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  rw [hcoeff x]
  exact (map_sum e (fun j ↦ fibreDifference C f k (W j)) Finset.univ).symm

/-- **Stacks 02S4 part (4), on a quasi-compact scheme, member by member.** A `k`-cycle
rationally equivalent to zero is a finite sum over integral closed subschemes `W j` of
`X ×_S ℙ¹_S` (of relative dimension `k + 1`, in neither distinguished section) of the proper
pushforward along `W j ⟶ X` of the cycle of the zero divisor of `W j` minus the cycle of its
infinity divisor, both as closed subschemes of `W j`. -/
theorem exists_finite_familyFibreDifferences [CompactSpace X] (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) :
    ∃ (J : Type u) (_ : Fintype J) (W : J → (projectiveLineProduct f).IdealSheafData),
      (∀ j, IsIntegral (W j).subscheme) ∧
      (∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
      α = ∑ j, properPushforward C (familyBase f (W j)) f (fibreBaseProjection f (W j))
        (fibreBaseProjection_comp f (W j)) k
        (cycleAssociatedToClosedSubscheme C (familyBase f (W j))
            (zeroDivisor f (W j)).subschemeι k -
          cycleAssociatedToClosedSubscheme C (familyBase f (W j))
            (infinityDivisor f (W j)).subschemeι k) := by
  obtain ⟨J, _, W, hInt, hDim, h₀, hInf, hsum⟩ := exists_finite_fibreDifferences C f k α hα
  refine ⟨J, inferInstance, W, hInt, hDim, h₀, hInf, hsum.trans (Finset.sum_congr rfl ?_)⟩
  intro j _
  have := hInt j
  exact fibreDifference_eq_properPushforward_sub C f k (W j)

end MMP.Chow

end
