module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# The orthogonal projection onto the range of an injective operator

For an injective `K : H →L[ℂ] V` between finite-dimensional complex inner product spaces,
`K† K` is invertible and `P = K (K† K)⁻¹ K†` is the orthogonal projection onto `range K`: a
self-adjoint idempotent with range `range K`. The formula makes `P` depend continuously on `K`.
A self-adjoint idempotent is determined by its range.

## Main definitions

* `MMP.rangeProj`: `K (K† K)⁻¹ K†`.

## Main results

* `MMP.isUnit_adjoint_comp_self`: `K† K` is invertible for `K` injective.
* `MMP.isIdempotentElem_rangeProj`, `MMP.isSelfAdjoint_rangeProj`,
  `MMP.range_rangeProj`.
* `MMP.continuousOn_rangeProj`: `rangeProj K` depends continuously on `K` where `K† K` is
  invertible.
* `MMP.eq_of_range_eq_of_isSelfAdjoint`: self-adjoint idempotents with the same
  range are equal.
-/

@[expose] public noncomputable section

open ContinuousLinearMap

namespace MMP

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The orthogonal projection `K (K† K)⁻¹ K†` onto the range of `K` (for `K† K` invertible). -/
def rangeProj (K : H →L[ℂ] V) : V →L[ℂ] V :=
  K ∘L Ring.inverse (adjoint K ∘L K) ∘L adjoint K

variable {K : H →L[ℂ] V}

/-- If `K† K` is invertible, then `rangeProj K ∘L K = K`. -/
lemma rangeProj_comp_self (hu : IsUnit (adjoint K ∘L K)) : rangeProj K ∘L K = K := by
  rw [rangeProj, comp_assoc, comp_assoc, ← mul_def, Ring.inverse_mul_cancel _ hu, one_def, comp_id]

/-- If `K† K` is invertible, then `rangeProj K` is idempotent. -/
lemma isIdempotentElem_rangeProj (hu : IsUnit (adjoint K ∘L K)) :
    IsIdempotentElem (rangeProj K) := by
  ext v
  change rangeProj K (rangeProj K v) = rangeProj K v
  exact congrArg (fun A : H →L[ℂ] V ↦ A (Ring.inverse (adjoint K ∘L K) (adjoint K v)))
    (rangeProj_comp_self hu)

/-- `rangeProj K` is self-adjoint. -/
lemma isSelfAdjoint_rangeProj : IsSelfAdjoint (rangeProj K) := by
  have hG : IsSelfAdjoint (adjoint K ∘L K) := by
    rw [isSelfAdjoint_iff', adjoint_comp, adjoint_adjoint]
  have hinv : adjoint (Ring.inverse (adjoint K ∘L K)) = Ring.inverse (adjoint K ∘L K) := by
    rw [← star_eq_adjoint, ← Ring.inverse_star, hG.star_eq]
  rw [isSelfAdjoint_iff', rangeProj, adjoint_comp, adjoint_comp, adjoint_adjoint, hinv,
    comp_assoc]

/-- If `K† K` is invertible, then the range of `rangeProj K` is the range of `K`. -/
lemma range_rangeProj (hu : IsUnit (adjoint K ∘L K)) :
    LinearMap.range (rangeProj K).toLinearMap = LinearMap.range K.toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨K v, ?_⟩
    change (rangeProj K ∘L K) v = K v
    rw [rangeProj_comp_self hu]

/-- For `K` injective on a finite-dimensional space, `K† K` is invertible. -/
lemma isUnit_adjoint_comp_self [FiniteDimensional ℂ H] (hK : Function.Injective K) :
    IsUnit (adjoint K ∘L K) := by
  have hinj : Function.Injective (adjoint K ∘L K) := by
    rw [← coe_coe, ← LinearMap.ker_eq_bot, ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.2 hK
  exact isUnit_iff_bijective.2
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (adjoint K ∘L K).toLinearMap)).1 hinj⟩

/-- `rangeProj` depends continuously on `K` on a set where `K` is continuous and `K† K` is
invertible. -/
lemma continuousOn_rangeProj {B : Type*} [TopologicalSpace B] {K : B → H →L[ℂ] V} {s : Set B}
    (hK : ContinuousOn K s) :
    ContinuousOn (fun b ↦ rangeProj (K b)) (s ∩ {b | IsUnit (adjoint (K b) ∘L K b)}) := by
  have hA : ContinuousOn (fun b ↦ adjoint (K b)) s := adjoint.continuous.comp_continuousOn hK
  have hG : ContinuousOn (fun b ↦ adjoint (K b) ∘L K b) s := hA.clm_comp hK
  have hI : ContinuousOn (fun b ↦ Ring.inverse (adjoint (K b) ∘L K b))
      (s ∩ {b | IsUnit (adjoint (K b) ∘L K b)}) := by
    rintro b ⟨hbs, u, hu⟩
    have h1 : ContinuousAt Ring.inverse (adjoint (K b) ∘L K b) :=
      hu ▸ NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp_continuousWithinAt (f := fun b ↦ adjoint (K b) ∘L K b) h1
      ((hG b hbs).mono Set.inter_subset_left)
  exact (hK.mono Set.inter_subset_left).clm_comp (hI.clm_comp (hA.mono Set.inter_subset_left))

/-- Two self-adjoint idempotents with the same range are equal. -/
lemma eq_of_range_eq_of_isSelfAdjoint {P P' : V →L[ℂ] V} (hP : IsIdempotentElem P)
    (hP' : IsIdempotentElem P') (hsa : IsSelfAdjoint P) (hsa' : IsSelfAdjoint P')
    (h : LinearMap.range P.toLinearMap = LinearMap.range P'.toLinearMap) : P = P' :=
  IsStarProjection.ext ⟨hP, hsa⟩ ⟨hP', hsa'⟩ h

end MMP
