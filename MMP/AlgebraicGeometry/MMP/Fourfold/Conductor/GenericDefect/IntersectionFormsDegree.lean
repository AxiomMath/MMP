module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.IsolatedPointAlgebraicKernel
public import MMP.AlgebraicGeometry.Chow.CapDegreeDivisorGysinComponent

/-!
# Degrees of first Chern class caps on a complex threefold

Let `W` be a scheme proper over `ℂ` of dimension three. This file states, in the exact term shapes
`MMP.Fourfold.linearCombination_num3_eq_zero_of_divisorClass_eq_zero` uses, two facts about
the degree `deg(c₁(L₂) c₁(L₃) ∩ -)` on Stacks' Chow group `A_2(W)`:

* `deg(c₁(L₂) c₁(L₃) ∩ c₁(M) ∩ [W]) = (M · L₂ · L₃)`;
* on a scheme with an ample invertible module, `∑ᵢ cᵢ deg(c₁(K) ∩ aᵢ) = 0` when
  `∑ᵢ cᵢ cl(aᵢ) = 0`.

## Main results

* `MMP.Fourfold.num3_eq_capDegree_firstChernClassCapChow_fundamentalChowClass`
* `MMP.Fourfold.sum_intCast_mul_capDegree_eq_zero_of_isAmple`

## Implementation notes

The proofs of invertibility and of local finite type that the degrees carry are implicit
arguments, so that a caller's elaboration of the degree is matched as it stands: the kernel then
never compares two different such proofs, which in a larger environment it does by unfolding.
-/

public section

open AlgebraicGeometry CategoryTheory Stacks.Chow
open MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel

namespace MMP.Fourfold

section Proper

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsProper (W ↘ Spec (.of ℂ))]
  (M L₂ L₃ : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
  [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
  [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]

/-- `deg(c₁(L₂) c₁(L₃) c₁(M) ∩ [W]) = (L₂ · L₃ · M)` on a scheme of dimension three. -/
theorem capDegree_snoc_snoc_fundamentalChowClass_eq_num3
    (hd : topologicalKrullDim W = ((1 + 1 + 1 : ℕ) : WithBot ℕ∞)) :
    (capDegree ℂ (W ↘ Spec (.of ℂ))
      (Fin.snoc (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) M)
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ)) :
        ℚ) = num3 W (W ↘ Spec (.of ℂ)) L₂ L₃ M :=
  capDegree_snoc_snoc_eq_num3 L₂ L₃ M hd

/-- `deg(c₁(L₂) c₁(L₃) ∩ c₁(M) ∩ [W]) = deg(c₁(L₂) c₁(L₃) c₁(M) ∩ [W])`. -/
theorem capDegree_firstChernClassCapChow_fundamentalChowClass
    [hM : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M] :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M :=
      hM
    capDegree ℂ (W ↘ Spec (.of ℂ))
      (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules)
      (firstChernClassCapChow (fieldChowSituation ℂ) ((1 + 1 : ℕ) : ℤ) (W ↘ Spec (.of ℂ)) M
        (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ))) =
    capDegree ℂ (W ↘ Spec (.of ℂ))
      (Fin.snoc (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) M)
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ)) :=
  MMP.Chow.capDegree_firstChernClassCapChow (W ↘ Spec (.of ℂ))
    (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules) M
    (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ))

end Proper

/-- `c₁(M) ∩ [W]` does not depend on the proofs that `W` is locally of finite type over `ℂ` and
that `M` is invertible: the class built from properness equals the one built from `W` being a
complex scheme. -/
theorem firstChernClassCapChow_fundamentalChowClass_congr {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsProper (W ↘ Spec (.of ℂ))] (M : W.Modules)
    [hM : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M] :
    @firstChernClassCapChow (fieldChowSituation ℂ) ((1 + 1 : ℕ) : ℤ) W (W ↘ Spec (.of ℂ))
        IsProper.toLocallyOfFiniteType M hM
        (@fundamentalChowClass (fieldChowSituation ℂ) W (W ↘ Spec (.of ℂ))
          IsProper.toLocallyOfFiniteType ((1 + 1 + 1 : ℕ) : ℤ)) =
      firstChernClassCapChow (fieldChowSituation ℂ) ((1 + 1 : ℕ) : ℤ) (W ↘ Spec (.of ℂ)) M
        (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((1 + 1 + 1 : ℕ) : ℤ)) :=
  rfl

/-- **The degree of a first Chern class cap is an intersection number.** On a complex scheme `W`
proper over `ℂ` of dimension three, for invertible modules `M`, `L₂`, `L₃`:
`deg(c₁(L₂) c₁(L₃) ∩ c₁(M) ∩ [W]) = (M · L₂ · L₃)`. -/
theorem num3_eq_capDegree_firstChernClassCapChow_fundamentalChowClass {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsProper (W ↘ Spec (.of ℂ))]
    (M L₂ L₃ : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]
    (hd : topologicalKrullDim W = ((1 + 1 + 1 : ℕ) : WithBot ℕ∞)) :
    num3 W (W ↘ Spec (.of ℂ)) M L₂ L₃ =
      (capDegree ℂ (W ↘ Spec (.of ℂ))
        (Fin.snoc (fun _ : Fin 1 => L₂) L₃ : Fin (1 + 1) → W.Modules)
        (firstChernClassCapChow (fieldChowSituation ℂ) ((1 + 1 : ℕ) : ℤ) (W ↘ Spec (.of ℂ)) M
          (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ))
            ((1 + 1 + 1 : ℕ) : ℤ))) : ℚ) := by
  rw [num3_comm12, num3_comm23]
  exact (capDegree_snoc_snoc_fundamentalChowClass_eq_num3 M L₂ L₃ hd).symm.trans
    (congrArg (Int.cast : ℤ → ℚ)
      ((capDegree_firstChernClassCapChow_fundamentalChowClass M L₂ L₃).symm.trans
        (MMP.Chow.capDegree_congr _ rfl (firstChernClassCapChow_fundamentalChowClass_congr M))))

/-- **Homologically trivial combinations have zero degree.** On a complex scheme proper over `ℂ`
with an ample invertible module, for classes `aᵢ ∈ A_d(X)` and integers `cᵢ` with
`∑ᵢ cᵢ cl(aᵢ) = 0`: `∑ᵢ cᵢ deg(c₁(K₁) ⋯ c₁(K_d) ∩ aᵢ) = 0`. -/
theorem sum_intCast_mul_capDegree_eq_zero_of_isAmple {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A) {d : ℕ}
    (K : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (K j)]
    {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (a : ι → chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d)
    (h : ∑ i ∈ s, c i • MMP.Chow.chowCycleClass ℚ d (a i) = 0) :
    ∑ i ∈ s, (c i : ℚ) * (capDegree ℂ (X ↘ Spec (.of ℂ)) K (a i) : ℚ) = 0 := by
  have hdeg := MMP.Chow.capDegree_eq_zero_of_chowCycleClass_eq_zero_of_isAmple A hA d K
    (∑ i ∈ s, c i • a i) (by rw [map_sum]; simpa only [map_zsmul] using h)
  rw [map_sum] at hdeg
  have h1 := congrArg (Int.cast : ℤ → ℚ) hdeg
  rw [Int.cast_zero, Int.cast_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
  rw [map_zsmul, smul_eq_mul, Int.cast_mul]

end MMP.Fourfold
