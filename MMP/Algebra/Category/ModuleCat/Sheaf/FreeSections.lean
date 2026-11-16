module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Sections of a free sheaf of modules of finite rank

Let `R` be a sheaf of rings and `I` a finite type. Every section of the free sheaf of modules
`R^{(I)}` over an object `X` is a linear combination `∑ⱼ aⱼ • eⱼ` of the tautological sections
`eⱼ`, with coefficients `aⱼ ∈ R(X)`: the finite coproduct `R^{(I)}` is a biproduct, so its
sections are those of the product.

## Main definitions

* `MMP.freeProj`: the projection `R^{(I)} ⟶ R` onto the `k`-th factor.

## Main results

* `MMP.exists_eq_sum_smul_freeSection`: every section of `free I` over `X` is
  `∑ j, a j • (freeSection j).1 X`.
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

namespace MMP

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The projection `R^{(I)} ⟶ R` onto the `k`-th factor. -/
noncomputable def freeProj {I : Type} [DecidableEq I] (k : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan I) fun j => if j = k then 𝟙 _ else 0

/-- The `k`-th projection `R^{(I)} ⟶ R` restricted to the `j`-th summand is the identity if
`j = k` and zero otherwise. -/
lemma ιFree_freeProj {I : Type} [DecidableEq I] (j k : I) :
    ιFree j ≫ freeProj (R := R) k = if j = k then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac (isColimitFreeCofan I) _ j

/-- For finite `I`, the sum over `k` of the projections onto the `k`-th factor followed by the
inclusions of the `k`-th summand is the identity of `R^{(I)}`. -/
lemma sum_freeProj_ιFree (I : Type) [Fintype I] [DecidableEq I] :
    ∑ k : I, freeProj (R := R) k ≫ ιFree k = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun j => ?_
  change ιFree j ≫ _ = ιFree j ≫ 𝟙 _
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, ιFree_freeProj]
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_comp])
    (by simp)]
  simp

/-- The value of `ιFree k : R ⟶ R^{(I)}` on `r ∈ R(X)` is `r • eₖ`. -/
lemma ιFree_val_app {I : Type} (k : I) (X : Cᵒᵖ) (r : R.obj.obj X) :
    (ιFree (R := R) k).val.app X r =
      r • (show (free (R := R) I).val.obj X from (freeSection (R := R) k).1 X) := by
  have h1 : (show (free (R := R) I).val.obj X from (freeSection (R := R) k).1 X) =
      (ιFree (R := R) k).val.app X (show (unit R).val.obj X from (1 : R.obj.obj X)) := by
    change ((free I).unitHomEquiv (ιFree k ≫ 𝟙 _)).val X = _
    rw [unitHomEquiv_apply_coe, Category.comp_id]
  rw [h1, ← map_smul]
  congr 1
  exact (mul_one r).symm

/-- Every section of `R^{(I)}` over `X` is a linear combination of the tautological sections
`eⱼ = (freeSection j).1 X` with coefficients in `R(X)`. -/
theorem exists_eq_sum_smul_freeSection {I : Type} [Fintype I] [DecidableEq I] (X : Cᵒᵖ)
    (x : (free (R := R) I).val.obj X) :
    ∃ a : I → R.obj.obj X, x = ∑ j, a j •
      (show (free (R := R) I).val.obj X from (freeSection (R := R) j).1 X) := by
  refine ⟨fun k => (freeProj (R := R) k).val.app X x, ?_⟩
  have h := congrArg (fun f : free (R := R) I ⟶ free I => f.val.app X x)
    (sum_freeProj_ιFree (R := R) I)
  simp only at h
  have hsum : ∀ (s : Finset I) (f : I → (free (R := R) I ⟶ free I)),
      (∑ k ∈ s, f k).val.app X x = ∑ k ∈ s, (f k).val.app X x := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  rw [hsum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  exact ιFree_val_app k X _

end MMP
