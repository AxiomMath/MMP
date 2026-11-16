module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Cochains
public import MMP.AlgebraicTopology.PoincareDuality.MayerVietoris

/-!
# Mayer–Vietoris for singular cohomology, at the cochain level

Let `A`, `B` be open subsets covering a space `Y`. A cochain of a subset `S ⊆ Y` is represented
by a cochain `φ` of `Y`, read on the simplices of `Y` lying in `S` (two cochains agree on `S` iff
their difference lies in `vanishing R n S`); `φ` is a cocycle on `S` iff
`δ φ ∈ vanishing R (n + 1) S`. The `{A, B}`-small simplices are those lying in `A` or in `B`;
a cochain vanishes on them iff it lies in `vanishing R n A ⊓ vanishing R n B`.

With Hatcher's subdivision `ρ = 1 - ∂ D - D ∂` towards `{A, B}` (`smallChainMap`):

* `ρ` fixes small simplices, so `ρ^* φ = φ` on small simplices (`pullback_smallChainMap_apply`);
  `ρ^* φ = 0` if `φ` vanishes on small simplices; for a cocycle `φ`,
  `φ = ρ^* φ + δ (D^* φ)` (`pullback_smallChainMap_succ_of_cocycle`). Hence a cocycle which on
  small simplices is a coboundary is a coboundary (`exists_eq_coboundary_of_small`), and a
  cochain whose coboundary vanishes on small simplices gives the cocycle `ρ^* κ` of `Y`, equal to
  `κ` on small simplices (`coboundary_pullback_eq_zero`).
* The *Mayer–Vietoris coboundary* `mvCoboundary e = ρ^* κ`, `κ = δ (e|_{A ∩ B})` on the simplices
  of `A` and `0` elsewhere, where `e|_{A ∩ B}` is `e` on the simplices of `A ∩ B` and `0`
  elsewhere: a cocycle of `Y` of degree `n + 1` for a cocycle `e` of `A ∩ B` of degree `n`
  (`coboundary_mvCoboundary`).
* Exactness: a cocycle of `Y` which is `δ α` on `A` and `δ β` on `B` is cohomologous to
  `mvCoboundary (α - β)` (`exists_sub_mvCoboundary_eq_coboundary`); cocycles `a` of `A` and `b`
  of `B` cohomologous on `A ∩ B` glue to a cocycle of `Y` (`exists_glue_succ`, `exists_glue_zero`);
  and `mvCoboundary (a - b)` is a coboundary (`exists_mvCoboundary_sub_eq_coboundary`), as is
  `mvCoboundary e` for `e` a coboundary on `A ∩ B` (`exists_mvCoboundary_eq_coboundary`).

## Main definitions

* `MMP.SingularCochain.restrictTo`: `e` on the simplices of `S`, `0` elsewhere.
* `MMP.SingularCochain.mvCoboundary`: the Mayer–Vietoris coboundary.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.2 and §3.1.
-/

@[expose] public noncomputable section

open Finsupp Set Classical

namespace MMP

namespace SingularCochain

open SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

section restrictTo

variable (R) in
/-- The cochain `e` on the simplices of `S`, and `0` elsewhere. -/
def restrictTo (S : Set Y) (n : ℕ) : (Simplex Y n → R) →ₗ[R] (Simplex Y n → R) where
  toFun e σ := if range σ ⊆ S then e σ else 0
  map_add' e f := by ext σ; by_cases h : range σ ⊆ S <;> simp [h]
  map_smul' r e := by ext σ; by_cases h : range σ ⊆ S <;> simp [h]

/-- `restrictTo R S n e σ` is `e σ` if `σ` lies in `S`, and `0` otherwise. -/
lemma restrictTo_apply (S : Set Y) {n : ℕ} (e : Simplex Y n → R) (σ : Simplex Y n) :
    restrictTo R S n e σ = if range σ ⊆ S then e σ else 0 :=
  rfl

/-- `restrictTo R S n e` agrees with `e` on the simplices of `S`. -/
lemma restrictTo_sub_mem_vanishing (S : Set Y) {n : ℕ} (e : Simplex Y n → R) :
    restrictTo R S n e - e ∈ vanishing R n S := fun σ hσ ↦ by
  simp [restrictTo_apply, hσ]

/-- `restrictTo R S n e` vanishes on a simplex not lying in `S`. -/
lemma restrictTo_of_not_subset (S : Set Y) {n : ℕ} (e : Simplex Y n → R) {σ : Simplex Y n}
    (hσ : ¬ range σ ⊆ S) : restrictTo R S n e σ = 0 := by
  simp [restrictTo_apply, hσ]

/-- The restriction to `S` of a cochain vanishing on the simplices of `S` is `0`. -/
lemma restrictTo_eq_zero_of_mem_vanishing (S : Set Y) {n : ℕ} {e : Simplex Y n → R}
    (he : e ∈ vanishing R n S) : restrictTo R S n e = 0 := by
  ext σ
  by_cases hσ : range σ ⊆ S
  · simp [restrictTo_apply, hσ, he σ hσ]
  · simp [restrictTo_apply, hσ]

/-- Cochains agreeing on `S` have coboundaries agreeing on `S`. -/
lemma coboundary_sub_mem_vanishing {n : ℕ} {S : Set Y} {φ ψ : Simplex Y n → R}
    (h : φ - ψ ∈ vanishing R n S) :
    coboundary R n φ - coboundary R n ψ ∈ vanishing R (n + 1) S := by
  rw [← map_sub]
  exact coboundary_mem_vanishing h

/-- A cochain vanishing on the simplices of `T` vanishes on those of a subset `S ⊆ T`. -/
lemma vanishing_anti {n : ℕ} {S T : Set Y} (h : S ⊆ T) : vanishing R n T ≤ vanishing R n S :=
  fun _ hφ σ hσ ↦ hφ σ (hσ.trans h)

end restrictTo

section small

variable {A B : Set Y}

/-- A simplex lying in `A` or in `B` is an `{A, B}`-small chain. -/
lemma single_mem_small_pair {n : ℕ} {σ : Simplex Y n} (hσ : range σ ⊆ A ∨ range σ ⊆ B) :
    single σ (1 : R) ∈ small R n {A, B} := by
  rcases hσ with h | h
  · exact mem_small_of_mem_inside (U := A) (by simp) (single_mem_supported R _ h)
  · exact mem_small_of_mem_inside (U := B) (by simp) (single_mem_supported R _ h)

/-- Hatcher's `ρ` fixes small simplices. -/
lemma smallChainMap_single_of_small {n : ℕ} {σ : Simplex Y n}
    (hσ : range σ ⊆ A ∨ range σ ⊆ B) :
    smallChainMap R {A, B} n (single σ 1) = single σ 1 := by
  have h1 := single_mem_small_pair (R := R) hσ
  cases n with
  | zero => rw [smallChainMap_zero, smallHomotopy_eq_zero_of_mem_small h1, map_zero, sub_zero]
  | succ n =>
    have h2 : bd R n (single σ (1 : R)) ∈ small R n {A, B} := by
      rcases hσ with h | h
      · exact mem_small_of_mem_inside (U := A) (by simp)
          (bd_mem_inside (single_mem_supported R _ h))
      · exact mem_small_of_mem_inside (U := B) (by simp)
          (bd_mem_inside (single_mem_supported R _ h))
    rw [smallChainMap_succ, smallHomotopy_eq_zero_of_mem_small h1,
      smallHomotopy_eq_zero_of_mem_small h2, map_zero, sub_zero, sub_zero]

/-- `ρ^* φ = φ` on small simplices. -/
lemma pullback_smallChainMap_apply {n : ℕ} (φ : Simplex Y n → R) {σ : Simplex Y n}
    (hσ : range σ ⊆ A ∨ range σ ⊆ B) :
    pullback (smallChainMap R {A, B} n) φ σ = φ σ := by
  change eval φ (smallChainMap R {A, B} n (single σ 1)) = φ σ
  rw [smallChainMap_single_of_small hσ]
  simp [eval]

/-- `ρ^* φ - φ` vanishes on small simplices. -/
lemma pullback_smallChainMap_sub_mem {n : ℕ} (φ : Simplex Y n → R) :
    pullback (smallChainMap R {A, B} n) φ - φ ∈ vanishing R n A ⊓ vanishing R n B :=
  ⟨fun σ hσ ↦ by simp [pullback_smallChainMap_apply φ (Or.inl hσ)],
    fun σ hσ ↦ by simp [pullback_smallChainMap_apply φ (Or.inr hσ)]⟩

variable (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ)

include hA hB hAB

/-- `ρ^* φ = 0` if `φ` vanishes on small simplices. -/
lemma pullback_smallChainMap_eq_zero {n : ℕ} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A ⊓ vanishing R n B) : pullback (smallChainMap R {A, B} n) φ = 0 := by
  ext σ
  exact pullback_mem_vanishing hA hB hφ σ (by rw [hAB]; exact subset_univ _)

omit hA hB hAB in
variable (R) in
/-- The pull-back `D^*` along Hatcher's homotopy `D`. -/
def mvHomotopyPullback (A B : Set Y) (n : ℕ) :
    (Simplex Y (n + 1) → R) →ₗ[R] (Simplex Y n → R) where
  toFun ψ σ := eval ψ (smallHomotopy R {A, B} n (single σ 1))
  map_add' φ ψ := by ext σ; simp [linearCombination_apply, mul_add, Finsupp.sum_add]
  map_smul' r φ := by ext σ; simp [linearCombination_apply, Finsupp.mul_sum, mul_left_comm]

omit hA hB hAB in
/-- Evaluating `D^* ψ` on a chain `c` is evaluating `ψ` on `D c`. -/
lemma eval_mvHomotopyPullback {n : ℕ} (ψ : Simplex Y (n + 1) → R) (c : Chain R Y n) :
    eval (mvHomotopyPullback R A B n ψ) c = eval ψ (smallHomotopy R {A, B} n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp [mvHomotopyPullback]

omit hA hB hAB in
/-- For a cocycle `φ` of degree `n + 1`, `ρ^* φ = φ - δ (D^* φ)`. -/
lemma pullback_smallChainMap_succ_of_cocycle {n : ℕ} {φ : Simplex Y (n + 1) → R}
    (hφ : coboundary R (n + 1) φ = 0) :
    pullback (smallChainMap R {A, B} (n + 1)) φ = φ - coboundary R n (mvHomotopyPullback R A B n φ) := by
  ext σ
  change eval φ (smallChainMap R {A, B} (n + 1) (single σ 1)) = _
  have h1 : eval φ (bd R (n + 1) (smallHomotopy R {A, B} (n + 1) (single σ 1))) = 0 := by
    rw [← eval_coboundary, hφ]
    simp
  have h2 : eval φ (smallHomotopy R {A, B} n (bd R n (single σ 1))) =
      coboundary R n (mvHomotopyPullback R A B n φ) σ := by
    rw [← eval_mvHomotopyPullback, ← eval_coboundary]
    simp [eval]
  rw [smallChainMap_succ, map_sub, map_sub, h1, h2]
  simp [eval]

omit hA hB hAB in
/-- For a cocycle `φ` of degree `0`, `ρ^* φ = φ`. -/
lemma pullback_smallChainMap_zero_of_cocycle {φ : Simplex Y 0 → R}
    (hφ : coboundary R 0 φ = 0) : pullback (smallChainMap R {A, B} 0) φ = φ := by
  ext σ
  change eval φ (smallChainMap R {A, B} 0 (single σ 1)) = _
  rw [smallChainMap_zero, map_sub, ← eval_coboundary, hφ]
  simp [eval]

/-- **A cocycle which is a coboundary on small simplices is a coboundary.** -/
theorem exists_eq_coboundary_of_small {n : ℕ} {φ : Simplex Y (n + 1) → R}
    (hφ : coboundary R (n + 1) φ = 0) (θ : Simplex Y n → R)
    (hθ : φ - coboundary R n θ ∈ vanishing R (n + 1) A ⊓ vanishing R (n + 1) B) :
    φ = coboundary R n (pullback (smallChainMap R {A, B} n) θ + mvHomotopyPullback R A B n φ) := by
  have h1 := pullback_smallChainMap_succ_of_cocycle (A := A) (B := B) hφ
  have h2 := pullback_smallChainMap_eq_zero hA hB hAB hθ
  rw [map_sub, ← coboundary_pullback_smallChainMap, sub_eq_zero] at h2
  rw [map_add, ← h2, h1]
  abel

/-- A cocycle of degree `0` vanishing on small simplices is `0`. -/
theorem eq_zero_of_small_zero {φ : Simplex Y 0 → R} (hφ : coboundary R 0 φ = 0)
    (h : φ ∈ vanishing R 0 A ⊓ vanishing R 0 B) : φ = 0 := by
  rw [← pullback_smallChainMap_zero_of_cocycle (A := A) (B := B) hφ]
  exact pullback_smallChainMap_eq_zero hA hB hAB h

/-- A cochain `κ` whose coboundary vanishes on small simplices gives the cocycle `ρ^* κ`. -/
theorem coboundary_pullback_eq_zero {n : ℕ} {κ : Simplex Y n → R}
    (hκ : coboundary R n κ ∈ vanishing R (n + 1) A ⊓ vanishing R (n + 1) B) :
    coboundary R n (pullback (smallChainMap R {A, B} n) κ) = 0 := by
  rw [coboundary_pullback_smallChainMap]
  exact pullback_smallChainMap_eq_zero hA hB hAB hκ

end small

section mayerVietoris

variable (R) in
/-- The cochain `κ` of the Mayer–Vietoris coboundary: `δ (e|_{A ∩ B})` on the simplices of `A`,
`0` elsewhere. -/
def mvKappa (A B : Set Y) (n : ℕ) : (Simplex Y n → R) →ₗ[R] (Simplex Y (n + 1) → R) :=
  restrictTo R A (n + 1) ∘ₗ coboundary R n ∘ₗ restrictTo R (A ∩ B) n

variable (R) in
/-- **The Mayer–Vietoris coboundary** `H^n (A ∩ B) → H^{n+1} (A ∪ B)` on cochains:
`e ↦ ρ^* κ`, `κ = δ (e|_{A ∩ B})` on the simplices of `A`, `0` elsewhere. -/
def mvCoboundary (A B : Set Y) (n : ℕ) : (Simplex Y n → R) →ₗ[R] (Simplex Y (n + 1) → R) :=
  pullback (smallChainMap R {A, B} (n + 1)) ∘ₗ mvKappa R A B n

variable {A B : Set Y}

/-- `κ` agrees with `δ (e|_{A ∩ B})` on the simplices of `A`. -/
lemma mvKappa_sub_mem_vanishing {n : ℕ} (e : Simplex Y n → R) :
    mvKappa R A B n e - coboundary R n (restrictTo R (A ∩ B) n e) ∈ vanishing R (n + 1) A :=
  restrictTo_sub_mem_vanishing A _

/-- `κ` vanishes on the simplices of `B` for a cocycle `e` of `A ∩ B`. -/
lemma mvKappa_mem_vanishing_right {n : ℕ} {e : Simplex Y n → R}
    (he : coboundary R n e ∈ vanishing R (n + 1) (A ∩ B)) :
    mvKappa R A B n e ∈ vanishing R (n + 1) B := fun σ hσB ↦ by
  change restrictTo R A (n + 1) _ σ = 0
  by_cases hσA : range σ ⊆ A
  · rw [restrictTo_apply, if_pos hσA]
    change coboundary R n (restrictTo R (A ∩ B) n e) σ = 0
    have h := coboundary_sub_mem_vanishing (restrictTo_sub_mem_vanishing (A ∩ B) e) σ
      (subset_inter hσA hσB)
    rw [Pi.sub_apply, sub_eq_zero] at h
    rw [h]
    exact he σ (subset_inter hσA hσB)
  · exact restrictTo_of_not_subset A _ hσA

/-- For a cocycle `e` of `A ∩ B`, `δ κ` vanishes on small simplices. -/
lemma coboundary_mvKappa_mem {n : ℕ} {e : Simplex Y n → R}
    (he : coboundary R n e ∈ vanishing R (n + 1) (A ∩ B)) :
    coboundary R (n + 1) (mvKappa R A B n e) ∈ vanishing R (n + 2) A ⊓ vanishing R (n + 2) B := by
  refine ⟨?_, coboundary_mem_vanishing (mvKappa_mem_vanishing_right he)⟩
  have h := coboundary_sub_mem_vanishing (mvKappa_sub_mem_vanishing (A := A) (B := B) e)
  rwa [coboundary_coboundary, sub_zero] at h

/-- `mvCoboundary e` agrees with `κ` on small simplices. -/
lemma mvCoboundary_apply_of_small {n : ℕ} (e : Simplex Y n → R) {σ : Simplex Y (n + 1)}
    (hσ : range σ ⊆ A ∨ range σ ⊆ B) : mvCoboundary R A B n e σ = mvKappa R A B n e σ :=
  pullback_smallChainMap_apply _ hσ

/-- The Mayer–Vietoris coboundary of a cochain vanishing on the simplices of `A ∩ B` is `0`. -/
lemma mvCoboundary_eq_zero_of_mem_vanishing {n : ℕ} {e : Simplex Y n → R}
    (he : e ∈ vanishing R n (A ∩ B)) : mvCoboundary R A B n e = 0 := by
  simp [mvCoboundary, mvKappa, restrictTo_eq_zero_of_mem_vanishing _ he]

/-- Cochains agreeing on the simplices of `A ∩ B` have the same Mayer–Vietoris coboundary. -/
lemma mvCoboundary_congr {n : ℕ} {e e' : Simplex Y n → R}
    (he : e - e' ∈ vanishing R n (A ∩ B)) : mvCoboundary R A B n e = mvCoboundary R A B n e' := by
  rw [← sub_eq_zero, ← map_sub]
  exact mvCoboundary_eq_zero_of_mem_vanishing he

variable (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ)

include hA hB hAB

/-- **The Mayer–Vietoris coboundary of a cocycle of `A ∩ B` is a cocycle of `Y`.** -/
theorem coboundary_mvCoboundary {n : ℕ} {e : Simplex Y n → R}
    (he : coboundary R n e ∈ vanishing R (n + 1) (A ∩ B)) :
    coboundary R (n + 1) (mvCoboundary R A B n e) = 0 :=
  coboundary_pullback_eq_zero hA hB hAB (coboundary_mvKappa_mem he)

/-- **Exactness at `H^{n+1} Y`**: a cocycle `φ` of `Y` which is `δ α` on `A` and `δ β` on `B` is
cohomologous to `mvCoboundary (α - β)`. -/
theorem exists_sub_mvCoboundary_eq_coboundary {n : ℕ} {φ : Simplex Y (n + 1) → R}
    (hφ : coboundary R (n + 1) φ = 0) (α β : Simplex Y n → R)
    (hα : φ - coboundary R n α ∈ vanishing R (n + 1) A)
    (hβ : φ - coboundary R n β ∈ vanishing R (n + 1) B) :
    ∃ η, φ - mvCoboundary R A B n (α - β) = coboundary R n η := by
  have he : coboundary R n (α - β) ∈ vanishing R (n + 1) (A ∩ B) := by
    have := Submodule.sub_mem _ (vanishing_anti inter_subset_right hβ)
      (vanishing_anti inter_subset_left hα)
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  set θ : Simplex Y n → R := fun τ ↦ if range τ ⊆ B then β τ else α τ
  have hθ : θ - (α - restrictTo R (A ∩ B) n (α - β)) ∈ vanishing R n A := fun τ hτA ↦ by
    by_cases hτB : range τ ⊆ B
    · simp [θ, restrictTo_apply, hτB, hτA]
    · simp [θ, restrictTo_apply, hτB, show ¬ range τ ⊆ A ∩ B from fun h ↦ hτB (h.trans
        inter_subset_right)]
  refine ⟨_, exists_eq_coboundary_of_small hA hB hAB (φ := φ - mvCoboundary R A B n (α - β))
    (by rw [map_sub, hφ, coboundary_mvCoboundary hA hB hAB he, sub_zero]) θ ⟨?_, ?_⟩⟩
  · intro σ hσ
    have h1 := coboundary_sub_mem_vanishing hθ σ hσ
    have h2 := mvKappa_sub_mem_vanishing (A := A) (B := B) (α - β) σ hσ
    have h3 := hα σ hσ
    rw [(coboundary R n).map_sub α] at h1
    simp only [Pi.sub_apply, Pi.zero_apply] at h1 h2 h3 ⊢
    rw [mvCoboundary_apply_of_small _ (Or.inl hσ)]
    linear_combination h3 - h2 - h1
  · intro σ hσ
    have h1 : coboundary R n θ σ = coboundary R n β σ := by
      have := coboundary_sub_mem_vanishing (φ := θ) (ψ := β) (S := B) (fun τ hτ ↦ by
        simp [θ, hτ]) σ hσ
      rwa [Pi.sub_apply, sub_eq_zero] at this
    have h2 := mvKappa_mem_vanishing_right he σ hσ
    have h3 := hβ σ hσ
    simp only [Pi.sub_apply, Pi.zero_apply] at h3 ⊢
    rw [mvCoboundary_apply_of_small _ (Or.inr hσ), h1, h2]
    linear_combination h3

/-- **Exactness at `H^{n+1} A ⊕ H^{n+1} B`**: cocycles `a` of `A` and `b` of `B` with
`a - b = δ γ` on `A ∩ B` glue to a cocycle `c` of `Y` with `c = a` on `A` and `c = b + δ η` on
`B`. -/
theorem exists_glue_succ {n : ℕ} {a b : Simplex Y (n + 1) → R}
    (ha : coboundary R (n + 1) a ∈ vanishing R (n + 2) A)
    (hb : coboundary R (n + 1) b ∈ vanishing R (n + 2) B) (γ : Simplex Y n → R)
    (hab : a - b - coboundary R n γ ∈ vanishing R (n + 1) (A ∩ B)) :
    ∃ c, coboundary R (n + 1) c = 0 ∧ c - a ∈ vanishing R (n + 1) A ∧
      ∃ η, c - b - coboundary R n η ∈ vanishing R (n + 1) B := by
  set Γ := restrictTo R (A ∩ B) n γ
  set θ : Simplex Y (n + 1) → R := fun τ ↦ if range τ ⊆ A then a τ else b τ + coboundary R n Γ τ
  have hθA : θ - a ∈ vanishing R (n + 1) A := fun τ hτ ↦ by simp [θ, hτ]
  have hΓ : coboundary R n Γ - coboundary R n γ ∈ vanishing R (n + 1) (A ∩ B) :=
    coboundary_sub_mem_vanishing (restrictTo_sub_mem_vanishing _ _)
  have hθB : θ - (b + coboundary R n Γ) ∈ vanishing R (n + 1) B := fun τ hτB ↦ by
    by_cases hτA : range τ ⊆ A
    · have h1 := hab τ (subset_inter hτA hτB)
      have h2 := hΓ τ (subset_inter hτA hτB)
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
      simp only [θ, if_pos hτA]
      linear_combination h1 - h2
    · simp [θ, hτA]
  have hδ : coboundary R (n + 1) θ ∈ vanishing R (n + 2) A ⊓ vanishing R (n + 2) B := by
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ (coboundary_sub_mem_vanishing hθA) ha
      rwa [sub_add_cancel] at this
    · have := Submodule.add_mem _ (coboundary_sub_mem_vanishing hθB) hb
      rwa [map_add, coboundary_coboundary, add_zero, sub_add_cancel] at this
  refine ⟨pullback (smallChainMap R {A, B} (n + 1)) θ, coboundary_pullback_eq_zero hA hB hAB hδ,
    ?_, Γ, ?_⟩
  · have := Submodule.add_mem _ (pullback_smallChainMap_sub_mem (A := A) (B := B) θ).1 hθA
    rwa [sub_add_sub_cancel] at this
  · have := Submodule.add_mem _ (pullback_smallChainMap_sub_mem (A := A) (B := B) θ).2 hθB
    rwa [sub_add_sub_cancel, sub_add_eq_sub_sub] at this

/-- **Exactness at `H^0 A ⊕ H^0 B`**: cocycles `a` of `A` and `b` of `B` agreeing on `A ∩ B` glue
to a cocycle `c` of `Y` with `c = a` on `A` and `c = b` on `B`. -/
theorem exists_glue_zero {a b : Simplex Y 0 → R}
    (ha : coboundary R 0 a ∈ vanishing R 1 A) (hb : coboundary R 0 b ∈ vanishing R 1 B)
    (hab : a - b ∈ vanishing R 0 (A ∩ B)) :
    ∃ c, coboundary R 0 c = 0 ∧ c - a ∈ vanishing R 0 A ∧ c - b ∈ vanishing R 0 B := by
  set θ : Simplex Y 0 → R := fun τ ↦ if range τ ⊆ A then a τ else b τ
  have hθA : θ - a ∈ vanishing R 0 A := fun τ hτ ↦ by simp [θ, hτ]
  have hθB : θ - b ∈ vanishing R 0 B := fun τ hτB ↦ by
    by_cases hτA : range τ ⊆ A
    · have h1 := hab τ (subset_inter hτA hτB)
      simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
      simp only [θ, if_pos hτA]
      exact h1
    · simp [θ, hτA]
  have hδ : coboundary R 0 θ ∈ vanishing R 1 A ⊓ vanishing R 1 B := by
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ (coboundary_sub_mem_vanishing hθA) ha
      rwa [sub_add_cancel] at this
    · have := Submodule.add_mem _ (coboundary_sub_mem_vanishing hθB) hb
      rwa [sub_add_cancel] at this
  refine ⟨pullback (smallChainMap R {A, B} 0) θ, coboundary_pullback_eq_zero hA hB hAB hδ, ?_, ?_⟩
  · have := Submodule.add_mem _ (pullback_smallChainMap_sub_mem (A := A) (B := B) θ).1 hθA
    rwa [sub_add_sub_cancel] at this
  · have := Submodule.add_mem _ (pullback_smallChainMap_sub_mem (A := A) (B := B) θ).2 hθB
    rwa [sub_add_sub_cancel] at this

/-- **Exactness at `H^n (A ∩ B)`, one half**: for cocycles `a` of `A` and `b` of `B`,
`mvCoboundary (a - b)` is a coboundary of `Y`. -/
theorem exists_mvCoboundary_sub_eq_coboundary {n : ℕ} {a b : Simplex Y n → R}
    (ha : coboundary R n a ∈ vanishing R (n + 1) A) (hb : coboundary R n b ∈ vanishing R (n + 1) B) :
    ∃ η, mvCoboundary R A B n (a - b) = coboundary R n η := by
  have he : coboundary R n (a - b) ∈ vanishing R (n + 1) (A ∩ B) := by
    rw [map_sub]
    exact Submodule.sub_mem _ (vanishing_anti inter_subset_left ha)
      (vanishing_anti inter_subset_right hb)
  set E := restrictTo R (A ∩ B) n (a - b)
  set θ : Simplex Y n → R := fun τ ↦ if range τ ⊆ A then E τ - a τ else -b τ
  have hθA : θ - (E - a) ∈ vanishing R n A := fun τ hτ ↦ by simp [θ, hτ]
  have hθB : θ + b ∈ vanishing R n B := fun τ hτB ↦ by
    by_cases hτA : range τ ⊆ A
    · simp [θ, E, hτA, hτB, restrictTo_apply]
    · simp [θ, hτA]
  refine ⟨_, exists_eq_coboundary_of_small hA hB hAB (coboundary_mvCoboundary hA hB hAB he) θ
    ⟨fun σ hσ ↦ ?_, fun σ hσ ↦ ?_⟩⟩
  · have h1 := coboundary_sub_mem_vanishing hθA σ hσ
    have h2 := mvKappa_sub_mem_vanishing (A := A) (B := B) (a - b) σ hσ
    have h3 := ha σ hσ
    rw [(coboundary R n).map_sub E] at h1
    simp only [Pi.sub_apply, Pi.zero_apply] at h1 h2 h3 ⊢
    rw [mvCoboundary_apply_of_small _ (Or.inl hσ)]
    linear_combination h2 - h1 + h3
  · have h1 : coboundary R n θ σ + coboundary R n b σ = 0 := by
      have := coboundary_mem_vanishing hθB σ hσ
      rwa [map_add, Pi.add_apply] at this
    have h2 := mvKappa_mem_vanishing_right he σ hσ
    have h3 := hb σ hσ
    simp only [Pi.sub_apply, Pi.zero_apply] at h3 ⊢
    rw [mvCoboundary_apply_of_small _ (Or.inr hσ), h2]
    linear_combination -h1 + h3

/-- The Mayer–Vietoris coboundary of a coboundary of `A ∩ B` is a coboundary of `Y`. -/
theorem exists_mvCoboundary_eq_coboundary {n : ℕ} {e : Simplex Y (n + 1) → R}
    (γ : Simplex Y n → R) (he : e - coboundary R n γ ∈ vanishing R (n + 1) (A ∩ B)) :
    ∃ η, mvCoboundary R A B (n + 1) e = coboundary R (n + 1) η := by
  rw [mvCoboundary_congr he, ← sub_zero (coboundary R n γ)]
  exact exists_mvCoboundary_sub_eq_coboundary hA hB hAB
    (by rw [coboundary_coboundary]; exact Submodule.zero_mem _)
    (by rw [map_zero]; exact Submodule.zero_mem _)

end mayerVietoris

end SingularCochain

end MMP
