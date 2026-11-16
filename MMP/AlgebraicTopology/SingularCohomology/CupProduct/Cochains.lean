module

public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains

/-!
# The cup product of singular cochains

A singular `p`-cochain of a space `Y` with coefficients in a commutative ring `R` is a function
on singular `p`-simplices; its coboundary is `(δ φ) σ = ∑ i, (-1) ^ i φ (σ ∘ δⁱ)`. The cup
product of a `p`-cochain `φ` and a `q`-cochain `ψ` is the `(p + q)`-cochain
`(φ ∪ ψ) σ = φ (σ ⌊ [0, …, p]) * ψ (σ ⌊ [p, …, p + q])` (front and back faces), and the
Leibniz rule `δ (φ ∪ ψ) = δ φ ∪ ψ + (-1) ^ p φ ∪ δ ψ` holds (Dold, VII.8; Hatcher, §3.2).

For subsets `A, B ⊆ Y`, a cochain vanishing on the simplices of `A`, cupped with one vanishing
on the simplices of `B`, vanishes on the `{A, B}`-small chains. Pulling back along the
small-chains map `ρ` of `MMP.SingularChain.smallChainMap`, for `A`, `B` open,
gives a cochain vanishing on the simplices of `A ∪ B`. On the relative cohomology
`H^p(Y, A) = Z^p(Y, A) / B^p(Y, A)` this defines the relative cup product
`H^p(Y, A) × H^q(Y, B) → H^{p+q}(Y, A ∪ B)`.

## Main definitions

* `MMP.SingularCochain.coboundary`: `δ`.
* `MMP.SingularCochain.cup`: the cup product of cochains.
* `MMP.SingularCochain.relCohomology R Y A p`: `Z^p(Y, A) / B^p(Y, A)`.
* `MMP.SingularCochain.relCup`: the relative cup product on it.

## Main results

* `MMP.SingularCochain.coboundary_cup`: the Leibniz rule.
* `MMP.SingularCochain.coboundary_coboundary`: `δ ∘ δ = 0`.

## References

* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.8.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.2.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularCochain

open SingularChain

variable (R : Type*) [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The simplicial operator `Δᵃ → Δᵇ` induced by a map of vertices. -/
def smap {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) :
    C(stdSimplex ℝ (Fin (a + 1)), stdSimplex ℝ (Fin (b + 1))) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map _⟩

/-- The simplicial operator of a composite of vertex maps is the composite of the operators. -/
lemma smap_comp {a b c : ℕ} (f : Fin (b + 1) → Fin (c + 1)) (g : Fin (a + 1) → Fin (b + 1)) :
    (smap f).comp (smap g) = smap (f ∘ g) := by
  ext1 t; exact stdSimplex.map_comp_apply g f t

/-- `(σ ∘ smap f) ∘ smap g = σ ∘ smap (f ∘ g)` for a singular simplex `σ`. -/
lemma comp_smap_comp {a b c : ℕ} (σ : Simplex Y c) (f : Fin (b + 1) → Fin (c + 1))
    (g : Fin (a + 1) → Fin (b + 1)) : (σ.comp (smap f)).comp (smap g) = σ.comp (smap (f ∘ g)) := by
  rw [ContinuousMap.comp_assoc, smap_comp]

/-- The face map `Fin (n + 1) → Fin (n + 2)` omitting `i`, for `i : ℕ`. -/
def skip (n i : ℕ) : Fin (n + 1) → Fin (n + 2) := fun j ↦
  if (j : ℕ) < i then ⟨j, by omega⟩ else ⟨j + 1, by omega⟩

/-- The `i`-th face map is the simplicial operator of the vertex map `skip n i`. -/
lemma face_eq_smap (n : ℕ) (i : Fin (n + 2)) : face n i = smap (skip n i) := by
  congr 1

/-- The front vertices `j ↦ j`, `Fin (a + 1) → Fin (b + 1)`, `a ≤ b`. -/
def front (a b : ℕ) (h : a ≤ b) : Fin (a + 1) → Fin (b + 1) := fun j ↦ ⟨j, by omega⟩

/-- The back vertices `j ↦ j + s`, `Fin (a + 1) → Fin (b + 1)`, `a + s ≤ b`. -/
def back (a b s : ℕ) (h : a + s ≤ b) : Fin (a + 1) → Fin (b + 1) := fun j ↦ ⟨j + s, by omega⟩

/-- `skip n i j` is `j` if `j < i` and `j + 1` otherwise. -/
lemma skip_val (n i : ℕ) (j : Fin (n + 1)) :
    (skip n i j : ℕ) = if (j : ℕ) < i then (j : ℕ) else (j : ℕ) + 1 := by
  unfold skip; split_ifs <;> rfl

/-- `front a b h j` is `j`. -/
lemma front_val (a b : ℕ) (h : a ≤ b) (j : Fin (a + 1)) : (front a b h j : ℕ) = j := rfl

/-- `back a b s h j` is `j + s`. -/
lemma back_val (a b s : ℕ) (h : a + s ≤ b) (j : Fin (a + 1)) : (back a b s h j : ℕ) = j + s := rfl

/-- The coboundary `(δ φ) σ = ∑ i, (-1) ^ i φ (σ ∘ δⁱ)`. -/
def coboundary (n : ℕ) : (Simplex Y n → R) →ₗ[R] (Simplex Y (n + 1) → R) where
  toFun φ σ := ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * φ (σ.comp (face n i))
  map_add' φ ψ := by ext σ; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r φ := by ext σ; simp [Finset.mul_sum, mul_left_comm]

variable {R}

/-- The evaluation of a cochain on a chain. -/
abbrev eval {n : ℕ} (φ : Simplex Y n → R) : Chain R Y n →ₗ[R] R := linearCombination R φ

/-- `(δ φ) σ = ∑ i, (-1) ^ i φ (σ ∘ δⁱ)`. -/
lemma coboundary_apply (n : ℕ) (φ : Simplex Y n → R) (σ : Simplex Y (n + 1)) :
    coboundary R n φ σ = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * φ (σ.comp (face n i)) := rfl

/-- The coboundary is adjoint to the boundary: `(δ φ)(c) = φ(∂ c)`. -/
lemma eval_coboundary (n : ℕ) (φ : Simplex Y n → R) (c : Chain R Y (n + 1)) :
    eval (coboundary R n φ) c = eval φ (bd R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, bd_single,
      map_sum]
    simp [coboundary_apply, smul_eq_mul]

/-- `δ ∘ δ = 0`. -/
lemma coboundary_coboundary (n : ℕ) (φ : Simplex Y n → R) :
    coboundary R (n + 1) (coboundary R n φ) = 0 := by
  ext σ
  have h1 := eval_coboundary (n + 1) (coboundary R n φ) (single σ 1)
  have h2 := eval_coboundary n φ (bd R (n + 1) (single σ 1))
  rw [bd_bd, map_zero] at h2
  simpa [h2] using h1

/-- The pull-back of a cochain along a chain map given in degree `n`. -/
def pullback {n : ℕ} (ρ : Chain R Y n →ₗ[R] Chain R Y n) :
    (Simplex Y n → R) →ₗ[R] (Simplex Y n → R) where
  toFun φ σ := eval φ (ρ (single σ 1))
  map_add' φ ψ := by ext σ; simp [linearCombination_apply, mul_add, Finsupp.sum_add]
  map_smul' r φ := by ext σ; simp [linearCombination_apply, Finsupp.mul_sum, mul_left_comm]

/-- `(ρ^* φ)(c) = φ(ρ c)`. -/
lemma eval_pullback {n : ℕ} (ρ : Chain R Y n →ₗ[R] Chain R Y n) (φ : Simplex Y n → R)
    (c : Chain R Y n) : eval (pullback ρ φ) c = eval φ (ρ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul]
    simp [pullback]

/-- The coboundary commutes with pulling back along the small-chains map `ρ`. -/
lemma coboundary_pullback_smallChainMap (𝒰 : Set (Set Y)) (n : ℕ) (φ : Simplex Y n → R) :
    coboundary R n (pullback (smallChainMap R 𝒰 n) φ) =
      pullback (smallChainMap R 𝒰 (n + 1)) (coboundary R n φ) := by
  ext σ
  have h1 := eval_coboundary n (pullback (smallChainMap R 𝒰 n) φ) (single σ 1)
  rw [eval_pullback, ← bd_smallChainMap, ← eval_coboundary, ← eval_pullback] at h1
  simpa using h1

section cup

/-- The cup product `(φ ∪ ψ) σ = φ (front face) * ψ (back face)` of a `p`-cochain and a
`q`-cochain, a cochain of degree `n = p + q`. -/
def cup (p q n : ℕ) (h : p + q = n) :
    (Simplex Y p → R) →ₗ[R] (Simplex Y q → R) →ₗ[R] (Simplex Y n → R) :=
  LinearMap.mk₂ R (fun φ ψ σ ↦ φ (σ.comp (smap (front p n (by omega)))) *
      ψ (σ.comp (smap (back q n p (by omega)))))
    (fun _ _ _ ↦ by ext; simp [add_mul]) (fun _ _ _ ↦ by ext; simp [mul_assoc])
    (fun _ _ _ ↦ by ext; simp [mul_add]) (fun _ _ _ ↦ by ext; simp [mul_left_comm])

/-- `(φ ∪ ψ) σ = φ (σ ⌊ [0, …, p]) * ψ (σ ⌊ [p, …, n])`. -/
lemma cup_apply (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (ψ : Simplex Y q → R)
    (σ : Simplex Y n) :
    cup p q n h φ ψ σ = φ (σ.comp (smap (front p n (by omega)))) *
      ψ (σ.comp (smap (back q n p (by omega)))) := rfl

private lemma coboundary_apply' (n : ℕ) (φ : Simplex Y n → R) (σ : Simplex Y (n + 1)) :
    coboundary R n φ σ = ∑ i ∈ Finset.range (n + 2),
      (-1 : R) ^ i * φ (σ.comp (smap (skip n i))) := by
  rw [coboundary_apply, ← Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : R) ^ i *
    φ (σ.comp (smap (skip n i))))]
  simp only [face_eq_smap]

/-- The Leibniz rule `δ (φ ∪ ψ) = δ φ ∪ ψ + (-1) ^ p φ ∪ δ ψ`. -/
lemma coboundary_cup (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (ψ : Simplex Y q → R) :
    coboundary R n (cup p q n h φ ψ) =
      cup (p + 1) q (n + 1) (by omega) (coboundary R p φ) ψ +
        (-1 : R) ^ p • cup p (q + 1) (n + 1) (by omega) φ (coboundary R q ψ) := by
  ext σ
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [cup_apply]
  simp only [coboundary_apply', comp_smap_comp]
  simp only [cup_apply, comp_smap_comp]
  simp only [Finset.sum_mul, Finset.mul_sum]
  have eA : ∀ f : ℕ → R, ∑ i ∈ Finset.range (p + 2), f i = ∑ i ∈ Finset.range (p + 1), f i +
      f (p + 1) := fun f ↦ Finset.sum_range_succ f (p + 1)
  have eB : ∀ f : ℕ → R, ∑ i ∈ Finset.range (q + 2), f i = ∑ k ∈ Finset.range (q + 1), f (k + 1) +
      f 0 := fun f ↦ Finset.sum_range_succ' f (q + 1)
  rw [eA, eB, ← Finset.sum_range_add_sum_Ico _ (show p + 1 ≤ n + 2 by omega),
    Finset.sum_Ico_eq_sum_range, show n + 2 - (p + 1) = q + 1 by omega]
  have hA : ∀ i ∈ Finset.range (p + 1),
      (-1 : R) ^ i * (φ (σ.comp (smap (skip n i ∘ front p n (by omega)))) *
        ψ (σ.comp (smap (skip n i ∘ back q n p (by omega))))) =
      (-1 : R) ^ i * φ (σ.comp (smap (front (p + 1) (n + 1) (by omega) ∘ skip p i))) *
        ψ (σ.comp (smap (back q (n + 1) (p + 1) (by omega)))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : skip n i ∘ front p n (by omega) = front (p + 1) (n + 1) (by omega) ∘ skip p i := by
      funext j; apply Fin.ext; have := j.isLt
      simp only [Function.comp_apply, skip_val, front_val, back_val]
      by_cases h1 : (j : ℕ) < i <;> simp only [h1, if_true, if_false] <;> omega
    have e2 : skip n i ∘ back q n p (by omega) = back q (n + 1) (p + 1) (by omega) := by
      funext j; apply Fin.ext; have := j.isLt
      simp only [Function.comp_apply, skip_val, front_val, back_val]
      by_cases h1 : (j : ℕ) + p < i <;> simp only [h1, if_true, if_false] <;> omega
    rw [e1, e2, mul_assoc]
  have hB : ∀ k ∈ Finset.range (q + 1),
      (-1 : R) ^ (p + 1 + k) * (φ (σ.comp (smap (skip n (p + 1 + k) ∘ front p n (by omega)))) *
        ψ (σ.comp (smap (skip n (p + 1 + k) ∘ back q n p (by omega))))) =
      (-1 : R) ^ p * (φ (σ.comp (smap (front p (n + 1) (by omega)))) *
        ((-1 : R) ^ (k + 1) * ψ (σ.comp (smap (back (q + 1) (n + 1) p (by omega) ∘
          skip q (k + 1)))))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e1 : skip n (p + 1 + k) ∘ front p n (by omega) = front p (n + 1) (by omega) := by
      funext j; apply Fin.ext; have := j.isLt
      simp only [Function.comp_apply, skip_val, front_val, back_val]
      by_cases h1 : (j : ℕ) < p + 1 + k <;> simp only [h1, if_true, if_false] <;> omega
    have e2 : skip n (p + 1 + k) ∘ back q n p (by omega) =
        back (q + 1) (n + 1) p (by omega) ∘ skip q (k + 1) := by
      funext j; apply Fin.ext; have := j.isLt
      simp only [Function.comp_apply, skip_val, front_val, back_val]
      by_cases h1 : (j : ℕ) + p < p + 1 + k <;> by_cases h2 : (j : ℕ) < k + 1 <;>
        simp only [h1, h2, if_true, if_false] <;> omega
    rw [e1, e2]
    ring
  have hlast : front (p + 1) (n + 1) (by omega) ∘ skip p (p + 1) = front p (n + 1) (by omega) := by
    funext j; apply Fin.ext; have := j.isLt
    simp only [Function.comp_apply, skip_val, front_val, back_val]
    by_cases h1 : (j : ℕ) < p + 1 <;> simp only [h1, if_true, if_false] <;> omega
  have hfirst : back (q + 1) (n + 1) p (by omega) ∘ skip q 0 = back q (n + 1) (p + 1) (by omega) := by
    funext j; apply Fin.ext; have := j.isLt
    simp only [Function.comp_apply, skip_val, front_val, back_val]
    by_cases h1 : (j : ℕ) < 0 <;> simp only [h1, if_true, if_false] <;> omega
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, hlast, hfirst, pow_succ, pow_zero]
  ring

end cup

section relative

variable (R) in
/-- Cochains vanishing on the simplices of `A`. -/
def vanishing (n : ℕ) (A : Set Y) : Submodule R (Simplex Y n → R) where
  carrier := {φ | ∀ σ : Simplex Y n, range σ ⊆ A → φ σ = 0}
  add_mem' ha hb σ hσ := by simp [ha σ hσ, hb σ hσ]
  zero_mem' _ _ := rfl
  smul_mem' r φ hφ σ hσ := by simp [hφ σ hσ]

/-- A simplex with image in `A`, precomposed with any map of simplices, has image in `A`. -/
lemma range_comp_subset {a b : ℕ} {σ : Simplex Y b} {A : Set Y} (hσ : range σ ⊆ A)
    (f : C(stdSimplex ℝ (Fin (a + 1)), stdSimplex ℝ (Fin (b + 1)))) : range (σ.comp f) ⊆ A :=
  fun _ ⟨t, ht⟩ ↦ hσ ⟨f t, ht⟩

/-- The coboundary of a cochain vanishing on the simplices of `A` vanishes on them. -/
lemma coboundary_mem_vanishing {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) : coboundary R n φ ∈ vanishing R (n + 1) A := fun σ hσ ↦ by
  rw [coboundary_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hφ _ (range_comp_subset hσ _), mul_zero]

/-- A cochain vanishing on the simplices of `A` and of `B` vanishes on `{A, B}`-small chains. -/
lemma eval_eq_zero_of_mem_small {n : ℕ} {A B : Set Y} {χ : Simplex Y n → R}
    (hχ : χ ∈ vanishing R n A ⊓ vanishing R n B) {c : Chain R Y n}
    (hc : c ∈ small R n {A, B}) : eval χ c = 0 := by
  have := VertexChain.mem_of_mem_supported (eval χ) ⊥ (s := {σ | ∃ U ∈ ({A, B} : Set (Set Y)),
    range σ ⊆ U}) (fun σ hσ ↦ by
      obtain ⟨U, hU, hσU⟩ := hσ
      rw [Submodule.mem_bot, eval, linearCombination_single, one_smul]
      rcases hU with rfl | rfl
      · exact hχ.1 σ hσU
      · exact hχ.2 σ hσU) hc
  simpa using this

/-- The cup product of a cochain vanishing on the simplices of `A` and one vanishing on the
simplices of `B` vanishes on the simplices of `A` and on those of `B`. -/
lemma cup_mem_vanishing {p q n : ℕ} (h : p + q = n) {A B : Set Y} {φ : Simplex Y p → R}
    (hφ : φ ∈ vanishing R p A) {ψ : Simplex Y q → R} (hψ : ψ ∈ vanishing R q B) :
    cup p q n h φ ψ ∈ vanishing R n A ⊓ vanishing R n B :=
  ⟨fun σ hσ ↦ by rw [cup_apply, hφ _ (range_comp_subset hσ _), zero_mul],
    fun σ hσ ↦ by rw [cup_apply, hψ _ (range_comp_subset hσ _), mul_zero]⟩

/-- Pulling back along `ρ` turns a cochain vanishing on `{A, B}`-small chains into one vanishing
on the simplices of `A ∪ B`, for `A`, `B` open. -/
lemma pullback_mem_vanishing {n : ℕ} {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    {χ : Simplex Y n → R} (hχ : χ ∈ vanishing R n A ⊓ vanishing R n B) :
    pullback (smallChainMap R {A, B} n) χ ∈ vanishing R n (A ∪ B) := fun σ hσ ↦ by
  have h𝒰 : ∀ U ∈ ({A, B} : Set (Set Y)), IsOpen U := by
    rintro U (rfl | rfl) <;> assumption
  exact eval_eq_zero_of_mem_small hχ (smallChainMap_single_mem_small h𝒰 n
    (by rwa [sUnion_insert, sUnion_singleton]))

variable (R) in
/-- Relative cocycles `Z^n(Y, A)`. -/
def relCocycles (A : Set Y) (n : ℕ) : Submodule R (Simplex Y n → R) :=
  vanishing R n A ⊓ LinearMap.ker (coboundary R n)

variable (R) in
/-- Relative coboundaries `B^n(Y, A)`: coboundaries of cochains vanishing on `A`. -/
def relCoboundaries (A : Set Y) : ∀ n : ℕ, Submodule R (Simplex Y n → R)
  | 0 => ⊥
  | n + 1 => (vanishing R n A).map (coboundary R n)

/-- `B^n(Y, A) ≤ Z^n(Y, A)`. -/
lemma relCoboundaries_le (A : Set Y) (n : ℕ) : relCoboundaries R A n ≤ relCocycles R A n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨coboundary_mem_vanishing hα, coboundary_coboundary n α⟩

variable (R) in
/-- The relative cohomology `H^n(Y, A) = Z^n(Y, A) / B^n(Y, A)` of singular cochains. -/
abbrev relCohomology (A : Set Y) (n : ℕ) : Type _ :=
  relCocycles R A n ⧸ (relCoboundaries R A n).comap (relCocycles R A n).subtype

/-- The cochain-level relative cup product `(φ, ψ) ↦ ρ^* (φ ∪ ψ)`. -/
def relCupCochain {A B : Set Y} (p q n : ℕ) (h : p + q = n) :
    (Simplex Y p → R) →ₗ[R] (Simplex Y q → R) →ₗ[R] (Simplex Y n → R) :=
  LinearMap.compr₂ (cup p q n h) (pullback (smallChainMap R {A, B} n))

/-- For `A`, `B` open, the relative cup product of cocycles in `Z^p(Y, A)` and `Z^q(Y, B)` lies
in `Z^n(Y, A ∪ B)`. -/
lemma relCupCochain_mem_relCocycles {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R} (hφ : φ ∈ relCocycles R A p)
    {ψ : Simplex Y q → R} (hψ : ψ ∈ relCocycles R B q) :
    relCupCochain (A := A) (B := B) p q n h φ ψ ∈ relCocycles R (A ∪ B) n := by
  refine ⟨pullback_mem_vanishing hA hB (cup_mem_vanishing h hφ.1 hψ.1), ?_⟩
  have h1 : coboundary R p φ = 0 := hφ.2
  have h2 : coboundary R q ψ = 0 := hψ.2
  change coboundary R n (pullback _ (cup p q n h φ ψ)) = 0
  rw [coboundary_pullback_smallChainMap, coboundary_cup, h1, h2]
  simp

/-- For `A`, `B` open, the relative cup product of a coboundary in `B^p(Y, A)` and a cocycle in
`Z^q(Y, B)` lies in `B^n(Y, A ∪ B)`. -/
lemma relCupCochain_mem_relCoboundaries_left {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R} (hφ : φ ∈ relCoboundaries R A p)
    {ψ : Simplex Y q → R} (hψ : ψ ∈ relCocycles R B q) :
    relCupCochain (A := A) (B := B) p q n h φ ψ ∈ relCoboundaries R (A ∪ B) n := by
  cases p with
  | zero =>
    rw [show φ = 0 from hφ]; simp [relCoboundaries]
  | succ p =>
    obtain rfl : n = p + q + 1 := by omega
    obtain ⟨α, hα, rfl⟩ := hφ
    have h2 : coboundary R q ψ = 0 := hψ.2
    refine ⟨relCupCochain (A := A) (B := B) p q (p + q) rfl α ψ,
      pullback_mem_vanishing hA hB (cup_mem_vanishing rfl hα hψ.1), ?_⟩
    change coboundary R (p + q) (pullback _ (cup p q (p + q) rfl α ψ)) = _
    rw [coboundary_pullback_smallChainMap, coboundary_cup, h2]
    simp [relCupCochain]

/-- For `A`, `B` open, the relative cup product of a cocycle in `Z^p(Y, A)` and a coboundary in
`B^q(Y, B)` lies in `B^n(Y, A ∪ B)`. -/
lemma relCupCochain_mem_relCoboundaries_right {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (p q n : ℕ) (h : p + q = n) {φ : Simplex Y p → R} (hφ : φ ∈ relCocycles R A p)
    {ψ : Simplex Y q → R} (hψ : ψ ∈ relCoboundaries R B q) :
    relCupCochain (A := A) (B := B) p q n h φ ψ ∈ relCoboundaries R (A ∪ B) n := by
  cases q with
  | zero =>
    rw [show ψ = 0 from hψ]; simp [relCoboundaries]
  | succ q =>
    obtain rfl : n = p + q + 1 := by omega
    obtain ⟨β, hβ, rfl⟩ := hψ
    have h1 : coboundary R p φ = 0 := hφ.2
    refine ⟨(-1 : R) ^ p • relCupCochain (A := A) (B := B) p q (p + q) rfl φ β,
      Submodule.smul_mem _ _ (pullback_mem_vanishing hA hB (cup_mem_vanishing rfl hφ.1 hβ)), ?_⟩
    change coboundary R (p + q) ((-1 : R) ^ p • pullback _ (cup p q (p + q) rfl φ β)) = _
    rw [map_smul, coboundary_pullback_smallChainMap, coboundary_cup, h1]
    simp only [map_zero, LinearMap.zero_apply, zero_add, map_smul, smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    rfl

/-- The relative cup product on relative cocycles. -/
def relCupCocycles {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] relCocycles R B q →ₗ[R] relCocycles R (A ∪ B) n :=
  LinearMap.mk₂ R (fun (φ : relCocycles R A p) (ψ : relCocycles R B q) ↦
      (⟨relCupCochain (A := A) (B := B) p q n h (φ : Simplex Y p → R) (ψ : Simplex Y q → R),
        relCupCochain_mem_relCocycles hA hB p q n h φ.2 ψ.2⟩ : relCocycles R (A ∪ B) n))
    (fun φ φ' ψ ↦ by ext1; exact (relCupCochain (A := A) (B := B) p q n h).map_add₂ _ _ _)
    (fun r φ ψ ↦ by ext1; exact (relCupCochain (A := A) (B := B) p q n h).map_smul₂ _ _ _)
    (fun φ ψ ψ' ↦ by ext1; exact map_add (relCupCochain (A := A) (B := B) p q n h _) _ _)
    (fun r φ ψ ↦ by ext1; exact map_smul (relCupCochain (A := A) (B := B) p q n h _) _ _)

/-- The relative cup product with a relative cocycle, on relative cohomology classes. -/
def relCupLeft {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ) (h : p + q = n) :
    relCocycles R A p →ₗ[R] relCohomology R B q →ₗ[R] relCohomology R (A ∪ B) n :=
  (Submodule.liftQ _ ((relCupCocycles hA hB p q n h).compr₂ (Submodule.mkQ _)).flip
    (fun ψ hψ ↦ by
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun φ ↦ ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact relCupCochain_mem_relCoboundaries_right hA hB p q n h φ.2 hψ)).flip

/-- `φ ∪ [ψ] = [φ ∪ ψ]` for relative cocycles `φ`, `ψ`. -/
lemma relCupLeft_mk {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (ψ : relCocycles R B q) :
    relCupLeft hA hB p q n h φ (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk (relCupCocycles hA hB p q n h φ ψ) :=
  rfl

/-- The relative cup product `H^p(Y, A) × H^q(Y, B) → H^n(Y, A ∪ B)`, `n = p + q`, for `A`, `B`
open in `Y`: `[φ] ∪ [ψ] = [ρ^* (φ ∪ ψ)]`. -/
def relCup {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ) (h : p + q = n) :
    relCohomology R A p →ₗ[R] relCohomology R B q →ₗ[R] relCohomology R (A ∪ B) n :=
  Submodule.liftQ _ (relCupLeft hA hB p q n h) (fun φ hφ ↦ by
    rw [LinearMap.mem_ker]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun ψ ↦ ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      relCupLeft_mk, Submodule.Quotient.mk_eq_zero]
    exact relCupCochain_mem_relCoboundaries_left hA hB p q n h hφ ψ.2)

/-- `[φ] ∪ [ψ] = [φ ∪ ψ]` for relative cocycles `φ`, `ψ`. -/
lemma relCup_mk {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (p q n : ℕ) (h : p + q = n)
    (φ : relCocycles R A p) (ψ : relCocycles R B q) :
    relCup (R := R) hA hB p q n h (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk (relCupCocycles hA hB p q n h φ ψ) :=
  rfl

end relative

end SingularCochain

end MMP
