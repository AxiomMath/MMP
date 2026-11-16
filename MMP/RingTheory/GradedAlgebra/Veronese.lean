module

public import MMP.Attr
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Veronese subalgebras of a graded algebra

Let `A` be a commutative semiring and `R = ⨁_{m ≥ 0} R_m` a commutative `ℕ`-graded
`A`-algebra, with grading `𝒜 : ℕ → Submodule A R`. For an integer `d ≥ 1` the `d`-th
Veronese subalgebra of `R` is `R^(d) = ⨁_{m ≥ 0} R_{dm}`, with the multiplication of `R`.

We realise `R^(d)` as an `A`-subalgebra of `R`: the elements of `R` whose homogeneous
components in degrees not divisible by `d` vanish. It is graded by `m ↦ R_{dm}`, and for
`d ≥ 1` this grading makes it a graded `A`-algebra, i.e. `R^(d)` is the internal direct sum
of the `R_{dm}`.

## Main definitions

* `MMP.Fourfold.veroneseSubalgebra 𝒜 d`: the Veronese subalgebra `R^(d)`.
* `MMP.Fourfold.veroneseGrade 𝒜 d m`: its degree-`m` part, the elements lying in `R_{dm}`.
* `MMP.Fourfold.veroneseGrade.linearEquiv`: `R^(d)_m ≃ₗ[A] R_{dm}`.
* The instance `GradedAlgebra (veroneseGrade 𝒜 d)` for `d ≠ 0`.

## Main results

* `MMP.Fourfold.mem_veroneseSubalgebra_iff`: membership in `R^(d)`.
* `MMP.Fourfold.veroneseSubalgebra_toSubmodule_eq_iSup`: the underlying submodule of `R^(d)`
  is `⨆ m, R_{dm}`.
* `MMP.Fourfold.veroneseGrade_isInternal`: for `d ≥ 1`, `R^(d) = ⨁_m R_{dm}` internally.
* `MMP.Fourfold.coe_decompose_veroneseGrade`: the degree-`m` component of `x ∈ R^(d)` is the
  degree-`dm` component of `x` in `R`.

## Implementation notes

The definition makes sense for `d = 0`, where it is the degree-zero part `R_0`; the
hypothesis `d ≥ 1` (as `0 < d` or `[NeZero d]`) enters only where the grading by
`m ↦ R_{dm}` is shown to be a direct sum decomposition.

StacksDraft has the Veronese subring of a graded commutative ring
(`Stacks.Veronese.veroneseSubring`, `Stacks.Veronese.veroneseGrading`); the source needs the
`A`-algebra structure over a base `A` and graded semirings, which it does not provide.
-/

@[expose] public noncomputable section

namespace MMP.Fourfold

open DirectSum

variable {A R : Type*} [CommSemiring A] [CommSemiring R] [Algebra A R]
variable (𝒜 : ℕ → Submodule A R) [GradedAlgebra 𝒜]

/-- The `d`-th Veronese subalgebra `R^(d) = ⨁_{m ≥ 0} R_{dm}` of an `ℕ`-graded `A`-algebra
`R`: the elements of `R` all of whose homogeneous components in degrees not divisible by `d`
vanish. -/
@[mmp "def_fourfold_veronese"]
def veroneseSubalgebra (d : ℕ) : Subalgebra A R where
  carrier := {x | ∀ n, ¬ d ∣ n → (decompose 𝒜 x n : R) = 0}
  zero_mem' _ _ := by simp
  add_mem' := by
    intro x y hx hy n hn
    simp [decompose_add, hx n hn, hy n hn]
  mul_mem' := by
    classical
    intro x y hx hy n hn
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [← sum_support_decompose 𝒜 x, Finset.sum_mul, decompose_sum, DFinsupp.finsetSum_apply,
      Submodule.coe_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coe_decompose_mul_of_left_mem 𝒜 n (decompose 𝒜 x i).2]
    split_ifs with hin
    · by_cases hi : d ∣ i
      · rw [hy (n - i) fun h => hn (by simpa [Nat.sub_add_cancel hin] using Nat.dvd_add h hi),
          mul_zero]
      · rw [hx i hi, zero_mul]
    · rfl
  algebraMap_mem' a n hn :=
    decompose_of_mem_ne 𝒜 (SetLike.algebraMap_mem_graded 𝒜 a) fun h => hn (h ▸ dvd_zero d)

variable {𝒜} in
/-- An element `x` lies in `R^(d)` if and only if its homogeneous components in all degrees
not divisible by `d` vanish. -/
theorem mem_veroneseSubalgebra_iff {d : ℕ} {x : R} :
    x ∈ veroneseSubalgebra 𝒜 d ↔ ∀ n, ¬ d ∣ n → (decompose 𝒜 x n : R) = 0 :=
  Iff.rfl

variable {𝒜} in
/-- A homogeneous element of degree `d * m` lies in the Veronese subalgebra `R^(d)`. -/
theorem mem_veroneseSubalgebra_of_mem {d m : ℕ} {x : R} (hx : x ∈ 𝒜 (d * m)) :
    x ∈ veroneseSubalgebra 𝒜 d := fun _ hn =>
  decompose_of_mem_ne 𝒜 hx fun h => hn (h ▸ dvd_mul_right d m)

variable {𝒜} in
/-- The homogeneous components of an element of `R^(d)` lie in `R^(d)`. -/
theorem decompose_mem_veroneseSubalgebra {d : ℕ} {x : R} (hx : x ∈ veroneseSubalgebra 𝒜 d)
    (n : ℕ) : (decompose 𝒜 x n : R) ∈ veroneseSubalgebra 𝒜 d := by
  by_cases hn : d ∣ n
  · obtain ⟨m, rfl⟩ := hn
    exact mem_veroneseSubalgebra_of_mem (decompose 𝒜 x (d * m)).2
  · rw [hx n hn]
    exact zero_mem _

/-- The Veronese subalgebra is, as a submodule, `⨆ m, R_{dm}`. -/
theorem veroneseSubalgebra_toSubmodule_eq_iSup (d : ℕ) :
    Subalgebra.toSubmodule (veroneseSubalgebra 𝒜 d) = ⨆ m, 𝒜 (d * m) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← sum_support_decompose 𝒜 x]
    refine Submodule.sum_mem _ fun n _ => ?_
    by_cases hn : d ∣ n
    · obtain ⟨m, rfl⟩ := hn
      exact Submodule.mem_iSup_of_mem m (decompose 𝒜 x (d * m)).2
    · rw [hx n hn]
      exact zero_mem _
  · exact iSup_le fun m x hx => mem_veroneseSubalgebra_of_mem hx

/-- The degree-`m` part of the Veronese subalgebra `R^(d)`: its elements lying in `R_{dm}`. -/
@[mmp "def_fourfold_veronese"]
def veroneseGrade (d m : ℕ) : Submodule A (veroneseSubalgebra 𝒜 d) :=
  (𝒜 (d * m)).comap (veroneseSubalgebra 𝒜 d).val.toLinearMap

variable {𝒜} in
/-- An element of `R^(d)` lies in its degree-`m` part if and only if it lies in `R_{dm}`. -/
@[simp]
theorem mem_veroneseGrade {d m : ℕ} {x : veroneseSubalgebra 𝒜 d} :
    x ∈ veroneseGrade 𝒜 d m ↔ (x : R) ∈ 𝒜 (d * m) :=
  Iff.rfl

/-- The degree-`m` part of `R^(d)` is `R_{dm}`. -/
def veroneseGrade.linearEquiv (d m : ℕ) : veroneseGrade 𝒜 d m ≃ₗ[A] 𝒜 (d * m) where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨⟨y.1, mem_veroneseSubalgebra_of_mem y.2⟩, y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {𝒜} in
/-- The isomorphism `R^(d)_m ≃ₗ[A] R_{dm}` does not change the underlying element of `R`. -/
@[simp]
theorem veroneseGrade.coe_linearEquiv_apply {d m : ℕ} (x : veroneseGrade 𝒜 d m) :
    (veroneseGrade.linearEquiv 𝒜 d m x : R) = x :=
  rfl

variable {𝒜} in
/-- The inverse isomorphism `R_{dm} ≃ₗ[A] R^(d)_m` does not change the underlying element
of `R`. -/
@[simp]
theorem veroneseGrade.coe_linearEquiv_symm_apply {d m : ℕ} (y : 𝒜 (d * m)) :
    (((veroneseGrade.linearEquiv 𝒜 d m).symm y : veroneseSubalgebra 𝒜 d) : R) = y :=
  rfl

/-- The grading `m ↦ R_{dm}` of `R^(d)` is multiplicative: `1` has degree `0`, and the
product of elements of degrees `i` and `j` has degree `i + j`. -/
instance veroneseGrade.gradedMonoid (d : ℕ) : SetLike.GradedMonoid (veroneseGrade 𝒜 d) where
  one_mem := by
    rw [mem_veroneseGrade, mul_zero]
    exact SetLike.GradedOne.one_mem
  mul_mem i j x y hx hy := by
    rw [mem_veroneseGrade, mul_add]
    exact SetLike.GradedMul.mul_mem hx hy

variable {𝒜} in
/-- The degree-`d * m₀` component in `R` of the element of `R^(d)` represented by
`z : ⨁ m, R^(d)_m` is the `m₀`-th coordinate of `z`. -/
theorem coe_decompose_coeAddMonoidHom_veroneseGrade {d : ℕ} (hd : 0 < d)
    (z : ⨁ m, veroneseGrade 𝒜 d m) (m₀ : ℕ) :
    (decompose 𝒜 ((DirectSum.coeAddMonoidHom (veroneseGrade 𝒜 d) z : veroneseSubalgebra 𝒜 d) :
      R) (d * m₀) : R) = ((z m₀ : veroneseSubalgebra 𝒜 d) : R) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | of m y =>
    rw [coeAddMonoidHom_of]
    obtain rfl | h := eq_or_ne m m₀
    · rw [of_eq_same]
      exact decompose_of_mem_same 𝒜 y.2
    · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
      exact decompose_of_mem_ne 𝒜 y.2 fun h' => h (Nat.eq_of_mul_eq_mul_left hd h')
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, Subalgebra.coe_add, decompose_add, add_apply, Submodule.coe_add, h₁, h₂]

/-- For `d ≥ 1`, the Veronese subalgebra `R^(d)` is the internal direct sum of the `R_{dm}`. -/
@[mmp "def_fourfold_veronese"]
theorem veroneseGrade_isInternal {d : ℕ} (hd : 0 < d) :
    DirectSum.IsInternal (veroneseGrade 𝒜 d) := by
  classical
  constructor
  · intro z₁ z₂ h
    ext m₀ : 1
    have h' := congrArg (fun v : veroneseSubalgebra 𝒜 d => (decompose 𝒜 (v : R) (d * m₀) : R)) h
    simp only [coe_decompose_coeAddMonoidHom_veroneseGrade hd] at h'
    exact Subtype.ext (Subtype.ext h')
  · rintro ⟨x, hx⟩
    let z : ⨁ m, veroneseGrade 𝒜 d m :=
      ∑ n ∈ (decompose 𝒜 x).support.filter (d ∣ ·),
        DirectSum.of (fun m => veroneseGrade 𝒜 d m) (n / d)
          ⟨⟨decompose 𝒜 x (d * (n / d)), mem_veroneseSubalgebra_of_mem (decompose 𝒜 x _).2⟩,
            (decompose 𝒜 x _).2⟩
    refine ⟨z, Subtype.ext ?_⟩
    simp only [z, map_sum, coeAddMonoidHom_of, AddSubmonoidClass.coe_finsetSum]
    conv_rhs => rw [← sum_support_decompose 𝒜 x]
    rw [Finset.sum_congr rfl fun n hn => by rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2],
      Finset.sum_filter_of_ne]
    exact fun n _ hne => not_not.mp fun hn => hne (hx n hn)

/-- For `d ≥ 1`, the Veronese subalgebra `R^(d)`, graded by `m ↦ R_{dm}`, is a graded
`A`-algebra. -/
instance veroneseGrade.gradedAlgebra (d : ℕ) [NeZero d] : GradedAlgebra (veroneseGrade 𝒜 d) :=
  { veroneseGrade.gradedMonoid 𝒜 d,
    (veroneseGrade_isInternal 𝒜 (Nat.pos_of_ne_zero (NeZero.ne d))).chooseDecomposition with }

variable {𝒜} in
/-- The degree-`m` component of `x ∈ R^(d)` is the degree-`dm` component of `x` in `R`. -/
@[simp]
theorem coe_decompose_veroneseGrade {d : ℕ} [NeZero d] (x : veroneseSubalgebra 𝒜 d) (m : ℕ) :
    ((decompose (veroneseGrade 𝒜 d) x m : veroneseSubalgebra 𝒜 d) : R) =
      decompose 𝒜 (x : R) (d * m) := by
  conv_rhs => rw [← (decompose (veroneseGrade 𝒜 d)).symm_apply_apply x]
  exact (coe_decompose_coeAddMonoidHom_veroneseGrade (Nat.pos_of_ne_zero (NeZero.ne d))
    (decompose (veroneseGrade 𝒜 d) x) m).symm

end MMP.Fourfold
