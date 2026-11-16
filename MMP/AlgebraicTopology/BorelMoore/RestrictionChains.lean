module

public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Subdivision towards an open subset

Let `U` be an open subset of a space `Y`. Call a singular simplex *good* if its image lies in
`U`. Good simplices are closed under taking faces, barycentric subdivision `S` and the
subdivision homotopy `T`. Let `p` be the projection of singular chains onto the good part and
`q = 1 - p`. Subdividing only the bad simplices, over and over, gives the chains
`X_N = (q S) ^ N q`, and with `D_N = ∑_{i < N} T X_i` the chain map
`ρ_N = 1 - ∂ D_N - D_N ∂` (as for the theorem of small chains) satisfies `q ρ_N = X_N`. Hence the
good part `p ρ_N` fails to be a chain map only by `p ∂ X_N`:
`∂ (p ρ_N c) = p ρ_N (∂ c) - p ∂ X_N c`.

The bad chains `X_N σ` of a simplex `σ` concentrate on `σ(σ⁻¹(Y - U))`: for every open `V`
containing `range σ - U`, all simplices of `X_N σ` lie in `V` for `N` large, since the
simplices of the `N`-th subdivision of `Δⁿ` have diameter at most `(n / (n + 1)) ^ N`.
This is the input for the restriction of locally finite chains to `U`.

## Main definitions

* `MMP.SingularChain.goodProj`, `badProj`: the projections `p`, `q`.
* `MMP.SingularChain.badChain`: `X_N`.
* `MMP.SingularChain.towardsHomotopy`: `D_N`.
* `MMP.SingularChain.towardsChainMap`: `ρ_N`.

## Main results

* `MMP.SingularChain.badProj_towardsChainMap`: `q ρ_N = X_N`.
* `MMP.SingularChain.bd_goodProj_towardsChainMap`: the defect formula.
* `MMP.SingularChain.eventually_badChain_mem_inside`: concentration of `X_N σ`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

section inside

/-- Barycentric subdivision preserves chains made of simplices with image in `A`. -/
lemma subdiv_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    subdiv R n c ∈ inside R n A :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [subdiv_single]
    exact supported_mono (fun τ hτ ↦ Set.Subset.trans hτ hσ) (push_mem_inside σ n _)) hc

/-- The subdivision homotopy `T` sends chains in `A` to chains in `A`. -/
lemma subdivHomotopy_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    subdivHomotopy R n c ∈ inside R (n + 1) A :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [subdivHomotopy_single]
    exact supported_mono (fun τ hτ ↦ Set.Subset.trans hτ hσ) (push_mem_inside σ (n + 1) _)) hc

end inside

section proj

open Classical

variable (R) in
/-- The projection `p` of singular chains onto their part made of simplices with image in `U`. -/
def goodProj (U : Set Y) (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y n :=
  linearCombination R fun σ ↦ if range σ ⊆ U then single σ 1 else 0

variable (R) in
/-- The complementary projection `q = 1 - p`. -/
def badProj (U : Set Y) (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y n :=
  LinearMap.id - goodProj R U n

variable {U : Set Y}

/-- `p σ = σ` if `σ` has image in `U`, and `p σ = 0` otherwise. -/
lemma goodProj_single {n : ℕ} (σ : Simplex Y n) :
    goodProj R U n (single σ 1) = if range σ ⊆ U then single σ 1 else 0 := by
  classical
  simp [goodProj]

/-- `q σ = 0` if `σ` has image in `U`, and `q σ = σ` otherwise. -/
lemma badProj_single {n : ℕ} (σ : Simplex Y n) :
    badProj R U n (single σ 1) = if range σ ⊆ U then 0 else single σ 1 := by
  rw [badProj, LinearMap.sub_apply, LinearMap.id_apply, goodProj_single]
  split_ifs <;> simp

/-- The coefficient of `τ` in `p c` is that in `c` if `τ` has image in `U`, and `0` otherwise. -/
lemma goodProj_apply {n : ℕ} (c : Chain R Y n) (τ : Simplex Y n) :
    goodProj R U n c τ = if range τ ⊆ U then c τ else 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]; split_ifs <;> simp
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, goodProj_single]
    by_cases hσ : σ = τ
    · subst hσ; split_ifs <;> simp
    · split_ifs <;> simp [single_apply, hσ]

/-- The coefficient of `τ` in `q c` is `0` if `τ` has image in `U`, and that in `c` otherwise. -/
lemma badProj_apply {n : ℕ} (c : Chain R Y n) (τ : Simplex Y n) :
    badProj R U n c τ = if range τ ⊆ U then 0 else c τ := by
  rw [badProj, LinearMap.sub_apply, LinearMap.id_apply, Finsupp.sub_apply, goodProj_apply]
  split_ifs <;> simp

/-- The good part `p c` is a chain in `U`. -/
lemma goodProj_mem_inside_self {n : ℕ} (c : Chain R Y n) :
    goodProj R U n c ∈ inside R n U := by
  intro τ hτ
  rw [Finset.mem_coe, mem_support_iff, goodProj_apply] at hτ
  by_contra h
  exact hτ (if_neg h)

/-- If `c` is a chain in `A`, then so is `p c`. -/
lemma goodProj_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    goodProj R U n c ∈ inside R n A := by
  intro τ hτ
  rw [Finset.mem_coe, mem_support_iff, goodProj_apply] at hτ
  split_ifs at hτ with h
  · exact hc (mem_support_iff.2 hτ)
  · exact absurd rfl hτ

/-- If `c` is supported on a set `s` of simplices, then so is `q c`. -/
lemma badProj_mem_supported {n : ℕ} {s : Set (Simplex Y n)} {c : Chain R Y n}
    (hc : c ∈ supported R R s) : badProj R U n c ∈ supported R R s := by
  intro τ hτ
  rw [Finset.mem_coe, mem_support_iff, badProj_apply] at hτ
  split_ifs at hτ with h
  · exact absurd rfl hτ
  · exact hc (mem_support_iff.2 hτ)

/-- If `c` is a chain in `A`, then so is `q c`. -/
lemma badProj_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    badProj R U n c ∈ inside R n A :=
  badProj_mem_supported hc

/-- `q` vanishes on chains in `U`. -/
lemma badProj_eq_zero_of_mem_inside {n : ℕ} {c : Chain R Y n} (hc : c ∈ inside R n U) :
    badProj R U n c = 0 := by
  ext τ
  rw [badProj_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hc (mem_support_iff.2 hne))

/-- `p c + q c = c`. -/
lemma goodProj_add_badProj {n : ℕ} (c : Chain R Y n) :
    goodProj R U n c + badProj R U n c = c := by
  simp [badProj]

/-- `q` is idempotent: `q q = q`. -/
lemma badProj_badProj {n : ℕ} (c : Chain R Y n) :
    badProj R U n (badProj R U n c) = badProj R U n c := by
  ext τ
  simp only [badProj_apply]
  split_ifs <;> rfl

/-- `p q = 0`. -/
lemma goodProj_badProj {n : ℕ} (c : Chain R Y n) :
    goodProj R U n (badProj R U n c) = 0 := by
  ext τ
  simp only [goodProj_apply, badProj_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs <;> rfl

/-- `q ∂ = q ∂ q`: the faces of good simplices are good. -/
lemma badProj_bd_badProj {n : ℕ} (c : Chain R Y (n + 1)) :
    badProj R U n (bd R n (badProj R U (n + 1) c)) = badProj R U n (bd R n c) := by
  conv_rhs => rw [← goodProj_add_badProj (U := U) c]
  rw [map_add, map_add, badProj_eq_zero_of_mem_inside (bd_mem_inside (goodProj_mem_inside_self _)),
    zero_add]

/-- `q S = q S q`. -/
lemma badProj_subdiv_badProj {n : ℕ} (c : Chain R Y n) :
    badProj R U n (subdiv R n (badProj R U n c)) = badProj R U n (subdiv R n c) := by
  conv_rhs => rw [← goodProj_add_badProj (U := U) c]
  rw [map_add, map_add,
    badProj_eq_zero_of_mem_inside (subdiv_mem_inside (goodProj_mem_inside_self _)), zero_add]

/-- `p S p = S p`. -/
lemma goodProj_subdiv_goodProj {n : ℕ} (c : Chain R Y n) :
    goodProj R U n (subdiv R n (goodProj R U n c)) = subdiv R n (goodProj R U n c) := by
  have h := goodProj_add_badProj (U := U) (subdiv R n (goodProj R U n c))
  rwa [badProj_eq_zero_of_mem_inside (subdiv_mem_inside (goodProj_mem_inside_self _)),
    add_zero] at h

end proj

section tower

variable (R) (U : Set Y)

/-- The bad chains `X_N = (q S) ^ N q`: the simplices of the iterated subdivision that are
still not in `U`, where good simplices are no longer subdivided. -/
def badChain (N n : ℕ) : Chain R Y n →ₗ[R] Chain R Y n :=
  ((badProj R U n ∘ₗ subdiv R n) ^ N) ∘ₗ badProj R U n

/-- `D_N = ∑_{i < N} T X_i`. -/
def towardsHomotopy (N n : ℕ) : Chain R Y n →ₗ[R] Chain R Y (n + 1) :=
  ∑ i ∈ Finset.range N, subdivHomotopy R n ∘ₗ badChain R U i n

/-- The chain map `ρ_N = 1 - ∂ D_N - D_N ∂`. -/
def towardsChainMap (N : ℕ) : ∀ n : ℕ, Chain R Y n →ₗ[R] Chain R Y n
  | 0 => LinearMap.id - bd R 0 ∘ₗ towardsHomotopy R U N 0
  | n + 1 => LinearMap.id - bd R (n + 1) ∘ₗ towardsHomotopy R U N (n + 1) -
      towardsHomotopy R U N n ∘ₗ bd R n

variable {R U}

/-- `X_0 = q`. -/
lemma badChain_zero (n : ℕ) (c : Chain R Y n) : badChain R U 0 n c = badProj R U n c := by
  simp [badChain]

/-- `X_{N+1} = q S X_N`. -/
lemma badChain_succ (N n : ℕ) (c : Chain R Y n) :
    badChain R U (N + 1) n c = badProj R U n (subdiv R n (badChain R U N n c)) := by
  simp only [badChain, LinearMap.comp_apply, pow_succ', Module.End.mul_apply]

/-- `q X_N = X_N`. -/
lemma badProj_badChain (N n : ℕ) (c : Chain R Y n) :
    badProj R U n (badChain R U N n c) = badChain R U N n c := by
  cases N with
  | zero => rw [badChain_zero, badProj_badProj]
  | succ N => rw [badChain_succ, badProj_badProj]

/-- `p X_N = 0`. -/
lemma goodProj_badChain (N n : ℕ) (c : Chain R Y n) :
    goodProj R U n (badChain R U N n c) = 0 := by
  rw [← badProj_badChain, goodProj_badProj]

/-- `X_N ∂ = q ∂ X_N`. -/
lemma badChain_bd (N n : ℕ) (c : Chain R Y (n + 1)) :
    badChain R U N n (bd R n c) = badProj R U n (bd R n (badChain R U N (n + 1) c)) := by
  induction N with
  | zero => rw [badChain_zero, badChain_zero, badProj_bd_badProj]
  | succ N ih =>
    rw [badChain_succ, badChain_succ, ih, badProj_subdiv_badProj, ← bd_subdiv,
      badProj_bd_badProj]

/-- `D_{N+1} = D_N + T X_N`. -/
lemma towardsHomotopy_succ (N n : ℕ) (c : Chain R Y n) :
    towardsHomotopy R U (N + 1) n c =
      towardsHomotopy R U N n c + subdivHomotopy R n (badChain R U N n c) := by
  simp [towardsHomotopy, Finset.sum_range_succ]

/-- `D_0 = 0`. -/
lemma towardsHomotopy_zero (n : ℕ) (c : Chain R Y n) : towardsHomotopy R U 0 n c = 0 := by
  simp [towardsHomotopy]

/-- In degree `0`, `ρ_N c = c - ∂ D_N c`. -/
lemma towardsChainMap_zero_apply (N : ℕ) (c : Chain R Y 0) :
    towardsChainMap R U N 0 c = c - bd R 0 (towardsHomotopy R U N 0 c) := rfl

/-- In degree `n + 1`, `ρ_N c = c - ∂ D_N c - D_N ∂ c`. -/
lemma towardsChainMap_succ_apply (N n : ℕ) (c : Chain R Y (n + 1)) :
    towardsChainMap R U N (n + 1) c = c - bd R (n + 1) (towardsHomotopy R U N (n + 1) c) -
      towardsHomotopy R U N n (bd R n c) := rfl

/-- `ρ_N` is a chain map. -/
lemma bd_towardsChainMap (N n : ℕ) (c : Chain R Y (n + 1)) :
    bd R n (towardsChainMap R U N (n + 1) c) = towardsChainMap R U N n (bd R n c) := by
  rw [towardsChainMap_succ_apply, map_sub, map_sub, bd_bd, sub_zero]
  cases n with
  | zero => rfl
  | succ n => rw [towardsChainMap_succ_apply, bd_bd, map_zero, sub_zero]

/-- The step `ρ_{N+1} - ρ_N` in degree `0`. -/
lemma towardsChainMap_succ_sub_zero (N : ℕ) (c : Chain R Y 0) :
    towardsChainMap R U (N + 1) 0 c - towardsChainMap R U N 0 c =
      -bd R 0 (subdivHomotopy R 0 (badChain R U N 0 c)) := by
  rw [towardsChainMap_zero_apply, towardsChainMap_zero_apply, towardsHomotopy_succ, map_add]
  abel

/-- The step `ρ_{N+1} - ρ_N` in degree `n + 1`. -/
lemma towardsChainMap_succ_sub_succ (N n : ℕ) (c : Chain R Y (n + 1)) :
    towardsChainMap R U (N + 1) (n + 1) c - towardsChainMap R U N (n + 1) c =
      -(bd R (n + 1) (subdivHomotopy R (n + 1) (badChain R U N (n + 1) c)) +
        subdivHomotopy R n (badChain R U N n (bd R n c))) := by
  rw [towardsChainMap_succ_apply, towardsChainMap_succ_apply, towardsHomotopy_succ,
    towardsHomotopy_succ, map_add]
  abel

/-- `q ρ_N = X_N`. -/
lemma badProj_towardsChainMap (N : ℕ) : ∀ n (c : Chain R Y n),
    badProj R U n (towardsChainMap R U N n c) = badChain R U N n c := by
  induction N with
  | zero =>
    intro n c
    cases n with
    | zero => rw [towardsChainMap_zero_apply, towardsHomotopy_zero, map_zero, sub_zero,
        badChain_zero]
    | succ n => rw [towardsChainMap_succ_apply, towardsHomotopy_zero, towardsHomotopy_zero,
        map_zero, sub_zero, sub_zero, badChain_zero]
  | succ N ih =>
    intro n c
    cases n with
    | zero =>
      have h := congrArg (badProj R U 0) (towardsChainMap_succ_sub_zero (U := U) N c)
      rw [map_sub, ih, map_neg, bd_subdivHomotopy_zero, map_sub, badProj_badChain] at h
      rw [badChain_succ]
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      abel
    | succ n =>
      have h := congrArg (badProj R U (n + 1)) (towardsChainMap_succ_sub_succ (U := U) N n c)
      have h1 := bd_subdivHomotopy_add (R := R) n (badChain R U N (n + 1) c)
      rw [map_sub, ih, map_neg, eq_sub_iff_add_eq.2 h1, map_add, map_sub, map_sub,
        badProj_badChain, badChain_bd] at h
      have h2 : badProj R U (n + 1) (subdivHomotopy R n (badProj R U n
          (bd R n (badChain R U N (n + 1) c)))) =
          badProj R U (n + 1) (subdivHomotopy R n (bd R n (badChain R U N (n + 1) c))) := by
        conv_rhs => rw [← goodProj_add_badProj (U := U) (bd R n (badChain R U N (n + 1) c))]
        rw [map_add, map_add, badProj_eq_zero_of_mem_inside
          (subdivHomotopy_mem_inside (goodProj_mem_inside_self _)), zero_add]
      rw [h2] at h
      rw [badChain_succ]
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      abel

/-- The defect of the good part of `ρ_N`: `∂ (p ρ_N c) = p ρ_N (∂ c) - p ∂ X_N c`. -/
lemma bd_goodProj_towardsChainMap (N n : ℕ) (c : Chain R Y (n + 1)) :
    bd R n (goodProj R U (n + 1) (towardsChainMap R U N (n + 1) c)) =
      goodProj R U n (towardsChainMap R U N n (bd R n c)) -
        goodProj R U n (bd R n (badChain R U N (n + 1) c)) := by
  set y := towardsChainMap R U N (n + 1) c
  have hy : badProj R U (n + 1) y = badChain R U N (n + 1) c := badProj_towardsChainMap N _ c
  rw [← bd_towardsChainMap, ← hy]
  have h0 : badProj R U n (bd R n (goodProj R U (n + 1) y)) = 0 :=
    badProj_eq_zero_of_mem_inside (bd_mem_inside (goodProj_mem_inside_self _))
  have h1 := goodProj_add_badProj (U := U) (bd R n (goodProj R U (n + 1) y))
  rw [h0, add_zero] at h1
  have e : bd R n y = bd R n (goodProj R U (n + 1) y) + bd R n (badProj R U (n + 1) y) := by
    rw [← map_add, goodProj_add_badProj]
  rw [e, map_add, h1]
  abel

end tower

section concentration

variable {U : Set Y}

/-- A chain in `A` has coefficient `0` at every simplex whose image is not contained in `A`. -/
lemma eq_zero_of_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A)
    {τ : Simplex Y n} (hτ : ¬range τ ⊆ A) : c τ = 0 := by
  by_contra h
  exact hτ (hc (mem_support_iff.2 h))

/-- If `c` is a chain in `A`, then so is `X_N c`. -/
lemma badChain_mem_inside {N n : ℕ} {A : Set Y} {c : Chain R Y n} (hc : c ∈ inside R n A) :
    badChain R U N n c ∈ inside R n A := by
  induction N with
  | zero => rw [badChain_zero]; exact badProj_mem_inside hc
  | succ N ih => rw [badChain_succ]; exact badProj_mem_inside (subdiv_mem_inside ih)

/-- If `c` is a chain in `A`, then so is `D_N c`. -/
lemma towardsHomotopy_mem_inside {N n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) : towardsHomotopy R U N n c ∈ inside R (n + 1) A := by
  rw [towardsHomotopy, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ subdivHomotopy_mem_inside (badChain_mem_inside hc)

/-- If `c` is a chain in `A`, then so is `ρ_N c`. -/
lemma towardsChainMap_mem_inside {N n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) : towardsChainMap R U N n c ∈ inside R n A := by
  cases n with
  | zero =>
    rw [towardsChainMap_zero_apply]
    exact sub_mem hc (bd_mem_inside (towardsHomotopy_mem_inside hc))
  | succ n =>
    rw [towardsChainMap_succ_apply]
    exact sub_mem (sub_mem hc (bd_mem_inside (towardsHomotopy_mem_inside hc)))
      (towardsHomotopy_mem_inside (bd_mem_inside hc))

/-- A simplex `σ` is a chain in its image `range σ`. -/
lemma single_mem_inside_range {n : ℕ} (σ : Simplex Y n) :
    single σ (1 : R) ∈ inside R n (range σ) :=
  single_mem_supported R _ (show range σ ⊆ range σ from subset_rfl)

/-- The simplices `σ ∘ affine w` whose vertices `w` are pairwise at distance at most `D`. -/
def affineSimplices {n : ℕ} (σ : Simplex Y n) (D : ℝ) : Set (Simplex Y n) :=
  {τ | ∃ w : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)),
    (∀ i j, dist (w i) (w j) ≤ D) ∧ τ = σ.comp (VertexChain.affine w)}

/-- Pushing forward along `σ` a chain of affine simplices of `Δⁿ` whose vertices are pairwise at
distance at most `D` gives a chain supported on `affineSimplices σ D`. -/
lemma push_mem_supported_affineSimplices {n : ℕ} (σ : Simplex Y n) {D : ℝ}
    {c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (n + 1)}
    (hc : c ∈ supported R R {w | ∀ i j, dist (w i) (w j) ≤ D}) :
    push R σ n c ∈ supported R R (affineSimplices σ D) :=
  VertexChain.mem_of_mem_supported _ _ (fun w hw ↦ by
    rw [push_single]; exact single_mem_supported R _ ⟨w, hw, rfl⟩) hc

/-- Barycentric subdivision sends chains supported on `affineSimplices σ D` to chains supported on
`affineSimplices σ (n / (n + 1) * D)`. -/
lemma subdiv_mem_supported_affineSimplices {n : ℕ} (σ : Simplex Y n) {D : ℝ}
    {c : Chain R Y n} (hc : c ∈ supported R R (affineSimplices σ D)) :
    subdiv R n c ∈ supported R R (affineSimplices σ ((n : ℝ) / (n + 1) * D)) :=
  VertexChain.mem_of_mem_supported _ _ (fun τ hτ ↦ by
    obtain ⟨w, hw, rfl⟩ := hτ
    rw [← push_single, ← push_subdiv]
    exact push_mem_supported_affineSimplices σ
      (supported_mono (fun _ h ↦ h.2) (VertexChain.subdiv_single_mem R n w hw))) hc

/-- The bad chain `X_N σ` is supported on `affineSimplices σ ((n / (n + 1)) ^ N)`. -/
lemma badChain_single_mem_supported {n : ℕ} (σ : Simplex Y n) (N : ℕ) :
    badChain R U N n (single σ 1) ∈
      supported R R (affineSimplices σ (((n : ℝ) / (n + 1)) ^ N)) := by
  induction N with
  | zero =>
    rw [badChain_zero, pow_zero]
    refine badProj_mem_supported (single_mem_supported R _
      ⟨vertices n, fun i j ↦ VertexChain.dist_vertex_le i j, ?_⟩)
    ext t
    exact congr_arg σ (VertexChain.affine_vertices t).symm
  | succ N ih =>
    rw [badChain_succ, pow_succ']
    exact badProj_mem_supported (subdiv_mem_supported_affineSimplices σ ih)

/-- Concentration of the bad chains: if `U` and `V` are open and cover `Y`, then the bad chains
`X_N σ` of a simplex `σ` lie in `V` for all large `N`. -/
lemma eventually_badChain_mem_inside (hU : IsOpen U) {V : Set Y} (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n : ℕ} (σ : Simplex Y n) :
    ∃ N₀, ∀ N ≥ N₀, badChain R U N n (single σ 1) ∈ inside R n V := by
  have : CompactSpace (stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (n + 1)))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun b : Bool ↦ cond b (σ ⁻¹' U) (σ ⁻¹' V)) isCompact_univ
    (fun b ↦ by
      cases b
      · exact hV.preimage σ.continuous
      · exact hU.preimage σ.continuous)
    (fun t _ ↦ by
      have : σ t ∈ U ∪ V := hUV ▸ mem_univ _
      rcases this with h | h
      · exact mem_iUnion.2 ⟨true, h⟩
      · exact mem_iUnion.2 ⟨false, h⟩)
  have hr1 : (n : ℝ) / (n + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hδ hr1
  refine ⟨N₀, fun N hN τ hτ ↦ ?_⟩
  have hτbad : ¬range τ ⊆ U := by
    have h := hτ
    rw [Finset.mem_coe, mem_support_iff, ← badProj_badChain, badProj_apply] at h
    split_ifs at h with h'
    · exact absurd rfl h
    · exact h'
  obtain ⟨w, hw, rfl⟩ := badChain_single_mem_supported (U := U) σ N hτ
  have hr : ((n : ℝ) / (n + 1)) ^ N < δ :=
    (pow_le_pow_of_le_one (by positivity) hr1.le hN).trans_lt hN₀
  have hsub : range (VertexChain.affine w) ⊆ Metric.ball (w 0) δ := by
    rintro _ ⟨t, rfl⟩
    exact Metric.mem_ball.2 ((VertexChain.dist_affine_le w hw t).trans_lt hr)
  obtain ⟨b, hb⟩ := hball (w 0) (mem_univ _)
  cases b
  · rintro _ ⟨t, rfl⟩
    exact hb (hsub ⟨t, rfl⟩)
  · exact absurd (by rintro _ ⟨t, rfl⟩; exact hb (hsub ⟨t, rfl⟩)) hτbad

/-- If `X_N c` is a chain in `A`, then so is `ρ_{N+1} c - ρ_N c`. -/
lemma towardsChainMap_succ_sub_mem_inside {A : Set Y} (N n : ℕ) {c : Chain R Y n}
    (hc : badChain R U N n c ∈ inside R n A) :
    towardsChainMap R U (N + 1) n c - towardsChainMap R U N n c ∈ inside R n A := by
  cases n with
  | zero =>
    rw [towardsChainMap_succ_sub_zero]
    exact neg_mem (bd_mem_inside (subdivHomotopy_mem_inside hc))
  | succ n =>
    rw [towardsChainMap_succ_sub_succ, badChain_bd]
    exact neg_mem (add_mem (bd_mem_inside (subdivHomotopy_mem_inside hc))
      (subdivHomotopy_mem_inside (badProj_mem_inside (bd_mem_inside hc))))

/-- Stabilization: if `U` and `V` are open and cover `Y`, then for large `N` the chains `ρ_N σ`
differ only by chains in `V`, and the bad chains `X_N σ` lie in `V`. -/
lemma eventually_towardsChainMap_sub_mem_inside (hU : IsOpen U) {V : Set Y} (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n : ℕ} (σ : Simplex Y n) :
    ∃ N₀, ∀ N ≥ N₀, towardsChainMap R U N n (single σ 1) -
        towardsChainMap R U N₀ n (single σ 1) ∈ inside R n V ∧
      badChain R U N n (single σ 1) ∈ inside R n V := by
  obtain ⟨N₀, h⟩ := eventually_badChain_mem_inside (R := R) hU hV hUV σ
  refine ⟨N₀, fun N hN ↦ ⟨?_, h N hN⟩⟩
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [← sub_add_sub_cancel _ (towardsChainMap R U N n (single σ 1))]
    exact add_mem (towardsChainMap_succ_sub_mem_inside N n (h N hN)) ih

end concentration

section restrCoeff

variable (R) (U : Set Y)

/-- The good part `p ρ_N σ` of `ρ_N σ`. -/
def goodPart (N : ℕ) {n : ℕ} (σ : Simplex Y n) : Chain R Y n :=
  goodProj R U n (towardsChainMap R U N n (single σ 1))

open Classical in
/-- The coefficient of `τ` in the restriction of `σ` to `U`: the eventual value of the
coefficient of `τ` in `p ρ_N σ` (`0` if it does not stabilize). -/
def restrCoeff {n : ℕ} (σ τ : Simplex Y n) : R :=
  if h : ∃ N₀, ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ then
    goodPart R U (Nat.find h) σ τ else 0

variable {R U}

/-- If the coefficient of `τ` in `p ρ_N σ` is constant for `N ≥ N₀`, then `restrCoeff R U σ τ`
is its value at `N₀`. -/
lemma restrCoeff_eq {n : ℕ} {σ τ : Simplex Y n} {N₀ : ℕ}
    (h : ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ) :
    restrCoeff R U σ τ = goodPart R U N₀ σ τ := by
  classical
  have h' : ∃ N₀, ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ := ⟨N₀, h⟩
  rw [restrCoeff, dif_pos h', ← Nat.find_spec h' (max (Nat.find h') N₀) (le_max_left _ _),
    h _ (le_max_right _ _)]

/-- The good part `p ρ_N σ` is a chain in `range σ ∩ U`. -/
lemma goodPart_mem_inside {N n : ℕ} (σ : Simplex Y n) :
    goodPart R U N σ ∈ inside R n (range σ ∩ U) := by
  intro τ hτ
  exact subset_inter (goodProj_mem_inside (towardsChainMap_mem_inside
    (single_mem_inside_range σ)) hτ) (goodProj_mem_inside_self _ hτ)

/-- A simplex `τ` with nonzero coefficient in the restriction of `σ` has image in `range σ ∩ U`. -/
lemma range_subset_of_restrCoeff_ne_zero {n : ℕ} {σ τ : Simplex Y n}
    (h : restrCoeff R U σ τ ≠ 0) : range τ ⊆ range σ ∩ U := by
  classical
  rw [restrCoeff] at h
  split_ifs at h with h'
  · exact goodPart_mem_inside σ (mem_support_iff.2 h)
  · exact absurd rfl h

/-- A chain in `A` and in `B` is a chain in every `C` containing `A ∩ B`. -/
lemma mem_inside_of_inter {n : ℕ} {A B C : Set Y} {c : Chain R Y n} (hA : c ∈ inside R n A)
    (hB : c ∈ inside R n B) (h : A ∩ B ⊆ C) : c ∈ inside R n C :=
  fun τ hτ ↦ (subset_inter (hA hτ) (hB hτ)).trans h

/-- Stabilization near `U`, for an open `V` containing the points of `σ` outside `U`. -/
lemma eventually_goodPart_sub_mem_inside [T2Space Y] (hU : IsOpen U) {n : ℕ} (σ : Simplex Y n)
    {V : Set Y} (hV : IsOpen V) (hσV : range σ ∩ Uᶜ ⊆ V) :
    ∃ N₀, ∀ N ≥ N₀, towardsChainMap R U N n (single σ 1) -
        towardsChainMap R U N₀ n (single σ 1) ∈ inside R n V ∧
      badChain R U N n (single σ 1) ∈ inside R n V := by
  have hV₁ : IsOpen (V ∪ (range σ)ᶜ) :=
    hV.union (isCompact_range σ.continuous).isClosed.isOpen_compl
  have hUV : U ∪ (V ∪ (range σ)ᶜ) = univ := eq_univ_of_forall fun x ↦ by
    by_cases hx : x ∈ U
    · exact Or.inl hx
    by_cases hx' : x ∈ range σ
    · exact Or.inr (Or.inl (hσV ⟨hx', hx⟩))
    · exact Or.inr (Or.inr hx')
  obtain ⟨N₀, h⟩ := eventually_towardsChainMap_sub_mem_inside (R := R) hU hV₁ hUV σ
  have hsub : (V ∪ (range σ)ᶜ) ∩ range σ ⊆ V := by
    rintro x ⟨hx | hx, hx'⟩
    exacts [hx, absurd hx' hx]
  refine ⟨N₀, fun N hN ↦ ⟨mem_inside_of_inter (h N hN).1 (sub_mem
    (towardsChainMap_mem_inside (single_mem_inside_range σ))
    (towardsChainMap_mem_inside (single_mem_inside_range σ))) hsub,
    mem_inside_of_inter (h N hN).2 (badChain_mem_inside (single_mem_inside_range σ)) hsub⟩⟩

/-- In a Hausdorff space, the points of `σ` outside an open `U` and a compact `K ⊆ U` have
disjoint open neighbourhoods. -/
lemma separatedNhds_range_inter_compl [T2Space Y] (hU : IsOpen U) {n : ℕ} (σ : Simplex Y n)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) : SeparatedNhds (range σ ∩ Uᶜ) K :=
  SeparatedNhds.of_isCompact_isCompact ((isCompact_range σ.continuous).inter_right
    hU.isClosed_compl) hK (Set.disjoint_left.2 fun _ hx hxK ↦ hx.2 (hKU hxK))

/-- The coefficients of the restriction of `σ` near a compact subset `K` of `U` are those of a
single `p ρ_{N₀} σ`, and so are those of the faces of `σ`. -/
lemma exists_restrCoeff_eq_goodPart [T2Space Y] (hU : IsOpen U) {n : ℕ}
    (σ : Simplex Y (n + 1)) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ ∃ N₀ : ℕ,
      (∀ τ : Simplex Y (n + 1), (range τ ∩ W).Nonempty →
        restrCoeff R U σ τ = goodPart R U N₀ σ τ) ∧
      (∀ (i : Fin (n + 2)) (τ : Simplex Y n), (range τ ∩ W).Nonempty →
        restrCoeff R U (σ.comp (face n i)) τ = goodPart R U N₀ (σ.comp (face n i)) τ) ∧
      (∀ τ : Simplex Y n, (range τ ∩ W).Nonempty →
        bd R n (goodPart R U N₀ σ) τ =
          ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * goodPart R U N₀ (σ.comp (face n i)) τ) := by
  obtain ⟨V, W, hV, hW, hCV, hKW, hVW⟩ := separatedNhds_range_inter_compl hU σ hK hKU
  have hface : ∀ i : Fin (n + 2), range (σ.comp (face n i)) ∩ Uᶜ ⊆ V := fun i x hx ↦
    hCV ⟨by obtain ⟨t, ht⟩ := hx.1; exact ⟨_, ht⟩, hx.2⟩
  obtain ⟨Nσ, hσ⟩ := eventually_goodPart_sub_mem_inside (R := R) hU σ hV hCV
  choose Nf hf using fun i : Fin (n + 2) ↦
    eventually_goodPart_sub_mem_inside (R := R) hU (σ.comp (face n i)) hV (hface i)
  let N₀ := max Nσ (Finset.univ.sup Nf)
  have hNσ : Nσ ≤ N₀ := le_max_left _ _
  have hNf : ∀ i, Nf i ≤ N₀ := fun i ↦ (Finset.le_sup (f := Nf) (Finset.mem_univ i)).trans
    (le_max_right _ _)
  have hnotV : ∀ {m : ℕ} (τ : Simplex Y m), (range τ ∩ W).Nonempty → ¬range τ ⊆ V := by
    rintro m τ ⟨x, hx, hxW⟩ h
    exact Set.disjoint_left.1 hVW (h hx) hxW
  have stab : ∀ {m : ℕ} (ς : Simplex Y m) (M : ℕ), (∀ N ≥ M,
      towardsChainMap R U N m (single ς 1) - towardsChainMap R U M m (single ς 1) ∈
        inside R m V) → ∀ N₁ ≥ M, ∀ τ : Simplex Y m, (range τ ∩ W).Nonempty →
      ∀ N ≥ N₁, goodPart R U N ς τ = goodPart R U N₁ ς τ := by
    intro m ς M hM N₁ hN₁ τ hτ N hN
    have hd : towardsChainMap R U N m (single ς 1) - towardsChainMap R U N₁ m (single ς 1) ∈
        inside R m V := by
      rw [← sub_sub_sub_cancel_right _ _ (towardsChainMap R U M m (single ς 1))]
      exact sub_mem (hM N (hN₁.trans hN)) (hM N₁ hN₁)
    have h0 := eq_zero_of_mem_inside (goodProj_mem_inside (U := U) hd) (hnotV τ hτ)
    rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
  refine ⟨W, hW, hKW, N₀, fun τ hτ ↦ restrCoeff_eq
      (stab σ Nσ (fun N hN ↦ (hσ N hN).1) N₀ hNσ τ hτ),
    fun i τ hτ ↦ restrCoeff_eq (stab _ (Nf i) (fun N hN ↦ (hf i N hN).1) N₀ (hNf i) τ hτ),
    fun τ hτ ↦ ?_⟩
  rw [goodPart, bd_goodProj_towardsChainMap, Finsupp.sub_apply,
    eq_zero_of_mem_inside (goodProj_mem_inside (bd_mem_inside (hσ N₀ hNσ).2)) (hnotV τ hτ),
    sub_zero, bd_single, map_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, goodPart]

/-- Local finiteness of the restriction of a simplex: near a point of `U` only finitely many
simplices have a nonzero coefficient. -/
lemma exists_finite_restrCoeff_ne_zero [T2Space Y] (hU : IsOpen U) {n : ℕ} (σ : Simplex Y n)
    {x : Y} (hx : x ∈ U) : ∃ W, IsOpen W ∧ x ∈ W ∧
      {τ : Simplex Y n | restrCoeff R U σ τ ≠ 0 ∧ (range τ ∩ W).Nonempty}.Finite := by
  obtain ⟨V, W, hV, hW, hCV, hKW, hVW⟩ :=
    separatedNhds_range_inter_compl hU σ isCompact_singleton (singleton_subset_iff.2 hx)
  obtain ⟨N₀, h⟩ := eventually_goodPart_sub_mem_inside (R := R) hU σ hV hCV
  refine ⟨W, hW, hKW rfl, (goodPart R U N₀ σ).support.finite_toSet.subset ?_⟩
  rintro τ ⟨hτ, y, hy, hyW⟩
  have hnotV : ¬range τ ⊆ V := fun h ↦ Set.disjoint_left.1 hVW (h hy) hyW
  have hstab : ∀ N ≥ N₀, goodPart R U N σ τ = goodPart R U N₀ σ τ := fun N hN ↦ by
    have h0 := eq_zero_of_mem_inside (goodProj_mem_inside (U := U) (h N hN).1) hnotV
    rwa [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
  rw [restrCoeff_eq hstab] at hτ
  exact mem_support_iff.2 hτ

end restrCoeff

end SingularChain

end MMP
