module

public import MMP.AlgebraicTopology.SingularHomology.Excision.Diameter
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The theorem of small chains

For a topological space `Y`, a singular `n`-simplex is a continuous map `Δⁿ → Y`, and the
singular `n`-chains with coefficients in a commutative ring `R` are the formal combinations of
singular `n`-simplices, with boundary `∂ σ = ∑ i, (-1) ^ i σ ∘ δⁱ`. The barycentric subdivision
`S σ` and the subdivision homotopy `T σ` are the push-forwards along `σ` of the subdivision
and the homotopy of the identity simplex of `Δⁿ`, as vertex chains; they satisfy `∂ S = S ∂`,
`∂ T + T ∂ = 1 - S`, and a chain with every simplex inside a subset `U` keeps this property under
`S` and `T`.

Let `𝒰` be a family of open subsets of `Y`. A chain is `𝒰`-small if each of its simplices lies in
a member of `𝒰`. For every singular simplex `σ` with image in `⋃₀ 𝒰`, some `S ^ m σ` is
`𝒰`-small, by the Lebesgue number lemma. Following Hatcher, with `m(σ)` the least such `m`
(made monotone under taking faces) and `D σ = ∑_{i < m(σ)} T S ^ i σ`, the chain map
`ρ = 1 - ∂ D - D ∂` is chain homotopic to the identity by construction and sends every chain of
simplices with image in `⋃₀ 𝒰` to a `𝒰`-small chain.

## Main definitions

* `MMP.SingularChain.bd`: the boundary of singular chains.
* `MMP.SingularChain.subdiv`, `subdivHomotopy`: `S` and `T`.
* `MMP.SingularChain.small`: the `𝒰`-small chains.
* `MMP.SingularChain.postcomp`: the push-forward `f_♯` of chains along a map.
* `MMP.SingularChain.smallHomotopy`, `smallChainMap`: Hatcher's `D` and `ρ`.

## Main results

* `MMP.SingularChain.bd_bd`, `bd_subdiv`, `bd_subdivHomotopy_add`.
* `MMP.SingularChain.smallChainMap_mem_small`: `ρ` lands in the `𝒰`-small chains.
* `MMP.SingularChain.bd_smallChainMap`: `ρ` is a chain map.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable (R : Type*) [CommRing R] (Y : Type*) [TopologicalSpace Y]

/-- Singular `n`-simplices of `Y`: continuous maps from the standard `n`-simplex. -/
abbrev Simplex (n : ℕ) := C(stdSimplex ℝ (Fin (n + 1)), Y)

/-- Singular `n`-chains of `Y` with coefficients in `R`. -/
abbrev Chain (n : ℕ) := Simplex Y n →₀ R

/-- The `i`-th face inclusion `Δⁿ → Δⁿ⁺¹`. -/
def face (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩

variable {Y}

/-- The boundary `∂ σ = ∑ i, (-1) ^ i σ ∘ δⁱ`. -/
def bd (n : ℕ) : Chain R Y (n + 1) →ₗ[R] Chain R Y n :=
  linearCombination R fun σ ↦ ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • single (σ.comp (face n i)) 1

/-- The identity simplex of `Δⁿ`, as a tuple of vertices. -/
def vertices (n : ℕ) : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) := fun i ↦ stdSimplex.vertex i

/-- Push-forward of vertex chains of `Δⁿ` along a singular `n`-simplex `σ`: the tuple `w` goes
to `σ ∘ affine w`. -/
def push {n : ℕ} (σ : Simplex Y n) (k : ℕ) :
    VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1) →ₗ[R] Chain R Y k :=
  lmapDomain R R fun w ↦ σ.comp (VertexChain.affine w)

variable {R}

/-- The boundary of a single simplex: `∂ σ = ∑ i, (-1) ^ i σ ∘ δⁱ`. -/
lemma bd_single (n : ℕ) (σ : Simplex Y (n + 1)) :
    bd R n (single σ 1) = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • single (σ.comp (face n i)) 1 := by
  simp [bd]

/-- The push-forward along `σ` of a single vertex tuple `w` is the simplex `σ ∘ affine w`. -/
lemma push_single {n : ℕ} (σ : Simplex Y n) (k : ℕ) (w : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    push R σ k (single w 1) = single (σ.comp (VertexChain.affine w)) 1 := by
  simp [push]

/-- The push-forward along `σ` of the identity simplex of `Δⁿ` is `σ`. -/
lemma push_vertices {n : ℕ} (σ : Simplex Y n) :
    push R σ n (single (vertices n) 1) = single σ 1 := by
  rw [push_single]
  congr 1
  ext t
  exact congr_arg σ (VertexChain.affine_vertices t)

/-- Push-forward along a singular simplex commutes with the boundary. -/
lemma push_bd {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 2)) :
    bd R k (push R σ (k + 1) c) = push R σ k (VertexChain.bd R (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      push_single, bd_single, VertexChain.bd_single, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, push_single]
    congr 2
    ext t
    exact congr_arg σ (VertexChain.affine_map w i.succAbove t)

/-- Push-forward along `σ ∘ affine u` is push-forward along `σ` after mapping vertex chains by
`affine u`. -/
lemma push_comp {n m : ℕ} (σ : Simplex Y n) (u : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (m + 1))) (k + 1)) :
    push R (σ.comp (VertexChain.affine u)) k c =
      push R σ k (VertexChain.map R (VertexChain.affine u) (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul,
      push_single, VertexChain.map_single, push_single]
    congr 2
    ext t
    exact congr_arg σ (VertexChain.affine_affine u w t)

/-- The boundary of a boundary vanishes: `∂ ∂ = 0`. -/
lemma bd_bd (n : ℕ) (c : Chain R Y (n + 2)) : bd R n (bd R (n + 1) c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_zero]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, ← push_vertices σ,
      push_bd, push_bd, VertexChain.bd_bd, map_zero, smul_zero]

variable (R) in
/-- The barycentric subdivision `S σ` of singular chains. -/
def subdiv (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y n :=
  linearCombination R fun σ ↦
    push R σ n (VertexChain.subdiv R (VertexChain.tupleBary n) (n + 1) (single (vertices n) 1))

variable (R) in
/-- The subdivision homotopy `T σ` of singular chains. -/
def subdivHomotopy (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y (n + 1) :=
  linearCombination R fun σ ↦ push R σ (n + 1)
    (VertexChain.subdivHomotopy R (VertexChain.tupleBary n) (n + 1) (single (vertices n) 1))

/-- The subdivision of a simplex `σ` is the push-forward along `σ` of the subdivision of the
identity simplex of `Δⁿ`. -/
lemma subdiv_single (n : ℕ) (σ : Simplex Y n) :
    subdiv R n (single σ 1) =
      push R σ n (VertexChain.subdiv R (VertexChain.tupleBary n) (n + 1) (single (vertices n) 1)) := by
  simp [subdiv]

/-- The subdivision homotopy of a simplex `σ` is the push-forward along `σ` of the subdivision
homotopy of the identity simplex of `Δⁿ`. -/
lemma subdivHomotopy_single (n : ℕ) (σ : Simplex Y n) :
    subdivHomotopy R n (single σ 1) = push R σ (n + 1)
      (VertexChain.subdivHomotopy R (VertexChain.tupleBary n) (n + 1) (single (vertices n) 1)) := by
  simp [subdivHomotopy]

private lemma affine_comp_vertices {n k : ℕ} (w : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    VertexChain.affine w ∘ vertices k = w := by
  funext i; exact VertexChain.affine_vertex w i

/-- Naturality of the subdivision: `S (σ_♯ c) = σ_♯ (S c)`. -/
lemma push_subdiv {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    push R σ k (VertexChain.subdiv R (VertexChain.tupleBary n) (k + 1) c) =
      subdiv R k (push R σ k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      push_single, subdiv_single, push_comp, VertexChain.map_subdiv _ (VertexChain.affine_tupleBary w),
      VertexChain.map_single, affine_comp_vertices]

/-- Naturality of the subdivision homotopy: `T (σ_♯ c) = σ_♯ (T c)`. -/
lemma push_subdivHomotopy {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    push R σ (k + 1) (VertexChain.subdivHomotopy R (VertexChain.tupleBary n) (k + 1) c) =
      subdivHomotopy R k (push R σ k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      push_single, subdivHomotopy_single, push_comp,
      VertexChain.map_subdivHomotopy _ (VertexChain.affine_tupleBary w),
      VertexChain.map_single, affine_comp_vertices]

/-- The subdivision is a chain map. -/
lemma bd_subdiv (n : ℕ) (c : Chain R Y (n + 1)) :
    bd R n (subdiv R (n + 1) c) = subdiv R n (bd R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      subdiv_single, push_bd, VertexChain.bd_subdiv, push_subdiv, ← push_bd, push_vertices]

/-- The subdivision homotopy: `∂ T + T ∂ = 1 - S`. -/
lemma bd_subdivHomotopy_add (n : ℕ) (c : Chain R Y (n + 1)) :
    bd R (n + 1) (subdivHomotopy R (n + 1) c) + subdivHomotopy R n (bd R n c) =
      c - subdiv R (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add]; rw [add_add_add_comm, hc, hd]; abel
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, ← smul_add, ← smul_sub]
    congr 1
    rw [subdivHomotopy_single, push_bd, ← push_vertices σ, push_bd, ← push_subdivHomotopy,
      ← map_add, VertexChain.bd_subdivHomotopy_add, map_sub, push_subdiv, push_vertices,
      subdiv_single]

/-- The subdivision homotopy in degree `0`: `∂ T = 1 - S`. -/
lemma bd_subdivHomotopy_zero (c : Chain R Y 0) :
    bd R 0 (subdivHomotopy R 0 c) = c - subdiv R 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add]; rw [hc, hd]; abel
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, ← smul_sub]
    congr 1
    have := VertexChain.bd_subdivHomotopy_add (R := R) (VertexChain.tupleBary 0) 0
      (single (vertices 0) 1)
    rw [VertexChain.subdivHomotopy_zero, add_zero] at this
    rw [subdivHomotopy_single, push_bd, this, map_sub, push_vertices, push_subdiv, push_vertices]

/-- Iterated subdivision commutes with the boundary: `∂ S ^ m = S ^ m ∂`. -/
lemma bd_subdiv_pow (n : ℕ) (m : ℕ) (c : Chain R Y (n + 1)) :
    bd R n ((subdiv R (n + 1) ^ m) c) = (subdiv R n ^ m) (bd R n c) := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih => rw [pow_succ, Module.End.mul_apply, ih, bd_subdiv, pow_succ, Module.End.mul_apply]

section small

variable (R) in
/-- Chains whose simplices all lie in `U`. -/
abbrev inside (n : ℕ) (U : Set Y) : Submodule R (Chain R Y n) :=
  supported R R {σ | range σ ⊆ U}

variable (R) in
/-- The `𝒰`-small chains: those whose simplices each lie in a member of `𝒰`. -/
abbrev small (n : ℕ) (𝒰 : Set (Set Y)) : Submodule R (Chain R Y n) :=
  supported R R {σ | ∃ U ∈ 𝒰, range σ ⊆ U}

/-- A push-forward along `σ` is a chain in the image of `σ`. -/
lemma push_mem_inside {n : ℕ} (σ : Simplex Y n) (k : ℕ)
    (c : VertexChain.Chain R (stdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    push R σ k c ∈ inside R k (range σ) := by
  have hc : c ∈ supported R R univ := by simp
  refine VertexChain.mem_of_mem_supported _ _ (fun w _ ↦ ?_) hc
  rw [push_single]
  exact single_mem_supported R _ (show range (σ.comp (VertexChain.affine w)) ⊆ range σ by
    rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩)

/-- Every chain lies in `univ`. -/
lemma mem_inside_univ {n : ℕ} (c : Chain R Y n) : c ∈ inside R n (univ : Set Y) :=
  (mem_supported R c).2 fun _ _ ↦ subset_univ _

/-- The boundary of a chain in `U` lies in `U`. -/
lemma bd_mem_inside {n : ℕ} {U : Set Y} {c : Chain R Y (n + 1)} (hc : c ∈ inside R (n + 1) U) :
    bd R n c ∈ inside R n U :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [bd_single]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (single_mem_supported R _ ?_)
    rintro _ ⟨t, rfl⟩
    exact hσ ⟨_, rfl⟩) hc

/-- A chain in a member of `𝒰` is `𝒰`-small. -/
lemma mem_small_of_mem_inside {n : ℕ} {𝒰 : Set (Set Y)} {U : Set Y} (hU : U ∈ 𝒰) {c : Chain R Y n}
    (hc : c ∈ inside R n U) : c ∈ small R n 𝒰 :=
  supported_mono (s := {σ : Simplex Y n | range σ ⊆ U})
    (t := {σ : Simplex Y n | ∃ U ∈ 𝒰, range σ ⊆ U}) (fun _ h ↦ ⟨U, hU, h⟩) hc

/-- The subdivision of a `𝒰`-small chain is `𝒰`-small. -/
lemma subdiv_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {c : Chain R Y n} (hc : c ∈ small R n 𝒰) :
    subdiv R n c ∈ small R n 𝒰 :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    obtain ⟨U, hU, hσ⟩ := hσ
    rw [subdiv_single]
    exact mem_small_of_mem_inside hU (supported_mono (fun τ hτ ↦ Set.Subset.trans hτ hσ)
      (push_mem_inside σ n _))) hc

/-- Iterated subdivisions of a `𝒰`-small chain are `𝒰`-small. -/
lemma subdiv_pow_mem_small {n : ℕ} {𝒰 : Set (Set Y)} (m : ℕ) {c : Chain R Y n}
    (hc : c ∈ small R n 𝒰) : (subdiv R n ^ m) c ∈ small R n 𝒰 := by
  induction m with
  | zero => exact hc
  | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact subdiv_mem_small ih

/-- The subdivision homotopy of a `𝒰`-small chain is `𝒰`-small. -/
lemma subdivHomotopy_mem_small {n : ℕ} {𝒰 : Set (Set Y)} {c : Chain R Y n}
    (hc : c ∈ small R n 𝒰) : subdivHomotopy R n c ∈ small R (n + 1) 𝒰 :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    obtain ⟨U, hU, hσ⟩ := hσ
    rw [subdivHomotopy_single]
    exact mem_small_of_mem_inside hU (supported_mono (fun τ hτ ↦ Set.Subset.trans hτ hσ)
      (push_mem_inside σ (n + 1) _))) hc

/-- `S ^ m σ` is the push-forward along `σ` of the `m`-fold subdivision of the identity simplex
of `Δⁿ`. -/
lemma subdiv_pow_single (n m : ℕ) (σ : Simplex Y n) :
    (subdiv R n ^ m) (single σ 1) = push R σ n
      ((VertexChain.subdiv R (VertexChain.tupleBary n) (n + 1))^[m] (single (vertices n) 1)) := by
  induction m with
  | zero => exact (push_vertices σ).symm
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', push_subdiv]

/-- Some iterated subdivision of a simplex with image in `⋃₀ 𝒰`, `𝒰` open, is `𝒰`-small. -/
lemma exists_subdiv_pow_mem_small {n : ℕ} {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    {σ : Simplex Y n} (hσ : range σ ⊆ ⋃₀ 𝒰) :
    ∃ m, (subdiv R n ^ m) (single σ 1) ∈ small R n 𝒰 := by
  obtain ⟨m, hm⟩ := VertexChain.exists_iterate_subdiv_small R (fun U : 𝒰 ↦ σ ⁻¹' U)
    (fun U ↦ (h𝒰 U U.2).preimage σ.continuous) (by
      refine eq_univ_of_forall fun t ↦ ?_
      obtain ⟨U, hU, ht⟩ := hσ ⟨t, rfl⟩
      exact mem_iUnion.2 ⟨⟨U, hU⟩, ht⟩)
  refine ⟨m, ?_⟩
  rw [subdiv_pow_single]
  refine VertexChain.mem_of_mem_supported _ _ (fun w hw ↦ ?_) hm
  obtain ⟨U, hU⟩ := hw
  rw [push_single]
  exact single_mem_supported R _ ⟨U, U.2, fun _ ⟨t, ht⟩ ↦ ht ▸ hU ⟨t, rfl⟩⟩

variable (R) in
/-- The least `m` with `S ^ m σ` `𝒰`-small (`0` if there is none). -/
def smallIndex₀ {n : ℕ} (𝒰 : Set (Set Y)) (σ : Simplex Y n) : ℕ := by
  classical
  exact if h : ∃ m, (subdiv R n ^ m) (single σ 1) ∈ small R n 𝒰 then Nat.find h else 0

variable (R) in
/-- Hatcher's `m(σ)`: the least `m` with `S ^ m σ` `𝒰`-small, enlarged to dominate the same
index of all faces of `σ`. -/
def smallIndex (𝒰 : Set (Set Y)) : ∀ n : ℕ, Simplex Y n → ℕ
  | 0, σ => smallIndex₀ R 𝒰 σ
  | n + 1, σ => max (smallIndex₀ R 𝒰 σ)
      (Finset.univ.sup fun i : Fin (n + 2) ↦ smallIndex 𝒰 n (σ.comp (face n i)))

/-- The least index `smallIndex₀ R 𝒰 σ` is at most `m(σ)`. -/
lemma smallIndex₀_le_smallIndex (𝒰 : Set (Set Y)) (n : ℕ) (σ : Simplex Y n) :
    smallIndex₀ R 𝒰 σ ≤ smallIndex R 𝒰 n σ := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- `m(σ)` dominates the index `m` of each face of `σ`. -/
lemma smallIndex_face_le (𝒰 : Set (Set Y)) (n : ℕ) (σ : Simplex Y (n + 1)) (i : Fin (n + 2)) :
    smallIndex R 𝒰 n (σ.comp (face n i)) ≤ smallIndex R 𝒰 (n + 1) σ :=
  le_max_of_le_right (Finset.le_sup (f := fun i : Fin (n + 2) ↦
    smallIndex R 𝒰 n (σ.comp (face n i))) (Finset.mem_univ i))

/-- For a simplex `σ` with image in `⋃₀ 𝒰`, `𝒰` open, `S ^ m σ` is `𝒰`-small whenever
`m(σ) ≤ m`. -/
lemma subdiv_pow_mem_small_of_le {n : ℕ} {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    {σ : Simplex Y n} (hσ : range σ ⊆ ⋃₀ 𝒰) {m : ℕ} (hm : smallIndex R 𝒰 n σ ≤ m) :
    (subdiv R n ^ m) (single σ 1) ∈ small R n 𝒰 := by
  classical
  have h := exists_subdiv_pow_mem_small (R := R) h𝒰 hσ
  have h0 : smallIndex₀ R 𝒰 σ = Nat.find h := by simp [smallIndex₀, h]
  have hle : Nat.find h ≤ m := h0 ▸ (smallIndex₀_le_smallIndex 𝒰 n σ).trans hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [add_comm, pow_add, Module.End.mul_apply]
  exact subdiv_pow_mem_small _ (Nat.find_spec h)

variable (R) in
/-- `D_m = ∑_{i < m} T S ^ i`. -/
def homotopyUpTo (m n : ℕ) : Chain R Y n →ₗ[R] Chain R Y (n + 1) :=
  ∑ i ∈ Finset.range m, subdivHomotopy R n ∘ₗ subdiv R n ^ i

/-- `∂ D_m + D_m ∂ = 1 - S ^ m`. -/
lemma bd_homotopyUpTo_add (m n : ℕ) (c : Chain R Y (n + 1)) :
    bd R (n + 1) (homotopyUpTo R m (n + 1) c) + homotopyUpTo R m n (bd R n c) =
      c - (subdiv R (n + 1) ^ m) c := by
  induction m with
  | zero => simp [homotopyUpTo]
  | succ m ih =>
    simp only [homotopyUpTo, Finset.sum_range_succ, LinearMap.add_apply, map_add,
      LinearMap.comp_apply] at ih ⊢
    rw [add_add_add_comm, ih, ← bd_subdiv_pow, bd_subdivHomotopy_add, pow_succ',
      Module.End.mul_apply]
    abel

/-- In degree `0`: `∂ D_m = 1 - S ^ m`. -/
lemma bd_homotopyUpTo_zero (m : ℕ) (c : Chain R Y 0) :
    bd R 0 (homotopyUpTo R m 0 c) = c - (subdiv R 0 ^ m) c := by
  induction m with
  | zero => simp [homotopyUpTo]
  | succ m ih =>
    simp only [homotopyUpTo, Finset.sum_range_succ, LinearMap.add_apply, map_add,
      LinearMap.comp_apply] at ih ⊢
    rw [ih, bd_subdivHomotopy_zero, pow_succ', Module.End.mul_apply]
    abel

/-- For a simplex `τ` with image in `⋃₀ 𝒰`, `𝒰` open, and `m(τ) ≤ m`, the difference
`D_m τ - D_{m(τ)} τ` is `𝒰`-small. -/
lemma homotopyUpTo_sub_mem_small {n : ℕ} {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U)
    {τ : Simplex Y n} (hτ : range τ ⊆ ⋃₀ 𝒰) {m : ℕ} (hm : smallIndex R 𝒰 n τ ≤ m) :
    homotopyUpTo R m n (single τ 1) - homotopyUpTo R (smallIndex R 𝒰 n τ) n (single τ 1) ∈
      small R (n + 1) 𝒰 := by
  simp only [homotopyUpTo]
  rw [← LinearMap.sub_apply, ← Finset.sum_Ico_eq_sub _ hm, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [LinearMap.comp_apply]
  exact subdivHomotopy_mem_small (subdiv_pow_mem_small_of_le h𝒰 hτ (Finset.mem_Ico.1 hi).1)

variable (R) in
/-- Hatcher's chain homotopy `D σ = D_{m(σ)} σ`. -/
def smallHomotopy (𝒰 : Set (Set Y)) (n : ℕ) : Chain R Y n →ₗ[R] Chain R Y (n + 1) :=
  linearCombination R fun σ ↦ homotopyUpTo R (smallIndex R 𝒰 n σ) n (single σ 1)

/-- On a single simplex, `D σ = D_{m(σ)} σ`. -/
lemma smallHomotopy_single (𝒰 : Set (Set Y)) (n : ℕ) (σ : Simplex Y n) :
    smallHomotopy R 𝒰 n (single σ 1) = homotopyUpTo R (smallIndex R 𝒰 n σ) n (single σ 1) := by
  simp [smallHomotopy]

variable (R) in
/-- Hatcher's chain map `ρ = 1 - ∂ D - D ∂`. -/
def smallChainMap (𝒰 : Set (Set Y)) : ∀ n : ℕ, Chain R Y n →ₗ[R] Chain R Y n
  | 0 => LinearMap.id - bd R 0 ∘ₗ smallHomotopy R 𝒰 0
  | n + 1 => LinearMap.id - bd R (n + 1) ∘ₗ smallHomotopy R 𝒰 (n + 1) -
      smallHomotopy R 𝒰 n ∘ₗ bd R n

/-- In degree `0`, `ρ = 1 - ∂ D`. -/
lemma smallChainMap_zero (𝒰 : Set (Set Y)) (c : Chain R Y 0) :
    smallChainMap R 𝒰 0 c = c - bd R 0 (smallHomotopy R 𝒰 0 c) := rfl

/-- In positive degree, `ρ = 1 - ∂ D - D ∂`. -/
lemma smallChainMap_succ (𝒰 : Set (Set Y)) (n : ℕ) (c : Chain R Y (n + 1)) :
    smallChainMap R 𝒰 (n + 1) c =
      c - bd R (n + 1) (smallHomotopy R 𝒰 (n + 1) c) - smallHomotopy R 𝒰 n (bd R n c) := rfl

/-- `ρ` is a chain map. -/
lemma bd_smallChainMap (𝒰 : Set (Set Y)) (n : ℕ) (c : Chain R Y (n + 1)) :
    bd R n (smallChainMap R 𝒰 (n + 1) c) = smallChainMap R 𝒰 n (bd R n c) := by
  rw [smallChainMap_succ, map_sub, map_sub, bd_bd, sub_zero]
  cases n with
  | zero => rfl
  | succ n => rw [smallChainMap_succ, bd_bd, map_zero, sub_zero]

/-- The theorem of small chains: `ρ` sends a simplex with image in `⋃₀ 𝒰` to a `𝒰`-small
chain. -/
lemma smallChainMap_single_mem_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U) (n : ℕ)
    {σ : Simplex Y n} (hσ : range σ ⊆ ⋃₀ 𝒰) : smallChainMap R 𝒰 n (single σ 1) ∈ small R n 𝒰 := by
  cases n with
  | zero =>
    rw [smallChainMap_zero, smallHomotopy_single, bd_homotopyUpTo_zero, sub_sub_cancel]
    exact subdiv_pow_mem_small_of_le h𝒰 hσ le_rfl
  | succ n =>
    have key : single σ 1 - bd R (n + 1) (homotopyUpTo R (smallIndex R 𝒰 (n + 1) σ) (n + 1)
        (single σ 1)) = (subdiv R (n + 1) ^ smallIndex R 𝒰 (n + 1) σ) (single σ 1) +
          homotopyUpTo R (smallIndex R 𝒰 (n + 1) σ) n (bd R n (single σ 1)) := by
      have h1 := bd_homotopyUpTo_add (R := R) (smallIndex R 𝒰 (n + 1) σ) n (single σ 1)
      rw [← sub_eq_iff_eq_add, sub_sub, h1, sub_sub_cancel]
    rw [smallChainMap_succ, smallHomotopy_single, key, add_sub_assoc]
    refine Submodule.add_mem _ (subdiv_pow_mem_small_of_le h𝒰 hσ le_rfl) ?_
    rw [bd_single, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul, map_smul, ← smul_sub, smallHomotopy_single]
    have hτ : range (σ.comp (face n i)) ⊆ ⋃₀ 𝒰 := fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
    exact Submodule.smul_mem _ _ (homotopyUpTo_sub_mem_small h𝒰 hτ (smallIndex_face_le 𝒰 n σ i))

/-- The theorem of small chains: `ρ` sends every chain of simplices with image in `⋃₀ 𝒰` to a
`𝒰`-small chain. -/
lemma smallChainMap_mem_small {𝒰 : Set (Set Y)} (h𝒰 : ∀ U ∈ 𝒰, IsOpen U) (n : ℕ)
    {c : Chain R Y n} (hc : c ∈ inside R n (⋃₀ 𝒰)) : smallChainMap R 𝒰 n c ∈ small R n 𝒰 :=
  VertexChain.mem_of_mem_supported _ _ (fun _ hσ ↦ smallChainMap_single_mem_small h𝒰 n hσ) hc

end small

section postcomp

variable {Z : Type*} [TopologicalSpace Z]

variable (R) in
/-- The push-forward `f_♯` of finite singular chains along a continuous map `f`:
post-composition `σ ↦ f ∘ σ` of simplices. -/
def postcomp (f : C(Y, Z)) (n : ℕ) : Chain R Y n →ₗ[R] Chain R Z n :=
  lmapDomain R R fun σ ↦ f.comp σ

/-- The push-forward of a single simplex: `f_♯ (a σ) = a (f ∘ σ)`. -/
lemma postcomp_single (f : C(Y, Z)) {n : ℕ} (σ : Simplex Y n) (a : R) :
    postcomp R f n (single σ a) = single (f.comp σ) a := by
  simp [postcomp]

/-- Push-forward commutes with the boundary. -/
lemma postcomp_bd (f : C(Y, Z)) {n : ℕ} (c : Chain R Y (n + 1)) :
    postcomp R f n (bd R n c) = bd R n (postcomp R f (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, postcomp_single]
    rw [bd_single, bd_single, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [map_smul, postcomp_single]
    rfl

/-- Push-forward is functorial: `g_♯ f_♯ = (g ∘ f)_♯`. -/
lemma postcomp_comp {W : Type*} [TopologicalSpace W] (f : C(Y, Z)) (g : C(Z, W)) (n : ℕ)
    (c : Chain R Y n) : postcomp R g n (postcomp R f n c) = postcomp R (g.comp f) n c := by
  simp only [postcomp, lmapDomain_apply, ← mapDomain_comp]
  rfl

/-- Push-forward along the identity is the identity. -/
lemma postcomp_id (n : ℕ) (c : Chain R Y n) : postcomp R (ContinuousMap.id Y) n c = c := by
  simp only [postcomp, lmapDomain_apply]
  exact mapDomain_id

/-- Push-forward along `f` sends chains in `U` to chains in any `V` with `f (U) ⊆ V`. -/
lemma postcomp_mem_inside (f : C(Y, Z)) {n : ℕ} {U : Set Y} {V : Set Z} (hUV : MapsTo f U V)
    {c : Chain R Y n} (hc : c ∈ inside R n U) : postcomp R f n c ∈ inside R n V :=
  VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
    rw [postcomp_single]
    refine single_mem_supported R _ ?_
    rintro _ ⟨t, rfl⟩
    exact hUV (hσ ⟨t, rfl⟩)) hc

end postcomp

section stdSimplexHomeo

open Convexity

variable (ι : Type*) [Fintype ι]

/-- The standard simplex `stdSimplex ℝ ι ⊆ ι → ℝ` is homeomorphic to `StdSimplex ℝ ι`. -/
def stdSimplexHomeo : stdSimplex ℝ ι ≃ₜ StdSimplex ℝ ι where
  toFun t :=
    { weights := Finsupp.equivFunOnFinite.symm t.1
      nonneg := fun i ↦ t.2.1 i
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
        exact t.2.2 }
  invFun s := ⟨s.weights, fun i ↦ s.weights_nonneg i, s.total_of_fintype⟩
  left_inv _ := rfl
  right_inv s := StdSimplex.ext (Finsupp.equivFunOnFinite_symm_coe s.weights)
  continuous_toFun := by
    rw [(StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ ι).isInducing.continuous_iff]
    exact continuous_subtype_val
  continuous_invFun :=
    (StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ ι).continuous.subtype_mk _

variable {ι}

@[simp]
lemma stdSimplexHomeo_apply_weights (t : stdSimplex ℝ ι) (i : ι) :
    (stdSimplexHomeo ι t).weights i = t i :=
  rfl

@[simp]
lemma stdSimplexHomeo_symm_apply (s : StdSimplex ℝ ι) (i : ι) :
    (stdSimplexHomeo ι).symm s i = s.weights i :=
  rfl

/-- The homeomorphism `stdSimplexHomeo` commutes with the maps induced by `f : ι → κ`. -/
lemma stdSimplexHomeo_map {κ : Type*} [Fintype κ] (f : ι → κ) (t : stdSimplex ℝ ι) :
    stdSimplexHomeo κ (stdSimplex.map f t) = StdSimplex.map f (stdSimplexHomeo ι t) :=
  StdSimplex.ext (Finsupp.ext fun k ↦ by
    classical
    rw [stdSimplexHomeo_apply_weights, StdSimplex.weights_map, Finsupp.mapDomain_apply]
    change FunOnFinite.linearMap ℝ ℝ f t k = _
    rw [FunOnFinite.linearMap_apply_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [Finsupp.single_apply, Finset.sum_filter])

lemma stdSimplexHomeo_symm_map {κ : Type*} [Fintype κ] (f : ι → κ) (s : StdSimplex ℝ ι) :
    (stdSimplexHomeo κ).symm (StdSimplex.map f s) = stdSimplex.map f ((stdSimplexHomeo ι).symm s) :=
  (stdSimplexHomeo κ).injective (by
    rw [Homeomorph.apply_symm_apply, stdSimplexHomeo_map, Homeomorph.apply_symm_apply])

/-- The homeomorphism `stdSimplexHomeo` sends the vertex `x` to the point mass at `x`. -/
lemma stdSimplexHomeo_vertex [DecidableEq ι] (x : ι) :
    stdSimplexHomeo ι (stdSimplex.vertex x) = StdSimplex.single x := by
  ext i
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma stdSimplexHomeo_symm_single [DecidableEq ι] (x : ι) :
    (stdSimplexHomeo ι).symm (StdSimplex.single x) = stdSimplex.vertex x := by
  rw [← stdSimplexHomeo_vertex, Homeomorph.symm_apply_apply]

/-- The homeomorphism `stdSimplexHomeo` intertwines the face inclusions `face n i` with the maps
induced by `i.succAbove`. -/
lemma stdSimplexHomeo_face (n : ℕ) (i : Fin (n + 2)) (t : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplexHomeo (Fin (n + 2)) (face n i t) = StdSimplex.map i.succAbove (stdSimplexHomeo _ t) :=
  stdSimplexHomeo_map _ _

lemma stdSimplexHomeo_symm_face (n : ℕ) (i : Fin (n + 2)) (s : StdSimplex ℝ (Fin (n + 1))) :
    (stdSimplexHomeo (Fin (n + 2))).symm (StdSimplex.map i.succAbove s) =
      face n i ((stdSimplexHomeo _).symm s) :=
  stdSimplexHomeo_symm_map _ _

end stdSimplexHomeo

end SingularChain

end MMP
