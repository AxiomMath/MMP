module

public import MMP.AlgebraicTopology.BorelMoore.Restriction

/-!
# Iterated restriction of singular simplices (Fulton, §19.1)

Let `U' ⊆ U` be open subsets of a Hausdorff space `Y`. Restricting a singular simplex `σ` of `Y`
first to `U` and then to `U'` does not give the restriction of `σ` to `U'`, but the two differ
by the boundary of a homotopy (Borel–Moore, §3). With `ρ_N = 1 - ∂ D_N - D_N ∂` the chain maps of
the subdivision towards `U`, `X_N` the bad chains, and `p'`, `ρ'_M`, `X'_M` the corresponding
operators for `U'`, the identity `σ = ρ_N σ + ∂ D_N σ + D_N ∂ σ` gives
`p' ρ'_M σ = p' ρ'_M (p ρ_N σ) + ∂ (p' ρ'_M D_N σ) + p' ρ'_M D_N ∂ σ`
`+ p' ρ'_M X_N σ + p' ∂ X'_M D_N σ`.
Near a compact subset of `U'` the last two terms vanish for large `N` and `M`, and the others
are the stage `(N, M)` approximations of `σ|_{U'}`, of `(σ|_U)|_{U'}`, of `∂ (h σ)` and of
`h (∂ σ)`, where `h σ = ∑_i (T X_i σ)|_{U'}` (`T` the subdivision homotopy). This gives the
homotopy identity `σ|_{U'} - (σ|_U)|_{U'} = ∂ (h σ) + h (∂ σ)` coefficientwise.

## Main definitions

* `MMP.SingularChain.restrFin`: the coefficients of the restriction of a finite
  chain.
* `MMP.SingularChain.compCoeff`: the coefficients of `(σ|_U)|_{U'}`.
* `MMP.SingularChain.homCoeff`: the coefficients of the homotopy `h σ`.

## Main results

* `MMP.SingularChain.restrCoeff_sub_compCoeff_succ`,
  `MMP.SingularChain.restrCoeff_sub_compCoeff_zero`: the homotopy identity.

## References

* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

section restrFin

variable (R) (U : Set Y)

/-- The coefficient of `ω` in the restriction to `U` of a finite chain `c`: `∑_ν c_ν (ν|_U)_ω`. -/
def restrFin {n : ℕ} (c : Chain R Y n) (ω : Simplex Y n) : R :=
  c.sum fun ν a ↦ a * restrCoeff R U ν ω

/-- The coefficient of `τ` in the iterated restriction `(σ|_U)|_{U'}`. -/
def compCoeff (U' : Set Y) {n : ℕ} (σ τ : Simplex Y n) : R :=
  ∑ᶠ ν, restrCoeff R U σ ν * restrCoeff R U' ν τ

/-- The coefficient of the `(n + 1)`-simplex `ω` in the homotopy `h σ = ∑_i (T X_i σ)|_{U'}`
between `σ|_{U'}` and `(σ|_U)|_{U'}`. -/
def homCoeff (U' : Set Y) {n : ℕ} (σ : Simplex Y n) (ω : Simplex Y (n + 1)) : R :=
  ∑ᶠ i : ℕ, restrFin R U' (subdivHomotopy R n (badChain R U i n (single σ 1))) ω

variable {R U}

/-- The restriction coefficients of a finite chain are additive in the chain. -/
lemma restrFin_add {n : ℕ} (c d : Chain R Y n) (ω : Simplex Y n) :
    restrFin R U (c + d) ω = restrFin R U c ω + restrFin R U d ω :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) fun _ _ _ ↦ add_mul _ _ _

/-- The restriction coefficients of `a • c` are `a` times those of `c`. -/
lemma restrFin_smul {n : ℕ} (a : R) (c : Chain R Y n) (ω : Simplex Y n) :
    restrFin R U (a • c) ω = a * restrFin R U c ω := by
  rw [restrFin, restrFin, Finsupp.sum_smul_index (fun _ ↦ zero_mul _), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_assoc _ _ _

/-- The restriction coefficients of a finite sum of chains are the sums of their coefficients. -/
lemma restrFin_sum {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → Chain R Y n) (ω : Simplex Y n) :
    restrFin R U (∑ i ∈ s, c i) ω = ∑ i ∈ s, restrFin R U (c i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [restrFin]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, restrFin_add, ih]

/-- The restriction coefficients of the chain `single ν a` are `a` times those of `ν|_U`. -/
lemma restrFin_single {n : ℕ} (ν : Simplex Y n) (a : R) (ω : Simplex Y n) :
    restrFin R U (single ν a) ω = a * restrCoeff R U ν ω :=
  Finsupp.sum_single_index (zero_mul _)

/-- A simplex meeting `W` does not lie in a set `V` disjoint from `W`. -/
lemma not_range_subset_of_disjoint {m : ℕ} {V W : Set Y} (hVW : Disjoint V W) {ω : Simplex Y m}
    (hω : (range ω ∩ W).Nonempty) : ¬range ω ⊆ V := fun h ↦ by
  obtain ⟨y, hy, hyW⟩ := hω
  exact Set.disjoint_left.1 hVW (h hy) hyW

/-- The restriction to `U` of a chain inside `V` has zero coefficient at every simplex meeting
a set `W` disjoint from `V`. -/
lemma restrFin_eq_zero_of_mem_inside {n : ℕ} {V W : Set Y} (hVW : Disjoint V W)
    {c : Chain R Y n} (hc : c ∈ inside R n V) {ω : Simplex Y n} (hω : (range ω ∩ W).Nonempty) :
    restrFin R U c ω = 0 := by
  refine Finset.sum_eq_zero fun ν hν ↦ ?_
  change c ν * restrCoeff R U ν ω = 0
  by_cases h : restrCoeff R U ν ω = 0
  · rw [h, mul_zero]
  · exact absurd (((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_left).trans
      (hc (Finset.mem_coe.2 hν))) (not_range_subset_of_disjoint hVW hω)

end restrFin

section stable

variable [T2Space Y] {U : Set Y}

/-- Near `W`, disjoint from a neighbourhood `V` of the points of `ν` outside `U`, the
coefficients of `ν|_U` are those of `p ρ_M ν` for all large `M`. -/
lemma exists_restrCoeff_eq_goodPart_of_disjoint (hU : IsOpen U) {n : ℕ} (ν : Simplex Y n)
    {V W : Set Y} (hV : IsOpen V) (hVW : Disjoint V W) (hνV : range ν ∩ Uᶜ ⊆ V) :
    ∃ M, ∀ m ≥ M, ∀ ω : Simplex Y n, (range ω ∩ W).Nonempty →
      restrCoeff R U ν ω = goodPart R U m ν ω := by
  obtain ⟨M, hM⟩ := eventually_goodPart_sub_mem_inside (R := R) hU ν hV hνV
  have key : ∀ m ≥ M, ∀ ω : Simplex Y n, (range ω ∩ W).Nonempty →
      goodPart R U m ν ω = goodPart R U M ν ω := by
    intro m hm ω hω
    have h0 := eq_zero_of_mem_inside (goodProj_mem_inside (U := U) (hM m hm).1)
      (not_range_subset_of_disjoint hVW hω)
    rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at h0
    exact h0
  refine ⟨M, fun m hm ω hω ↦ restrCoeff_eq fun N hN ↦ ?_⟩
  rw [key N (hm.trans hN) ω hω, key m hm ω hω]

omit [T2Space Y] in
/-- The good part of `ρ_M` of a finite chain is the sum of the good parts of its simplices. -/
lemma goodProj_towardsChainMap_eq_sum (m : ℕ) {n : ℕ} (c : Chain R Y n) :
    goodProj R U n (towardsChainMap R U m n c) = c.sum fun ν a ↦ a • goodPart R U m ν := by
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [map_finsuppSum, map_finsuppSum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  simp only
  rw [← smul_single_one, map_smul, map_smul, goodPart]

/-- For a finite chain `c` whose simplices have their points outside `U` in `V`, near `W` the
coefficients of `c|_U` are those of `p ρ_M c` for all large `M`. -/
lemma exists_restrFin_eq (hU : IsOpen U) {n : ℕ} (c : Chain R Y n) {V W : Set Y}
    (hV : IsOpen V) (hVW : Disjoint V W) (hc : ∀ ν ∈ c.support, range ν ∩ Uᶜ ⊆ V) :
    ∃ M, ∀ m ≥ M, ∀ ω : Simplex Y n, (range ω ∩ W).Nonempty →
      restrFin R U c ω = goodProj R U n (towardsChainMap R U m n c) ω := by
  have h : ∀ ν ∈ c.support, ∃ M, ∀ m ≥ M, ∀ ω : Simplex Y n, (range ω ∩ W).Nonempty →
      restrCoeff R U ν ω = goodPart R U m ν ω := fun ν hν ↦
    exists_restrCoeff_eq_goodPart_of_disjoint hU ν hV hVW (hc ν hν)
  choose! Mf hMf using h
  refine ⟨c.support.sup Mf, fun m hm ω hω ↦ ?_⟩
  rw [goodProj_towardsChainMap_eq_sum, restrFin, Finsupp.sum, Finsupp.sum,
    Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun ν hν ↦ ?_
  rw [Finsupp.smul_apply, smul_eq_mul,
    hMf ν hν m ((Finset.le_sup (f := Mf) hν).trans hm) ω hω]

/-- The bad chains `X_M c` of a finite chain lie in `V` for all large `M`. -/
lemma exists_badChain_mem_inside (hU : IsOpen U) {n : ℕ} (c : Chain R Y n) {V : Set Y}
    (hV : IsOpen V) (hc : ∀ ν ∈ c.support, range ν ∩ Uᶜ ⊆ V) :
    ∃ M, ∀ m ≥ M, badChain R U m n c ∈ inside R n V := by
  have h : ∀ ν ∈ c.support, ∃ M, ∀ m ≥ M, badChain R U m n (single ν 1) ∈ inside R n V :=
    fun ν hν ↦ by
      obtain ⟨M, hM⟩ := eventually_goodPart_sub_mem_inside (R := R) hU ν hV (hc ν hν)
      exact ⟨M, fun m hm ↦ (hM m hm).2⟩
  choose! Mf hMf using h
  refine ⟨c.support.sup Mf, fun m hm ↦ ?_⟩
  conv => enter [2]; rw [← Finsupp.sum_single c]
  rw [map_finsuppSum]
  refine Submodule.sum_mem _ fun ν hν ↦ ?_
  simp only
  rw [← smul_single_one, map_smul]
  exact Submodule.smul_mem _ _ (hMf ν hν m ((Finset.le_sup (f := Mf) hν).trans hm))

omit [T2Space Y] in
/-- If `c` is a chain inside `A` and `A ∩ Uᶜ ⊆ V`, then every simplex of `c` has its points
outside `U` in `V`. -/
lemma support_subset_of_mem_inside {n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) {V : Set Y} (hA : A ∩ Uᶜ ⊆ V) :
    ∀ ν ∈ c.support, range ν ∩ Uᶜ ⊆ V := fun ν hν ↦
  (inter_subset_inter_left _ (hc (Finset.mem_coe.2 hν))).trans hA

end stable

section iterated

variable [T2Space Y] {U U' : Set Y}

/-- Near `W`, the homotopy coefficients `h σ` are those of the restriction to `U'` of `D_k σ`, for
all large `k`. -/
lemma exists_homCoeff_eq (hU : IsOpen U) (hUU' : U' ⊆ U) {n : ℕ} (σ : Simplex Y n)
    {V W : Set Y} (hV : IsOpen V) (hVW : Disjoint V W) (hσV : range σ ∩ U'ᶜ ⊆ V) :
    ∃ k₀, ∀ k ≥ k₀, (∀ ω : Simplex Y (n + 1), (range ω ∩ W).Nonempty →
      homCoeff R U U' σ ω = restrFin R U' (towardsHomotopy R U k n (single σ 1)) ω) ∧
      badChain R U k n (single σ 1) ∈ inside R n V := by
  have hσU : range σ ∩ Uᶜ ⊆ V :=
    (inter_subset_inter_right _ (compl_subset_compl.2 hUU')).trans hσV
  obtain ⟨k₀, hk₀⟩ := eventually_goodPart_sub_mem_inside (R := R) hU σ hV hσU
  refine ⟨k₀, fun k hk ↦ ⟨fun ω hω ↦ ?_, (hk₀ k hk).2⟩⟩
  have hzero : ∀ i ≥ k, restrFin R U' (subdivHomotopy R n (badChain R U i n (single σ 1))) ω =
      0 := fun i hi ↦ restrFin_eq_zero_of_mem_inside hVW
    (subdivHomotopy_mem_inside (hk₀ i (hk.trans hi)).2) hω
  rw [homCoeff, finsum_eq_sum_of_support_subset (s := Finset.range k) _ (fun i hi ↦ by
    rw [Finset.coe_range, mem_Iio]
    by_contra h
    exact hi (hzero i (not_lt.1 h))), towardsHomotopy, LinearMap.sum_apply, restrFin_sum]
  rfl

/-- Near `W`, the coefficients of `(σ|_U)|_{U'}` are those of the restriction to `U'` of
`p ρ_k σ`, for all large `k`. -/
lemma exists_compCoeff_eq (hU : IsOpen U) (hUU' : U' ⊆ U) {n : ℕ} (σ : Simplex Y n)
    {V W : Set Y} (hV : IsOpen V) (hVW : Disjoint V W) (hσV : range σ ∩ U'ᶜ ⊆ V) :
    ∃ k₀, ∀ k ≥ k₀, ∀ τ : Simplex Y n, (range τ ∩ W).Nonempty →
      compCoeff R U U' σ τ = restrFin R U' (goodPart R U k σ) τ := by
  have hσU : range σ ∩ Uᶜ ⊆ V :=
    (inter_subset_inter_right _ (compl_subset_compl.2 hUU')).trans hσV
  obtain ⟨k₀, hk₀⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := R) hU σ hV hVW hσU
  refine ⟨k₀, fun k hk τ hτ ↦ ?_⟩
  have hterm : ∀ ν, restrCoeff R U σ ν * restrCoeff R U' ν τ =
      goodPart R U k σ ν * restrCoeff R U' ν τ := fun ν ↦ by
    by_cases h : restrCoeff R U' ν τ = 0
    · rw [h, mul_zero, mul_zero]
    · obtain ⟨y, hy, hyW⟩ := hτ
      rw [hk₀ k hk ν ⟨y, ((range_subset_of_restrCoeff_ne_zero h).trans inter_subset_left) hy,
        hyW⟩]
  rw [compCoeff, finsum_congr hterm, restrFin, Finsupp.sum,
    finsum_eq_sum_of_support_subset (s := (goodPart R U k σ).support) _ (fun ν hν ↦ by
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hν (by simp only [h0, zero_mul]))]

omit [T2Space Y] in
/-- The stage identity: `p' ρ'_M σ = p' ρ'_M (p ρ_N σ) + ∂ (p' ρ'_M D_N σ) + p' ρ'_M D_N ∂ σ +
p' ρ'_M X_N σ + p' ∂ X'_M D_N σ` in degree `n + 1`. -/
lemma goodProj_towardsChainMap_stage_succ (k m n : ℕ) (c : Chain R Y (n + 1)) :
    goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1) c) =
      goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1)
          (goodProj R U (n + 1) (towardsChainMap R U k (n + 1) c))) +
        bd R (n + 1) (goodProj R U' (n + 2) (towardsChainMap R U' m (n + 2)
          (towardsHomotopy R U k (n + 1) c))) +
        goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1)
          (towardsHomotopy R U k n (bd R n c))) +
        goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1) (badChain R U k (n + 1) c)) +
        goodProj R U' (n + 1) (bd R (n + 1) (badChain R U' m (n + 2)
          (towardsHomotopy R U k (n + 1) c))) := by
  set y := towardsChainMap R U' m (n + 2) (towardsHomotopy R U k (n + 1) c)
  have hc : c = goodProj R U (n + 1) (towardsChainMap R U k (n + 1) c) +
      badChain R U k (n + 1) c + bd R (n + 1) (towardsHomotopy R U k (n + 1) c) +
      towardsHomotopy R U k n (bd R n c) := by
    rw [← badProj_towardsChainMap, goodProj_add_badProj, towardsChainMap_succ_apply]
    abel
  have hy : goodProj R U' (n + 1) (bd R (n + 1) y) = bd R (n + 1) (goodProj R U' (n + 2) y) +
      goodProj R U' (n + 1) (bd R (n + 1) (badChain R U' m (n + 2)
        (towardsHomotopy R U k (n + 1) c))) := by
    rw [← badProj_towardsChainMap]
    conv_lhs => rw [← goodProj_add_badProj (U := U') y]
    rw [map_add, map_add]
    congr 1
    have h := goodProj_add_badProj (U := U') (bd R (n + 1) (goodProj R U' (n + 2) y))
    rwa [badProj_eq_zero_of_mem_inside (bd_mem_inside (goodProj_mem_inside_self _)),
      add_zero] at h
  conv_lhs => rw [hc]
  rw [map_add, map_add, map_add, map_add, map_add, map_add, ← bd_towardsChainMap, hy]
  abel

omit [T2Space Y] in
/-- The stage identity in degree `0`. -/
lemma goodProj_towardsChainMap_stage_zero (k m : ℕ) (c : Chain R Y 0) :
    goodProj R U' 0 (towardsChainMap R U' m 0 c) =
      goodProj R U' 0 (towardsChainMap R U' m 0
          (goodProj R U 0 (towardsChainMap R U k 0 c))) +
        bd R 0 (goodProj R U' 1 (towardsChainMap R U' m 1 (towardsHomotopy R U k 0 c))) +
        goodProj R U' 0 (towardsChainMap R U' m 0 (badChain R U k 0 c)) +
        goodProj R U' 0 (bd R 0 (badChain R U' m 1 (towardsHomotopy R U k 0 c))) := by
  set y := towardsChainMap R U' m 1 (towardsHomotopy R U k 0 c)
  have hc : c = goodProj R U 0 (towardsChainMap R U k 0 c) +
      badChain R U k 0 c + bd R 0 (towardsHomotopy R U k 0 c) := by
    rw [← badProj_towardsChainMap, goodProj_add_badProj, towardsChainMap_zero_apply]
    abel
  have hy : goodProj R U' 0 (bd R 0 y) = bd R 0 (goodProj R U' 1 y) +
      goodProj R U' 0 (bd R 0 (badChain R U' m 1 (towardsHomotopy R U k 0 c))) := by
    rw [← badProj_towardsChainMap]
    conv_lhs => rw [← goodProj_add_badProj (U := U') y]
    rw [map_add, map_add]
    congr 1
    have h := goodProj_add_badProj (U := U') (bd R 0 (goodProj R U' 1 y))
    rwa [badProj_eq_zero_of_mem_inside (bd_mem_inside (goodProj_mem_inside_self _)),
      add_zero] at h
  conv_lhs => rw [hc]
  rw [map_add, map_add, map_add, map_add, ← bd_towardsChainMap, hy]
  abel

end iterated

section homotopy

variable [T2Space Y] {U U' : Set Y}

omit [T2Space Y] in
/-- If `τ = ω ∘ f` meets `W`, then so does `ω`. -/
lemma range_inter_nonempty_of_comp {a b : ℕ} {τ : Simplex Y a} {W : Set Y}
    (hτ : (range τ ∩ W).Nonempty) {ω : Simplex Y b}
    {f : C(stdSimplex ℝ (Fin (a + 1)), stdSimplex ℝ (Fin (b + 1)))} (h : ω.comp f = τ) :
    (range ω ∩ W).Nonempty := by
  obtain ⟨y, ⟨t, rfl⟩, hyW⟩ := hτ
  exact ⟨ω (f t), ⟨_, rfl⟩, by rw [← h] at hyW; exact hyW⟩

omit [T2Space Y] in
open Classical in
/-- The boundary of a chain `e`, near `W`, from the coefficients of `e` near `W`. -/
lemma bd_apply_eq_finsum {n : ℕ} (e : Chain R Y (n + 1)) (g : Simplex Y (n + 1) → R)
    {W : Set Y} (τ : Simplex Y n) (hτ : (range τ ∩ W).Nonempty)
    (hg : ∀ ω : Simplex Y (n + 1), (range ω ∩ W).Nonempty → g ω = e ω) :
    ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) *
      ∑ᶠ ω : Simplex Y (n + 1), (if ω.comp (face n i) = τ then g ω else 0) = bd R n e τ := by
  rw [bd_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  have hterm : ∀ ω : Simplex Y (n + 1), (if ω.comp (face n i) = τ then g ω else 0) =
      if ω.comp (face n i) = τ then e ω else 0 := fun ω ↦ by
    split_ifs with h
    · exact hg ω (range_inter_nonempty_of_comp hτ h)
    · rfl
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset (s := e.support) _ (fun ω hω ↦ by
    rw [Function.mem_support] at hω
    split_ifs at hω
    · exact Finsupp.mem_support_iff.2 hω
    · exact absurd rfl hω)]

open Classical in
/-- **The homotopy identity, degree `n + 1`**: for a simplex `τ` of `U'`,
`(σ|_{U'})_τ - ((σ|_U)|_{U'})_τ = (∂ (h σ))_τ + (h (∂ σ))_τ`. -/
theorem restrCoeff_sub_compCoeff_succ (hU : IsOpen U) (hU' : IsOpen U') (hUU' : U' ⊆ U)
    {n : ℕ} (σ τ : Simplex Y (n + 1)) (hτ : range τ ⊆ U') :
    restrCoeff R U' σ τ - compCoeff R U U' σ τ =
      ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω : Simplex Y (n + 2),
          (if ω.comp (face (n + 1) i) = τ then homCoeff R U U' σ ω else 0) +
        ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * homCoeff R U U' (σ.comp (face n i)) τ := by
  obtain ⟨V, W, hV, -, hσV, hKW, hVW⟩ :=
    separatedNhds_range_inter_compl hU' σ (isCompact_range τ.continuous) hτ
  have hτW : (range τ ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hKW ⟨_, rfl⟩⟩
  have hnot : ¬range τ ⊆ V := not_range_subset_of_disjoint hVW hτW
  have hface : ∀ i : Fin (n + 2), range (σ.comp (face n i)) ∩ U'ᶜ ⊆ V :=
    fun i _ ⟨⟨t, ht⟩, hx⟩ ↦ hσV ⟨⟨_, ht⟩, hx⟩
  obtain ⟨kσ, hkσ⟩ := exists_homCoeff_eq (R := R) hU hUU' σ hV hVW hσV
  choose kf hkf using fun i ↦ exists_homCoeff_eq (R := R) hU hUU' (σ.comp (face n i)) hV hVW
    (hface i)
  obtain ⟨kc, hkc⟩ := exists_compCoeff_eq (R := R) hU hUU' σ hV hVW hσV
  set k := max kσ (max kc (Finset.univ.sup kf))
  have hk1 : kσ ≤ k := le_max_left _ _
  have hk2 : kc ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hk3 : ∀ i, kf i ≤ k := fun i ↦ (Finset.le_sup (f := kf) (Finset.mem_univ i)).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  set c₂ := goodPart R U k σ with hc₂
  set c₃ := towardsHomotopy R U k (n + 1) (single σ 1) with hc₃
  set c₄ := towardsHomotopy R U k n (bd R n (single σ 1)) with hc₄
  have hA₂ : (range σ ∩ U) ∩ U'ᶜ ⊆ V := (inter_subset_inter_left _ inter_subset_left).trans hσV
  obtain ⟨m₁, hm₁⟩ := exists_restrFin_eq (R := R) hU' (single σ 1) hV hVW
    (support_subset_of_mem_inside (single_mem_inside_range σ) hσV)
  obtain ⟨m₂, hm₂⟩ := exists_restrFin_eq (R := R) hU' c₂ hV hVW
    (support_subset_of_mem_inside (goodPart_mem_inside σ) hA₂)
  obtain ⟨m₃, hm₃⟩ := exists_restrFin_eq (R := R) hU' c₃ hV hVW
    (support_subset_of_mem_inside (towardsHomotopy_mem_inside (single_mem_inside_range σ)) hσV)
  obtain ⟨m₄, hm₄⟩ := exists_restrFin_eq (R := R) hU' c₄ hV hVW
    (support_subset_of_mem_inside
      (towardsHomotopy_mem_inside (bd_mem_inside (single_mem_inside_range σ))) hσV)
  obtain ⟨m₅, hm₅⟩ := exists_badChain_mem_inside (R := R) hU' c₃ hV
    (support_subset_of_mem_inside (towardsHomotopy_mem_inside (single_mem_inside_range σ)) hσV)
  set m := max (max m₁ m₂) (max (max m₃ m₄) m₅)
  have e₁ : restrCoeff R U' σ τ =
      goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1) (single σ 1)) τ := by
    rw [← hm₁ m (by omega) τ hτW, restrFin_single, one_mul]
  have e₂ : compCoeff R U U' σ τ =
      goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1) c₂) τ := by
    rw [hkc k hk2 τ hτW, hm₂ m (by omega) τ hτW]
  have e₃ : ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω : Simplex Y (n + 2),
      (if ω.comp (face (n + 1) i) = τ then homCoeff R U U' σ ω else 0) =
      bd R (n + 1) (goodProj R U' (n + 2) (towardsChainMap R U' m (n + 2) c₃)) τ :=
    bd_apply_eq_finsum _ _ τ hτW fun ω hω ↦ by
      rw [(hkσ k hk1).1 ω hω, hm₃ m (by omega) ω hω]
  have e₄ : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * homCoeff R U U' (σ.comp (face n i)) τ =
      goodProj R U' (n + 1) (towardsChainMap R U' m (n + 1) c₄) τ := by
    rw [← hm₄ m (by omega) τ hτW, hc₄, bd_single, map_sum, restrFin_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, restrFin_smul, (hkf i k (hk3 i)).1 τ hτW]
  have hst := congrArg (fun c : Chain R Y (n + 1) ↦ c τ)
    (goodProj_towardsChainMap_stage_succ (U := U) (U' := U') k m n (single σ 1))
  simp only [Finsupp.add_apply] at hst
  have z₁ := eq_zero_of_mem_inside (goodProj_mem_inside (U := U')
    (towardsChainMap_mem_inside (N := m) (U := U') (hkσ k hk1).2)) hnot
  have z₂ := eq_zero_of_mem_inside (goodProj_mem_inside (U := U')
    (bd_mem_inside (hm₅ m (by omega)))) hnot
  rw [e₁, e₂, e₃, e₄, hst, z₁, z₂, hc₂, hc₃, hc₄, goodPart]
  ring

open Classical in
/-- **The homotopy identity, degree `0`**: for a point-simplex `τ` of `U'`,
`(σ|_{U'})_τ - ((σ|_U)|_{U'})_τ = (∂ (h σ))_τ`. -/
theorem restrCoeff_sub_compCoeff_zero (hU : IsOpen U) (hU' : IsOpen U') (hUU' : U' ⊆ U)
    (σ τ : Simplex Y 0) (hτ : range τ ⊆ U') :
    restrCoeff R U' σ τ - compCoeff R U U' σ τ =
      ∑ i : Fin (0 + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω : Simplex Y (0 + 1),
          (if ω.comp (face 0 i) = τ then homCoeff R U U' σ ω else 0) := by
  obtain ⟨V, W, hV, -, hσV, hKW, hVW⟩ :=
    separatedNhds_range_inter_compl hU' σ (isCompact_range τ.continuous) hτ
  have hτW : (range τ ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hKW ⟨_, rfl⟩⟩
  have hnot : ¬range τ ⊆ V := not_range_subset_of_disjoint hVW hτW
  obtain ⟨kσ, hkσ⟩ := exists_homCoeff_eq (R := R) hU hUU' σ hV hVW hσV
  obtain ⟨kc, hkc⟩ := exists_compCoeff_eq (R := R) hU hUU' σ hV hVW hσV
  set k := max kσ kc
  set c₂ := goodPart R U k σ with hc₂
  set c₃ := towardsHomotopy R U k 0 (single σ 1) with hc₃
  have hA₂ : (range σ ∩ U) ∩ U'ᶜ ⊆ V := (inter_subset_inter_left _ inter_subset_left).trans hσV
  obtain ⟨m₁, hm₁⟩ := exists_restrFin_eq (R := R) hU' (single σ 1) hV hVW
    (support_subset_of_mem_inside (single_mem_inside_range σ) hσV)
  obtain ⟨m₂, hm₂⟩ := exists_restrFin_eq (R := R) hU' c₂ hV hVW
    (support_subset_of_mem_inside (goodPart_mem_inside σ) hA₂)
  obtain ⟨m₃, hm₃⟩ := exists_restrFin_eq (R := R) hU' c₃ hV hVW
    (support_subset_of_mem_inside (towardsHomotopy_mem_inside (single_mem_inside_range σ)) hσV)
  obtain ⟨m₅, hm₅⟩ := exists_badChain_mem_inside (R := R) hU' c₃ hV
    (support_subset_of_mem_inside (towardsHomotopy_mem_inside (single_mem_inside_range σ)) hσV)
  set m := max (max m₁ m₂) (max m₃ m₅)
  have e₁ : restrCoeff R U' σ τ =
      goodProj R U' 0 (towardsChainMap R U' m 0 (single σ 1)) τ := by
    rw [← hm₁ m (by omega) τ hτW, restrFin_single, one_mul]
  have e₂ : compCoeff R U U' σ τ = goodProj R U' 0 (towardsChainMap R U' m 0 c₂) τ := by
    rw [hkc k (le_max_right _ _) τ hτW, hm₂ m (by omega) τ hτW]
  have e₃ :=
    bd_apply_eq_finsum (n := 0) (goodProj R U' 1 (towardsChainMap R U' m 1 c₃))
      (homCoeff R U U' σ) τ hτW fun ω hω ↦ by
      rw [(hkσ k (le_max_left _ _)).1 ω hω, hm₃ m (by omega) ω hω]
  have hst := congrArg (fun c : Chain R Y 0 ↦ c τ)
    (goodProj_towardsChainMap_stage_zero (U := U) (U' := U') k m (single σ 1))
  simp only [Finsupp.add_apply] at hst
  have z₁ := eq_zero_of_mem_inside (goodProj_mem_inside (U := U')
    (towardsChainMap_mem_inside (N := m) (U := U') (hkσ k (le_max_left _ _)).2)) hnot
  have z₂ := eq_zero_of_mem_inside (goodProj_mem_inside (U := U')
    (bd_mem_inside (hm₅ m (by omega)))) hnot
  trans bd R 0 (goodProj R U' 1 (towardsChainMap R U' m 1 c₃)) τ
  · rw [e₁, e₂, hst, z₁, z₂, hc₂, hc₃]
    simp only [goodPart]
    ring
  · convert e₃.symm

end homotopy

section admissible

variable {U U' : Set Y}

/-- A simplex with nonzero coefficient in the restriction to `U'` of a chain inside `A` lies in
`A ∩ U'`. -/
lemma range_subset_of_restrFin_ne_zero {n : ℕ} {A : Set Y} {c : Chain R Y n}
    (hc : c ∈ inside R n A) {ω : Simplex Y n} (h : restrFin R U' c ω ≠ 0) :
    range ω ⊆ A ∩ U' := by
  obtain ⟨ν, hν, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h' : restrCoeff R U' ν ω ≠ 0 := fun h0 ↦ hne (by simp only [h0, mul_zero])
  have := range_subset_of_restrCoeff_ne_zero h'
  exact subset_inter (this.trans (inter_subset_left.trans (hc (Finset.mem_coe.2 hν))))
    (this.trans inter_subset_right)

/-- Every simplex with a nonzero coefficient in the homotopy `h σ` lies in `range σ ∩ U'`. -/
lemma range_subset_of_homCoeff_ne_zero {n : ℕ} {σ : Simplex Y n} {ω : Simplex Y (n + 1)}
    (h : homCoeff R U U' σ ω ≠ 0) : range ω ⊆ range σ ∩ U' := by
  obtain ⟨i, hi⟩ : ∃ i,
      restrFin R U' (subdivHomotopy R n (badChain R U i n (single σ 1))) ω ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  exact range_subset_of_restrFin_ne_zero
    (subdivHomotopy_mem_inside (badChain_mem_inside (single_mem_inside_range σ))) hi

variable [T2Space Y]

/-- The homotopy `h σ` is locally finite on `U'`. -/
lemma exists_finite_homCoeff_ne_zero (hU : IsOpen U) (hU' : IsOpen U') (hUU' : U' ⊆ U)
    {n : ℕ} (σ : Simplex Y n) {x : Y} (hx : x ∈ U') : ∃ W, IsOpen W ∧ x ∈ W ∧
      {ω : Simplex Y (n + 1) | homCoeff R U U' σ ω ≠ 0 ∧ (range ω ∩ W).Nonempty}.Finite := by
  classical
  obtain ⟨V, W, hV, hW, hσV, hxW, hVW⟩ :=
    separatedNhds_range_inter_compl hU' σ isCompact_singleton (singleton_subset_iff.2 hx)
  obtain ⟨k, hk⟩ := exists_homCoeff_eq (R := R) hU hUU' σ hV hVW hσV
  set c := towardsHomotopy R U k n (single σ 1)
  have h : ∀ ν ∈ c.support, ∃ W', IsOpen W' ∧ x ∈ W' ∧
      {ω : Simplex Y (n + 1) | restrCoeff R U' ν ω ≠ 0 ∧ (range ω ∩ W').Nonempty}.Finite :=
    fun ν _ ↦ exists_finite_restrCoeff_ne_zero hU' ν hx
  choose! Wf hWf using h
  refine ⟨W ∩ ⋂ ν ∈ c.support, Wf ν, hW.inter (isOpen_biInter_finset fun ν hν ↦ (hWf ν hν).1),
    ⟨hxW rfl, mem_iInter₂.2 fun ν hν ↦ (hWf ν hν).2.1⟩, ?_⟩
  refine (c.support.finite_toSet.biUnion fun ν hν ↦ (hWf ν hν).2.2).subset ?_
  rintro ω ⟨hω, y, hy, hyW, hyW'⟩
  rw [(hk k le_rfl).1 ω ⟨y, hy, hyW⟩] at hω
  obtain ⟨ν, hν, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
  have h' : restrCoeff R U' ν ω ≠ 0 := fun h0 ↦ hne (by simp only [h0, mul_zero])
  exact mem_iUnion₂.2 ⟨ν, hν, h', y, hy, mem_iInter₂.1 hyW' ν hν⟩

end admissible

end SingularChain

end MMP
