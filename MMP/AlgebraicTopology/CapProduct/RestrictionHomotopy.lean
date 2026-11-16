module

public import MMP.AlgebraicTopology.CapProduct.RestrictionChains
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction

/-!
# The cap product and restriction to an open subset: the homotopy of a simplex

Let `U` be an open subset of a Hausdorff space `Y` and `φ` a `p`-cocycle. For a singular
`n`-simplex `σ` (`p + q = n`) the chain homotopy identity `σ = ρ_N σ + ∂ D_N σ + D_N ∂ σ` of the
subdivision towards `U` and the Leibniz rule give
`φ ∩ σ - φ ∩ ρ_N σ = ∂ (φ ∩ D_N σ) + φ ∩ D_N ∂ σ`. Restricting to `U` near a simplex
`ω` of `U`, for large `N` the chain `ρ_N σ` is its good part plus bad simplices away from `ω`, the
good part gives `φ ∩ σ|_U`, and the restrictions of `φ ∩ D_N σ` stabilize to the coefficients of
a chain `h σ` of `U` (Borel–Moore, §3). Hence, coefficientwise on `U`,
`(φ ∩ σ)|_U - φ ∩ σ|_U = ∂ (h σ) + h (∂ σ)`.

## Main definitions

* `MMP.BorelMooreCap.capRestrCoeff`: the coefficients of `φ ∩ σ|_U`.
* `MMP.BorelMooreCap.capHomCoeff`: the coefficients of `h σ`.

## Main results

* `MMP.BorelMooreCap.restrFin_capFin_sub_capRestrCoeff_succ`,
  `MMP.BorelMooreCap.restrFin_capFin_sub_capRestrCoeff_zero`: the homotopy
  identity.
* `MMP.BorelMooreCap.exists_finite_capHomCoeff_ne_zero`: `h σ` is locally finite
  on `U`.

## References

* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory Set Finsupp

universe u

namespace MMP

open MMP

namespace BorelMooreCap

open SingularCochain SingularChain

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- A cochain vanishing on the simplices of `B` caps to zero with a chain lying in `B`. -/
lemma capFin_eq_zero_of_vanishing (p q n : ℕ) (h : p + q = n) {B : Set Y}
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p B) {c : Chain R Y n} (hc : c ∈ inside R n B) :
    capFin R p q n h φ c = 0 := by
  classical
  rw [← Finsupp.sum_single c, map_finsuppSum]
  exact Finset.sum_eq_zero fun σ hσ ↦
    capFin_single_eq_zero_of_vanishing p q n h hφ (hc (Finset.mem_coe.2 hσ)) _

/-- The stage identity in positive degree, with coefficients in `R`:
`φ ∩ c - φ ∩ ρ_N c = ∂ (φ ∩ D_N c) + φ ∩ D_N ∂ c` for a cocycle `φ`. -/
theorem capFin_sub_capFin_towardsChainMap_succ (U : Set Y) (N p q n : ℕ) (h : p + q = n + 1)
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (c : Chain R Y (n + 1)) :
    capFin R p q (n + 1) h φ c - capFin R p q (n + 1) h φ (towardsChainMap R U N (n + 1) c) =
      bd R q (capFin R p (q + 1) (n + 2) (by omega) φ
          (towardsHomotopy R U N (n + 1) c)) +
        capFin R p q (n + 1) h φ (towardsHomotopy R U N n (bd R n c)) := by
  have e := capFin_bd_of_cocycle p q (n + 1) h hφ (towardsHomotopy R U N (n + 1) c)
  rw [towardsChainMap_succ_apply, map_sub, map_sub, e]
  abel

/-- The stage identity in degree `0`: `φ ∩ c - φ ∩ ρ_N c = ∂ (φ ∩ D_N c)`. -/
theorem capFin_sub_capFin_towardsChainMap_zero' (U : Set Y) (N p q : ℕ) (h : p + q = 0)
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (c : Chain R Y 0) :
    capFin R p q 0 h φ c - capFin R p q 0 h φ (towardsChainMap R U N 0 c) =
      bd R q (capFin R p (q + 1) 1 (by omega) φ (towardsHomotopy R U N 0 c)) := by
  obtain rfl : p = 0 := by omega
  obtain rfl : q = 0 := by omega
  rw [towardsChainMap_zero_apply, map_sub, capFin_bd_of_cocycle 0 0 0 h hφ]
  simp

section coeff

variable (R) (U : Set Y)

/-- The coefficient of `ω` in the cap product `φ ∩ σ|_U` of `φ` with the restriction of `σ`,
read in `Y`. -/
def capRestrCoeff (p q n : ℕ) (h : p + q = n) (φ : Simplex Y p → R) (σ : Simplex Y n)
    (ω : Simplex Y q) : R :=
  ∑ᶠ τ : Simplex Y n, restrCoeff R U σ τ * capFin R p q n h φ (single τ 1) ω

/-- The coefficient of the `q`-simplex `ω` in the homotopy `h ν = ∑_i (φ ∩ T X_i ν)|_U` of an
`n`-simplex `ν`, `p + q = n + 1`: the limit of the restrictions of `φ ∩ D_N ν`. -/
def capHomCoeff (p q n : ℕ) (h : p + q = n + 1) (φ : Simplex Y p → R) (ν : Simplex Y n)
    (ω : Simplex Y q) : R :=
  ∑ᶠ i : ℕ, restrFin R U (capFin R p q (n + 1) h φ
    (subdivHomotopy R n (badChain R U i n (single ν 1)))) ω

end coeff

variable {U : Set Y}

/-- A simplex `ω` with a nonzero homotopy coefficient `capHomCoeff R U p q n h φ ν ω` lies in
`range ν ∩ U`. -/
lemma range_subset_of_capHomCoeff_ne_zero {p q n : ℕ} {h : p + q = n + 1}
    {φ : Simplex Y p → R} {ν : Simplex Y n} {ω : Simplex Y q}
    (hne : capHomCoeff R U p q n h φ ν ω ≠ 0) : range ω ⊆ range ν ∩ U := by
  obtain ⟨i, hi⟩ : ∃ i, restrFin R U (capFin R p q (n + 1) h φ
      (subdivHomotopy R n (badChain R U i n (single ν 1)))) ω ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (finsum_eq_zero_of_forall_eq_zero h')
  exact range_subset_of_restrFin_ne_zero (capFin_mem_inside p q (n + 1) h φ
    (subdivHomotopy_mem_inside (badChain_mem_inside (single_mem_inside_range ν)))) hi

/-- The homotopy of a simplex on which `φ` vanishes is zero. -/
lemma capHomCoeff_eq_zero_of_vanishing {p q n : ℕ} (h : p + q = n + 1) {B : Set Y}
    {φ : Simplex Y p → R} (hφ : φ ∈ vanishing R p B) {ν : Simplex Y n} (hν : range ν ⊆ B)
    (ω : Simplex Y q) : capHomCoeff R U p q n h φ ν ω = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
  rw [capFin_eq_zero_of_vanishing p q (n + 1) h hφ (subdivHomotopy_mem_inside
    (badChain_mem_inside (show single ν (1 : R) ∈ inside R n B from
      fun τ hτ ↦ (single_mem_inside_range (R := R) ν hτ).trans hν))), restrFin_zero]

/-- A simplex `ω` with a nonzero coefficient `capRestrCoeff R U p q n h φ σ ω` lies in
`range σ ∩ U`. -/
lemma range_subset_of_capRestrCoeff_ne_zero {p q n : ℕ} {h : p + q = n} {φ : Simplex Y p → R}
    {σ : Simplex Y n} {ω : Simplex Y q} (hne : capRestrCoeff R U p q n h φ σ ω ≠ 0) :
    range ω ⊆ range σ ∩ U := by
  obtain ⟨τ, hτ⟩ : ∃ τ, restrCoeff R U σ τ * capFin R p q n h φ (single τ 1) ω ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (finsum_eq_zero_of_forall_eq_zero h')
  have h1 := range_subset_of_restrCoeff_ne_zero (left_ne_zero_of_mul hτ)
  have h2 : range ω ⊆ range τ := capFin_mem_inside p q n h φ (single_mem_inside_range τ)
    (Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hτ))
  exact h2.trans h1

variable [T2Space Y]

/-- Near `W`, away from a neighbourhood `V` of the points of `ν` outside `U`, the homotopy
coefficients are those of the restriction of `φ ∩ D_k ν`, for all large `k`. -/
lemma exists_capHomCoeff_eq (hU : IsOpen U) {p q n : ℕ} (h : p + q = n + 1)
    (φ : Simplex Y p → R) (ν : Simplex Y n) {V W : Set Y} (hV : IsOpen V) (hVW : Disjoint V W)
    (hνV : range ν ∩ Uᶜ ⊆ V) :
    ∃ k₀, ∀ k ≥ k₀, (∀ ω : Simplex Y q, (range ω ∩ W).Nonempty →
      capHomCoeff R U p q n h φ ν ω = restrFin R U (capFin R p q (n + 1) h φ
        (towardsHomotopy R U k n (single ν 1))) ω) ∧
      badChain R U k n (single ν 1) ∈ inside R n V := by
  obtain ⟨k₀, hk₀⟩ := eventually_goodPart_sub_mem_inside (R := R) hU ν hV hνV
  refine ⟨k₀, fun k hk ↦ ⟨fun ω hω ↦ ?_, (hk₀ k hk).2⟩⟩
  have hzero : ∀ i ≥ k, restrFin R U (capFin R p q (n + 1) h φ
      (subdivHomotopy R n (badChain R U i n (single ν 1)))) ω = 0 := fun i hi ↦
    restrFin_eq_zero_of_mem_inside hVW (capFin_mem_inside p q (n + 1) h φ
      (subdivHomotopy_mem_inside (hk₀ i (hk.trans hi)).2)) hω
  rw [capHomCoeff, finsum_eq_sum_of_support_subset (s := Finset.range k) _ (fun i hi ↦ by
    rw [Finset.coe_range, mem_Iio]
    by_contra h'
    exact hi (hzero i (not_lt.1 h'))), towardsHomotopy, LinearMap.sum_apply, map_sum,
    restrFin_sum]
  rfl

/-- The homotopy `h ν` is locally finite on `U`. -/
lemma exists_finite_capHomCoeff_ne_zero (hU : IsOpen U) {p q n : ℕ} (h : p + q = n + 1)
    (φ : Simplex Y p → R) (ν : Simplex Y n) {x : Y} (hx : x ∈ U) : ∃ W, IsOpen W ∧ x ∈ W ∧
      {ω : Simplex Y q | capHomCoeff R U p q n h φ ν ω ≠ 0 ∧ (range ω ∩ W).Nonempty}.Finite := by
  classical
  obtain ⟨V, W, hV, hW, hνV, hxW, hVW⟩ :=
    separatedNhds_range_inter_compl hU ν isCompact_singleton (singleton_subset_iff.2 hx)
  obtain ⟨k, hk⟩ := exists_capHomCoeff_eq (R := R) (q := q) hU h φ ν hV hVW hνV
  set c := capFin R p q (n + 1) h φ (towardsHomotopy R U k n (single ν 1))
  have h' : ∀ μ ∈ c.support, ∃ W', IsOpen W' ∧ x ∈ W' ∧
      {ω : Simplex Y q | restrCoeff R U μ ω ≠ 0 ∧ (range ω ∩ W').Nonempty}.Finite :=
    fun μ _ ↦ exists_finite_restrCoeff_ne_zero hU μ hx
  choose! Wf hWf using h'
  refine ⟨W ∩ ⋂ μ ∈ c.support, Wf μ, hW.inter (isOpen_biInter_finset fun μ hμ ↦ (hWf μ hμ).1),
    ⟨hxW rfl, mem_iInter₂.2 fun μ hμ ↦ (hWf μ hμ).2.1⟩, ?_⟩
  refine (c.support.finite_toSet.biUnion fun μ hμ ↦ (hWf μ hμ).2.2).subset ?_
  rintro ω ⟨hω, y, hy, hyW, hyW'⟩
  rw [(hk k le_rfl).1 ω ⟨y, hy, hyW⟩] at hω
  obtain ⟨μ, hμ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hω
  have h'' : restrCoeff R U μ ω ≠ 0 := fun h0 ↦ hne (by simp only [h0, mul_zero])
  exact mem_iUnion₂.2 ⟨μ, hμ, h'', y, hy, mem_iInter₂.1 hyW' μ hμ⟩

/-- The main term: near `W`, `(φ ∩ ρ_N σ)|_U` has the coefficients of `φ ∩ σ|_U`. -/
lemma exists_restrFin_capFin_towardsChainMap_eq (hU : IsOpen U) {p q n : ℕ} (h : p + q = n)
    (φ : Simplex Y p → R) (σ : Simplex Y n) {V W : Set Y} (hV : IsOpen V) (hVW : Disjoint V W)
    (hσV : range σ ∩ Uᶜ ⊆ V) :
    ∃ M, ∀ N ≥ M, ∀ ω : Simplex Y q, (range ω ∩ W).Nonempty →
      restrFin R U (capFin R p q n h φ (towardsChainMap R U N n (single σ 1))) ω =
        capRestrCoeff R U p q n h φ σ ω := by
  classical
  obtain ⟨Mg, hMg⟩ := exists_restrCoeff_eq_goodPart_of_disjoint (R := R) hU σ hV hVW hσV
  obtain ⟨Mb, hMb⟩ := eventually_goodPart_sub_mem_inside (R := R) hU σ hV hσV
  refine ⟨max Mg Mb, fun N hN ω hω ↦ ?_⟩
  have hs : towardsChainMap R U N n (single σ 1) =
      goodPart R U N σ + badChain R U N n (single σ 1) := by
    rw [goodPart, ← badProj_towardsChainMap, goodProj_add_badProj]
  rw [hs, map_add, restrFin_add, restrFin_eq_zero_of_mem_inside hVW (capFin_mem_inside p q n h φ
      (hMb N (le_of_max_le_right hN)).2) hω, add_zero,
    restrFin_of_mem_inside (capFin_mem_inside p q n h φ (show goodPart R U N σ ∈ inside R n U from
      fun τ hτ ↦ (goodPart_mem_inside σ hτ).trans inter_subset_right))]
  set g := goodPart R U N σ
  have hterm : ∀ τ : Simplex Y n, restrCoeff R U σ τ * capFin R p q n h φ (single τ 1) ω =
      g τ * capFin R p q n h φ (single τ 1) ω := fun τ ↦ by
    by_cases h0 : capFin R p q n h φ (single τ 1) ω = 0
    · rw [h0, mul_zero, mul_zero]
    · have hωτ : range ω ⊆ range τ := capFin_mem_inside p q n h φ (single_mem_inside_range τ)
        (Finsupp.mem_support_iff.2 h0)
      obtain ⟨y, hy, hyW⟩ := hω
      rw [hMg N (le_of_max_le_left hN) τ ⟨y, hωτ hy, hyW⟩]
  rw [capRestrCoeff, finsum_congr hterm, finsum_eq_sum_of_support_subset (s := g.support) _
    (fun τ hτ ↦ by
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hτ (by simp only [h0, zero_mul]))]
  conv_lhs => rw [← Finsupp.sum_single g]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [capFin_single, capFin_single, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> ring

open Classical in
/-- **The homotopy identity**, positive degree: for a cocycle `φ`, an `(m + 1)`-simplex `σ` and
a simplex `ω` of `U`, `(φ ∩ σ)|_U - φ ∩ σ|_U = ∂ (h σ) + h (∂ σ)` at `ω`. -/
theorem restrFin_capFin_sub_capRestrCoeff_succ (hU : IsOpen U) {p q m : ℕ} (h : p + q = m + 1)
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (σ : Simplex Y (m + 1)) {ω : Simplex Y q}
    (hω : range ω ⊆ U) :
    restrFin R U (capFin R p q (m + 1) h φ (single σ 1)) ω -
        capRestrCoeff R U p q (m + 1) h φ σ ω =
      ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = ω then
            capHomCoeff R U p (q + 1) (m + 1) (by omega) φ σ ω' else 0) +
        ∑ i : Fin (m + 2), (-1 : R) ^ (i : ℕ) *
          capHomCoeff R U p q m h φ (σ.comp (face m i)) ω := by
  obtain ⟨V, W, hV, -, hσV, hωW, hVW⟩ :=
    separatedNhds_range_inter_compl hU σ (isCompact_range ω.continuous) hω
  have hωW' : (range ω ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hωW ⟨_, rfl⟩⟩
  have hface : ∀ i : Fin (m + 2), range (σ.comp (face m i)) ∩ Uᶜ ⊆ V := fun i x hx ↦
    hσV ⟨by obtain ⟨t, ht⟩ := hx.1; exact ⟨_, ht⟩, hx.2⟩
  obtain ⟨Na, ha⟩ := exists_capHomCoeff_eq (R := R) (q := q + 1) hU (by omega) φ σ hV hVW hσV
  choose Nf hf using fun i : Fin (m + 2) ↦
    exists_capHomCoeff_eq (R := R) (q := q) hU h φ (σ.comp (face m i)) hV hVW (hface i)
  obtain ⟨Mg, hMg⟩ := exists_restrFin_capFin_towardsChainMap_eq (R := R) (q := q) hU h φ σ hV hVW
    hσV
  set N := max (max Na Mg) (Finset.univ.sup Nf)
  have hNa : Na ≤ N := le_max_of_le_left (le_max_left _ _)
  have hMg' : Mg ≤ N := le_max_of_le_left (le_max_right _ _)
  have hNf : ∀ i, Nf i ≤ N := fun i ↦ (Finset.le_sup (f := Nf) (Finset.mem_univ i)).trans
    (le_max_right _ _)
  have hst := congrArg (fun c ↦ restrFin R U c ω)
    (capFin_sub_capFin_towardsChainMap_succ U N p q m h hφ (single σ 1))
  simp only [restrFin_sub, restrFin_add, restrFin_smul] at hst
  rw [hMg N hMg' ω hωW', restrFin_bd hU _ hω] at hst
  rw [hst]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    refine finsum_congr fun ω' ↦ ?_
    split_ifs with h'
    · exact ((ha N hNa).1 ω' (range_inter_nonempty_of_comp hωW' h')).symm
    · rfl
  · rw [bd_single, map_sum, map_sum, restrFin_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, restrFin_smul, (hf i N (hNf i)).1 ω hωW']

open Classical in
/-- **The homotopy identity** in degree `0`: `(φ ∩ σ)|_U - φ ∩ σ|_U = ∂ (h σ)` at `ω`. -/
theorem restrFin_capFin_sub_capRestrCoeff_zero (hU : IsOpen U) {p q : ℕ} (h : p + q = 0)
    {φ : Simplex Y p → R} (hφ : coboundary R p φ = 0) (σ : Simplex Y 0) {ω : Simplex Y q}
    (hω : range ω ⊆ U) :
    restrFin R U (capFin R p q 0 h φ (single σ 1)) ω - capRestrCoeff R U p q 0 h φ σ ω =
      ∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) * ∑ᶠ ω' : Simplex Y (q + 1),
          (if ω'.comp (face q i) = ω then
            capHomCoeff R U p (q + 1) 0 (by omega) φ σ ω' else 0) := by
  obtain ⟨V, W, hV, -, hσV, hωW, hVW⟩ :=
    separatedNhds_range_inter_compl hU σ (isCompact_range ω.continuous) hω
  have hωW' : (range ω ∩ W).Nonempty := ⟨_, ⟨stdSimplex.vertex 0, rfl⟩, hωW ⟨_, rfl⟩⟩
  obtain ⟨Na, ha⟩ := exists_capHomCoeff_eq (R := R) (q := q + 1) hU (by omega) φ σ hV hVW hσV
  obtain ⟨Mg, hMg⟩ := exists_restrFin_capFin_towardsChainMap_eq (R := R) (q := q) hU h φ σ hV hVW
    hσV
  set N := max Na Mg
  have hst := congrArg (fun c ↦ restrFin R U c ω)
    (capFin_sub_capFin_towardsChainMap_zero' U N p q h hφ (single σ 1))
  simp only [restrFin_sub, restrFin_smul] at hst
  rw [hMg N (le_max_right _ _) ω hωW', restrFin_bd hU _ hω] at hst
  rw [hst]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  refine finsum_congr fun ω' ↦ ?_
  split_ifs with h'
  · exact ((ha N (le_max_left _ _)).1 ω' (range_inter_nonempty_of_comp hωW' h')).symm
  · rfl

end BorelMooreCap

end MMP
