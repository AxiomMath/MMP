module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.BracketsCofinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightSupportFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.Divisor.NormalizationBranchesCofinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations

/-!
# The local deficit of the difficulty at a junction

Let `(Y, Θ)` be the junction `Y_i`, `i ≥ i₀`, of a prepared chain, and `Q ⊆ Y` its varying union.
Write the difficulty as `𝒟(Y, Θ) = ∑_{c_Y(v) a closed point} w_v + ∑_C β_C + ∑_h d_h ρ^□(S_h^ν)`.
Every bracket satisfies `β_C ≥ -(r_C^var - 1)` for curves `C ⊆ Q` and `β_C ≥ 0` otherwise, where
`r_C^var ≥ 1` is the varying branch number, and `r_C^var > 1` for only finitely many `C`. Summing
gives
`𝒟(Y, Θ) ≥ ∑_{c_Y(v) a closed point} w_v + ∑_h d_h ρ^□(S_h^ν) - ∑_{C ⊆ Q} (r_C^var - 1)`.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty.sum_sub_sum_varyingBranchNumber_le`:
  the finiteness of the point and curve sums, the bound `r_C^var ≥ 1` on curves of `Q`, and the
  inequality.

## Implementation notes

* The junction `Y_i` of the prepared chain is the model `⟨⟨i, none⟩, hi⟩` with `i₀ ≤ i`.
* The irreducible curves `C ⊆ Q` are the proper curves `γ` of `Y` with
  `closure {γ.point} ⊆ Q`, the varying union being
  `MMP.Fourfold.StabilizedTail.TerminalChain.varyingUnion`.
* The weights, defaults, boxed ranks and varying branch numbers are predicates; the statement
  takes any families satisfying them, as in
  `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`. The label sum runs over a finite type
  (`MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`), so its finiteness is not restated.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Fourfold MMP.Mori

/-! ### Arithmetic of weights and defaults -/

/-- The ceiling of a sum with multiplicities loses at most `R - 1`, where `R` is the total
multiplicity of the non-integral terms. -/
private theorem sum_mul_ceil_le_ceil_sum_add_max {ι : Type*} (s : Finset ι) (r : ι → ℕ)
    (x : ι → ℝ) (p : ι → Prop) [DecidablePred p] (hx : ∀ h ∈ s, ¬ p h → ∃ z : ℤ, x h = z) :
    ∑ h ∈ s, (r h : ℤ) * ⌈x h⌉ ≤
      ⌈∑ h ∈ s, (r h : ℝ) * x h⌉ + max ((∑ h ∈ s with p h, (r h : ℤ)) - 1) 0 := by
  classical
  have hδ : ∀ h ∈ s, ((⌈x h⌉ : ℤ) : ℝ) - x h = if p h then ((⌈x h⌉ : ℤ) : ℝ) - x h else 0 := by
    intro h hh
    split_ifs with hp
    · rfl
    · obtain ⟨z, hz⟩ := hx h hh hp
      rw [hz, Int.ceil_intCast, sub_self]
  have hE : ((∑ h ∈ s, (r h : ℤ) * ⌈x h⌉ : ℤ) : ℝ) =
      ∑ h ∈ s, (r h : ℝ) * x h + ∑ h ∈ s with p h, (r h : ℝ) * (((⌈x h⌉ : ℤ) : ℝ) - x h) := by
    rw [Finset.sum_filter]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h hh => ?_
    have := hδ h hh
    split_ifs at this ⊢ with hp
    · ring
    · rw [sub_eq_zero] at this
      rw [this]
      ring
  have hceil : ∑ h ∈ s, (r h : ℝ) * x h ≤ ((⌈∑ h ∈ s, (r h : ℝ) * x h⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hle : ∀ h ∈ s.filter p, (r h : ℝ) * (((⌈x h⌉ : ℤ) : ℝ) - x h) ≤ (r h : ℝ) := by
    intro h _
    have h1 : ((⌈x h⌉ : ℤ) : ℝ) - x h ≤ 1 := by linarith [Int.ceil_lt_add_one (x h)]
    have h0 : (0 : ℝ) ≤ r h := Nat.cast_nonneg _
    nlinarith
  rcases Nat.eq_zero_or_pos (∑ h ∈ s with p h, r h) with hR | hR
  · have hzero : ∀ h ∈ s.filter p, r h = 0 := fun h hh =>
      (Finset.sum_eq_zero_iff.mp hR) h hh
    have : ∑ h ∈ s with p h, (r h : ℝ) * (((⌈x h⌉ : ℤ) : ℝ) - x h) = 0 :=
      Finset.sum_eq_zero fun h hh => by rw [hzero h hh, Nat.cast_zero, zero_mul]
    have hR' : (∑ h ∈ s with p h, (r h : ℤ)) = 0 := by exact_mod_cast hR
    rw [hR', zero_sub, max_eq_right (by norm_num), add_zero]
    exact_mod_cast (hE.trans (by rw [this, add_zero])).le.trans hceil
  · obtain ⟨h₀, hh₀, hr₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hR.ne'
    have hlt : ∑ h ∈ s with p h, (r h : ℝ) * (((⌈x h⌉ : ℤ) : ℝ) - x h) <
        ∑ h ∈ s with p h, (r h : ℝ) := by
      refine Finset.sum_lt_sum hle ⟨h₀, hh₀, ?_⟩
      have h1 : ((⌈x h₀⌉ : ℤ) : ℝ) - x h₀ < 1 := by linarith [Int.ceil_lt_add_one (x h₀)]
      have h0 : (0 : ℝ) < r h₀ := by exact_mod_cast Nat.pos_of_ne_zero hr₀
      nlinarith
    have hR1 : (1 : ℤ) ≤ ∑ h ∈ s with p h, (r h : ℤ) := by exact_mod_cast hR
    rw [max_eq_left (by linarith)]
    have key : ((∑ h ∈ s, (r h : ℤ) * ⌈x h⌉ : ℤ) : ℝ) <
        ((⌈∑ h ∈ s, (r h : ℝ) * x h⌉ + ∑ h ∈ s with p h, (r h : ℤ) : ℤ) : ℝ) := by
      rw [hE]
      push_cast
      linarith
    have := Int.cast_lt.mp key
    omega

/-- The default splits as `d(b) = w(b) + ∑_{j ≥ 2} w(1 - j(1 - b))` for `b < 1`. -/
private theorem defaultWeight_eq_add (N : ℕ) {b : ℝ} (hb : b < 1) :
    defaultWeight N b = difficultyWeight N b +
      ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b)) := by
  have hset : {j : ℕ | 1 ≤ j} = insert 1 {j : ℕ | 2 ≤ j} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
    omega
  rw [defaultWeight]
  change ∑ᶠ (j : ℕ) (_ : j ∈ {j : ℕ | 1 ≤ j}), _ = _
  rw [hset, finsum_mem_insert' _ (by simp)
    ((finite_support_difficultyWeight N hb).subset Set.inter_subset_right)]
  congr 2
  push_cast
  ring

/-- The higher terms of the default vanish for `b ≤ 1/2`. -/
private theorem finsum_difficultyWeight_eq_zero (N : ℕ) {b : ℝ} (hb : b ≤ 1 / 2) :
    ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b)) = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
  rw [finsum_eq_if]
  split_ifs with hj
  · apply difficultyWeight_of_nonpos
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  · rfl

/-- **The bracket bound, arithmetic form.** Let `b_h ∈ [0, 1)`, `r_h ≤ m_h` with
`∑_h m_h b_h < 1`, and `N b_h ∈ ℤ` for the labels outside `p`. If `W ≥ w(∑_h m_h b_h)`, and
moreover `W ≥ w(∑_h m_h b_h) + ∑_{j ≥ 2} w(1 - j(1 - b_{h₀}))` whenever some `h₀` has
`r_{h₀} ≥ 1`, `b_{h₀} > 1/2` (and then `m_{h₀} = 1`), then
`W - ∑_h r_h d(b_h) ≥ -max {∑_{h ∈ p} r_h - 1, 0}`. -/
private theorem neg_max_le_sub_sum_mul_defaultWeight {ι : Type*} [Fintype ι] (N : ℕ)
    (b : ι → ℝ) (r m : ι → ℕ) (p : ι → Prop) [DecidablePred p] (W : ℤ)
    (hb0 : ∀ h, 0 ≤ b h) (hb1 : ∀ h, b h < 1) (hrm : ∀ h, r h ≤ m h)
    (hmb : ∑ h, (m h : ℝ) * b h < 1) (hfix : ∀ h, ¬ p h → ∃ z : ℤ, (N : ℝ) * b h = z)
    (hW1 : (difficultyWeight N (∑ h, (m h : ℝ) * b h) : ℤ) ≤ W)
    (hW2 : ∀ h₀, 1 ≤ r h₀ → 1 / 2 < b h₀ → m h₀ = 1 →
      ((difficultyWeight N (∑ h, (m h : ℝ) * b h) +
        ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b h₀)) : ℕ) : ℤ) ≤ W) :
    -max ((∑ h with p h, (r h : ℤ)) - 1) 0 ≤ W - ∑ h, (r h : ℤ) * defaultWeight N (b h) := by
  classical
  set H : ι → ℕ := fun h => ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b h))
    with hHdef
  set A := difficultyWeight N (∑ h, (m h : ℝ) * b h)
  have hd : ∀ h, (defaultWeight N (b h) : ℤ) = ⌈(N : ℝ) * b h⌉ + H h := by
    intro h
    rw [defaultWeight_eq_add N (hb1 h), Nat.cast_add, natCast_difficultyWeight,
      max_eq_left (hb0 h)]
  have hnn : ∀ h ∈ (Finset.univ : Finset ι), 0 ≤ (m h : ℝ) * b h := fun h _ =>
    mul_nonneg (Nat.cast_nonneg _) (hb0 h)
  have hH : (A : ℤ) + ∑ h, (r h : ℤ) * H h ≤ W := by
    by_cases hex : ∃ h₀, 1 ≤ r h₀ ∧ 1 / 2 < b h₀
    · obtain ⟨h₀, hr₀, hb₀⟩ := hex
      have hm₀ : m h₀ = 1 := by
        have h1 : 1 ≤ m h₀ := hr₀.trans (hrm h₀)
        by_contra hne
        have h2 : (2 : ℝ) ≤ m h₀ := by exact_mod_cast (by omega : 2 ≤ m h₀)
        have := Finset.single_le_sum hnn (Finset.mem_univ h₀)
        nlinarith
      have hr₀1 : r h₀ = 1 := le_antisymm (hm₀ ▸ hrm h₀) hr₀
      have hsum : ∑ h, (r h : ℤ) * H h = H h₀ := by
        rw [Finset.sum_eq_single h₀ (fun h _ hne => ?_) (by simp), hr₀1, Nat.cast_one, one_mul]
        rcases Nat.eq_zero_or_pos (r h) with h0 | h0
        · rw [h0, Nat.cast_zero, zero_mul]
        · have hbh : b h ≤ 1 / 2 := by
            by_contra hbh
            push Not at hbh
            have hmh : (1 : ℝ) ≤ m h := by exact_mod_cast h0.trans_le (hrm h)
            have h2 := Finset.add_le_sum hnn (Finset.mem_univ h) (Finset.mem_univ h₀) hne
            rw [hm₀, Nat.cast_one] at h2
            nlinarith
          simp only [hHdef, finsum_difficultyWeight_eq_zero N hbh, Nat.cast_zero, mul_zero]
      rw [hsum]
      exact_mod_cast hW2 h₀ hr₀ hb₀ hm₀
    · push Not at hex
      have : ∑ h, (r h : ℤ) * H h = 0 := Finset.sum_eq_zero fun h _ => by
        rcases Nat.eq_zero_or_pos (r h) with h0 | h0
        · rw [h0, Nat.cast_zero, zero_mul]
        · simp only [hHdef, finsum_difficultyWeight_eq_zero N (hex h h0), Nat.cast_zero, mul_zero]
      rw [this, add_zero]
      exact hW1
  have hfirst : ∑ h, (r h : ℤ) * ⌈(N : ℝ) * b h⌉ - max ((∑ h with p h, (r h : ℤ)) - 1) 0 ≤
      A := by
    have h1 := sum_mul_ceil_le_ceil_sum_add_max Finset.univ r (fun h => (N : ℝ) * b h) p
      (fun h _ hp => hfix h hp)
    have h2 : difficultyWeight N (∑ h, (r h : ℝ) * b h) ≤ A :=
      difficultyWeight_mono N (Finset.sum_le_sum fun h _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrm h) (hb0 h))
    have h3 : (difficultyWeight N (∑ h, (r h : ℝ) * b h) : ℤ) =
        ⌈∑ h, (r h : ℝ) * ((N : ℝ) * b h)⌉ := by
      rw [natCast_difficultyWeight, max_eq_left (Finset.sum_nonneg fun h _ =>
        mul_nonneg (Nat.cast_nonneg _) (hb0 h)), Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun h _ => by ring
    have h2' : (difficultyWeight N (∑ h, (r h : ℝ) * b h) : ℤ) ≤ A := by exact_mod_cast h2
    linarith
  have hsplit : ∑ h, (r h : ℤ) * defaultWeight N (b h) =
      ∑ h, (r h : ℤ) * ⌈(N : ℝ) * b h⌉ + ∑ h, (r h : ℤ) * H h := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by rw [hd h]; ring
  rw [hsplit]
  linarith

/-! ### Regular systems of parameters of a two-dimensional regular local ring -/

section LocalRing

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem isRegularSystemOfParameters_swap {x y : R}
    (hxy : IsRegularSystemOfParameters ![x, y]) : IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← hxy.1]
  congr 1
  ext
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem span_pair_eq_maximalIdeal {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    Ideal.span {x, y} = maximalIdeal R := by
  rw [← hxy.1]
  congr 1
  ext
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]

/-- An element `a ∈ 𝔪 ∖ 𝔪²` of a local ring with a regular system of parameters `(z₀, z₁)` is
the first member of a regular system of parameters `(a, t)`. -/
private theorem exists_isRegularSystemOfParameters_of_notMem_sq {z₀ z₁ : R}
    (hz : IsRegularSystemOfParameters ![z₀, z₁]) {a : R} (ha : a ∈ maximalIdeal R)
    (ha2 : a ∉ maximalIdeal R ^ 2) : ∃ t : R, IsRegularSystemOfParameters ![a, t] := by
  have hspan := span_pair_eq_maximalIdeal hz
  have hz₀ : z₀ ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hz₁ : z₁ ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hc⟩ := Ideal.mem_span_pair.mp (hspan ▸ ha : a ∈ Ideal.span {z₀, z₁})
  have key : ∀ {u v c d : R}, IsUnit c → c * u + d * v = a → u ∈ maximalIdeal R →
      v ∈ maximalIdeal R → Ideal.span {u, v} = maximalIdeal R →
      IsRegularSystemOfParameters ![a, v] := by
    intro u v c d hc hcd hu hv huv
    refine ⟨le_antisymm ?_ ?_, hz.2⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact ha
      · exact hv
    · rw [← huv, Ideal.span_le]
      have hmem : ∀ i, ![a, v] i ∈ Ideal.span (Set.range ![a, v]) := fun i =>
        Ideal.subset_span ⟨i, rfl⟩
      have ha' : a ∈ Ideal.span (Set.range ![a, v]) := hmem 0
      have hv' : v ∈ Ideal.span (Set.range ![a, v]) := hmem 1
      obtain ⟨c', hc'⟩ := hc.exists_left_inv
      have hu' : u = c' * a - c' * d * v := by linear_combination c' * hcd - u * hc'
      refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr hv'⟩
      rw [SetLike.mem_coe, hu']
      exact sub_mem (Ideal.mul_mem_left _ _ ha') (Ideal.mul_mem_left _ _ hv')
  by_cases h₀ : IsUnit c₀
  · exact ⟨z₁, key h₀ hc hz₀ hz₁ hspan⟩
  · have h₁ : IsUnit c₁ := by
      by_contra h₁
      apply ha2
      rw [← hc, pow_two]
      exact add_mem (Ideal.mul_mem_mul ((mem_maximalIdeal _).mpr h₀) hz₀)
        (Ideal.mul_mem_mul ((mem_maximalIdeal _).mpr h₁) hz₁)
    exact ⟨z₀, key (c := c₁) (d := c₀) h₁ (by linear_combination hc) hz₁ hz₀
      (by rwa [Set.pair_comm])⟩

/-- A regular local ring of dimension two has a regular system of parameters `(x, y)`. -/
private theorem exists_isRegularSystemOfParameters_pair [IsRegularLocalRing R]
    (h : ringKrullDim R = 2) : ∃ x y : R, IsRegularSystemOfParameters ![x, y] := by
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters R
  obtain rfl : n = 2 := by
    have h' := hz.2
    rw [h] at h'
    exact_mod_cast h'.symm
  exact ⟨z 0, z 1, by convert hz using 1; ext i; fin_cases i <;> rfl⟩

/-- An element of `𝔪`-adic order one in a local ring with a regular system of parameters
`(z₀, z₁)` is the first member of a regular system of parameters `(a, t)`. -/
private theorem exists_isRegularSystemOfParameters_of_iSup_eq_one {z₀ z₁ : R}
    (hz : IsRegularSystemOfParameters ![z₀, z₁]) {a : R}
    (ha : ⨆ (n : ℕ) (_ : a ∈ maximalIdeal R ^ n), (n : ℕ∞) = 1) :
    ∃ t : R, IsRegularSystemOfParameters ![a, t] := by
  have hG := (isGreatest_iff_iSup_eq (s := {n : ℕ | a ∈ maximalIdeal R ^ n}) ⟨0, by simp⟩
    (M := 1)).mpr (by exact_mod_cast ha)
  exact exists_isRegularSystemOfParameters_of_notMem_sq hz (by simpa using hG.1) fun h =>
    absurd (hG.2 (show 2 ∈ {n : ℕ | a ∈ maximalIdeal R ^ n} from h)) (by norm_num)

/-- In a Noetherian local ring of dimension two with regular system of parameters `(x, t)`,
`x ∉ (t)`: otherwise the maximal ideal would be principal, of height at most one. -/
private theorem notMem_span_singleton_of_isRegularSystemOfParameters [IsNoetherianRing R]
    {x t : R} (hxt : IsRegularSystemOfParameters ![x, t]) : x ∉ Ideal.span {t} := by
  intro hx
  have hm : maximalIdeal R = Ideal.span {t} := by
    rw [← span_pair_eq_maximalIdeal hxt]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono (by simp))
    rintro _ (rfl | rfl)
    · exact hx
    · exact Ideal.subset_span rfl
  have h1 := Ideal.height_le_spanRank_toENat (maximalIdeal R) (Ideal.IsMaximal.ne_top inferInstance)
  have h2 : (maximalIdeal R).spanRank ≤ 1 := by
    rw [hm]
    exact (Submodule.spanRank_span_le_card _).trans (by simp)
  have h3 : (maximalIdeal R).height ≤ 1 :=
    h1.trans ((Cardinal.toENat.monotone' h2).trans (by simp))
  have h4 := maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hxt.2] at h4
  have : ((maximalIdeal R).height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h3
  rw [h4] at this
  norm_num at this

/-- The weighted order `v_{x,t;j}(x)` of the parameter `x` is `j`. -/
private theorem monomialValuation_self [IsNoetherianRing R] {x t : R}
    (hxt : IsRegularSystemOfParameters ![x, t]) {j : ℕ} :
    MMP.Resolution.monomialValuation t x j x = j := by
  have hspan := span_pair_eq_maximalIdeal hxt
  have htm : t ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hxm : x ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hmem : x ∈ MMP.Resolution.monomialIdeal t x j j :=
    Ideal.subset_span ⟨0, 1, by simp, by simp⟩
  have hnot : x ∉ MMP.Resolution.monomialIdeal t x j (j + 1) := by
    intro h
    have hle : MMP.Resolution.monomialIdeal t x j (j + 1) ≤
        Ideal.span {x * x} ⊔ Ideal.span {x * t} ⊔ Ideal.span {t ^ (j + 1)} := by
      refine Ideal.span_le.mpr ?_
      rintro r ⟨a, b, hab, rfl⟩
      rcases b with _ | _ | b
      · refine Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨t ^ (a - (j + 1)), ?_⟩)
        rw [pow_zero, mul_one, ← pow_add]
        congr 1
        omega
      · refine Ideal.mem_sup_left (Ideal.mem_sup_right
          (Ideal.mem_span_singleton.mpr ⟨t ^ (a - 1), ?_⟩))
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp only [add_tsub_cancel_right]
        ring
      · exact Ideal.mem_sup_left (Ideal.mem_sup_left
          (Ideal.mem_span_singleton.mpr ⟨x ^ b * t ^ a, by ring⟩))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle h)
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hy₁
    obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hy₂
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hu : IsUnit (1 - α * x - β * t) := by
      rw [← notMem_maximalIdeal]
      intro hm
      have h1 := add_mem (add_mem hm (Ideal.mul_mem_left _ α hxm)) (Ideal.mul_mem_left _ β htm)
      rw [show 1 - α * x - β * t + α * x + β * t = 1 by ring] at h1
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    apply notMem_span_singleton_of_isRegularSystemOfParameters hxt
    have : x * (1 - α * x - β * t) = γ * t ^ (j + 1) := by linear_combination -hyz
    rw [show x = γ * t ^ j * u * t by
      rw [← mul_one x, ← hu', ← mul_assoc, this]; ring]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  refine le_antisymm (iSup₂_le fun ν hν => ?_) (le_iSup₂_of_le j hmem le_rfl)
  by_contra hlt
  have hν' : j + 1 ≤ ν := by
    have : (j : ℕ∞) < ν := not_le.mp hlt
    exact_mod_cast Order.add_one_le_of_lt this
  refine hnot (Ideal.span_le.mpr ?_ hν)
  rintro r ⟨a, b, hab, rfl⟩
  exact Ideal.subset_span ⟨a, b, by omega, rfl⟩

end LocalRing

/-! ### Dimension arithmetic -/

/-- In `WithBot ℕ∞`, `1 + c = n + 1` forces `c = n`. -/
private theorem eq_of_one_add_eq {c : ℕ∞} {n : ℕ} (h : (1 : WithBot ℕ∞) + c = ((n + 1 : ℕ) : ℕ∞)) :
    c = n :=
  WithBot.coe_injective (ENat.WithBot.one_add_cancel.mp (by rw [h]; push_cast; ring))

/-! ### Log discrepancies, weights and centres -/

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq_of_surjective {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- A valuation with a log discrepancy over a proper model has that log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : MMP.Mori.QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-! ### Centres of labels -/

section LabelCentre

variable {T : StabilizedTail}

/-- The valuation of `k(X_i)` transported from a valuation of `k(X_0)` is unique. -/
private theorem isTransportedValuationFrom_unique : ∀ (i : ℕ)
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, ht⟩, ⟨u', hu', ht'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    have hd := T.isThreefoldStepDiagram i
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hb := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq_of_surjective hb.functionFieldMap_bijective.2
      (ht.trans ht'.symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hY' : MMP.Mori.IsNormalVariety ℂ (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  let D : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P⟩
  let D' : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P'⟩
  have hD : D.valuation = D'.valuation := by
    change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
    rw [valuation_eq_of_comap_eq_of_surjective hf h]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hD)

/-- Along the programme of a bridge, every `π_k : V_k ⟶ Z_i` induces a surjection
`k(Z_i) → k(V_k)` of function fields: `π_0 = f_i ∘ p_i` is birational, and
`π_{k+1} = h_k ∘ g_k⁺` with `π_k = h_k ∘ g_k` and `g_k`, `g_k⁺` birational. -/
private theorem surjective_functionFieldMap_modelMap (C : T.TerminalChain) (i : ℕ)
    [IsIntegral (T.Z i)] :
    ∀ k ≤ (C.bridge i).P.m,
      ∀ [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)],
        Function.Surjective
          (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k))
  | 0, _, _ => by
    have hb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    have hp := (C.junction i).isBirationalMorphism
    haveI := hp.isDominant
    intro z
    obtain ⟨y, rfl⟩ := hp.functionFieldMap_bijective.2 z
    obtain ⟨x, rfl⟩ := hb.functionFieldMap_bijective.2 y
    exact ⟨x, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply
      (C.junction i).p (T.f i) x).symm⟩
  | k + 1, hk, hdom => by
    have hk' : k < (C.bridge i).P.m := hk
    have hd := (C.bridge i).P.isThreefoldStepDiagram k hk'
    haveI := hd.isNormalVariety_target.1.toIsIntegral
    have hg := hd.isBirationalMorphism_minus
    haveI := hg.isDominant
    have hgp := hd.isSmallMorphism_plus.isBirationalMorphism
    haveI := hgp.isDominant
    have hπ : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k + 1) =
        (C.bridge i).P.gp k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.πY_eq k hk'
    have hπ' : modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k =
        (C.bridge i).P.g k ≫ (C.bridge i).P.h k :=
      (C.bridge i).P.modelMap_eq k hk'
    haveI hgph : IsDominant ((C.bridge i).P.gp k ≫ (C.bridge i).P.h k) := hπ ▸ hdom
    haveI : IsDominant ((C.bridge i).P.h k) := IsDominant.of_comp ((C.bridge i).P.gp k) _
    haveI : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k) :=
      hπ' ▸ inferInstance
    have IH := surjective_functionFieldMap_modelMap C i k hk'.le
    have hh : Function.Surjective (functionFieldMap ((C.bridge i).P.h k)) := by
      intro t
      obtain ⟨z, hz⟩ := IH (functionFieldMap ((C.bridge i).P.g k) t)
      refine ⟨z, (functionFieldMap ((C.bridge i).P.g k)).injective ?_⟩
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        ← MMP.Positivity.DivisorOver.functionFieldMap_congr hπ', hz]
    intro t
    obtain ⟨y, rfl⟩ := hgp.functionFieldMap_bijective.2 t
    obtain ⟨z, rfl⟩ := hh y
    have e1 := @MMP.Positivity.DivisorOver.functionFieldMap_congr _ _ _ _ _ _ hdom hgph hπ
    exact ⟨z, (congrArg (fun φ => φ z) e1).trans
      (@MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply _ _ _ _ _ _
        ((C.bridge i).P.gp k) ((C.bridge i).P.h k) hgp.isDominant inferInstance hgph z).symm⟩

/-- The centre of a label on a normal model of a terminal chain is unique. -/
private theorem isLabelCentre_unique (C : T.TerminalChain) (S : C.Label) :
    ∀ (x : C.ModelIndex), MMP.Mori.IsNormalVariety ℂ (C.modelStructure x) →
      ∀ {P P' : MMP.Mori.PrimeDivisor (C.model x)},
        C.IsLabelCentre S x P → C.IsLabelCentre S x P' → P = P'
  | ⟨i, none⟩, hY, P, P', ⟨w, hw, hPw⟩, ⟨w', hw', hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY (C.junction i).p hb.isDominant
      hb.functionFieldMap_bijective.2 _ _ (hPw.trans hPw'.symm)
  | ⟨i, some k⟩, hY, P, P', ⟨w, hw, hdom, hPw⟩, ⟨w', hw', _, hPw'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hw hw'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact @primeDivisor_eq_of_valuationOver_eq _ _ _ _ _ _ _ hY _ hdom
      (@surjective_functionFieldMap_modelMap T C i _ k k.2.le hdom) _ _ (hPw.trans hPw'.symm)

end LabelCentre

/-! ### Weighted monomial valuations at the generic point of a curve -/

section MonomialValuation

/-- The order-reversing monoid map `WithTop ℤ → (WithZero (Multiplicative ℤ))`,
`n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → (WithZero (Multiplicative ℤ))
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private theorem expNeg_top : expNeg ⊤ = 0 := rfl

private theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private theorem expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R (WithZero (Multiplicative ℤ)) where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- At the generic point of a codimension-two closed subset `V` with regular local ring, every
regular system of parameters `(x, t)` and weight `j ≥ 1` carry a monomial valuation
`v_{x,t;j}`. -/
private theorem exists_isWeightedMonomialValuation (hY : IsNormalVariety ℂ sY)
    {V : IrreducibleCloseds Y} (hcodim : codimension V = 2)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hxt : IsRegularSystemOfParameters ![x, t]) {j : ℕ} (hj : 1 ≤ j) :
    ∃ v, IsWeightedMonomialValuation sY V x t j v := by
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap hxt) hj
  refine ⟨valuationOfAddValuation W, hY, hcodim, inferInstance, hxt, hj, fun f hf => ?_⟩
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
  refine ⟨M, hM.symm, ?_⟩
  change expNeg (W _) = _
  rw [hW, ← hM]
  rfl

/-- The log discrepancy `a(v_{x,t;j}; Y, Θ) = 1 + j - ∑_P Θ(P) μ_P`, where `μ_P` is the weighted
order of a local equation of `P`. -/
private theorem hasLogDiscrepancy_of_isWeightedMonomialValuation {Θ : QDivisor Y}
    (hΘ : MMP.Fourfold.IsPair sY Θ) {V : IrreducibleCloseds Y}
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsWeightedMonomialValuation sY V x t j v)
    (f : MMP.Mori.PrimeDivisor Y → Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hf0 : ∀ P, f P ≠ 0)
    (hf : ∀ P, IdealSheafData.stalk P.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f P})
    (μ : MMP.Mori.PrimeDivisor Y → ℕ)
    (hμ : ∀ P, MMP.Resolution.monomialValuation t x j (f P) = μ P) :
    HasLogDiscrepancy sY Θ v (1 + j - ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) * μ P) := by
  have h := hv.hasLogDiscrepancy hΘ f (fun P _ => hf P)
  convert h using 3 with P _
  obtain ⟨M, hM1, hM2⟩ := hv.2.2.2.2.2 (f P) (hf0 P)
  rw [hM2, WithZero.log_exp, neg_neg]
  rw [show μ P = M by exact_mod_cast (hμ P).symm.trans hM1]
  norm_cast

/-- `v_{x,t;j}` sends the first parameter `x` to `exp (-j)`, i.e. `x` has weighted order
`j`. -/
private theorem apply_eq_exp_of_isWeightedMonomialValuation {V : IrreducibleCloseds Y}
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsWeightedMonomialValuation sY V x t j v) :
    v (algebraMap _ Y.functionField x) = WithZero.exp (-(j : ℤ)) := by
  have hx0 : x ≠ 0 := fun h =>
    notMem_span_singleton_of_isRegularSystemOfParameters hv.2.2.2.1 (h ▸ zero_mem _)
  obtain ⟨M, hM1, hM2⟩ := hv.2.2.2.2.2 x hx0
  rw [monomialValuation_self hv.2.2.2.1] at hM1
  rw [hM2, show M = j by exact_mod_cast hM1.symm]

/-- The valuations `v_{x,t;j}`, `j ≥ 1`, are pairwise distinct. -/
private theorem injOn_of_isWeightedMonomialValuation {V : IrreducibleCloseds Y}
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    {vj : ℕ → Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hvj : ∀ j, IsWeightedMonomialValuation sY V x t (max j 1) (vj j)) :
    Set.InjOn vj {j | 1 ≤ j} := by
  intro j hj j' hj' h
  have h1 := apply_eq_exp_of_isWeightedMonomialValuation (hvj j)
  rw [h, apply_eq_exp_of_isWeightedMonomialValuation (hvj j')] at h1
  have h3 := WithZero.exp_injective h1
  simp only [Set.mem_setOf_eq] at hj hj'
  rw [max_eq_left hj, max_eq_left hj'] at h3
  omega

/-- If the first parameter of `v_{x,t;j}` is a local equation of a component `P₀` of `Θ`, then
`a(v_{x,t;j}; Y, Θ) ≤ 1 + j - Θ(P₀) j`. -/
private theorem exists_hasLogDiscrepancy_le_of_isWeightedMonomialValuation {Θ : QDivisor Y}
    (hΘ : MMP.Fourfold.IsPair sY Θ) {V : IrreducibleCloseds Y}
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    (f : MMP.Mori.PrimeDivisor Y → Y.presheaf.stalk V.isIrreducible.genericPoint)
    (hf0 : ∀ P, f P ≠ 0)
    (hf : ∀ P, IdealSheafData.stalk P.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f P})
    {P₀ : MMP.Mori.PrimeDivisor Y} (hP₀ : P₀ ∈ Θ.support)
    {t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hv : IsWeightedMonomialValuation sY V (f P₀) t j v) :
    ∃ a, HasLogDiscrepancy sY Θ v a ∧ a ≤ 1 + j - (Θ.coeff P₀ : ℝ) * j := by
  choose μ hμ _ using fun P => hv.2.2.2.2.2 (f P) (hf0 P)
  refine ⟨_, hasLogDiscrepancy_of_isWeightedMonomialValuation hΘ hv f hf0 hf μ hμ, ?_⟩
  have hμ₀ : μ P₀ = j := by
    have := hμ P₀
    rw [monomialValuation_self hv.2.2.2.1] at this
    exact_mod_cast this.symm
  have hle := Finset.single_le_sum (f := fun P => (Θ.coeff P : ℝ) * (μ P : ℝ))
    (fun P _ => mul_nonneg (by exact_mod_cast hΘ.nonneg P) (Nat.cast_nonneg _)) hP₀
  simp only [hμ₀] at hle
  linarith

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension (hX : IsNormalVariety ℂ sY)
    (D : DivisorOver ℂ sY) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sY := hX.1.toIsSeparated
  haveI : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set Y), D.center.isClosed⟩ :=
    Closeds.ext (by rw [Closeds.coe_closure]; exact D.coe_center.symm)
  rw [hc]
  change 2 ≤ closedsCodimension (T := Y) ⟨(D.center : Set Y), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

/-- On a terminal pair, a valuation with centre of codimension at least two has log discrepancy
`> 1`. -/
private theorem one_lt_of_isKltTerminalPair {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    (hX : IsNormalVariety ℂ sY) {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    {V : IrreducibleCloseds Y} (hc : MMP.Intersection.IsCentre ℂ sY v V)
    (hV : 2 ≤ codimension V) {a : ℝ} (ha : HasLogDiscrepancy sY Θ v a) : 1 < a := by
  obtain ⟨n, D, hDv, hlog⟩ := ha
  obtain ⟨D', -, hvD', rfl⟩ := hc
  have hcen : D.center = D'.center :=
    MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hDv.trans hvD')
  exact hΘ.2 n D a ((isExceptional_iff_two_le_codimension hX D).mpr (hcen ▸ hV)) hlog

end MonomialValuation

/-! ### Sums -/

/-- Proper curves are determined by their closures, so finitely many closures carry finitely many
proper curves. -/
private theorem finite_setOf_closure_point_mem {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} {𝒮 : Set (Set X)} (h : 𝒮.Finite) :
    {γ : MMP.Mori.ProperCurve sX | closure {γ.point} ∈ 𝒮}.Finite :=
  h.preimage fun _ _ _ _ he => MMP.Mori.ProperCurve.ext (inseparable_iff_closure_eq.mpr he).eq

/-- A finite sum over a subset of `s` is at most the finitely supported sum over `s`. -/
private theorem sum_le_finsum_mem {α : Type*} {s : Set α} (f : α → ℕ)
    (hs : (s ∩ Function.support f).Finite) (F : Finset α) (hF : (F : Set α) ⊆ s) :
    ∑ a ∈ F, f a ≤ ∑ᶠ a ∈ s, f a := by
  classical
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hs,
    ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset fun a ha => ?_
  rw [Finset.mem_filter] at ha
  exact hs.mem_toFinset.mpr ⟨hF ha.1, ha.2⟩

/-! ### Curves on a model of a prepared chain -/

/-- The closure of the generic point of a proper curve, as a subspace of `X`, has dimension
one: it is the image of the closed embedding `C ⟶ X`. -/
private theorem topologicalKrullDim_closure_point {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- The irreducible closed subset `closure {γ}` underlying a proper curve `γ`. -/
private abbrev curveCloseds {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}
    (γ : ProperCurve sX) : IrreducibleCloseds X :=
  ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩

section Curve

variable {T : StabilizedTail} (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex)
  (γ : ProperCurve (Q.chain.modelStructure x.1))

/-- On a model of a prepared chain, the generic point of a curve has coheight two. -/
private theorem coheight_genericPoint_curveCloseds :
    Order.coheight (curveCloseds γ).isIrreducible.genericPoint = 2 := by
  have hdim := (Q.echoSetting_model x).2.2.2.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) :=
    (Q.echoSetting_model x).2.2.1.1.1.toLocallyOfFiniteType
  have hdf := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
    (Q.chain.modelStructure x.1) (curveCloseds γ).isIrreducible.genericPoint
  have hV : topologicalKrullDim ((curveCloseds γ : Set (Q.chain.model x.1))) = 1 :=
    topologicalKrullDim_closure_point γ
  rw [((curveCloseds γ).isIrreducible.isGenericPoint_genericPoint (curveCloseds γ).isClosed).def,
    hV, hdim] at hdf
  exact eq_of_one_add_eq (n := 2) hdf

private theorem codimension_curveCloseds : codimension (curveCloseds γ) = 2 := by
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  exact coheight_genericPoint_curveCloseds Q x γ

private theorem ringKrullDim_stalk_curveCloseds :
    ringKrullDim ((Q.chain.model x.1).presheaf.stalk
      (curveCloseds γ).isIrreducible.genericPoint) = 2 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, coheight_genericPoint_curveCloseds]
  rfl

private theorem isRegularLocalRing_stalk_curveCloseds :
    IsRegularLocalRing ((Q.chain.model x.1).presheaf.stalk
      (curveCloseds γ).isIrreducible.genericPoint) :=
  (Q.echoSetting_model x).2.2.2.2.2 _ (topologicalKrullDim_closure_point γ)

/-- **Branches are bounded by the order.** The branches of the normalization of a prime divisor
`P` over a curve `C` number at most the `𝔪_C`-adic order of a local equation of `P`. -/
private theorem encard_branches_le_monomialValuation (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1))
    {z₀ z₁ : (Q.chain.model x.1).presheaf.stalk (curveCloseds γ).isIrreducible.genericPoint}
    (hz : IsRegularSystemOfParameters ![z₀, z₁])
    {g : (Q.chain.model x.1).presheaf.stalk (curveCloseds γ).isIrreducible.genericPoint}
    (hg : IdealSheafData.stalk P.idealSheaf (curveCloseds γ).isIrreducible.genericPoint =
      Ideal.span {g}) :
    {B : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
      primeDivisorNormalization P '' B.support = closure {γ.point}}.encard ≤
      MMP.Resolution.monomialValuation z₁ z₀ 1 g := by
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) :=
    (Q.echoSetting_model x).2.2.1.1.1.toLocallyOfFiniteType
  have h1 := encard_branches_le_multiplicityAlong (Q.chain.modelStructure x.1) (curveCloseds γ)
    (isRegularLocalRing_stalk_curveCloseds Q x γ) (ringKrullDim_stalk_curveCloseds Q x γ) P
  rwa [MMP.Mori.PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span P _ (g := g)
    (by rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk, hg]),
    ← monomialValuation_one_eq_iSup hz] at h1

/-- A finite sum of weights over valuations centred at a curve is at most the bracket's sum of
weights at that curve. -/
private theorem sum_le_finsum_isCentre_curveCloseds
    (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
          (Z : Set (Q.chain.model x.1)) = closure {γ.point}) →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (F : Finset (Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))))
    (hF : ∀ v ∈ F, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v (curveCloseds γ)) :
    ∑ v ∈ F, w v ≤ ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
        (Z : Set (Q.chain.model x.1)) = closure {γ.point}), w v := by
  have hcent : {v | ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
      (Z : Set (Q.chain.model x.1)) = closure {γ.point}} =
      {v | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v (curveCloseds γ)} :=
    Set.ext fun v => ⟨fun ⟨Z, hc, hZ⟩ => by
      obtain rfl : Z = curveCloseds γ := IrreducibleCloseds.ext hZ
      exact hc, fun hc => ⟨_, hc, rfl⟩⟩
  have hW : ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
        (Z : Set (Q.chain.model x.1)) = closure {γ.point}), w v =
      ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v (curveCloseds γ)},
        w v := by
    rw [← hcent]
    rfl
  rw [hW]
  exact sum_le_finsum_mem w ((Q.finite_setOf_isCentre_closure x γ).subset
    fun v ⟨hv, hv0⟩ => ⟨⟨_, hv, rfl⟩, w v, hw v ⟨_, hv, rfl⟩, hv0⟩) F hF

end Curve

/-! ### The local ceiling error -/

/-- At the admissible scale, the coefficient of a fixed label in the boundary of a model is
integral. -/
private theorem exists_intCast_eq_scale_mul_coeff {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex)
    (hnv : IsNormalVariety ℂ (Q.chain.modelStructure x.1))
    {c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model x.1)}
    (hcc : ∀ S, Q.chain.IsLabelCentre S x.1 (c S)) {S : Q.chain.Label}
    (hS : ¬ Q.chain.IsVaryingLabel S) :
    ∃ z : ℤ, (Q.scale : ℝ) * (((Q.chain.modelBoundary x.1).coeff (c S) : ℚ) : ℝ) = z := by
  obtain ⟨c₀, ⟨n₀, hn₀⟩, hc₀⟩ := Q.isLabelCoefficient_of_isFixedLabel S
    ((Q.chain.not_isVaryingLabel_iff S).mp hS)
  obtain ⟨P, hP, hPc⟩ := hc₀ x.1 x.2
  obtain ⟨z₀, hz₀⟩ := Q.isAdmissibleScale.exists_intCast_eq_of_eventually hn₀
  refine ⟨z₀, ?_⟩
  rw [← isLabelCentre_unique Q.chain S x.1 hnv hP (hcc S), hPc]
  exact_mod_cast hz₀

/-- **Local ceiling error.** On a model `(Y, Θ)` of a prepared chain, the bracket at an
irreducible closed curve `C` satisfies `β_C ≥ -max {r_C^var - 1, 0}`, where `r_C^var` is the sum
of the branch numbers `r_{C,h}` of the varying labels. -/
private theorem neg_max_le_of_isCurveBracket {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex)
    (γ : ProperCurve (Q.chain.modelStructure x.1)) {β : ℤ} (hβ : Q.IsCurveBracket x γ β)
    (rv : Q.chain.Label → ℕ)
    (hrv : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelBranchNumber S x.1 γ (rv S)) :
    -max (((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), rv S : ℕ) : ℤ) - 1) 0 ≤ β := by
  classical
  set Θ := Q.chain.modelBoundary x.1
  set N := Q.scale
  obtain ⟨hΘ, -, hQf, -, ⟨c, hcinj, hcc, hcsupp, hccoeff⟩, -⟩ := Q.echoSetting_model x
  have hnv : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hQf.1
  have hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) Θ := hΘ.1.1
  haveI : Fintype Q.chain.Label := @Fintype.ofFinite _ Q.chain.finite_label
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hnv.1.toLocallyOfFiniteType
  set V := curveCloseds γ
  haveI := isRegularLocalRing_stalk_curveCloseds Q x γ
  have hcodim := codimension_curveCloseds Q x γ
  -- the data of the bracket
  obtain ⟨w, r, d, hw, hr, hd, rfl⟩ := hβ
  have hcen : ∀ S P, Q.chain.IsLabelCentre S x.1 P → P = c S := fun S P h =>
    isLabelCentre_unique Q.chain S x.1 hnv h (hcc S)
  have hr' : ∀ S, r S = branchNumber (c S) (closure {γ.point}) := fun S => by
    obtain ⟨P, hP, h⟩ := hr S
    rw [h, hcen S P hP]
  have hrv' : ∀ S, Q.chain.IsVaryingLabel S → rv S = r S := fun S hS => by
    obtain ⟨P, hP, h⟩ := hrv S hS
    rw [h, hr' S, hcen S P hP]
  set b : Q.chain.Label → ℝ := fun S => ((Θ.coeff (c S) : ℚ) : ℝ) with hbdef
  have hd' : ∀ S, d S = defaultWeight N (b S) := fun S => by
    obtain ⟨b', ⟨P, hP, hb'⟩, h⟩ := hd S
    rw [h, ← hb', hcen S P hP]
  have hb0 : ∀ S, 0 ≤ b S := fun S => by
    simp only [hbdef]
    exact_mod_cast (hccoeff S).1
  have hb1 : ∀ S, b S < 1 := fun S => by
    simp only [hbdef]
    exact_mod_cast (hccoeff S).2
  -- local equations, regular parameters and orders
  choose f hf0 hf using fun P : MMP.Mori.PrimeDivisor (Q.chain.model x.1) =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) P
  obtain ⟨z₀, z₁, hz2⟩ := exists_isRegularSystemOfParameters_pair
    (ringKrullDim_stalk_curveCloseds Q x γ)
  have hord : ∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ∃ M : ℕ,
      ∀ {a t : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint},
        IsRegularSystemOfParameters ![a, t] → MMP.Resolution.monomialValuation t a 1 (f P) = M := by
    intro P
    obtain ⟨v, hv⟩ := exists_isWeightedMonomialValuation hnv hcodim hz2 le_rfl
    obtain ⟨M, hM, -⟩ := hv.2.2.2.2.2 (f P) (hf0 P)
    exact ⟨M, fun hat => by
      rw [monomialValuation_one_eq_iSup hat, ← hM, monomialValuation_one_eq_iSup hz2]⟩
  choose M hM using hord
  set m : Q.chain.Label → ℕ := fun S => M (c S)
  -- the weights at `C`
  have hwt : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      ∀ a, HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ v a →
      w v = difficultyWeight N (2 - a) := by
    intro v hv a ha
    obtain ⟨-, a', ha', h⟩ := hw v ⟨V, hv, rfl⟩
    rw [h, HasLogDiscrepancy.unique (IsValuationLogDiscrepancy.hasLogDiscrepancy ha') ha]
  have hsum : ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) * (M P : ℝ) = ∑ S, (m S : ℝ) * b S := by
    have h1 : ∑ S, (m S : ℝ) * b S =
        ∑ P ∈ Finset.univ.image c, (Θ.coeff P : ℝ) * (M P : ℝ) := by
      rw [Finset.sum_image (fun S _ S' _ h => hcinj h)]
      exact Finset.sum_congr rfl fun S _ => mul_comm _ _
    rw [h1]
    refine Finset.sum_subset (fun P hP => ?_) (fun P _ hP => ?_)
    · obtain ⟨S, rfl⟩ := hcsupp P (Finsupp.mem_support_iff.mp hP)
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · have h0 : Θ.coeff P = 0 := Finsupp.notMem_support_iff.mp hP
      rw [h0, Rat.cast_zero, zero_mul]
  -- the order valuation `v₁`
  have hfirst : ∀ {a t : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint},
      IsRegularSystemOfParameters ![a, t] →
        ∀ v, IsWeightedMonomialValuation (Q.chain.modelStructure x.1) V a t 1 v →
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧ ∑ S, (m S : ℝ) * b S < 1 ∧
          w v = difficultyWeight N (∑ S, (m S : ℝ) * b S) := by
    intro a t hat v hv
    have hc := hv.isNormalizedDivisorialValuation_and_isCentre.2
    have ha := hasLogDiscrepancy_of_isWeightedMonomialValuation hpair hv f hf0 hf M
      (fun P => hM P hat)
    rw [hsum] at ha
    have h1 := one_lt_of_isKltTerminalPair hΘ hnv hc hcodim.ge ha
    refine ⟨hc, by push_cast at h1; linarith, ?_⟩
    rw [hwt v hc _ ha]
    congr 1
    push_cast
    ring
  obtain ⟨v₁, hv₁⟩ := exists_isWeightedMonomialValuation hnv hcodim hz2 le_rfl
  obtain ⟨hv₁c, hmb, hwv₁⟩ := hfirst hz2 v₁ hv₁
  -- the sum of the weights at `C`
  set W : ℕ := ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
      (Z : Set (Q.chain.model x.1)) = closure {γ.point}), w v
  have hWle : ∀ F : Finset (Valuation (Q.chain.model x.1).functionField
      (WithZero (Multiplicative ℤ))),
      (∀ v ∈ F, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V) →
        ∑ v ∈ F, w v ≤ W :=
    sum_le_finsum_isCentre_curveCloseds Q x γ w hw
  -- branch numbers are bounded by multiplicities
  have hrm : ∀ S, r S ≤ m S := by
    intro S
    rw [hr' S]
    by_cases hVS : closure {γ.point} ⊆ (c S).support
    · have h1 := encard_branches_le_monomialValuation Q x γ (c S) hz2 (hf (c S))
      rw [hM (c S) hz2] at h1
      exact (Set.encard_le_coe_iff_finite_ncard_le.mp h1).2
    · rw [branchNumber_eq_zero_of_not_subset hVS]
      exact Nat.zero_le _
  -- fixed labels have integral coefficients at the admissible scale
  have hfix : ∀ S, ¬ Q.chain.IsVaryingLabel S → ∃ z : ℤ, (N : ℝ) * b S = z := fun S hS =>
    exists_intCast_eq_scale_mul_coeff Q x hnv hcc hS
  have hW1 : (difficultyWeight N (∑ S, (m S : ℝ) * b S) : ℤ) ≤ W := by
    rw [← hwv₁]
    exact_mod_cast hWle {v₁} (by simpa using hv₁c)
  have hW2 : ∀ h₀, 1 ≤ r h₀ → 1 / 2 < b h₀ → m h₀ = 1 →
      ((difficultyWeight N (∑ S, (m S : ℝ) * b S) +
        ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b h₀)) : ℕ) : ℤ) ≤ W := by
    intro h₀ hr₀ hb₀ hm₀
    -- the local equation of the label `h₀` is a regular parameter
    obtain ⟨t, hat⟩ := exists_isRegularSystemOfParameters_of_iSup_eq_one hz2
      (a := f (c h₀)) (by rw [← monomialValuation_one_eq_iSup hz2, hM _ hz2]; exact_mod_cast hm₀)
    -- the valuations `v_j = v_{x,t;j}`
    choose vj hvj using fun j : ℕ => exists_isWeightedMonomialValuation
      (sY := Q.chain.modelStructure x.1) hnv hcodim hat (le_max_right j 1)
    have hvjc : ∀ j, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (vj j) V := fun j =>
      (hvj j).isNormalizedDivisorialValuation_and_isCentre.2
    have hinj : Set.InjOn vj {j | 1 ≤ j} := injOn_of_isWeightedMonomialValuation hvj
    have hwj : ∀ j : ℕ, 2 ≤ j → difficultyWeight N (1 - j * (1 - b h₀)) ≤ w (vj j) := by
      intro j hj
      have hmem : c h₀ ∈ Θ.support := Finsupp.mem_support_iff.mpr fun h0 => by
        have : b h₀ = 0 := by simp only [hbdef, show Θ.coeff (c h₀) = 0 from h0, Rat.cast_zero]
        linarith
      obtain ⟨a, ha, hle⟩ :=
        exists_hasLogDiscrepancy_le_of_isWeightedMonomialValuation hpair f hf0 hf hmem (hvj j)
      have key : a ≤ 1 + j - b h₀ * j := by
        simpa only [max_eq_left (show 1 ≤ j by omega)] using hle
      rw [hwt _ (hvjc j) _ ha]
      apply difficultyWeight_mono
      linarith
    -- summing over the `v_j`
    set Jf : Finset ℕ := (finite_support_difficultyWeight N (hb1 h₀)).toFinset.filter (2 ≤ ·)
      with hJf
    have hJsum : ∑ᶠ (j : ℕ) (_ : 2 ≤ j), difficultyWeight N (1 - j * (1 - b h₀)) =
        ∑ j ∈ Jf, difficultyWeight N (1 - j * (1 - b h₀)) :=
      finsum_cond_eq_sum_of_cond_iff _ fun {j} hj => by simp [hJf, hj]
    have h1J : 1 ∉ Jf := by simp [hJf]
    have hJ1 : ∀ j ∈ insert 1 Jf, 1 ≤ j := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · have := (Finset.mem_filter.mp hj).2
        omega
    have hw1' : w (vj 1) = difficultyWeight N (∑ S, (m S : ℝ) * b S) :=
      (hfirst hat (vj 1) (by simpa using hvj 1)).2.2
    have hsumle : ∑ j ∈ insert 1 Jf, w (vj j) ≤ W := by
      rw [← Finset.sum_image (fun j hj j' hj' h => hinj (hJ1 j hj) (hJ1 j' hj') h)]
      exact hWle _ fun v hv => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
        exact hvjc j
    rw [Finset.sum_insert h1J, hw1'] at hsumle
    rw [hJsum]
    exact_mod_cast (Nat.add_le_add_left
      (Finset.sum_le_sum fun j hj => hwj j (Finset.mem_filter.mp hj).2) _).trans hsumle
  have hR : ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), rv S : ℕ) : ℤ) =
      ∑ S with Q.chain.IsVaryingLabel S, (r S : ℤ) := by
    rw [finsum_cond_eq_sum_of_cond_iff rv (t := Finset.univ.filter Q.chain.IsVaryingLabel)
      (fun _ => by simp)]
    push_cast
    exact Finset.sum_congr rfl fun S hS => by rw [hrv' S (Finset.mem_filter.mp hS).2]
  have hrd : ((∑ᶠ S, r S * d S : ℕ) : ℤ) = ∑ S, (r S : ℤ) * defaultWeight N (b S) := by
    rw [finsum_eq_sum_of_fintype]
    push_cast
    exact Finset.sum_congr rfl fun S _ => by rw [hd' S]
  rw [hR, hrd]
  exact neg_max_le_sub_sum_mul_defaultWeight N b r m _ (W : ℤ) hb0 hb1 hrm hmb hfix hW1 hW2

/-! ### Uniqueness of weights, defaults and boxed ranks -/

section Uniqueness

variable {T : StabilizedTail} {C : T.TerminalChain}

/-- The weight `w_v` of a valuation on a model of a terminal chain is unique. -/
private theorem isValuationWeight_unique {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w w' : ℕ}
    (h : C.IsValuationWeight N x v w) (h' : C.IsValuationWeight N x v w') : w = w' := by
  obtain ⟨-, a, ha, rfl⟩ := h
  obtain ⟨-, a', ha', rfl⟩ := h'
  rw [HasLogDiscrepancy.unique (IsValuationLogDiscrepancy.hasLogDiscrepancy ha)
    (IsValuationLogDiscrepancy.hasLogDiscrepancy ha')]

/-- The default `d_h` of a label on a normal model of a terminal chain is unique. -/
private theorem isLabelDefault_unique {x : C.ModelIndex}
    (hX : IsNormalVariety ℂ (C.modelStructure x)) {N : ℕ} {S : C.Label} {d d' : ℕ}
    (h : C.IsLabelDefault N S x d) (h' : C.IsLabelDefault N S x d') : d = d' := by
  obtain ⟨b, ⟨P, hP, rfl⟩, rfl⟩ := h
  obtain ⟨b', ⟨P', hP', rfl⟩, rfl⟩ := h'
  rw [isLabelCentre_unique C S x hX hP hP']

/-- The boxed rank `ρ^□(S_h^ν)` of a label on a normal model of a terminal chain is unique. -/
private theorem isLabelBoxedRank_unique {x : C.ModelIndex}
    (hX : IsNormalVariety ℂ (C.modelStructure x)) {S : C.Label} {ρ ρ' : ℕ}
    (h : C.IsLabelBoxedRank S x ρ) (h' : C.IsLabelBoxedRank S x ρ') : ρ = ρ' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨P', hP', rfl⟩ := h'
  obtain rfl := isLabelCentre_unique C S x hX hP hP'
  rfl

end Uniqueness

/-! ### Branches along a curve -/

/-- On a model of a prepared chain, only finitely many prime divisors of the normalization of a
prime divisor `P` map onto a given irreducible closed curve: at most its multiplicity along the
curve. -/
private theorem finite_setOf_image_eq_closure {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex)
    (γ : ProperCurve (Q.chain.modelStructure x.1)) (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1)) :
    {B : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
      primeDivisorNormalization P '' B.support = closure {γ.point}}.Finite := by
  haveI := isRegularLocalRing_stalk_curveCloseds Q x γ
  obtain ⟨z₀, z₁, hz⟩ := exists_isRegularSystemOfParameters_pair
    (ringKrullDim_stalk_curveCloseds Q x γ)
  obtain ⟨g, hg0, hg⟩ := exists_stalk_idealSheaf_eq_span
    (η := (curveCloseds γ).isIrreducible.genericPoint) P
  obtain ⟨v, hv⟩ := exists_isWeightedMonomialValuation (Q.echoSetting_model x).2.2.1.1
    (codimension_curveCloseds Q x γ) hz le_rfl
  obtain ⟨M, hM, -⟩ := hv.2.2.2.2.2 g hg0
  have h1 := encard_branches_le_monomialValuation Q x γ P hz hg
  rw [hM] at h1
  exact (Set.encard_le_coe_iff_finite_ncard_le.mp h1).1

/-- **Every surface through a curve has a branch over it.** On a model of a prepared chain, a
prime divisor `P` containing an irreducible closed curve `C` has branch number `r_C ≥ 1`. -/
private theorem one_le_branchNumber {T : StabilizedTail}
    (Q : StabilizedTail.PreparedChain T) (x : Q.ModelIndex)
    (γ : ProperCurve (Q.chain.modelStructure x.1)) (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1))
    (hP : closure {γ.point} ⊆ P.support) : 1 ≤ branchNumber P (closure {γ.point}) := by
  have hnv : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := (Q.echoSetting_model x).2.2.1.1
  haveI : AlgebraicGeometry.IsVariety ℂ (Q.chain.modelStructure x.1) := hnv.1
  obtain ⟨-, B, hB⟩ := exists_primeDivisor_image_primeDivisorNormalization_eq
    (Q.chain.modelStructure x.1) (fun _ : Unit => P) (curveCloseds γ)
    (codimension_curveCloseds Q x γ)
    fun y hy => Set.mem_iUnion.mpr ⟨(), hP hy⟩
  exact (Set.ncard_pos (finite_setOf_image_eq_closure Q x γ P)).mpr ⟨B, hB⟩

/-- **At most one branch in total.** If the normalizations of the prime divisors in `F` have at
most one branch over `Z` between them, then their branch numbers along `Z` sum to at most one. -/
private theorem sum_branchNumber_le_one {Y : Scheme} (F : Finset (MMP.Mori.PrimeDivisor Y))
    {Z : Set Y} (hfin : ∀ P ∈ F, {B : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P) |
      primeDivisorNormalization P '' B.support = Z}.Finite)
    (h : {B : Σ S : F, MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S.1) |
      primeDivisorNormalization B.1.1 '' B.2.support = Z}.Subsingleton) :
    ∑ P ∈ F, branchNumber P Z ≤ 1 := by
  by_cases hex : ∃ P ∈ F, branchNumber P Z ≠ 0
  · obtain ⟨P, hP, hP0⟩ := hex
    rw [Finset.sum_eq_single P (fun P' hP' hne => by_contra fun h0 => hne ?_) (absurd hP)]
    · haveI := (hfin P hP).to_subtype
      exact Set.ncard_le_one_iff_subsingleton.mpr fun B hB B' hB' =>
        eq_of_heq (Sigma.mk.inj (@h ⟨⟨P, hP⟩, B⟩ hB ⟨⟨P, hP⟩, B'⟩ hB')).2
    · obtain ⟨B, hB⟩ := Set.nonempty_of_ncard_ne_zero h0
      obtain ⟨B', hB'⟩ := Set.nonempty_of_ncard_ne_zero hP0
      exact congrArg Subtype.val (Sigma.mk.inj (@h ⟨⟨P', hP'⟩, B⟩ hB ⟨⟨P, hP⟩, B'⟩ hB')).1
  · push Not at hex
    rw [Finset.sum_eq_zero hex]
    exact zero_le_one

/-- **Local deficit of the difficulty.** At the junction `(Y, Θ) = Y_i`, `i ≥ i₀`, of a prepared
chain with varying union `Q` (`MMP.Fourfold.StabilizedTail.TerminalChain.varyingUnion`), with
point weights `w_v` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`), defaults
`d_h`, boxed ranks `ρ^□(S_h^ν)` and varying branch numbers `r_C^var`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingBranchNumber`): only finitely many
valuations centred at closed points have `w_v ≠ 0`; `r_C^var ≥ 1` for every curve `C ⊆ Q`, with
`r_C^var ≠ 1` for only finitely many of them; and the difficulty `𝒟(Y, Θ)` satisfies
`𝒟(Y, Θ) ≥ ∑_{c_Y(v) a closed point} w_v + ∑_h d_h ρ^□(S_h^ν) - ∑_{C ⊆ Q} (r_C^var - 1)`. -/
@[mmp "lem_mmp_indexd_local_deficit"]
public theorem IsDifficulty.sum_sub_sum_varyingBranchNumber_le {T : StabilizedTail}
    {Q : PreparedChain T} {i : ℕ} {hi : Q.start ≤ i} {D : ℤ}
    (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v))
    (d ρ : Q.chain.Label → ℕ) (hd : ∀ S, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, Q.chain.IsLabelBoxedRank S ⟨i, none⟩ (ρ S))
    (r : MMP.Mori.ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℕ)
    (hr : ∀ γ, closure {γ.point} ⊆ Q.chain.varyingUnion i →
      Q.chain.IsVaryingBranchNumber ⟨i, none⟩ γ (r γ)) :
    {v | (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) ∧ w v ≠ 0}.Finite ∧
    (∀ γ, closure {γ.point} ⊆ Q.chain.varyingUnion i → 1 ≤ r γ) ∧
    {γ | closure {γ.point} ⊆ Q.chain.varyingUnion i ∧ r γ ≠ 1}.Finite ∧
    ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v : ℕ) : ℤ) +
      ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) -
      ∑ᶠ (γ) (_ : closure {γ.point} ⊆ Q.chain.varyingUnion i), ((r γ : ℤ) - 1) ≤ D := by
  classical
  obtain ⟨-, -, hQf, -, ⟨c, hcinj, hcc, -, -⟩, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  have hnv : IsNormalVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hQf.1
  haveI : Fintype Q.chain.Label := @Fintype.ofFinite _ Q.chain.finite_label
  have hcen : ∀ S P, Q.chain.IsLabelCentre S ⟨i, none⟩ P → P = c S := fun S P h =>
    isLabelCentre_unique Q.chain S ⟨i, none⟩ hnv h (hcc S)
  -- curves of the varying union are the curves inside a varying label
  have hVQ : ∀ γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩),
      closure {γ.point} ⊆ Q.chain.varyingUnion i ↔
        ∃ S, Q.chain.IsVaryingLabel S ∧ closure {γ.point} ⊆ (c S).support := by
    refine fun γ => ⟨fun hγ => ?_, fun ⟨S, hS, hsub⟩ y hy => ⟨S, hS, c S, hcc S, hsub hy⟩⟩
    obtain ⟨S, hS, P, hP, hmem⟩ := hγ (subset_closure (Set.mem_singleton γ.point))
    obtain rfl := hcen S P hP
    refine ⟨S, hS, closure_minimal (Set.singleton_subset_iff.mpr hmem) ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  -- the varying branch number is the sum of the branch numbers of the varying labels
  have hrsum : ∀ γ (hγ : closure {γ.point} ⊆ Q.chain.varyingUnion i),
      r γ = ∑ S with Q.chain.IsVaryingLabel S, branchNumber (c S) (closure {γ.point}) := by
    intro γ hγ
    obtain ⟨r', hr', hreq⟩ := hr γ hγ
    rw [hreq, finsum_cond_eq_sum_of_cond_iff r' (t := Finset.univ.filter Q.chain.IsVaryingLabel)
      (fun _ => by simp)]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨P, hP, h⟩ := hr' S (Finset.mem_filter.mp hS).2
    rw [h, hcen S P hP]
  have hpos : ∀ γ, closure {γ.point} ⊆ Q.chain.varyingUnion i → 1 ≤ r γ := by
    intro γ hγ
    obtain ⟨S, hS, hsub⟩ := (hVQ γ).mp hγ
    rw [hrsum γ hγ]
    exact (one_le_branchNumber Q ⟨⟨i, none⟩, hi⟩ γ (c S) hsub).trans
      (Finset.single_le_sum (f := fun S => branchNumber (c S) (closure {γ.point}))
        (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩))
  have hfin : {γ | closure {γ.point} ⊆ Q.chain.varyingUnion i ∧ r γ ≠ 1}.Finite := by
    haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) :=
      hnv.1.toLocallyOfFiniteType
    haveI : QuasiCompact (Q.chain.modelStructure ⟨i, none⟩) := hnv.1.toQuasiCompact
    let F := (Finset.univ.filter Q.chain.IsVaryingLabel).image c
    refine (finite_setOf_closure_point_mem ((finite_setOf_nontrivial_normalizationBranches
      (Q.chain.modelStructure ⟨i, none⟩) F).image ((↑) : IrreducibleCloseds _ → Set _))).subset ?_
    rintro γ ⟨hγ, hr1⟩
    refine ⟨curveCloseds γ, ?_, rfl⟩
    by_contra hnt
    rw [Set.mem_setOf_eq, Set.not_nontrivial_iff] at hnt
    refine hr1 (le_antisymm ?_ (hpos γ hγ))
    rw [hrsum γ hγ, ← Finset.sum_image (f := fun P => branchNumber P (closure {γ.point}))
      fun S _ S' _ h => hcinj h]
    exact sum_branchNumber_le_one F (fun P _ => finite_setOf_image_eq_closure Q _ γ P) hnt
  refine ⟨?_, hpos, hfin, ?_⟩
  · refine (Q.finite_setOf_isCentre_singleton ⟨⟨i, none⟩, hi⟩).subset ?_
    rintro v ⟨⟨Z, hZ, y, -, hy⟩, hv0⟩
    exact ⟨⟨Z, y, hZ, hy⟩, w v, hw v ⟨Z, hZ, y, by rw [← hy]; exact Z.isClosed, hy⟩, hv0⟩
  · obtain ⟨w₀, β, d₀, ρ₀, hw₀, hβ, hd₀, hρ₀, hDeq⟩ := hD
    rw [hDeq]
    have e1 : ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w₀ v =
        ∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v :=
      finsum_congr fun v => finsum_congr fun hv => isValuationWeight_unique (hw₀ v hv) (hw v hv)
    have e2 : ∑ᶠ S, d₀ S * ρ₀ S = ∑ᶠ S, d S * ρ S := finsum_congr fun S => by
      rw [isLabelDefault_unique hnv (hd₀ S) (hd S), isLabelBoxedRank_unique hnv (hρ₀ S) (hρ S)]
    rw [e1, e2]
    -- the brackets are bounded below by `-(r_C^var - 1)` on `Q` and by `0` off `Q`
    set g : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℤ := fun γ =>
      if closure {γ.point} ⊆ Q.chain.varyingUnion i then (r γ : ℤ) - 1 else 0 with hgdef
    have hg : ∑ᶠ (γ) (_ : closure {γ.point} ⊆ Q.chain.varyingUnion i), ((r γ : ℤ) - 1) =
        ∑ᶠ γ, g γ := finsum_congr fun γ => finsum_eq_if
    have hbound : ∀ γ, 0 ≤ β γ + g γ := by
      intro γ
      by_cases hγ : closure {γ.point} ⊆ Q.chain.varyingUnion i
      · obtain ⟨r', hr', hreq⟩ := hr γ hγ
        have h := neg_max_le_of_isCurveBracket Q ⟨⟨i, none⟩, hi⟩ γ (hβ γ) r' hr'
        rw [← hreq, max_eq_left (by have := hpos γ hγ; omega)] at h
        simp only [hgdef, if_pos hγ]
        linarith
      · have h := neg_max_le_of_isCurveBracket Q ⟨⟨i, none⟩, hi⟩ γ (hβ γ) (fun _ => 0)
          fun S hS => ⟨c S, hcc S, (branchNumber_eq_zero_of_not_subset
            fun hsub => hγ ((hVQ γ).mpr ⟨S, hS, hsub⟩)).symm⟩
        simp only [finsum_zero, Nat.cast_zero, zero_sub] at h
        simp only [hgdef, if_neg hγ]
        linarith [max_eq_right (show (-1 : ℤ) ≤ 0 by norm_num)]
    have hfing : (Function.support g).Finite := hfin.subset fun γ hγ => by
      simp only [Function.mem_support, hgdef] at hγ
      split_ifs at hγ with h
      · exact ⟨h, fun h1 => hγ (by rw [h1]; norm_num)⟩
      · exact absurd rfl hγ
    rw [hg]
    push_cast
    linarith [finsum_add_distrib
      ((Q.finite_setOf_isCurveBracket_ne_zero ⟨⟨i, none⟩, hi⟩).2.2 β hβ) hfing,
      finsum_nonneg hbound]

end MMP.Fourfold.StabilizedTail.PreparedChain

end
