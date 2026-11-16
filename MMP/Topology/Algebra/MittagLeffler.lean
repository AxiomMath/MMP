module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Mittag-Leffler lemma for towers of complete groups

Let `⋯ → G₂ → G₁ → G₀` be a tower of complete, Hausdorff, first countable topological abelian
groups whose transition maps `φ : G_{j+1} → G_j` are continuous additive maps with dense image.
Then every sequence `s_j ∈ G_j` has the form `s_j = t_j - φ(t_{j+1})`: the map
`∏ G_j → ∏ G_j, t ↦ (t_j - φ(t_{j+1}))_j` is surjective, that is, `lim¹_j G_j = 0`.

The proof is the classical one. Using density, choose `d_j ∈ G_j` recursively so that
`e_j = s_j + d_j - φ(d_{j+1})` is small in every `G_i`, `i ≤ j`, after mapping down. The series
`σ_i = ∑_{N > i} φ_{iN}(e_N)` then converges in `G_i`, and `t_j = e_j + σ_j - d_j` solves the
equations, because `φ(σ_{j+1}) = σ_j - φ(e_{j+1})`.

## Main results

* `MMP.Topology.sum_mem_of_add_subset`: if `u (m + 1) + u (m + 1) ⊆ u m` and `g k ∈ u (k + 1)`,
  then every finite sum of the `g k` with `k ≥ m` lies in `u m`.
* `MMP.Topology.summable_of_mem_succ`: in a complete group with a basis `u` of neighbourhoods of
  zero satisfying `u (m + 1) + u (m + 1) ⊆ u m`, a sequence with `g k ∈ u (k + 1)` is summable.
* `MMP.Topology.exists_sub_eq_of_denseRange`: the Mittag-Leffler lemma, `lim¹ = 0` for a tower
  of complete metrizable groups with dense transition maps.
* `MMP.Topology.exists_sub_eq_of_forall_mem`: if subgroups `Q_j ≤ G_j` contain the images of the
  transition maps and `lim¹_j Q_j = 0`, then `lim¹_j G_j = 0`.

## Implementation notes

The tower is given by the maps `φ h : G j →+ G i` for all `i ≤ j`, compatible under composition,
as an inverse system indexed by `ℕ` provides them; only the maps `G (j + 1) → G j` need to have
dense range. Metrizability enters as first countability of the uniform groups.

## References

* [Grauert–Remmert, *Theory of Stein spaces*, Chapter IV, §1]
* [Stacks Project, Tag 0598]
-/

@[expose] public section

open Filter Topology
open scoped Pointwise

namespace MMP.Topology

/-- If `u` is antitone, contains `0` everywhere and satisfies `u (m + 1) + u (m + 1) ⊆ u m`, and
`g k ∈ u (k + 1)` for all `k`, then a finite sum of the `g k` over indices `k ≥ m` lies in `u m`. -/
theorem sum_mem_of_add_subset {G : Type*} [AddCommMonoid G] {u : ℕ → Set G}
    (hu0 : ∀ m, (0 : G) ∈ u m) (hanti : Antitone u) (hadd : ∀ m, u (m + 1) + u (m + 1) ⊆ u m)
    {g : ℕ → G} (hg : ∀ k, g k ∈ u (k + 1)) (t : Finset ℕ) (m : ℕ) (hm : ∀ k ∈ t, m ≤ k) :
    ∑ k ∈ t, g k ∈ u m := by
  induction t using Finset.strongInduction generalizing m with
  | H t ih =>
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simpa using hu0 m
    · have hk : t.min' hne ∈ t := t.min'_mem hne
      rw [← Finset.add_sum_erase t g hk]
      have hrest : ∑ i ∈ t.erase (t.min' hne), g i ∈ u (t.min' hne + 1) := by
        refine ih _ (Finset.erase_ssubset hk) _ fun i hi => ?_
        obtain ⟨hik, hit⟩ := Finset.mem_erase.1 hi
        exact Nat.succ_le_of_lt (lt_of_le_of_ne (t.min'_le i hit) (Ne.symm hik))
      exact hanti (hm _ hk) (hadd _ (Set.add_mem_add (hg _) hrest))

/-- In a complete uniform group with an antitone basis `u` of neighbourhoods of zero such that
`u (m + 1) + u (m + 1) ⊆ u m`, a sequence with `g k ∈ u (k + 1)` for all `k` is summable. -/
theorem summable_of_mem_succ {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] {u : ℕ → Set G} (hu : (𝓝 (0 : G)).HasAntitoneBasis u)
    (hadd : ∀ m, u (m + 1) + u (m + 1) ⊆ u m) {g : ℕ → G} (hg : ∀ k, g k ∈ u (k + 1)) :
    Summable g := by
  refine summable_iff_vanishing.2 fun e he => ?_
  obtain ⟨m, -, hm⟩ := hu.toHasBasis.mem_iff.1 he
  refine ⟨Finset.range m, fun t ht => hm (sum_mem_of_add_subset
    (fun m => mem_of_mem_nhds (hu.toHasBasis.mem_of_mem trivial)) hu.antitone hadd hg t m
    fun k hk => ?_)⟩
  by_contra h
  exact Finset.disjoint_left.1 ht hk (Finset.mem_range.2 (not_le.1 h))

/-- **The Mittag-Leffler lemma.** Let `G₀ ← G₁ ← G₂ ← ⋯` be a tower of complete Hausdorff first
countable uniform abelian groups, with continuous additive transition maps `φ h : G j → G i`
(`h : i ≤ j`), compatible under composition, such that each `G (j + 1) → G j` has dense range.
Then every sequence `s` has the form `s j = t j - φ (t (j + 1))`, that is, `lim¹_j G_j = 0`. -/
theorem exists_sub_eq_of_denseRange {G : ℕ → Type*} [∀ j, AddCommGroup (G j)]
    [∀ j, UniformSpace (G j)] [∀ j, IsUniformAddGroup (G j)] [∀ j, CompleteSpace (G j)]
    [∀ j, T2Space (G j)] [∀ j, FirstCountableTopology (G j)]
    (φ : ∀ ⦃i j : ℕ⦄, i ≤ j → G j →+ G i)
    (hφ : ∀ ⦃i j k : ℕ⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : G k),
      φ hij (φ hjk x) = φ (hij.trans hjk) x)
    (hcont : ∀ ⦃i j : ℕ⦄ (h : i ≤ j), Continuous (φ h))
    (hdense : ∀ j, DenseRange (φ (Nat.le_succ j))) (s : ∀ j, G j) :
    ∃ t : ∀ j, G j, ∀ j, s j = t j - φ (Nat.le_succ j) (t (j + 1)) := by
  choose u hu hadd using fun j => IsTopologicalAddGroup.exists_antitone_basis_nhds_zero (G j)
  have humem : ∀ j m, u j m ∈ 𝓝 (0 : G j) := fun j m => (hu j).toHasBasis.mem_of_mem trivial
  -- `W N`: the elements of `G N` whose image in each `G i`, `i ≤ N`, lies in `u i (N + 1)`.
  let W : ∀ N, Set (G N) := fun N =>
    ⋂ i : Fin (N + 1), φ (Nat.lt_succ_iff.1 i.2) ⁻¹' u i (N + 1)
  have hW : ∀ N, W N ∈ 𝓝 (0 : G N) := fun N =>
    iInter_mem.2 fun i => (hcont _).tendsto' 0 0 (map_zero _) (humem _ _)
  have step : ∀ N (x : G N), ∃ y : G (N + 1), s N + x - φ (Nat.le_succ N) y ∈ W N := by
    intro N x
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := (hdense N).inter_nhds_nonempty
      ((continuous_const.sub continuous_id).tendsto' (s N + x) 0 (sub_self _) (hW N))
    exact ⟨y, hy⟩
  choose c hc using step
  let d : ∀ N, G N := Nat.rec (motive := G) 0 c
  let e : ∀ N, G N := fun N => s N + d N - φ (Nat.le_succ N) (d (N + 1))
  have he : ∀ N, e N ∈ W N := fun N => hc N (d N)
  -- `E i N`: the image of `e N` in `G i`, a function of `N` with values in the fixed `G i`.
  let E : ∀ i, ℕ → G i := fun i N => if h : i ≤ N then φ h (e N) else 0
  have hE : ∀ i N (h : i ≤ N), E i N = φ h (e N) := fun i N h => dif_pos h
  have hEmem : ∀ i N, i ≤ N → E i N ∈ u i (N + 1) := fun i N h => by
    rw [hE i N h]
    exact Set.mem_iInter.1 (he N) ⟨i, Nat.lt_succ_of_le h⟩
  have hEφ : ∀ j N, j + 1 ≤ N → φ (Nat.le_succ j) (E (j + 1) N) = E j N := fun j N h => by
    rw [hE _ _ h, hE _ _ (by omega), hφ]
  -- the series `σ i = ∑ₖ E i (i + 1 + k)`
  have hsum : ∀ i, Summable fun k => E i (i + 1 + k) := fun i =>
    summable_of_mem_succ (hu i) (hadd i) fun k =>
      (hu i).antitone (by omega) (hEmem i (i + 1 + k) (by omega))
  let σ : ∀ i, G i := fun i => ∑' k, E i (i + 1 + k)
  have hshift : ∀ j, φ (Nat.le_succ j) (σ (j + 1)) = σ j - E j (j + 1) := by
    intro j
    have h1 : HasSum (fun k => φ (Nat.le_succ j) (E (j + 1) (j + 1 + 1 + k)))
        (φ (Nat.le_succ j) (σ (j + 1))) :=
      (hsum (j + 1)).hasSum.map (φ (Nat.le_succ j)) (hcont _)
    have h2 : HasSum (fun k => E j (j + 1 + (k + 1))) (σ j - E j (j + 1)) := by
      simpa using (hasSum_nat_add_iff' (f := fun k => E j (j + 1 + k)) 1).2 (hsum j).hasSum
    have h3 : (fun k => φ (Nat.le_succ j) (E (j + 1) (j + 1 + 1 + k))) =
        fun k => E j (j + 1 + (k + 1)) := by
      funext k
      rw [hEφ j _ (by omega)]
      congr 1
      omega
    rw [h3] at h1
    exact h1.unique h2
  refine ⟨fun j => e j + σ j - d j, fun j => ?_⟩
  simp only [map_sub, map_add, hshift, hE j (j + 1) (Nat.le_succ j)]
  simp only [e]
  abel

/-- **`lim¹` of a tower through subgroups containing the images.** Let `ρ : G_{j+1} → G_j` be a
tower of abelian groups and `Q_j ≤ G_j` subgroups containing the image of `ρ`. If every sequence
`σ_j ∈ Q_j` has the form `v_j - ρ(v_{j+1})` with `v_j ∈ Q_j`, then so does every sequence
`s_j ∈ G_j`, with `t_j ∈ G_j`. -/
theorem exists_sub_eq_of_forall_mem {G : ℕ → Type*} [∀ j, AddCommGroup (G j)]
    (ρ : ∀ j, G (j + 1) →+ G j) (Q : ∀ j, AddSubgroup (G j)) (hρ : ∀ j x, ρ j x ∈ Q j)
    (hQ : ∀ σ : ∀ j, Q j, ∃ v : ∀ j, Q j, ∀ j, (σ j : G j) = v j - ρ j (v (j + 1)))
    (s : ∀ j, G j) : ∃ t : ∀ j, G j, ∀ j, s j = t j - ρ j (t (j + 1)) := by
  obtain ⟨v, hv⟩ := hQ fun j => ⟨ρ j (s (j + 1)), hρ j _⟩
  refine ⟨fun j => s j + v j, fun j => ?_⟩
  simp only [map_add, show ρ j (s (j + 1)) = _ from hv j]
  abel

end MMP.Topology
