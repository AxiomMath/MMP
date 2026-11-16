module
public import Mathlib
public import MMP.Attr
public import MMP.Combinatorics.WeightedGraph.Shapes
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedGraphLogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform

/-!
# Log canonical and log terminal rational trees

A negative definite rational tree `Γ` with all boundary degrees `β_j = 0` whose log
discrepancy vector `a(Γ)` is nonnegative is one of the following: a weighted chain; a star with
three arms whose arm determinants `(Δ_1, Δ_2, Δ_3)`, up to order, are `(2, 2, m)` with `m ≥ 2`,
`(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)`, `(2, 3, 6)`, `(2, 4, 4)` or `(3, 3, 3)`; a vertex with
four neighbours of weight `2` and no other vertices; or a chain `w_1, …, w_s` (`s ≥ 2`) with two
weight-`2` leaves attached at each end. If `a(Γ)` is positive, only the chains and the stars
`(2, 2, m)`, `(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)` remain: in every other case some log
discrepancy vanishes.

With boundary, let `f` be the minimal resolution of a surface germ `(X, P; B)` over an
algebraically closed field with weighted dual graph `Γ = Γ(f)`. If `Γ` is a rational tree, some
`β_j` is positive and `a(Γ) ≥ 0`, then the graph `Γ⁰` obtained by setting every `β_j` to `0` is
a proper subgraph of `Γ`, so `a(Γ⁰) > a(Γ) ≥ 0`, and the log terminal list for `Γ⁰`, which has
the same underlying weighted tree, is the list for `Γ`.

## Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.isWeightedChain_or_isStar_or_of_nonneg`:
  the log canonical list without boundary.
* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.isWeightedChain_or_isStar_of_pos`:
  the log terminal list without boundary.
* `MMP.Flips.IsMinimalGermResolution.isWeightedChain_or_isStar_of_boundary_pos`: with some
  positive boundary degree, a log canonical rational tree is on the log terminal list.

## Implementation notes

The components of `Γ - x` are described as *branches*: for a neighbour `y` of `x`, the branch
at `x` through `y` is the set of vertices joined to `y` by a walk avoiding `x`. Shapes (chains,
stars, forked branches, the graphs of FA Fig. 2) are recognised from the degrees of the
vertices. A graph which is not on the list contains a connected induced subgraph `Γ|_S` with
one of the shapes of FA 3.2.6, whose log discrepancy at a vertex is negative; the degrees of
`Γ|_S` are pinned down by the count `∑ (deg - 2) = -2` for a tree, from a lower bound on the
degree of a few vertices and an upper bound on the number of leaves.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.2.7, 3.3.1
-/

@[expose] public section

universe u

namespace MMP.Flips.WeightedGraph

open Finset SimpleGraph

/-! ### Chains in a graph -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finset `X` that is connected inside itself, in which every vertex has at most two
neighbours and `w` at most one, is enumerated as a chain starting at `w`. -/
private theorem exists_chain_enum : ∀ (n : ℕ) (X : Finset V) (w : V), #X = n → w ∈ X →
    (∀ z ∈ X, ∃ p : G.Walk w z, ∀ t ∈ p.support, t ∈ X) →
    (∀ z ∈ X, #{y ∈ X | G.Adj z y} ≤ 2) → #{y ∈ X | G.Adj w y} ≤ 1 →
    ∃ (s : ℕ) (e : Fin (s + 1) → V), Function.Injective e ∧ (∀ z, z ∈ X ↔ ∃ i, e i = z) ∧
      e 0 = w ∧ ∀ i j, G.Adj (e i) (e j) ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)
  | 0, X, w, hn, hw, _, _, _ => by
    rw [card_eq_zero] at hn
    simp [hn] at hw
  | n + 1, X, w, hn, hw, hconn, hdeg, hw1 => by
    by_cases hX : X = {w}
    · refine ⟨0, fun _ => w, fun i j _ => Fin.ext (by have := i.2; have := j.2; omega),
        fun z => ?_, rfl,
        fun i j => ?_⟩
      · simp [hX, eq_comm]
      · simp [Fin.val_eq_zero]
    obtain ⟨z, hzX, hzw⟩ : ∃ z ∈ X, z ≠ w := by
      by_contra h
      push Not at h
      exact hX (eq_singleton_iff_unique_mem.2 ⟨hw, h⟩)
    obtain ⟨w', hww', hw'X⟩ : ∃ w', G.Adj w w' ∧ w' ∈ X := by
      obtain ⟨p, hp⟩ := hconn z hzX
      cases p with
      | nil => exact absurd rfl hzw
      | cons h q => exact ⟨_, h, hp _ (by simp)⟩
    have huniq : ∀ t ∈ X, G.Adj w t → t = w' := fun t ht hwt =>
      card_le_one.1 hw1 t (mem_filter.2 ⟨ht, hwt⟩) w' (mem_filter.2 ⟨hw'X, hww'⟩)
    have hw'w : w' ≠ w := hww'.ne'
    obtain ⟨s, e, hinj, hmem, he0, hadj⟩ := exists_chain_enum n (X.erase w) w'
      (by rw [card_erase_of_mem hw, hn]; rfl) (mem_erase.2 ⟨hw'w, hw'X⟩)
      (fun z hz => by
        obtain ⟨hzw, hzX⟩ := mem_erase.1 hz
        obtain ⟨p, hp⟩ := hconn z hzX
        have hqX : ∀ t ∈ (p.toPath : G.Walk w z).support, t ∈ X := fun t ht =>
          hp t (p.support_toPath_subset ht)
        have hq := p.toPath.2
        generalize (p.toPath : G.Walk w z) = q at hqX hq
        clear hp
        cases q with
        | nil => exact absurd rfl hzw
        | cons h r =>
          rw [Walk.cons_isPath_iff] at hq
          obtain rfl := huniq _ (hqX _ (by simp)) h
          exact ⟨r, fun t ht => mem_erase.2 ⟨fun e => hq.2 (e ▸ ht), hqX t (by simp [ht])⟩⟩)
      (fun z hz => (card_le_card fun t ht => by
          simp only [mem_filter, mem_erase] at ht ⊢
          exact ⟨ht.1.2, ht.2⟩).trans (hdeg z (mem_of_mem_erase hz)))
      (by
        have hsub : {y ∈ X.erase w | G.Adj w' y} ⊆ {y ∈ X | G.Adj w' y}.erase w := by
          intro t ht
          simp only [mem_filter, mem_erase] at ht ⊢
          exact ⟨ht.1.1, ht.1.2, ht.2⟩
        have h2 : #({y ∈ X | G.Adj w' y}.erase w) ≤ 1 := by
          rw [card_erase_of_mem (mem_filter.2 ⟨hw, hww'.symm⟩)]
          exact Nat.sub_le_iff_le_add.2 ((hdeg w' hw'X).trans (by norm_num))
        exact (card_le_card hsub).trans h2)
    have he'X : ∀ i, e i ∈ X.erase w := fun i => (hmem _).2 ⟨i, rfl⟩
    refine ⟨s + 1, Fin.cons w e, ?_, fun z => ?_, rfl, fun i j => ?_⟩
    · refine Fin.cons_injective_iff.2 ⟨fun ⟨i, hi⟩ => ?_, hinj⟩
      exact (mem_erase.1 (he'X i)).1 hi
    · rw [Fin.exists_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ← hmem, mem_erase]
      refine ⟨fun hz => (eq_or_ne z w).imp Eq.symm fun h => ⟨h, hz⟩, ?_⟩
      rintro (rfl | ⟨-, hz⟩)
      · exact hw
      · exact hz
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
          constructor
          · intro h
            obtain rfl := hinj ((huniq _ (mem_of_mem_erase (he'X j)) h).trans he0.symm)
            simp
          · intro h
            obtain rfl : j = 0 := Fin.ext (by simp at h ⊢; omega)
            rw [he0]
            exact hww'
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
          constructor
          · intro h
            obtain rfl := hinj ((huniq _ (mem_of_mem_erase (he'X i)) h.symm).trans he0.symm)
            simp
          · intro h
            obtain rfl : i = 0 := Fin.ext (by simp at h ⊢; omega)
            rw [he0]
            exact hww'.symm
        | succ j =>
          simp only [Fin.cons_succ, Fin.val_succ, hadj]
          omega

/-- An interior vertex of a path has two distinct neighbours on the path. -/
private theorem exists_adj_adj_of_mem_support : ∀ {a b : V} (p : G.Walk a b), p.IsPath →
    ∀ {x : V}, x ∈ p.support → x ≠ a → x ≠ b →
      ∃ y ∈ p.support, ∃ z ∈ p.support, y ≠ z ∧ G.Adj x y ∧ G.Adj x z
  | _, _, .nil, _, x, hx, hxa, _ => by
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hxa
  | a, b, .cons (v := c) h q, hp, x, hx, hxa, hxb => by
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hx
    have hxq := hx.resolve_left hxa
    by_cases hxc : x = c
    · subst hxc
      cases q with
      | nil => exact absurd rfl hxb
      | cons h' q' =>
        refine ⟨a, by simp, _, by simp, fun e => hp.2 ?_, h.symm, h'⟩
        subst e
        simp
    · obtain ⟨y, hy, z, hz, hyz, h1, h2⟩ := exists_adj_adj_of_mem_support q hp.1 hxq hxc hxb
      exact ⟨y, by simp [hy], z, by simp [hz], hyz, h1, h2⟩

/-! ### Walks avoiding a vertex -/

/-- `a` and `b` are joined by a walk avoiding `x`. -/
private def ReachAvoid (x a b : V) : Prop := ∃ p : G.Walk a b, x ∉ p.support

variable {G}

private theorem ReachAvoid.refl {x a : V} (ha : a ≠ x) : ReachAvoid G x a a :=
  ⟨.nil, by simpa using ha.symm⟩

private theorem ReachAvoid.symm {x a b : V} (h : ReachAvoid G x a b) : ReachAvoid G x b a :=
  let ⟨p, hp⟩ := h; ⟨p.reverse, by simpa using hp⟩

private theorem ReachAvoid.trans {x a b c : V} (h : ReachAvoid G x a b)
    (h' : ReachAvoid G x b c) : ReachAvoid G x a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨p.append q, fun hx => ?_⟩
  rw [Walk.support_append, List.mem_append] at hx
  exact hx.elim hp fun h => hq (List.mem_of_mem_tail h)

private theorem ReachAvoid.of_adj {x a b : V} (h : G.Adj a b) (ha : a ≠ x) (hb : b ≠ x) :
    ReachAvoid G x a b :=
  ⟨.cons h .nil, by simp [ha.symm, hb.symm]⟩

private theorem ReachAvoid.ne_left {x a b : V} (h : ReachAvoid G x a b) : a ≠ x := by
  obtain ⟨p, hp⟩ := h
  rintro rfl
  exact hp p.start_mem_support

private theorem ReachAvoid.ne_right {x a b : V} (h : ReachAvoid G x a b) : b ≠ x := by
  obtain ⟨p, hp⟩ := h
  rintro rfl
  exact hp p.end_mem_support

private theorem reachAvoid_of_mem_support {x a b t : V} (p : G.Walk a b) (hp : x ∉ p.support)
    (ht : t ∈ p.support) : ReachAvoid G x a t :=
  ⟨p.takeUntil t ht, fun h => hp (p.support_takeUntil_subset ht h)⟩

/-- In an acyclic graph, two neighbours of `x` joined by a walk avoiding `x` are equal. -/
private theorem eq_of_reachAvoid (hac : G.IsAcyclic) {x y y' : V} (h : G.Adj x y)
    (h' : G.Adj x y') (hr : ReachAvoid G x y y') : y = y' := by
  by_contra hne
  obtain ⟨p, hp⟩ := hr
  have hq : x ∉ p.toPath.1.support := fun hx => hp (p.support_toPath_subset hx)
  let r : G.Path y y' := ⟨.cons h.symm (.cons h' .nil), by
    simp [Walk.cons_isPath_iff, h.ne', h'.ne, hne]⟩
  apply hq
  rw [hac.path_unique p.toPath r]
  simp [r]

/-- In a connected graph every vertex `z ≠ x` is joined to a neighbour of `x` by a walk
avoiding `x`. -/
private theorem exists_adj_reachAvoid (hc : G.Connected) {x z : V} (hz : z ≠ x) :
    ∃ y, G.Adj x y ∧ ReachAvoid G x y z := by
  obtain ⟨p, hp⟩ := (hc.preconnected x z).some.toPath
  cases p with
  | nil => exact absurd rfl hz
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hp
    exact ⟨_, h, q, hp.2⟩

variable (G) in
/-- The branch at `x` through `y`: the vertices joined to `y` by a walk avoiding `x`. -/
private noncomputable def branch (x y : V) : Finset V :=
  open Classical in {z | ReachAvoid G x y z}

private theorem mem_branch {x y z : V} : z ∈ branch G x y ↔ ReachAvoid G x y z := by
  simp [branch]

private theorem self_mem_branch {x y : V} (h : y ≠ x) : y ∈ branch G x y :=
  mem_branch.2 (.refl h)

private theorem notMem_branch {x y : V} : x ∉ branch G x y := fun h =>
  (mem_branch.1 h).ne_right rfl

private theorem ne_of_mem_branch {x y z : V} (h : z ∈ branch G x y) : z ≠ x :=
  (mem_branch.1 h).ne_right

private theorem mem_branch_of_adj {x y z t : V} (hz : z ∈ branch G x y) (h : G.Adj z t)
    (ht : t ≠ x) : t ∈ branch G x y :=
  mem_branch.2 ((mem_branch.1 hz).trans (.of_adj h (ne_of_mem_branch hz) ht))

private theorem eq_of_mem_branch (hac : G.IsAcyclic) {x y t : V} (hxy : G.Adj x y)
    (ht : t ∈ branch G x y) (hxt : G.Adj x t) : t = y :=
  (eq_of_reachAvoid hac hxy hxt (mem_branch.1 ht)).symm

private theorem disjoint_branch (hac : G.IsAcyclic) {x y y' : V} (h : G.Adj x y)
    (h' : G.Adj x y') (hne : y ≠ y') : Disjoint (branch G x y) (branch G x y') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne (eq_of_reachAvoid hac h h' ((mem_branch.1 hz).trans (mem_branch.1 hz').symm))

private theorem exists_mem_branch (hc : G.Connected) {x z : V} (hz : z ≠ x) :
    ∃ y, G.Adj x y ∧ z ∈ branch G x y := by
  obtain ⟨y, h, hr⟩ := exists_adj_reachAvoid hc hz
  exact ⟨y, h, mem_branch.2 hr⟩

/-- A vertex of a branch is joined to its root by a walk inside the branch. -/
private theorem exists_walk_subset_branch {x y z : V} (hz : z ∈ branch G x y) :
    ∃ p : G.Walk y z, ∀ t ∈ p.support, t ∈ branch G x y := by
  obtain ⟨p, hp⟩ := mem_branch.1 hz
  exact ⟨p, fun t ht => mem_branch.2 (reachAvoid_of_mem_support p hp ht)⟩

/-- In the enumeration of a chain, a vertex other than the first with at most one neighbour in
the chain is the last one. -/
private theorem eq_last_of_card_le_one {X : Finset V} {s : ℕ} {e : Fin (s + 1) → V}
    (hinj : Function.Injective e) (hmem : ∀ z, z ∈ X ↔ ∃ i, e i = z)
    (hadj : ∀ i j, G.Adj (e i) (e j) ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i))
    {i : Fin (s + 1)} (hi : i ≠ 0) (hdeg : #{t ∈ X | G.Adj (e i) t} ≤ 1) :
    i = Fin.last s := by
  by_contra hl
  have h1 : (i : ℕ) < s := lt_of_le_of_ne (Fin.is_le i) fun h => hl (Fin.ext h)
  have h0 : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun h => hi (Fin.ext h)
  have : 1 < #{t ∈ X | G.Adj (e i) t} := one_lt_card.2
    ⟨e ⟨i + 1, by omega⟩, mem_filter.2 ⟨(hmem _).2 ⟨_, rfl⟩, (hadj _ _).2 (Or.inl rfl)⟩,
      e ⟨i - 1, by omega⟩, mem_filter.2 ⟨(hmem _).2 ⟨_, rfl⟩, (hadj _ _).2 (Or.inr (by
        simp only; omega))⟩,
      fun h => by have := congrArg Fin.val (hinj h); simp only at this; omega⟩
  omega

/-- **Degree count in a tree.** If every vertex outside `L` has degree at least `2` and every
vertex of `L` degree at least `1`, then `∑ (deg x - 2)₊ + 2 ≤ #L`. -/
private theorem sum_degree_sub_two_add_two_le (hT : G.IsTree) (L : Finset V)
    (h1 : ∀ x ∈ L, 1 ≤ G.degree x) (h2 : ∀ x ∉ L, 2 ≤ G.degree x) :
    ∑ x, (G.degree x - 2) + 2 ≤ #L := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hcard := hT.card_edgeFinset
  have key : ∀ x ∈ (univ : Finset V), ((G.degree x - 2 : ℕ) : ℤ) ≤
      (G.degree x : ℤ) - 2 + (if x ∈ L then 1 else 0) := by
    intro x _
    split_ifs with hx
    · have := h1 x hx; omega
    · have := h2 x hx; omega
  have := Finset.sum_le_sum key
  have e1 : (∑ x, (G.degree x : ℤ)) = 2 * #G.edgeFinset := by exact_mod_cast hsum
  have e2 : ∑ x : V, (if x ∈ L then (1 : ℤ) else 0) = #L := by
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
  have e3 : ∑ _x : V, (2 : ℤ) = 2 * Fintype.card V := by
    rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  have e4 : ((#G.edgeFinset : ℕ) : ℤ) + 1 = Fintype.card V := by exact_mod_cast hcard
  rw [sum_add_distrib, sum_sub_distrib, e1, e2, e3] at this
  have h : ((∑ x, (G.degree x - 2) : ℕ) : ℤ) + 2 ≤ #L := by push_cast; linarith
  exact_mod_cast h

end Graph

/-! ### Shapes recognised from degrees -/

section Shapes

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

private theorem edgeWeight_eq_ite (hs : Γ.HasSimpleEdges) (j k : V) :
    Γ.edgeWeight j k = if Γ.underlyingGraph.Adj j k then 1 else 0 := by
  split_ifs with h
  · exact (hs j k h).2
  · by_contra hne
    by_cases hjk : j = k
    · subst hjk
      exact hne (Γ.edgeWeight_self j)
    · exact h ⟨hjk, Nat.pos_of_ne_zero hne⟩

private theorem hasSimpleEdges_of_isRationalTree (hΓ : Γ.IsRationalTree) : Γ.HasSimpleEdges :=
  fun j k h => ⟨h.1, le_antisymm (hΓ.edgeWeight_le_one j k) h.2⟩

/-- A branch at `x` is a component of `Γ - x`. -/
private theorem isComponent_branch {x y : V} (hy : y ≠ x) :
    Γ.IsComponentOfRemoveVertex x (branch Γ.underlyingGraph x y) := by
  have hm : ∀ {z : V}, z ≠ x → z ∈ (univ \ {x} : Finset V) := fun h => by simp [h]
  let φ : Γ.underlyingGraph.induce ({x}ᶜ : Set V) →g (Γ.removeVertex x).underlyingGraph :=
    { toFun := fun z => ⟨z.1, hm z.2⟩
      map_rel' := fun {a b} h =>
        ⟨fun e => h.1 (congrArg (fun z : ↥(univ \ {x} : Finset V) => (z : V)) e), h.2⟩ }
  let ψ : (Γ.removeVertex x).underlyingGraph →g Γ.underlyingGraph :=
    { toFun := Subtype.val
      map_rel' := fun {a b} h => ⟨fun e => h.1 (Subtype.ext e), h.2⟩ }
  refine ⟨(Γ.removeVertex x).underlyingGraph.connectedComponentMk ⟨y, hm hy⟩, ?_⟩
  ext z
  simp only [Finset.mem_coe, Set.mem_image, ConnectedComponent.mem_supp_iff]
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := mem_branch.1 hz
    have hw : ∀ t ∈ p.support, t ∈ ({x}ᶜ : Set V) := fun t ht e => hp (e ▸ ht)
    refine ⟨⟨z, hm (ne_of_mem_branch hz)⟩, ?_, rfl⟩
    exact ConnectedComponent.eq.2 ⟨((p.induce _ hw).map φ).reverse⟩
  · rintro ⟨⟨z, hz⟩, hc, rfl⟩
    obtain ⟨q⟩ := (ConnectedComponent.eq.1 hc).symm
    refine mem_branch.2 ⟨q.map ψ, fun hx => ?_⟩
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨t, -, ht⟩ := hx
    have ht' : (t : V) = x := ht
    exact (mem_sdiff.1 t.2).2 (mem_singleton.2 ht')

/-- A walk avoiding `v` gives reachability in the graph induced on `{v}ᶜ`. -/
private theorem reachable_induce_of_reachAvoid {G : SimpleGraph V} [DecidableRel G.Adj]
    {v a b : V}
    (h : ReachAvoid G v a b) :
    (G.induce ({v}ᶜ : Set V)).Reachable ⟨a, h.ne_left⟩ ⟨b, h.ne_right⟩ := by
  obtain ⟨p, hp⟩ := h
  have hw : ∀ t ∈ p.support, t ∈ ({v}ᶜ : Set V) := fun t ht e => hp (e ▸ ht)
  exact ⟨p.induce _ hw⟩

/-- An injective enumeration of `C` along which the adjacencies are the consecutive ones is a
chain order of `Γ|_C`. -/
private theorem exists_isChainOrder_restrict (hs : Γ.HasSimpleEdges) (hp : ∀ j, Γ.genus j = 0)
    {C : Finset V} {s : ℕ} {e : Fin (s + 1) → V} (hinj : Function.Injective e)
    (hmem : ∀ z, z ∈ C ↔ ∃ i, e i = z)
    (hadj : ∀ i j, Γ.underlyingGraph.Adj (e i) (e j) ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)) :
    ∃ E : Fin (s + 1) ≃ C, (Γ.restrict C).IsChainOrder E ∧ ∀ i, (E i : V) = e i := by
  refine ⟨Equiv.ofBijective (fun i => ⟨e i, (hmem _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hinj (congrArg Subtype.val h), fun z => ?_⟩, ⟨fun i => hp _, fun i j => ?_⟩,
    fun i => rfl⟩
  · obtain ⟨i, hi⟩ := (hmem z).1 z.2
    exact ⟨i, Subtype.ext hi⟩
  · show Γ.edgeWeight (e i) (e j) = _
    rw [edgeWeight_eq_ite Γ hs]
    exact if_congr (hadj i j) rfl rfl

variable {Γ}

/-- A branch all of whose vertices have degree at most `2` is a chain attached at an end. -/
private theorem isChainAttachedAtEnd_branch (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {x y : V} (hxy : Γ.underlyingGraph.Adj x y)
    (hdeg : ∀ z ∈ branch Γ.underlyingGraph x y, Γ.underlyingGraph.degree z ≤ 2) :
    Γ.IsChainAttachedAtEnd x (branch Γ.underlyingGraph x y) := by
  have hyC : y ∈ branch Γ.underlyingGraph x y := self_mem_branch hxy.ne'
  obtain ⟨s, e, hinj, hmem, he0, hadj⟩ := exists_chain_enum Γ.underlyingGraph _
    (branch Γ.underlyingGraph x y) y rfl hyC (fun z hz => exists_walk_subset_branch hz)
    (fun z hz => (card_le_card fun t ht => (mem_neighborFinset _ _ _).2 (mem_filter.1 ht).2).trans
      ((card_neighborFinset_eq_degree _ _).le.trans (hdeg z hz)))
    (by
      have hsub : {t ∈ branch Γ.underlyingGraph x y | Γ.underlyingGraph.Adj y t} ⊆
          (Γ.underlyingGraph.neighborFinset y).erase x := fun t ht =>
        mem_erase.2 ⟨ne_of_mem_branch (mem_filter.1 ht).1,
          (mem_neighborFinset _ _ _).2 (mem_filter.1 ht).2⟩
      refine (card_le_card hsub).trans ?_
      rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hxy.symm),
        card_neighborFinset_eq_degree]
      have := hdeg y hyC
      omega)
  obtain ⟨E, hE, hEe⟩ := exists_isChainOrder_restrict Γ hs hp hinj hmem hadj
  have h0 : (E ⟨0, s.succ_pos⟩ : V) = y := by rw [hEe, ← he0]; rfl
  refine ⟨hT, isComponent_branch Γ hxy.ne', s + 1, s.succ_pos, E, hE, by rw [h0]; exact hxy,
    fun w hw hxw => ?_⟩
  rw [h0]
  exact eq_of_mem_branch hT.isAcyclic hxy hw hxw

/-- A branch at `u` that does not contain `x` lies in any branch at `x` containing `u`. -/
private theorem branch_subset_branch {G : SimpleGraph V} [DecidableRel G.Adj] {x w u a : V}
    (hu : u ∈ branch G x w) (hua : G.Adj u a) (hxa : x ∉ branch G u a) :
    branch G u a ⊆ branch G x w := by
  intro z hz
  obtain ⟨p, hp⟩ := mem_branch.1 hz
  have hpx : x ∉ p.support := fun hx => hxa (mem_branch.2 (reachAvoid_of_mem_support p hp hx))
  have hax : a ≠ x := fun h => hxa (h ▸ self_mem_branch hua.ne')
  exact mem_branch.2 ((mem_branch.1 hu).trans
    ((ReachAvoid.of_adj hua (ne_of_mem_branch hu) hax).trans ⟨p, hpx⟩))

/-- A branch at `x` containing one vertex `u` of degree `3` and otherwise only vertices of
degree at most `2` is a forked branch with fork `u`. -/
private theorem exists_isForkedBranch_branch (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {x w u : V} (hxw : Γ.underlyingGraph.Adj x w)
    (hu : u ∈ branch Γ.underlyingGraph x w) (hdu : Γ.underlyingGraph.degree u = 3)
    (hdeg : ∀ z ∈ branch Γ.underlyingGraph x w, z ≠ u → Γ.underlyingGraph.degree z ≤ 2) :
    ∃ A B, Γ.IsForkedBranch x (branch Γ.underlyingGraph x w) u A B := by
  have hac := hT.isAcyclic
  have hc := hT.connected
  have hux : u ≠ x := ne_of_mem_branch hu
  obtain ⟨n0, hun0, hxn0⟩ := exists_mem_branch hc hux.symm
  have hcard : #((Γ.underlyingGraph.neighborFinset u).erase n0) = 2 := by
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hun0), card_neighborFinset_eq_degree,
      hdu]
  obtain ⟨a, b, hab, hNe⟩ := card_eq_two.1 hcard
  have ha : a ∈ (Γ.underlyingGraph.neighborFinset u).erase n0 := by rw [hNe]; simp
  have hb : b ∈ (Γ.underlyingGraph.neighborFinset u).erase n0 := by rw [hNe]; simp
  obtain ⟨han0, hua⟩ := mem_erase.1 ha
  obtain ⟨hbn0, hub⟩ := mem_erase.1 hb
  rw [mem_neighborFinset] at hua hub
  have hnb : ∀ t, Γ.underlyingGraph.Adj u t → t = n0 ∨ t = a ∨ t = b := fun t ht => by
    by_cases h : t = n0
    · exact Or.inl h
    · have : t ∈ (Γ.underlyingGraph.neighborFinset u).erase n0 :=
        mem_erase.2 ⟨h, (mem_neighborFinset _ _ _).2 ht⟩
      rw [hNe] at this
      simp only [mem_insert, mem_singleton] at this
      exact Or.inr this
  have hd0A := disjoint_branch hac hun0 hua (Ne.symm han0)
  have hd0B := disjoint_branch hac hun0 hub (Ne.symm hbn0)
  have hdAB := disjoint_branch hac hua hub hab
  have hxA : x ∉ branch Γ.underlyingGraph u a := Finset.disjoint_left.1 hd0A hxn0
  have hxB : x ∉ branch Γ.underlyingGraph u b := Finset.disjoint_left.1 hd0B hxn0
  have hAC := branch_subset_branch hu hua hxA
  have hBC := branch_subset_branch hu hub hxB
  set C := branch Γ.underlyingGraph x w with hCdef
  set A := branch Γ.underlyingGraph u a with hAdef
  set B := branch Γ.underlyingGraph u b with hBdef
  set X := C \ (A ∪ B) with hXdef
  have hmemX : ∀ z, z ∈ X ↔ z ∈ C ∧ z ∉ A ∧ z ∉ B := fun z => by
    simp only [hXdef, mem_sdiff, mem_union, not_or]
  have hwC : w ∈ C := self_mem_branch hxw.ne'
  have hwX : w ∈ X := (hmemX w).2 ⟨hwC, fun h => hxA (mem_branch_of_adj h hxw.symm hux.symm),
    fun h => hxB (mem_branch_of_adj h hxw.symm hux.symm)⟩
  have huX : u ∈ X := (hmemX u).2 ⟨hu, notMem_branch, notMem_branch⟩
  have hX0 : ∀ z ∈ X, z ≠ u → z ∈ branch Γ.underlyingGraph u n0 := fun z hz hzu => by
    obtain ⟨n, hun, hzn⟩ := exists_mem_branch hc hzu
    obtain ⟨-, hzA, hzB⟩ := (hmemX z).1 hz
    rcases hnb n hun with rfl | rfl | rfl
    · exact hzn
    · exact absurd hzn hzA
    · exact absurd hzn hzB
  have hXu : ∀ t ∈ X, Γ.underlyingGraph.Adj u t → t = n0 := fun t ht hut => by
    obtain ⟨-, htA, htB⟩ := (hmemX t).1 ht
    rcases hnb t hut with h | rfl | rfl
    · exact h
    · exact absurd (self_mem_branch hua.ne') htA
    · exact absurd (self_mem_branch hub.ne') htB
  have hcu : #{t ∈ X | Γ.underlyingGraph.Adj u t} ≤ 1 :=
    card_le_one.2 fun t ht t' ht' => by
      rw [hXu t (mem_filter.1 ht).1 (mem_filter.1 ht).2,
        hXu t' (mem_filter.1 ht').1 (mem_filter.1 ht').2]
  have hconn' : ∀ z ∈ X, z ≠ u →
      ∃ p : Γ.underlyingGraph.Walk w z, ∀ t ∈ p.support, t ∈ X := fun z hz hzu => by
    have hz0 := hX0 z hz hzu
    have hzC := ((hmemX z).1 hz).1
    obtain ⟨r, hr⟩ := (mem_branch.1 hxn0).symm.trans (mem_branch.1 hz0)
    have hr' : u ∉ (r.toPath : Γ.underlyingGraph.Walk x z).support := fun h =>
      hr (r.support_toPath_subset h)
    have hrp := r.toPath.2
    generalize (r.toPath : Γ.underlyingGraph.Walk x z) = q at hr' hrp
    cases q with
    | nil => exact absurd rfl (ne_of_mem_branch hzC)
    | cons h q =>
      rw [Walk.cons_isPath_iff] at hrp
      rw [Walk.support_cons, List.mem_cons, not_or] at hr'
      have hw' := eq_of_reachAvoid hac hxw h
        ((mem_branch.1 hzC).trans ⟨q.reverse, by simpa using hrp.2⟩)
      subst hw'
      refine ⟨q, fun t ht => (hmemX t).2
        ⟨mem_branch.2 (reachAvoid_of_mem_support q hrp.2 ht), ?_⟩⟩
      have ht0 : t ∈ branch Γ.underlyingGraph u n0 := mem_branch.2 ((mem_branch.1 hz0).trans
        (reachAvoid_of_mem_support q.reverse (by simpa using hr'.2) (by simpa using ht)))
      exact ⟨Finset.disjoint_left.1 hd0A ht0, Finset.disjoint_left.1 hd0B ht0⟩
  have hconnu : ∃ p : Γ.underlyingGraph.Walk w u, ∀ t ∈ p.support, t ∈ X := by
    by_cases hn0x : n0 = x
    · have : u = w := eq_of_mem_branch hac hxw hu (hn0x ▸ hun0.symm)
      rw [this]
      exact ⟨.nil, by simpa using hwX⟩
    · have hn0b := self_mem_branch (G := Γ.underlyingGraph) hun0.ne'
      have hn0X : n0 ∈ X := (hmemX n0).2 ⟨mem_branch_of_adj hu hun0 hn0x,
        Finset.disjoint_left.1 hd0A hn0b, Finset.disjoint_left.1 hd0B hn0b⟩
      obtain ⟨p, hp⟩ := hconn' n0 hn0X hun0.ne'
      refine ⟨p.concat hun0.symm, fun t ht => ?_⟩
      simp only [Walk.support_concat, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hp t ht
      · exact huX
  have hconn : ∀ z ∈ X, ∃ p : Γ.underlyingGraph.Walk w z, ∀ t ∈ p.support, t ∈ X :=
    fun z hz => by
      by_cases hzu : z = u
      · rw [hzu]; exact hconnu
      · exact hconn' z hz hzu
  have hdegX : ∀ z ∈ X, #{t ∈ X | Γ.underlyingGraph.Adj z t} ≤ 2 := fun z hz => by
    by_cases hzu : z = u
    · rw [hzu]; exact hcu.trans (by norm_num)
    · exact (card_le_card fun t ht => (mem_neighborFinset _ _ _).2 (mem_filter.1 ht).2).trans
        ((card_neighborFinset_eq_degree _ _).le.trans (hdeg z ((hmemX z).1 hz).1 hzu))
  have hdegw : #{t ∈ X | Γ.underlyingGraph.Adj w t} ≤ 1 := by
    by_cases hwu : w = u
    · rw [hwu]; exact hcu
    · have hsub : {t ∈ X | Γ.underlyingGraph.Adj w t} ⊆
          (Γ.underlyingGraph.neighborFinset w).erase x := fun t ht =>
        mem_erase.2 ⟨ne_of_mem_branch ((hmemX t).1 (mem_filter.1 ht).1).1,
          (mem_neighborFinset _ _ _).2 (mem_filter.1 ht).2⟩
      refine (card_le_card hsub).trans ?_
      rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hxw.symm),
        card_neighborFinset_eq_degree]
      have := hdeg w hwC hwu
      omega
  obtain ⟨s, e, hinj, hmem, he0, hadj⟩ :=
    exists_chain_enum Γ.underlyingGraph _ X w rfl hwX hconn hdegX hdegw
  have heX : ∀ i, e i ∈ X := fun i => (hmem _).2 ⟨i, rfl⟩
  have heC : ∀ i, e i ∈ C := fun i => ((hmemX _).1 (heX i)).1
  have he0' : e ⟨0, s.succ_pos⟩ = w := by rw [← he0]; rfl
  obtain ⟨iu, hiu⟩ := (hmem u).1 huX
  have hiu' : iu = Fin.last s := by
    by_cases h0 : iu = 0
    · have huw : u = w := by rw [← hiu, h0, he0]
      have hs0 : s = 0 := by
        by_contra hs
        have h1 : Γ.underlyingGraph.Adj (e 0) (e ⟨1, by omega⟩) := (hadj _ _).2 (Or.inl rfl)
        rw [he0, ← huw] at h1
        have h2 := hXu _ (heX _) h1
        have hn0x : x = n0 := eq_of_mem_branch hac hun0 hxn0 (by rw [huw]; exact hxw.symm)
        have h3 := heC ⟨1, by omega⟩
        rw [h2, ← hn0x] at h3
        exact notMem_branch h3
      subst hs0
      rw [h0]
      rfl
    · exact eq_last_of_card_le_one hinj hmem hadj h0 (by rw [hiu]; exact hcu)
  have hlast : e ⟨s + 1 - 1, by omega⟩ = u := by
    rw [← hiu, hiu']
    congr 1
  refine ⟨A, B, hs, hT, isComponent_branch Γ hxw.ne', s + 1, s.succ_pos, e, hinj, hlast, heC,
    by rw [he0']; exact hxw, fun z hz hxz => by rw [he0']; exact eq_of_mem_branch hac hxw hz hxz,
    fun t ht => (hadj _ _).2 (Or.inl rfl), fun t ht => ?_, by
      rw [degree_eq_underlyingGraph_degree]; exact hdu, ?_, hdAB,
    isChainAttachedAtEnd_branch hT hs hp hua fun z hz => hdeg z (hAC hz) (ne_of_mem_branch hz),
    isChainAttachedAtEnd_branch hT hs hp hub fun z hz => hdeg z (hBC hz) (ne_of_mem_branch hz)⟩
  · rw [degree_eq_underlyingGraph_degree]
    have hne : e ⟨t, by omega⟩ ≠ u := by
      rw [← hiu, hiu']
      intro h
      have := congrArg Fin.val (hinj h)
      simp only [Fin.val_last] at this
      omega
    refine le_antisymm (hdeg _ (heC _) hne) ?_
    rw [← card_neighborFinset_eq_degree]
    have hnext : e ⟨t + 1, ht⟩ ∈ Γ.underlyingGraph.neighborFinset (e ⟨t, by omega⟩) :=
      (mem_neighborFinset _ _ _).2 ((hadj _ _).2 (Or.inl rfl))
    obtain ⟨y, hy, hyne⟩ : ∃ y, Γ.underlyingGraph.Adj (e ⟨t, by omega⟩) y ∧
        y ≠ e ⟨t + 1, ht⟩ := by
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · refine ⟨x, by rw [he0']; exact hxw.symm, fun h => ?_⟩
        have h' := heC ⟨0 + 1, ht⟩
        rw [← h] at h'
        exact notMem_branch h'
      · refine ⟨e ⟨t - 1, by omega⟩, (hadj _ _).2 (Or.inr (by simp only; omega)), fun h => ?_⟩
        have := congrArg Fin.val (hinj h)
        simp only at this
        omega
    exact one_lt_card.2 ⟨_, (mem_neighborFinset _ _ _).2 hy, _, hnext, hyne⟩
  · have himg : univ.image e = X := by
      ext z
      simp [hmem z]
    rw [himg, hXdef, sdiff_sdiff_right_self, inf_eq_inter,
      inter_eq_right.2 (union_subset hAC hBC)]

/-- The number of neighbours of `z` in `X` is at most its degree. -/
private theorem card_filter_adj_le_degree (X : Finset V) (z : V) :
    #{t ∈ X | Γ.underlyingGraph.Adj z t} ≤ Γ.underlyingGraph.degree z :=
  (card_le_card fun t ht => (mem_neighborFinset _ _ _).2 (mem_filter.1 ht).2).trans
    (card_neighborFinset_eq_degree _ _).le

/-- A tree all of whose vertices have degree at most `2` is a weighted chain. -/
private theorem isWeightedChain_of_degree_le (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) (hdeg : ∀ z, Γ.underlyingGraph.degree z ≤ 2) :
    Γ.IsWeightedChain := by
  obtain ⟨w, hw⟩ : ∃ w, Γ.underlyingGraph.degree w ≤ 1 := by
    by_contra h
    push Not at h
    have hsum := Γ.underlyingGraph.sum_degrees_eq_twice_card_edges
    have hcard := hT.card_edgeFinset
    have : ∑ _x : V, 2 ≤ ∑ x, Γ.underlyingGraph.degree x := sum_le_sum fun x _ => h x
    rw [sum_const, card_univ, smul_eq_mul] at this
    omega
  obtain ⟨s, e, hinj, hmem, -, hadj⟩ := exists_chain_enum Γ.underlyingGraph _ univ w rfl
    (mem_univ w) (fun z _ => ⟨(hT.connected.preconnected w z).some, fun t _ => mem_univ t⟩)
    (fun z _ => (card_filter_adj_le_degree (Γ := Γ) _ z).trans (hdeg z))
    ((card_filter_adj_le_degree (Γ := Γ) _ w).trans hw)
  refine ⟨s + 1, Equiv.ofBijective e ⟨hinj, fun z => (hmem z).1 (mem_univ z)⟩,
    fun i => hp _, fun i j => ?_⟩
  show Γ.edgeWeight (e i) (e j) = _
  rw [edgeWeight_eq_ite Γ hs]
  exact if_congr (hadj i j) rfl rfl

/-- A tree in which every vertex other than `v` has degree at most `2` is a star at `v`. -/
private theorem exists_isStar (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {v : V} (hdeg : ∀ z, z ≠ v → Γ.underlyingGraph.degree z ≤ 2) :
    ∃ arms : Fin (Γ.degree v) → Finset V, Γ.IsStar v arms := by
  have hcard : #(Γ.underlyingGraph.neighborFinset v) = Γ.degree v := by
    rw [card_neighborFinset_eq_degree, degree_eq_underlyingGraph_degree]
  let nb : Fin (Γ.degree v) ≃ Γ.underlyingGraph.neighborFinset v :=
    (equivFinOfCardEq hcard).symm
  have hnb : ∀ i, Γ.underlyingGraph.Adj v (nb i) := fun i =>
    (mem_neighborFinset _ _ _).1 (nb i).2
  refine ⟨fun i => branch Γ.underlyingGraph v (nb i), hs, hT, rfl,
    fun i => isComponent_branch Γ (hnb i).ne', fun i j hij => disjoint_branch hT.isAcyclic
      (hnb i) (hnb j) (fun h => hij (nb.injective (Subtype.ext h))), ?_,
    fun i => isChainAttachedAtEnd_branch hT hs hp (hnb i) fun z hz =>
      hdeg z (ne_of_mem_branch hz)⟩
  ext z
  simp only [mem_biUnion, mem_univ, true_and, mem_sdiff, mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    exact ne_of_mem_branch hi
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_branch hT.connected hz
    refine ⟨nb.symm ⟨y, (mem_neighborFinset _ _ _).2 hy⟩, ?_⟩
    simpa using hzy

/-- A tree with a vertex `v` of degree `4`, a vertex `v'` of degree `3`, and all other degrees at
most `2` has Fig. 2(b) shape at `v`. -/
private theorem isFig2RightShape_of_degree (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {v v' : V} (hvv' : v' ≠ v)
    (hdv : Γ.underlyingGraph.degree v = 4) (hdv' : Γ.underlyingGraph.degree v' = 3)
    (hdeg : ∀ z, z ≠ v → z ≠ v' → Γ.underlyingGraph.degree z ≤ 2) : Γ.IsFig2RightShape v := by
  have hac := hT.isAcyclic
  have hc := hT.connected
  obtain ⟨n, hvn, hv'n⟩ := exists_mem_branch hc hvv'
  have hcard : #((Γ.underlyingGraph.neighborFinset v).erase n) = 3 := by
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hvn), card_neighborFinset_eq_degree, hdv]
  obtain ⟨p, q, r, hpq, hpr, hqr, hE⟩ := card_eq_three.1 hcard
  have hmem : ∀ t, t ∈ (Γ.underlyingGraph.neighborFinset v).erase n ↔ t = p ∨ t = q ∨ t = r :=
    fun t => by rw [hE]; simp
  obtain ⟨hpn, hvp⟩ := mem_erase.1 ((hmem p).2 (Or.inl rfl))
  obtain ⟨hqn, hvq⟩ := mem_erase.1 ((hmem q).2 (Or.inr (Or.inl rfl)))
  obtain ⟨hrn, hvr⟩ := mem_erase.1 ((hmem r).2 (Or.inr (Or.inr rfl)))
  rw [mem_neighborFinset] at hvp hvq hvr
  have hnbr : ∀ y, Γ.underlyingGraph.Adj v y → y = n ∨ y = p ∨ y = q ∨ y = r := fun y hy => by
    by_cases h : y = n
    · exact Or.inl h
    · exact Or.inr ((hmem y).1 (mem_erase.2 ⟨h, (mem_neighborFinset _ _ _).2 hy⟩))
  have chain : ∀ y, Γ.underlyingGraph.Adj v y → y ≠ n →
      Γ.IsChainAttachedAtEnd v (branch Γ.underlyingGraph v y) := fun y hy hyn =>
    isChainAttachedAtEnd_branch hT hs hp hy fun z hz => hdeg z (ne_of_mem_branch hz)
      (fun h => Finset.disjoint_left.1 (disjoint_branch hac hy hvn hyn) hz (h ▸ hv'n))
  obtain ⟨A, B, hF⟩ := exists_isForkedBranch_branch hT hs hp hvn hv'n hdv'
    fun z hz hzv' => hdeg z (ne_of_mem_branch hz) hzv'
  refine ⟨hs, hT, by rw [degree_eq_underlyingGraph_degree]; exact hdv,
    branch Γ.underlyingGraph v p, branch Γ.underlyingGraph v q, branch Γ.underlyingGraph v r,
    branch Γ.underlyingGraph v n, disjoint_branch hac hvp hvq hpq,
    disjoint_branch hac hvp hvr hpr, disjoint_branch hac hvp hvn hpn,
    disjoint_branch hac hvq hvr hqr, disjoint_branch hac hvq hvn hqn,
    disjoint_branch hac hvr hvn hrn, ?_, chain p hvp hpn, chain q hvq hqn, chain r hvr hrn,
    ⟨v', A, B, hF⟩⟩
  ext z
  simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_singleton]
  constructor
  · rintro (((h | h) | h) | h) <;> exact ne_of_mem_branch h
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_branch hc hz
    rcases hnbr y hy with rfl | rfl | rfl | rfl <;> simp [hzy]

/-- A tree with three vertices `v, a, b` of degree `3`, with `a` and `b` in different
components of `Γ - v`, and all other degrees at most `2`, has Fig. 2(a) shape at `v`. -/
private theorem isFig2LeftShape_of_degree (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {v a b : V} (hav : a ≠ v) (hbv : b ≠ v)
    (hab : ¬ ReachAvoid Γ.underlyingGraph v a b)
    (hdv : Γ.underlyingGraph.degree v = 3) (hda : Γ.underlyingGraph.degree a = 3)
    (hdb : Γ.underlyingGraph.degree b = 3)
    (hdeg : ∀ z, z ≠ v → z ≠ a → z ≠ b → Γ.underlyingGraph.degree z ≤ 2) :
    Γ.IsFig2LeftShape v := by
  have hac := hT.isAcyclic
  have hc := hT.connected
  obtain ⟨na, hvna, hana⟩ := exists_mem_branch hc hav
  obtain ⟨nb, hvnb, hbnb⟩ := exists_mem_branch hc hbv
  have hnab : na ≠ nb := by
    rintro rfl
    exact hab ((mem_branch.1 hana).symm.trans (mem_branch.1 hbnb))
  have hdab := disjoint_branch hac hvna hvnb hnab
  have hcard : #(((Γ.underlyingGraph.neighborFinset v).erase na).erase nb) = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hnab.symm, (mem_neighborFinset _ _ _).2 hvnb⟩),
      card_erase_of_mem ((mem_neighborFinset _ _ _).2 hvna), card_neighborFinset_eq_degree, hdv]
  obtain ⟨nc, hE⟩ := card_eq_one.1 hcard
  have hnc : nc ∈ ((Γ.underlyingGraph.neighborFinset v).erase na).erase nb := by
    rw [hE]; exact mem_singleton_self nc
  simp only [mem_erase, mem_neighborFinset] at hnc
  obtain ⟨hncb, hnca, hvnc⟩ := hnc
  have hnbr : ∀ y, Γ.underlyingGraph.Adj v y → y = na ∨ y = nb ∨ y = nc := fun y hy => by
    by_cases h1 : y = na
    · exact Or.inl h1
    by_cases h2 : y = nb
    · exact Or.inr (Or.inl h2)
    have : y ∈ ((Γ.underlyingGraph.neighborFinset v).erase na).erase nb :=
      mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, (mem_neighborFinset _ _ _).2 hy⟩⟩
    rw [hE, mem_singleton] at this
    exact Or.inr (Or.inr this)
  have hdac := disjoint_branch hac hvna hvnc hnca.symm
  have hdbc := disjoint_branch hac hvnb hvnc hncb.symm
  obtain ⟨A₂, B₂, hF₂⟩ := exists_isForkedBranch_branch hT hs hp hvna hana hda
    fun z hz hza => hdeg z (ne_of_mem_branch hz) hza
      (fun h => Finset.disjoint_left.1 hdab hz (h ▸ hbnb))
  obtain ⟨A₃, B₃, hF₃⟩ := exists_isForkedBranch_branch hT hs hp hvnb hbnb hdb
    fun z hz hzb => hdeg z (ne_of_mem_branch hz)
      (fun h => Finset.disjoint_left.1 hdab (h ▸ hana) hz) hzb
  refine ⟨hs, hT, by rw [degree_eq_underlyingGraph_degree]; exact hdv,
    branch Γ.underlyingGraph v nc, branch Γ.underlyingGraph v na, branch Γ.underlyingGraph v nb,
    hdac.symm, hdbc.symm, hdab, ?_,
    isChainAttachedAtEnd_branch hT hs hp hvnc fun z hz => hdeg z (ne_of_mem_branch hz)
      (fun h => Finset.disjoint_left.1 hdac (h ▸ hana) hz)
      (fun h => Finset.disjoint_left.1 hdbc (h ▸ hbnb) hz),
    ⟨a, A₂, B₂, hF₂⟩, ⟨b, A₃, B₃, hF₃⟩⟩
  ext z
  simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ((h | h) | h) <;> exact ne_of_mem_branch h
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_branch hc hz
    rcases hnbr y hy with rfl | rfl | rfl <;> simp [hzy]

/-- A tree with two vertices `v ≠ v'` of degree `3` and all other degrees at most `2` is a
two-fork graph. -/
private theorem exists_isTwoForkGraphWith_of_degree (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges)
    (hp : ∀ j, Γ.genus j = 0) {v v' : V} (hvv' : v' ≠ v)
    (hdv : Γ.underlyingGraph.degree v = 3) (hdv' : Γ.underlyingGraph.degree v' = 3)
    (hdeg : ∀ z, z ≠ v → z ≠ v' → Γ.underlyingGraph.degree z ≤ 2) :
    ∃ C₁ C₂ C₃ A B, Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B := by
  have hac := hT.isAcyclic
  have hc := hT.connected
  obtain ⟨n, hvn, hv'n⟩ := exists_mem_branch hc hvv'
  have hcard : #((Γ.underlyingGraph.neighborFinset v).erase n) = 2 := by
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hvn), card_neighborFinset_eq_degree, hdv]
  obtain ⟨p, q, hpq, hE⟩ := card_eq_two.1 hcard
  have hmem : ∀ t, t ∈ (Γ.underlyingGraph.neighborFinset v).erase n ↔ t = p ∨ t = q :=
    fun t => by rw [hE]; simp
  obtain ⟨hpn, hvp⟩ := mem_erase.1 ((hmem p).2 (Or.inl rfl))
  obtain ⟨hqn, hvq⟩ := mem_erase.1 ((hmem q).2 (Or.inr rfl))
  rw [mem_neighborFinset] at hvp hvq
  have hnbr : ∀ y, Γ.underlyingGraph.Adj v y → y = n ∨ y = p ∨ y = q := fun y hy => by
    by_cases h : y = n
    · exact Or.inl h
    · exact Or.inr ((hmem y).1 (mem_erase.2 ⟨h, (mem_neighborFinset _ _ _).2 hy⟩))
  have chain : ∀ y, Γ.underlyingGraph.Adj v y → y ≠ n →
      Γ.IsChainAttachedAtEnd v (branch Γ.underlyingGraph v y) := fun y hy hyn =>
    isChainAttachedAtEnd_branch hT hs hp hy fun z hz => hdeg z (ne_of_mem_branch hz)
      (fun h => Finset.disjoint_left.1 (disjoint_branch hac hy hvn hyn) hz (h ▸ hv'n))
  obtain ⟨A, B, hF⟩ := exists_isForkedBranch_branch hT hs hp hvn hv'n hdv'
    fun z hz hzv' => hdeg z (ne_of_mem_branch hz) hzv'
  refine ⟨_, _, _, A, B, hs, hT, hvv'.symm, by rw [degree_eq_underlyingGraph_degree]; exact hdv,
    disjoint_branch hac hvp hvq hpq, disjoint_branch hac hvp hvn hpn,
    disjoint_branch hac hvq hvn hqn, ?_, chain p hvp hpn, chain q hvq hqn, hF⟩
  ext z
  simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ((h | h) | h) <;> exact ne_of_mem_branch h
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_branch hc hz
    rcases hnbr y hy with rfl | rfl | rfl <;> simp [hzy]

end Shapes

/-! ### Induced subgraphs -/

section Restrict

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

private theorem adj_restrict (S : Finset V) (x y : S) :
    (Γ.restrict S).underlyingGraph.Adj x y ↔ Γ.underlyingGraph.Adj x y :=
  ⟨fun h => ⟨fun e => h.1 (Subtype.ext e), h.2⟩,
    fun h => ⟨fun e => h.1 (congrArg Subtype.val e), h.2⟩⟩

/-- The degree of a vertex of `Γ|_S` is its number of neighbours in `S`. -/
private theorem degree_restrict (S : Finset V) (x : S) :
    (Γ.restrict S).underlyingGraph.degree x = #{y ∈ S | Γ.underlyingGraph.Adj x y} := by
  rw [← card_neighborFinset_eq_degree]
  refine card_bij (fun y _ => (y : V)) (fun y hy => ?_) (fun y _ z _ h => Subtype.ext h)
    (fun y hy => ?_)
  · rw [mem_neighborFinset, adj_restrict] at hy
    exact mem_filter.2 ⟨y.2, hy⟩
  · obtain ⟨hyS, hy⟩ := mem_filter.1 hy
    exact ⟨⟨y, hyS⟩, by rw [mem_neighborFinset, adj_restrict]; exact hy, rfl⟩

private theorem card_le_degree_restrict {S T : Finset V} (hTS : T ⊆ S) {x : V} (hx : x ∈ S)
    (hT : ∀ y ∈ T, Γ.underlyingGraph.Adj x y) :
    #T ≤ (Γ.restrict S).underlyingGraph.degree ⟨x, hx⟩ := by
  rw [degree_restrict]
  exact card_le_card fun y hy => mem_filter.2 ⟨hTS hy, hT y hy⟩

/-- A walk of `Γ` inside `S` gives reachability in `Γ|_S`. -/
private theorem reachable_restrict {S : Finset V} {a b : V} (p : Γ.underlyingGraph.Walk a b)
    (hp : ∀ t ∈ p.support, t ∈ S) :
    (Γ.restrict S).underlyingGraph.Reachable ⟨a, hp a p.start_mem_support⟩
      ⟨b, hp b p.end_mem_support⟩ := by
  let φ : Γ.underlyingGraph.induce (S : Set V) →g (Γ.restrict S).underlyingGraph :=
    { toFun := fun z => ⟨z.1, z.2⟩
      map_rel' := fun {x y} h => (adj_restrict Γ S _ _).2 h }
  exact ⟨(p.induce (S : Set V) fun t ht => hp t ht).map φ⟩

/-- A walk of `Γ|_S` avoiding `x` gives a walk of `Γ` avoiding `x`. -/
private theorem reachAvoid_of_restrict {S : Finset V} {x a b : S}
    (h : ReachAvoid (Γ.restrict S).underlyingGraph x a b) :
    ReachAvoid Γ.underlyingGraph x a b := by
  obtain ⟨p, hp⟩ := h
  let f : (Γ.restrict S).underlyingGraph →g Γ.underlyingGraph :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h => (adj_restrict Γ S _ _).1 h }
  refine ⟨p.map f, fun hx => hp ?_⟩
  rw [Walk.support_map, List.mem_map] at hx
  obtain ⟨t, ht, htx⟩ := hx
  obtain rfl : t = x := Subtype.ext htx
  exact ht

/-- If every vertex of `S` is joined to `v ∈ S` by a walk inside `S`, then `Γ|_S` is a tree. -/
private theorem isTree_restrict (hT : Γ.IsTree) {S : Finset V} {v : V} (hv : v ∈ S)
    (hS : ∀ z ∈ S, ∃ p : Γ.underlyingGraph.Walk v z, ∀ t ∈ p.support, t ∈ S) :
    (Γ.restrict S).IsTree := by
  let f : (Γ.restrict S).underlyingGraph →g Γ.underlyingGraph :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h => (adj_restrict Γ S _ _).1 h }
  haveI : Nonempty S := ⟨⟨v, hv⟩⟩
  refine ⟨Connected.mk fun x y => ?_, hT.isAcyclic.comap f Subtype.val_injective⟩
  obtain ⟨p, hp⟩ := hS x x.2
  obtain ⟨q, hq⟩ := hS y y.2
  exact (reachable_restrict Γ p hp).symm.trans (reachable_restrict Γ q hq)

/-- A negative definite weighted graph has positive determinant. -/
private theorem det_pos_of_isNegDef {W : Type*} [Fintype W] [DecidableEq W]
    {Γ : WeightedGraph W} (hneg : Γ.IsNegDef) : 0 < Γ.det := by
  have h := hneg.delta_pos univ
  rw [← det_restrict, WeightedGraph.det, ← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv mem_univ).symm] at h
  convert h using 1
  rw [WeightedGraph.det]
  congr 1
  ext x y
  simp only [WeightedGraph.matrix, Matrix.neg_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.subtypeUnivEquiv_symm_apply, Subtype.ext_iff]
  rfl

private theorem d_nonpos (hΓ : Γ.IsRationalTree) (hβ : ∀ j, Γ.boundary j = 0) (j : V) :
    Γ.d j ≤ 0 := by
  have h' : (2 : ℚ) ≤ Γ.weight j := by exact_mod_cast hΓ.two_le_weight j
  simp only [WeightedGraph.d, hΓ.genus_eq_zero j, hβ j]
  push_cast
  linarith

/-- An induced subgraph `Γ|_S`, connected through `v ∈ S`, of a negative definite rational tree
with `β = 0` and nonnegative log discrepancies is again such a graph. -/
private theorem restrict_data (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (ha0 : ∀ k, 0 ≤ a k) (hT : Γ.IsTree) {S : Finset V} {v : V} (hv : v ∈ S)
    (hS : ∀ z ∈ S, ∃ p : Γ.underlyingGraph.Walk v z, ∀ t ∈ p.support, t ∈ S) :
    (Γ.restrict S).IsTree ∧ (Γ.restrict S).IsRationalTree ∧ (Γ.restrict S).IsNegDef ∧
      (∀ j, (Γ.restrict S).boundary j = 0) ∧
      ∃ a' : S → ℚ, (Γ.restrict S).IsLogDiscrepancyVector a' ∧ ∀ k, 0 ≤ a' k := by
  have hT' := isTree_restrict Γ hT hv hS
  have hneg' := (Γ.restrict_isSubgraph S).isNegDef hneg
  obtain ⟨a', ha', -⟩ := existsUnique_isLogDiscrepancyVector _ (det_pos_of_isNegDef hneg').ne'
  refine ⟨hT', ⟨fun j => hΓ.genus_eq_zero j, fun j => hΓ.two_le_weight j,
    fun j k => hΓ.edgeWeight_le_one j k, Or.inl hT'⟩, hneg', fun j => hβ j, a', ha',
    fun k => (ha0 k).trans (ha.le_of_isSubgraph ha' (Γ.restrict_isSubgraph S) hneg
      (d_nonpos Γ hΓ hβ) k)⟩

/-- If both ends of a path inside `S` have degree at least `2` in `Γ|_S`, then so has every
vertex of the path. -/
private theorem two_le_degree_restrict_of_mem_support {S : Finset V} {a b : V}
    (p : Γ.underlyingGraph.Walk a b) (hp : p.IsPath) (hpS : ∀ t ∈ p.support, t ∈ S)
    (ha : 2 ≤ (Γ.restrict S).underlyingGraph.degree ⟨a, hpS a p.start_mem_support⟩)
    (hb : 2 ≤ (Γ.restrict S).underlyingGraph.degree ⟨b, hpS b p.end_mem_support⟩)
    (x : V) (hx : x ∈ p.support) :
    2 ≤ (Γ.restrict S).underlyingGraph.degree ⟨x, hpS x hx⟩ := by
  by_cases hxa : x = a
  · subst hxa; exact ha
  by_cases hxb : x = b
  · subst hxb; exact hb
  obtain ⟨y, hy, z, hz, hyz, h1, h2⟩ := exists_adj_adj_of_mem_support _ p hp hx hxa hxb
  have := card_le_degree_restrict Γ (T := {y, z})
    (by simp [insert_subset_iff, hpS _ hy, hpS _ hz]) (hpS x hx) (by simp [h1, h2])
  rwa [card_pair hyz] at this

/-- A vertex with three distinct neighbours in `S` has degree at least `3` in `Γ|_S`. -/
private theorem three_le_degree_restrict {S : Finset V} {x y₁ y₂ y₃ : V} (hx : x ∈ S)
    (hy₁ : y₁ ∈ S) (hy₂ : y₂ ∈ S) (hy₃ : y₃ ∈ S) (h₁ : Γ.underlyingGraph.Adj x y₁)
    (h₂ : Γ.underlyingGraph.Adj x y₂) (h₃ : Γ.underlyingGraph.Adj x y₃) (h₁₂ : y₁ ≠ y₂)
    (h₁₃ : y₁ ≠ y₃) (h₂₃ : y₂ ≠ y₃) : 3 ≤ (Γ.restrict S).underlyingGraph.degree ⟨x, hx⟩ := by
  have := card_le_degree_restrict Γ (T := {y₁, y₂, y₃})
    (by simp [insert_subset_iff, hy₁, hy₂, hy₃]) hx (by simp [h₁, h₂, h₃])
  rwa [card_insert_of_notMem (by simp [h₁₂, h₁₃]), card_pair h₂₃] at this

end Restrict

/-! ### The graphs of the list -/

section Builders

/-- The multisets of arm determinants of a log canonical three-arm star: `{2, 2, m}` with
`m ≥ 2`, the platonic `{2, 3, 3}`, `{2, 3, 4}`, `{2, 3, 5}` and the euclidean `{2, 3, 6}`,
`{2, 4, 4}`, `{3, 3, 3}`. -/
private def IsLcTriple (M : Multiset ℤ) : Prop :=
  (∃ m : ℤ, 2 ≤ m ∧ M = {2, 2, m}) ∨ M = {2, 3, 3} ∨ M = {2, 3, 4} ∨ M = {2, 3, 5} ∨
    M = {2, 3, 6} ∨ M = {2, 4, 4} ∨ M = {3, 3, 3}

private theorem IsLcTriple.of_eq {M M' : Multiset ℤ} (h : IsLcTriple M) (e : M = M') :
    IsLcTriple M' := e ▸ h

private theorem isLcTriple_of_sorted {x y z : ℕ} (hx : 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : 1 ≤ (x : ℚ)⁻¹ + (y : ℚ)⁻¹ + (z : ℚ)⁻¹) : IsLcTriple {(x : ℤ), (y : ℤ), (z : ℤ)} := by
  rcases h.lt_or_eq with h | h
  · rcases (MMP.Flips.one_lt_inv_add_inv_add_inv_iff hx hxy hyz).1 h with h | h | h | h <;>
      simp only [Prod.mk.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨z, by omega, by push_cast; rfl⟩
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inl (by push_cast; rfl))
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl (by push_cast; rfl)))
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl (by push_cast; rfl))))
  · rcases (MMP.Flips.inv_add_inv_add_inv_eq_one_iff hx hxy hyz).1 h.symm with h | h | h <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by push_cast; rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by push_cast; rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by push_cast; rfl))))))

/-- Three integers `≥ 2` with `1/x + 1/y + 1/z ≥ 1` form one of the triples of
`IsLcTriple`. -/
private theorem isLcTriple {x y z : ℤ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (h : 1 ≤ 1 / (x : ℚ) + 1 / y + 1 / z) : IsLcTriple {x, y, z} := by
  lift x to ℕ using (by omega)
  lift y to ℕ using (by omega)
  lift z to ℕ using (by omega)
  simp only [one_div] at h
  push_cast at h
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  all_goals first
    | exact (isLcTriple_of_sorted (x := x) (y := y) (z := z) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])
    | exact (isLcTriple_of_sorted (x := x) (y := z) (z := y) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])
    | exact (isLcTriple_of_sorted (x := y) (y := x) (z := z) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])
    | exact (isLcTriple_of_sorted (x := y) (y := z) (z := x) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])
    | exact (isLcTriple_of_sorted (x := z) (y := x) (z := y) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])
    | exact (isLcTriple_of_sorted (x := z) (y := y) (z := x) (by omega) (by omega) (by omega)
        (by linarith)).of_eq
        (by simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_swap])

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-- A chain attached at an end, with all weights at least `2`, has `Δ ≥ 2`. -/
private theorem two_le_delta_of_isChainAttachedAtEnd (hw : ∀ j, 2 ≤ Γ.weight j) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) : 2 ≤ Γ.delta C := by
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  have := add_one_le_det_of_isChainOrder (Γ.restrict C) hs e he fun w => hw w
  unfold WeightedGraph.delta
  push_cast at this
  omega

/-- **The three-arm case.** The arm determinants of a log canonical three-arm star form one of
the triples of `IsLcTriple`. -/
private theorem isLcTriple_of_isStar_three (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 3 → Finset V} (hstar : Γ.IsStar v arms)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hv : 0 ≤ a v) :
    IsLcTriple {Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} := by
  have hd := fun i => two_le_delta_of_isChainAttachedAtEnd hΓ.two_le_weight
    (hstar.isChainAttachedAtEnd i)
  rw [ha.apply_eq_of_isStar_three hneg hΓ.genus_eq_zero hβ hstar] at hv
  have hpos : (0 : ℚ) < Γ.delta (arms 0) * Γ.delta (arms 1) * Γ.delta (arms 2) / Γ.det := by
    have h : ∀ i, (0 : ℚ) < Γ.delta (arms i) := fun i => by
      exact_mod_cast two_pos.trans_le (hd i)
    exact div_pos (mul_pos (mul_pos (h 0) (h 1)) (h 2))
      (by exact_mod_cast det_pos_of_isNegDef hneg)
  have := nonneg_of_mul_nonneg_right hv hpos
  exact isLcTriple (hd 0) (hd 1) (hd 2) (by linarith)

/-- A chain attached at `x` consisting of the single vertex `u`: `u` is a leaf at `x`. -/
private theorem adj_of_isChainAttachedAtEnd_singleton {x u : V}
    (h : Γ.IsChainAttachedAtEnd x {u}) :
    Γ.underlyingGraph.Adj x u ∧ ∀ t, Γ.underlyingGraph.Adj u t → t = x := by
  obtain ⟨-, hcomp, s, hs, e, -, hadj, -⟩ := h
  have he : (e ⟨0, hs⟩ : V) = u := mem_singleton.1 (e ⟨0, hs⟩).2
  refine ⟨he ▸ hadj, fun t ht => ?_⟩
  by_contra htx
  have htu : t ∉ ({u} : Finset V) := fun h => ht.ne (mem_singleton.1 h).symm
  have := Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex hcomp (mem_singleton_self u) htu htx
  exact ht.2.ne' this

/-- **The four-arm case.** A star with four arms which are single vertices of weight `2`. -/
private theorem four_arm_data (hs : Γ.HasSimpleEdges) {v : V} {arms : Fin 4 → Finset V}
    (hstar : Γ.IsStar v arms) (harms : ∀ i, ∃ u, arms i = {u} ∧ Γ.weight u = 2) :
    ∃ u : Fin 4 → V, Function.Injective u ∧ Set.range u = {v}ᶜ ∧
      (∀ k, Γ.weight (u k) = 2) ∧ (∀ k, Γ.IsSimpleEdge v (u k)) ∧
      ∀ k l, k ≠ l → Γ.edgeWeight (u k) (u l) = 0 := by
  choose u hu hw using harms
  have hmem : ∀ i, u i ∈ arms i := fun i => by rw [hu i]; exact mem_singleton_self _
  have hne : ∀ i, u i ≠ v := fun i h => by
    have : u i ∈ univ.biUnion arms := mem_biUnion.2 ⟨i, mem_univ _, hmem i⟩
    rw [hstar.biUnion_eq] at this
    simp [h] at this
  refine ⟨u, fun i j hij => ?_, ?_, hw, fun k => ?_, fun k l hkl => ?_⟩
  · by_contra hne
    exact Finset.disjoint_left.1 (hstar.pairwise_disjoint hne) (hmem i) (hij ▸ hmem j)
  · ext z
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact hne i
    · intro hz
      have : z ∈ univ.biUnion arms := by rw [hstar.biUnion_eq]; simp [hz]
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 this
      rw [hu i, mem_singleton] at hi
      exact ⟨i, hi.symm⟩
  · have h := hstar.isChainAttachedAtEnd k
    rw [hu k] at h
    exact hs _ _ (adj_of_isChainAttachedAtEnd_singleton h).1
  · exact Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex (hstar.isComponent k) (hmem k)
      (fun h => Finset.disjoint_left.1 (hstar.pairwise_disjoint hkl.symm) (hmem l) h) (hne l)

/-- **The two-fork case.** A tree with two vertices `v ≠ v'` of degree `3`, two leaves
`u 0, u 1` at `v`, two leaves `u 2, u 3` at `v'`, and all other degrees at most `2` is a chain
from `v` to `v'` with two leaves at each end. -/
private theorem two_fork_data (hT : Γ.IsTree) (hs : Γ.HasSimpleEdges) {v v' : V}
    (hvv' : v ≠ v') (u : Fin 4 → V) (hu01 : u 0 ≠ u 1) (hu23 : u 2 ≠ u 3)
    (hadj0 : ∀ k : Fin 4, (k : ℕ) < 2 → Γ.underlyingGraph.Adj v (u k))
    (hadj1 : ∀ k : Fin 4, 2 ≤ (k : ℕ) → Γ.underlyingGraph.Adj v' (u k))
    (hnb0 : ∀ k : Fin 4, (k : ℕ) < 2 → ∀ t, Γ.underlyingGraph.Adj (u k) t → t = v)
    (hnb1 : ∀ k : Fin 4, 2 ≤ (k : ℕ) → ∀ t, Γ.underlyingGraph.Adj (u k) t → t = v')
    (hdv : Γ.underlyingGraph.degree v = 3) (hdv' : Γ.underlyingGraph.degree v' = 3)
    (hdeg : ∀ z, z ≠ v → z ≠ v' → Γ.underlyingGraph.degree z ≤ 2) :
    ∃ (s : ℕ) (_ : 2 ≤ s) (w : Fin s → V),
      Function.Bijective (Sum.elim w u) ∧
      (∀ i j : Fin s,
        Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0) ∧
      (∀ (i : Fin s) (k : Fin 4), Γ.edgeWeight (w i) (u k) =
        if ((k : ℕ) < 2 ∧ (i : ℕ) = 0) ∨ (2 ≤ (k : ℕ) ∧ (i : ℕ) + 1 = s) then 1 else 0) ∧
      ∀ k l : Fin 4, Γ.edgeWeight (u k) (u l) = 0 := by
  have hnb : ∀ k t, Γ.underlyingGraph.Adj (u k) t → t = v ∨ t = v' := fun k t h => by
    by_cases hk : (k : ℕ) < 2
    · exact Or.inl (hnb0 k hk t h)
    · exact Or.inr (hnb1 k (by omega) t h)
  have hdu : ∀ k, Γ.underlyingGraph.degree (u k) ≤ 1 := fun k => by
    rw [← card_neighborFinset_eq_degree]
    by_cases hk : (k : ℕ) < 2
    · exact (card_le_card fun t ht => mem_singleton.2
        (hnb0 k hk t ((mem_neighborFinset _ _ _).1 ht))).trans (card_singleton v).le
    · exact (card_le_card fun t ht => mem_singleton.2
        (hnb1 k (by omega) t ((mem_neighborFinset _ _ _).1 ht))).trans (card_singleton v').le
  have huv : ∀ k, u k ≠ v := fun k h => by have := hdu k; rw [h, hdv] at this; omega
  have huv' : ∀ k, u k ≠ v' := fun k h => by have := hdu k; rw [h, hdv'] at this; omega
  have key : ∀ k l : Fin 4, (k : ℕ) < 2 → 2 ≤ (l : ℕ) → u k ≠ u l := fun k l hk hl h =>
    hvv' (hnb1 l hl v (h ▸ (hadj0 k hk).symm))
  have huinj : Function.Injective u := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp only [Fin.isValue] at h ⊢
    all_goals first
      | rfl
      | exact absurd h hu01 | exact absurd h.symm hu01
      | exact absurd h hu23 | exact absurd h.symm hu23
      | exact absurd h (key _ _ (by decide) (by decide))
      | exact absurd h.symm (key _ _ (by decide) (by decide))
  set W : Finset V := {z | ∀ k, u k ≠ z} with hWdef
  have hWmem : ∀ z, z ∈ W ↔ ∀ k, u k ≠ z := fun z => by simp [hWdef]
  have hvW : v ∈ W := (hWmem v).2 huv
  have hv'W : v' ∈ W := (hWmem v').2 huv'
  have hconn : ∀ z ∈ W, ∃ p : Γ.underlyingGraph.Walk v z, ∀ t ∈ p.support, t ∈ W := by
    intro z hz
    refine ⟨((hT.connected.preconnected v z).some.toPath : Γ.underlyingGraph.Walk v z),
      fun t ht => (hWmem t).2 fun k hk => ?_⟩
    subst hk
    obtain ⟨y, -, y', -, hyy', h1, h2⟩ := exists_adj_adj_of_mem_support _ _
      (hT.connected.preconnected v z).some.toPath.2 ht (huv k)
      (fun h => (hWmem z).1 hz k h)
    by_cases hk : (k : ℕ) < 2
    · exact hyy' ((hnb0 k hk y h1).trans (hnb0 k hk y' h2).symm)
    · exact hyy' ((hnb1 k (by omega) y h1).trans (hnb1 k (by omega) y' h2).symm)
  have hWv : ∀ x ∈ ({v, v'} : Finset V), ∀ k l : Fin 4,
      Γ.underlyingGraph.Adj x (u k) → Γ.underlyingGraph.Adj x (u l) → k ≠ l →
      #{t ∈ W | Γ.underlyingGraph.Adj x t} ≤ 1 := by
    intro x hx k l hk hl hkl
    have hsub : {t ∈ W | Γ.underlyingGraph.Adj x t} ⊆
        ((Γ.underlyingGraph.neighborFinset x).erase (u k)).erase (u l) := fun t ht => by
      obtain ⟨htW, hxt⟩ := mem_filter.1 ht
      exact mem_erase.2 ⟨fun h => (hWmem t).1 htW l h.symm, mem_erase.2
        ⟨fun h => (hWmem t).1 htW k h.symm, (mem_neighborFinset _ _ _).2 hxt⟩⟩
    refine (card_le_card hsub).trans ?_
    rw [card_erase_of_mem (mem_erase.2 ⟨fun h => hkl (huinj h).symm,
        (mem_neighborFinset _ _ _).2 hl⟩), card_erase_of_mem ((mem_neighborFinset _ _ _).2 hk),
      card_neighborFinset_eq_degree]
    rcases mem_insert.1 hx with rfl | hx
    · rw [hdv]
    · rw [mem_singleton.1 hx, hdv']
  have hcv : #{t ∈ W | Γ.underlyingGraph.Adj v t} ≤ 1 :=
    hWv v (by simp) 0 1 (hadj0 0 (by decide)) (hadj0 1 (by decide)) (by decide)
  have hcv' : #{t ∈ W | Γ.underlyingGraph.Adj v' t} ≤ 1 :=
    hWv v' (by simp) 2 3 (hadj1 2 (by decide)) (hadj1 3 (by decide)) (by decide)
  obtain ⟨s, e, hinj, hmem, he0, hadj⟩ := exists_chain_enum Γ.underlyingGraph _ W v rfl hvW
    hconn (fun z hz => by
      by_cases h1 : z = v
      · rw [h1]
        exact hcv.trans (by norm_num)
      by_cases h2 : z = v'
      · rw [h2]
        exact hcv'.trans (by norm_num)
      exact (card_filter_adj_le_degree (Γ := Γ) _ z).trans (hdeg z h1 h2)) hcv
  obtain ⟨i', hi'⟩ := (hmem v').1 hv'W
  have hi'0 : i' ≠ 0 := fun h => hvv' (by rw [← he0, ← h, hi'])
  have hi'l := eq_last_of_card_le_one hinj hmem hadj hi'0 (by rw [hi']; exact hcv')
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hi'0 (hi'l.trans (Fin.last_zero))
  have heW : ∀ i, e i ∈ W := fun i => (hmem _).2 ⟨i, rfl⟩
  have hev : ∀ i, e i = v → i = 0 := fun i h => hinj (h.trans he0.symm)
  have hev' : ∀ i, e i = v' → (i : ℕ) = s := fun i h => by
    have := hinj (h.trans (hi'.symm.trans (congrArg e hi'l)))
    rw [this, Fin.val_last]
  refine ⟨s + 1, by omega, e, ⟨hinj.sumElim huinj fun i k h => (hWmem _).1 (heW i) k h.symm,
    fun z => ?_⟩, fun i j => ?_, fun i k => ?_, fun k l => ?_⟩
  · by_cases hz : ∀ k, u k ≠ z
    · obtain ⟨i, hi⟩ := (hmem z).1 ((hWmem z).2 hz)
      exact ⟨Sum.inl i, hi⟩
    · push Not at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨Sum.inr k, hk⟩
  · rw [edgeWeight_eq_ite Γ hs]
    exact if_congr (hadj i j) rfl rfl
  · rw [edgeWeight_eq_ite Γ hs]
    refine if_congr ⟨fun h => ?_, ?_⟩ rfl rfl
    · by_cases hk : (k : ℕ) < 2
      · exact Or.inl ⟨hk, by rw [hev i (hnb0 k hk _ h.symm)]; rfl⟩
      · exact Or.inr ⟨by omega, by rw [hev' i (hnb1 k (by omega) _ h.symm)]⟩
    · rintro (⟨hk, hi⟩ | ⟨hk, hi⟩)
      · obtain rfl : i = 0 := Fin.ext hi
        rw [he0]
        exact hadj0 k hk
      · have : i = Fin.last s := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [this, ← hi'l, hi']
        exact hadj1 k hk
  · rw [edgeWeight_eq_ite Γ hs, if_neg]
    intro h
    rcases hnb k _ h with h' | h'
    · exact huv l h'
    · exact huv' l h'

end Builders

/-! ### The excluded configurations -/

section Excluded

private theorem eq_zero_of_sum_le_sum {W : Type*} [Fintype W] [DecidableEq W] (f : W → ℕ)
    (T : Finset W) (h : ∑ x, f x ≤ ∑ x ∈ T, f x) {x : W} (hx : x ∉ T) : f x = 0 := by
  have h1 := sum_sdiff (subset_univ T) (f := f)
  have h2 := single_le_sum (fun y _ => Nat.zero_le (f y)) (mem_sdiff.2 ⟨mem_univ x, hx⟩)
    (f := f)
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-- A path from `v` to a vertex `z ≠ v` of degree at least `3`, with its second vertex `n`, its
next-to-last vertex `pr`, and two further neighbours `y₁, y₂` of `z`. -/
private theorem exists_path_fork (hT : Γ.IsTree) {v z : V} (hvz : z ≠ v)
    (hz : 3 ≤ Γ.underlyingGraph.degree z) :
    ∃ (p : Γ.underlyingGraph.Walk v z) (n pr y₁ y₂ : V), p.IsPath ∧
      Γ.underlyingGraph.Adj v n ∧ n ∈ p.support ∧ ReachAvoid Γ.underlyingGraph v n z ∧
      pr ∈ p.support ∧ Γ.underlyingGraph.Adj pr z ∧ Γ.underlyingGraph.Adj z y₁ ∧
      Γ.underlyingGraph.Adj z y₂ ∧ y₁ ≠ y₂ ∧ y₁ ≠ pr ∧ y₂ ≠ pr := by
  obtain ⟨p, hp⟩ := (hT.connected.preconnected v z).some.toPath
  have hlen : 0 < p.length := by
    by_contra h
    exact hvz (Walk.eq_of_length_eq_zero (by omega : p.length = 0)).symm
  have hpr := p.adj_getVert_succ (i := p.length - 1) (by omega)
  rw [Nat.sub_add_cancel hlen, Walk.getVert_length] at hpr
  have hcard : 1 < #((Γ.underlyingGraph.neighborFinset z).erase (p.getVert (p.length - 1))) := by
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hpr.symm), card_neighborFinset_eq_degree]
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁₂⟩ := one_lt_card.1 hcard
  obtain ⟨hy₁p, hzy₁⟩ := mem_erase.1 hy₁
  obtain ⟨hy₂p, hzy₂⟩ := mem_erase.1 hy₂
  rw [mem_neighborFinset] at hzy₁ hzy₂
  cases p with
  | nil => exact absurd rfl hvz
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hp
    exact ⟨.cons h q, _, _, y₁, y₂, (Walk.cons_isPath_iff _ _).2 hp, h, by simp, ⟨q, hp.2⟩,
      Walk.getVert_mem_support _ _, hpr, hzy₁, hzy₂, hy₁₂, hy₁p, hy₂p⟩

/-- A vertex on a walk from `v` inside `S` is reached from `v` inside `S`. -/
private theorem exists_walk_of_mem_support {S : Finset V} {v z : V}
    (p : Γ.underlyingGraph.Walk v z) (hpS : ∀ t ∈ p.support, t ∈ S) {x : V}
    (hx : x ∈ p.support) : ∃ q : Γ.underlyingGraph.Walk v x, ∀ t ∈ q.support, t ∈ S :=
  ⟨p.takeUntil x hx, fun t ht => hpS t (p.support_takeUntil_subset hx ht)⟩

/-- The end of a walk from `v` inside `S`, followed by an edge into `S`. -/
private theorem exists_walk_of_adj_end {S : Finset V} {v z y : V}
    (p : Γ.underlyingGraph.Walk v z) (hpS : ∀ t ∈ p.support, t ∈ S)
    (h : Γ.underlyingGraph.Adj z y) (hy : y ∈ S) :
    ∃ q : Γ.underlyingGraph.Walk v y, ∀ t ∈ q.support, t ∈ S := by
  refine ⟨p.concat h, fun t ht => ?_⟩
  simp only [Walk.support_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact hpS t ht
  · exact hy

private theorem exists_walk_refl {S : Finset V} {v : V} (hv : v ∈ S) :
    ∃ q : Γ.underlyingGraph.Walk v v, ∀ t ∈ q.support, t ∈ S :=
  ⟨.nil, by simpa using hv⟩

private theorem exists_walk_of_adj {S : Finset V} {v y : V} (hv : v ∈ S)
    (h : Γ.underlyingGraph.Adj v y) (hy : y ∈ S) :
    ∃ q : Γ.underlyingGraph.Walk v y, ∀ t ∈ q.support, t ∈ S :=
  exists_walk_of_adj_end (S := S) .nil (by simpa using hv) h hy

private theorem one_le_degree_restrict {S : Finset V} {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (h : Γ.underlyingGraph.Adj x y) : 1 ≤ (Γ.restrict S).underlyingGraph.degree ⟨x, hx⟩ := by
  have := card_le_degree_restrict Γ (T := {y}) (by simpa using hy) hx (by simpa using h)
  rwa [card_singleton] at this

variable (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef) (hβ : ∀ j, Γ.boundary j = 0)
  {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ k, 0 ≤ a k) (hT : Γ.IsTree)

include hΓ hneg hβ ha ha0 hT

/-- **No vertex of degree `≥ 5`** (FA 3.2.7): `v` and its neighbours span a star with at least
five arms, whose log discrepancy at `v` is negative. -/
private theorem degree_le_four (v : V) : Γ.underlyingGraph.degree v ≤ 4 := by
  by_contra h5
  push Not at h5
  set S := insert v (Γ.underlyingGraph.neighborFinset v) with hSdef
  have hvS : v ∈ S := mem_insert_self _ _
  have hS : ∀ z ∈ S, ∃ p : Γ.underlyingGraph.Walk v z, ∀ t ∈ p.support, t ∈ S := by
    intro z hz
    rcases mem_insert.1 hz with rfl | hz'
    · exact exists_walk_refl hvS
    · exact exists_walk_of_adj hvS ((mem_neighborFinset _ _ _).1 hz') hz
  obtain ⟨hT', hΓ', hneg', hβ', a', ha', ha'0⟩ := restrict_data Γ hΓ hneg hβ ha ha0 hT hvS hS
  have hs' := hasSimpleEdges_of_isRationalTree _ hΓ'
  set v₀ : S := ⟨v, hvS⟩
  have hdv₀ : Γ.underlyingGraph.degree v ≤ (Γ.restrict S).underlyingGraph.degree v₀ := by
    rw [← card_neighborFinset_eq_degree]
    exact card_le_degree_restrict Γ (subset_insert _ _) hvS fun y hy =>
      (mem_neighborFinset _ _ _).1 hy
  have hL := sum_degree_sub_two_add_two_le (G := (Γ.restrict S).underlyingGraph) hT'
    (univ.erase v₀) (fun x hx => by
      have hxv : (x : V) ≠ v := fun h => (mem_erase.1 hx).1 (Subtype.ext h)
      have hx' : (x : V) ∈ Γ.underlyingGraph.neighborFinset v :=
        (mem_insert.1 x.2).resolve_left hxv
      exact one_le_degree_restrict x.2 hvS ((mem_neighborFinset _ _ _).1 hx').symm)
    (fun x hx => by
      rw [show x = v₀ from not_not.1 fun h => hx (mem_erase.2 ⟨h, mem_univ _⟩)]
      omega)
  have hcardL : #(univ.erase v₀) = Γ.underlyingGraph.degree v := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_coe, hSdef,
      card_insert_of_notMem (fun h => (mem_neighborFinset _ _ _).1 h |>.ne rfl),
      card_neighborFinset_eq_degree]
    rfl
  have hle : ∀ x, x ≠ v₀ → (Γ.restrict S).underlyingGraph.degree x ≤ 2 := fun x hx => by
    have := eq_zero_of_sum_le_sum (fun x => (Γ.restrict S).underlyingGraph.degree x - 2) {v₀}
      (by rw [sum_singleton]; omega) (x := x) (by simpa using hx)
    omega
  obtain ⟨arms, hstar⟩ := exists_isStar hT' hs' hΓ'.genus_eq_zero hle
  have := ha'.apply_neg_of_isStar_of_five_le hΓ' hneg' hβ'
    (by rw [degree_eq_underlyingGraph_degree]; omega) hstar
  exact absurd (ha'0 v₀) (not_le.2 this)

/-- **A vertex of degree `4` is the only fork** (FA 3.2.7): otherwise `v`, its neighbours, a
path to another fork `v'` and two further neighbours of `v'` span a graph of Fig. 2(b) shape at
`v`, whose log discrepancy at `v` is negative. -/
private theorem degree_le_two_of_degree_eq_four {v v' : V} (hvv' : v' ≠ v)
    (hdv : Γ.underlyingGraph.degree v = 4) : Γ.underlyingGraph.degree v' ≤ 2 := by
  by_contra h3
  push Not at h3
  obtain ⟨p, n, pr, y₁, y₂, hp, hvn, hnp, -, hprp, hprv', hy₁, hy₂, hy₁₂, hy₁p, hy₂p⟩ :=
    exists_path_fork hT hvv' (by omega)
  set S := insert v (Γ.underlyingGraph.neighborFinset v) ∪ p.support.toFinset ∪ {y₁, y₂}
    with hSdef
  have hmemS : ∀ z, z ∈ S ↔ ((z = v ∨ z ∈ Γ.underlyingGraph.neighborFinset v) ∨
      z ∈ p.support) ∨ z = y₁ ∨ z = y₂ := fun z => by
    simp only [hSdef, mem_union, mem_insert, mem_singleton, List.mem_toFinset]
  have hvS : v ∈ S := (hmemS v).2 (Or.inl (Or.inl (Or.inl rfl)))
  have hnfS : Γ.underlyingGraph.neighborFinset v ⊆ S := fun z hz =>
    (hmemS z).2 (Or.inl (Or.inl (Or.inr hz)))
  have hpS : ∀ t ∈ p.support, t ∈ S := fun t ht => (hmemS t).2 (Or.inl (Or.inr ht))
  have hy₁S : y₁ ∈ S := (hmemS y₁).2 (Or.inr (Or.inl rfl))
  have hy₂S : y₂ ∈ S := (hmemS y₂).2 (Or.inr (Or.inr rfl))
  have hv'S : v' ∈ S := hpS _ p.end_mem_support
  have hS : ∀ z ∈ S, ∃ q : Γ.underlyingGraph.Walk v z, ∀ t ∈ q.support, t ∈ S := by
    intro z hz
    rcases (hmemS z).1 hz with ((rfl | hz') | hz') | rfl | rfl
    · exact exists_walk_refl hvS
    · exact exists_walk_of_adj hvS ((mem_neighborFinset _ _ _).1 hz') hz
    · exact exists_walk_of_mem_support p hpS hz'
    · exact exists_walk_of_adj_end p hpS hy₁ hz
    · exact exists_walk_of_adj_end p hpS hy₂ hz
  obtain ⟨hT', hΓ', hneg', hβ', a', ha', ha'0⟩ := restrict_data Γ hΓ hneg hβ ha ha0 hT hvS hS
  have hs' := hasSimpleEdges_of_isRationalTree _ hΓ'
  set v₀ : S := ⟨v, hvS⟩
  set v₀' : S := ⟨v', hv'S⟩
  have hne : v₀ ≠ v₀' := fun h => hvv' (congrArg Subtype.val h).symm
  have hd4 : 4 ≤ (Γ.restrict S).underlyingGraph.degree v₀ := by
    have := card_le_degree_restrict Γ hnfS hvS fun y hy => (mem_neighborFinset _ _ _).1 hy
    rwa [card_neighborFinset_eq_degree, hdv] at this
  have hd3 : 3 ≤ (Γ.restrict S).underlyingGraph.degree v₀' :=
    three_le_degree_restrict Γ hv'S (hpS _ hprp) hy₁S hy₂S hprv'.symm hy₁ hy₂ hy₁p.symm
      hy₂p.symm hy₁₂
  have hsupp := two_le_degree_restrict_of_mem_support Γ p hp hpS (le_trans (by norm_num) hd4)
    (le_trans (by norm_num) hd3)
  set L0 := (Γ.underlyingGraph.neighborFinset v).erase n ∪ {y₁, y₂} with hL0def
  have hL0 : #L0 ≤ 5 := by
    refine (card_union_le _ _).trans ?_
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).2 hvn), card_neighborFinset_eq_degree,
      hdv]
    have := card_insert_le y₁ {y₂}
    rw [card_singleton] at this
    omega
  set L : Finset S := {x | (x : V) ∈ L0} with hLdef
  have hLcard : #L ≤ #L0 :=
    card_le_card_of_injOn Subtype.val (fun x hx => (mem_filter.1 hx).2)
      Subtype.val_injective.injOn
  have hL := sum_degree_sub_two_add_two_le (G := (Γ.restrict S).underlyingGraph) hT' L
    (fun x hx => by
      have hx' : (x : V) ∈ L0 := (mem_filter.1 hx).2
      rcases mem_union.1 hx' with h | h
      · exact one_le_degree_restrict x.2 hvS
          ((mem_neighborFinset _ _ _).1 (mem_erase.1 h).2).symm
      · simp only [mem_insert, mem_singleton] at h
        rcases h with h | h
        · exact one_le_degree_restrict x.2 hv'S (by rw [h]; exact hy₁.symm)
        · exact one_le_degree_restrict x.2 hv'S (by rw [h]; exact hy₂.symm))
    (fun x hx => by
      have hx' : (x : V) ∉ L0 := fun h => hx (mem_filter.2 ⟨mem_univ _, h⟩)
      rcases (hmemS x).1 x.2 with ((h | h) | h) | h | h
      · rw [show x = v₀ from Subtype.ext h]
        omega
      · have hxn : (x : V) = n := by
          by_contra hxn
          exact hx' (mem_union_left _ (mem_erase.2 ⟨hxn, h⟩))
        exact hsupp x (hxn ▸ hnp)
      · exact hsupp x h
      · exact absurd (mem_union_right _ (by simp [h])) hx'
      · exact absurd (mem_union_right _ (by simp [h])) hx')
  have hT2 := sum_pair (f := fun x => (Γ.restrict S).underlyingGraph.degree x - 2) hne
  have hsub := sum_le_sum_of_subset (f := fun x => (Γ.restrict S).underlyingGraph.degree x - 2)
    (subset_univ ({v₀, v₀'} : Finset S))
  have hle : ∀ x, x ≠ v₀ → x ≠ v₀' → (Γ.restrict S).underlyingGraph.degree x ≤ 2 :=
    fun x h1 h2 => by
      have := eq_zero_of_sum_le_sum (fun x => (Γ.restrict S).underlyingGraph.degree x - 2)
        {v₀, v₀'} (by omega) (x := x) (by simp [h1, h2])
      omega
  have hfig := isFig2RightShape_of_degree hT' hs' hΓ'.genus_eq_zero hne.symm (by omega)
    (by omega) hle
  exact absurd (ha'0 v₀) (not_le.2 (ha'.apply_neg_of_isFig2RightShape hΓ' hneg' hβ' hfig))

/-- **At most two forks** (FA 3.2.7): with three forks, all of degree `3` by the previous
steps, FA 3.2.4's combinatorics give a fork `v` with forks `x₂, x₃` in different components of
`Γ - v`; then `v`, its neighbours, paths to `x₂, x₃` and two further neighbours of each span a
graph of Fig. 2(a) shape at `v`, whose log discrepancy at `v` is negative. -/
private theorem card_forks_le_two
    (h42 : ∀ v v', v' ≠ v → Γ.underlyingGraph.degree v = 4 →
      Γ.underlyingGraph.degree v' ≤ 2) :
    #{v | 3 ≤ Γ.underlyingGraph.degree v} ≤ 2 := by
  by_contra hF
  push Not at hF
  have h3 : ∀ v, Γ.underlyingGraph.degree v ≤ 3 := fun v => by
    by_contra h
    have hv4 : Γ.underlyingGraph.degree v = 4 := by
      have := degree_le_four hΓ hneg hβ ha ha0 hT v
      omega
    obtain ⟨v', hv'F, hv'v⟩ :=
      exists_mem_ne (s := ({v | 3 ≤ Γ.underlyingGraph.degree v} : Finset V)) (by omega) v
    have := (mem_filter.1 hv'F).2
    have := h42 v v' hv'v hv4
    omega
  obtain ⟨v, hv3, x₂, x₃, h2v, h3v, hd2, hd3, hnr⟩ :=
    MMP.Foundations.exists_branch_vertex_separating_branch_vertices_of_isTree hT hF
  have hnra : ¬ ReachAvoid Γ.underlyingGraph v x₂ x₃ := fun h =>
    hnr (reachable_induce_of_reachAvoid h)
  have hx23 : x₂ ≠ x₃ := fun h => hnra (h ▸ ReachAvoid.refl h2v)
  have hdv : Γ.underlyingGraph.degree v = 3 := le_antisymm (h3 v) hv3
  have hdx₂ : Γ.underlyingGraph.degree x₂ = 3 := le_antisymm (h3 x₂) hd2
  have hdx₃ : Γ.underlyingGraph.degree x₃ = 3 := le_antisymm (h3 x₃) hd3
  obtain ⟨p₂, n₂, pr₂, y₂₁, y₂₂, hp₂, hvn₂, hn₂p, hn₂r, hpr₂p, hpr₂, hy₂₁, hy₂₂, hy₂, hy₂₁p,
    hy₂₂p⟩ := exists_path_fork hT h2v (by omega)
  obtain ⟨p₃, n₃, pr₃, y₃₁, y₃₂, hp₃, hvn₃, hn₃p, hn₃r, hpr₃p, hpr₃, hy₃₁, hy₃₂, hy₃, hy₃₁p,
    hy₃₂p⟩ := exists_path_fork hT h3v (by omega)
  have hn23 : n₂ ≠ n₃ := fun h => hnra (hn₂r.symm.trans (h ▸ hn₃r))
  set S := insert v (Γ.underlyingGraph.neighborFinset v) ∪ p₂.support.toFinset ∪
    p₃.support.toFinset ∪ {y₂₁, y₂₂} ∪ {y₃₁, y₃₂} with hSdef
  have hmemS : ∀ z, z ∈ S ↔ ((((z = v ∨ z ∈ Γ.underlyingGraph.neighborFinset v) ∨
      z ∈ p₂.support) ∨ z ∈ p₃.support) ∨ z = y₂₁ ∨ z = y₂₂) ∨ z = y₃₁ ∨ z = y₃₂ := fun z => by
    simp only [hSdef, mem_union, mem_insert, mem_singleton, List.mem_toFinset]
  have hvS : v ∈ S := (hmemS v).2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))
  have hnfS : Γ.underlyingGraph.neighborFinset v ⊆ S := fun z hz =>
    (hmemS z).2 (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz)))))
  have hp₂S : ∀ t ∈ p₂.support, t ∈ S := fun t ht =>
    (hmemS t).2 (Or.inl (Or.inl (Or.inl (Or.inr ht))))
  have hp₃S : ∀ t ∈ p₃.support, t ∈ S := fun t ht =>
    (hmemS t).2 (Or.inl (Or.inl (Or.inr ht)))
  have hy₂₁S : y₂₁ ∈ S := (hmemS _).2 (Or.inl (Or.inr (Or.inl rfl)))
  have hy₂₂S : y₂₂ ∈ S := (hmemS _).2 (Or.inl (Or.inr (Or.inr rfl)))
  have hy₃₁S : y₃₁ ∈ S := (hmemS _).2 (Or.inr (Or.inl rfl))
  have hy₃₂S : y₃₂ ∈ S := (hmemS _).2 (Or.inr (Or.inr rfl))
  have hx₂S : x₂ ∈ S := hp₂S _ p₂.end_mem_support
  have hx₃S : x₃ ∈ S := hp₃S _ p₃.end_mem_support
  have hS : ∀ z ∈ S, ∃ q : Γ.underlyingGraph.Walk v z, ∀ t ∈ q.support, t ∈ S := by
    intro z hz
    rcases (hmemS z).1 hz with ((((rfl | hz') | hz') | hz') | rfl | rfl) | rfl | rfl
    · exact exists_walk_refl hvS
    · exact exists_walk_of_adj hvS ((mem_neighborFinset _ _ _).1 hz') hz
    · exact exists_walk_of_mem_support p₂ hp₂S hz'
    · exact exists_walk_of_mem_support p₃ hp₃S hz'
    · exact exists_walk_of_adj_end p₂ hp₂S hy₂₁ hz
    · exact exists_walk_of_adj_end p₂ hp₂S hy₂₂ hz
    · exact exists_walk_of_adj_end p₃ hp₃S hy₃₁ hz
    · exact exists_walk_of_adj_end p₃ hp₃S hy₃₂ hz
  obtain ⟨hT', hΓ', hneg', hβ', a', ha', ha'0⟩ := restrict_data Γ hΓ hneg hβ ha ha0 hT hvS hS
  have hs' := hasSimpleEdges_of_isRationalTree _ hΓ'
  set v₀ : S := ⟨v, hvS⟩
  set x₂₀ : S := ⟨x₂, hx₂S⟩
  set x₃₀ : S := ⟨x₃, hx₃S⟩
  have hne₂ : x₂₀ ≠ v₀ := fun h => h2v (congrArg Subtype.val h)
  have hne₃ : x₃₀ ≠ v₀ := fun h => h3v (congrArg Subtype.val h)
  have hne₂₃ : x₂₀ ≠ x₃₀ := fun h => hx23 (congrArg Subtype.val h)
  have hdv₀ : 3 ≤ (Γ.restrict S).underlyingGraph.degree v₀ := by
    have := card_le_degree_restrict Γ hnfS hvS fun y hy => (mem_neighborFinset _ _ _).1 hy
    rwa [card_neighborFinset_eq_degree, hdv] at this
  have hdx₂₀ : 3 ≤ (Γ.restrict S).underlyingGraph.degree x₂₀ :=
    three_le_degree_restrict Γ hx₂S (hp₂S _ hpr₂p) hy₂₁S hy₂₂S hpr₂.symm hy₂₁ hy₂₂ hy₂₁p.symm
      hy₂₂p.symm hy₂
  have hdx₃₀ : 3 ≤ (Γ.restrict S).underlyingGraph.degree x₃₀ :=
    three_le_degree_restrict Γ hx₃S (hp₃S _ hpr₃p) hy₃₁S hy₃₂S hpr₃.symm hy₃₁ hy₃₂ hy₃₁p.symm
      hy₃₂p.symm hy₃
  have hsupp₂ := two_le_degree_restrict_of_mem_support Γ p₂ hp₂ hp₂S
    (le_trans (by norm_num) hdv₀) (le_trans (by norm_num) hdx₂₀)
  have hsupp₃ := two_le_degree_restrict_of_mem_support Γ p₃ hp₃ hp₃S
    (le_trans (by norm_num) hdv₀) (le_trans (by norm_num) hdx₃₀)
  set L0 := ((Γ.underlyingGraph.neighborFinset v).erase n₂).erase n₃ ∪ {y₂₁, y₂₂} ∪
    {y₃₁, y₃₂} with hL0def
  have hL0 : #L0 ≤ 5 := by
    refine (card_union_le _ _).trans ?_
    have h1 := card_union_le (((Γ.underlyingGraph.neighborFinset v).erase n₂).erase n₃)
      {y₂₁, y₂₂}
    rw [card_erase_of_mem (mem_erase.2 ⟨hn23.symm, (mem_neighborFinset _ _ _).2 hvn₃⟩),
      card_erase_of_mem ((mem_neighborFinset _ _ _).2 hvn₂), card_neighborFinset_eq_degree,
      hdv] at h1
    have h2 := card_insert_le y₂₁ {y₂₂}
    have h3 := card_insert_le y₃₁ {y₃₂}
    rw [card_singleton] at h2 h3
    omega
  set L : Finset S := {x | (x : V) ∈ L0} with hLdef
  have hLcard : #L ≤ #L0 :=
    card_le_card_of_injOn Subtype.val (fun x hx => (mem_filter.1 hx).2)
      Subtype.val_injective.injOn
  have hL := sum_degree_sub_two_add_two_le (G := (Γ.restrict S).underlyingGraph) hT' L
    (fun x hx => by
      have hx' : (x : V) ∈ L0 := (mem_filter.1 hx).2
      simp only [hL0def, mem_union, mem_erase, mem_insert, mem_singleton] at hx'
      rcases hx' with (⟨-, -, h⟩ | h | h) | h | h
      · exact one_le_degree_restrict x.2 hvS ((mem_neighborFinset _ _ _).1 h).symm
      · exact one_le_degree_restrict x.2 hx₂S (by rw [h]; exact hy₂₁.symm)
      · exact one_le_degree_restrict x.2 hx₂S (by rw [h]; exact hy₂₂.symm)
      · exact one_le_degree_restrict x.2 hx₃S (by rw [h]; exact hy₃₁.symm)
      · exact one_le_degree_restrict x.2 hx₃S (by rw [h]; exact hy₃₂.symm))
    (fun x hx => by
      have hx' : (x : V) ∉ L0 := fun h => hx (mem_filter.2 ⟨mem_univ _, h⟩)
      simp only [hL0def, mem_union, mem_erase, mem_insert, mem_singleton, not_or,
        not_and] at hx'
      obtain ⟨⟨hxnf, hy21, hy22⟩, hy31, hy32⟩ := hx'
      rcases (hmemS x).1 x.2 with ((((h | h) | h) | h) | h | h) | h | h
      · rw [show x = v₀ from Subtype.ext h]
        omega
      · by_cases hx2 : (x : V) = n₂
        · exact hsupp₂ x (hx2 ▸ hn₂p)
        by_cases hx3 : (x : V) = n₃
        · exact hsupp₃ x (hx3 ▸ hn₃p)
        exact absurd h (hxnf hx3 hx2)
      · exact hsupp₂ x h
      · exact hsupp₃ x h
      · exact absurd h hy21
      · exact absurd h hy22
      · exact absurd h hy31
      · exact absurd h hy32)
  have hT3 : ∑ x ∈ ({v₀, x₂₀, x₃₀} : Finset S),
      ((Γ.restrict S).underlyingGraph.degree x - 2) =
      ((Γ.restrict S).underlyingGraph.degree v₀ - 2) +
        (((Γ.restrict S).underlyingGraph.degree x₂₀ - 2) +
          ((Γ.restrict S).underlyingGraph.degree x₃₀ - 2)) := by
    rw [sum_insert (by simp [hne₂.symm, hne₃.symm]), sum_pair hne₂₃]
  have hsub := sum_le_sum_of_subset (f := fun x => (Γ.restrict S).underlyingGraph.degree x - 2)
    (subset_univ ({v₀, x₂₀, x₃₀} : Finset S))
  have hle : ∀ x, x ≠ v₀ → x ≠ x₂₀ → x ≠ x₃₀ →
      (Γ.restrict S).underlyingGraph.degree x ≤ 2 := fun x h1 h2 h3 => by
    have := eq_zero_of_sum_le_sum (fun x => (Γ.restrict S).underlyingGraph.degree x - 2)
      {v₀, x₂₀, x₃₀} (by omega) (x := x) (by simp [h1, h2, h3])
    omega
  have hfig := isFig2LeftShape_of_degree hT' hs' hΓ'.genus_eq_zero hne₂ hne₃
    (fun h => hnra (reachAvoid_of_restrict Γ h)) (by omega) (by omega) (by omega) hle
  exact absurd (ha'0 v₀) (not_le.2 (ha'.apply_neg_of_isFig2LeftShape hΓ' hneg' hβ' hfig))

/-- A tree with exactly two forks `v ≠ v'` and a nonnegative log discrepancy vector is a chain
with two leaves of weight `2` attached at each end. -/
private theorem exists_twoForkChain_of_forks {v v' : V} (hvv' : v ≠ v')
    (hF : ∀ z, 3 ≤ Γ.underlyingGraph.degree z ↔ z = v ∨ z = v') :
    ∃ (s : ℕ) (_ : 2 ≤ s) (w : Fin s → V) (u : Fin 4 → V),
      Function.Bijective (Sum.elim w u) ∧ (∀ k, Γ.weight (u k) = 2) ∧
      (∀ i j : Fin s,
        Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0) ∧
      (∀ (i : Fin s) (k : Fin 4), Γ.edgeWeight (w i) (u k) =
        if ((k : ℕ) < 2 ∧ (i : ℕ) = 0) ∨ (2 ≤ (k : ℕ) ∧ (i : ℕ) + 1 = s) then 1 else 0) ∧
      ∀ k l : Fin 4, Γ.edgeWeight (u k) (u l) = 0 := by
  have hs := hasSimpleEdges_of_isRationalTree Γ hΓ
  have hp := hΓ.genus_eq_zero
  have hv3 := (hF v).2 (Or.inl rfl)
  have hv'3 := (hF v').2 (Or.inr rfl)
  have hdv : Γ.underlyingGraph.degree v = 3 := by
    by_contra h
    have := degree_le_two_of_degree_eq_four hΓ hneg hβ ha ha0 hT (Ne.symm hvv')
      (by have := degree_le_four hΓ hneg hβ ha ha0 hT v; omega)
    omega
  have hdv' : Γ.underlyingGraph.degree v' = 3 := by
    by_contra h
    have := degree_le_two_of_degree_eq_four hΓ hneg hβ ha ha0 hT hvv'
      (by have := degree_le_four hΓ hneg hβ ha ha0 hT v'; omega)
    omega
  have hdeg : ∀ z, z ≠ v → z ≠ v' → Γ.underlyingGraph.degree z ≤ 2 := fun z h1 h2 => by
    by_contra h
    exact ((hF z).1 (by omega)).elim h1 h2
  obtain ⟨C₁, C₂, C₃, A, B, htwo⟩ :=
    exists_isTwoForkGraphWith_of_degree hT hs hp (Ne.symm hvv') hdv hdv' hdeg
  obtain ⟨⟨u₀, h₀, w₀⟩, ⟨u₁, h₁, w₁⟩, ⟨u₂, h₂, w₂⟩, ⟨u₃, h₃, w₃⟩⟩ :=
    ha.eq_singleton_of_isTwoForkGraphWith hneg hp hβ hΓ.two_le_weight htwo (ha0 v)
  have c₁ := htwo.isChainAttachedAtEnd₁
  have c₂ := htwo.isChainAttachedAtEnd₂
  rw [h₀] at c₁
  rw [h₁] at c₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hAB, hA, hB⟩ :=
    htwo.isForkedBranch₃.exists_spine
  rw [h₂] at hA
  rw [h₃] at hB
  rw [h₂, h₃] at hAB
  have l₀ := adj_of_isChainAttachedAtEnd_singleton c₁
  have l₁ := adj_of_isChainAttachedAtEnd_singleton c₂
  have l₂ := adj_of_isChainAttachedAtEnd_singleton hA
  have l₃ := adj_of_isChainAttachedAtEnd_singleton hB
  have hu₀₁ : u₀ ≠ u₁ := fun h => Finset.disjoint_left.1 htwo.disjoint₁₂
    (by rw [h₀]; exact mem_singleton_self _) (by rw [h₁, h]; exact mem_singleton_self _)
  have hu₂₃ : u₂ ≠ u₃ := fun h => Finset.disjoint_left.1 hAB (mem_singleton_self _)
    (by rw [h]; exact mem_singleton_self _)
  obtain ⟨s, hs2, w, hbij, hww, hwu, huu⟩ := two_fork_data hT hs hvv' ![u₀, u₁, u₂, u₃]
    hu₀₁ hu₂₃
    (fun k hk => by
      fin_cases k
      · exact l₀.1
      · exact l₁.1
      all_goals simp at hk)
    (fun k hk => by
      fin_cases k
      any_goals simp at hk
      · exact l₂.1
      · exact l₃.1)
    (fun k hk => by
      fin_cases k
      · exact l₀.2
      · exact l₁.2
      all_goals simp at hk)
    (fun k hk => by
      fin_cases k
      any_goals simp at hk
      · exact l₂.2
      · exact l₃.2)
    hdv hdv' hdeg
  exact ⟨s, hs2, w, ![u₀, u₁, u₂, u₃], hbij, fun k => by fin_cases k <;> simp [w₀, w₁, w₂, w₃],
    hww, hwu, huu⟩

end Excluded

/-! ### The classification -/

/-- **Log canonical rational trees without boundary** (FA Lemma 3.2.7). Let `Γ` be a negative
definite rational tree with all boundary degrees `β_j = 0` whose log discrepancy vector `a` is
nonnegative. Then `Γ` is
1. a weighted chain; or
2. a star with three arms `arms` at a vertex `v` whose arm determinants
   `Δ_i = Γ.delta (arms i)` form, as a multiset, `{2, 2, m}` for some `m ≥ 2`, or `{2, 3, 3}`,
   `{2, 3, 4}`, `{2, 3, 5}`, `{2, 3, 6}`, `{2, 4, 4}` or `{3, 3, 3}`; or
3. a vertex `v` together with four vertices `u 0, …, u 3` of weight `2`, each joined to `v` by a
   simple edge and to no other vertex, and no further vertices; or
4. a chain `w 0, …, w (s - 1)` with `2 ≤ s`, consecutive `w i` joined by simple edges, together
   with four vertices `u 0, …, u 3` of weight `2`, where `u 0`, `u 1` are joined to `w 0` and
   `u 2`, `u 3` to `w (s - 1)` by simple edges, with no other edges and no further vertices. -/
@[mmp "lem_fa3_no_boundary_lc_graph_list"]
public theorem IsLogDiscrepancyVector.isWeightedChain_or_isStar_or_of_nonneg {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) (hβ : ∀ j, Γ.boundary j = 0) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) (ha_nonneg : ∀ k, 0 ≤ a k) :
    Γ.IsWeightedChain ∨
    (∃ (v : V) (arms : Fin 3 → Finset V), Γ.IsStar v arms ∧
      ((∃ m : ℤ, 2 ≤ m ∧
          ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 2, m}) ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 3} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 4} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 5} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 6} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 4, 4} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {3, 3, 3})) ∨
    (∃ (v : V) (u : Fin 4 → V), Function.Injective u ∧ Set.range u = {v}ᶜ ∧
      (∀ k, Γ.weight (u k) = 2) ∧ (∀ k, Γ.IsSimpleEdge v (u k)) ∧
      ∀ k l, k ≠ l → Γ.edgeWeight (u k) (u l) = 0) ∨
    (∃ (s : ℕ) (_ : 2 ≤ s) (w : Fin s → V) (u : Fin 4 → V),
      Function.Bijective (Sum.elim w u) ∧ (∀ k, Γ.weight (u k) = 2) ∧
      (∀ i j : Fin s,
        Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0) ∧
      (∀ (i : Fin s) (k : Fin 4), Γ.edgeWeight (w i) (u k) =
        if ((k : ℕ) < 2 ∧ (i : ℕ) = 0) ∨ (2 ≤ (k : ℕ) ∧ (i : ℕ) + 1 = s) then 1 else 0) ∧
      ∀ k l : Fin 4, Γ.edgeWeight (u k) (u l) = 0) := by
  have hs := hasSimpleEdges_of_isRationalTree Γ hΓ
  have hp := hΓ.genus_eq_zero
  rcases hΓ.isTree_or_isEmpty with hT | hE
  swap
  · exact Or.inl ⟨0, Equiv.equivOfIsEmpty _ _, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  have h4 := degree_le_four hΓ hneg hβ ha ha_nonneg hT
  have h42 : ∀ v v', v' ≠ v → Γ.underlyingGraph.degree v = 4 →
      Γ.underlyingGraph.degree v' ≤ 2 := fun v v' hvv' hv =>
    degree_le_two_of_degree_eq_four hΓ hneg hβ ha ha_nonneg hT hvv' hv
  have hF := card_forks_le_two hΓ hneg hβ ha ha_nonneg hT h42
  set F : Finset V := {v | 3 ≤ Γ.underlyingGraph.degree v} with hFdef
  have hmemF : ∀ z, z ∈ F ↔ 3 ≤ Γ.underlyingGraph.degree z := fun z => by simp [hFdef]
  interval_cases hc : #F
  · refine Or.inl (isWeightedChain_of_degree_le hT hs hp fun z => ?_)
    have : z ∉ F := by rw [card_eq_zero] at hc; simp [hc]
    rw [hmemF] at this
    omega
  · obtain ⟨v, hv⟩ := card_eq_one.1 hc
    have hdeg : ∀ z, z ≠ v → Γ.underlyingGraph.degree z ≤ 2 := fun z hz => by
      have : z ∉ F := by rw [hv]; simpa using hz
      rw [hmemF] at this
      omega
    have hv3 : 3 ≤ Γ.underlyingGraph.degree v :=
      (hmemF v).1 (by rw [hv]; exact mem_singleton_self v)
    have hdv := h4 v
    have hΓd := degree_eq_underlyingGraph_degree Γ v
    have hstar := exists_isStar hT hs hp hdeg
    rcases (by omega : Γ.underlyingGraph.degree v = 3 ∨ Γ.underlyingGraph.degree v = 4)
      with h3 | h4'
    · rw [hΓd, h3] at hstar
      obtain ⟨arms, hstar⟩ := hstar
      exact Or.inr (Or.inl ⟨v, arms, hstar,
        isLcTriple_of_isStar_three hΓ hneg hβ hstar ha (ha_nonneg v)⟩)
    · rw [hΓd, h4'] at hstar
      obtain ⟨arms, hstar⟩ := hstar
      obtain ⟨u, hu⟩ := four_arm_data hs hstar
        (ha.forall_arms_eq_singleton_of_isStar_four hΓ hneg hβ hstar (ha_nonneg v))
      exact Or.inr (Or.inr (Or.inl ⟨v, u, hu⟩))
  · obtain ⟨v, v', hvv', hF2⟩ := card_eq_two.1 hc
    exact Or.inr (Or.inr (Or.inr (exists_twoForkChain_of_forks hΓ hneg hβ ha ha_nonneg hT hvv'
      fun z => by rw [← hmemF, hF2]; simp)))

/-! ### The log terminal list -/

/-- **Log terminal rational trees without boundary** (FA Lemma 3.2.7). Let `Γ` be a negative
definite rational tree with all boundary degrees `β_j = 0` whose log discrepancy vector `a` is
positive. Then `Γ` is a weighted chain, or a star with three arms `arms` at a vertex `v` whose
arm determinants `Δ_i = Γ.delta (arms i)` form, as a multiset, `{2, 2, m}` for some `m ≥ 2`, or
`{2, 3, 3}`, `{2, 3, 4}` or `{2, 3, 5}`. -/
@[mmp "lem_fa3_no_boundary_lt_graph_list"]
public theorem IsLogDiscrepancyVector.isWeightedChain_or_isStar_of_pos {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) (hβ : ∀ j, Γ.boundary j = 0) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) (ha_pos : ∀ k, 0 < a k) :
    Γ.IsWeightedChain ∨
    ∃ (v : V) (arms : Fin 3 → Finset V), Γ.IsStar v arms ∧
      ((∃ m : ℤ, 2 ≤ m ∧
          ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 2, m}) ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 3} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 4} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 5}) := by
  rcases ha.isWeightedChain_or_isStar_or_of_nonneg hΓ hneg hβ (fun k => (ha_pos k).le) with
    h | ⟨v, arms, hstar, h | h | h | h | h⟩ | ⟨v, u, hu, hrange, hn, hvu, huu⟩ |
      ⟨s, hs, w, u, hbij, hn, hww, hwu, huu⟩
  · exact .inl h
  · exact .inr ⟨v, arms, hstar, .inl h⟩
  · exact .inr ⟨v, arms, hstar, .inr (.inl h)⟩
  · exact .inr ⟨v, arms, hstar, .inr (.inr (.inl h))⟩
  · exact .inr ⟨v, arms, hstar, .inr (.inr (.inr h))⟩
  · exact ((ha_pos v).ne' (ha.apply_eq_zero_of_isStar_three hΓ hneg hβ hstar h)).elim
  · have h0 := (isLogDiscrepancyVector_iff_of_four_arms hu hrange hΓ.genus_eq_zero hβ hn hvu
      huu (det_pos_of_isNegDef hneg).ne').1 ha
    exact ((ha_pos v).ne' (by simp [h0])).elim
  · exact ((ha_pos _).ne' (((isLogDiscrepancyVector_iff_of_two_forks hs hbij hΓ.genus_eq_zero hβ
      hn hww hwu huu (det_pos_of_isNegDef hneg).ne').1 ha).1 ⟨0, by omega⟩)).elim

end MMP.Flips.WeightedGraph

/-! ### Surface germs with boundary -/

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry Finset MMP.Mori WeightedGraph

section ZeroBoundary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted graph `Γ⁰`: `Γ` with every boundary degree `β_j` replaced by `0`. -/
private def zeroBoundary (Γ : WeightedGraph V) : WeightedGraph V :=
  { Γ with boundary := 0, boundary_nonneg := fun _ => le_rfl }

/-- `Γ⁰|_{univ}` is a subgraph of `Γ`. -/
private lemma zeroBoundary_restrict_isSubgraph (Γ : WeightedGraph V) :
    ((zeroBoundary Γ).restrict univ).IsSubgraph Γ :=
  ⟨fun _ => rfl, fun _ _ _ => le_rfl, fun _ => le_rfl, fun j => Γ.boundary_nonneg j⟩

/-- A log discrepancy vector of `G|_{univ}` is one of `G`. -/
private lemma isLogDiscrepancyVector_of_restrict_univ (G : WeightedGraph V)
    {a : ↥(univ : Finset V) → ℚ}
    (ha : (G.restrict univ).IsLogDiscrepancyVector a) :
    G.IsLogDiscrepancyVector fun k => a ⟨k, mem_univ k⟩ := by
  let e : ↥(univ : Finset V) ≃ V := Equiv.subtypeUnivEquiv mem_univ
  have hm : ∀ k l : ↥(univ : Finset V), (G.restrict univ).matrix k l = G.matrix k l := by
    intro k l
    simp only [WeightedGraph.matrix, Matrix.of_apply, Subtype.ext_iff]
    rfl
  have hc : ∀ l : ↥(univ : Finset V), (G.restrict univ).c l = G.c l := by
    intro l
    simp only [WeightedGraph.c, Finset.sum_erase_eq_sub (mem_univ _)]
    congr 2
    exact Fintype.sum_equiv e _ _ fun k => rfl
  intro j
  have := ha ⟨j, mem_univ j⟩
  rw [hc] at this
  rw [← this]
  exact (Fintype.sum_equiv e _ _ fun k => by rw [hm]; rfl).symm

private lemma isStar_of_zeroBoundary {Γ : WeightedGraph V} {v : V} {N : ℕ}
    {arms : Fin N → Finset V} (h : (zeroBoundary Γ).IsStar v arms) : Γ.IsStar v arms := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun i => ?_⟩
  obtain ⟨t, c, s, hs, e, he, hadj, hu⟩ := h7 i
  exact ⟨t, c, s, hs, e, ⟨he.1, he.2⟩, hadj, hu⟩

private lemma isWeightedChain_of_zeroBoundary {Γ : WeightedGraph V}
    (h : (zeroBoundary Γ).IsWeightedChain) : Γ.IsWeightedChain := by
  obtain ⟨s, e, h⟩ := h
  exact ⟨s, e, ⟨h.1, h.2⟩⟩

/-- **Removing the boundary strictly raises log discrepancies.** If `Γ` is a negative definite
connected weighted graph with `d_j(Γ) ≤ 0`, all weights `≥ 2` and some `β_j > 0`, then `Γ⁰`
has a log discrepancy vector strictly larger than any log discrepancy vector `a` of `Γ`: `Γ⁰` is
a proper subgraph of `Γ`, and `Γ` is not Du Val because it has some nonzero boundary degree. -/
private lemma exists_isLogDiscrepancyVector_zeroBoundary_gt {Γ : WeightedGraph V}
    (hneg : Γ.IsNegDef) (hconn : Γ.IsConnected) (hd : ∀ j, Γ.d j ≤ 0)
    (hw : ∀ j, 2 ≤ Γ.weight j) (hβ : ∃ j, 0 < Γ.boundary j) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) :
    ∃ a', (zeroBoundary Γ).IsLogDiscrepancyVector a' ∧ ∀ k, a k < a' k := by
  obtain ⟨j, hj⟩ := hβ
  haveI : Nonempty V := ⟨j⟩
  obtain ⟨a', ha', -⟩ := existsUnique_isLogDiscrepancyVector ((zeroBoundary Γ).restrict univ)
    (hneg.delta_pos univ).ne'
  have hne : (zeroBoundary Γ).restrict univ ≠ Γ.restrict univ := fun h => hj.ne' <| by
    simpa [zeroBoundary, WeightedGraph.restrict] using
      (congrArg (fun G => G.boundary ⟨j, mem_univ j⟩) h).symm
  exact ⟨_, isLogDiscrepancyVector_of_restrict_univ _ ha', fun k =>
    ha.lt_of_isSubgraph ha' (zeroBoundary_restrict_isSubgraph Γ) (.inr hne) hneg hconn hd
      (fun l h => by have := hw l; omega) (fun h => hj.ne' (h j).2.2) ⟨k, mem_univ k⟩⟩

end ZeroBoundary

/-- **Boundary reduces to the empty boundary** (FA 3.3.1). Let `f` be a minimal resolution of a
surface germ with boundary `(X, P; B)` over an algebraically closed field `k`, with exceptional
curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If `Γ` is a rational tree, some boundary
degree `β_j = (f⁻¹_* B · E_j)` is positive, and the log discrepancy vector `a` of `Γ` has all
entries `a_k ≥ 0`, then `Γ` is a weighted chain, or a star with three arms `arms` at a vertex `v`
whose arm determinants `Δ_i = Γ.delta (arms i)` form, as a multiset, `{2, 2, m}` for some `m ≥ 2`,
or `{2, 3, 3}`, `{2, 3, 4}` or `{2, 3, 5}`. -/
@[mmp "lem_fa3_boundary_reduces_to_empty"]
public theorem IsMinimalGermResolution.isWeightedChain_or_isStar_of_boundary_pos {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hrat : Γ.IsRationalTree) (hβ : ∃ j, 0 < Γ.boundary j)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ k, 0 ≤ a k) :
    Γ.IsWeightedChain ∨
    ∃ (v : Fin n) (arms : Fin 3 → Finset (Fin n)), Γ.IsStar v arms ∧
      ((∃ m : ℤ, 2 ≤ m ∧
          ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 2, m}) ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 3} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 4} ∨
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 5}) := by
  have : Nonempty (Fin n) := hβ.nonempty
  obtain ⟨a', ha', hlt⟩ := exists_isLogDiscrepancyVector_zeroBoundary_gt hΓ.isNegDef
    ⟨hΓ.preconnected⟩ (hf.d_nonpos hΓ) hrat.two_le_weight hβ ha
  rcases IsLogDiscrepancyVector.isWeightedChain_or_isStar_of_pos (Γ := zeroBoundary Γ)
      ⟨hrat.1, hrat.2, hrat.3, hrat.4⟩ hΓ.isNegDef (fun _ => rfl) ha'
      (fun i => (ha0 i).trans_lt (hlt i)) with h0 | ⟨v, arms, hs, h⟩
  · exact .inl (isWeightedChain_of_zeroBoundary h0)
  · exact .inr ⟨v, arms, isStar_of_zeroBoundary hs, h⟩

end MMP.Flips
