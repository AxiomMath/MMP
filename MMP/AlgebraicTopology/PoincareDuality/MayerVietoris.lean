module

public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains

/-!
# Mayer–Vietoris for the vanishing of `H_*(Y, Y - K)`

For a topological space `Y`, a subset `K ⊆ Y` and a commutative ring `R`, a singular `m`-chain
`c` is a *relative boundary* for `K` if `c - ∂ w` lies in `C_m(Y - K)` for some `(m+1)`-chain `w`,
i.e. `c` is a boundary in `C_*(Y) / C_*(Y - K)`. The relative homology `H_{m+1}(Y, Y - K; R)`
vanishes (`RelVanishing R Y m K`) if every `(m+1)`-chain with boundary in `C_m(Y - K)` is a
relative boundary for `K`.

This is the Mayer–Vietoris step of Hatcher's Lemma 3.27 at the chain level: for closed `A`, `B`
with `H_{m+1}(Y, Y - A ∩ B) = 0`, a chain that is a relative boundary for `A` and for `B` is a
relative boundary for `A ∪ B`. The proof uses the theorem of small chains for the open cover
`{Y - A, Y - B}` of `Y - A ∩ B`; Hatcher's chain homotopy `D` vanishes on chains that are already
small.

## Main definitions

* `MMP.SingularChain.IsRelBoundary`: relative boundaries for `K`.
* `MMP.SingularChain.RelVanishing`: `H_{m+1}(Y, Y - K; R) = 0`.

## Main results

* `MMP.SingularChain.smallHomotopy_eq_zero_of_mem_small`: `D` vanishes on small
  chains.
* `MMP.SingularChain.isRelBoundary_union`: the Mayer–Vietoris step.
* `MMP.SingularChain.RelVanishing.union`: vanishing for `A`, `B` and (one degree
  up) `A ∩ B` gives vanishing for `A ∪ B`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3, Lemma 3.27.
-/

@[expose] public noncomputable section

open Finsupp Set

namespace MMP

namespace SingularChain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

section inside

/-- A chain lying in `U` lies in any `V ⊇ U`. -/
lemma inside_mono (n : ℕ) {U V : Set Y} (h : U ⊆ V) : inside R n U ≤ inside R n V :=
  supported_mono fun _ hσ ↦ hσ.trans h

/-- A chain lies in `U ∩ V` iff it lies in `U` and in `V`. -/
lemma inside_inter (n : ℕ) (U V : Set Y) :
    inside R n (U ∩ V) = inside R n U ⊓ inside R n V := by
  rw [inside, inside, inside, ← supported_inter]
  congr 1
  ext σ
  exact subset_inter_iff

/-- A chain lying in a member `U` of `𝒰` is `𝒰`-small. -/
lemma inside_le_small (n : ℕ) {𝒰 : Set (Set Y)} {U : Set Y} (hU : U ∈ 𝒰) :
    inside R n U ≤ small R n 𝒰 :=
  fun _ hc ↦ mem_small_of_mem_inside hU hc

end inside

section relBoundary

variable (R) in
/-- `c` is a boundary in `C_*(Y) / C_*(Y - K)`: `c - ∂ w` lies in `Y - K` for some `w`. -/
def IsRelBoundary (m : ℕ) (K : Set Y) (c : Chain R Y m) : Prop :=
  ∃ w : Chain R Y (m + 1), c - bd R m w ∈ inside R m Kᶜ

variable (R Y) in
/-- `H_{m+1}(Y, Y - K; R) = 0`: every `(m+1)`-chain with boundary in `Y - K` is a relative
boundary for `K`. -/
def RelVanishing (m : ℕ) (K : Set Y) : Prop :=
  ∀ c : Chain R Y (m + 1), bd R m c ∈ inside R m Kᶜ → IsRelBoundary R (m + 1) K c

/-- A relative boundary for `K` is a relative boundary for any `K' ⊆ K`. -/
lemma IsRelBoundary.mono {m : ℕ} {K K' : Set Y} (h : K' ⊆ K) {c : Chain R Y m}
    (hc : IsRelBoundary R m K c) : IsRelBoundary R m K' c := by
  obtain ⟨w, hw⟩ := hc
  exact ⟨w, inside_mono m (compl_subset_compl.2 h) hw⟩

/-- The zero chain is a relative boundary for `K`. -/
lemma isRelBoundary_zero (m : ℕ) (K : Set Y) : IsRelBoundary R m K 0 :=
  ⟨0, by simp⟩

/-- A chain lying in `Y - K` is a relative boundary for `K`. -/
lemma isRelBoundary_of_mem_inside {m : ℕ} {K : Set Y} {c : Chain R Y m}
    (hc : c ∈ inside R m Kᶜ) : IsRelBoundary R m K c :=
  ⟨0, by simpa using hc⟩

/-- A boundary `∂ w` is a relative boundary for `K`. -/
lemma isRelBoundary_bd (m : ℕ) (K : Set Y) (w : Chain R Y (m + 1)) :
    IsRelBoundary R m K (bd R m w) :=
  ⟨w, by simp⟩

/-- The sum of two relative boundaries for `K` is a relative boundary for `K`. -/
lemma IsRelBoundary.add {m : ℕ} {K : Set Y} {c d : Chain R Y m} (hc : IsRelBoundary R m K c)
    (hd : IsRelBoundary R m K d) : IsRelBoundary R m K (c + d) := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, hv⟩ := hd
  refine ⟨w + v, ?_⟩
  have : c + d - bd R m (w + v) = (c - bd R m w) + (d - bd R m v) := by rw [map_add]; abel
  rw [this]
  exact Submodule.add_mem _ hw hv

/-- The negative of a relative boundary for `K` is a relative boundary for `K`. -/
lemma IsRelBoundary.neg {m : ℕ} {K : Set Y} {c : Chain R Y m} (hc : IsRelBoundary R m K c) :
    IsRelBoundary R m K (-c) := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨-w, ?_⟩
  have : -c - bd R m (-w) = -(c - bd R m w) := by rw [map_neg]; abel
  rw [this]
  exact Submodule.neg_mem _ hw

/-- The difference of two relative boundaries for `K` is a relative boundary for `K`. -/
lemma IsRelBoundary.sub {m : ℕ} {K : Set Y} {c d : Chain R Y m} (hc : IsRelBoundary R m K c)
    (hd : IsRelBoundary R m K d) : IsRelBoundary R m K (c - d) := by
  rw [sub_eq_add_neg]
  exact hc.add hd.neg

/-- A scalar multiple of a relative boundary for `K` is a relative boundary for `K`. -/
lemma IsRelBoundary.smul {m : ℕ} {K : Set Y} {c : Chain R Y m} (r : R)
    (hc : IsRelBoundary R m K c) : IsRelBoundary R m K (r • c) := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨r • w, ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ r hw

end relBoundary

section smallHomotopy

/-- The subdivision index of a simplex lying in a member of `𝒰` is `0`. -/
lemma smallIndex_eq_zero {𝒰 : Set (Set Y)} :
    ∀ (n : ℕ) {σ : Simplex Y n}, (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex R 𝒰 n σ = 0 := by
  have h₀ : ∀ {n : ℕ} {σ : Simplex Y n}, (∃ U ∈ 𝒰, range σ ⊆ U) → smallIndex₀ R 𝒰 σ = 0 := by
    intro n σ hσ
    classical
    have h0 : (subdiv R n ^ 0) (single σ 1) ∈ small R n 𝒰 := by
      rw [pow_zero, Module.End.one_apply]
      exact single_mem_supported R _ hσ
    have h : ∃ m, (subdiv R n ^ m) (single σ 1) ∈ small R n 𝒰 := ⟨0, h0⟩
    simp only [smallIndex₀, h, ↓reduceDIte]
    exact (Nat.find_eq_zero h).2 h0
  intro n
  induction n with
  | zero => intro σ hσ; exact h₀ hσ
  | succ n ih =>
    intro σ hσ
    obtain ⟨U, hU, hσU⟩ := hσ
    refine Nat.eq_zero_of_le_zero (max_le (h₀ ⟨U, hU, hσU⟩).le (Finset.sup_le fun i _ ↦ ?_))
    refine (ih ⟨U, hU, ?_⟩).le
    rintro _ ⟨t, rfl⟩
    exact hσU ⟨_, rfl⟩

/-- Hatcher's chain homotopy `D` vanishes on `𝒰`-small chains. -/
lemma smallHomotopy_eq_zero_of_mem_small {𝒰 : Set (Set Y)} {n : ℕ} {c : Chain R Y n}
    (hc : c ∈ small R n 𝒰) : smallHomotopy R 𝒰 n c = 0 := by
  have : smallHomotopy R 𝒰 n c ∈ (⊥ : Submodule R (Chain R Y (n + 1))) :=
    VertexChain.mem_of_mem_supported _ _ (fun σ hσ ↦ by
      rw [smallHomotopy_single, smallIndex_eq_zero n hσ]
      simp [homotopyUpTo]) hc
  simpa using this

/-- On a chain with `𝒰`-small boundary, `ρ = 1 - ∂ D`. -/
lemma smallChainMap_succ_of_bd_mem_small {𝒰 : Set (Set Y)} {n : ℕ} {g : Chain R Y (n + 1)}
    (hg : bd R n g ∈ small R n 𝒰) :
    smallChainMap R 𝒰 (n + 1) g = g - bd R (n + 1) (smallHomotopy R 𝒰 (n + 1) g) := by
  rw [smallChainMap_succ, smallHomotopy_eq_zero_of_mem_small hg, sub_zero]

end smallHomotopy

section mayerVietoris

/-- A chain small for `{U, V}` splits as a chain in `U` plus a chain in `V`. -/
lemma exists_add_of_mem_small_pair {n : ℕ} {U V : Set Y} {c : Chain R Y n}
    (hc : c ∈ small R n {U, V}) :
    ∃ cU ∈ inside R n U, ∃ cV ∈ inside R n V, c = cU + cV := by
  classical
  refine ⟨c.filter (fun σ ↦ range σ ⊆ U), ?_, c.filter (fun σ ↦ ¬ range σ ⊆ U), ?_,
    (filter_add_filter_not c _).symm⟩
  · rw [inside, mem_supported, support_filter, Finset.coe_filter]
    exact fun σ hσ ↦ hσ.2
  · rw [inside, mem_supported, support_filter, Finset.coe_filter]
    rintro σ ⟨hσ, hσU⟩
    obtain ⟨W, hW, hσW⟩ := (mem_supported R c).1 hc hσ
    rcases hW with rfl | rfl
    · exact absurd hσW hσU
    · exact hσW

/-- The Mayer–Vietoris step of Hatcher's Lemma 3.27: for closed `A`, `B` with
`H_{m+1}(Y, Y - A ∩ B) = 0`, a relative boundary for `A` and for `B` is one for `A ∪ B`. -/
theorem isRelBoundary_union {m : ℕ} {A B : Set Y} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : RelVanishing R Y m (A ∩ B)) {c : Chain R Y m} (hcA : IsRelBoundary R m A c)
    (hcB : IsRelBoundary R m B c) : IsRelBoundary R m (A ∪ B) c := by
  obtain ⟨wA, ha⟩ := hcA
  obtain ⟨wB, hb⟩ := hcB
  set 𝒰 : Set (Set Y) := {Aᶜ, Bᶜ}
  have h𝒰 : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U (rfl | rfl)
    · exact hA.isOpen_compl
    · exact hB.isOpen_compl
  have hAs : inside R m Aᶜ ≤ small R m 𝒰 := inside_le_small m (by simp [𝒰])
  have hBs : inside R m Bᶜ ≤ small R m 𝒰 := inside_le_small m (by simp [𝒰])
  have hbd : bd R m (wA - wB) = (c - bd R m wB) - (c - bd R m wA) := by rw [map_sub]; abel
  have hbdIn : bd R m (wA - wB) ∈ inside R m (A ∩ B)ᶜ := by
    rw [hbd]
    exact Submodule.sub_mem _
      (inside_mono m (compl_subset_compl.2 inter_subset_right) hb)
      (inside_mono m (compl_subset_compl.2 inter_subset_left) ha)
  obtain ⟨e, he⟩ := hAB (wA - wB) hbdIn
  set g := wA - wB - bd R (m + 1) e with hgdef
  have hbdg : bd R m g = bd R m (wA - wB) := by rw [hgdef, map_sub, bd_bd, sub_zero]
  have hbdgs : bd R m g ∈ small R m 𝒰 := by
    rw [hbdg, hbd]
    exact Submodule.sub_mem _ (hBs hb) (hAs ha)
  have hgU : g ∈ inside R (m + 1) (⋃₀ 𝒰) := by
    have : ⋃₀ 𝒰 = (A ∩ B)ᶜ := by simp [𝒰, compl_inter]
    rw [this]
    exact he
  have hρ := smallChainMap_succ_of_bd_mem_small hbdgs
  obtain ⟨gA, hgA, gB, hgB, hsplit⟩ :=
    exists_add_of_mem_small_pair (smallChainMap_mem_small h𝒰 (m + 1) hgU)
  rw [hρ] at hsplit
  have hw : wA - gA = wB + gB + bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) g + e) := by
    rw [map_add]
    have h1 : wA = wB + (g + bd R (m + 1) e) := by rw [hgdef]; abel
    generalize bd R (m + 1) (smallHomotopy R 𝒰 (m + 1) g) = X at hsplit ⊢
    rw [h1, (sub_eq_iff_eq_add.1 hsplit)]
    abel
  refine ⟨wA - gA, ?_⟩
  rw [compl_union, inside_inter]
  refine ⟨?_, ?_⟩
  · have : c - bd R m (wA - gA) = (c - bd R m wA) + bd R m gA := by rw [map_sub]; abel
    rw [this]
    exact Submodule.add_mem _ ha (bd_mem_inside hgA)
  · rw [hw, map_add, map_add, bd_bd]
    have : c - (bd R m wB + bd R m gB + 0) = (c - bd R m wB) - bd R m gB := by abel
    rw [this]
    exact Submodule.sub_mem _ hb (bd_mem_inside hgB)

/-- Vanishing of `H_{m+1}(Y, Y - A)`, `H_{m+1}(Y, Y - B)` and `H_{m+2}(Y, Y - A ∩ B)` gives
vanishing of `H_{m+1}(Y, Y - A ∪ B)`, for closed `A` and `B`. -/
theorem RelVanishing.union {m : ℕ} {A B : Set Y} (hA : IsClosed A) (hB : IsClosed B)
    (hvA : RelVanishing R Y m A) (hvB : RelVanishing R Y m B)
    (hvAB : RelVanishing R Y (m + 1) (A ∩ B)) : RelVanishing R Y m (A ∪ B) := by
  intro c hc
  exact isRelBoundary_union hA hB hvAB
    (hvA c (inside_mono m (compl_subset_compl.2 subset_union_left) hc))
    (hvB c (inside_mono m (compl_subset_compl.2 subset_union_right) hc))

end mayerVietoris

end SingularChain

end MMP
